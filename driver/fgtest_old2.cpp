#include "defs.h"
#include "debug.h"
#include "version.h"

#include "dfsan/dfsan.h"
#include "afl_trace_map.h"
#include <z3++.h>

#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <utility>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <regex>
using namespace __dfsan;
using namespace qsym;
#define OPTIMISTIC 1

// ===== NEW: Static address trigger configuration =====
#define SYMBOLIC_TRIGGER_ADDR 0x100000
#define USE_STATIC_TRIGGER 1
// =====================================================

#undef AOUT
# define AOUT(...)                                      \
  do {                                                  \
    fprintf(stderr, __VA_ARGS__);                                \
  } while(false)
bool print_debug = true;
static dfsan_label_info *__dfsan_label_info;
static char *input_buf;
static size_t input_size;

dfsan_label_info* __dfsan::get_label_info(dfsan_label label) {
  return &__dfsan_label_info[label];
}

// for output
static const char* __output_dir = ".";
static u32 __instance_id = 0;
static u32 __session_id = 0;
static u32 __current_index = 0;
static z3::context __z3_context;
static z3::solver __z3_solver(__z3_context, "QF_BV");

// caches
static std::unordered_map<dfsan_label, u32> tsize_cache;
static std::unordered_map<dfsan_label, std::unordered_set<u32> > deps_cache;
static std::unordered_map<dfsan_label, z3::expr> expr_cache;
static std::unordered_map<dfsan_label, memcmp_msg*> memcmp_cache;

// dependencies
struct expr_hash {
  std::size_t operator()(const z3::expr &expr) const {
    return expr.hash();
  }
};
struct expr_equal {
  bool operator()(const z3::expr &lhs, const z3::expr &rhs) const {
    return lhs.id() == rhs.id();
  }
};
typedef std::unordered_set<z3::expr, expr_hash, expr_equal> expr_set_t;

struct labeltuple_hash {
  std::size_t operator()(const std::tuple<uint32_t, uint32_t> &x) const {
    return std::get<0>(x) ^ std::get<1>(x);
  }
};
typedef std::unordered_set<std::tuple<uint32_t, uint32_t>, labeltuple_hash> labeltuple_set_t;

typedef struct {
  expr_set_t expr_deps;
  std::unordered_set<dfsan_label> input_deps;
} branch_dep_t;
static std::vector<branch_dep_t*> __branch_deps;
labeltuple_set_t added_label;

AflTraceMap *_trace;

static inline branch_dep_t* get_branch_dep(size_t n) {
  if (n >= __branch_deps.size()) {
    __branch_deps.resize(n + 1);
  }
  return __branch_deps.at(n);
}

static inline void set_branch_dep(size_t n, branch_dep_t* dep) {
  if (n >= __branch_deps.size()) {
    __branch_deps.resize(n + 1);
  }
  __branch_deps.at(n) = dep;
}

static z3::expr read_concrete(dfsan_label label, u16 size) {
  auto itr = memcmp_cache.find(label);
  if (itr == memcmp_cache.end()) {
    throw z3::exception("cannot find memcmp content");
  }

  memcmp_msg *mmsg = itr->second;
  z3::expr val = __z3_context.bv_val(mmsg->content[0], 8);
  for (u8 i = 1; i < size; i++) {
    val = z3::concat(__z3_context.bv_val(mmsg->content[i], 8), val);
  }
  return val;
}

static z3::expr get_cmd(z3::expr const &lhs, z3::expr const &rhs, u32 predicate) {
  switch (predicate) {
    case bveq:  return lhs == rhs;
    case bvneq: return lhs != rhs;
    case bvugt: return z3::ugt(lhs, rhs);
    case bvuge: return z3::uge(lhs, rhs);
    case bvult: return z3::ult(lhs, rhs);
    case bvule: return z3::ule(lhs, rhs);
    case bvsgt: return lhs > rhs;
    case bvsge: return lhs >= rhs;
    case bvslt: return lhs < rhs;
    case bvsle: return lhs <= rhs;
    default:
      AOUT("FATAL: unsupported predicate: %u\n", predicate);
      throw z3::exception("unsupported predicate");
      break;
  }
  Die();
}

static inline z3::expr cache_expr(dfsan_label label, z3::expr const &e, std::unordered_set<u32> &deps) {
  expr_cache.insert({label,e});
  deps_cache.insert({label,deps});
  return e;
}

static inline z3::expr cache_expr_only(dfsan_label label, z3::expr const &e) {
  expr_cache.insert({label,e});
  return e;
}

// [serialize() function remains the same - keeping original for brevity]
// [serialize_simple() function remains the same]
// [cache_expr_deps() function remains the same]
// [_get_input_deps() function remains the same]

static void generate_input(z3::model &m) {
  char path[PATH_MAX];
  snprintf(path, PATH_MAX, "%s/id-%d-%d-%d", __output_dir,
           __instance_id, __session_id, __current_index++);
  int fd = open(path, O_CREAT | O_WRONLY, S_IRUSR | S_IWUSR);
  if (fd == -1) {
    throw z3::exception("failed to open new input file for write");
  }

  if (write(fd, input_buf, input_size) == -1) {
    throw z3::exception("failed to copy original input\n");
  }

  unsigned num_constants = m.num_consts();
  for (unsigned i = 0; i < num_constants; i++) {
    z3::func_decl decl = m.get_const_decl(i);
    z3::expr e = m.get_const_interp(decl);
    z3::symbol name = decl.name();

    if (name.kind() == Z3_INT_SYMBOL) {
      int offset = name.to_int();
      u8 value = (u8)e.get_numeral_int();
      lseek(fd, offset, SEEK_SET);
      write(fd, &value, sizeof(value));
    } else {
      if (!name.str().compare("fsize")) {
        off_t size = (off_t)e.get_numeral_int64();
        if (size > input_size) {
          lseek(fd, size, SEEK_SET);
          u8 dummy = 0;
          write(fd, &dummy, sizeof(dummy));
        } else {
          AOUT("truncate file to %ld\n", size);
          ftruncate(fd, size);
        }
        throw z3::exception("skip fsize constraints");
      }
    }
  }

  close(fd);
}

int sym_count = 0;

static bool __solve_expr(z3::expr &e) {
  bool ret = false;
  z3::solver opt_solver = z3::solver(__z3_context, "QF_BV");
  opt_solver.set("timeout", 1000U);
  opt_solver.add(e);
  z3::check_result res = opt_solver.check();
  if (res == z3::sat) {
    __z3_solver.push();
    __z3_solver.add(e);
    res = __z3_solver.check();
    if (res == z3::sat) {
      z3::model m = __z3_solver.get_model();
      generate_input(m);
      ret = true;
    } else {
    #if OPTIMISTIC
      z3::model m = opt_solver.get_model();
      generate_input(m);
    #endif
    }
    __z3_solver.pop();
  }
  return ret;
}

static void __solve_cond(dfsan_label label, u8 r, bool add_nested, u64 addr) {
  z3::expr result = __z3_context.bool_val(r != 0);

  bool pushed = false;
  try {
    std::unordered_set<dfsan_label> inputs;
    z3::expr cond = serialize(label, inputs).simplify();

    std::vector<dfsan_label> worklist;
    worklist.insert(worklist.begin(), inputs.begin(), inputs.end());
    while (!worklist.empty()) {
      auto off = worklist.back();
      worklist.pop_back();

      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        for (auto i : deps->input_deps) {
          if (inputs.insert(i).second)
            worklist.push_back(i);
        }
      }
    }

    __z3_solver.reset();
    __z3_solver.set("timeout", 5000U);
    expr_set_t added;
    for (auto off : inputs) {
      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        for (auto &expr : deps->expr_deps) {
          if (added.insert(expr).second) {
            __z3_solver.add(expr);
          }
        }
      }
    }

    z3::expr e = (cond != result);

    if (__solve_expr(e)) {
      // Solved
    } else {
      // Not solvable
    }

    if (add_nested) {
      for (auto off : inputs) {
        auto c = get_branch_dep(off);
        if (c == nullptr) {
          c = new branch_dep_t();
          set_branch_dep(off, c);
        }
        if (c == nullptr) {
          AOUT("WARNING: out of memory\n");
        } else {
          c->input_deps.insert(inputs.begin(), inputs.end());
          c->expr_deps.insert(cond == result);
        }
      }
    }

  } catch (z3::exception e) {
    AOUT("WARNING: solving error: %s @ label %d\n", e.msg(), label);
  }
}

// ===== NEW: Handle static address trigger =====
static void __handle_static_trigger(dfsan_label label, uint64_t addr, uint64_t value) {
  if (addr != SYMBOLIC_TRIGGER_ADDR) return;
  
  AOUT("Static trigger detected at 0x%lx, value=0x%lx, label=%d\n", 
       addr, value, label);
  
  // Mark this load as beginning of symbolic execution
  // The label will be tracked through subsequent operations
  std::unordered_set<u32> deps;
  try {
    z3::expr sym_val = serialize(label, deps);
    AOUT("  Symbolic expression: %s\n", sym_val.to_string().c_str());
    AOUT("  Input dependencies: ");
    for (auto d : deps) {
      AOUT("%u ", d);
    }
    AOUT("\n");
  } catch (z3::exception e) {
    AOUT("  Error serializing: %s\n", e.msg());
  }
}
// =============================================

static void __handle_gep(dfsan_label ptr_label, uptr ptr,
                         dfsan_label index_label, int64_t index,
                         uint64_t num_elems, uint64_t elem_size,
                         int64_t current_offset, void* addr) {

  AOUT("tainted GEP index: %ld = %d, ne: %ld, es: %ld, offset: %ld\n",
      index, index_label, num_elems, elem_size, current_offset);

  u8 size = get_label_info(index_label)->size;
  try {
    std::unordered_set<dfsan_label> inputs;
    z3::expr i = serialize(index_label, inputs);
    z3::expr r = __z3_context.bv_val(index, size);

    std::vector<dfsan_label> worklist;
    worklist.insert(worklist.begin(), inputs.begin(), inputs.end());
    while (!worklist.empty()) {
      auto off = worklist.back();
      worklist.pop_back();

      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        for (auto i : deps->input_deps) {
          if (inputs.insert(i).second)
            worklist.push_back(i);
        }
      }
    }

    __z3_solver.reset();
    __z3_solver.set("timeout", 5000U);
    expr_set_t added;
    for (auto off : inputs) {
      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        // constraint handling
      }
    }
    assert(__z3_solver.check() == z3::sat);

    z3::expr idx = z3::zext(i, 64 - size);
    if (num_elems > 0) {
      // GEP solving logic
    }

    for (auto off : inputs) {
      auto c = get_branch_dep(off);
      if (c == nullptr) {
        c = new branch_dep_t();
        set_branch_dep(off, c);
      }
      if (c == nullptr) {
        AOUT("WARNING: out of memory\n");
      } else {
        c->input_deps.insert(inputs.begin(), inputs.end());
      }
    }

  } catch (z3::exception e) {
    AOUT("WARNING: index solving error: %s @%p\n", e.msg(), __builtin_return_address(0));
  }
}

// ===== NEW: Read input from stdin =====
static bool read_stdin_input() {
  // Read from stdin into a buffer
  size_t capacity = 4096;
  size_t total_read = 0;
  input_buf = (char*)malloc(capacity);
  
  if (!input_buf) {
    fprintf(stderr, "Failed to allocate buffer for stdin\n");
    return false;
  }
  
  ssize_t n;
  while ((n = read(STDIN_FILENO, input_buf + total_read, capacity - total_read)) > 0) {
    total_read += n;
    if (total_read >= capacity) {
      capacity *= 2;
      char* new_buf = (char*)realloc(input_buf, capacity);
      if (!new_buf) {
        free(input_buf);
        fprintf(stderr, "Failed to reallocate buffer for stdin\n");
        return false;
      }
      input_buf = new_buf;
    }
  }
  
  if (n < 0) {
    free(input_buf);
    fprintf(stderr, "Failed to read from stdin: %s\n", strerror(errno));
    return false;
  }
  
  input_size = total_read;
  AOUT("Read %zu bytes from stdin\n", input_size);
  return true;
}
// ====================================

int main(int argc, char* const argv[]) {
  if (argc < 3) {
    fprintf(stderr, "Usage: %s <program> <target> [args...]\n", argv[0]);
    exit(1);
  }

  char *program = argv[1];
  char *target = argv[2];

  __output_dir = getenv("SYMCC_OUTPUT_DIR");
  if (!__output_dir) {
    __output_dir = ".";
  }

  char *input = getenv("SYMCC_INPUT_FILE");
  if (input == NULL) {
    fprintf(stderr, "ERROR: Cannot read SYMCC_INPUT_FILE environment variable! Exiting...\n");
    exit(1);
  }

  // ===== MODIFIED: Handle stdin properly =====
  if (strcmp(input, "stdin") == 0) {
    AOUT("Reading input from stdin...\n");
    if (!read_stdin_input()) {
      exit(1);
    }
  } else {
    // Original file reading logic
    struct stat st;
    int fd = open(input, O_RDONLY);
    if (fd == -1) {
      fprintf(stderr, "Failed to open input file: %s\n", strerror(errno));
      exit(1);
    }
    fstat(fd, &st);
    input_size = st.st_size;
    input_buf = (char *)mmap(NULL, input_size, PROT_READ, MAP_PRIVATE, fd, 0);
    if (input_buf == (void *)-1) {
      fprintf(stderr, "Failed to map input file: %s\n", strerror(errno));
      exit(1);
    }
    close(fd);
  }
  // ==========================================

  int shmid = shmget(IPC_PRIVATE, 0xc00000000,
    O_CREAT | SHM_NORESERVE | S_IRUSR | S_IWUSR);
  if (shmid == -1) {
    fprintf(stderr, "Failed to get shmid: %s\n", strerror(errno));
    exit(1);
  }

  __dfsan_label_info = (dfsan_label_info *)shmat(shmid, NULL, SHM_RDONLY);
  if (__dfsan_label_info == (void *)-1) {
    fprintf(stderr, "Failed to map shm(%d): %s\n", shmid, strerror(errno));
    exit(1);
  }

  int pipefds[2];
  if (pipe(pipefds) != 0) {
    fprintf(stderr, "Failed to create pipe fds: %s\n", strerror(errno));
    exit(1);
  }

  int length = snprintf(NULL, 0, "taint_file=\"%s\":shm_id=%d:pipe_fd=%d:debug=0",
                        input, shmid, pipefds[1]);
  char* options = (char *)malloc(length + 1);
  snprintf(options, length + 1, "taint_file=\"%s\":shm_id=%d:pipe_fd=%d:debug=0",
           input, shmid, pipefds[1]);
  
  int pid = fork();
  if (pid < 0) {
    fprintf(stderr, "Failed to fork: %s\n", strerror(errno));
    exit(1);
  }

  if (pid == 0) {
    close(pipefds[0]);
    setenv("TAINT_OPTIONS", options, 1);
    char* args[argc];
    for (int i = 0; i < argc-1; i++) {
      args[i] = argv[i+1];
    }
    args[argc-1] = NULL;
    execv(program, args);
    exit(0);
  }

  close(pipefds[1]);
  free(options);

  const char* bitmap = std::getenv("SYMCC_AFL_COVERAGE_MAP");
  if (!bitmap) {
    fprintf(stderr, "Failed to get bitmap file from env\n");
    exit(1);
  }
  _trace = new AflTraceMap(bitmap);

  pipeMsg msg;
  gep_msg gmsg;
  dfsan_label_info *info;
  size_t msg_size;
  memcmp_msg *mmsg = nullptr;

  std::vector<std::pair<uint32_t, uint64_t>> branch_label;

  while (read(pipefds[0], &msg, sizeof(msg)) > 0) {
    switch (msg.msg_type) {
      case cond_type:
        if (_trace->isInterestingBranch(msg.id, msg.result)) {
          __solve_cond(msg.label, msg.result, msg.flags & F_ADD_CONS, msg.id);
        }
        break;
        
      case gep_type:
        if (read(pipefds[0], &gmsg, sizeof(gmsg)) != sizeof(gmsg)) {
          fprintf(stderr, "Failed to receive gep msg: %s\n", strerror(errno));
          break;
        }
        if (msg.label != gmsg.index_label) {
          fprintf(stderr, "Incorrect gep msg: %d vs %d\n", msg.label, gmsg.index_label);
          break;
        }
        __handle_gep(gmsg.ptr_label, gmsg.ptr, gmsg.index_label, gmsg.index,
                     gmsg.num_elems, gmsg.elem_size, gmsg.current_offset, (void*)msg.addr);
        break;
        
      case memcmp_type:
        info = get_label_info(msg.label);
        if (info->l1 != CONST_LABEL && info->l2 != CONST_LABEL)
          break;
        msg_size = sizeof(memcmp_msg) + msg.result;
        mmsg = (memcmp_msg*)malloc(msg_size);
        if (read(pipefds[0], mmsg, msg_size) != msg_size) {
          fprintf(stderr, "Failed to receive memcmp msg: %s\n", strerror(errno));
          break;
        }
        if (msg.label != mmsg->label) {
          fprintf(stderr, "Incorrect memcmp msg: %d vs %d\n", msg.label, mmsg->label);
          break;
        }
        memcmp_cache[msg.label] = mmsg;
        break;
        
      case fsize_type:
        break;
        
      // ===== NEW: Handle static trigger message type =====
      // You'll need to add this message type to your pipe protocol
      // For now, this is a placeholder showing how to integrate it
      #ifdef STATIC_TRIGGER_MSG_TYPE
      case STATIC_TRIGGER_MSG_TYPE:
        __handle_static_trigger(msg.label, msg.addr, msg.result);
        break;
      #endif
      // =================================================
        
      default:
        break;
    }
  }

  int status;
  waitpid(pid, &status, 0);
  
  if (strcmp(input, "stdin") == 0) {
    free(input_buf);
  }
  
  exit(0);
}