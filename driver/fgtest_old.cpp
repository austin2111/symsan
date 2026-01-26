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
  // labeltuple_set_t label_tuples;
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
  // should never reach here
  Die();
}

// static inline z3::expr cache_expr(dfsan_label label, z3::expr const &e, std::unordered_set<u32> &deps) {
//   expr_cache.insert({label,e});
//   deps_cache.insert({label,deps});
//   return e;
// }

static inline z3::expr cache_expr(dfsan_label label, z3::expr const &e, std::unordered_set<u32> &deps) {
  expr_cache.insert({label,e});
  deps_cache.insert({label,deps});
  return e;
}

static inline z3::expr cache_expr_only(dfsan_label label, z3::expr const &e) {
  expr_cache.insert({label,e});
  return e;
}

static z3::expr serialize(dfsan_label label, std::unordered_set<u32> &deps) {
  if (label < CONST_OFFSET || label == kInitializingLabel) {
    AOUT("WARNING: invalid label: %d\n", label);
    throw z3::exception("invalid label");
  }

  dfsan_label_info *info = get_label_info(label);
  // if (print_debug) {
  //   AOUT("%u = (l1:%u, l2:%u, op:%u, size:%u, op1:%llu, op2:%llu)\n",
  //         label, info->l1, info->l2, info->op, info->size, info->op1.i, info->op2.i);
  // }

  auto expr_itr = expr_cache.find(label);
  if (expr_itr != expr_cache.end()) {
    auto deps_itr = deps_cache.find(label);
    deps.insert(deps_itr->second.begin(), deps_itr->second.end());
    return expr_itr->second;
  }

  // special ops
  if (info->op == 0) {
    // input
    z3::symbol symbol = __z3_context.int_symbol(info->op1.i);
    z3::sort sort = __z3_context.bv_sort(8);
    tsize_cache[label] = 1; // lazy init
    deps.insert(info->op1.i);
    // fprintf(stderr, "input offset 0x%lx\n", info->op1.i);
    // caching is not super helpful
    return __z3_context.constant(symbol, sort);
  } else if (info->op == Load) {
    u64 offset = get_label_info(info->l1)->op1.i;
    z3::symbol symbol = __z3_context.int_symbol(offset);
    z3::sort sort = __z3_context.bv_sort(8);
    z3::expr out = __z3_context.constant(symbol, sort);
    deps.insert(offset);
    for (u32 i = 1; i < info->l2; i++) {
      // fprintf(stderr, "offset + i 0x%lx\n", offset+i);
      symbol = __z3_context.int_symbol(offset + i);
      out = z3::concat(__z3_context.constant(symbol, sort), out);
      deps.insert(offset + i);
    }
    tsize_cache[label] = 1; // lazy init
    return cache_expr(label, out, deps);
  } else if (info->op == ZExt) {
    // Z3_mk_zero_ext(g_context, bits, expr)
    z3::expr base = serialize(info->l1, deps);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr(label, z3::zext(base, info->op2.i), deps);
  } else if (info->op == SExt) {
    z3::expr base = serialize(info->l1, deps);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr(label, z3::sext(base, info->op2.i), deps);
  } else if (info->op == Trunc) {
    z3::expr base = serialize(info->l1, deps);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr(label, base.extract(info->op2.i - 1, 0), deps);
  } else if (info->op == Extract) {
    z3::expr base = serialize(info->l1, deps);
    assert(base.get_sort().bv_size() > info->op2.i);
    assert(base.get_sort().bv_size() > info->op1.i);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    // Z3_mk_extract(g_context, first_bit, last_bit, expr)
    return cache_expr(label, base.extract(info->op1.i, info->op2.i), deps);
  } else if (info->op == Not) {
    if (info->l2 == 0/* || info->size != 1*/) {
      throw z3::exception("invalid Not operation");
    }
    z3::expr e = serialize(info->l2, deps);
    tsize_cache[label] = tsize_cache[info->l2]; // lazy init
    if (!e.is_bool()) {
      // bvnot
      return cache_expr(label, ~e, deps);
    } else {
      throw z3::exception("Only LNot should be recorded");
      // return cache_expr(label, !e, deps);
    }
  } else if (info->op == Neg) {
    if (info->l2 == 0) {
      throw z3::exception("invalid Neg predicate");
    }
    z3::expr e = serialize(info->l2, deps);
    tsize_cache[label] = tsize_cache[info->l2]; // lazy init
    return cache_expr(label, -e, deps);
  }
  // higher-order
  else if (info->op == fmemcmp) {
    z3::expr op1 = (info->l1 >= CONST_OFFSET) ? serialize(info->l1, deps) :
                   read_concrete(label, info->size); // memcmp size in bytes
    if (info->l2 < CONST_OFFSET) {
      throw z3::exception("invalid memcmp operand2");
    }
    z3::expr op2 = serialize(info->l2, deps);
    tsize_cache[label] = 1; // lazy init
    z3::expr e = z3::ite(op1 == op2, __z3_context.bv_val(0, 32),
                                     __z3_context.bv_val(1, 32));
    return cache_expr(label, e, deps);
  } else if (info->op == fsize) {
    // file size
    z3::symbol symbol = __z3_context.str_symbol("fsize");
    z3::sort sort = __z3_context.bv_sort(info->size);
    z3::expr base = __z3_context.constant(symbol, sort);
    tsize_cache[label] = 1; // lazy init
    // don't cache because of deps
    if (info->op1.i) {
      // minus the offset stored in op1
      z3::expr offset = __z3_context.bv_val((uint64_t)info->op1.i, info->size);
      return base - offset;
    } else {
      return base;
    }
  } else if (info->op == Ite) {
    // Covert bool expression to bv.
    z3::expr op1 = serialize(info->l1, deps);
    if (op1.is_bool()) {
      z3::expr e = z3::ite(op1, __z3_context.bv_val(1, 1),
                                     __z3_context.bv_val(0, 1));
      assert(info->size > 1);
      e = z3::zext(e, info->size - 1);
      tsize_cache[label] = tsize_cache[info->l1]; // lazy init
      return cache_expr(label, e, deps);
    } else {
      throw z3::exception("invalid Ite operation(for bool expr only)");
    }
  } else if (info->op == Equal) {
    // try an alternative symbolic address.
    // build an equal expression for a symbolic address.
    z3::expr e = serialize(info->l1, deps) == \
                 __z3_context.bv_val((uint64_t)info->op1.i, info->size);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr(label, e, deps);
  }

  // common ops
  u8 size = info->size;
  if (info->l1 == 0) {
    if (info->op == Concat) {
      // size = 8;
      size = info->size - get_label_info(info->l2)->size;
    } else {
      size = get_label_info(info->l2)->size;
    }
  }

  z3::expr op1 = __z3_context.bv_val((uint64_t)info->op1.i, size);
  if (info->l1 >= CONST_OFFSET) {
    op1 = serialize(info->l1, deps).simplify();
  }

  if (info->l2 == 0) {
    if (info->op == Concat) {
      // size = 8;
      size = info->size - get_label_info(info->l1)->size;
    } else {
      size = get_label_info(info->l1)->size;
    }
  }

  z3::expr op2 = __z3_context.bv_val((uint64_t)info->op2.i, size);
  if (info->l2 >= CONST_OFFSET) {
    std::unordered_set<u32> deps2;
    op2 = serialize(info->l2, deps2).simplify();
    deps.insert(deps2.begin(),deps2.end());
  }
  // AOUT("op %ld: op1 sort size = %d, op2 sort size = %d\n", info->op, op1.get_sort().bv_size(), op2.get_sort().bv_size());

  // size for concat is a bit complicated ...
  // if (info->op == Concat && info->l1 == 0) {
  //   assert(info->l2 >= CONST_OFFSET);
  //   size = info->size - get_label_info(info->l2)->size;
  // }
  // z3::expr op1 = __z3_context.bv_val((uint64_t)info->op1.i, size);
  // if (info->l1 >= CONST_OFFSET) {
  //   op1 = serialize(info->l1, deps).simplify();
  // } else if (info->size == 1) {
  //   op1 = __z3_context.bool_val(info->op1.i == 1);
  // }
  // if (info->op == Concat && info->l2 == 0) {
  //   assert(info->l1 >= CONST_OFFSET);
  //   size = info->size - get_label_info(info->l1)->size;
  // }
  // z3::expr op2 = __z3_context.bv_val((uint64_t)info->op2.i, size);
  // if (info->l2 >= CONST_OFFSET) {
  //   std::unordered_set<u32> deps2;
  //   op2 = serialize(info->l2, deps2).simplify();
  //   deps.insert(deps2.begin(),deps2.end());
  // } else if (info->size == 1) {
  //   op2 = __z3_context.bool_val(info->op2.i == 1);
  // }
  // update tree_size
  tsize_cache[label] = tsize_cache[info->l1] + tsize_cache[info->l2];

  switch((info->op & 0xff)) {
    // llvm doesn't distinguish between logical and bitwise and/or/xor
    case And:     return cache_expr(label, info->size != 1 ? (op1 & op2) : (op1 && op2), deps);
    case Or:      return cache_expr(label, info->size != 1 ? (op1 | op2) : (op1 || op2), deps);
    case Xor:     return cache_expr(label, op1 ^ op2, deps);
    case Shl:     return cache_expr(label, z3::shl(op1, op2), deps);
    case LShr:    return cache_expr(label, z3::lshr(op1, op2), deps);
    case AShr:    return cache_expr(label, z3::ashr(op1, op2), deps);
    case Add:     return cache_expr(label, op1 + op2, deps);
    case Sub:     return cache_expr(label, op1 - op2, deps);
    case Mul:     return cache_expr(label, op1 * op2, deps);
    case UDiv:    return cache_expr(label, z3::udiv(op1, op2), deps);
    case SDiv:    return cache_expr(label, op1 / op2, deps);
    case URem:    return cache_expr(label, z3::urem(op1, op2), deps);
    case SRem:    return cache_expr(label, z3::srem(op1, op2), deps);
    // relational
    case ICmp:    return cache_expr(label, get_cmd(op1, op2, info->op >> 8), deps);
    // concat
    case Concat:  return cache_expr(label, z3::concat(op2, op1), deps); // little endian
    default:
      AOUT("FATAL: unsupported op: %u\n", info->op);
      throw z3::exception("unsupported operator");
      break;
  }
  // should never reach here
  Die();
}

static z3::expr serialize_simple(dfsan_label label) {
  if (label < CONST_OFFSET || label == kInitializingLabel) {
    AOUT("WARNING: invalid label: %d\n", label);
    throw z3::exception("invalid label");
  }

  dfsan_label_info *info = get_label_info(label);
  // if (print_debug) {
  //   AOUT("%u = (l1:%u, l2:%u, op:%u, size:%u, op1:%llu, op2:%llu)\n",
  //         label, info->l1, info->l2, info->op, info->size, info->op1.i, info->op2.i);
  // }

  auto expr_itr = expr_cache.find(label);
  if (expr_itr != expr_cache.end()) {
    auto deps_itr = deps_cache.find(label);
    return expr_itr->second;
  }

  // special ops
  if (info->op == 0) {
    // input
    z3::symbol symbol = __z3_context.int_symbol(info->op1.i);
    z3::sort sort = __z3_context.bv_sort(8);
    tsize_cache[label] = 1; // lazy init
    // fprintf(stderr, "input offset 0x%lx\n", info->op1.i);
    // caching is not super helpful
    return __z3_context.constant(symbol, sort);
  } else if (info->op == Load) {
    u64 offset = get_label_info(info->l1)->op1.i;
    z3::symbol symbol = __z3_context.int_symbol(offset);
    z3::sort sort = __z3_context.bv_sort(8);
    z3::expr out = __z3_context.constant(symbol, sort);
    for (u32 i = 1; i < info->l2; i++) {
      // fprintf(stderr, "offset + i 0x%lx\n", offset+i);
      symbol = __z3_context.int_symbol(offset + i);
      out = z3::concat(__z3_context.constant(symbol, sort), out);
    }
    tsize_cache[label] = 1; // lazy init
    return cache_expr_only(label, out);
  } else if (info->op == ZExt) {
    // Z3_mk_zero_ext(g_context, bits, expr)
    z3::expr base = serialize_simple(info->l1);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr_only(label, z3::zext(base, info->op2.i));
  } else if (info->op == SExt) {
    z3::expr base = serialize_simple(info->l1);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr_only(label, z3::sext(base, info->op2.i));
  } else if (info->op == Trunc) {
    z3::expr base = serialize_simple(info->l1);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr_only(label, base.extract(info->op2.i - 1, 0));
  } else if (info->op == Extract) {
    z3::expr base = serialize_simple(info->l1);
    assert(base.get_sort().bv_size() > info->op2.i);
    assert(base.get_sort().bv_size() > info->op1.i);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    // Z3_mk_extract(g_context, first_bit, last_bit, expr)
    return cache_expr_only(label, base.extract(info->op1.i, info->op2.i));
  } else if (info->op == Not) {
    if (info->l2 == 0/* || info->size != 1*/) {
      throw z3::exception("invalid Not operation");
    }
    z3::expr e = serialize_simple(info->l2);
    tsize_cache[label] = tsize_cache[info->l2]; // lazy init
    if (!e.is_bool()) {
      // bvnot
      return cache_expr_only(label, ~e);
    } else {
      throw z3::exception("Only LNot should be recorded");
      // return cache_expr(label, !e, deps);
    }
  } else if (info->op == Neg) {
    if (info->l2 == 0) {
      throw z3::exception("invalid Neg predicate");
    }
    z3::expr e = serialize_simple(info->l2);
    tsize_cache[label] = tsize_cache[info->l2]; // lazy init
    return cache_expr_only(label, -e);
  }
  // higher-order
  else if (info->op == fmemcmp) {
    z3::expr op1 = (info->l1 >= CONST_OFFSET) ? serialize_simple(info->l1) :
                   read_concrete(label, info->size); // memcmp size in bytes
    if (info->l2 < CONST_OFFSET) {
      throw z3::exception("invalid memcmp operand2");
    }
    z3::expr op2 = serialize_simple(info->l2);
    tsize_cache[label] = 1; // lazy init
    z3::expr e = z3::ite(op1 == op2, __z3_context.bv_val(0, 32),
                                     __z3_context.bv_val(1, 32));
    return cache_expr_only(label, e);
  } else if (info->op == fsize) {
    // file size
    z3::symbol symbol = __z3_context.str_symbol("fsize");
    z3::sort sort = __z3_context.bv_sort(info->size);
    z3::expr base = __z3_context.constant(symbol, sort);
    tsize_cache[label] = 1; // lazy init
    // don't cache because of deps
    if (info->op1.i) {
      // minus the offset stored in op1
      z3::expr offset = __z3_context.bv_val((uint64_t)info->op1.i, info->size);
      return base - offset;
    } else {
      return base;
    }
  } else if (info->op == Ite) {
    // Covert bool expression to bv.
    z3::expr op1 = serialize_simple(info->l1);
    if (op1.is_bool()) {
      z3::expr e = z3::ite(op1, __z3_context.bv_val(1, 1),
                                     __z3_context.bv_val(0, 1));
      assert(info->size > 1);
      e = z3::zext(e, info->size - 1);
      tsize_cache[label] = tsize_cache[info->l1]; // lazy init
      return cache_expr_only(label, e);
    } else {
      throw z3::exception("invalid Ite operation(for bool expr only)");
    }
  } else if (info->op == Equal) {
    // try an alternative symbolic address.
    // build an equal expression for a symbolic address.
    z3::expr e = serialize_simple(info->l1) == \
                 __z3_context.bv_val((uint64_t)info->op1.i, info->size);
    tsize_cache[label] = tsize_cache[info->l1]; // lazy init
    return cache_expr_only(label, e);
  }

  // common ops
  u8 size = info->size;
  if (info->l1 == 0) {
    if (info->op == Concat) {
      // size = 8;
      size = info->size - get_label_info(info->l2)->size;
    } else {
      size = get_label_info(info->l2)->size;
    }
  }

  z3::expr op1 = __z3_context.bv_val((uint64_t)info->op1.i, size);
  if (info->l1 >= CONST_OFFSET) {
    op1 = serialize_simple(info->l1).simplify();
  }

  if (info->l2 == 0) {
    if (info->op == Concat) {
      // size = 8;
      size = info->size - get_label_info(info->l1)->size;
    } else {
      size = get_label_info(info->l1)->size;
    }
  }

  z3::expr op2 = __z3_context.bv_val((uint64_t)info->op2.i, size);
  if (info->l2 >= CONST_OFFSET) {
    std::unordered_set<u32> deps2;
    op2 = serialize_simple(info->l2).simplify();
  }
  // AOUT("op %ld: op1 sort size = %d, op2 sort size = %d\n", info->op, op1.get_sort().bv_size(), op2.get_sort().bv_size());

  // size for concat is a bit complicated ...
  // if (info->op == Concat && info->l1 == 0) {
  //   assert(info->l2 >= CONST_OFFSET);
  //   size = info->size - get_label_info(info->l2)->size;
  // }
  // z3::expr op1 = __z3_context.bv_val((uint64_t)info->op1.i, size);
  // if (info->l1 >= CONST_OFFSET) {
  //   op1 = serialize(info->l1, deps).simplify();
  // } else if (info->size == 1) {
  //   op1 = __z3_context.bool_val(info->op1.i == 1);
  // }
  // if (info->op == Concat && info->l2 == 0) {
  //   assert(info->l1 >= CONST_OFFSET);
  //   size = info->size - get_label_info(info->l1)->size;
  // }
  // z3::expr op2 = __z3_context.bv_val((uint64_t)info->op2.i, size);
  // if (info->l2 >= CONST_OFFSET) {
  //   std::unordered_set<u32> deps2;
  //   op2 = serialize(info->l2, deps2).simplify();
  //   deps.insert(deps2.begin(),deps2.end());
  // } else if (info->size == 1) {
  //   op2 = __z3_context.bool_val(info->op2.i == 1);
  // }
  // update tree_size
  tsize_cache[label] = tsize_cache[info->l1] + tsize_cache[info->l2];

  switch((info->op & 0xff)) {
    // llvm doesn't distinguish between logical and bitwise and/or/xor
    case And:     return cache_expr_only(label, info->size != 1 ? (op1 & op2) : (op1 && op2));
    case Or:      return cache_expr_only(label, info->size != 1 ? (op1 | op2) : (op1 || op2));
    case Xor:     return cache_expr_only(label, op1 ^ op2);
    case Shl:     return cache_expr_only(label, z3::shl(op1, op2));
    case LShr:    return cache_expr_only(label, z3::lshr(op1, op2));
    case AShr:    return cache_expr_only(label, z3::ashr(op1, op2));
    case Add:     return cache_expr_only(label, op1 + op2);
    case Sub:     return cache_expr_only(label, op1 - op2);
    case Mul:     return cache_expr_only(label, op1 * op2);
    case UDiv:    return cache_expr_only(label, z3::udiv(op1, op2));
    case SDiv:    return cache_expr_only(label, op1 / op2);
    case URem:    return cache_expr_only(label, z3::urem(op1, op2));
    case SRem:    return cache_expr_only(label, z3::srem(op1, op2));
    // relational
    case ICmp:    return cache_expr_only(label, get_cmd(op1, op2, info->op >> 8));
    // concat
    case Concat:  return cache_expr_only(label, z3::concat(op2, op1)); // little endian
    default:
      AOUT("FATAL: unsupported op: %u\n", info->op);
      throw z3::exception("unsupported operator");
      break;
  }
  // should never reach here
  Die();
}

static inline void cache_expr_deps(dfsan_label label, std::unordered_set<u32> &deps) {
  deps_cache.insert({label, deps});
}

// iteratively get all input deps of the current label
static void _get_input_deps(dfsan_label label, std::unordered_set<u32> &deps) {
  if (label < CONST_OFFSET || label == kInitializingLabel) {
    throw z3::exception("invalid label");
  }

  dfsan_label_info *info = get_label_info(label);

  auto deps_itr = deps_cache.find(label);
  if (deps_itr != deps_cache.end()) {
    deps.insert(deps_itr->second.begin(), deps_itr->second.end());
    return;
  }

  // special ops
  if (info->op == 0) {
    deps.insert(info->op1.i);
    return;
  } else if (info->op == Load) {
    uint64_t offset = get_label_info(info->l1)->op1.i;
    deps.insert(offset);
    for (uint32_t i = 1; i < info->l2; i++) {
      deps.insert(offset + i);
    }
    cache_expr_deps(label, deps);
    return;
  } else if (info->op == ZExt || info->op == SExt || info->op == Trunc || info->op == Extract) {
    _get_input_deps(info->l1, deps);
    cache_expr_deps(label, deps);
    return;
  } else if (info->op == Not || info->op == Neg) {
    _get_input_deps(info->l2, deps);
    cache_expr_deps(label, deps);
    return;
  } else if (info->op == Ite) {
    _get_input_deps(info->l1, deps);
    cache_expr_deps(label, deps);
    return;
  } else if (info->op == Equal) {
    _get_input_deps(info->l1, deps);
    cache_expr_deps(label, deps);
    return;
  }
  

  // common ops
  if (info->l1 >= CONST_OFFSET) {
    _get_input_deps(info->l1, deps);
  }
  if (info->l2 >= CONST_OFFSET) {
    std::unordered_set<uint32_t> deps2;
    _get_input_deps(info->l2, deps2);
    deps.insert(deps2.begin(),deps2.end());
  }
  cache_expr_deps(label, deps);
  return;
}

// static void collect_input_deps(dfsan_label label, u8 r, bool add_nested, uint64_t addr) {
//   std::unordered_set<dfsan_label> inputs;
//   _get_input_deps(label, inputs);

//   std::vector<dfsan_label> worklist;
//   worklist.insert(worklist.begin(), inputs.begin(), inputs.end());
//   while (!worklist.empty()) {
//     auto off = worklist.back();
//     worklist.pop_back();

//     auto deps = get_branch_dep(off);
//     if (deps != nullptr) {
//       for (auto i : deps->input_deps) {
//         if (inputs.insert(i).second)
//           worklist.push_back(i);
//       }
//     }
//   }

//   for (auto off : inputs) {
//     auto c = get_branch_dep(off);
//     if (c == nullptr) {
//       c = new branch_dep_t();
//       // fprintf(stderr, "new branch dep at offset 0x%lx\n", off);
//       set_branch_dep(off, c);
//     }
//     if (c == nullptr) {
//       AOUT("WARNING: out of memory\n");
//     } else {
//       c->input_deps.insert(inputs.begin(), inputs.end());
//       c->label_tuples.insert(std::make_tuple(label, r));
//     }
//   }

// }

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
  // AOUT("generate #%d output\n", __current_index - 1);

  // from qsym
  unsigned num_constants = m.num_consts();
  for (unsigned i = 0; i < num_constants; i++) {
    z3::func_decl decl = m.get_const_decl(i);
    z3::expr e = m.get_const_interp(decl);
    z3::symbol name = decl.name();

    if (name.kind() == Z3_INT_SYMBOL) {
      int offset = name.to_int();
      u8 value = (u8)e.get_numeral_int();
      // fprintf(stderr, "offset %d = %x\n", offset, value);
      lseek(fd, offset, SEEK_SET);
      write(fd, &value, sizeof(value));
    } else { // string symbol
      if (!name.str().compare("fsize")) {
        off_t size = (off_t)e.get_numeral_int64();
        if (size > input_size) { // grow
          lseek(fd, size, SEEK_SET);
          u8 dummy = 0;
          write(fd, &dummy, sizeof(dummy));
        } else {
          AOUT("truncate file to %ld\n", size);
          ftruncate(fd, size);
        }
        // don't remember size constraints
        throw z3::exception("skip fsize constraints");
      }
    }
  }

  close(fd);
}
int sym_count = 0;

// assumes under try-catch and the global solver __z3_solver already has nested context
static bool __solve_expr(z3::expr &e) {
  bool ret = false;
  // set up local optmistic solver
  z3::solver opt_solver = z3::solver(__z3_context, "QF_BV");
  opt_solver.set("timeout", 1000U); // follow timeout of symcc
  opt_solver.add(e);
  // fprintf(stderr, "\n%s\n", __z3_solver.to_smt2().c_str());
  // return false;
  z3::check_result res = opt_solver.check();
  if (res == z3::sat) {
    // optimistic sat, check nested
    __z3_solver.push();
    __z3_solver.add(e);
    // if (sym_count++ < 1000)
      // fprintf(stderr, "\n%s\n", __z3_solver.to_smt2().c_str());
      // return false;
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
    // reset
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

    // AOUT("\n%s\n", __z3_solver.to_smt2().c_str());
    // AOUT("sym branch: 0x%lx constraint: %s\n", addr, cond.to_string().c_str());
    // return;
    // collect additional input deps
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
    // 2. add constraints
    expr_set_t added;
    for (auto off : inputs) {
      // AOUT("adding offset 0x%lx\n", off);
      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        for (auto &expr : deps->expr_deps) {
          if (added.insert(expr).second) {
            //AOUT("adding expr: %s\n", expr.to_string().c_str());
            __z3_solver.add(expr);
          }
        }
      }
    }
    // fprintf(stderr, "%s\n", __z3_solver.to_smt2().c_str());
    // fprintf(stderr, "%s\n", cond.to_string().c_str());
    // return;
    // assert(__z3_solver.check() == z3::sat);
    // fprintf(stderr, "\n%s\n", __z3_solver.to_smt2().c_str());
      // fprintf(stderr, "interesting branch 0x%lx\n", addr & 0xfff);
    // z3::expr e = cond;
    // if (r) {
    //   e = !cond;
    // }
    z3::expr e = (cond != result);

    if (__solve_expr(e)) {
      // AOUT("branch solved\n");
    } else {
      // AOUT("branch not solvable @%p\n", addr);
      //AOUT("\n%s\n", __z3_solver.to_smt2().c_str());
      //AOUT("  tree_size = %d", __dfsan_label_info[label].tree_size);
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
#if 0
static void __solve_last_cond(dfsan_label label, u8 r, std::unordered_set<dfsan_label> &inputs) {

  // z3::expr result = __z3_context.bool_val(r != 0);

  bool pushed = false;
  try {
    // std::unordered_set<dfsan_label> inputs;
    z3::expr cond = serialize(label, inputs).simplify();

    // AOUT("\n%s\n", __z3_solver.to_smt2().c_str());
    // AOUT("sym branch: 0x%lx constraint: %s\n", addr, cond.to_string().c_str());
    // return;
    // collect additional input deps
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
    
    // fprintf(stderr, "branch: 0x%lx \n", addr);
    // 2. add constraints
    dfsan_label dep_label = 0;
    u8 dep_r = 0;
    for (auto off : inputs) {
      // AOUT("adding offset 0x%lx\n", off);
      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        for (auto &expr : deps->label_tuples) {
          if (added_label.insert(expr).second) {
            dep_label = std::get<0>(expr);
            dep_r = std::get<1>(expr);
            // fprintf(stderr, "unfloding label tuple %d %d offset %d\n", dep_label, dep_r, off);
            z3::expr dep_cond = serialize_simple(dep_label).simplify();
            if (dep_r) {
              dep_cond = !dep_cond;
            }
            // fprintf(stderr, "dep_cond: %s\n", dep_cond.to_string().c_str());
            __z3_solver.add(dep_cond);
            // __solve_last_cond(std::get<0>(expr), std::get<1>(expr));
          }
        }
      }
    }
    // fprintf(stderr, "%s\n", __z3_solver.to_smt2().c_str());
    // fprintf(stderr, "%s\n", cond.to_string().c_str());
    // return;
    // assert(__z3_solver.check() == z3::sat);
    // fprintf(stderr, "\n%s\n", __z3_solver.to_smt2().c_str());
      // fprintf(stderr, "interesting branch 0x%lx\n", addr & 0xfff);
    z3::expr e = cond;
    if (r) {
      e = !cond;
    }
    __z3_solver.add(e);
    // z3::expr e = (cond != result);

  } catch (z3::exception e) {
    AOUT("WARNING: solving error: %s @ label %d\n", e.msg(), label);
  }

}

static void solve_last_cond(dfsan_label label, u8 r, bool add_nested, uint64_t addr) {
  added_label.clear();
  __z3_solver.reset();
  __z3_solver.set("timeout", 5000U);
  // fprintf(stderr, "solving label: 0x%d", label);
  // recursively add all constraints from dependencies
  std::unordered_set<dfsan_label> inputs;
  __solve_last_cond(label, r, inputs);
  for (auto off : inputs) {
    fprintf(stderr, "offset 0x%x\n", off);
  }
  // fprintf(stderr, "%s\n", __z3_solver.to_smt2().c_str());
}
#endif
// assumes under try-catch and the global solver already has context
static void __solve_gep(z3::expr &index, uint64_t lb, uint64_t ub, uint64_t step, void *addr) {

  // enumerate indices
  for (uint64_t i = lb; i < ub; i += step) {
    z3::expr idx = __z3_context.bv_val(i, 64);
    z3::expr e = (index == idx);
    if (__solve_expr(e))
      AOUT("\tindex == %ld feasible\n", i);
  }

  // check feasibility for OOB
  // upper bound
  z3::expr u = __z3_context.bv_val(ub, 64);
  z3::expr e = z3::uge(index, u);
  if (__solve_expr(e))
    AOUT("\tindex >= %ld solved @%p\n", ub, addr);
  else
    AOUT("\tindex >= %ld not possible\n", ub);

  // lower bound
  if (lb == 0) {
    e = (index < 0);
  } else {
    z3::expr l = __z3_context.bv_val(lb, 64);
    e = z3::ult(index, l);
  }
  if (__solve_expr(e))
    AOUT("\tindex < %ld solved @%p\n", lb, addr);
  else
    AOUT("\tindex < %ld not possible\n", lb);
}

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

    // collect additional input deps
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

    // set up the global solver with nested constraints
    __z3_solver.reset();
    __z3_solver.set("timeout", 5000U);
    expr_set_t added;
    for (auto off : inputs) {
      auto deps = get_branch_dep(off);
      if (deps != nullptr) {
        // for (auto &expr : deps->expr_deps) {
        //   if (added.insert(expr).second) {
        //     __z3_solver.add(expr);
        //   }
        // }
      }
    }
    assert(__z3_solver.check() == z3::sat);

    // first, check against fixed array bounds if available
    z3::expr idx = z3::zext(i, 64 - size);
    if (num_elems > 0) {
      __solve_gep(idx, 0, num_elems, 1, addr);
    } else {
      dfsan_label_info *bounds = get_label_info(ptr_label);
      // if the array is not with fixed size, check bound info
      if (bounds->op == Alloca) {
        z3::expr es = __z3_context.bv_val(elem_size, 64);
        z3::expr co = __z3_context.bv_val(current_offset, 64);
        if (bounds->l2 == 0) {
          // only perform index enumeration and bound check
          // when the size of the buffer is fixed
          z3::expr p = __z3_context.bv_val(ptr, 64);
          z3::expr np = idx * es + co + p;
          __solve_gep(np, (uint64_t)bounds->op1.i, (uint64_t)bounds->op2.i, elem_size, addr);
        } else {
          // if the buffer size is input-dependent (not fixed)
          // check if over flow is possible
          std::unordered_set<dfsan_label> dummy;
          z3::expr bs = serialize(bounds->l2, dummy); // size label
          if (bounds->l1) {
            dummy.clear();
            z3::expr be = serialize(bounds->l1, dummy); // elements label
            bs = bs * be;
          }
          z3::expr e = z3::ugt(idx * es * co, bs);
          if (__solve_expr(e))
            AOUT("index >= buffer size feasible @%p\n", addr);
        }
      }
    }

    // always preserve
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
        // c->expr_deps.insert(i == r);
      }
    }

  } catch (z3::exception e) {
    AOUT("WARNING: index solving error: %s @%p\n", e.msg(), __builtin_return_address(0));
  }

}

int main(int argc, char* const argv[]) {
  char *program = argv[1];
  char *target = argv[2];

  // setup output dir
  char *options = getenv("TAINT_OPTIONS");
  // char *output = strstr(options, "output_dir=");
  __output_dir = getenv("SYMCC_OUTPUT_DIR");
  // if (output) {
  //   output += 11; // skip "output_dir="
  //   char *end = strchr(output, ':'); // try ':' first, then ' '
  //   if (end == NULL) end = strchr(output, ' ');
  //   size_t n = end == NULL? strlen(output) : (size_t)(end - output);
  //   __output_dir = strndup(output, n);
  // }

  // load input file from symcc env.
  char *input = getenv("SYMCC_INPUT_FILE");
  if (input == NULL) {
      fprintf(stderr, "ERROR: Cannot read SYMCC_INPUT_FILE environment variable! Exiting...\n");
      exit(1);
  }
  if (strcmp(input, "stdin") != 0) {
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
  }

  // setup shmem and pipe
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

  // prepare the env and fork
  int length = snprintf(NULL, 0, "taint_file=\"%s\":shm_id=%d:pipe_fd=%d:debug=0",
                        input, shmid, pipefds[1]);
  options = (char *)malloc(length + 1);
  snprintf(options, length + 1, "taint_file=\"%s\":shm_id=%d:pipe_fd=%d:debug=0",
           input, shmid, pipefds[1]);
  
  int pid = fork();
  if (pid < 0) {
    fprintf(stderr, "Failed to fork: %s\n", strerror(errno));
    exit(1);
  }

  if (pid == 0) {
    close(pipefds[0]); // close the read fd
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

  // get bitmap file from env SYMCC_AFL_COVERAGE_MAP
  // so it's compatibale with symcc driver.
  const char* bitmap = std::getenv("SYMCC_AFL_COVERAGE_MAP");
  if (!bitmap) {
    fprintf(stderr, "Failed to get bitmap file from env\n");
    exit(1);
  }
  _trace = new AflTraceMap(bitmap);
  // _trace(bitmap);

  pipeMsg msg;
  gep_msg gmsg;
  dfsan_label_info *info;
  size_t msg_size;
  memcmp_msg *mmsg = nullptr;

  std::vector<std::pair<uint32_t, uint64_t>> branch_label;
  // size_t branch_size = 0;
  // dfsan_label last_label = 0;
  // uint64_t last_pc = 0;

  while (read(pipefds[0], &msg, sizeof(msg)) > 0) {
    // solve constraints
    switch (msg.msg_type) {
      case cond_type:
        // info = get_label_info(msg.label);
        // last_label = msg.label;
        // last_pc = msg.id;
        // fprintf(stderr, "sym branch: 0x%lx %s\n", msg.id, msg.result? "taken":"not taken");
        if (_trace->isInterestingBranch(msg.id, msg.result)) {
          // branch_label.push_back({msg.id, msg.label});
          // branch_size++;
          // AOUT("interesting branch: 0x%lx, %s\n", msg.id, msg.result? "taken":"not taken");
          __solve_cond(msg.label, msg.result, msg.flags & F_ADD_CONS, msg.id);
          
          // collect_input_deps(msg.label, msg.result, msg.flags & F_ADD_CONS, msg.id);
        
        }
        break;
      case gep_type:
        if (read(pipefds[0], &gmsg, sizeof(gmsg)) != sizeof(gmsg)) {
          fprintf(stderr, "Failed to receive gep msg: %s\n", strerror(errno));
          break;
        }
        // double check
        if (msg.label != gmsg.index_label) {
          fprintf(stderr, "Incorrect gep msg: %d vs %d\n", msg.label, gmsg.index_label);
          break;
        }
        __handle_gep(gmsg.ptr_label, gmsg.ptr, gmsg.index_label, gmsg.index,
                     gmsg.num_elems, gmsg.elem_size, gmsg.current_offset, (void*)msg.addr);
        break;
      case memcmp_type:
        info = get_label_info(msg.label);
        // if both operands are symbolic, no content to be read
        if (info->l1 != CONST_LABEL && info->l2 != CONST_LABEL)
          break;
        msg_size = sizeof(memcmp_msg) + msg.result;
        mmsg = (memcmp_msg*)malloc(msg_size); // not freed until terminate
        if (read(pipefds[0], mmsg, msg_size) != msg_size) {
          fprintf(stderr, "Failed to receive memcmp msg: %s\n", strerror(errno));
          break;
        }
        // double check
        if (msg.label != mmsg->label) {
          fprintf(stderr, "Incorrect memcmp msg: %d vs %d\n", msg.label, mmsg->label);
          break;
        }
        // save the content
        memcmp_cache[msg.label] = mmsg;
        break;
      case fsize_type:
        break;
      default:
        break;
    }
  }

  // wait for child and check if segmenation fault
  int status;
  waitpid(pid, &status, 0);
  if (WIFSIGNALED(status)) {
    // fprintf(stderr, "Child terminated by signal: %d\n", WTERMSIG(status));
    // int i = 0;
    // for (auto &b : branch_label) {
      // i++;
      // if (branch_size - i > 21) continue;
      // fprintf(stderr, "pc 0x%x\n", b.first);
      // fprintf(stderr, "0x%x\n", b.second);
      // __solve_cond_print(b.second, 0, 1, b.first);
    // }
    // solve_last_cond(last_label, 0, 1, last_pc);
  }
  // wait(NULL);
  exit(0);
}
