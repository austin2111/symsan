cmake_minimum_required(VERSION 3.4)

project(symsan VERSION 1.2.2 LANGUAGES C CXX ASM)

find_package(LLVM 12 REQUIRED CONFIG)

if (LLVM_FOUND)
    message(STATUS "LLVM_VERSION_MAJOR: ${LLVM_VERSION_MAJOR}")
    message(STATUS "LLVM_VERSION_MINOR: ${LLVM_VERSION_MINOR}")
    message(STATUS "LLVM_VERSION_PATCH: ${LLVM_VERSION_PATCH}")
else()
    message(FATAL_ERROR "You haven't install LLVM !")
endif()

if (NOT TARGET LLVMPassConfig)
    add_library(LLVMPassConfig INTERFACE IMPORTED)
    set_target_properties(LLVMPassConfig PROPERTIES
        INTERFACE_COMPILE_OPTIONS "-fno-rtti" #-fpic
        INTERFACE_INCLUDE_DIRECTORIES "${LLVM_INCLUDE_DIRS}"
        INTERFACE_LINK_DIRECTORIES "${LLVM_LIBRARY_DIRS}"
        INTERFACE_COMPILE_DEFINITIONS "LLVM_VERSION_MAJOR=${LLVM_VERSION_MAJOR};LLVM_VERSION_MINOR=${LLVM_VERSION_MINOR};"
        # INTERFACE_LINK_OPTIONS "-Wl,-znodelete"
    )
endif()

option(SYMSAN_DEBUG  "Enable dfsan debug flag" OFF)
set(DFSAN_FLAGS_INC "${CMAKE_CURRENT_SOURCE_DIR}/runtime/dfsan/dfsan_flags.inc")

file(READ "${DFSAN_FLAGS_INC}" DFSAN_FLAGS_CONTENTS)

if(SYMSAN_DEBUG)
  set(DEBUG_VALUE "true")
else()
  set(DEBUG_VALUE "false")
endif()

string(REGEX REPLACE
  "DFSAN_FLAG\\(bool, *debug, *(true|false),"
  "DFSAN_FLAG(bool, debug, ${DEBUG_VALUE},"
  DFSAN_FLAGS_CONTENTS
  "${DFSAN_FLAGS_CONTENTS}")

file(WRITE "${DFSAN_FLAGS_INC}" "${DFSAN_FLAGS_CONTENTS}")

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})

include_directories(include)

set(SYMSAN_BIN_DIR "bin")
set(SYMSAN_LIB_DIR "lib/symsan")

add_subdirectory(compiler)
add_subdirectory(instrumentation)
add_subdirectory(runtime)
add_subdirectory(wrappers)
add_subdirectory(solvers)
add_subdirectory(driver)
add_subdirectory(tests)
add_subdirectory(libcxx)
