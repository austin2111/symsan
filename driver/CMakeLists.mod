set(CMAKE_POSITION_INDEPENDENT_CODE ON)
set(CMAKE_CXX_STANDARD 14)

set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -stdlib=libc++ -g")

## simple driver for testing out-of-process solving
add_executable(FGTest fgtest.cpp afl_trace_map.cpp third_party/xxhash/xxhash.cpp)
set_target_properties(FGTest PROPERTIES OUTPUT_NAME "fgtest")
target_include_directories(FGTest PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/../runtime
)
target_link_options(FGTest PRIVATE "-lz3")

option(SYMSAN_DEBUG  "Enable dfsan debug flag" OFF)
set(DFSAN_FLAGS_INC "${CMAKE_CURRENT_SOURCE_DIR}/dfsan_flags.inc")
#set(GENERATED_DFSAN_FLAGS_INC "${CMAKE_CURRENT_BINARY_DIR}/dfsan_flags.inc")

file(READ "${DFSAN_FLAGS_INC}" DFSAN_FLAGS_CONTENTS)

if(SYMSAN_DEBUG)
  string(REGEX REPLACE
    "DFSAN_FLAG\\(bool, *debug, *false,"
    "DFSAN_FLAG(bool, debug, true,"
    DFSAN_FLAGS_CONTENTS
    "${DFSAN_FLAGS_CONTENTS}")
endif()

file(WRITE "${DFSAN_FLAGS_INC}" "${DFSAN_FLAGS_CONTENTS}")
#include_directories(${CMAKE_CURRENT_BINARY_DIR})

install (TARGETS FGTest DESTINATION ${SYMSAN_BIN_DIR})
