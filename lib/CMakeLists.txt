execute_process (COMMAND bash -c "flex ${CMAKE_SOURCE_DIR}/lex/grammar.lex")

# Also add header fiels for conveniencein QtCreator.
file (GLOB_RECURSE SOURCES *.c *.h)
add_library(
  weak_compiler SHARED
  "${SOURCES}"
  # This comes from build directory and shouldn't be added to git history.
  ${CMAKE_BINARY_DIR}/lex.yy.c
)

# This is to play with compile time optimization a little.
# set_property(TARGET weak_compiler PROPERTY RULE_LAUNCH_COMPILE "${CMAKE_COMMAND} -E time")

target_link_libraries(weak_compiler PRIVATE fl)
target_compile_options(weak_compiler PRIVATE -Wall -Wextra -Wpedantic -fPIC -flto -O3)

if (WEAK_COMPILER_SANITIZE)
  message(STATUS "Building the compiler library with sanitizer flags")
  set(weak_san_flags "\
    -fsanitize=address -fno-omit-frame-pointer\
    -fsanitize=undefined -fno-sanitize-recover=all\
    -fsanitize-address-use-after-scope"
  )

  if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    string(APPEND weak_san_flags " -fsanitize=cfi -fvisibility=default -flto")
  endif()

  if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    string(APPEND weak_san_flags " -fanalyzer")
  endif()

  add_compile_options(weak_san_flags)
  link_libraries(weak_san_flags)
endif()

include_directories(include)
