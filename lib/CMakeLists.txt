execute_process (COMMAND bash -c "flex ${CMAKE_SOURCE_DIR}/lex/grammar.lex")

# Also add header fiels for conveniencein QtCreator.
file (GLOB_RECURSE SOURCES *.c *.h)
add_library(
  weak_compiler SHARED
  "${SOURCES}"
  # This comes from build directory and shouldn't be added to git history.
  ${CMAKE_BINARY_DIR}/lex.yy.c
)

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake from ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
llvm_map_components_to_libnames(llvm_libs ${LLVM_TARGETS_TO_BUILD} support core irreader)

target_link_libraries(weak_compiler PRIVATE ${llvm_libs} fl)
target_compile_options(weak_compiler PRIVATE -Wall -Wextra -Wpedantic -fPIC -flto -O3)

if (WEAK_COMPILER_SANITIZE)
  message(STATUS "Building the compiler library with sanitizer flags")
  set(weak_san_flags "\
    -fsanitize=address -fno-omit-frame-pointer\
    -fsanitize=undefined -fno-sanitize-recover=all\
    -fsanitize-address-use-after-scope"
  )
  message(STATUS "Sanitizer flags: ${weak_san_flags}")

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
