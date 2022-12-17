# Also add header fiels for conveniencein QtCreator.
file (GLOB_RECURSE SOURCES *.cpp *.h)
add_library(WeakCompiler SHARED "${SOURCES}")

find_package(LLVM REQUIRED CONFIG)

message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
message(STATUS "Using LLVMConfig.cmake from ${LLVM_DIR}")

include_directories(${LLVM_INCLUDE_DIRS})
add_definitions(${LLVM_DEFINITIONS})
add_definitions(${LLVM_DEFINITIONS_LIST})
separate_arguments(LLVM_DEFINITIONS_LIST NATIVE_COMMAND ${LLVM_DEFINITIONS})
llvm_map_components_to_libnames(llvm_libs ${LLVM_TARGETS_TO_BUILD} support core irreader)

target_link_libraries(WeakCompiler PRIVATE ${llvm_libs})
target_compile_options(WeakCompiler PRIVATE -Wall -Wextra -Wpedantic -fPIC -flto -O3)

if (WEAK_COMPILER_SANITIZE)
  message(STATUS "Building the compiler library with sanitizer flags")
  set(SanFlags "\
    -fsanitize=address -fno-omit-frame-pointer\
    -fsanitize=undefined -fno-sanitize-recover=all\
    -fsanitize-address-use-after-scope"
  )
  message(STATUS "Sanitizer flags: ${SanFlags}")

  if(CMAKE_CXX_COMPILER_ID STREQUAL "Clang")
    string(APPEND SanFlags " -fsanitize=cfi -fvisibility=default -flto")
  endif()

  if (CMAKE_CXX_COMPILER_ID STREQUAL "GNU")
    string(APPEND SanFlags " -fanalyzer")
  endif()

  add_compile_options(SanFlags)
  link_libraries(SanFlags)
endif()

include_directories(Compiler PUBLIC include)