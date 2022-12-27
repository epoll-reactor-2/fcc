cmake_minimum_required(VERSION 3.9)

project(
  weak_compiler
  DESCRIPTION "The compiler for unnamed programming language"
  HOMEPAGE_URL "https://gitlab.com/epoll-reactor/weak_compiler"
  LANGUAGES C
)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD 11)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_THREAD_PREFER_PTHREAD ON)
set(THREADS_PREFER_PTHREAD_FLAG ON)

enable_testing()

add_subdirectory(lib)
add_subdirectory(tests)
add_subdirectory(compiler)
