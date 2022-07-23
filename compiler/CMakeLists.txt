include_directories(../lib/include)

find_library(LibCompiler PATHS "../lib")

file (GLOB_RECURSE SOURCES *.cpp)
add_executable(Compiler "${SOURCES}")
target_link_libraries(Compiler PUBLIC LibCompiler)