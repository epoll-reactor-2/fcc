include_directories(../lib/include)
add_executable(Compiler Compiler.cpp)
target_link_libraries(Compiler PRIVATE WeakCompiler)