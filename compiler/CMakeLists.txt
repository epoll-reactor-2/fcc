include_directories(../lib/include)
add_executable(compiler compiler.c)
target_link_libraries(compiler PRIVATE weak_compiler)
