include_directories(../lib/include)
include_directories(../tests)
include_directories(../tests/utils)

function(add_compiler_test exec_file path)
  message(STATUS "Adding test ${exec_file}")
  add_executable(${exec_file} ${path})
  target_link_libraries (${exec_file} PRIVATE weak_compiler)
  target_compile_options(${exec_file} PRIVATE -fPIC -flto)
  add_test(NAME ${exec_file} COMMAND ${exec_file})
endfunction()

function(delete_old_inputs)
  file(GLOB_RECURSE files "${CMAKE_CURRENT_BINARY_DIR}/*.wl")
  foreach (file ${files})
    file(REMOVE ${file})
  endforeach()
endfunction()

function(copy_inputs source_path target_path)
  file(GLOB_RECURSE inputs "${source_path}/*.wl")
  foreach (file ${inputs})
    get_filename_component(name ${file} NAME_WE)
    message(STATUS "Copying test to ${CMAKE_CURRENT_BINARY_DIR}/${target_path}/${name}.wl")
    file(
      COPY ${file}
      DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/${target_path}
    )
  endforeach()
endfunction()

delete_old_inputs()
copy_inputs("front_end/input/parser" "parser")
copy_inputs("front_end/input/variable_use_analysis/warns" "variable_use_analysis/warns")
copy_inputs("front_end/input/variable_use_analysis/errors" "variable_use_analysis/errors")
copy_inputs("front_end/input/function_analysis" "function_analysis")
copy_inputs("front_end/input/type_analysis" "type_analysis")
copy_inputs("MiddleEnd/input/code_gen" "code_gen")

file(GLOB_RECURSE test_files *.c)
foreach(file ${test_files})
  message(STATUS "Test file ${file}")
  get_filename_component(name ${file} NAME_WE)
  add_compiler_test(${name} ${file})
endforeach()

# add_executable(fuzzer fuzzer/fuzzer.cpp)
# target_link_libraries (fuzzer PRIVATE weak_compiler)
