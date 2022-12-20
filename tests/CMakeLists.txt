include_directories(../lib/include)
include_directories(../tests)

function(AddCompilerTest ExecFile Path)
  message(STATUS "Adding test ${ExecFile}")
  add_executable(${ExecFile} ${Path})
  target_link_libraries (${ExecFile} PRIVATE WeakCompiler)
  target_compile_options(${ExecFile} PRIVATE -fPIC -flto -O3)
  add_test(NAME ${ExecFile} COMMAND ${ExecFile})
endfunction()

function(DeleteOldInputFiles)
  file(GLOB_RECURSE Files "${CMAKE_CURRENT_BINARY_DIR}/*.wl")
  foreach (File ${Files})
    file(REMOVE ${File})
  endforeach()
endfunction()

function(CopyInputFiles SourcePath TargetPath)
  file(GLOB_RECURSE InputFiles "${SourcePath}/*.wl")
  foreach (File ${InputFiles})
    get_filename_component(Name ${File} NAME_WE)
    message(STATUS "Copying test to ${CMAKE_CURRENT_BINARY_DIR}/${TargetPath}/${Name}.wl")
    file(
      COPY ${File}
      DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/${TargetPath}
    )
  endforeach()
endfunction()

DeleteOldInputFiles()
CopyInputFiles("FrontEnd/Input/Parser" "Parser")
CopyInputFiles("FrontEnd/Input/VariableUseAnalysis/Warns" "VariableUseAnalysis/Warns")
CopyInputFiles("FrontEnd/Input/VariableUseAnalysis/Errors" "VariableUseAnalysis/Errors")
CopyInputFiles("FrontEnd/Input/FunctionAnalysis" "FunctionAnalysis")
CopyInputFiles("FrontEnd/Input/TypeAnalysis" "TypeAnalysis")
CopyInputFiles("MiddleEnd/Input/CodeGen/Valid" "CodeGen/Valid")

file(GLOB_RECURSE Files "FrontEnd/*.cpp MiddleEnd/*.cpp")
foreach(File ${Files})
  get_filename_component(Name ${File} NAME_WE)
  AddCompilerTest(${Name} ${File})
endforeach()

add_executable(Fuzzer Fuzzer/Fuzzer.cpp)
target_link_libraries (Fuzzer PRIVATE WeakCompiler)
