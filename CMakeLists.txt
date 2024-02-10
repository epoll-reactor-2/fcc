cmake_minimum_required(VERSION 3.10)
project(weak_compiler C)

set(CMAKE_C_STANDARD 99)

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fPIC")

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -Wshadow -Wvla -Wpointer-arith -Wframe-larger-than=32768")

option(LOG "Enable logging" OFF)
if (LOG)
    add_definitions(-DUSE_LOG)
endif()

option(SANITIZE "Enable sanitization" OFF)
if (SANITIZE)
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fanalyzer")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=address -fno-omit-frame-pointer")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=undefined -fno-sanitize-recover=all")
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize-address-use-after-scope")

    if (CMAKE_C_COMPILER_ID STREQUAL "Clang")
        set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -fsanitize=cfi -fvisibility=default -flto")
    endif()
else()
    set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -march=native -mtune=generic -O3")
endif()

set(LEX_SRC "lex.yy.c")

find_package(FLEX REQUIRED)
if(FLEX_FOUND)
    add_custom_command(
      OUTPUT ${LEX_SRC}
      COMMAND ${FLEX_EXECUTABLE}
              --outfile=${LEX_SRC}
              ${CMAKE_SOURCE_DIR}/lex/grammar.lex
      COMMENT "Generating lex source"
    )
endif()

file(GLOB BACK_END_INPUTS tests/back_end/input/*)
file(COPY ${BACK_END_INPUTS} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/inputs)

file(GLOB MIDDLE_END_INPUTS tests/middle_end/input/*)
file(COPY ${MIDDLE_END_INPUTS} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/inputs)

file(GLOB FRONT_END_INPUTS tests/front_end/input/*)
file(COPY ${FRONT_END_INPUTS} DESTINATION ${CMAKE_CURRENT_BINARY_DIR}/inputs)

# Collect source files
file(GLOB_RECURSE LIB_SRC "lib/*.c")

# Add library target
add_library(weak_compiler SHARED ${LIB_SRC} ${LEX_SRC})
target_include_directories(weak_compiler PRIVATE lib)
target_link_libraries(weak_compiler -lfl)

enable_testing()

# Build executable targets
file(GLOB_RECURSE TEST_SRC "tests/*.c")
foreach(TEST_FILE ${TEST_SRC})
    get_filename_component(TEST_NAME ${TEST_FILE} NAME_WE)
    add_executable(${TEST_NAME}_test ${TEST_FILE})
    target_link_libraries(${TEST_NAME}_test weak_compiler -lfl)
    target_include_directories(${TEST_NAME}_test PRIVATE lib)
    target_include_directories(${TEST_NAME}_test PRIVATE tests)
    add_test(
           NAME ${TEST_NAME}_test
        COMMAND ${TEST_NAME}_test
    )
endforeach()

# Custom target for cleaning
add_custom_target(clean_all COMMAND ${CMAKE_COMMAND} -E remove_directory build)

# Custom target for cppcheck
option(CHECK_ALL "Enable all checks in cppcheck" OFF)
add_custom_target(cppcheck
    COMMAND cppcheck -f --enable=$<$<BOOL:${CHECK_ALL}>:all>$<$<NOT:$<BOOL:${CHECK_ALL}>>:warning,performance,portability> --language=c --std=c11 lib
    WORKING_DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}
    COMMENT "Running cppcheck"
)