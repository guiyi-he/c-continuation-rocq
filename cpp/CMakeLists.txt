cmake_minimum_required(VERSION 3.16)
project(rewpla_solver VERSION 0.5.0 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(rewpla_solver_lib
  src/ast.cpp
  src/parser.cpp
  src/regex_frontend.cpp
  src/partial_derivative.cpp
  src/solver.cpp
  src/eager_solver.cpp
)
target_include_directories(rewpla_solver_lib PUBLIC include)

if(MSVC)
  target_compile_options(rewpla_solver_lib PRIVATE /W4 /permissive-)
else()
  target_compile_options(rewpla_solver_lib PRIVATE -Wall -Wextra -Wpedantic)
endif()

add_executable(rewpla-solver src/main.cpp)
target_link_libraries(rewpla-solver PRIVATE rewpla_solver_lib)

add_executable(rewpla-redos src/redos_main.cpp)
target_link_libraries(rewpla-redos PRIVATE rewpla_solver_lib)

add_executable(rewpla-distance-bench bench/distance_bench.cpp)
target_link_libraries(rewpla-distance-bench PRIVATE rewpla_solver_lib)

include(CTest)
if(BUILD_TESTING)
  add_executable(rewpla-solver-tests tests/test_solver.cpp)
  target_link_libraries(rewpla-solver-tests PRIVATE rewpla_solver_lib)
  add_test(NAME rewpla-solver-unit COMMAND rewpla-solver-tests)
  find_package(Python3 COMPONENTS Interpreter)
  if(Python3_Interpreter_FOUND)
    add_test(NAME rewpla-solver-cli
      COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/cli_smoke.py
              $<TARGET_FILE:rewpla-solver>)
    add_test(NAME rewpla-regex-frontend-differential
      COMMAND ${Python3_EXECUTABLE}
              ${CMAKE_CURRENT_SOURCE_DIR}/tests/regex_frontend_differential.py
              $<TARGET_FILE:rewpla-solver>)
    add_test(NAME rewpla-redos-smoke
      COMMAND ${Python3_EXECUTABLE} ${CMAKE_CURRENT_SOURCE_DIR}/tests/redos_smoke.py
              $<TARGET_FILE:rewpla-redos>)
  endif()
endif()
