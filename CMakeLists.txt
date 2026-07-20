cmake_minimum_required(VERSION 3.20)
project(DB25LogicalPlan VERSION 0.1.0 LANGUAGES CXX)

# Match the rest of the DB25 stack: C++23, no exceptions (Result-type errors).
set(CMAKE_CXX_STANDARD 23)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

# ---------------------------------------------------------------------------
# Dependencies (git submodules under external/, mirroring how the parser
# consumes the tokenizer at external/tokenizer).
#
#   external/parser    - self-contained: add_subdirectory builds db25parser and
#                        its own tokenizer sub-submodule.
#   external/analyzer  - a single translation unit (src/analyzer.cpp) plus
#                        headers. We deliberately do NOT add_subdirectory it:
#                        its CMake uses find_package(DB25Parser), which would
#                        force an install of the parser. Instead we compile
#                        analyzer.cpp straight into our library and point it at
#                        the in-tree parser/tokenizer headers.
# ---------------------------------------------------------------------------
set(PARSER_DIR    ${CMAKE_CURRENT_SOURCE_DIR}/external/parser)
set(ANALYZER_DIR  ${CMAKE_CURRENT_SOURCE_DIR}/external/analyzer)
set(TOKENIZER_DIR ${PARSER_DIR}/external/tokenizer)

if(NOT EXISTS ${PARSER_DIR}/CMakeLists.txt)
    message(FATAL_ERROR
        "external/parser is empty. Run: git submodule update --init --recursive")
endif()
if(NOT EXISTS ${ANALYZER_DIR}/src/analyzer.cpp)
    message(FATAL_ERROR
        "external/analyzer is empty. Run: git submodule update --init --recursive")
endif()

# Turn off the parser's own tests/tools/benchmarks BEFORE add_subdirectory so it
# does not FetchContent googletest (no network) or build extra artifacts.
set(BUILD_TESTS      OFF CACHE BOOL "" FORCE)
set(BUILD_TOOLS      OFF CACHE BOOL "" FORCE)
set(BUILD_BENCHMARKS OFF CACHE BOOL "" FORCE)

add_subdirectory(${PARSER_DIR} ${CMAKE_CURRENT_BINARY_DIR}/parser)

# ---------------------------------------------------------------------------
# db25logicalplan: the IR + binder, plus the analyzer compiled in-tree.
# ---------------------------------------------------------------------------
add_library(db25logicalplan STATIC
    src/logical_plan.cpp
    src/binder.cpp
    ${ANALYZER_DIR}/src/analyzer.cpp
)

target_include_directories(db25logicalplan PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include   # our db25/plan/*
    ${ANALYZER_DIR}/include               # db25/semantic/*
    ${PARSER_DIR}/include                 # db25/ast/*, db25/parser/*, db25/memory/*
    ${TOKENIZER_DIR}/include              # simd_tokenizer.hpp et al.
)

# The parser library brings in the AST/arena/tokenizer object code.
target_link_libraries(db25logicalplan PUBLIC db25parser)

target_compile_options(db25logicalplan PRIVATE -fno-exceptions -Wall -Wextra)

# ---------------------------------------------------------------------------
# Tests (self-contained harness; no gtest).
# ---------------------------------------------------------------------------
enable_testing()
add_executable(test_binder tests/test_binder.cpp)
target_link_libraries(test_binder PRIVATE db25logicalplan)
target_compile_options(test_binder PRIVATE -fno-exceptions)
add_test(NAME test_binder COMMAND test_binder)
