cmake_minimum_required(VERSION 3.20)

project(unicode_cpp
    VERSION 0.1.0
    DESCRIPTION
        "Strict Unicode-as-attack-surface conformance for C++"
    LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(unicode_cpp INTERFACE)
add_library(unicode_cpp::unicode_cpp ALIAS unicode_cpp)

target_include_directories(unicode_cpp INTERFACE
    $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include>
    $<INSTALL_INTERFACE:include>)

target_compile_features(unicode_cpp INTERFACE cxx_std_20)

if(MSVC)
    target_compile_options(unicode_cpp INTERFACE /W4 /WX /permissive-)
else()
    target_compile_options(unicode_cpp INTERFACE
        -Wall -Wextra -Wpedantic -Werror)
endif()

option(UNICODE_CPP_BUILD_TESTS "Build unicode_cpp tests" OFF)
if(UNICODE_CPP_BUILD_TESTS)
    enable_testing()
    add_subdirectory(test)
endif()

include(GNUInstallDirs)
install(DIRECTORY include/unicode_cpp
    DESTINATION ${CMAKE_INSTALL_INCLUDEDIR})
