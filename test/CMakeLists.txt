include(FetchContent)
FetchContent_Declare(
    doctest
    GIT_REPOSITORY https://github.com/doctest/doctest.git
    GIT_TAG v2.4.11)
FetchContent_MakeAvailable(doctest)

add_executable(unicode_cpp_tests
    utf8_test.cpp
    utf16_test.cpp
    utf32_test.cpp
    bom_test.cpp
    noncharacters_test.cpp
    identifier_test.cpp
    opaque_blob_test.cpp
    validated_utf8_test.cpp
    security_test.cpp)
target_link_libraries(unicode_cpp_tests
    PRIVATE unicode_cpp::unicode_cpp doctest::doctest)

include(${doctest_SOURCE_DIR}/scripts/cmake/doctest.cmake)
doctest_discover_tests(unicode_cpp_tests)
