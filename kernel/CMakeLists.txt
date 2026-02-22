cmake_minimum_required(VERSION 3.16)
project(mypa_kernel LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_executable(mypa-kernel
  src/document_codec.cpp
  src/main.cpp
  src/proof_system.cpp
  src/json_rpc.cpp
)
