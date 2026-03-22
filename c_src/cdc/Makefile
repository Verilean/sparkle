CXX ?= clang++
CXXFLAGS = -std=c++20 -O3 -march=native -pthread -Wall -Wextra
SHARED_EXT := $(if $(findstring Darwin,$(shell uname)),dylib,so)

.PHONY: all clean test

all: cdc_test cdc_example cdc_runner.$(SHARED_EXT)

cdc_test: cdc_test.cpp spsc_queue.hpp cdc_rollback.hpp
	$(CXX) $(CXXFLAGS) -o $@ cdc_test.cpp

cdc_example: cdc_example.cpp spsc_queue.hpp cdc_rollback.hpp
	$(CXX) $(CXXFLAGS) -o $@ cdc_example.cpp

cdc_runner.$(SHARED_EXT): cdc_runner.cpp cdc_runner.hpp spsc_queue.hpp cdc_rollback.hpp
	$(CXX) $(CXXFLAGS) -shared -fPIC -o $@ cdc_runner.cpp

test: cdc_test
	./cdc_test

clean:
	rm -f cdc_test cdc_example cdc_runner.so cdc_runner.dylib
