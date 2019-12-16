Z3DIR := $(shell ocamlfind query z3)

build :
	dune build @install

examples : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe input/block_192.json
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe input/block_192_rev.json

test : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune runtest

test_% : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./test/$@.exe

clean :
	dune clean

.PHONY : build run test test_% utop clean


