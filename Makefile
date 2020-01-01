Z3DIR := $(shell ocamlfind query z3)

build :
	dune build @install

examples : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe examples/block_192/input.json
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe examples/block_192_rev/input.json
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe examples/block_add/input.json
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe examples/block_add_2/input.json
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./main.exe examples/block_long/input.json

test : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune runtest

test_% : build
	LD_LIBRARY_PATH=$(Z3DIR) \
	dune exec ./test/$@.exe

clean :
	dune clean

.PHONY : build run test test_% utop clean


