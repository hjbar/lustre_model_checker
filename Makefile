all: format build FORCE

clean:
	@dune clean

format:
	@dune fmt

build:
	@dune build

examples: all clear
	@cd examples && make -s

check: all clear
	@cd examples && make -s check

cat: all clear
	@cd examples && make -s cat

compare: all clear
	@cd examples && make -s compare

clear:
	clear

FORCE:
