all: format build FORCE

clean:
	@dune clean

format:
	@dune fmt

build:
	@dune build

fullclean: clean
	@rm -rf lib/aez

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
