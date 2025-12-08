all: install format build FORCE

install:
	@mkdir -p lib
ifeq ("$(wildcard lib/aez)","")
	@cd targz && tar xvfz aez.tar.gz
	@mv targz/aez lib/aez
else
endif

clean:
	@rm -rf lmoch
	@dune clean

format:
	@dune fmt

build:
	@dune build
	@rm -rf lmoch
	@cp _build/default/src/lmoch.exe lmoch

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
