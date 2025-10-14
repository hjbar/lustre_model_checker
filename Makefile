
all: src/lmoch format

src/lmoch: lib/aez-0.3/aez.cmxa FORCE
	(cd src ; \
	 $(MAKE))

lib/aez-0.3/aez.cmxa:
	(cd lib ; \
	 tar xvfz aez-0.3.tar.gz ; \
	 cd aez-0.3 ; \
	 ./configure ; \
	 $(MAKE))

format:
	find . -type d -name _build -prune -o \( -name "*.ml" -o -name "*.mli" \) -print \
	| xargs -r ocamlformat --enable-outside-detected-project --no-comment-check --inplace

clean:
	(cd src; $(MAKE) clean)
	(cd examples; $(MAKE) clean)

cleanall:
	rm -f *~
	(cd src; $(MAKE) cleanall)
	(cd examples; $(MAKE) cleanall)
	rm -rf lib/aez-0.3

FORCE:
