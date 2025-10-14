OCAMLBUILD= ocamlbuild -no-links -classic-display \
		-libs unix,nums,aez \
		-cflags "-I ../../lib/aez-0.3" \
		-lflags "-I ../../lib/aez-0.3" \
		-tags debug,annot

TARGET=native
MAIN=lmoch

all: $(MAIN) format

native: TARGET := native
native: all
opt: native
$(MAIN).opt: native
$(MAIN).native: native


byte: TARGET := byte
byte: all
$(MAIN).byte: byte


$(MAIN): $(MAIN).target
	cp _build/$(MAIN).$(TARGET) $(MAIN)

$(MAIN).target:
	$(OCAMLBUILD) $(MAIN).$(TARGET)

format:
	find . -type d -name _build -prune -o \( -name "*.ml" -o -name "*.mli" \) -print \
	| xargs -r ocamlformat --enable-outside-detected-project --no-comment-check --inplace

clean:
	ocamlbuild -classic-display -clean

realclean: clean
	rm -f $(MAIN) *~

cleanall: realclean
