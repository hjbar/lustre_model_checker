LMOCH = ../src/lmoch
NODE = check
LUS_FILES := $(wildcard *.lus)

check:
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		$(LMOCH) $$f $(NODE); \
		echo "\n=====\n"; \
	done

cat:
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		cat $$f; \
		echo "\n=====\n"; \
	done

compare:
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		cat $$f; \
		echo "\n---\n"; \
		$(LMOCH) $$f $(NODE); \
		echo "\n=====\n"; \
	done


clean:

cleanall: clean
	rm -f *~
