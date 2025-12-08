LMOCH = ../../lmoch
NODE = check
LUS_FILES := $(wildcard *.lus)

all: clear check

check:
	@echo "\n=====\n";
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		$(LMOCH) $$f $(NODE); \
		echo "\n=====\n"; \
	done

cat:
	@echo "\n=====\n";
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		cat $$f; \
		echo "\n=====\n"; \
	done

compare:
	@echo "\n=====\n";
	@for f in $(LUS_FILES); do \
		echo "$$f :\n"; \
		cat $$f; \
		echo "\n---\n"; \
		$(LMOCH) $$f $(NODE); \
		echo "\n=====\n"; \
	done

clear:
	clear
