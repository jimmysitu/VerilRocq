VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

debug:
	@if [ -z "$(FILE)" ]; then echo "Usage: make debug FILE=path/to/file.v"; exit 1; fi
	@# Use tr to replace newlines with spaces to avoid quoting issues with xargs
	@ARGS=$$(grep -E '^(-R|-Q)' _CoqProject | tr '\n' ' '); \
	echo "Debugging $(FILE)..."; \
	echo "---------------------------------------------------"; \
	coqtop $$ARGS < $(FILE) 2>&1 | \
	awk '{print} /^Error:/ {while(getline > 0) {print; if($$0 ~ /^\s*$$/) exit}}'

compile:
	@if [ -z "$(FILE)" ]; then echo "Usage: make compile FILE=path/to/file.v"; exit 1; fi
	@ARGS=$$(grep -E '^(-R|-Q)' _CoqProject | tr '\n' ' '); \
	echo "Compiling $(FILE) to .vo ..."; \
	coqc $$ARGS $(FILE)

clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq Makefile.coq.conf
	find . -type f -name '.*.aux' -exec rm {} +
	find . -type f -name '*.v.d' -exec rm {} +
	find . -type f -name '*.glob' -exec rm {} +
	find . -type f -name '*.vo' -exec rm {} +
	find . -type f -name '*.vos' -exec rm {} +
	find . -type f -name '*.vok' -exec rm {} +
	find . -type f -name '*~' -exec rm {} +
	find . -type f -name '.coqdeps.d' -exec rm {} +
