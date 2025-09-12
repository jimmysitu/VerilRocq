VS:=$(shell find . -type f -name '*.v')

.PHONY: clean

all: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(VS)
	$(COQBIN)coq_makefile -f _CoqProject $(VS) -o Makefile.coq

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
