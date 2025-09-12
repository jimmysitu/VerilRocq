.PHONY: clean all

all:
	$(MAKE) -C dep/coqutil
	$(MAKE) -C src

clean:
	$(MAKE) -C src clean
	$(MAKE) -C dep/coqutil clean
