include ../Makefile.config

DIRS=c compression raytracer spass regression
ifeq ($(CLIGHTGEN),true)
DIRS+=clightgen
endif

all:
	set -e; for i in $(DIRS); do $(MAKE) CCOMPOPTS='$(CCOMPOPTS)' -C $$i all; done

test:
	set -e; for i in $(DIRS); do $(MAKE) SIMU='$(SIMU)' -C $$i test; done

parallel:
	parallel $(MAKE) SIMU='$(SIMU)' -C {} test ::: $(DIRS)

bench:
	for i in $(DIRS); do $(MAKE) -C $$i bench; done

clean:
	for i in $(DIRS); do $(MAKE) -C $$i clean; done
