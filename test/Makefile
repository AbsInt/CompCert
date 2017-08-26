DIRS=c compression raytracer spass regression

all:
	set -e; for i in $(DIRS); do $(MAKE) CCOMPOPTS='$(CCOMPOPTS)' -C $$i all; done

test:
	set -e; for i in $(DIRS); do $(MAKE) SIMU='$(SIMU)' -C $$i test; done

bench:
	for i in $(DIRS); do $(MAKE) -C $$i bench; done

clean:
	for i in $(DIRS); do $(MAKE) -C $$i clean; done
