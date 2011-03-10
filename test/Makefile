DIRS=c compression raytracer spass regression

all:
	for i in $(DIRS); do $(MAKE) -C $$i all; done

test:
	for i in $(DIRS); do $(MAKE) -C $$i test; done

clean:
	for i in $(DIRS); do $(MAKE) -C $$i clean; done
