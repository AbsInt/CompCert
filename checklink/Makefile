TESTS=c arcode lzw lzss raytracer regression spass

.PHONY: all $(TESTS)

all: $(TESTS)

CL=../cchecklink $(ARGS)
TESTDIR=../test

C=aes almabench binarytrees bisect chomp fannkuch fft fib integr knucleotide \
  lists mandelbrot nbody nsievebits nsieve perlin qsort sha1 spectral vmach

c:
	for x in $(C); do \
		echo $(CL) $(TESTDIR)/c/$$x.compcert $(TESTDIR)/c/$$x.sdump; \
		$(CL) $(TESTDIR)/c/$$x.compcert $(TESTDIR)/c/$$x.sdump; \
	done

ARCODE=optlist bitfile arcode armain
ARCODE_SDUMP=$(addsuffix .sdump, $(ARCODE))
arcode:
	$(CL) $(addprefix $(TESTDIR)/compression/, arcode $(ARCODE_SDUMP))

LZW=optlist bitfile lzwencode lzwdecode lzwmain
LZW_SDUMP=$(addsuffix .sdump, $(LZW))
lzw:
	$(CL) $(addprefix $(TESTDIR)/compression/, lzw $(LZW_SDUMP))

LZSS=optlist bitfile lzvars lzhash lzencode lzdecode
LZSS_SDUMP=$(addsuffix .sdump, $(LZSS))
lzss:
	$(CL) $(addprefix $(TESTDIR)/compression/, lzss $(LZSS_SDUMP))

RAYTRACER_SDUMP=`ls $(TESTDIR)/raytracer/*.sdump`
raytracer:
	$(CL) $(TESTDIR)/raytracer/render $(RAYTRACER_SDUMP)

SDUMP_COMPCERT=`echo $$x | sed s/sdump/compcert/`
REGRESSION_SDUMP=`ls $(TESTDIR)/regression/*.sdump`
regression:
	for x in $(REGRESSION_SDUMP); \
	do \
		if [ -f $(SDUMP_COMPCERT) ] ; \
		then \
			echo $(CL) $(SDUMP_COMPCERT) $$x; \
			$(CL) $(SDUMP_COMPCERT) $$x ; \
		fi ; \
	done

SPASS_SDUMP=`ls $(TESTDIR)/spass/*.sdump`
spass:
	$(CL) $(TESTDIR)/spass/spass $(SPASS_SDUMP)
