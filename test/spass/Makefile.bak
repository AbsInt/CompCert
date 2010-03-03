LEVEL = ../../..
PROG = SPASS

CPPFLAGS = -DCLOCK_NO_TIMING -fno-strict-aliasing -w
LDFLAGS  = -lm

ifdef SMALL_PROBLEM_SIZE
RUN_OPTIONS="$(PROJ_SRC_DIR)/small_problem.dfg"
else
RUN_OPTIONS="$(PROJ_SRC_DIR)/problem.dfg"
endif

include ../../Makefile.multisrc
