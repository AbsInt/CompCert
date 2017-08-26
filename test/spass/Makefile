include ../../Makefile.config

CC=../../ccomp 
CFLAGS=$(CCOMPOPTS) -stdlib ../../runtime -dparse -dclight -dasm -fstruct-return

SRCS=analyze.c clause.c clock.c closure.c cnf.c component.c                 \
  condensing.c context.c defs.c dfgparser.c dfgscanner.c doc-proof.c        \
  flags.c foldfg.c graph.c hash.c hasharray.c iaparser.c iascanner.c        \
  kbo.c list.c memory.c misc.c options.c order.c partition.c                \
  proofcheck.c renaming.c resolution.c rpos.c rules-inf.c rules-red.c       \
  rules-sort.c rules-split.c rules-ur.c search.c sharing.c sort.c st.c      \
  stack.c strings.c subst.c subsumption.c symbol.c table.c tableau.c        \
  term.c terminator.c top.c unify.c vector.c

all: spass

spass: $(SRCS:.c=.o)
	$(CC) $(CFLAGS) -o spass $(SRCS:.c=.o) $(LIBMATH)

clean:
	rm -f spass
	rm -f *.o *.s *.parsed.c *.light.c *.sdump

test:
	$(SIMU) ./spass small_problem.dfg | grep 'Proof found'

TIME=xtime -o /dev/null     # Xavier's hack
#TIME=time >/dev/null       # Otherwise

bench:
	@echo -n "spass: "; $(TIME) ./spass problem.dfg

depend:
	gcc -MM $(SRCS) > .depend

include .depend
