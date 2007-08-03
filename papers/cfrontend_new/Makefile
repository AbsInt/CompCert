
LATEX=latex
PDFLATEX=pdflatex
TEXQUOTE=./texquote3

$(basename paper.tex): paper.tex macros.tex syntax.tex syntax2.tex values.tex dynsem1.tex dynsem2.tex dynsem3.tex dynsem4.tex trace.tex
	$(PDFLATEX) paper.tex

clean::
	rm -f `cat .genfiles`
	rm -f *.log *.dvi *.blg *~ #*# .genfiles

.SUFFIXES: .tex .etex .ftex 

.etex.tex:
	$(TEXQUOTE) < $< > $*.tex
	@echo $*.tex >> .genfiles

.ftex.tex:
	$(TEXQUOTE) < $< > $*.tex
	@echo $*.tex >> .genfiles

