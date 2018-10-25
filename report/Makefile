report.pdf: report.tex bibliography.bib preamble.tex
	latexmk -xelatex report.tex

.PHONY: clean
clean:
	latexmk -CA

.PHONY: veryclean
veryclean: clean
	rm -f report.pdf
