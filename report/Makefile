GRAPHS = scaling_graph_large.pdf scaling_graph.pdf

report.pdf: report.tex bibliography.bib preamble.tex title.tex ${GRAPHS}
	latexmk -xelatex report.tex

.PHONY: clean
clean:
	latexmk -CA

.PHONY: veryclean
veryclean: clean
	rm -f report.pdf
