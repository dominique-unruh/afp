ISABELLE=/opt/Isabelle2021-1/bin/isabelle

doc: output/document.pdf output/outline.pdf

show_outline: output/outline.pdf
	evince output/outline.pdf &

output/document.pdf output/outline.pdf: ROOT $(wildcard *.thy) $(wildcard *.ML) document/root.tex document/root.bib
	$(ISABELLE) document -P output Tensor_Product

build:
	$(ISABELLE) build -b Tensor_Product
