ISABELLE=/opt/Isabelle/bin/isabelle

doc: output/document.pdf output/outline.pdf

show_outline: output/outline.pdf
	evince output/outline.pdf &

output/document.pdf output/outline.pdf: ROOT $(wildcard *.thy) $(wildcard *.ML) document/root.tex document/root.bib
	$(ISABELLE) document -P output Tensor_Product

build:
	$(ISABELLE) build -b Tensor_Product

THY_FILES = $(filter-out All.thy CStar_Algebras.thy, $(wildcard *.thy))
ZIP_CONTENT = $(THY_FILES) ROOT document/root.tex document/root.bib
Hilbert_Space_Tensor_Product.zip: $(ZIP_CONTENT) Makefile
	rm -rf tmp $@
	mkdir -p tmp/Hilbert_Space_Tensor_Product/
	cp --parents $(ZIP_CONTENT) tmp/Hilbert_Space_Tensor_Product/
	ls -lh tmp/Hilbert_Space_Tensor_Product/
	cd tmp && zip -r ../$@ Hilbert_Space_Tensor_Product/
