.PHONY: all clean

BIBINPUTS := $(abspath ../../..):
export BIBINPUTS

all:
	mkdir -p build
	latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build paper.tex

clean:
	latexmk -C -outdir=build paper.tex
