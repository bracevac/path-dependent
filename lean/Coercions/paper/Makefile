.PHONY: all tutorial tutorial-check clean

TUTORIAL_BUILD := ../../../tmp/pdfs/fcdot-tutorial
PAPER_OUTPUT := ../../../output/pdf

all:
	latexmk -pdf -interaction=nonstopmode main.tex

tutorial:
	mkdir -p "$(TUTORIAL_BUILD)" "$(PAPER_OUTPUT)"
	latexmk -pdf -halt-on-error -interaction=nonstopmode -outdir="$(TUTORIAL_BUILD)" tutorial.tex
	cp "$(TUTORIAL_BUILD)/tutorial.pdf" "$(PAPER_OUTPUT)/fcdot-tutorial.pdf"

tutorial-check:
	cd ../../.. && lake env lean lean/Coercions/paper/TutorialExamples.lean

clean:
	latexmk -C
