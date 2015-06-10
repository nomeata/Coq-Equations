all: equations.pdf

intro.tex: intro.vo
	coqdoc --latex --body-only --utf8 --interpolate -o $@ ${<:.vo=.v}

%.vo: %.v
	coqc $<

%.pdf: %.tex
	rubber -d $<
