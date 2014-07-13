all:
	make compile

compile:
	kompile fpl.k

run:
	krun test.fpl

doc:
	kompile fpl.k --backend pdf
