run: build draw

draw:
	./main | dot -Tpng | imv -

build:
	idris --build graph.ipkg
