run: build draw

draw:
	./main | dot -Tpng | imv -

build:
	idris --build graph.ipkg

c-code:
	idris --compileonly src/Main.idr

repl:
	idris --repl graph.ipkg

shell:
	nix-shell --run zsh



