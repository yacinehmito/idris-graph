IDRIS := idris
LIB   := graph
MAIN  := src/Main.idr
BIN   := main
OPTS  :=

.PHONY: build install test check doc clean clobber draw c-code repl shell

build:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

install: build
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

test: clean
	${IDRIS} ${OPTS} --testpkg ${LIB}.ipkg

check: clobber
	${IDRIS} ${OPTS} --checkpkg ${LIB}.ipkg

doc:
	${IDRIS} ${OPTS} --mkdoc ${LIB}.ipkg

clean:
	${IDRIS} ${OPTS} --clean ${LIB}.ipkg
	find . -type f -name '*~' -delete

clobber: clean
	find . -type f -name '*.ibc' -delete

draw: build
	${BIN} | dot -Tpng | imv -

c-code:
	idris --compileonly ${MAIN}

repl:
	idris --repl ${LIB}.ipkg

shell:
	nix-shell --run zsh

