SOURCES := $(shell find . -type f -name '*.agda')

agda-calc : $(SOURCES)
	agda -c --ghc-flag=-dynamic --ghc-flag=-o --ghc-flag=agda-calc src/Main.agda

clean :
	rm -f agda-calc
	rm -rf src/MAlonzo
	find . -type f -name '*.agdai' -exec rm '{}' \;
