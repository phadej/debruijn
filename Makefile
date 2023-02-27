.PHONY : cabal-fmt stylish-haskell

all :
	@echo "Hello there"

cabal-fmt :
	cabal-fmt -i */*.cabal

stylish-haskell :
	bash -O globstar -c 'stylish-haskell -i */src/**/*.hs */tests/**/*.hs'
