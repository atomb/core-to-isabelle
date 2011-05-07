GHC := ghc

%.hcr : %.hs
	$(GHC) -O0 -fforce-recomp -fext-core -c $<
