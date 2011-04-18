GHC := ghc

%.hcr : %.hs
	$(GHC) -fforce-recomp -fext-core -c $<
