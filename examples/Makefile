GHC := ghc
HCR2THY := ../cabal-dev/bin/hcr2thy

%.hcr : %.hs
	$(GHC) -O0 -fforce-recomp -fext-core -c $<

%.thy : %.hcr
	$(HCR2THY) $< > $@
