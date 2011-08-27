GHC := ghc
CORE2ISA := ../cabal-dev/bin/core2isa

%.hcr : %.hs
	$(GHC) -O0 -fforce-recomp -fext-core -c $<

%.thy : %.hcr
	$(CORE2ISA) $< > $@
