import PNP.Concrete.NormalizerModeCacheState

namespace PNP.Concrete.NormalizerBlocks

example (r : CutDriver.State) (after : CacheMode.State) :
    ModeCacheDriver.modeView (ModeCacheDriver.withMode r after) = after :=
  ModeCacheDriver.modeView_withMode r after
example (r : CutDriver.State) (after : CacheMode.State) :
    ModeCacheDriver.owners (ModeCacheDriver.withMode r after) = ModeCacheDriver.owners r :=
  (ModeCacheDriver.withMode_cache r after).1
example (r : CutDriver.State) (after : CacheMode.State) :
    ModeCacheDriver.literals (ModeCacheDriver.withMode r after) = ModeCacheDriver.literals r :=
  (ModeCacheDriver.withMode_cache r after).2

#print axioms ModeCacheDriver.modeView_store
#print axioms ModeCacheDriver.withMode_store
#print axioms ModeCacheDriver.modeView_withMode
#print axioms ModeCacheDriver.withMode_registers
#print axioms ModeCacheDriver.withMode_frame
#print axioms ModeCacheDriver.withMode_cache
#print axioms ModeCacheDriver.liftMode_exec
#print axioms ModeCacheDriver.modeView_bounded

end PNP.Concrete.NormalizerBlocks
