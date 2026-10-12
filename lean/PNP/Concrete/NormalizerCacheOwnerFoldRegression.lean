import PNP.Concrete.NormalizerCacheOwnerFold

namespace PNP.Concrete.NormalizerBlocks

example : CacheOwner.values [some 9,some 2] [⟨true,1⟩,⟨true,0⟩]
    [⟨false,9⟩,⟨false,2⟩,⟨false,9⟩,⟨false,7⟩] = [some 1,some 0,some 1,none] := rfl
example : CacheOwner.values [] [] [] = [] := rfl
example (r : DenseClauses.State) (bound : Nat) (bounded : r.store.Bounded bound) :
    CacheOwner.callSteps r ≤ CacheOwner.callBound.eval bound :=
  CacheOwner.callSteps_bound r bound bounded

#print axioms CacheOwner.appendEntry_exec
#print axioms CacheOwner.appended_buffer
#print axioms CacheOwner.body_exec
#print axioms CacheOwner.body_fields
#print axioms CacheOwner.bodyFuel_bound
#print axioms CacheOwner.body_buffer
#print axioms CacheOwner.call_exec
#print axioms CacheOwner.callSteps_bound
#print axioms CacheOwner.called_canonical

end PNP.Concrete.NormalizerBlocks
