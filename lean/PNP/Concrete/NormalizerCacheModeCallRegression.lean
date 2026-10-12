import PNP.Concrete.NormalizerCacheModeCall

namespace PNP.Concrete.NormalizerBlocks

example : CacheMode.values [none,some 8] [⟨false,8⟩]
    [[⟨true,0⟩,⟨true,0⟩,⟨true,0⟩],[⟨false,0⟩,⟨false,0⟩,⟨false,0⟩]]
    [⟨true,0⟩,⟨true,1⟩] 0 = [none,some 0] := rfl
example : CacheMode.values [some 8] [⟨false,8⟩] [] [] 0 = [] := rfl
example (r : CacheMode.State) : Exec CacheMode.call r.store (CacheMode.callSteps r) (CacheMode.called r).store :=
  CacheMode.call_exec r
example (r : CacheMode.State) (n : Nat) (bounded : r.store.Bounded n) :
    CacheMode.callSteps r ≤ CacheMode.callBound.eval n := CacheMode.callSteps_bound r n bounded

#print axioms CacheMode.prefix_cons
#print axioms CacheMode.stepped_cons
#print axioms CacheMode.scan_state_step
#print axioms CacheMode.scan_buffer
#print axioms CacheMode.start_exec
#print axioms CacheMode.front_exec
#print axioms CacheMode.front_buffer
#print axioms CacheMode.call_exec
#print axioms CacheMode.called_fields
#print axioms CacheMode.called_canonical
#print axioms CacheMode.frontSteps_bound
#print axioms CacheMode.callSteps_bound

end PNP.Concrete.NormalizerBlocks
