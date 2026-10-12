import PNP.Concrete.NormalizerCacheSigmaCall
namespace PNP.Concrete.NormalizerBlocks
example (r : CacheSigma.State) : (CacheSigma.result r).registers.output.length = 1 :=
  CacheSigma.result_sign_length r
example (r : CacheSigma.State) : (CacheSigma.result r).matching = r.matching :=
  (CacheSigma.result_fields r).2.2.2.1
example (r : CacheSigma.State) (n : Nat) (h : CacheSigma.InputsBounded r n) :
    CacheSigma.fuel r ≤ CacheSigma.bound.eval n := CacheSigma.fuel_bound r n h
example (r : CacheSigma.State) :
    Exec CacheSigma.read r.store (CacheSigma.fuel r) (CacheSigma.result r).store :=
  CacheSigma.read_exec r
#print axioms CacheSigma.stashOwner_exec
#print axioms CacheSigma.readOwner_exec
#print axioms CacheSigma.loadLiteral_exec
#print axioms CacheSigma.setup_exec
#print axioms CacheSigma.ready_fields
#print axioms CacheSigma.read_exec
#print axioms CacheSigma.result_fields
#print axioms CacheSigma.result_sign_length
#print axioms CacheSigma.ready_bounded
#print axioms CacheSigma.setupFuel_bound
#print axioms CacheSigma.bound_eval
#print axioms CacheSigma.fuel_bound
#print axioms CacheSigma.canonical
end PNP.Concrete.NormalizerBlocks
