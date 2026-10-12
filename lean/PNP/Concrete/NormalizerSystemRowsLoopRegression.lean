import PNP.Concrete.NormalizerSystemRowsLoop
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (iteration : SystemRows.Iteration) (word : BitString) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (SystemRows.scan iteration word r).fuel ≤ word.length*(1+iteration.bound.eval n)+1 :=
  SystemRows.scan_fuel_bound iteration word r n fixed budget
example (iteration : SystemRows.Iteration) (word : BitString) (r : SystemRows.State) :
    (SystemRows.scan iteration word r).state.counter = List.replicate word.length true ++ r.counter :=
  SystemRows.scan_counter iteration word r
example (iteration : SystemRows.Iteration) (word : BitString) (r : SystemRows.State) :
    (SystemRows.scan iteration word r).state.remaining = [] := SystemRows.scan_remaining iteration word r
#print axioms SystemRows.scan_exec
#print axioms SystemRows.scan_shared
#print axioms SystemRows.scan_rows
#print axioms SystemRows.scan_remaining
#print axioms SystemRows.scan_counter
#print axioms SystemRows.scan_fuel_bound
#print axioms SystemRows.whole_exec
end PNP.Concrete.NormalizerBlocks
