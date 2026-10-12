import PNP.Concrete.NormalizerSystemRowsA
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (word : BitString) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (SystemRows.scan SystemRows.aIteration word r).fuel ≤ word.length*(1+SystemRows.aBound.eval n)+1 :=
  SystemRows.a_scan_bound word r n fixed budget
example (word : BitString) (r : SystemRows.State) :
    (SystemRows.scan SystemRows.aIteration word r).state.counter = List.replicate word.length true ++ r.counter :=
  SystemRows.scan_counter SystemRows.aIteration word r
example (r : SystemRows.State) :
    (SystemRows.aResult r).remaining = r.remaining.tail := (SystemRows.a_frame r).2.1
#print axioms SystemRows.advance_exec
#print axioms SystemRows.emit_bound
#print axioms SystemRows.a_exec
#print axioms SystemRows.a_shared
#print axioms SystemRows.a_frame
#print axioms SystemRows.a_fuel_bound
#print axioms SystemRows.aIteration
#print axioms SystemRows.a_whole_exec
#print axioms SystemRows.a_scan_bound
end PNP.Concrete.NormalizerBlocks
