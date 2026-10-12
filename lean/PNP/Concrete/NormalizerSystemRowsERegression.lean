import PNP.Concrete.NormalizerSystemRowsE
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (word : BitString) (r : SystemRows.State) (n : Nat)
    (fixed : r.shared.Bounded n) (budget : r.counter.length + word.length ≤ n) :
    (SystemRows.scan SystemRows.eIteration word r).fuel ≤ word.length*(1+SystemRows.eBound.eval n)+1 :=
  SystemRows.e_scan_bound word r n fixed budget
example (r : SystemRows.State) (absent : r.registers.output = []) :
    SystemRows.eBranchResult r = r := by
  simp only [SystemRows.eBranchResult,absent,List.headD_nil,Bool.false_eq_true,ite_false]
example (r : SystemRows.State) :
    (SystemRows.eResult r).counter = true::r.counter := (SystemRows.e_frame r).2.2
#print axioms SystemRows.imagePacket_data
#print axioms SystemRows.eBranch_exec
#print axioms SystemRows.eBranch_shared
#print axioms SystemRows.eBranch_frame
#print axioms SystemRows.eBranch_fuel_bound
#print axioms SystemRows.e_exec
#print axioms SystemRows.e_shared
#print axioms SystemRows.e_frame
#print axioms SystemRows.e_fuel_bound
#print axioms SystemRows.eIteration
#print axioms SystemRows.e_whole_exec
#print axioms SystemRows.e_scan_bound
end PNP.Concrete.NormalizerBlocks
