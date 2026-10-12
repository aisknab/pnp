import PNP.Concrete.NormalizerMemberScan

namespace PNP.Concrete.NormalizerBlocks

example (r : TraceMember.State) : (TraceMember.whole r).state.pending = [] := TraceMember.whole_stopped r
example (r : TraceMember.State) :
    (TraceMember.whole r).fuel ≤ (TraceMember.stepBound r + 1) * (r.pending.length + 1) + 1 :=
  TraceMember.whole_fuel_bound r
example (fuel : Nat) (r : TraceMember.State) (h : r.pending = []) :
    TraceMember.scan fuel r = ⟨1, r⟩ := TraceMember.scan_empty fuel r h
example (fuel : Nat) (r : TraceMember.State) :
    (TraceMember.scan fuel r).state.targetTag = r.targetTag := (TraceMember.scan_preserves fuel r).2.1

#print axioms TraceMember.scan_empty
#print axioms TraceMember.scan_step
#print axioms TraceMember.scan_exec
#print axioms TraceMember.scan_fuel_bound
#print axioms TraceMember.scan_stopped
#print axioms TraceMember.scan_preserves
#print axioms TraceMember.whole_exec
#print axioms TraceMember.whole_fuel_bound
#print axioms TraceMember.whole_stopped

end PNP.Concrete.NormalizerBlocks
