import PNP.Concrete.NormalizerCutSelectionCall
namespace PNP.Concrete.NormalizerBlocks
example (tag : Bool) (r : CutSelection.State) (bound : Nat) (h : r.store.Bounded bound) :
    CutSelection.callSteps tag r ≤ CutSelection.callBound.eval bound :=
  CutSelection.callSteps_bound tag r bound h
example (tag : Bool) (r : CutSelection.State) (trace : List TraceData.Row)
    (hc : r.registers.target = []) (ht : r.registers.input = TraceData.encode trace) :
    (CutSelection.called tag r).registers.output = [true,false] := by
  rw [CutSelection.called_canonical tag r 0 trace hc ht]
  rfl
#print axioms CutSelection.callFront_exec
#print axioms CutSelection.callFrontSteps_bound
#print axioms CutSelection.call_exec
#print axioms CutSelection.callSteps_bound
#print axioms CutSelection.called_canonical
end PNP.Concrete.NormalizerBlocks
