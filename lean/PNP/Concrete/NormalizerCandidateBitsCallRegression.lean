import PNP.Concrete.NormalizerCandidateBitsCall
namespace PNP.Concrete.NormalizerBlocks
example : CandidateBits.values (fun i => i == 1) 0 3 = [false,true,false] := rfl
example (r : CandidateBits.State) : (CandidateBits.called r).registers.output.length = r.remaining.length :=
  CandidateBits.called_output_length r
example (r : CandidateBits.State) (n : Nat) (h : r.store.Bounded n) :
    CandidateBits.callSteps r ≤ CandidateBits.callBound.eval n := CandidateBits.callSteps_bound r n h
example (r : CandidateBits.State) :
    Exec CandidateBits.call r.store (CandidateBits.callSteps r) (CandidateBits.called r).store :=
  CandidateBits.call_exec r
#print axioms CandidateBits.scan_buffer
#print axioms CandidateBits.values_ofFn
#print axioms CandidateBits.start_exec
#print axioms CandidateBits.front_exec
#print axioms CandidateBits.prepareFinish_exec
#print axioms CandidateBits.finish_exec
#print axioms CandidateBits.call_exec
#print axioms CandidateBits.called_fields
#print axioms CandidateBits.called_output_length
#print axioms CandidateBits.called_canonical
#print axioms CandidateBits.callSteps_bound
end PNP.Concrete.NormalizerBlocks
