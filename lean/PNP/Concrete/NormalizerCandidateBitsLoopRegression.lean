import PNP.Concrete.NormalizerCandidateBitsLoop
namespace PNP.Concrete.NormalizerBlocks
example (r : CandidateBits.State) : (CandidateBits.scan [] r).state.buffer = r.buffer := rfl
example (r : CandidateBits.State) (word : BitString) :
    (CandidateBits.scan word r).state.buffer.length = word.length + r.buffer.length :=
  CandidateBits.scan_buffer_length word r
example (r : CandidateBits.State) : (CandidateBits.whole r).state.remaining = [] :=
  (CandidateBits.scan_fields r.remaining r).2.2.2
example (r : CandidateBits.State) :
    Exec CandidateBits.loop r.store (CandidateBits.whole r).fuel (CandidateBits.whole r).state.store :=
  CandidateBits.whole_exec r
#print axioms CandidateBits.scan_exec
#print axioms CandidateBits.scan_fields
#print axioms CandidateBits.scan_counter
#print axioms CandidateBits.scan_buffer_length
#print axioms CandidateBits.scan_fuel_bound
#print axioms CandidateBits.whole_exec
#print axioms CandidateBits.loopBound_eval
#print axioms CandidateBits.whole_fuel_bound
end PNP.Concrete.NormalizerBlocks
