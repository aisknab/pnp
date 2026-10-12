import PNP.Concrete.NormalizerCandidateBitsBody
namespace PNP.Concrete.NormalizerBlocks
example (r : CandidateBits.State) : (CandidateBits.bodyResult r).counter = true::r.counter :=
  (CandidateBits.body_fields r).2.2.2.2
example (r : CandidateBits.State) : (CandidateBits.bodyResult r).remaining = r.remaining.tail :=
  (CandidateBits.body_fields r).2.2.2.1
example (r : CandidateBits.State) :
    Exec CandidateBits.body r.store (CandidateBits.bodyFuel r) (CandidateBits.bodyResult r).store :=
  CandidateBits.body_exec r
#print axioms CandidateBits.liftCore_exec
#print axioms CandidateBits.load_exec
#print axioms CandidateBits.query_exec
#print axioms CandidateBits.append_exec
#print axioms CandidateBits.advance_exec
#print axioms CandidateBits.body_exec
#print axioms CandidateBits.body_fields
#print axioms CandidateBits.body_buffer
#print axioms CandidateBits.bodyFuel_bound
end PNP.Concrete.NormalizerBlocks
