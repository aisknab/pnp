import PNP.Concrete.NormalizerCandidateTruth
namespace PNP.Concrete.NormalizerBlocks
open BitRegister Occurrence
example (r : CandidateTruth.State) : (CandidateTruth.literalResult r).registers.output.length = 1 := rfl
example (r : CandidateTruth.State) : (CandidateTruth.literalResult r).matching = r.matching :=
  (CandidateTruth.literal_fields r).2.2.1
example (r : CandidateTruth.State) (sign : Bool) :
    (CandidateTruth.caseCompared sign (r.withRegisters
      {r.registers with output := [sign]})).registers.output = [true] := by
  cases sign <;> rfl
#print axioms CandidateTruth.prepareBit_exec
#print axioms CandidateTruth.readBit_exec
#print axioms CandidateTruth.compareCase_exec
#print axioms CandidateTruth.compare_exec
#print axioms CandidateTruth.literal_exec
#print axioms CandidateTruth.literal_fields
#print axioms CandidateTruth.literal_output
#print axioms CandidateTruth.literal_canonical
#print axioms CandidateTruth.literalFuel_bound
end PNP.Concrete.NormalizerBlocks
