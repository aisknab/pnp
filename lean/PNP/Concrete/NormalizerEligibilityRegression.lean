import PNP.Concrete.NormalizerEligibility

namespace PNP.Concrete.NormalizerBlocks

example : Eligibility.value ⟨true, 0⟩ [] [none] [(⟨true, 0⟩, none)] = none := by decide
example : Eligibility.value ⟨true, 0⟩ [] [none] [(⟨false, 0⟩, none)] = some none := by decide
example : Eligibility.value ⟨false, 0⟩ [[⟨true, 0⟩]] [none] [(⟨true, 0⟩, none)] = some (some ⟨true, 0⟩) := by decide
example : Eligibility.value ⟨false, 0⟩ [[⟨true, 0⟩]] [none] [(⟨true, 0⟩, none), (⟨false, 0⟩, none)] = none := by decide

#print axioms Eligibility.save_exec
#print axioms Eligibility.member_exec
#print axioms Eligibility.restore_exec
#print axioms Eligibility.parentBranch_exec
#print axioms Eligibility.dispatch_exec
#print axioms Eligibility.phase_exec
#print axioms Eligibility.restored_fields
#print axioms Eligibility.phaseFuel_bound
#print axioms Eligibility.phase_canonical

end PNP.Concrete.NormalizerBlocks
