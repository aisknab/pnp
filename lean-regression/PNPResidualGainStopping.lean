import PNP.ResidualGainStopping

namespace PNP
namespace DirectWire

def stoppingZeroGateIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

theorem stoppingZeroGateIdentityMinimum :
    IsSemanticallyMinimum stoppingZeroGateIdentityImplementation := by
  intro gateCount _candidate _equivalent
  exact Nat.zero_le gateCount

theorem stoppingZeroGateIdentityNoStrictGain :
    ∀ next : Implementation 1 1,
      ¬StrictEquivalentGain stoppingZeroGateIdentityImplementation next :=
  (isSemanticallyMinimum_iff_forall_not_strictEquivalentGain
    stoppingZeroGateIdentityImplementation).mp stoppingZeroGateIdentityMinimum

theorem stoppingRedundantToIdentityGain :
    StrictEquivalentGain redundantIdentityImplementation
      stoppingZeroGateIdentityImplementation := by
  constructor
  · exact Nat.zero_lt_succ 0
  · exact identityCandidate_equivalent_redundantIdentity

theorem stoppingRedundantOneStepChain :
    StrictGainChain redundantIdentityImplementation
      [stoppingZeroGateIdentityImplementation] :=
  ⟨stoppingRedundantToIdentityGain, True.intro⟩

example :
    (referenceMinimumImplementation redundantIdentityImplementation).gateCount =
      referenceMinimum redundantIdentityImplementation :=
  referenceMinimumImplementation_gateCount_eq_referenceMinimum _

example :
    IsSemanticallyMinimum
      (referenceMinimumImplementation redundantIdentityImplementation) :=
  referenceMinimumImplementation_isSemanticallyMinimum _

example :
    residualSlack
      (referenceMinimumImplementation redundantIdentityImplementation) = 0 :=
  referenceMinimumImplementation_residualSlack_eq_zero _

example :
    ∃ next : Implementation 1 1,
      StrictEquivalentGain redundantIdentityImplementation next :=
  (residualSlack_pos_iff_exists_strictEquivalentGain
    redundantIdentityImplementation).mp (by
      rw [redundantIdentity_positiveSlack]
      decide)

example : 0 < residualSlack redundantIdentityImplementation :=
  (residualSlack_pos_iff_exists_strictEquivalentGain
    redundantIdentityImplementation).mpr
      ⟨stoppingZeroGateIdentityImplementation, stoppingRedundantToIdentityGain⟩

example : residualSlack stoppingZeroGateIdentityImplementation = 0 :=
  (residualSlack_eq_zero_iff_forall_not_strictEquivalentGain
    stoppingZeroGateIdentityImplementation).mpr
      stoppingZeroGateIdentityNoStrictGain

example :
    residualSlack
      (gainChainEnd redundantIdentityImplementation
        [stoppingZeroGateIdentityImplementation]) = 0 :=
  StrictGainChain.end_residualSlack_eq_zero_of_no_strictEquivalentGain
    stoppingRedundantOneStepChain stoppingZeroGateIdentityNoStrictGain

def stoppingRedundantExactMinimumResult :
    ExactMinimumResult redundantIdentityImplementation :=
  StrictGainChain.end_exactMinimumResult_of_no_strictEquivalentGain
    stoppingRedundantOneStepChain stoppingZeroGateIdentityNoStrictGain

example :
    stoppingRedundantExactMinimumResult.result =
      stoppingZeroGateIdentityImplementation := rfl

example : stoppingRedundantExactMinimumResult.result.gateCount = 0 := rfl

example :
    strictGainChainBool redundantIdentityImplementation
      [stoppingZeroGateIdentityImplementation] = true :=
  (strictGainChainBool_eq_true_iff redundantIdentityImplementation
    [stoppingZeroGateIdentityImplementation]).mpr stoppingRedundantOneStepChain

example
    (checked : strictGainChainBool redundantIdentityImplementation
      [stoppingZeroGateIdentityImplementation] = true) :
    residualSlack
      (gainChainEnd redundantIdentityImplementation
        [stoppingZeroGateIdentityImplementation]) = 0 :=
  strictGainChainBool_end_residualSlack_eq_zero_of_no_strictEquivalentGain
    checked stoppingZeroGateIdentityNoStrictGain

example
    (checked : strictGainChainBool redundantIdentityImplementation
      [stoppingZeroGateIdentityImplementation] = true) :
    (strictGainChainBool_end_exactMinimumResult_of_no_strictEquivalentGain
      checked stoppingZeroGateIdentityNoStrictGain).result.gateCount = 0 := rfl

example {inputs outputs : Nat} (current : Implementation inputs outputs) :
    IsSemanticallyMinimum current ↔
      ∀ next : Implementation inputs outputs,
        ¬StrictEquivalentGain current next :=
  isSemanticallyMinimum_iff_forall_not_strictEquivalentGain current

end DirectWire
end PNP
