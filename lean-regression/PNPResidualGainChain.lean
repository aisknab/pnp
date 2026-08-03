import PNP.LockedNANDResidualGainBound

namespace PNP
namespace DirectWire

def zeroGateIdentityImplementation : Implementation 1 1 :=
  ⟨0, Candidate.ofDirectWireWord identityProgram identityWord⟩

def notImplementation : Implementation 1 1 :=
  ⟨1, Candidate.ofDirectWireWord notProgram notWord⟩

theorem redundantToIdentityGain :
    StrictEquivalentGain redundantIdentityImplementation
      zeroGateIdentityImplementation := by
  constructor
  · exact Nat.zero_lt_succ 0
  · exact identityCandidate_equivalent_redundantIdentity

theorem redundantOneStepChain :
    StrictGainChain redundantIdentityImplementation
      [zeroGateIdentityImplementation] :=
  ⟨redundantToIdentityGain, True.intro⟩

example :
    strictGainChainBool redundantIdentityImplementation
      [zeroGateIdentityImplementation] = true :=
  (strictGainChainBool_eq_true_iff redundantIdentityImplementation
    [zeroGateIdentityImplementation]).mpr redundantOneStepChain

example :
    gainChainEnd redundantIdentityImplementation
      [zeroGateIdentityImplementation] = zeroGateIdentityImplementation := rfl

example :
    [zeroGateIdentityImplementation].length =
      residualSlack redundantIdentityImplementation := by
  simpa only [List.length_cons, List.length_nil] using
    redundantIdentity_positiveSlack.symm

example :
    strictGainChainBool redundantIdentityImplementation
      [redundantIdentityImplementation] = false := rfl

example :
    strictGainChainBool zeroGateIdentityImplementation
      [redundantIdentityImplementation] = false := rfl

example :
    strictGainChainBool notImplementation
      [zeroGateIdentityImplementation] = false := rfl

example (middle finish : Implementation 1 1) :
    ¬StrictGainChain redundantIdentityImplementation [middle, finish] := by
  intro invalid
  have impossible : 2 ≤ 1 := by
    rw [← redundantIdentity_positiveSlack]
    exact invalid.length_le_residualSlack
  exact (by decide : ¬2 ≤ 1) impossible

namespace LockedNANDGlobalCandidates

open LockedNANDTrace

example {inputs : Nat} (circuit : Circuit inputs) :
    strictGainChainBool (fullCandidateImplementation circuit) [] = true := rfl

example {inputs : Nat} (circuit : Circuit inputs)
    {chain : List
      (Implementation (carrierWidth inputs circuit.gateCount)
        (lockedBaselineCount circuit.program + 1))}
    (checked :
      strictGainChainBool (fullCandidateImplementation circuit) chain = true) :
    chain.length ≤ 4 :=
  fullCandidate_strictGainChainBool_length_le_four circuit checked

end LockedNANDGlobalCandidates
end DirectWire
end PNP
