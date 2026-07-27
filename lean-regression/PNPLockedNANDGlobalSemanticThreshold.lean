import PNP.LockedNANDGlobalSemanticThreshold

namespace PNP.DirectWire.LockedNANDGlobalSemanticThresholdRegression

open LockedNANDTrace
open LockedNANDGlobalCandidates

def zeroInput : Valuation 0 := fun index => Fin.elim0 index
def inputFalse : Valuation 1 := fun _ => false

def constantTrueProgram : Program 0 1 :=
  .snoc .empty
    { left := .constant false
      right := .constant false }

abbrev constantTrueCircuit : Circuit 0 :=
  { gateCount := 1
    program := constantTrueProgram
    outputGate := fin1Zero }

theorem constantTrueCircuit_satisfiable :
    constantTrueCircuit.Satisfiable :=
  ⟨zeroInput, rfl⟩

def negationProgram : Program 1 1 :=
  .snoc .empty
    { left := .input fin1Zero
      right := .input fin1Zero }

abbrev negationCircuit : Circuit 1 :=
  { gateCount := 1
    program := negationProgram
    outputGate := fin1Zero }

theorem negationCircuit_satisfiable :
    negationCircuit.Satisfiable :=
  ⟨inputFalse, rfl⟩

def constantFalseProgram : Program 0 2 :=
  .snoc
    (.snoc .empty
      { left := .constant false
        right := .constant false })
    { left := .gate fin1Zero
      right := .gate fin1Zero }

abbrev constantFalseCircuit : Circuit 0 :=
  { gateCount := 2
    program := constantFalseProgram
    outputGate := fin2One }

theorem constantFalseCircuit_not_satisfiable :
    ¬ constantFalseCircuit.Satisfiable := by
  rintro ⟨input, outputTrue⟩
  have inputEqual : input = zeroInput := by
    funext index
    exact Fin.elim0 index
  subst input
  change false = true at outputTrue
  exact Bool.noConfusion outputTrue

example :
    OutputNonconstant (fullCandidate constantTrueCircuit)
      (conditionalFinalOutput
        (lockedBaselineCount constantTrueProgram)) :=
  fullCandidate_final_nonconstant_of_satisfiable
    constantTrueCircuit constantTrueCircuit_satisfiable

example :
    OutputNotPositiveProjection (fullCandidate constantTrueCircuit)
      (conditionalFinalOutput
        (lockedBaselineCount constantTrueProgram)) :=
  fullCandidate_final_notPositiveProjection_of_satisfiable
    constantTrueCircuit constantTrueCircuit_satisfiable

example :
    ∃ valuation,
      (fullCandidate constantTrueCircuit).semantics valuation
          (conditionalFinalOutput
            (lockedBaselineCount constantTrueProgram)) ≠
        valuation (finalLockSlot 0 constantTrueCircuit.gateCount) :=
  (fullCandidate_final_notPositiveProjection_of_satisfiable
    constantTrueCircuit constantTrueCircuit_satisfiable)
      (finalLockSlot 0 constantTrueCircuit.gateCount)

example :
    ∃ valuation,
      (fullCandidate negationCircuit).semantics valuation
          (conditionalFinalOutput
            (lockedBaselineCount negationProgram)) ≠
        valuation (primarySlot (gates := negationCircuit.gateCount) fin1Zero) :=
  (fullCandidate_final_notPositiveProjection_of_satisfiable
    negationCircuit negationCircuit_satisfiable)
      (primarySlot (gates := negationCircuit.gateCount) fin1Zero)

example (output : Fin (lockedBaselineCount constantTrueProgram)) :
    ∃ valuation,
      (fullCandidate constantTrueCircuit).semantics valuation
          (baselineOutputEmbedding output) ≠
        (fullCandidate constantTrueCircuit).semantics valuation
          (conditionalFinalOutput
            (lockedBaselineCount constantTrueProgram)) :=
  fullCandidate_final_distinctFromBaseline_of_satisfiable
    constantTrueCircuit constantTrueCircuit_satisfiable output

example :
    ConditionalFinalOutputSatConditions
      (fullCandidate constantTrueCircuit) :=
  fullCandidate_satisfiableFinalConditions
    constantTrueCircuit constantTrueCircuit_satisfiable

example :
    ConditionalThresholdBoundaryPremises
      constantTrueCircuit.Satisfiable
      (carrierWidth 0 constantTrueCircuit.gateCount)
      (lockedBaselineCount constantTrueProgram) :=
  fullCandidateThresholdPremises constantTrueCircuit

example :
    lockedBaselineCount constantTrueProgram + 1 ≤
        referenceMinimum
          (Implementation.mk
            (lockedBaselineCount constantTrueProgram + 4)
            (fullCandidate constantTrueCircuit)) ∧
      referenceMinimum
          (Implementation.mk
            (lockedBaselineCount constantTrueProgram + 4)
            (fullCandidate constantTrueCircuit)) ≤
        lockedBaselineCount constantTrueProgram + 4 :=
  fullCandidate_referenceMinimum_bounds_of_satisfiable
    constantTrueCircuit constantTrueCircuit_satisfiable

example :
    residualSlack
        (Implementation.mk
          (lockedBaselineCount negationProgram + 4)
          (fullCandidate negationCircuit)) ≤
      4 :=
  fullCandidate_residualSlack_le_four negationCircuit

example :
    constantTrueCircuit.Satisfiable ↔
      lockedBaselineCount constantTrueProgram + 1 ≤
        referenceMinimum
          (Implementation.mk
            (lockedBaselineCount constantTrueProgram + 4)
            (fullCandidate constantTrueCircuit)) :=
  fullCandidate_satisfiable_iff_referenceMinimum_ge_succ
    constantTrueCircuit

example :
    referenceMinimum
        (Implementation.mk
          (lockedBaselineCount constantFalseProgram + 4)
          (fullCandidate constantFalseCircuit)) =
      lockedBaselineCount constantFalseProgram :=
  fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable

example :
    ¬ (lockedBaselineCount constantFalseProgram + 1 ≤
      referenceMinimum
        (Implementation.mk
          (lockedBaselineCount constantFalseProgram + 4)
          (fullCandidate constantFalseCircuit))) := by
  intro crossed
  exact constantFalseCircuit_not_satisfiable
    ((fullCandidate_satisfiable_iff_referenceMinimum_ge_succ
      constantFalseCircuit).2 crossed)

end PNP.DirectWire.LockedNANDGlobalSemanticThresholdRegression
