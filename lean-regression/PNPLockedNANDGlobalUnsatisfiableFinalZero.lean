import PNP.LockedNANDGlobalUnsatisfiableFinalZero

namespace PNP.DirectWire.LockedNANDGlobalUnsatisfiableFinalZeroRegression

open LockedNANDTrace
open LockedNANDGlobalCandidates

def zeroInput : Valuation 0 := fun index => Fin.elim0 index

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

def contradictionProgram : Program 1 3 :=
  .snoc
    (.snoc
      (.snoc .empty
        { left := .input fin1Zero
          right := .input fin1Zero })
      { left := .input fin1Zero
        right := .gate fin1Zero })
    { left := .gate fin2One
      right := .gate fin2One }

abbrev contradictionCircuit : Circuit 1 :=
  { gateCount := 3
    program := contradictionProgram
    outputGate := ⟨2, by decide⟩ }

theorem contradictionCircuit_not_satisfiable :
    ¬ contradictionCircuit.Satisfiable := by
  rintro ⟨input, outputTrue⟩
  cases inputValueEqual : input fin1Zero with
  | false =>
      simp [contradictionCircuit, contradictionProgram, Program.eval,
        Valuation.snoc, Gate.eval, Source.eval, boolNand,
        inputValueEqual] at outputTrue
  | true =>
      simp [contradictionCircuit, contradictionProgram, Program.eval,
        Valuation.snoc, Gate.eval, Source.eval, boolNand,
        inputValueEqual] at outputTrue
      exact (by decide : fin2One ≠ (0 : Fin 2)) outputTrue

def allFalseCarrier : Valuation (carrierWidth 0 2) := fun _ => false
def allTrueCarrier : Valuation (carrierWidth 0 2) := fun _ => true

example (input : Valuation (carrierWidth 0 2)) :
    (fullCandidate constantFalseCircuit).semantics input
        (conditionalFinalOutput
          (lockedBaselineCount constantFalseProgram)) =
      false :=
  fullCandidate_final_eq_false_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable input

example :
    (fullCandidate constantFalseCircuit).semantics allFalseCarrier
        (conditionalFinalOutput
          (lockedBaselineCount constantFalseProgram)) =
      false :=
  fullCandidate_final_eq_false_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable
      allFalseCarrier

example :
    (fullCandidate constantFalseCircuit).semantics allTrueCarrier
        (conditionalFinalOutput
          (lockedBaselineCount constantFalseProgram)) =
      false :=
  fullCandidate_final_eq_false_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable
      allTrueCarrier

example (input : Valuation (carrierWidth 0 2)) :
    (fullCandidate constantFalseCircuit).semantics
        (setFinalLockValue input true)
        (conditionalFinalOutput
          (lockedBaselineCount constantFalseProgram)) =
      false :=
  fullCandidate_final_eq_false_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable
      (setFinalLockValue input true)

example :
    referenceMinimum
        (Implementation.mk
          (lockedBaselineCount constantFalseProgram + 4)
          (fullCandidate constantFalseCircuit)) =
      lockedBaselineCount constantFalseProgram :=
  fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable
    constantFalseCircuit constantFalseCircuit_not_satisfiable

example :
    referenceMinimum
        (Implementation.mk
          (lockedBaselineCount contradictionProgram + 4)
          (fullCandidate contradictionCircuit)) =
      lockedBaselineCount contradictionProgram :=
  fullCandidate_referenceMinimum_eq_baseline_of_unsatisfiable
    contradictionCircuit contradictionCircuit_not_satisfiable

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

example :
    (fullCandidate constantTrueCircuit).semantics
        (flattenCarrier
          (coherentExtension constantTrueProgram zeroInput))
        (conditionalFinalOutput
          (lockedBaselineCount constantTrueProgram)) =
      true := by
  rw [fullCandidate_final_semantics_flatten,
    finalConjunction4_spec,
    tracePredicate_coherentExtension]
  rfl

end PNP.DirectWire.LockedNANDGlobalUnsatisfiableFinalZeroRegression
