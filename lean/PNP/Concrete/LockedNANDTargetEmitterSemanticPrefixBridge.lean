/-
Copyright (c) 2026 PNP Labs.

Proof-side identification of the physical newest-first prefix loop with the
independent right-fold semantic schedule.
-/

import PNP.Concrete.LockedNANDTargetEmitterControllerPrefixTrace
import PNP.Concrete.LockedNANDTargetEmitterSemanticFinal

namespace PNP.Concrete.LockedNAND.TargetEmitterSemanticPrefixBridge

open PNP.Concrete

abbrev Runtime := TargetEmitterProgramSemantics.Runtime

private structure CoreEq (left right : Runtime) : Prop where
  captured : left.captured = right.captured
  registers : left.registers = right.registers
  targetTokens : left.targetTokens = right.targetTokens

private theorem poppedRuntime_eq_of_coreEq
    {left right : Runtime} (core : CoreEq left right)
    (prior : List Nat) (value : Nat) :
    TargetEmitterControllerPrefixTrace.poppedRuntime
        left prior value =
      TargetEmitterControllerPrefixTrace.poppedRuntime
        right prior value := by
  rcases core with ⟨captured, registers, targetTokens⟩
  cases left
  cases right
  simp_all [TargetEmitterControllerPrefixTrace.poppedRuntime]

private theorem nextPrefix_popped_coreEq
    (runtime : Runtime) (first second : List Nat)
    (value : Nat) :
    CoreEq
      (TargetEmitterProgramSemantics.nextPrefixResult
        (TargetEmitterControllerPrefixTrace.poppedRuntime
          runtime first value))
      (TargetEmitterProgramSemantics.nextPrefixResult
        (TargetEmitterControllerPrefixTrace.poppedRuntime
          runtime second value)) := by
  refine
    { captured := rfl
      registers := ?_
      targetTokens := ?_ }
  · rw [TargetEmitterProgramSemantics.nextPrefixResult_registers,
      TargetEmitterProgramSemantics.nextPrefixResult_registers]
    simp [TargetEmitterControllerPrefixTrace.poppedRuntime]
  · rw [TargetEmitterProgramSemantics.nextPrefixResult_targetTokens,
      TargetEmitterProgramSemantics.nextPrefixResult_targetTokens]
    simp [TargetEmitterControllerPrefixTrace.poppedRuntime]

private theorem firstPrefix_popped_coreEq
    (runtime : Runtime) (first second : List Nat)
    (next newest : Nat) :
    CoreEq
      (TargetEmitterProgramSemantics.firstPrefixResult
        (TargetEmitterControllerPrefixTrace.poppedRuntime
          runtime (first ++ [next]) newest)
        first next)
      (TargetEmitterProgramSemantics.firstPrefixResult
        (TargetEmitterControllerPrefixTrace.poppedRuntime
          runtime (second ++ [next]) newest)
        second next) := by
  refine
    { captured := rfl
      registers := ?_
      targetTokens := ?_ }
  · rw [TargetEmitterProgramSemantics.firstPrefixResult_registers,
      TargetEmitterProgramSemantics.firstPrefixResult_registers]
    simp [TargetEmitterControllerPrefixTrace.poppedRuntime]
  · rw [TargetEmitterProgramSemantics.firstPrefixResult_targetTokens,
      TargetEmitterProgramSemantics.firstPrefixResult_targetTokens]
    simp [TargetEmitterControllerPrefixTrace.poppedRuntime]

private theorem nextPrefixLoop_eq_of_coreEq
    {left right : Runtime} (values : List Nat)
    (nonempty : values ≠ [])
    (core : CoreEq left right) :
    TargetEmitterControllerPrefixTrace.nextPrefixLoop values left =
      TargetEmitterControllerPrefixTrace.nextPrefixLoop values right := by
  cases values with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons value rest =>
      rw [TargetEmitterControllerPrefixTrace.nextPrefixLoop,
        TargetEmitterControllerPrefixTrace.nextPrefixLoop]
      rw [poppedRuntime_eq_of_coreEq core rest.reverse value]

private theorem nextPrefixLoop_append_single
    (runtime : Runtime) (values : List Nat) (value : Nat) :
    TargetEmitterControllerPrefixTrace.nextPrefixLoop
        (values ++ [value]) runtime =
      TargetEmitterProgramSemantics.nextPrefixResult
        (TargetEmitterControllerPrefixTrace.poppedRuntime
          (TargetEmitterControllerPrefixTrace.nextPrefixLoop
            values runtime)
          [] value) := by
  induction values generalizing runtime with
  | nil =>
      rfl
  | cons head rest inductionHypothesis =>
      rw [List.cons_append,
        TargetEmitterControllerPrefixTrace.nextPrefixLoop]
      change
        TargetEmitterControllerPrefixTrace.nextPrefixLoop
            (rest ++ [value])
            (TargetEmitterProgramSemantics.nextPrefixResult
              (TargetEmitterControllerPrefixTrace.poppedRuntime
                runtime (rest ++ [value]).reverse head)) =
          TargetEmitterProgramSemantics.nextPrefixResult
            (TargetEmitterControllerPrefixTrace.poppedRuntime
              (TargetEmitterControllerPrefixTrace.nextPrefixLoop rest
                (TargetEmitterProgramSemantics.nextPrefixResult
                  (TargetEmitterControllerPrefixTrace.poppedRuntime
                    runtime rest.reverse head)))
              [] value)
      rw [nextPrefixLoop_eq_of_coreEq (rest ++ [value])
        (by simp)
        (nextPrefix_popped_coreEq runtime
          (rest ++ [value]).reverse rest.reverse head)]
      exact inductionHypothesis
        (TargetEmitterProgramSemantics.nextPrefixResult
          (TargetEmitterControllerPrefixTrace.poppedRuntime
            runtime rest.reverse head))

private theorem rawNonemptyPrefixResult_eq_of_coreEq
    {left right : Runtime} (core : CoreEq left right)
    (prior : List Nat) (second newest : Nat) :
    TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
        left prior second newest =
      TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
        right prior second newest := by
  unfold TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
  rw [poppedRuntime_eq_of_coreEq core
    (prior ++ [second]) newest]

private theorem rawNonempty_cons_tail_coreEq
    (runtime : Runtime) (head : Nat) (rest : List Nat)
    (second newest : Nat) :
    CoreEq
      (TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
        runtime rest second newest)
      (TargetEmitterControllerPrefixTrace.nextPrefixLoop
        rest.reverse
        (TargetEmitterProgramSemantics.firstPrefixResult
          (TargetEmitterControllerPrefixTrace.poppedRuntime
            runtime ((head :: rest) ++ [second]) newest)
          (head :: rest) second)) := by
  unfold TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
  have startCore :=
    firstPrefix_popped_coreEq runtime rest
      (head :: rest) second newest
  cases rest with
  | nil =>
      simpa [TargetEmitterControllerPrefixTrace.nextPrefixLoop] using
        startCore
  | cons next tail =>
      have loops :=
        nextPrefixLoop_eq_of_coreEq
          (next :: tail).reverse (by simp) startCore
      rw [loops]
      exact
        { captured := rfl
          registers := rfl
          targetTokens := rfl }

private theorem runPrefix_cons_append_pair_step
    (runtime : Runtime) (head : Nat) (rest : List Nat)
    (second newest : Nat) :
    (TargetEmitterSemanticPrefix.runPrefix
      (head :: rest ++ [second, newest]) runtime).runtime =
        TargetEmitterProgramSemantics.nextPrefixResult
          { (TargetEmitterSemanticPrefix.runPrefix
              (rest ++ [second, newest])
              { runtime with
                checks := rest ++ [second, newest] }).runtime with
            scratch := head
            checks := [] } := by
  cases rest with
  | nil =>
      simp only [List.nil_append, List.cons_append]
      rw [TargetEmitterSemanticPrefix.runPrefix.eq_def]
  | cons next tail =>
      cases tail <;>
        simp only [List.nil_append, List.cons_append] <;>
        rw [TargetEmitterSemanticPrefix.runPrefix.eq_def]

/-- The physical nonempty prefix loop is the runtime component of the
independent right-fold schedule on the same oldest-first stack. -/
theorem runPrefix_append_pair_runtime
    (runtime : Runtime) (prior : List Nat)
    (second newest : Nat) :
    (TargetEmitterSemanticPrefix.runPrefix
      (prior ++ [second, newest]) runtime).runtime =
        TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
          runtime prior second newest := by
  induction prior generalizing runtime with
  | nil =>
      simp [TargetEmitterSemanticPrefix.runPrefix,
        TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult,
          TargetEmitterControllerPrefixTrace.nextPrefixLoop,
        TargetEmitterControllerPrefixTrace.poppedRuntime]
  | cons head rest inductionHypothesis =>
      rw [runPrefix_cons_append_pair_step]
      let tailInput : Runtime :=
        { runtime with checks := rest ++ [second, newest] }
      rw [show
        (TargetEmitterSemanticPrefix.runPrefix
          (rest ++ [second, newest]) tailInput).runtime =
            TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
              tailInput rest second newest by
          exact inductionHypothesis tailInput]
      rw [rawNonemptyPrefixResult_eq_of_coreEq
        (left := tailInput) (right := runtime)
        (by
          exact
            { captured := rfl
              registers := rfl
              targetTokens := rfl })
        rest second newest]
      unfold
        TargetEmitterControllerPrefixTrace.rawNonemptyPrefixResult
      rw [List.reverse_cons, nextPrefixLoop_append_single]
      apply congrArg TargetEmitterProgramSemantics.nextPrefixResult
      exact poppedRuntime_eq_of_coreEq
        (rawNonempty_cons_tail_coreEq runtime head rest
          second newest)
        [] head

end PNP.Concrete.LockedNAND.TargetEmitterSemanticPrefixBridge
