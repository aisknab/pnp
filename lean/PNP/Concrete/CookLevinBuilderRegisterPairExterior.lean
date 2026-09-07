/-
Copyright (c) 2026 PNP Labs.

The unchanged disposable-pair comparator with an arbitrary exterior suffix.
Boundary safety is checked from the finite rules, then its existing exact trace
is transported. No tape data is replaced by an empty-tail convention.
-/

import PNP.Concrete.WorkMachineLeftBoundary
import PNP.Concrete.CookLevinBuilderRegionResidualSelection

namespace PNP.Concrete.CookLevin.BuilderRegisterPairExterior

open PipelineTape
open BuilderUnaryPolynomial (scratchEndSymbol)
open BuilderDividerOperands (endTape)
open WorkMachineLeftBoundary

private def ruleSafe (rule : WorkRule) : Bool :=
  if rule.readSymbol == scratchEndSymbol then
    (rule.writeSymbol == scratchEndSymbol) && !(rule.move == .left)
  else true

private theorem rules_safe :
    BuilderRegionPairComparison.machine.rules.all ruleSafe = true := by decide

theorem boundary_safe :
    Safe scratchEndSymbol BuilderRegionPairComparison.machine := by
  intro rule hRule hRead
  have hSafe := (List.all_eq_true.mp rules_safe) rule hRule
  simp only [ruleSafe, hRead, beq_self_eq_true, ite_true, Bool.and_eq_true,
    beq_iff_eq] at hSafe
  refine ⟨hSafe.1, ?_⟩
  cases hMove : rule.move with
  | left =>
      intro _
      rw [hMove] at hSafe
      have hFalse : (false : Bool) = true := hSafe.2
      exact Bool.noConfusion hFalse
  | stay =>
      intro hImpossible
      cases hImpossible
  | right =>
      intro hImpossible
      cases hImpossible

def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration BuilderRegionPairComparison.machine
    (endTape (older ++ [coordinate, boundary]) inside outside)

def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) : WorkConfiguration :=
  appendConfiguration
    (BuilderRegionPairComparison.finalConfiguration coordinate boundary older inside) outside

theorem workRunExact (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    workRunExact? BuilderRegionPairComparison.machine
      (BuilderRegionPairComparison.workSteps coordinate boundary)
      (initialConfiguration coordinate boundary older inside outside) =
      some (finalConfiguration coordinate boundary older inside outside) := by
  have hProtected : Protected scratchEndSymbol
      (BuilderRegionPairComparison.initialConfiguration coordinate boundary older inside).tape :=
    Or.inr ⟨rfl, rfl⟩
  exact workRunExact_transport scratchEndSymbol BuilderRegionPairComparison.machine boundary_safe
    (BuilderRegionPairComparison.workSteps coordinate boundary) _ _ outside hProtected
    (BuilderRegionPairComparison.workRunExact coordinate boundary older inside)

theorem run_compile_exact (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    run (compileWorkMachine BuilderRegionPairComparison.machine)
      (6 * BuilderRegionPairComparison.workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older inside outside)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older inside outside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact coordinate boundary older inside outside)

theorem final_tape (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).tape =
      BuilderRegionResidualRegisters.inputTape
        (BuilderRegionResidualRegisters.ofComparison
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary))
        ((BuilderUnaryPolynomial.registerWord older).reverse ++ inside) outside := by
  have hBase :
      (BuilderRegionPairComparison.finalConfiguration coordinate boundary older inside).tape =
        BuilderRegionResidualRegisters.inputTape
          (BuilderRegionResidualRegisters.ofComparison
            (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary))
          ((BuilderUnaryPolynomial.registerWord older).reverse ++ inside) [] := by
    rw [BuilderRegionResidualRegisters.inputTape_ofComparison]
    rfl
  change appendTape
    (BuilderRegionPairComparison.finalConfiguration coordinate boundary older inside).tape outside = _
  rw [hBase]
  generalize BuilderRegionResidualRegisters.ofComparison
    (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary) = view
  rcases view with ⟨a, b, c, d⟩
  cases a <;>
    simp only [BuilderRegionResidualRegisters.inputTape, appendTape,
      BuilderDividerLayout.leftFocus, List.replicate_zero, List.replicate_succ,
      List.nil_append, List.cons_append, List.append_assoc]

theorem final_state (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state =
      if (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary).isLess then
        BuilderRegionPairComparison.machine.acceptState else
        BuilderRegionPairComparison.machine.rejectState := by
  change WorkMachineChain.secondState
    (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
      (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary)).state = _
  rw [BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration_state]
  cases BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate boundary <;> rfl

theorem final_accept_iff (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state =
      BuilderRegionPairComparison.machine.acceptState ↔ coordinate < boundary :=
  BuilderRegionPairComparison.final_accept_iff coordinate boundary older inside

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat)
    (inside outside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside outside).state =
      BuilderRegionPairComparison.machine.rejectState ↔ boundary ≤ coordinate :=
  BuilderRegionPairComparison.final_reject_iff coordinate boundary older inside

end PNP.Concrete.CookLevin.BuilderRegisterPairExterior
