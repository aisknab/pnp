/-
Copyright (c) 2026 PNP Labs.
Prepared all-value equality, branching and scratch-restoration contracts.
A zero first coordinate below the boundary must not take the diagonal branch.
-/
import PNP.Concrete.CookLevinBuilderRegisterEquality

namespace PNP.Concrete.CookLevin.BuilderRegisterEquality.Regression

open BuilderUnaryPolynomial (registerWord)
open BuilderDividerOperands (endTape)

example : graph.nodes.length = 4 := rfl
example : compareNode.program = BuilderRegionResidualSelection.machine := rfl
example : compareNode.onAccept = .node eraseUnequalNode.reference := rfl
example : compareNode.onReject = .node zeroNode.reference := rfl
example : zeroNode.program = BuilderUnaryTagMatch.machine 0 := rfl
example : zeroNode.onAccept = .node eraseEqualNode.reference := rfl
example : zeroNode.onReject = .node eraseUnequalNode.reference := rfl
example : eraseEqualNode.program = BuilderRegisterErase.machine 4 := rfl
example : eraseUnequalNode.program = BuilderRegisterErase.machine 4 := rfl
example : graph.WellFormed := graph_wellFormed

example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary) (initialConfiguration coordinate boundary older inside) =
      some (finalConfiguration coordinate boundary older inside) := workRunExact coordinate boundary older inside
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
      (encodeWorkConfiguration (initialConfiguration coordinate boundary older inside)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older inside) := run_compile_exact coordinate boundary older inside
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).state = machine.acceptState ↔ coordinate = boundary :=
  final_accept_iff coordinate boundary older inside
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).state = machine.rejectState ↔ coordinate ≠ boundary :=
  final_reject_iff coordinate boundary older inside

example (coordinate : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate coordinate older inside).state = machine.acceptState :=
  (final_accept_iff coordinate coordinate older inside).2 rfl
example (boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration 0 (boundary + 1) older inside).state = machine.rejectState :=
  (final_reject_iff 0 (boundary + 1) older inside).2 (by omega)
example (boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration (boundary + 1) boundary older inside).state = machine.rejectState :=
  (final_reject_iff (boundary + 1) boundary older inside).2 (by omega)
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) (hLess : coordinate < boundary) :
    (finalConfiguration coordinate boundary older inside).state ≠ machine.acceptState := by
  intro hAccept
  have hEqual := (final_accept_iff coordinate boundary older inside).1 hAccept
  omega
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).tape =
      endTape older inside (List.replicate (clearedSpan coordinate boundary) .blank) := final_tape coordinate boundary older inside
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).tape.right = (registerWord older).reverse ++ inside := rfl
example (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration coordinate boundary older inside).tape.left.length = clearedSpan coordinate boundary := by
  change (List.replicate (clearedSpan coordinate boundary) WorkSymbol.blank).length = _
  exact List.length_replicate
example (coordinate boundary bound : Nat) (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    clearedSpan coordinate boundary ≤ 4 + 4 * bound := clearedSpan_le coordinate boundary bound hCoordinate hBoundary
example (coordinate boundary inputLength : Nat) (bound : NatPolynomial)
    (hCoordinate : coordinate ≤ bound.eval inputLength) (hBoundary : boundary ≤ bound.eval inputLength) :
    clearedSpan coordinate boundary ≤ 4 + 4 * bound.eval inputLength ∧
      6 * workSteps coordinate boundary ≤ (rawTimePolynomial bound).eval inputLength :=
  source_polynomial_bounds coordinate boundary inputLength bound hCoordinate hBoundary

example : machine.rules.Pairwise WorkMachineChain.QueryDistinct := rules_pairwise_query_distinct
example : WorkMachineChain.NoRuleAtAccept machine := noRuleAtAccept
example : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := noRuleAtReject
example : machine.acceptState ≠ machine.rejectState := acceptState_ne_rejectState

end PNP.Concrete.CookLevin.BuilderRegisterEquality.Regression
