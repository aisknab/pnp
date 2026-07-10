/-
Copyright (c) 2026 PNP Labs.

Finite-signature baseline proofs for the five square local locked-NAND macros.
The four-gate final conjunction is intentionally excluded: its single-output
shape does not establish a four-gate minimum through the square-baseline
theorem.  No cross-instance distinctness, global builder, or threshold claim
is made here.
-/

import PNP.DirectWireBaseline
import PNP.LockedNANDDirect

namespace PNP
namespace DirectWire

/-! ## Finite signature bridge -/

def bool2RowValuation (row : Bool2) : Valuation 2 :=
  (emptyValuation.snoc row.x1).snoc row.x2

def bool3RowValuation (row : Bool3) : Valuation 3 :=
  ((emptyValuation.snoc row.x1).snoc row.x2).snoc row.x3

def bool4RowValuation (row : Bool4) : Valuation 4 :=
  (((emptyValuation.snoc row.x1).snoc row.x2).snoc row.x3).snoc row.x4

/-- The truth signature of one candidate output over an explicit finite row
    list. -/
def candidateOutputSignature {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs) (output : Fin outputs) :
    List Bool :=
  rows.map fun input => candidate.semantics (rowValuation input) output

def constantRowSignature {row : Type} (rows : List row) (value : Bool) :
    List Bool :=
  rows.map fun _ => value

def positiveProjectionRowSignature {row : Type} {inputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (input : Fin inputs) : List Bool :=
  rows.map fun row => rowValuation row input

/-- Finite conditions strong enough to construct every witness required by
    `BaselineOutputConditions`.  All inequalities are decidable list facts. -/
def FiniteBaselineSignatures {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs) : Prop :=
  (∀ output,
      candidateOutputSignature rows rowValuation candidate output ≠
          constantRowSignature rows false ∧
        candidateOutputSignature rows rowValuation candidate output ≠
          constantRowSignature rows true ∧
        ∀ input,
          candidateOutputSignature rows rowValuation candidate output ≠
            positiveProjectionRowSignature rows rowValuation input) ∧
    ∀ {leftOutput rightOutput}, leftOutput ≠ rightOutput →
      candidateOutputSignature rows rowValuation candidate leftOutput ≠
        candidateOutputSignature rows rowValuation candidate rightOutput

theorem boolAndTrue_left {left right : Bool}
    (checked : (left && right) = true) : left = true := by
  cases left with
  | false => exact Bool.noConfusion checked
  | true => rfl

theorem boolAndTrue_right {left right : Bool}
    (checked : (left && right) = true) : right = true := by
  cases left with
  | false => exact False.elim (Bool.noConfusion checked)
  | true => exact checked

/-- Decidable finite checker whose soundness supplies the propositional
    signature conditions without requiring a decision procedure for function
    spaces. -/
def finiteBaselineSignatureCheck
    {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs) : Bool :=
  allTrue (allFin outputs) (fun output =>
    decide (candidateOutputSignature rows rowValuation candidate output ≠
      constantRowSignature rows false) &&
    (decide (candidateOutputSignature rows rowValuation candidate output ≠
      constantRowSignature rows true) &&
    allTrue (allFin inputs) (fun input =>
      decide (candidateOutputSignature rows rowValuation candidate output ≠
        positiveProjectionRowSignature rows rowValuation input)))) &&
  allTrue (allFin outputs) (fun leftOutput =>
    allTrue (allFin outputs) (fun rightOutput =>
      if leftOutput = rightOutput then true
      else decide (candidateOutputSignature rows rowValuation candidate leftOutput ≠
        candidateOutputSignature rows rowValuation candidate rightOutput)))

theorem finiteBaselineSignatureCheck_sound
    {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs)
    (checked : finiteBaselineSignatureCheck rows rowValuation candidate = true) :
    FiniteBaselineSignatures rows rowValuation candidate := by
  have outputChecks := boolAndTrue_left checked
  have pairChecks := boolAndTrue_right checked
  constructor
  · intro output
    have outputCheck := allTrue_sound outputChecks (mem_allFin output)
    have notFalseCheck := boolAndTrue_left outputCheck
    have remainingCheck := boolAndTrue_right outputCheck
    have notTrueCheck := boolAndTrue_left remainingCheck
    have projectionChecks := boolAndTrue_right remainingCheck
    refine ⟨of_decide_eq_true notFalseCheck,
      of_decide_eq_true notTrueCheck, ?_⟩
    intro input
    exact of_decide_eq_true
      (allTrue_sound projectionChecks (mem_allFin input))
  · intro leftOutput rightOutput outputDifferent
    have leftChecks := allTrue_sound pairChecks (mem_allFin leftOutput)
    have pairCheck := allTrue_sound leftChecks (mem_allFin rightOutput)
    rw [if_neg outputDifferent] at pairCheck
    exact of_decide_eq_true pairCheck

/-- Unequal Boolean maps over the same finite list expose a concrete row where
    their values differ. -/
theorem exists_row_of_map_ne {row : Type} (rows : List row)
    (left right : row → Bool)
    (different : rows.map left ≠ rows.map right) :
    ∃ item, item ∈ rows ∧ left item ≠ right item := by
  induction rows with
  | nil => exact False.elim (different rfl)
  | cons head tail ih =>
      if headEqual : left head = right head then
        have tailDifferent : tail.map left ≠ tail.map right := by
          intro tailEqual
          apply different
          change left head :: tail.map left = right head :: tail.map right
          rw [headEqual, tailEqual]
        obtain ⟨item, member, itemDifferent⟩ := ih tailDifferent
        exact ⟨item, List.Mem.tail head member, itemDifferent⟩
      else
        exact ⟨head, List.Mem.head _, headEqual⟩

theorem bool_eq_true_of_ne_false (value : Bool) (notFalse : value ≠ false) :
    value = true := by
  cases value with
  | false => exact False.elim (notFalse rfl)
  | true => rfl

theorem bool_eq_false_of_ne_true (value : Bool) (notTrue : value ≠ true) :
    value = false := by
  cases value with
  | false => rfl
  | true => exact False.elim (notTrue rfl)

/-- Convert finite truth-signature inequalities into semantic witnesses. -/
theorem baselineOutputConditions_of_finiteSignatures
    {row : Type} {inputs gates outputs : Nat}
    (rows : List row) (rowValuation : row → Valuation inputs)
    (candidate : Candidate inputs gates outputs)
    (finite : FiniteBaselineSignatures rows rowValuation candidate) :
    BaselineOutputConditions candidate := by
  constructor
  · intro output
    obtain ⟨trueRow, _trueMember, trueDifferent⟩ :=
      exists_row_of_map_ne rows
        (fun row => candidate.semantics (rowValuation row) output)
        (fun _ => false) (finite.1 output).1
    obtain ⟨falseRow, _falseMember, falseDifferent⟩ :=
      exists_row_of_map_ne rows
        (fun row => candidate.semantics (rowValuation row) output)
        (fun _ => true) (finite.1 output).2.1
    refine ⟨rowValuation trueRow, rowValuation falseRow, ?_⟩
    have trueValue := bool_eq_true_of_ne_false
      (candidate.semantics (rowValuation trueRow) output) trueDifferent
    have falseValue := bool_eq_false_of_ne_true
      (candidate.semantics (rowValuation falseRow) output) falseDifferent
    intro equal
    rw [trueValue, falseValue] at equal
    exact Bool.noConfusion equal
  · intro output input
    obtain ⟨row, _member, different⟩ :=
      exists_row_of_map_ne rows
        (fun row => candidate.semantics (rowValuation row) output)
        (fun row => rowValuation row input)
        ((finite.1 output).2.2 input)
    exact ⟨rowValuation row, different⟩
  · intro leftOutput rightOutput outputDifferent
    obtain ⟨row, _member, different⟩ :=
      exists_row_of_map_ne rows
        (fun row => candidate.semantics (rowValuation row) leftOutput)
        (fun row => candidate.semantics (rowValuation row) rightOutput)
        (finite.2 outputDifferent)
    exact ⟨rowValuation row, different⟩

/-! ## Five local finite checks -/

theorem equalityDirect_finiteBaseline :
    FiniteBaselineSignatures boolRows3 bool3RowValuation equalityDirect :=
  finiteBaselineSignatureCheck_sound boolRows3 bool3RowValuation equalityDirect
    (by decide)

theorem constantOneDirect_finiteBaseline :
    FiniteBaselineSignatures boolRows2 bool2RowValuation constantOneDirect :=
  finiteBaselineSignatureCheck_sound boolRows2 bool2RowValuation constantOneDirect
    (by decide)

theorem constantZeroDirect_finiteBaseline :
    FiniteBaselineSignatures boolRows2 bool2RowValuation constantZeroDirect :=
  finiteBaselineSignatureCheck_sound boolRows2 bool2RowValuation constantZeroDirect
    (by decide)

theorem traceDirect_finiteBaseline :
    FiniteBaselineSignatures boolRows4 bool4RowValuation traceDirect :=
  finiteBaselineSignatureCheck_sound boolRows4 bool4RowValuation traceDirect
    (by decide)

theorem prefixAndDirect_finiteBaseline :
    FiniteBaselineSignatures boolRows2 bool2RowValuation prefixAndDirect :=
  finiteBaselineSignatureCheck_sound boolRows2 bool2RowValuation prefixAndDirect
    (by decide)

/-! ## Semantic baseline conditions -/

theorem equalityDirect_baselineOutputConditions :
    BaselineOutputConditions equalityDirect :=
  baselineOutputConditions_of_finiteSignatures boolRows3 bool3RowValuation
    equalityDirect equalityDirect_finiteBaseline

theorem constantOneDirect_baselineOutputConditions :
    BaselineOutputConditions constantOneDirect :=
  baselineOutputConditions_of_finiteSignatures boolRows2 bool2RowValuation
    constantOneDirect constantOneDirect_finiteBaseline

theorem constantZeroDirect_baselineOutputConditions :
    BaselineOutputConditions constantZeroDirect :=
  baselineOutputConditions_of_finiteSignatures boolRows2 bool2RowValuation
    constantZeroDirect constantZeroDirect_finiteBaseline

theorem traceDirect_baselineOutputConditions :
    BaselineOutputConditions traceDirect :=
  baselineOutputConditions_of_finiteSignatures boolRows4 bool4RowValuation
    traceDirect traceDirect_finiteBaseline

theorem prefixAndDirect_baselineOutputConditions :
    BaselineOutputConditions prefixAndDirect :=
  baselineOutputConditions_of_finiteSignatures boolRows2 bool2RowValuation
    prefixAndDirect prefixAndDirect_finiteBaseline

/-! ## Exact local reference minima -/

theorem equalityDirect_referenceMinimum :
    referenceMinimum ⟨10, equalityDirect⟩ = 10 :=
  referenceMinimum_eq_gateCount_of_squareBaseline equalityDirect
    equalityDirect_baselineOutputConditions

theorem constantOneDirect_referenceMinimum :
    referenceMinimum ⟨2, constantOneDirect⟩ = 2 :=
  referenceMinimum_eq_gateCount_of_squareBaseline constantOneDirect
    constantOneDirect_baselineOutputConditions

theorem constantZeroDirect_referenceMinimum :
    referenceMinimum ⟨3, constantZeroDirect⟩ = 3 :=
  referenceMinimum_eq_gateCount_of_squareBaseline constantZeroDirect
    constantZeroDirect_baselineOutputConditions

theorem traceDirect_referenceMinimum :
    referenceMinimum ⟨18, traceDirect⟩ = 18 :=
  referenceMinimum_eq_gateCount_of_squareBaseline traceDirect
    traceDirect_baselineOutputConditions

theorem prefixAndDirect_referenceMinimum :
    referenceMinimum ⟨2, prefixAndDirect⟩ = 2 :=
  referenceMinimum_eq_gateCount_of_squareBaseline prefixAndDirect
    prefixAndDirect_baselineOutputConditions

end DirectWire
end PNP
