/-
Copyright (c) 2026 PNP Labs.

Lossless unary-register payload contract for canonical local constraints.
Tags distinguish an absent coordinate, padded empty opportunity, requirement,
implication and exactly-one list. The tag is the last logical register, nearest
the active end. List counts, literal signs and variable bounds are checked.

This is an encoding and size interface for the physical builder, not a machine
that constructs a payload, runs the semantic slot decoder, or emits a formula.
No runtime, complete-builder or reduction claim follows from these definitions.
-/

import PNP.Concrete.CookLevinBuilderConstraintRegionSource

namespace PNP.Concrete.CookLevin.BuilderLocalConstraintPayload

open BuilderUnaryPolynomial

abbrev Slot (width : Nat) := Option (Option (LocalConstraint width))

def signValue (positive : Bool) : Nat := if positive then 1 else 0

def literalValues {width : Nat} (literal : BoundedLiteral width) : List Nat :=
  [signValue literal.positive, literal.index.val]

def literalListValues {width : Nat} : List (BoundedLiteral width) → List Nat
  | [] => []
  | literal :: rest => literalValues literal ++ literalListValues rest

def variableValues {width : Nat} (variables : List (Fin width)) : List Nat :=
  variables.map Fin.val

/-- Reader order. Counts describe the complete list, not a supplied verdict. -/
def front {width : Nat} : Slot width → List Nat
  | none => [0]
  | some none => [1]
  | some (some (.require literal)) => 2 :: literalValues literal
  | some (some (.implication premises conclusion)) =>
      [3, premises.length] ++ literalValues conclusion ++ literalListValues premises
  | some (some (.exactlyOne variables)) => [4, variables.length] ++ variableValues variables

/-- Logical register order puts the tag next to the active end marker. -/
def values {width : Nat} (slot : Slot width) : List Nat := (front slot).reverse

def decodeVariable (width value : Nat) : Option (Fin width) :=
  if h : value < width then some ⟨value, h⟩ else none

def decodeLiteral (width : Nat) : Nat → Nat → Option (BoundedLiteral width)
  | 0, value => (decodeVariable width value).map fun index => ⟨false, index⟩
  | 1, value => (decodeVariable width value).map fun index => ⟨true, index⟩
  | _, _ => none

def decodeLiteralList (width : Nat) : List Nat → Option (List (BoundedLiteral width))
  | [] => some []
  | sign :: value :: rest => do
      let literal ← decodeLiteral width sign value
      let literals ← decodeLiteralList width rest
      pure (literal :: literals)
  | _ => none

def decodeVariables (width : Nat) : List Nat → Option (List (Fin width))
  | [] => some []
  | value :: rest => do
      let index ← decodeVariable width value
      let variables ← decodeVariables width rest
      pure (index :: variables)

/-- The outer result is parse success; its two inner options retain slot semantics. -/
def decodeFront (width : Nat) : List Nat → Option (Slot width)
  | [0] => some none
  | [1] => some (some none)
  | [2, sign, value] =>
      (decodeLiteral width sign value).map fun literal => some (some (.require literal))
  | 3 :: count :: sign :: value :: rest =>
      if rest.length = 2 * count then do
        let conclusion ← decodeLiteral width sign value
        let premises ← decodeLiteralList width rest
        pure (some (some (.implication premises conclusion)))
      else none
  | 4 :: count :: rest =>
      if rest.length = count then
        (decodeVariables width rest).map fun variables => some (some (.exactlyOne variables))
      else none
  | _ => none

def decode (width : Nat) (payload : List Nat) : Option (Slot width) :=
  decodeFront width payload.reverse

theorem decodeVariable_value {width : Nat} (index : Fin width) :
    decodeVariable width index.val = some index := by
  simp only [decodeVariable, dif_pos index.isLt]

theorem decodeLiteral_values {width : Nat} (literal : BoundedLiteral width) :
    decodeLiteral width (signValue literal.positive) literal.index.val = some literal := by
  rcases literal with ⟨positive, index⟩
  cases positive <;> simp only [signValue, Bool.false_eq_true, if_false, if_true,
    decodeLiteral, decodeVariable_value, Option.map_some]

theorem literalListValues_length {width : Nat} (literals : List (BoundedLiteral width)) :
    (literalListValues literals).length = 2 * literals.length := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      simp only [literalListValues, literalValues, List.length_append,
        List.length_cons, List.length_nil, ih]
      omega

theorem decodeLiteralList_values {width : Nat} (literals : List (BoundedLiteral width)) :
    decodeLiteralList width (literalListValues literals) = some literals := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      simp only [literalListValues, literalValues, List.cons_append, List.nil_append,
        decodeLiteralList, decodeLiteral_values, ih]
      rfl

theorem decodeVariables_values {width : Nat} (variables : List (Fin width)) :
    decodeVariables width (variableValues variables) = some variables := by
  induction variables with
  | nil => rfl
  | cons index rest ih =>
      have hRest : decodeVariables width (rest.map Fin.val) = some rest := ih
      simp only [variableValues, List.map_cons, decodeVariables, decodeVariable_value, hRest]
      rfl

theorem decodeFront_front {width : Nat} (slot : Slot width) :
    decodeFront width (front slot) = some slot := by
  cases slot with
  | none => rfl
  | some entry =>
      cases entry with
      | none => rfl
      | some constraint =>
          cases constraint with
          | require literal =>
              simpa only [front, literalValues, decodeFront, Option.map_some] using
                congrArg (Option.map fun item => some (some (LocalConstraint.require item)))
                  (decodeLiteral_values literal)
          | implication premises conclusion =>
              simp only [front, literalValues, List.cons_append, List.nil_append,
                decodeFront, literalListValues_length, ite_true,
                decodeLiteral_values, decodeLiteralList_values]
              rfl
          | exactlyOne variables =>
              have hLength : (variableValues variables).length = variables.length :=
                List.length_map Fin.val
              simp only [front, List.cons_append, List.nil_append, decodeFront,
                hLength, ite_true, decodeVariables_values, Option.map_some]

theorem decode_values {width : Nat} (slot : Slot width) :
    decode width (values slot) = some slot := by
  simp only [decode, values, List.reverse_reverse, decodeFront_front]

theorem values_injective {width : Nat} :
    Function.Injective (values (width := width)) := by
  intro left right hEqual
  have h := congrArg (decode width) hEqual
  rw [decode_values, decode_values] at h
  exact Option.some.inj h

theorem values_ne_nil {width : Nat} (slot : Slot width) : values slot ≠ [] := by
  intro hEmpty
  have h := decode_values slot
  rw [hEmpty] at h
  cases h

theorem absent_ne_padding (width : Nat) :
    values (none : Slot width) ≠ values (some none : Slot width) := by
  intro h
  have hEqual := values_injective h
  cases hEqual

/-- The finite tag schema is independent of source length and constraint size. -/
def tag {width : Nat} : Slot width → Nat
  | none => 0
  | some none => 1
  | some (some (.require _)) => 2
  | some (some (.implication _ _)) => 3
  | some (some (.exactlyOne _)) => 4

theorem tag_le {width : Nat} (slot : Slot width) : tag slot ≤ 4 := by
  cases slot with
  | none => change 0 ≤ 4; omega
  | some entry =>
      cases entry with
      | none => change 1 ≤ 4; omega
      | some constraint => cases constraint <;> simp only [tag] <;> omega

theorem values_tag {width : Nat} (slot : Slot width) :
    ∃ body, values slot = body ++ [tag slot] := by
  cases slot with
  | none => exact ⟨[], rfl⟩
  | some entry =>
      cases entry with
      | none => exact ⟨[], rfl⟩
      | some constraint =>
          cases constraint with
          | require literal =>
              exact ⟨(literalValues literal).reverse, by
                simp only [values, front, tag, List.reverse_cons]⟩
          | implication premises conclusion =>
              exact ⟨(premises.length :: literalValues conclusion ++
                literalListValues premises).reverse, by
                  simp only [values, front, tag, List.cons_append, List.nil_append,
                    List.reverse_cons]⟩
          | exactlyOne variables =>
              exact ⟨(variables.length :: variableValues variables).reverse, by
                simp only [values, front, tag, List.cons_append, List.nil_append,
                  List.reverse_cons]⟩

/-- Only the existing canonical constraint-size interface is needed. -/
def SizeBounded {width : Nat} (bound : Nat) : Slot width → Prop
  | none => True
  | some none => True
  | some (some constraint) => LocalConstraint.SizeBounded bound constraint

theorem values_length_le {width bound : Nat} (slot : Slot width)
    (hBounded : SizeBounded bound slot) :
    (values slot).length ≤ 2 * bound + 10 := by
  cases slot with
  | none => simp only [values, front, List.length_reverse, List.length_cons, List.length_nil]; omega
  | some entry =>
      cases entry with
      | none => simp only [values, front, List.length_reverse, List.length_cons, List.length_nil]; omega
      | some constraint =>
          cases constraint with
          | require literal =>
              simp only [values, front, literalValues, List.length_reverse,
                List.length_cons, List.length_nil]
              omega
          | implication premises conclusion =>
              change premises.length ≤ bound + 3 at hBounded
              simp only [values, front, literalValues, List.length_reverse,
                List.length_append, List.length_cons, List.length_nil, literalListValues_length]
              omega
          | exactlyOne variables =>
              change variables.length ≤ bound at hBounded
              simp only [values, front, variableValues, List.length_reverse,
                List.length_append, List.length_cons, List.length_nil, List.length_map]
              omega

private theorem signValue_le (positive : Bool) : signValue positive ≤ 1 := by
  cases positive <;> decide

private theorem literalValues_le {width bound : Nat} (literal : BoundedLiteral width)
    (hWidth : width ≤ bound) (value : Nat) (hValue : value ∈ literalValues literal) :
    value ≤ 2 * bound + 4 := by
  simp only [literalValues, List.mem_cons, List.not_mem_nil, or_false] at hValue
  rcases hValue with rfl | rfl
  · have h := signValue_le literal.positive
    omega
  · have h := literal.index.isLt
    omega

private theorem literalListValues_le {width bound : Nat} (literals : List (BoundedLiteral width))
    (hWidth : width ≤ bound) (value : Nat) (hValue : value ∈ literalListValues literals) :
    value ≤ 2 * bound + 4 := by
  induction literals with
  | nil => cases hValue
  | cons literal rest ih =>
      rw [literalListValues, List.mem_append] at hValue
      exact hValue.elim (literalValues_le literal hWidth value) ih

theorem values_member_le {width bound : Nat} (slot : Slot width)
    (hWidth : width ≤ bound) (hBounded : SizeBounded bound slot)
    (value : Nat) (hValue : value ∈ values slot) :
    value ≤ 2 * bound + 4 := by
  rw [values, List.mem_reverse] at hValue
  cases slot with
  | none =>
      simp only [front, List.mem_singleton] at hValue
      omega
  | some entry =>
      cases entry with
      | none =>
          simp only [front, List.mem_singleton] at hValue
          omega
      | some constraint =>
          cases constraint with
          | require literal =>
              simp only [front, List.mem_cons] at hValue
              exact hValue.elim (by intro h; omega) (literalValues_le literal hWidth value)
          | implication premises conclusion =>
              change premises.length ≤ bound + 3 at hBounded
              change value ∈ [3, premises.length] ++
                (literalValues conclusion ++ literalListValues premises) at hValue
              rw [List.mem_append] at hValue
              rcases hValue with hHeader | hPayload
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hHeader
                omega
              · rw [List.mem_append] at hPayload
                exact hPayload.elim (literalValues_le conclusion hWidth value)
                  (literalListValues_le premises hWidth value)
          | exactlyOne variables =>
              change variables.length ≤ bound at hBounded
              simp only [front, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hValue
              rcases hValue with (hTag | hCount) | hVariable
              · omega
              · omega
              · obtain ⟨index, _, hIndex⟩ := List.mem_map.mp hVariable
                have hLt := index.isLt
                change index.val = value at hIndex
                omega

private theorem registerWord_length_le (items : List Nat) (bound : Nat)
    (hBound : ∀ item ∈ items, item ≤ bound) :
    (registerWord items).length ≤ items.length * (bound + 1) := by
  induction items with
  | nil => simp only [registerWord, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons item rest ih =>
      have hItem := hBound item (List.mem_cons_self)
      have hRest := ih (fun next hNext => hBound next (List.mem_cons_of_mem item hNext))
      simp only [registerWord, List.length_cons, List.length_append,
        List.length_replicate, Nat.succ_mul]
      omega

def spanBound (bound : Nat) : Nat := (2 * bound + 10) * (2 * bound + 5)

theorem register_span_le {width bound : Nat} (slot : Slot width)
    (hWidth : width ≤ bound) (hBounded : SizeBounded bound slot) :
    (registerWord (values slot)).length ≤ spanBound bound := by
  have hSpan := registerWord_length_le (values slot) (2 * bound + 4)
    (values_member_le slot hWidth hBounded)
  exact Nat.le_trans hSpan
    (Nat.mul_le_mul_right (2 * bound + 5) (values_length_le slot hBounded))

/-- Semantic output specification only: a physical writer must still realize it. -/
def canonicalValues {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) : List Nat :=
  values (problem.formulaConstraintSlotDirect coordinate)

theorem decode_canonicalValues {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    decode problem.FormulaWidth (canonicalValues problem coordinate) =
      some (problem.formulaConstraintSlotDirect coordinate) :=
  decode_values _

theorem canonical_region_eq {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    canonicalValues problem coordinate =
      values (BuilderConstraintRegionSource.slotForCoordinate problem coordinate) := by
  rw [BuilderConstraintRegionSource.slotForCoordinate_eq]
  rfl

theorem canonical_sizeBounded {language : Language} (problem : VerifierTableauProblem language)
    (coordinate : Nat) :
    SizeBounded problem.formulaVariableSlotBound
      (problem.formulaConstraintSlotDirect coordinate) := by
  cases hSlot : problem.formulaConstraintSlotDirect coordinate with
  | none => trivial
  | some entry =>
      cases entry with
      | none => trivial
      | some constraint =>
          apply problem.constraint_sizeBounded_formulaVariableSlotBound constraint
          rw [problem.formulaConstraintSlotDirect_eq] at hSlot
          exact List.mem_of_getElem? hSlot

def sourceSpanPolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  let bound := formulaVariableCountPolynomial verifier
  .mul (.add (.mul (.constant 2) bound) (.constant 10))
    (.add (.mul (.constant 2) bound) (.constant 5))

theorem sourceSpanPolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (sourceSpanPolynomial problem.verifier).eval problem.input.length =
      spanBound problem.formulaVariableSlotBound := by
  rfl

theorem canonical_register_span_le {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    (registerWord (canonicalValues problem coordinate)).length ≤
      (sourceSpanPolynomial problem.verifier).eval problem.input.length := by
  rw [sourceSpanPolynomial_eval]
  exact register_span_le _ problem.formulaWidth_le_formulaVariableCountPolynomial
    (canonical_sizeBounded problem coordinate)

end PNP.Concrete.CookLevin.BuilderLocalConstraintPayload
