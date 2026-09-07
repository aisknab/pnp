/-
Copyright (c) 2026 PNP Labs.
The payload contract must preserve both slot option layers, exact literals and
list order, reject malformed words, and bound actual unary register space.
These examples do not substitute an encoding for physical construction.
-/
import PNP.Concrete.CookLevinBuilderLocalConstraintPayload

namespace PNP.Concrete.CookLevin.BuilderLocalConstraintPayload.Regression

open BuilderUnaryPolynomial

example (width : Nat) : values (none : Slot width) = [0] := rfl
example (width : Nat) : values (some none : Slot width) = [1] := rfl
example (width : Nat) : decode width [0] = some none := rfl
example (width : Nat) : decode width [1] = some (some none) := rfl
example (width : Nat) :
    values (none : Slot width) ≠ values (some none : Slot width) := absent_ne_padding width

example {width : Nat} (slot : Slot width) :
    decode width (values slot) = some slot := decode_values slot

example {width : Nat} (left right : Slot width) (h : values left = values right) :
    left = right := values_injective h

example {width : Nat} (slot : Slot width) : values slot ≠ [] := values_ne_nil slot
example {width : Nat} (slot : Slot width) : tag slot ≤ 4 := tag_le slot
example {width : Nat} (slot : Slot width) :
    ∃ body, values slot = body ++ [tag slot] := values_tag slot

example {width : Nat} (literal : BoundedLiteral width) :
    decode width (values (some (some (.require literal)))) =
      some (some (some (.require literal))) := decode_values _

example {width : Nat} (premises : List (BoundedLiteral width))
    (conclusion : BoundedLiteral width) :
    decode width (values (some (some (.implication premises conclusion)))) =
      some (some (some (.implication premises conclusion))) := decode_values _

example {width : Nat} (variables : List (Fin width)) :
    decode width (values (some (some (.exactlyOne variables)))) =
      some (some (some (.exactlyOne variables))) := decode_values _

example {width : Nat} (literal : BoundedLiteral width) :
    values (some (some (.require literal))) =
      [literal.index.val, signValue literal.positive, 2] := rfl

example : values (some (some (.require (⟨true, ⟨2, by decide⟩⟩ : BoundedLiteral 3)))) =
    [2, 1, 2] := rfl
example : values (some (some (.require (⟨false, ⟨2, by decide⟩⟩ : BoundedLiteral 3)))) =
    [2, 0, 2] := rfl

example : values (some (some (.implication
    ([⟨true, ⟨0, by decide⟩⟩, ⟨false, ⟨1, by decide⟩⟩] : List (BoundedLiteral 3))
    ⟨true, ⟨2, by decide⟩⟩))) = [1, 0, 0, 1, 2, 1, 2, 3] := rfl

example : values (some (some (.exactlyOne
    ([⟨2, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩] : List (Fin 3))))) =
      [1, 0, 2, 3, 4] := rfl

example (width : Nat) :
    decode width [0, 4] = some (some (some (.exactlyOne []))) := rfl

example : decode 3 [2, 1, 0, 3] =
    some (some (some (.implication [] (⟨true, ⟨2, by decide⟩⟩ : BoundedLiteral 3)))) := rfl

-- Invalid tag, missing fields and trailing registers are not padding.
example (width : Nat) : (decode width []).isSome = false := rfl
example (width : Nat) : (decode width [5]).isSome = false := rfl
example (width : Nat) : (decode width [1000000]).isSome = false := rfl
example (width : Nat) : (decode width [0, 0]).isSome = false := rfl
example (width : Nat) : (decode width [0, 1]).isSome = false := rfl
example (width : Nat) : (decode width [2]).isSome = false := rfl
example (width : Nat) : (decode width [3]).isSome = false := rfl
example (width : Nat) : (decode width [4]).isSome = false := rfl
example (width : Nat) : (decode width [0, 0, 0, 2]).isSome = false := rfl
example (width : Nat) : (decode width [0, 2, 2]).isSome = false := rfl
example (width : Nat) : (decode width [0, 1000000, 2]).isSome = false := rfl

-- Width, full list count, signed-pair shape and every member must validate.
example : (decode 0 [0, 1, 2]).isSome = false := rfl
example : (decode 3 [3, 1, 2]).isSome = false := rfl
example : (decode 3 [0, 1000000, 4]).isSome = false := rfl
example : (decode 3 [0, 2, 4]).isSome = false := rfl
example : (decode 3 [3, 1, 4]).isSome = false := rfl
example : (decode 3 [0, 1, 1, 3]).isSome = false := rfl
example : (decode 3 [0, 0, 1, 1, 3]).isSome = false := rfl
example : (decode 3 [0, 2, 0, 1, 1, 3]).isSome = false := rfl
example : (decode 3 [3, 0, 0, 1, 1, 3]).isSome = false := rfl
example : (decode 3 [0, 1, 3, 1, 1, 3]).isSome = false := rfl

example {width : Nat} (literals : List (BoundedLiteral width)) :
    (literalListValues literals).length = 2 * literals.length := literalListValues_length literals
example {width : Nat} (literals : List (BoundedLiteral width)) :
    decodeLiteralList width (literalListValues literals) = some literals := decodeLiteralList_values literals
example {width : Nat} (variables : List (Fin width)) :
    decodeVariables width (variableValues variables) = some variables := decodeVariables_values variables

example {width bound : Nat} (slot : Slot width) (hBounded : SizeBounded bound slot) :
    (values slot).length ≤ 2 * bound + 10 := values_length_le slot hBounded
example {width bound : Nat} (slot : Slot width) (hWidth : width ≤ bound)
    (hBounded : SizeBounded bound slot) (value : Nat) (hValue : value ∈ values slot) :
    value ≤ 2 * bound + 4 := values_member_le slot hWidth hBounded value hValue
example {width bound : Nat} (slot : Slot width) (hWidth : width ≤ bound)
    (hBounded : SizeBounded bound slot) :
    (registerWord (values slot)).length ≤ spanBound bound := register_span_le slot hWidth hBounded

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    decode problem.FormulaWidth (canonicalValues problem coordinate) =
      some (problem.formulaConstraintSlotDirect coordinate) := decode_canonicalValues problem coordinate

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    canonicalValues problem coordinate =
      values (BuilderConstraintRegionSource.slotForCoordinate problem coordinate) :=
  canonical_region_eq problem coordinate

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    SizeBounded problem.formulaVariableSlotBound
      (problem.formulaConstraintSlotDirect coordinate) := canonical_sizeBounded problem coordinate

example {language : Language} (problem : VerifierTableauProblem language) :
    (sourceSpanPolynomial problem.verifier).eval problem.input.length =
      (2 * problem.formulaVariableSlotBound + 10) * (2 * problem.formulaVariableSlotBound + 5) :=
  sourceSpanPolynomial_eval problem

example {language : Language} (problem : VerifierTableauProblem language) (coordinate : Nat) :
    (registerWord (canonicalValues problem coordinate)).length ≤
      (sourceSpanPolynomial problem.verifier).eval problem.input.length :=
  canonical_register_span_le problem coordinate

end PNP.Concrete.CookLevin.BuilderLocalConstraintPayload.Regression
