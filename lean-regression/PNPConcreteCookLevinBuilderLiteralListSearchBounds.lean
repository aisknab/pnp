import PNP.Concrete.CookLevinBuilderLiteralListSearchBounds

open PNP.Concrete PNP.Concrete.CookLevin
open PipelineTape BuilderUnaryPolynomial
open BuilderLiteralSearchFrame (chunk residual)
open BuilderLiteralListSearch (comparedOutside)
open BuilderLiteralListSearchBounds

-- Independent envelope and complete-runtime contracts.
example : stepAllowance 0 = 100 := rfl
example : entryBudget 1 2 = 401 := rfl
example : (envelope (.constant 1)).eval 99 = 401 := rfl
example (bound ordinal : Nat) : entryBudget bound ordinal ≤ entryBudget bound (ordinal + 1) := by
  rw [entryBudget_step]
  exact Nat.le_add_right _ _
example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    6 * BuilderLiteralListSearch.workSteps literals position ≤ (rawTimePolynomial bound).eval input :=
  (source_polynomial_bounds literals position older outside bound input hSpan).2
example (position : Nat) (older : List Nat) (inside outside : List WorkSymbol)
    (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues ([] : List (BoundedLiteral 0)) position older)).length +
      outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine BuilderLiteralListSearch.machine) rawSteps
        (encodeWorkConfiguration (BuilderLiteralListSearch.initialConfiguration ([] : List (BoundedLiteral 0)) position older inside outside)) =
        encodeWorkConfiguration (BuilderLiteralListSearch.finalConfiguration ([] : List (BoundedLiteral 0)) position older inside outside) ∧
      BuilderLiteralListSearch.observe (BuilderLiteralListSearch.finalConfiguration ([] : List (BoundedLiteral 0)) position older inside outside) = none :=
  uniform_polynomial_lookup ([] : List (BoundedLiteral 0)) position older inside outside bound input hSpan

example (bound : NatPolynomial) (input : Nat) :
    (envelope bound).eval input = entryBudget (bound.eval input) (bound.eval input + 1) :=
  BuilderLiteralListSearchBounds.envelope_eval bound input

example (bound ordinal : Nat) :
    entryBudget bound (ordinal + 1) = entryBudget bound ordinal + stepAllowance bound :=
  BuilderLiteralListSearchBounds.entryBudget_step bound ordinal

example (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input + 1) :
    entryBudget (bound.eval input) ordinal ≤ (envelope bound).eval input :=
  BuilderLiteralListSearchBounds.entryBudget_le_envelope bound input ordinal hOrdinal

example (payload older prior : List Nat) (ordinal remaining position value : Nat)
    (outside : List WorkSymbol) :
    (registerWord (BuilderLiteralSearchComparison.initialValues payload older
      (prior ++ chunk ordinal (remaining + 1) position value) (ordinal + 1) remaining (residual position value))).length +
      (BuilderLiteralSearchAdvance.finalOutside ordinal remaining position value
        (comparedOutside ordinal (remaining + 1) position value outside)).length ≤
    (registerWord (BuilderLiteralSearchComparison.initialValues payload older prior ordinal (remaining + 1) position)).length +
      outside.length + (registerWord (chunk ordinal (remaining + 1) position value)).length + (remaining + 2) :=
  BuilderLiteralListSearchBounds.continued_span payload older prior ordinal remaining position value outside

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    (registerWord (BuilderLiteralListSearch.finalValues literals position older)).length +
      (BuilderLiteralListSearch.finalOutside literals position outside).length ≤ (spanPolynomial bound).eval input ∧
    6 * BuilderLiteralListSearch.workSteps literals position ≤ (rawTimePolynomial bound).eval input :=
  BuilderLiteralListSearchBounds.source_polynomial_bounds literals position older outside bound input hSpan

example {width : Nat} (literals : List (BoundedLiteral width)) (position : Nat)
    (older : List Nat) (inside outside : List WorkSymbol) (bound : NatPolynomial) (input : Nat)
    (hSpan : (registerWord (BuilderLiteralListSearch.initialValues literals position older)).length + outside.length ≤ bound.eval input) :
    ∃ rawSteps, rawSteps ≤ (rawTimePolynomial bound).eval input ∧
      run (compileWorkMachine BuilderLiteralListSearch.machine) rawSteps
        (encodeWorkConfiguration (BuilderLiteralListSearch.initialConfiguration literals position older inside outside)) =
        encodeWorkConfiguration (BuilderLiteralListSearch.finalConfiguration literals position older inside outside) ∧
      BuilderLiteralListSearch.observe (BuilderLiteralListSearch.finalConfiguration literals position older inside outside) =
        DirectToken.boundedLiteralListSlot literals position :=
  BuilderLiteralListSearchBounds.uniform_polynomial_lookup literals position older inside outside bound input hSpan
