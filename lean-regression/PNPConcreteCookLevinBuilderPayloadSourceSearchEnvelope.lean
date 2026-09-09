/-
Copyright (c) 2026 PNP Labs.

Encoded-source scalar bounds, a single original-input envelope, and nonduplicating
history accounting. These contracts do not confer complete-builder credit.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchEnvelope

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchEnvelopeRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderPayloadSearchSource
open BuilderPayloadLiteralTokenSelector (Kind Source)
open BuilderPayloadSourceSearchControl (guardedOutside)
open BuilderLiteralSearchFrame (residual)
open BuilderLocalConstraintPayload (front literalValues literalListValues variableValues)
open BuilderPayloadSourceSearchEnvelope

example (polynomial : Kind → NatPolynomial) (kind : Kind) (input : Nat) :
    (polynomial kind).eval input ≤ (kindSum polynomial).eval input :=
  BuilderPayloadSourceSearchEnvelope.kind_le_sum polynomial kind input

example (bound : NatPolynomial) (input : Nat) :
    (envelope bound).eval input = entryBudget (bound.eval input) (bound.eval input + 1) :=
  BuilderPayloadSourceSearchEnvelope.envelope_eval bound input

example (bound ordinal : Nat) :
    entryBudget bound (ordinal + 1) = entryBudget bound ordinal + stepAllowance bound :=
  BuilderPayloadSourceSearchEnvelope.entryBudget_step bound ordinal

example (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input + 1) :
    entryBudget (bound.eval input) ordinal ≤ (envelope bound).eval input :=
  BuilderPayloadSourceSearchEnvelope.entryBudget_le_envelope bound input ordinal hOrdinal

example (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input) :
    entryBudget (bound.eval input) ordinal + stepAllowance (bound.eval input) ≤ (envelope bound).eval input :=
  BuilderPayloadSourceSearchEnvelope.budget_room bound input ordinal hOrdinal

example {width : Nat} (source : Source width) :
    source.originalLiteral.index.val ≤ (front source.slot).sum :=
  BuilderPayloadSourceSearchEnvelope.original_index_le_source_sum source

example {width : Nat} (constraint : LocalConstraint width)
    (index : Fin (body constraint).length) (bound : Nat)
    (hPayload : (front (some (some constraint))).sum ≤ bound) :
    (atSource constraint index).originalLiteral.index.val ≤ bound :=
  BuilderPayloadSourceSearchEnvelope.atSource_value_bound constraint index bound hPayload

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound) :
    (body constraint).length ≤ bound ∧ (front (some (some constraint))).sum ≤ bound ∧ position ≤ bound :=
  BuilderPayloadSourceSearchEnvelope.initial_scalar_bounds constraint request position older outside bound hSpan

example (kind : Kind) (ordinal count position value bound : Nat)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (BuilderPayloadSearchComparison.chunk kind ordinal count position value)).length ≤ 50 * bound + 90 :=
  BuilderPayloadSourceSearchEnvelope.chunk_word_bound kind ordinal count position value bound hOrdinal hCount hPosition hValue

example (count : Nat) (outside : List WorkSymbol) :
    (guardedOutside count outside).length ≤ outside.length + 2 * count + 2 :=
  BuilderPayloadSourceSearchEnvelope.guardedOutside_length_le count outside

example {width : Nat} (source : Source width)
    (ctx : BuilderPayloadLiteralTokenSelector.Context source.ordinal) (outside : List WorkSymbol) :
    (BuilderPayloadSearchComparison.finalOutside source ctx (guardedOutside ctx.remaining outside)).length ≤
      outside.length + 2 * ctx.remaining + 2 :=
  BuilderPayloadSourceSearchEnvelope.comparisonOutside_length_le source ctx outside

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older prior : List Nat) (kind : Kind) (ordinal remaining position value : Nat)
    (outside resultOutside : List WorkSymbol)
    (hExterior : resultOutside.length ≤ outside.length + 2 * (remaining + 1) + 2) :
    (registerWord (initialValues constraint request older
      (prior ++ BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)
      (ordinal + 1) remaining (residual position value))).length + resultOutside.length ≤
    (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length + (registerWord (BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)).length +
        2 * (remaining + 1) + 2 :=
  BuilderPayloadSourceSearchEnvelope.continued_span constraint request older prior kind ordinal remaining position value outside resultOutside hExterior

example {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older prior : List Nat) (kind : Kind) (ordinal remaining position value bound : Nat)
    (outside resultOutside : List WorkSymbol)
    (hOrdinal : ordinal ≤ bound) (hCount : remaining + 1 ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length ≤ entryBudget bound ordinal)
    (hExterior : resultOutside.length ≤ outside.length + 2 * (remaining + 1) + 2) :
    (registerWord (initialValues constraint request older
      (prior ++ BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)
      (ordinal + 1) remaining (residual position value))).length + resultOutside.length ≤ entryBudget bound (ordinal + 1) :=
  BuilderPayloadSourceSearchEnvelope.continued_budget constraint request older prior kind ordinal remaining position value bound outside resultOutside hOrdinal hCount hPosition hValue hSpan hExterior

example : (envelope (.constant 0)).eval 0 = 100 := rfl
example : (kindSum (fun _ => .constant 1)).eval 0 = 4 := rfl
example {width : Nat} (premises : List (BoundedLiteral width)) (resultLiteral : BoundedLiteral width) :
    resultLiteral.index.val ≤ (front (some (some (.implication premises resultLiteral)))).sum :=
  BuilderPayloadSourceSearchEnvelope.original_index_le_source_sum (.conclusion premises resultLiteral)

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchEnvelopeRegression
