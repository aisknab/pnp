/-
Copyright (c) 2026 PNP Labs.

One original-input envelope for source-body search. Actual variable indices are
bounded by the encoded source payload, and each retained miss is charged once.
These bounds support the whole-loop trace induction; they do not alone assert
a complete polynomial Cook-Levin builder.
-/
import PNP.Concrete.CookLevinBuilderPayloadSourceSearchControl

namespace PNP.Concrete.CookLevin.BuilderPayloadSourceSearchEnvelope

open PipelineTape BuilderUnaryPolynomial
open BuilderPayloadSearchSource
open BuilderPayloadLiteralTokenSelector (Kind Source)
open BuilderPayloadSourceSearchControl (guardedOutside)
open BuilderLiteralSearchFrame (residual)
open BuilderLocalConstraintPayload (front literalValues literalListValues variableValues)

def stepAllowance (bound : Nat) : Nat := 100 * bound + 100
def entryBudget (bound ordinal : Nat) : Nat := bound + ordinal * stepAllowance bound
def envelope (bound : NatPolynomial) : NatPolynomial := BuilderLiteralSearchFrame.globalSpanPolynomial bound

def kindSum (polynomial : Kind → NatPolynomial) : NatPolynomial :=
  .add (polynomial .required) (.add (polynomial .premise) (.add (polynomial .conclusion) (polynomial .positive)))
def passRawPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderLiteralSearchGuard.rawTimePolynomial (envelope bound))
    (.add (BuilderPayloadConclusionGuard.rawTimePolynomial (envelope bound))
      (.add (kindSum fun kind => BuilderPayloadSearchComparison.rawTimePolynomial kind (envelope bound))
        (.add (BuilderPayloadSearchAdvance.rawTimePolynomial (envelope bound))
          (.add (kindSum fun kind => BuilderPayloadSearchHit.rawTimePolynomial kind (envelope bound)) (.constant 24)))))
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .mul (.add bound (.constant 1)) (passRawPolynomial bound)
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (envelope bound) (kindSum fun kind => BuilderPayloadSearchHit.spanPolynomial kind (envelope bound))

theorem kind_le_sum (polynomial : Kind → NatPolynomial) (kind : Kind) (input : Nat) :
    (polynomial kind).eval input ≤ (kindSum polynomial).eval input := by
  cases kind <;> simp only [kindSum, NatPolynomial.eval_add] <;> omega

theorem envelope_eval (bound : NatPolynomial) (input : Nat) :
    (envelope bound).eval input = entryBudget (bound.eval input) (bound.eval input + 1) := rfl

theorem entryBudget_step (bound ordinal : Nat) :
    entryBudget bound (ordinal + 1) = entryBudget bound ordinal + stepAllowance bound := by
  simp only [entryBudget, Nat.add_mul, Nat.one_mul, Nat.add_assoc]

theorem entryBudget_le_envelope (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input + 1) :
    entryBudget (bound.eval input) ordinal ≤ (envelope bound).eval input := by
  rw [envelope_eval]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hOrdinal) _

theorem budget_room (bound : NatPolynomial) (input ordinal : Nat)
    (hOrdinal : ordinal ≤ bound.eval input) :
    entryBudget (bound.eval input) ordinal + stepAllowance (bound.eval input) ≤ (envelope bound).eval input := by
  rw [← entryBudget_step]
  apply entryBudget_le_envelope
  omega

private theorem getElem_le_sum (values : List Nat) (ordinal : Nat) (hOrdinal : ordinal < values.length) :
    values[ordinal] ≤ values.sum := by
  induction values generalizing ordinal with
  | nil => simp only [List.length_nil] at hOrdinal; omega
  | cons value rest ih =>
      cases ordinal with
      | zero =>
          simp only [List.getElem_cons_zero, List.sum_cons]
          omega
      | succ ordinal =>
          have hRest : ordinal < rest.length := by simp only [List.length_cons] at hOrdinal; omega
          have h := ih ordinal hRest
          simp only [List.getElem_cons_succ, List.sum_cons]
          omega

/-- The semantic width is not the cost parameter: the actual index occurs in
the source payload itself, including the implication's physically early conclusion. -/
theorem original_index_le_source_sum {width : Nat} (source : Source width) :
    source.originalLiteral.index.val ≤ (front source.slot).sum := by
  cases source with
  | required literal =>
      simp only [Source.originalLiteral, Source.slot, front, literalValues, List.sum_cons, List.sum_nil]
      omega
  | premise premises resultLiteral index =>
      have h := getElem_le_sum (literalListValues premises) (2 * index.val + 1)
        (BuilderPayloadFieldCopy.literal_field_lt premises index.val index.isLt ⟨1, by decide⟩)
      rw [BuilderPayloadFieldCopy.literal_field_value premises index.val index.isLt ⟨1, by decide⟩] at h
      change premises[index.val].index.val ≤ (literalListValues premises).sum at h
      simp only [Source.originalLiteral, Source.slot, front, literalValues,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega
  | conclusion premises literal =>
      simp only [Source.originalLiteral, Source.slot, front, literalValues,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega
  | positive variables index =>
      have hIndex : index.val < (variableValues variables).length := by
        simpa only [variableValues, List.length_map] using index.isLt
      have h := getElem_le_sum (variableValues variables) index.val hIndex
      simp only [variableValues, List.getElem_map] at h
      simp only [Source.originalLiteral, Source.slot, front, variableValues,
        List.sum_append, List.sum_cons, List.sum_nil]
      omega

theorem atSource_value_bound {width : Nat} (constraint : LocalConstraint width)
    (index : Fin (body constraint).length) (bound : Nat)
    (hPayload : (front (some (some constraint))).sum ≤ bound) :
    (atSource constraint index).originalLiteral.index.val ≤ bound := by
  have h := original_index_le_source_sum (atSource constraint index)
  rw [atSource_slot] at h
  exact Nat.le_trans h hPayload

theorem initial_scalar_bounds {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (position : Nat) (older : List Nat) (outside : List WorkSymbol) (bound : Nat)
    (hSpan : (registerWord (initialValues constraint request older [] 0 (body constraint).length position)).length +
      outside.length ≤ bound) :
    (body constraint).length ≤ bound ∧ (front (some (some constraint))).sum ≤ bound ∧ position ≤ bound := by
  simp only [initialValues, baseValues, requestValues, BuilderLocalConstraintPayload.values,
    registerWord_length, List.sum_append, List.sum_reverse, List.length_append, List.length_reverse,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil] at hSpan
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem chunk_word_bound (kind : Kind) (ordinal count position value bound : Nat)
    (hOrdinal : ordinal ≤ bound) (hCount : count ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound) :
    (registerWord (BuilderPayloadSearchComparison.chunk kind ordinal count position value)).length ≤ 50 * bound + 90 := by
  have hOld := BuilderLiteralSearchFrame.chunk_word_le ordinal count position value bound hOrdinal hCount hPosition hValue
  have hNew := BuilderPayloadSearchComparison.chunk_word_le_old_add_thirty kind ordinal count position value
  omega

theorem guardedOutside_length_le (count : Nat) (outside : List WorkSymbol) :
    (guardedOutside count outside).length ≤ outside.length + 2 * count + 2 := by
  have hZero := BuilderLiteralSearchGuard.finalOutside_length_le count outside
  have hOne := BuilderPayloadConclusionGuard.finalOutside_length_le count
    (BuilderLiteralSearchGuard.finalOutside count outside)
  unfold guardedOutside
  omega

theorem comparisonOutside_length_le {width : Nat} (source : Source width)
    (ctx : BuilderPayloadLiteralTokenSelector.Context source.ordinal) (outside : List WorkSymbol) :
    (BuilderPayloadSearchComparison.finalOutside source ctx (guardedOutside ctx.remaining outside)).length ≤
      outside.length + 2 * ctx.remaining + 2 := by
  have hGuards := guardedOutside_length_le ctx.remaining outside
  have hCompare := BuilderPayloadSearchComparison.finalOutside_length_le source ctx (guardedOutside ctx.remaining outside)
  omega

/-- The next physical frame is charged only for its newly retained chunk.
The cursor does not duplicate the old register file or increase the residual. -/
theorem continued_span {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older prior : List Nat) (kind : Kind) (ordinal remaining position value : Nat)
    (outside resultOutside : List WorkSymbol)
    (hExterior : resultOutside.length ≤ outside.length + 2 * (remaining + 1) + 2) :
    (registerWord (initialValues constraint request older
      (prior ++ BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)
      (ordinal + 1) remaining (residual position value))).length + resultOutside.length ≤
    (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length + (registerWord (BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)).length +
        2 * (remaining + 1) + 2 := by
  have hResidual := BuilderLiteralSearchFrame.residual_le position value
  simp only [initialValues, baseValues, registerWord_length, List.length_append, List.sum_append,
    List.length_cons, List.length_nil, List.sum_cons, List.sum_nil]
  omega

theorem continued_budget {width : Nat} (constraint : LocalConstraint width) (request : Request)
    (older prior : List Nat) (kind : Kind) (ordinal remaining position value bound : Nat)
    (outside resultOutside : List WorkSymbol)
    (hOrdinal : ordinal ≤ bound) (hCount : remaining + 1 ≤ bound)
    (hPosition : position ≤ bound) (hValue : value ≤ bound)
    (hSpan : (registerWord (initialValues constraint request older prior ordinal (remaining + 1) position)).length +
      outside.length ≤ entryBudget bound ordinal)
    (hExterior : resultOutside.length ≤ outside.length + 2 * (remaining + 1) + 2) :
    (registerWord (initialValues constraint request older
      (prior ++ BuilderPayloadSearchComparison.chunk kind ordinal (remaining + 1) position value)
      (ordinal + 1) remaining (residual position value))).length + resultOutside.length ≤ entryBudget bound (ordinal + 1) := by
  have hNext := continued_span constraint request older prior kind ordinal remaining position value outside resultOutside hExterior
  have hChunk := chunk_word_bound kind ordinal (remaining + 1) position value bound hOrdinal hCount hPosition hValue
  rw [entryBudget_step]
  unfold stepAllowance
  omega

end PNP.Concrete.CookLevin.BuilderPayloadSourceSearchEnvelope
