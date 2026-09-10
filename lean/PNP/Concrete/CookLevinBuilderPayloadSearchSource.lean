/-
Copyright (c) 2026 PNP Labs.

Canonical source-family and ordinal invariants for the complete payload search.
The body is derived from the actual local constraint. Indexed literal adapters
are derived from that body's valid index; no replacement literal or coverage
certificate is an input to the runtime machine.

The full guarded cycle and source-request dispatcher remain separate composition
obligations. These semantic refinements do not award complete-builder credit.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchHit
import PNP.Concrete.CookLevinBuilderPayloadConclusionGuard

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchSource

open PipelineTape BuilderUnaryPolynomial
open BuilderPayloadLiteralTokenSelector (Kind Source Context)

inductive Family where
  | required | implication | positive
  deriving DecidableEq, Repr

def family {width : Nat} : LocalConstraint width → Family
  | .require _ => .required
  | .implication _ _ => .implication
  | .exactlyOne _ => .positive
def bodyKind : Family → Kind
  | .required => .required
  | .implication => .premise
  | .positive => .positive
def lastKind : Family → Kind
  | .required => .required
  | .implication => .conclusion
  | .positive => .positive
def kindAt (family : Family) (count : Nat) : Kind :=
  if count = 1 then lastKind family else bodyKind family
def body {width : Nat} : LocalConstraint width → List (BoundedLiteral width)
  | .require literal => [literal]
  | .implication premises resultLiteral => BoundedClause.negated premises ++ [resultLiteral]
  | .exactlyOne variables => variables.map fun index => ⟨true, index⟩

theorem body_first_clause {width : Nat} (constraint : LocalConstraint width) :
    constraint.emit[0]? = some (body constraint) := by
  cases constraint <;> rfl

theorem body_implication_length {width : Nat} (premises : List (BoundedLiteral width))
    (resultLiteral : BoundedLiteral width) :
    (body (.implication premises resultLiteral)).length = premises.length + 1 := by
  simp only [body, BoundedClause.negated, List.length_append, List.length_map,
    List.length_cons, List.length_nil]
theorem body_positive_length {width : Nat} (variables : List (Fin width)) :
    (body (.exactlyOne variables)).length = variables.length := by
  simp only [body, List.length_map]

def atSource {width : Nat} : (constraint : LocalConstraint width) → Fin (body constraint).length → Source width
  | .require literal, _ => .required literal
  | .implication premises resultLiteral, index =>
      if h : index.val < premises.length then .premise premises resultLiteral ⟨index.val, h⟩
      else .conclusion premises resultLiteral
  | .exactlyOne variables, index =>
      .positive variables ⟨index.val, by simpa only [body_positive_length] using index.isLt⟩

theorem atSource_ordinal {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).ordinal = index.val := by
  cases constraint with
  | require literal =>
      have h := index.isLt
      change index.val < 1 at h
      change 0 = index.val
      omega
  | implication premises resultLiteral =>
      have h : index.val < premises.length + 1 := by
        simpa only [body_implication_length] using index.isLt
      simp only [atSource]
      split
      · rfl
      · change premises.length = index.val
        omega
  | exactlyOne variables => rfl

theorem atSource_slot {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).slot = some (some constraint) := by
  cases constraint with
  | require literal => rfl
  | implication premises resultLiteral => simp only [atSource]; split <;> rfl
  | exactlyOne variables => rfl

theorem atSource_selected {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).selectedLiteral = (body constraint)[index.val] := by
  cases constraint with
  | require literal =>
      have hIndex : index.val = 0 := by
        have h := index.isLt
        change index.val < 1 at h
        omega
      simp only [atSource, Source.selectedLiteral, Source.kind, reduceCtorEq, ite_false,
        Source.originalLiteral, body, hIndex, List.getElem_cons_zero]
  | implication premises resultLiteral =>
      simp only [atSource]
      split
      · exact BuilderPayloadLiteralTokenSelector.premise_canonical_order premises resultLiteral _
      · have h : index.val < premises.length + 1 := by
          simpa only [body_implication_length] using index.isLt
        have hIndex : index.val = premises.length := by omega
        simpa only [hIndex, body] using BuilderPayloadLiteralTokenSelector.conclusion_canonical_order premises resultLiteral
  | exactlyOne variables =>
      simp only [atSource, Source.selectedLiteral, Source.kind, reduceCtorEq, ite_false,
        Source.originalLiteral, body, List.getElem_map]

theorem atSource_original_index {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).originalLiteral.index = (body constraint)[index.val].index := by
  rw [← BuilderPayloadLiteralTokenSelector.selected_index, atSource_selected]

theorem atSource_kind {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (count : Nat) (hBalance : index.val + count = (body constraint).length) :
    (atSource constraint index).kind = kindAt (family constraint) count := by
  cases constraint with
  | require literal =>
      simp only [atSource, Source.kind, family, kindAt, lastKind, bodyKind, ite_self]
  | implication premises resultLiteral =>
      have hBalance' : index.val + count = premises.length + 1 := by
        simpa only [body_implication_length] using hBalance
      have hIndex : index.val < premises.length + 1 := by
        simpa only [body_implication_length] using index.isLt
      simp only [atSource]
      split
      · have hOther : count ≠ 1 := by omega
        simp only [Source.kind, family, kindAt, if_neg hOther, bodyKind]
      · have hLast : count = 1 := by omega
        simp only [Source.kind, family, kindAt, if_pos hLast, lastKind]
  | exactlyOne variables =>
      simp only [atSource, Source.kind, family, kindAt, lastKind, bodyKind, ite_self]

/-- The fixed request header retained throughout the source-body loop. -/
structure Request where
  gap : List Nat
  gap_length : gap.length = 9
  clauseIndex : Nat
  originalPosition : Nat

def requestValues {width : Nat} (constraint : LocalConstraint width) (request : Request) (older : List Nat) : List Nat :=
  older ++ BuilderLocalConstraintPayload.values (some (some constraint)) ++ request.gap ++
    [request.clauseIndex, request.originalPosition]
def baseValues {width : Nat} (constraint : LocalConstraint width) (request : Request) (older prior : List Nat) : List Nat :=
  requestValues constraint request older ++ prior
def initialValues {width : Nat} (constraint : LocalConstraint width) (request : Request) (older prior : List Nat)
    (ordinal count position : Nat) : List Nat :=
  baseValues constraint request older prior ++ [ordinal,count,position]
def context {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * index.val) (count position : Nat) :
    Context (atSource constraint index).ordinal :=
  {gap := request.gap, gap_length := request.gap_length,
   clauseIndex := request.clauseIndex, originalPosition := request.originalPosition,
   prior := prior, prior_length := by rw [atSource_ordinal]; exact hPrior,
   remaining := count, position := position}

theorem context_initial_values {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * index.val)
    (count position : Nat) (older : List Nat) :
    BuilderPayloadLiteralTokenSelector.initialValues (atSource constraint index)
      (context constraint index request prior hPrior count position) older =
      initialValues constraint request older prior index.val count position := by
  rw [BuilderPayloadLiteralTokenSelector.initial_values_layout]
  simp only [context, atSource_slot, atSource_ordinal, initialValues, baseValues, requestValues, List.append_assoc]

theorem context_base_values {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * index.val)
    (count position : Nat) (older : List Nat) :
    BuilderPayloadSearchComparison.baseValues (atSource constraint index)
      (context constraint index request prior hPrior count position) older =
      baseValues constraint request older prior := by
  simp only [BuilderPayloadSearchComparison.baseValues, BuilderPayloadLiteralTokenSelector.reader,
    BuilderPayloadLiteralTokenSelector.readerPrefix, context, atSource_slot,
    baseValues, requestValues, BuilderLocalConstraintPayload.values, List.reverse_append,
    List.reverse_reverse, List.reverse_cons, List.reverse_nil, List.append_assoc, List.cons_append, List.nil_append]

end PNP.Concrete.CookLevin.BuilderPayloadSearchSource
