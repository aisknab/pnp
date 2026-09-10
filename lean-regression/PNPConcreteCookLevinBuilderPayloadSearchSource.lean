/-
Copyright (c) 2026 PNP Labs.

Canonical first-clause binding, actual payload and ordinal preservation, and
the physical last-count schema distinction for arbitrary local constraints.
-/
import PNP.Concrete.CookLevinBuilderPayloadSearchSource

namespace PNP.Concrete.CookLevin.BuilderPayloadSearchSourceRegression

open PipelineTape BuilderUnaryPolynomial
open BuilderPayloadLiteralTokenSelector (Kind Source Context)
open BuilderPayloadSearchSource

example {width : Nat} (constraint : LocalConstraint width) :
    constraint.emit[0]? = some (body constraint) :=
  BuilderPayloadSearchSource.body_first_clause constraint

example {width : Nat} (premises : List (BoundedLiteral width))
    (resultLiteral : BoundedLiteral width) :
    (body (.implication premises resultLiteral)).length = premises.length + 1 :=
  BuilderPayloadSearchSource.body_implication_length premises resultLiteral

example {width : Nat} (variables : List (Fin width)) :
    (body (.exactlyOne variables)).length = variables.length :=
  BuilderPayloadSearchSource.body_positive_length variables

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).ordinal = index.val :=
  BuilderPayloadSearchSource.atSource_ordinal constraint index

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).slot = some (some constraint) :=
  BuilderPayloadSearchSource.atSource_slot constraint index

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).selectedLiteral = (body constraint)[index.val] :=
  BuilderPayloadSearchSource.atSource_selected constraint index

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length) :
    (atSource constraint index).originalLiteral.index = (body constraint)[index.val].index :=
  BuilderPayloadSearchSource.atSource_original_index constraint index

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (count : Nat) (hBalance : index.val + count = (body constraint).length) :
    (atSource constraint index).kind = kindAt (family constraint) count :=
  BuilderPayloadSearchSource.atSource_kind constraint index count hBalance

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * index.val)
    (count position : Nat) (older : List Nat) :
    BuilderPayloadLiteralTokenSelector.initialValues (atSource constraint index)
      (context constraint index request prior hPrior count position) older =
      initialValues constraint request older prior index.val count position :=
  BuilderPayloadSearchSource.context_initial_values constraint index request prior hPrior count position older

example {width : Nat} (constraint : LocalConstraint width) (index : Fin (body constraint).length)
    (request : Request) (prior : List Nat) (hPrior : prior.length = 17 * index.val)
    (count position : Nat) (older : List Nat) :
    BuilderPayloadSearchComparison.baseValues (atSource constraint index)
      (context constraint index request prior hPrior count position) older =
      baseValues constraint request older prior :=
  BuilderPayloadSearchSource.context_base_values constraint index request prior hPrior count position older

example : kindAt .required 1 = .required := rfl
example : kindAt .implication 1 = .conclusion := rfl
example : kindAt .positive 1 = .positive := rfl
example (count : Nat) :
    kindAt .implication (count + 2) = .premise := by
  rw [kindAt, if_neg (by omega)]
  rfl
example (count : Nat) : kindAt .positive count = .positive := by
  unfold kindAt lastKind bodyKind
  split <;> rfl

-- Empty implication premises select the real conclusion, not a fabricated head.
example {width : Nat} (resultLiteral : BoundedLiteral width) :
    (atSource (.implication [] resultLiteral) ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩).kind = .conclusion := rfl
example {width : Nat} (resultLiteral : BoundedLiteral width) :
    (atSource (.implication [] resultLiteral) ⟨0, by change 0 < 1; exact Nat.zero_lt_succ 0⟩).selectedLiteral = resultLiteral := rfl

end PNP.Concrete.CookLevin.BuilderPayloadSearchSourceRegression
