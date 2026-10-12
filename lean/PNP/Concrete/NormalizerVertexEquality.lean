/-
Copyright (c) 2026 PNP Labs.

Constructive lawfulness of tagged finite-index boolean equality.
The equality computation is unchanged; the proof avoids generic ordering
simplification and uses the finite decidable equality directly.
-/
import Std

namespace PNP.Concrete.NormalizerBlocks.ConstructiveVertexEquality

theorem lawful (c n : Nat) : LawfulBEq (Sum (Fin c) (Fin n)) where
  eq_of_beq := by
    intro a b h
    cases a with
    | inl i =>
        cases b with
        | inl j =>
            change decide (i = j) = true at h
            exact congrArg Sum.inl (of_decide_eq_true h)
        | inr v =>
            change false = true at h
            cases h
    | inr v =>
        cases b with
        | inl i =>
            change false = true at h
            cases h
        | inr w =>
            change decide (v = w) = true at h
            exact congrArg Sum.inr (of_decide_eq_true h)
  rfl := by
    intro a
    cases a with
    | inl i =>
        change decide (i = i) = true
        exact decide_eq_true rfl
    | inr v =>
        change decide (v = v) = true
        exact decide_eq_true rfl

theorem equal (a b : Sum (Fin c) (Fin n)) (same : (a == b) = true) : a = b :=
  @LawfulBEq.eq_of_beq _ _ (lawful c n) a b same

theorem reflexive (a : Sum (Fin c) (Fin n)) : (a == a) = true :=
  (lawful c n).rfl

end PNP.Concrete.NormalizerBlocks.ConstructiveVertexEquality
