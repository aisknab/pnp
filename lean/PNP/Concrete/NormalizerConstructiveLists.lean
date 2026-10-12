import Std

namespace PNP.Concrete.NormalizerBlocks.ConstructiveLists

/-- The existing finite equality computation has a constructive equality law. -/
theorem finiteLawful (n : Nat) : LawfulBEq (Fin n) where
  eq_of_beq {a b} h := by
    change decide (a = b) = true at h
    exact of_decide_eq_true h
  rfl {a} := by
    change decide (a = a) = true
    exact decide_eq_true rfl

/-- Lookup uses the supplied executable equality; no classical case split is needed. -/
theorem lookup {α : Type u} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (h : x ∈ xs) : xs[xs.idxOf x]? = some x := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    cases hb : (a == x) with
    | false =>
      have ne : x ≠ a := by
        intro eq
        subst a
        have self : (x == x) = true := (inferInstance : LawfulBEq α).rfl
        rw [self] at hb
        cases hb
      have ht : x ∈ xs := (List.mem_cons.mp h).resolve_left ne
      simpa only [List.idxOf_cons, hb, Bool.cond_false, List.getElem?_cons_succ]
        using ih ht
    | true =>
      have eq : a = x := eq_of_beq hb
      subst a
      simp only [List.idxOf_cons, hb, Bool.cond_true, List.getElem?_cons_zero]

/-- A finite list index is bounded by direct executable equality case analysis. -/
theorem indexBound {α : Type u} [BEq α] [LawfulBEq α]
    (xs : List α) (x : α) (h : x ∈ xs) : xs.idxOf x < xs.length := by
  induction xs with
  | nil => cases h
  | cons a xs ih =>
    cases hb : (a == x) with
    | false =>
      have ne : x ≠ a := by
        intro eq
        subst a
        have self : (x == x) = true := (inferInstance : LawfulBEq α).rfl
        rw [self] at hb
        cases hb
      have ht : x ∈ xs := (List.mem_cons.mp h).resolve_left ne
      simpa only [List.idxOf_cons, hb, Bool.cond_false, List.length_cons]
        using Nat.succ_lt_succ (ih ht)
    | true =>
      simp only [List.idxOf_cons, hb, Bool.cond_true, List.length_cons]
      exact Nat.zero_lt_succ xs.length

/-- Fix the equality-law proof explicitly instead of importing ordering-law authority. -/
theorem finiteIndexBound {n : Nat} (xs : List (Fin n)) (x : Fin n) (h : x ∈ xs) :
    xs.idxOf x < xs.length :=
  @indexBound (Fin n) inferInstance (finiteLawful n) xs x h

end PNP.Concrete.NormalizerBlocks.ConstructiveLists
