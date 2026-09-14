/-
Copyright (c) 2026 PNP Labs.

Canonical, duplicate-free source lists without enumeration of an ambient type.
This helper orders only the coordinates that an actual construction supplies.
-/

import PNP.NANDEnumerator
import Init.Data.List.Sort.Lemmas

namespace PNP.DirectWire.SourceListOrder

variable {alpha : Type} [DecidableEq alpha]

/-- Remove repetitions by traversing the supplied list only. -/
def unique : List alpha → List alpha
  | [] => []
  | head :: tail =>
      let rest := unique tail
      if head ∈ rest then rest else head :: rest

theorem mem_unique (item : alpha) (items : List alpha) :
    item ∈ unique items ↔ item ∈ items := by
  induction items generalizing item with
  | nil => rfl
  | cons head tail ih =>
      simp only [unique]
      split
      · rename_i present
        rw [ih item, List.mem_cons]
        constructor
        · exact Or.inr
        · intro member
          rcases member with equal | member
          · subst item
            exact (ih head).mp present
          · exact member
      · rw [List.mem_cons, ih item, List.mem_cons]

theorem unique_nodup (items : List alpha) : (unique items).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      simp only [unique]
      split
      · exact ih
      · rename_i absent
        exact List.nodup_cons.mpr ⟨absent, ih⟩

theorem unique_length_le (items : List alpha) :
    (unique items).length ≤ items.length := by
  induction items with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
      simp only [unique]
      split
      · exact Nat.le_trans ih (Nat.le_succ _)
      · exact Nat.succ_le_succ ih

omit [DecidableEq alpha] in
/-- Insert one actual source into an already ordered finite source list. -/
private def insertOrdered (key : alpha → Nat) (item : alpha) : List alpha → List alpha
  | [] => [item]
  | head :: tail =>
      if key item ≤ key head then item :: head :: tail
      else head :: insertOrdered key item tail

omit [DecidableEq alpha] in
private theorem insertOrdered_perm (key : alpha → Nat) (item : alpha)
    (items : List alpha) :
    (insertOrdered key item items).Perm (item :: items) := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
      simp only [insertOrdered]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons head ih).trans (List.Perm.swap item head tail)

omit [DecidableEq alpha] in
private theorem insertOrdered_ordered (key : alpha → Nat) (item : alpha)
    (items : List alpha)
    (ordered : items.Pairwise (fun left right => key left ≤ key right)) :
    (insertOrdered key item items).Pairwise (fun left right => key left ≤ key right) := by
  induction items with
  | nil => exact List.pairwise_singleton _ _
  | cons head tail ih =>
      have head_le := (List.pairwise_cons.mp ordered).1
      have tail_ordered := (List.pairwise_cons.mp ordered).2
      simp only [insertOrdered]
      split
      · rename_i before
        apply List.pairwise_cons.mpr
        refine ⟨?_, ordered⟩
        intro other member
        rcases List.mem_cons.mp member with same | member
        · subst other
          exact before
        · exact Nat.le_trans before (head_le other member)
      · rename_i after
        apply List.pairwise_cons.mpr
        refine ⟨?_, ih tail_ordered⟩
        intro other member
        have found := (insertOrdered_perm key item tail).mem_iff.mp member
        rcases List.mem_cons.mp found with same | member
        · subst other
          exact Nat.le_of_lt (Nat.lt_of_not_ge after)
        · exact head_le other member

omit [DecidableEq alpha] in
/-- Structural recursion keeps the actual source sort kernel-reducible. -/
private def sort (key : alpha → Nat) : List alpha → List alpha
  | [] => []
  | head :: tail => insertOrdered key head (sort key tail)

omit [DecidableEq alpha] in
private theorem sort_perm (key : alpha → Nat) (items : List alpha) :
    (sort key items).Perm items := by
  induction items with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
      exact (insertOrdered_perm key head (sort key tail)).trans (List.Perm.cons head ih)

omit [DecidableEq alpha] in
private theorem sort_ordered (key : alpha → Nat) (items : List alpha) :
    (sort key items).Pairwise (fun left right => key left ≤ key right) := by
  induction items with
  | nil => exact List.Pairwise.nil
  | cons head tail ih => exact insertOrdered_ordered key head (sort key tail) ih

/-- Sort actual source coordinates; no ambient-width enumeration occurs. -/
def canonical (key : alpha → Nat) (items : List alpha) : List alpha :=
  sort key (unique items)

theorem mem_canonical (key : alpha → Nat) (item : alpha) (items : List alpha) :
    item ∈ canonical key items ↔ item ∈ items := by
  exact (sort_perm key (unique items)).mem_iff.trans (mem_unique item items)

theorem canonical_nodup (key : alpha → Nat) (items : List alpha) :
    (canonical key items).Nodup :=
  (sort_perm key (unique items)).symm.nodup (unique_nodup items)

theorem canonical_length_le (key : alpha → Nat) (items : List alpha) :
    (canonical key items).length ≤ items.length := by
  unfold canonical
  rw [(sort_perm key (unique items)).length_eq]
  exact unique_length_le items

theorem canonical_ordered (key : alpha → Nat) (items : List alpha) :
    (canonical key items).Pairwise (fun left right => key left ≤ key right) :=
  sort_ordered key (unique items)

omit [DecidableEq alpha] in
/-- Injective keys, order, distinctness and membership determine the exact list. -/
theorem ordered_eq_of_mem (key : alpha → Nat) (injective : Function.Injective key)
    (left right : List alpha) (leftDistinct : left.Nodup) (rightDistinct : right.Nodup)
    (leftOrdered : left.Pairwise (fun a b => key a ≤ key b))
    (rightOrdered : right.Pairwise (fun a b => key a ≤ key b))
    (members : ∀ item, item ∈ left ↔ item ∈ right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have impossible := (members head).mpr (List.mem_cons_self ..)
          cases impossible
  | cons head tail ih =>
      cases right with
      | nil =>
          have impossible := (members head).mp (List.mem_cons_self ..)
          cases impossible
      | cons other rest =>
          have firstMember := (members head).mp (List.mem_cons_self ..)
          have secondMember := (members other).mpr (List.mem_cons_self ..)
          have equal : head = other := by
            rcases List.mem_cons.mp firstMember with same | firstTail
            · exact same
            · rcases List.mem_cons.mp secondMember with same | secondTail
              · exact same.symm
              · exact injective (Nat.le_antisymm
                  ((List.pairwise_cons.mp leftOrdered).1 other secondTail)
                  ((List.pairwise_cons.mp rightOrdered).1 head firstTail))
          subst other
          apply congrArg (List.cons head)
          apply ih rest (List.nodup_cons.mp leftDistinct).2
            (List.nodup_cons.mp rightDistinct).2
            (List.pairwise_cons.mp leftOrdered).2
            (List.pairwise_cons.mp rightOrdered).2
          intro item
          constructor
          · intro member
            have found := (members item).mp (List.mem_cons_of_mem head member)
            rcases List.mem_cons.mp found with same | found
            · subst item
              exact False.elim ((List.nodup_cons.mp leftDistinct).1 member)
            · exact found
          · intro member
            have found := (members item).mpr (List.mem_cons_of_mem head member)
            rcases List.mem_cons.mp found with same | found
            · subst item
              exact False.elim ((List.nodup_cons.mp rightDistinct).1 member)
            · exact found

/-- A supplied source list recovers an independent canonical reference exactly. -/
theorem canonical_eq_reference (key : alpha → Nat) (injective : Function.Injective key)
    (items reference : List alpha) (distinct : reference.Nodup)
    (ordered : reference.Pairwise (fun a b => key a ≤ key b))
    (members : ∀ item, item ∈ items ↔ item ∈ reference) :
    canonical key items = reference :=
  ordered_eq_of_mem key injective _ reference (canonical_nodup key items)
    distinct (canonical_ordered key items) ordered
    (fun item => (mem_canonical key item items).trans (members item))

end PNP.DirectWire.SourceListOrder
