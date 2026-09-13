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

/-- Sort actual source coordinates; no ambient-width enumeration occurs. -/
def canonical (key : alpha → Nat) (items : List alpha) : List alpha :=
  (unique items).mergeSort (fun left right => decide (key left ≤ key right))

theorem mem_canonical (key : alpha → Nat) (item : alpha) (items : List alpha) :
    item ∈ canonical key items ↔ item ∈ items := by
  exact List.mem_mergeSort.trans (mem_unique item items)

theorem canonical_nodup (key : alpha → Nat) (items : List alpha) :
    (canonical key items).Nodup :=
  (List.mergeSort_perm (unique items) _).symm.nodup (unique_nodup items)

theorem canonical_length_le (key : alpha → Nat) (items : List alpha) :
    (canonical key items).length ≤ items.length := by
  unfold canonical
  rw [List.length_mergeSort]
  exact unique_length_le items

theorem canonical_ordered (key : alpha → Nat) (items : List alpha) :
    (canonical key items).Pairwise (fun left right => key left ≤ key right) := by
  have ordered := List.pairwise_mergeSort
    (le := fun left right : alpha => decide (key left ≤ key right))
    (fun left middle right first second =>
      decide_eq_true (Nat.le_trans (of_decide_eq_true first) (of_decide_eq_true second)))
    (fun left right => by
      rcases Nat.le_total (key left) (key right) with forward | backward
      · rw [decide_eq_true forward]
        rfl
      · rw [decide_eq_true backward]
        cases decide (key left ≤ key right) <;> rfl)
    (unique items)
  exact ordered.imp (fun checked => of_decide_eq_true checked)

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
