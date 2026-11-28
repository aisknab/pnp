import PNP.ThreeUse.RowShape

/-!
# Finite witnesses for group-word systems

Only labels occurring in the finite row list affect feasibility. A solution can therefore be represented by a list with exactly those labels, in the computed order.
-/

set_option autoImplicit false

namespace PNP.ThreeUse
open PNP.Concrete

def reader {α : Type} [DecidableEq α] (p : α) : List (α × G) → G
  | [] => one
  | (a, g) :: ts => if a = p then g else reader p ts

def table {α : Type} [DecidableEq α] (rs : List (Row α)) (v : α → G) : List (α × G) :=
  (unique (labels rs)).map (fun p => (p, v p))

theorem reader_on {α : Type} [DecidableEq α] (p : α) (ps : List α) (v : α → G) (hp : p ∈ ps) :
    reader p (ps.map (fun a => (a, v a))) = v p := by
  induction ps with
  | nil => cases hp
  | cons a ps ih =>
    rw [List.map_cons, reader]
    by_cases e : a = p
    · rw [e, if_pos rfl]
    · rw [if_neg e]; apply ih
      rcases List.mem_cons.mp hp with g|g
      · exact False.elim (e g.symm)
      · exact g

theorem eval_agree {α : Type} (v u : α → G) (w : Word α)
    (h : ∀ a, a ∈ w.map Prod.fst → v a = u a) : eval v w = eval u w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    have hh := h t.1 List.mem_cons_self
    have gt := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    rw [eval, eval, gt]; simp only [wt, hh]

theorem table_ok {α : Type} [DecidableEq α] (rs : List (Row α)) (v : α → G) (ok : holds v rs) :
    holds (fun p => reader p (table rs v)) rs := by
  intro e he
  calc
    _ = eval v e.w := by
      apply eval_agree; intro p hp; apply reader_on
      apply (unique_mem _ _).mpr
      have all (rs' : List (Row α)) (he : e ∈ rs') : p ∈ labels rs' := by
        induction rs' with
        | nil => cases he
        | cons h ts ih =>
          rcases List.mem_cons.mp he with eq|inside
          · subst h; exact List.mem_append_left _ hp
          · exact List.mem_append_right _ (ih inside)
      exact all rs he
    _ = e.out := ok _ he

def finiteFeasible {α : Type} [DecidableEq α] (rs : List (Row α)) : Prop :=
  ∃ w : List (α × G), w.map Prod.fst = unique (labels rs) ∧ holds (fun p => reader p w) rs

theorem finite_iff {α : Type} [DecidableEq α] (rs : List (Row α)) : feasible rs ↔ finiteFeasible rs := by
  constructor
  · rintro ⟨v, h⟩; refine ⟨table rs v, ?_, table_ok rs v h⟩
    unfold table
    induction unique (labels rs) with
    | nil => rfl
    | cons a as_ ih => rw [List.map_cons, List.map_cons, ih]
  · rintro ⟨t, _, ok⟩; exact ⟨_, ok⟩

theorem strict_finite (bits : BitString) : CNFSAT bits ↔ finiteFeasible (targetRows bits) :=
  (raw_iff _).trans (finite_iff _)

end PNP.ThreeUse
