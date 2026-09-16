/-
Copyright (c) 2026 PNP Labs.

Recover the raw node at each physical position of the actual topological
compiler. Search the compiler's own position map, not an independently chosen
permutation or a numerical allocation by output size.

This is ordering provenance, not full history/ambient ownership, a successful
global strategy or polynomial execution.
-/

import PNP.NANDTopologicalCompiler

namespace PNP.DirectWire

private theorem allFin_length (width : Nat) : (allFin width).length = width := by
  induction width with
  | zero => rfl
  | succ width ih =>
      change (0 :: (allFin width).map Fin.succ).length = width + 1
      rw [List.length_cons, List.length_map, ih]

private theorem allFin_nodup (width : Nat) : (allFin width).Nodup := by
  induction width with
  | zero => exact List.nodup_nil
  | succ width ih =>
      change (0 :: (allFin width).map Fin.succ).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨index, _, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

private theorem nodup_length_le_subset {alpha : Type} [DecidableEq alpha]
    {left right : List alpha} (distinct : left.Nodup)
    (included : ∀ item, item ∈ left → item ∈ right) : left.length ≤ right.length := by
  induction right generalizing left with
  | nil =>
      cases left with
      | nil => exact Nat.le_refl 0
      | cons head tail =>
          have impossible := included head (List.Mem.head tail)
          cases impossible
  | cons head tail ih =>
      by_cases member : head ∈ left
      · obtain ⟨before, after, rfl⟩ := List.append_of_mem member
        have reordered : (before ++ head :: after).Perm (head :: (before ++ after)) :=
          List.perm_middle
        obtain ⟨absent, restDistinct⟩ := List.nodup_cons.mp (reordered.nodup distinct)
        have restIncluded : ∀ item, item ∈ before ++ after → item ∈ tail := by
          intro item present
          have belongs := included item (reordered.symm.subset (List.mem_cons_of_mem head present))
          rcases List.mem_cons.mp belongs with same | remaining
          · exact False.elim (absent (same ▸ present))
          · exact remaining
        have bound := ih restDistinct restIncluded
        have length := reordered.length_eq
        simp only [List.length_cons] at length
        change _ ≤ tail.length + 1
        omega
      · have restIncluded : ∀ item, item ∈ left → item ∈ tail := by
          intro item present
          rcases List.mem_cons.mp (included item present) with same | remaining
          · exact False.elim (member (same ▸ present))
          · exact remaining
        exact Nat.le_trans (ih distinct restIncluded) (Nat.le_succ tail.length)

private theorem perm_of_nodup_members {alpha : Type} {left right : List alpha}
    (leftDistinct : left.Nodup) (rightDistinct : right.Nodup)
    (sameMembers : ∀ item, item ∈ left ↔ item ∈ right) : left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact List.Perm.nil
      | cons head tail =>
          have impossible : head ∈ ([] : List alpha) :=
            (sameMembers head).mpr (List.Mem.head tail)
          cases impossible
  | cons head tail ih =>
      have present := (sameMembers head).mp (List.Mem.head tail)
      obtain ⟨before, after, rfl⟩ := List.append_of_mem present
      have middle : (before ++ head :: after).Perm (head :: (before ++ after)) :=
        List.perm_middle
      obtain ⟨headAbsent, restDistinct⟩ := List.nodup_cons.mp (middle.nodup rightDistinct)
      obtain ⟨tailAbsent, tailDistinct⟩ := List.nodup_cons.mp leftDistinct
      have remaining : ∀ item, item ∈ tail ↔ item ∈ before ++ after := by
        intro item
        constructor
        · intro member
          have inRight := middle.subset
            ((sameMembers item).mp (List.mem_cons_of_mem head member))
          rcases List.mem_cons.mp inRight with equal | member
          · exact False.elim (tailAbsent (equal ▸ member))
          · exact member
        · intro member
          have inLeft := (sameMembers item).mpr
            (middle.symm.subset (List.mem_cons_of_mem head member))
          rcases List.mem_cons.mp inLeft with equal | member
          · exact False.elim (headAbsent (equal ▸ member))
          · exact member
      exact ((ih tailDistinct restDistinct remaining).cons head).trans middle.symm

/-- Finite search returns the node at this exact computed position. -/
private def findPosition {nodes count : Nat} (position : Fin nodes → Fin count)
    (target : Fin count) : (remaining : List (Fin nodes)) →
      (∃ node, node ∈ remaining ∧ position node = target) →
        {node : Fin nodes // position node = target}
  | [], witness => False.elim (by obtain ⟨node, absent, _⟩ := witness; cases absent)
  | node :: remaining, witness =>
      if same : position node = target then ⟨node, same⟩
      else findPosition position target remaining (by
        obtain ⟨other, member, equal⟩ := witness
        rcases List.mem_cons.mp member with atHead | inTail
        · subst other
          exact False.elim (same equal)
        · exact ⟨other, inTail, equal⟩)

namespace CompiledRawNandGraph

variable {inputs nodes : Nat} {graph : RawNandGraph inputs nodes}

/-- Every actual compiled position has a source node; the finite search below
uses this only to rule out failure, not to choose an unrelated node. -/
theorem position_surjective (compiled : CompiledRawNandGraph graph) :
    Function.Surjective compiled.position := by
  intro target
  let image := (allFin nodes).map compiled.position
  have distinct : image.Nodup :=
    List.Pairwise.map compiled.position
      (fun left right different same => different (compiled.position_injective left right same))
      (allFin_nodup nodes)
  by_cases present : target ∈ image
  · obtain ⟨node, _, same⟩ := List.mem_map.mp present
    exact ⟨node, same⟩
  · have bound := nodup_length_le_subset
      (left := target :: image) (right := allFin compiled.count)
      (List.nodup_cons.mpr ⟨present, distinct⟩)
      (fun item _member => mem_allFin item)
    simp only [List.length_cons, image, List.length_map, allFin_length] at bound
    have count := compiled.count_eq
    omega

private def physicalPreimage (compiled : CompiledRawNandGraph graph) (target : Fin compiled.count) :
    {node : Fin nodes // compiled.position node = target} :=
  findPosition compiled.position target (allFin nodes) (by
    obtain ⟨node, same⟩ := compiled.position_surjective target
    exact ⟨node, mem_allFin node, same⟩)

/-- Computable inverse of this compiler's actual placement map. -/
def physicalOrigin (compiled : CompiledRawNandGraph graph) (position : Fin compiled.count) :
    Fin nodes := (compiled.physicalPreimage position).1

theorem position_physicalOrigin (compiled : CompiledRawNandGraph graph)
    (position : Fin compiled.count) :
    compiled.position (compiled.physicalOrigin position) = position :=
  (compiled.physicalPreimage position).2

theorem physicalOrigin_position (compiled : CompiledRawNandGraph graph) (node : Fin nodes) :
    compiled.physicalOrigin (compiled.position node) = node :=
  compiled.position_injective _ _ (compiled.position_physicalOrigin (compiled.position node))

theorem physicalOrigin_injective (compiled : CompiledRawNandGraph graph) :
    Function.Injective compiled.physicalOrigin := by
  intro left right same
  have positions := congrArg compiled.position same
  rw [compiled.position_physicalOrigin, compiled.position_physicalOrigin] at positions
  exact positions

theorem physicalOrigin_surjective (compiled : CompiledRawNandGraph graph) :
    Function.Surjective compiled.physicalOrigin :=
  fun node => ⟨compiled.position node, compiled.physicalOrigin_position node⟩

/-- Raw source nodes in actual compiled physical-position order. -/
def physicalOrigins (compiled : CompiledRawNandGraph graph) : List (Fin nodes) :=
  (allFin compiled.count).map compiled.physicalOrigin

theorem physicalOrigins_nodup (compiled : CompiledRawNandGraph graph) :
    compiled.physicalOrigins.Nodup :=
  List.Pairwise.map compiled.physicalOrigin
    (fun _ _ different same => different (compiled.physicalOrigin_injective same))
    (allFin_nodup compiled.count)

theorem physicalOrigins_perm (compiled : CompiledRawNandGraph graph) :
    compiled.physicalOrigins.Perm (allFin nodes) := by
  apply perm_of_nodup_members compiled.physicalOrigins_nodup (allFin_nodup nodes)
  intro node
  constructor
  · intro _member
    exact mem_allFin node
  · intro _member
    exact List.mem_map.mpr
      ⟨compiled.position node, mem_allFin _, compiled.physicalOrigin_position node⟩

end CompiledRawNandGraph

/-- Tie the recovered origin to the placement actually made by the compiler
state, rather than an independently supplied enumeration. -/
theorem RawNandCompilationState.finish_physicalOrigin {inputs nodes : Nat}
    {graph : RawNandGraph inputs nodes} (state : RawNandCompilationState graph)
    (complete : state.remaining = []) (node : Fin nodes) (position : Fin state.count)
    (placed : state.position node = some position) :
    (state.finish complete).physicalOrigin position = node := by
  have same := Option.some.inj ((state.finish_position complete node).symm.trans placed)
  rw [← same]
  exact (state.finish complete).physicalOrigin_position node

end PNP.DirectWire
