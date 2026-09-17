/-
Copyright (c) 2026 PNP Labs.

Exact local physical ownership for the computed structural reindexer. Every
new physical position carries the old gate selected by the actual backward
bijection. Reordering allocates and removes nothing.

Here "original" means present immediately before this operation. The complete
program ledger must lift it through its previous ownership map, including any
earlier allocations; this local ledger does not reset global history.

This is a local conservation result, not complete mixed-program integration,
full manuscript profiles, global ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireStructuralState
import PNP.NANDWireDescendantLedger

namespace PNP.DirectWire.WireStructuralState

open WireObligationHistory (State)
open WireDescendantHistory (DescendantOrigin PersistentOwnership originalOrigins)

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
variable {before : State source} {code : List (Nat × Nat)}

private theorem ofFn_nodup {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  apply List.pairwise_iff_getElem.mpr
  intro left right leftBound rightBound before same
  have leftValid : left < width := by simpa only [List.length_ofFn] using leftBound
  have rightValid : right < width := by simpa only [List.length_ofFn] using rightBound
  have sameValue : value ⟨left, leftValid⟩ = value ⟨right, rightValid⟩ := by
    simpa only [List.getElem_ofFn] using same
  have sameIndex : left = right := congrArg Fin.val (injective sameValue)
  omega

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

/-- Computed from the actual physical reindexing, with no supplied owner map. -/
def Receipt.ownership (receipt : Receipt before code) :
    PersistentOwnership before.current.implementation.gateCount
      receipt.next.current.implementation.gateCount where
  origin := fun gate =>
    .original (before.current.reindexBackwardGate receipt.relabeling gate)
  charged := []
  removed := []

namespace Receipt

variable (receipt : Receipt before code)

theorem ownership_origin
    (gate : Fin receipt.next.current.implementation.gateCount) :
    receipt.ownership.origin gate =
      .original (before.current.reindexBackwardGate receipt.relabeling gate) := rfl

theorem ownership_origin_forward (gate : Fin before.current.implementation.gateCount) :
    receipt.ownership.origin (before.current.reindexForwardGate receipt.relabeling gate) =
      .original gate := by
  rw [ownership_origin, WireCarrier.reindex_backward_forward]

theorem ownership_origin_injective : Function.Injective receipt.ownership.origin := by
  intro left right same
  have oldSame :
      before.current.reindexBackwardGate receipt.relabeling left =
        before.current.reindexBackwardGate receipt.relabeling right :=
    DescendantOrigin.original.inj same
  have transported := congrArg (before.current.reindexForwardGate receipt.relabeling) oldSame
  exact (before.current.reindex_forward_backward receipt.relabeling left).symm.trans
    (transported.trans (before.current.reindex_forward_backward receipt.relabeling right))

theorem ownership_live_members
    (origin : DescendantOrigin before.current.implementation.gateCount) :
    origin ∈ receipt.ownership.live ↔
      origin ∈ originalOrigins before.current.implementation.gateCount := by
  constructor
  · intro member
    obtain ⟨gate, originAt⟩ := List.mem_ofFn.mp member
    exact List.mem_ofFn.mpr
      ⟨before.current.reindexBackwardGate receipt.relabeling gate, originAt⟩
  · intro member
    obtain ⟨gate, originAt⟩ := List.mem_ofFn.mp member
    exact List.mem_ofFn.mpr
      ⟨before.current.reindexForwardGate receipt.relabeling gate,
        (receipt.ownership_origin_forward gate).trans originAt⟩

theorem ownership_not_allocated
    (gate : Fin receipt.next.current.implementation.gateCount)
    (stage event localGate : Nat) :
    receipt.ownership.origin gate ≠ .allocated stage event localGate := by
  rw [ownership_origin]
  intro impossible
  cases impossible

theorem ownership_charged : receipt.ownership.charged = [] := rfl

theorem ownership_removed : receipt.ownership.removed = [] := rfl

theorem ownership_wellFormed : receipt.ownership.WellFormed 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change (List.ofFn receipt.ownership.origin ++ []).Nodup
    rw [List.append_nil]
    exact ofFn_nodup receipt.ownership.origin receipt.ownership_origin_injective
  · change (receipt.ownership.live ++ []).Perm
      (originalOrigins before.current.implementation.gateCount ++ [])
    simp only [List.append_nil]
    exact perm_of_nodup_members
      (ofFn_nodup receipt.ownership.origin receipt.ownership_origin_injective)
      (ofFn_nodup DescendantOrigin.original
        (fun _ _ same => DescendantOrigin.original.inj same))
      receipt.ownership_live_members
  · intro origin member
    cases member

/-- The exact local interface consumed by complete-program physical ownership. -/
theorem physical_ownership :
    receipt.ownership.live.length = receipt.next.current.implementation.gateCount ∧
      receipt.ownership.charged.length = 0 ∧
      receipt.ownership.removed.length = 0 ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Nodup ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ receipt.ownership.charged) := by
  refine ⟨?_, rfl, rfl, receipt.ownership_wellFormed.distinct,
    receipt.ownership_wellFormed.conserved⟩
  exact List.length_ofFn

end Receipt
end PNP.DirectWire.WireStructuralState
