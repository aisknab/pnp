/-
Copyright (c) 2026 PNP Labs.

Derive a local physical ownership delta for each actual primitive transition,
even when its current carrier has a different gate count from the initial
semantic source. This is an internal ingredient of the complete mixed-program
fold, not a supplied owner map or a global successful strategy.
-/

import PNP.NANDWireOpenProgram
import PNP.NANDWireOpenSupportOwnership

namespace PNP.DirectWire.WireOpenProgram.PrimitiveOwnership

open WireObligationHistory (State PhysicalOrigin PhysicalOwnership keepExcept)
open WireObligationRestoration (materializer)
open WireDescendantHistory (DescendantOrigin PersistentOwnership originalOrigins)
open WireHistoryAmbientOwnership (ambientOriginals)

variable {inputs outputs fields initialGates : Nat}
variable {source : WireCarrier inputs outputs fields}
variable {before after : State source} {event : WireObligationHistory.RawEvent fields}

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

private theorem swap_suffixes {alpha : Type} (first middle last : List alpha) :
    ((first ++ middle) ++ last).Perm ((first ++ last) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := last)).append_left first

/-- Follow the actual unchanged, appended or normalized physical positions.
The original-coordinate dimension is independent of the semantic source. -/
def advance (step : WireObligationHistory.Transition source before event after)
    (ledger : PhysicalOwnership initialGates before.current.implementation.gateCount) :
    PhysicalOwnership initialGates after.current.implementation.gateCount :=
  match step with
  | .create _ _ _ _ _ => ledger
  | .restore _ _ _ _ entry =>
      ledger.append event.identity
        (materializer entry.snapshot.carrier (keepExcept entry.field)).implementation.gateCount
  | .realize _ _ _ _ _ entry realization _ =>
      ledger.append event.identity
        (materializer realization.carrier (keepExcept entry.field)).implementation.gateCount
  | .cancel _ _ _ _ _ _ _ => ledger
  | .normalize _ _ _ => PhysicalOwnership.normalize before.current.exposed ledger
  | .read _ _ _ _ _ => ledger

def allocations (step : WireObligationHistory.Transition source before event after) :
    List (PhysicalOrigin initialGates) :=
  List.ofFn (fun gate : Fin step.charged => .allocated event.identity gate.val)

theorem allocations_nodup (step : WireObligationHistory.Transition source before event after) :
    (allocations (initialGates := initialGates) step).Nodup := by
  apply ofFn_nodup
  intro left right same
  exact Fin.ext (PhysicalOrigin.allocated.inj same).2

theorem advance_charged (step : WireObligationHistory.Transition source before event after)
    (ledger : PhysicalOwnership initialGates before.current.implementation.gateCount) :
    (advance step ledger).charged = ledger.charged ++ allocations step := by
  cases step with
  | restore identity kind entry => rfl
  | realize identity raw kind entry realization computed => rfl
  | _ =>
      change ledger.charged = ledger.charged ++ []
      exact (List.append_nil ledger.charged).symm

theorem advance_removed_length (step : WireObligationHistory.Transition source before event after)
    (ledger : PhysicalOwnership initialGates before.current.implementation.gateCount) :
    (advance step ledger).removed.length = ledger.removed.length + step.removed := by
  cases step with
  | normalize kind =>
      exact PhysicalOwnership.normalize_removed_length before.current.exposed ledger
  | _ => rfl

theorem advance_conservation (step : WireObligationHistory.Transition source before event after)
    (ledger : PhysicalOwnership initialGates before.current.implementation.gateCount) :
    ((advance step ledger).live ++ (advance step ledger).removed).Perm
      ((ledger.live ++ ledger.removed) ++ allocations step) := by
  cases step with
  | restore identity kind entry =>
      change ((ledger.append event.identity _).live ++ ledger.removed).Perm _
      rw [PhysicalOwnership.append_live]
      exact swap_suffixes _ _ _
  | realize identity raw kind entry realization computed =>
      change ((ledger.append event.identity _).live ++ ledger.removed).Perm _
      rw [PhysicalOwnership.append_live]
      exact swap_suffixes _ _ _
  | normalize kind =>
      change ((PhysicalOwnership.normalize before.current.exposed ledger).live ++
        (PhysicalOwnership.normalize before.current.exposed ledger).removed).Perm
          ((ledger.live ++ ledger.removed) ++ [])
      rw [List.append_nil]
      exact PhysicalOwnership.normalize_partition before.current.exposed ledger
  | _ =>
      change (ledger.live ++ ledger.removed).Perm ((ledger.live ++ ledger.removed) ++ [])
      rw [List.append_nil]

/-- Source-derived local delta: every original is an actual pre-operation position. -/
def ledger (step : WireObligationHistory.Transition source before event after) :
    PhysicalOwnership before.current.implementation.gateCount after.current.implementation.gateCount :=
  advance step (PhysicalOwnership.initial before.current.implementation.gateCount)

theorem ledger_charged (step : WireObligationHistory.Transition source before event after) :
    (ledger step).charged = allocations step :=
  advance_charged step (PhysicalOwnership.initial before.current.implementation.gateCount)

theorem ledger_removed_length (step : WireObligationHistory.Transition source before event after) :
    (ledger step).removed.length = step.removed := by
  have count := advance_removed_length step
    (PhysicalOwnership.initial before.current.implementation.gateCount)
  change (ledger step).removed.length = 0 + step.removed at count
  exact count.trans (Nat.zero_add _)

theorem ledger_partition (step : WireObligationHistory.Transition source before event after) :
    ((ledger step).live ++ (ledger step).removed).Perm
      (ambientOriginals before.current.implementation.gateCount ++ (ledger step).charged) := by
  rw [ledger_charged]
  have conserved := advance_conservation step
    (PhysicalOwnership.initial before.current.implementation.gateCount)
  change ((ledger step).live ++ (ledger step).removed).Perm
    ((ambientOriginals before.current.implementation.gateCount ++ []) ++ allocations step) at conserved
  rw [List.append_nil] at conserved
  exact conserved

theorem physical_ownership (step : WireObligationHistory.Transition source before event after) :
    (ledger step).live.length = after.current.implementation.gateCount ∧
      (ledger step).charged.length = step.charged ∧
      (ledger step).removed.length = step.removed ∧
      ((ledger step).live ++ (ledger step).removed).Nodup ∧
      ((ledger step).live ++ (ledger step).removed).Perm
        (ambientOriginals before.current.implementation.gateCount ++ (ledger step).charged) := by
  have totalDistinct :
      (ambientOriginals before.current.implementation.gateCount ++ (ledger step).charged).Nodup := by
    rw [ledger_charged]
    apply List.nodup_append.mpr
    refine ⟨ofFn_nodup PhysicalOrigin.original
      (fun _ _ same => PhysicalOrigin.original.inj same), allocations_nodup step, ?_⟩
    intro old oldMember fresh freshMember same
    obtain ⟨gate, original⟩ := List.mem_ofFn.mp oldMember
    obtain ⟨allocatedGate, allocated⟩ := List.mem_ofFn.mp freshMember
    have impossible := original.trans (same.trans allocated.symm)
    cases impossible
  refine ⟨List.length_ofFn, ?_, ledger_removed_length step,
    (ledger_partition step).symm.nodup totalDistinct, ledger_partition step⟩
  rw [ledger_charged]
  exact List.length_ofFn

/-- Primitive allocations use an inner position of zero. The enclosing mixed
program position will distinguish them from all other primitive/nested actions. -/
def lift : PhysicalOrigin initialGates → DescendantOrigin initialGates
  | .original gate => .original gate
  | .allocated identity localGate => .allocated 0 identity localGate

theorem lift_injective : Function.Injective (lift (initialGates := initialGates)) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right => exact congrArg PhysicalOrigin.original (DescendantOrigin.original.inj same)
      | allocated identity localGate => cases same
  | allocated identity localGate =>
      cases right with
      | original right => cases same
      | allocated otherIdentity otherGate =>
          obtain ⟨_, sameIdentity, sameGate⟩ := DescendantOrigin.allocated.inj same
          cases sameIdentity
          cases sameGate
          rfl

def labelled (step : WireObligationHistory.Transition source before event after) :
    PersistentOwnership before.current.implementation.gateCount after.current.implementation.gateCount :=
  ⟨fun position => lift ((ledger step).origin position),
    (ledger step).charged.map lift, (ledger step).removed.map lift⟩

theorem labelled_live (step : WireObligationHistory.Transition source before event after) :
    (labelled step).live = (ledger step).live.map lift := by
  rw [PhysicalOwnership.live, List.map_ofFn]
  rfl

theorem labelled_physical_ownership (step : WireObligationHistory.Transition source before event after) :
    (labelled step).live.length = after.current.implementation.gateCount ∧
      (labelled step).charged.length = step.charged ∧
      (labelled step).removed.length = step.removed ∧
      ((labelled step).live ++ (labelled step).removed).Nodup ∧
      ((labelled step).live ++ (labelled step).removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ (labelled step).charged) := by
  have checked := physical_ownership step
  have distinct : (((ledger step).live ++ (ledger step).removed).map lift).Nodup :=
    List.Pairwise.map lift
      (fun _ _ different same => different (lift_injective same)) checked.2.2.2.1
  have partition := checked.2.2.2.2.map lift
  simp only [List.map_append] at distinct partition
  have originals :
      (ambientOriginals before.current.implementation.gateCount).map lift =
        originalOrigins before.current.implementation.gateCount := by
    rw [ambientOriginals, List.map_ofFn]
    rfl
  rw [originals] at partition
  refine ⟨List.length_ofFn, ?_, ?_, ?_, ?_⟩
  · change ((ledger step).charged.map lift).length = _
    rw [List.length_map]
    exact checked.2.1
  · change ((ledger step).removed.map lift).length = _
    rw [List.length_map]
    exact checked.2.2.1
  · rw [labelled_live]
    exact distinct
  · rw [labelled_live]
    exact partition

theorem labelled_charged_origin (step : WireObligationHistory.Transition source before event after)
    (origin : DescendantOrigin before.current.implementation.gateCount)
    (member : origin ∈ (labelled step).charged) :
    ∃ localGate, origin = .allocated 0 event.identity localGate := by
  obtain ⟨inner, present, equation⟩ := List.mem_map.mp member
  rw [ledger_charged] at present
  obtain ⟨gate, innerAt⟩ := List.mem_ofFn.mp present
  refine ⟨gate.val, ?_⟩
  rw [← equation, ← innerAt]
  rfl

end PNP.DirectWire.WireOpenProgram.PrimitiveOwnership
