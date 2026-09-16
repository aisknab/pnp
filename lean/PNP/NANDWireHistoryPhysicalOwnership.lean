/-
Copyright (c) 2026 PNP Labs.

Physical allocation identities follow the actual computational wire history.
An original gate retains its source coordinate. Each appended materializer gate
belongs to its executing event and local physical position, not its snapshot ID.
Normalization preserves surviving identities and records removed identities.

This is physical accounting for the existing history language, not a successful
global strategy, full manuscript routing, ZeroSlack or polynomial execution.
-/

import PNP.NANDWireObligationHistoryExecution
import PNP.NANDPhysicalGateProvenance

namespace PNP.DirectWire.WireObligationHistory

open WireObligationRestoration PhysicalGateProvenance

/-- Creation identities describe snapshots; allocation identities describe the
event which physically appends this particular gate. -/
inductive PhysicalOrigin (sourceGates : Nat) where
  | original (gate : Fin sourceGates)
  | allocated (event : Nat) (localGate : Nat)
  deriving DecidableEq, Repr

/-- The live map is indexed by actual physical positions. Charges are historical:
a later removal never removes an entry from the charged list. -/
structure PhysicalOwnership (sourceGates physicalGates : Nat) where
  origin : Fin physicalGates → PhysicalOrigin sourceGates
  charged : List (PhysicalOrigin sourceGates)
  removed : List (PhysicalOrigin sourceGates)

private theorem ofFn_eq_map_allFin {alpha : Type} {width : Nat}
    (value : Fin width → alpha) :
    List.ofFn value = (allFin width).map value := by
  induction width with
  | zero => rfl
  | succ width ih =>
      rw [List.ofFn_succ]
      change _ = value 0 :: ((allFin width).map Fin.succ).map value
      rw [List.map_map]
      exact congrArg (List.cons (value 0)) (ih _)

private theorem ofFn_splitFin {alpha : Type} {left right : Nat}
    (first : Fin left → alpha) (second : Fin right → alpha) :
    List.ofFn (splitFin first second) = List.ofFn first ++ List.ofFn second := by
  rw [List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext index
    exact splitFin_left first second index
  · apply congrArg List.ofFn
    funext index
    exact splitFin_right first second index

private theorem listNoDuplicates_nodup {alpha : Type} {items : List alpha}
    (distinct : ListNoDuplicates items) : items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons absent _ ih => exact List.nodup_cons.mpr ⟨absent, ih⟩

private theorem allFin_nodup (width : Nat) : (allFin width).Nodup :=
  listNoDuplicates_nodup (allFin_noDuplicates width)

private theorem ofFn_nodup_of_injective {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (injective : Function.Injective value) :
    (List.ofFn value).Nodup := by
  rw [ofFn_eq_map_allFin]
  exact List.Pairwise.map value
    (fun _ _ different same => different (injective same)) (allFin_nodup width)

private theorem swap_suffixes {alpha : Type} (first middle last : List alpha) :
    ((first ++ middle) ++ last).Perm ((first ++ last) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := last)).append_left first

namespace PhysicalOwnership

variable {sourceGates physicalGates : Nat}

def live (ledger : PhysicalOwnership sourceGates physicalGates) :
    List (PhysicalOrigin sourceGates) := List.ofFn ledger.origin

def initial (sourceGates : Nat) : PhysicalOwnership sourceGates sourceGates :=
  ⟨PhysicalOrigin.original, [], []⟩

def append (ledger : PhysicalOwnership sourceGates physicalGates) (event added : Nat) :
    PhysicalOwnership sourceGates (physicalGates + added) :=
  ⟨splitFin ledger.origin (fun gate => .allocated event gate.val),
    ledger.charged ++ List.ofFn (fun gate : Fin added => .allocated event gate.val),
    ledger.removed⟩

theorem append_origin_left (ledger : PhysicalOwnership sourceGates physicalGates)
    (event added : Nat) (gate : Fin physicalGates) :
    (ledger.append event added).origin (Fin.castAdd added gate) = ledger.origin gate :=
  splitFin_left ledger.origin (fun gate : Fin added => .allocated event gate.val) gate

theorem append_origin_right (ledger : PhysicalOwnership sourceGates physicalGates)
    (event added : Nat) (gate : Fin added) :
    (ledger.append event added).origin (Fin.natAdd physicalGates gate) =
      .allocated event gate.val :=
  splitFin_right ledger.origin (fun gate : Fin added => .allocated event gate.val) gate

theorem append_live (ledger : PhysicalOwnership sourceGates physicalGates) (event added : Nat) :
    (ledger.append event added).live =
      ledger.live ++ List.ofFn (fun gate : Fin added => .allocated event gate.val) :=
  ofFn_splitFin ledger.origin (fun gate : Fin added => .allocated event gate.val)

def normalize {inputs outputs : Nat} (current : Implementation inputs outputs)
    (ledger : PhysicalOwnership sourceGates current.gateCount) :
    PhysicalOwnership sourceGates (runPhysicalNormalization current).result.gateCount :=
  ⟨fun gate => ledger.origin (normalizedOrigin current gate), ledger.charged,
    ledger.removed ++ (normalizedRemoved current).map ledger.origin⟩

theorem normalize_partition {inputs outputs : Nat} (current : Implementation inputs outputs)
    (ledger : PhysicalOwnership sourceGates current.gateCount) :
    ((normalize current ledger).live ++ (normalize current ledger).removed).Perm
      (ledger.live ++ ledger.removed) := by
  have partition := ((normalized_partition current).2.2.2).map ledger.origin
  change (((allFin _).map (normalizedOrigin current) ++ normalizedRemoved current).map
      ledger.origin).Perm ((allFin _).map ledger.origin) at partition
  simp only [List.map_append, List.map_map] at partition
  rw [← ofFn_eq_map_allFin, ← ofFn_eq_map_allFin] at partition
  change (List.ofFn (fun gate => ledger.origin (normalizedOrigin current gate)) ++
    (ledger.removed ++ (normalizedRemoved current).map ledger.origin)).Perm _
  have reordered := swap_suffixes
    (List.ofFn (fun gate => ledger.origin (normalizedOrigin current gate)))
    ledger.removed ((normalizedRemoved current).map ledger.origin)
  rw [List.append_assoc] at reordered
  exact reordered.trans (partition.append_right ledger.removed)

theorem normalize_removed_length {inputs outputs : Nat} (current : Implementation inputs outputs)
    (ledger : PhysicalOwnership sourceGates current.gateCount) :
    (normalize current ledger).removed.length =
      ledger.removed.length + (runPhysicalNormalization current).trace.savedGates := by
  change (ledger.removed ++ (normalizedRemoved current).map ledger.origin).length = _
  rw [List.length_append, List.length_map, (normalized_partition current).2.1]

end PhysicalOwnership

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}

def sourcePhysicalOrigins (source : WireCarrier inputs outputs fields) :
    List (PhysicalOrigin source.implementation.gateCount) :=
  List.ofFn PhysicalOrigin.original

namespace Transition

variable {before after : State source} {event : RawEvent fields}

/-- Every constructor follows its real physical operation. In particular both
materializer branches label their literal appended suffix with this event ID. -/
def physicalOwnership (step : Transition source before event after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    PhysicalOwnership source.implementation.gateCount after.current.implementation.gateCount :=
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

/-- R8 ownership names the literal prefix and appended materializer positions
of the program actually produced by the existing restoration operation. -/
theorem restore_physical_positions (state : State source) (event : RawEvent fields)
    (identity : Nat) (kind : event.action = .restoreR8 identity)
    (entry : PendingEntry state identity)
    (ledger : PhysicalOwnership source.implementation.gateCount
      state.current.implementation.gateCount) :
    let added := materializer entry.snapshot.carrier (keepExcept entry.field)
    let step := Transition.restore state event identity kind entry
    (state.restore entry.field entry.snapshot entry.found).current.implementation.candidate.program =
      state.current.implementation.candidate.program.appendSubstituted
        (fun input => .input input) added.implementation.candidate.program ∧
    (∀ gate : Fin state.current.implementation.gateCount,
      (step.physicalOwnership ledger).origin (Fin.castAdd added.implementation.gateCount gate) =
        ledger.origin gate) ∧
    (∀ gate : Fin added.implementation.gateCount,
      (step.physicalOwnership ledger).origin
        (Fin.natAdd state.current.implementation.gateCount gate) = .allocated event.identity gate.val) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro gate
    exact ledger.append_origin_left event.identity _ gate
  · intro gate
    exact ledger.append_origin_right event.identity _ gate

/-- R7 uses the computed realization's actual materializer and the executing
R7 event identity, not the referenced creation's identity. -/
theorem realize_physical_positions (state : State source) (event : RawEvent fields)
    (identity : Nat) (raw : List RawSupportRecord)
    (kind : event.action = .realizeR7 identity raw) (entry : PendingEntry state identity)
    (realization : R7Realization entry.snapshot.carrier raw)
    (computed : computeR7 entry.snapshot.carrier raw = some realization)
    (ledger : PhysicalOwnership source.implementation.gateCount
      state.current.implementation.gateCount) :
    let added := materializer realization.carrier (keepExcept entry.field)
    let step := Transition.realize state event identity raw kind entry realization computed
    (state.restoreR7 entry.field entry.snapshot entry.found raw realization).current.implementation.candidate.program =
      state.current.implementation.candidate.program.appendSubstituted
        (fun input => .input input) added.implementation.candidate.program ∧
    (∀ gate : Fin state.current.implementation.gateCount,
      (step.physicalOwnership ledger).origin (Fin.castAdd added.implementation.gateCount gate) =
        ledger.origin gate) ∧
    (∀ gate : Fin added.implementation.gateCount,
      (step.physicalOwnership ledger).origin
        (Fin.natAdd state.current.implementation.gateCount gate) = .allocated event.identity gate.val) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro gate
    exact ledger.append_origin_left event.identity _ gate
  · intro gate
    exact ledger.append_origin_right event.identity _ gate

def allocations (step : Transition source before event after) :
    List (PhysicalOrigin source.implementation.gateCount) :=
  List.ofFn (fun gate : Fin step.charged => .allocated event.identity gate.val)

theorem allocations_nodup (step : Transition source before event after) :
    step.allocations.Nodup := by
  apply ofFn_nodup_of_injective
  intro left right same
  exact Fin.ext (PhysicalOrigin.allocated.inj same).2

theorem physical_charged (step : Transition source before event after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    (step.physicalOwnership ledger).charged = ledger.charged ++ step.allocations := by
  cases step with
  | restore identity kind entry => rfl
  | realize identity raw kind entry realization computed => rfl
  | _ =>
      change ledger.charged = ledger.charged ++ []
      exact (List.append_nil ledger.charged).symm

theorem physical_removed_length (step : Transition source before event after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    (step.physicalOwnership ledger).removed.length =
      ledger.removed.length + step.removed := by
  cases step with
  | normalize kind =>
      exact PhysicalOwnership.normalize_removed_length before.current.exposed ledger
  | _ => rfl

theorem physical_conservation (step : Transition source before event after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    ((step.physicalOwnership ledger).live ++ (step.physicalOwnership ledger).removed).Perm
      ((ledger.live ++ ledger.removed) ++ step.allocations) := by
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

end Transition

namespace Execution

variable {before after : State source} {events : List (RawEvent fields)}

def physicalOwnership {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    PhysicalOwnership source.implementation.gateCount after.current.implementation.gateCount :=
  match trace with
  | .nil _ => ledger
  | .cons step tail => tail.physicalOwnership (step.physicalOwnership ledger)

def allocations {before after : State source} {events : List (RawEvent fields)}
    (trace : Execution source before events after) :
    List (PhysicalOrigin source.implementation.gateCount) :=
  match trace with
  | .nil _ => []
  | .cons step tail => step.allocations ++ tail.allocations

theorem allocations_length (trace : Execution source before events after) :
    trace.allocations.length = trace.charged := by
  induction trace with
  | nil state => rfl
  | cons step tail ih =>
      change (step.allocations ++ tail.allocations).length = step.charged + tail.charged
      rw [List.length_append, ih]
      exact congrArg (fun count => count + tail.charged) List.length_ofFn

theorem physical_charged (trace : Execution source before events after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    (trace.physicalOwnership ledger).charged = ledger.charged ++ trace.allocations := by
  revert ledger
  induction trace with
  | nil state => intro ledger; exact (List.append_nil ledger.charged).symm
  | cons step tail ih =>
      intro ledger
      change (tail.physicalOwnership (step.physicalOwnership ledger)).charged = _
      rw [ih, step.physical_charged, List.append_assoc]
      rfl

theorem physical_removed_length (trace : Execution source before events after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    (trace.physicalOwnership ledger).removed.length =
      ledger.removed.length + trace.removed := by
  revert ledger
  induction trace with
  | nil state => intro ledger; rfl
  | cons step tail ih =>
      intro ledger
      change (tail.physicalOwnership (step.physicalOwnership ledger)).removed.length = _
      rw [ih, step.physical_removed_length, Nat.add_assoc]
      rfl

theorem physical_conservation (trace : Execution source before events after)
    (ledger : PhysicalOwnership source.implementation.gateCount
      before.current.implementation.gateCount) :
    ((trace.physicalOwnership ledger).live ++ (trace.physicalOwnership ledger).removed).Perm
      ((ledger.live ++ ledger.removed) ++ trace.allocations) := by
  revert ledger
  induction trace with
  | nil state =>
      intro ledger
      rw [allocations, List.append_nil]
      exact List.Perm.refl _
  | cons step tail ih =>
      intro ledger
      have composed := (ih (step.physicalOwnership ledger)).trans
        ((step.physical_conservation ledger).append_right tail.allocations)
      simpa only [physicalOwnership, allocations, List.append_assoc] using composed

theorem allocations_member (trace : Execution source before events after)
    (origin : PhysicalOrigin source.implementation.gateCount) (member : origin ∈ trace.allocations) :
    ∃ identity localGate, origin = .allocated identity localGate ∧
      identity ∈ events.map (fun event => event.identity) := by
  induction trace with
  | nil state => cases member
  | @cons before middle after event remaining step tail ih =>
      rcases List.mem_append.mp member with here | later
      · obtain ⟨gate, same⟩ := List.mem_ofFn.mp here
        exact ⟨event.identity, gate.val, same.symm, List.Mem.head _⟩
      · obtain ⟨identity, localGate, same, belongs⟩ := ih later
        exact ⟨identity, localGate, same, List.mem_cons_of_mem _ belongs⟩

theorem allocations_nodup (trace : Execution source before events after)
    (unique : (events.map (fun event => event.identity)).Nodup) :
    trace.allocations.Nodup := by
  revert unique
  induction trace with
  | nil state => intro _; exact List.nodup_nil
  | @cons before middle after event remaining step tail ih =>
      intro unique
      obtain ⟨absent, tailUnique⟩ := List.nodup_cons.mp unique
      apply List.nodup_append.mpr
      refine ⟨step.allocations_nodup, ih tailUnique, ?_⟩
      intro left leftMember right rightMember same
      obtain ⟨gate, leftIs⟩ := List.mem_ofFn.mp leftMember
      obtain ⟨identity, localGate, rightIs, belongs⟩ := tail.allocations_member right rightMember
      have equal := PhysicalOrigin.allocated.inj (leftIs.trans (same.trans rightIs))
      apply absent
      change event.identity ∈ remaining.map (fun event => event.identity)
      rw [equal.1]
      exact belongs

end Execution

namespace ClosedHistory

variable {raw : List (RawEvent fields)}

/-- No owner map, charge, order or correctness certificate is supplied. -/
def physicalOwnership (history : ClosedHistory source raw) :
    PhysicalOwnership source.implementation.gateCount
      history.state.current.implementation.gateCount :=
  history.execution.physicalOwnership (PhysicalOwnership.initial source.implementation.gateCount)

theorem physical_charged (history : ClosedHistory source raw) :
    history.physicalOwnership.charged = history.execution.allocations :=
  history.execution.physical_charged (PhysicalOwnership.initial source.implementation.gateCount)

theorem physical_partition (history : ClosedHistory source raw) :
    (history.physicalOwnership.live ++ history.physicalOwnership.removed).Perm
      (sourcePhysicalOrigins source ++ history.physicalOwnership.charged) := by
  rw [history.physical_charged]
  have conserved := history.execution.physical_conservation
    (PhysicalOwnership.initial source.implementation.gateCount)
  change (history.physicalOwnership.live ++ history.physicalOwnership.removed).Perm
    ((sourcePhysicalOrigins source ++ []) ++ history.execution.allocations) at conserved
  rw [List.append_nil] at conserved
  exact conserved

theorem physical_ownership (history : ClosedHistory source raw) :
    let ledger := history.physicalOwnership
    ledger.live.length = history.state.current.implementation.gateCount ∧
      ledger.charged.length = history.execution.charged ∧
      ledger.removed.length = history.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (sourcePhysicalOrigins source ++ ledger.charged) := by
  have unique := history.executed_identities_nodup
  rw [history.execution.record_identities] at unique
  have chargedDistinct := history.execution.allocations_nodup unique
  have originalsDistinct : (sourcePhysicalOrigins source).Nodup :=
    ofFn_nodup_of_injective PhysicalOrigin.original
      (fun _ _ same => PhysicalOrigin.original.inj same)
  have totalDistinct : (sourcePhysicalOrigins source ++ history.physicalOwnership.charged).Nodup := by
    rw [history.physical_charged]
    apply List.nodup_append.mpr
    refine ⟨originalsDistinct, chargedDistinct, ?_⟩
    intro left leftMember right rightMember same
    obtain ⟨gate, original⟩ := List.mem_ofFn.mp leftMember
    obtain ⟨identity, localGate, allocated, _⟩ :=
      history.execution.allocations_member right rightMember
    have impossible := original.trans (same.trans allocated)
    cases impossible
  refine ⟨List.length_ofFn, ?_, ?_,
    history.physical_partition.symm.nodup totalDistinct, history.physical_partition⟩
  · rw [history.physical_charged]
    exact history.execution.allocations_length
  · have removed := history.execution.physical_removed_length
      (PhysicalOwnership.initial source.implementation.gateCount)
    change history.physicalOwnership.removed.length = 0 + history.execution.removed at removed
    rw [Nat.zero_add] at removed
    exact removed

end ClosedHistory
end PNP.DirectWire.WireObligationHistory
