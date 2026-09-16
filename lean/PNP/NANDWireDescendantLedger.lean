/-
Copyright (c) 2026 PNP Labs.

Persistent physical identities for actual descendant-stage compilations.
Original coordinates refer to the initial source, and a fresh allocation names
its computed stage, executing event and local gate. Historical charges remain
present when a later stage removes their physical gates.

These are conservation laws for the existing closed computational histories,
not a complete manuscript calculus, successful strategy or polynomial bound.
-/

import PNP.NANDWireDescendantStage

namespace PNP.DirectWire.WireDescendantHistory

open WireObligationHistory WireHistoryAmbientOwnership

inductive DescendantOrigin (initialGates : Nat) where
  | original (gate : Fin initialGates)
  | allocated (stage event localGate : Nat)
  deriving Repr, DecidableEq

def originalOrigins (initialGates : Nat) : List (DescendantOrigin initialGates) :=
  List.ofFn DescendantOrigin.original

def createdBefore {initialGates : Nat} (position : Nat) :
    DescendantOrigin initialGates → Prop
  | .original _ => True
  | .allocated stage _ _ => stage < position

theorem createdBefore_mono {initialGates left right : Nat}
    (origin : DescendantOrigin initialGates)
    (before : createdBefore left origin) (included : left ≤ right) :
    createdBefore right origin := by
  cases origin with
  | original _ => exact True.intro
  | allocated stage event localGate => exact Nat.lt_of_lt_of_le before included

structure PersistentOwnership (initialGates physicalGates : Nat) where
  origin : Fin physicalGates → DescendantOrigin initialGates
  charged : List (DescendantOrigin initialGates)
  removed : List (DescendantOrigin initialGates)

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

private theorem ofFn_injective {alpha : Type} {width : Nat}
    (value : Fin width → alpha) (distinct : (List.ofFn value).Nodup) :
    Function.Injective value := by
  intro left right same
  have leftBound : left.val < (List.ofFn value).length := by
    simpa only [List.length_ofFn] using left.isLt
  have rightBound : right.val < (List.ofFn value).length := by
    simpa only [List.length_ofFn] using right.isLt
  rcases Nat.lt_trichotomy left.val right.val with before | equal | after
  · have different := List.pairwise_iff_getElem.mp distinct
      left.val right.val leftBound rightBound before
    have differentValue : value left ≠ value right := by
      simpa only [List.getElem_ofFn] using different
    exact False.elim (differentValue same)
  · exact Fin.ext equal
  · have different := List.pairwise_iff_getElem.mp distinct
      right.val left.val rightBound leftBound after
    have differentValue : value right ≠ value left := by
      simpa only [List.getElem_ofFn] using different
    exact False.elim (differentValue same.symm)

private theorem swap_suffixes {alpha : Type} (first middle last : List alpha) :
    ((first ++ middle) ++ last).Perm ((first ++ last) ++ middle) := by
  simpa only [List.append_assoc] using
    (List.perm_append_comm (l₁ := middle) (l₂ := last)).append_left first

namespace PersistentOwnership

variable {initialGates physicalGates : Nat}

def live (ledger : PersistentOwnership initialGates physicalGates) :
    List (DescendantOrigin initialGates) := List.ofFn ledger.origin

def initial (initialGates : Nat) : PersistentOwnership initialGates initialGates :=
  ⟨DescendantOrigin.original, [], []⟩

/-- This invariant is proved from the initial ledger and actual compilations.
It is not an extra public raw-program input. -/
structure WellFormed (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) : Prop where
  distinct : (ledger.live ++ ledger.removed).Nodup
  conserved : (ledger.live ++ ledger.removed).Perm
    (originalOrigins initialGates ++ ledger.charged)
  chargedBefore : ∀ origin, origin ∈ ledger.charged → createdBefore position origin

theorem initial_wellFormed (initialGates : Nat) : WellFormed (initial initialGates) 0 := by
  refine ⟨?_, ?_, ?_⟩
  · change (List.ofFn DescendantOrigin.original ++ []).Nodup
    rw [List.append_nil]
    exact ofFn_nodup DescendantOrigin.original
      (fun _ _ same => DescendantOrigin.original.inj same)
  · exact List.Perm.refl _
  · intro origin member
    cases member

theorem accounted_before (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position)
    (origin : DescendantOrigin initialGates)
    (member : origin ∈ originalOrigins initialGates ++ ledger.charged) :
    createdBefore position origin := by
  rcases List.mem_append.mp member with original | charged
  · obtain ⟨gate, originAt⟩ := List.mem_ofFn.mp original
    rw [← originAt]
    exact True.intro
  · exact checked.chargedBefore origin charged

theorem origin_before (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) (gate : Fin physicalGates) :
    createdBefore position (ledger.origin gate) :=
  ledger.accounted_before position checked _ (checked.conserved.subset
    (List.mem_append_left _ (List.mem_ofFn.mpr ⟨gate, rfl⟩)))

theorem origin_injective (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) :
    Function.Injective ledger.origin :=
  ofFn_injective ledger.origin (List.nodup_append.mp checked.distinct).1

/-- An old physical position retains its previous global identity. Only a
genuinely new local allocation receives the current stage coordinate. -/
def liftOrigin (ledger : PersistentOwnership initialGates physicalGates) (position : Nat) :
    PhysicalOrigin physicalGates → DescendantOrigin initialGates
  | .original gate => ledger.origin gate
  | .allocated event localGate => .allocated position event localGate

theorem liftOrigin_original (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) (gate : Fin physicalGates) :
    ledger.liftOrigin position (.original gate) = ledger.origin gate := rfl

theorem liftOrigin_allocated (ledger : PersistentOwnership initialGates physicalGates)
    (position event localGate : Nat) :
    ledger.liftOrigin position (.allocated event localGate) =
      .allocated position event localGate := rfl

theorem liftOrigin_injective (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) (checked : WellFormed ledger position) :
    Function.Injective (ledger.liftOrigin position) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right =>
          exact congrArg PhysicalOrigin.original
            (ledger.origin_injective position checked same)
      | allocated event localGate =>
          have before := ledger.origin_before position checked left
          change ledger.origin left = .allocated position event localGate at same
          rw [same] at before
          exact False.elim (Nat.lt_irrefl position before)
  | allocated event localGate =>
      cases right with
      | original right =>
          have before := ledger.origin_before position checked right
          change DescendantOrigin.allocated position event localGate = ledger.origin right at same
          rw [← same] at before
          exact False.elim (Nat.lt_irrefl position before)
      | allocated otherEvent otherGate =>
          obtain ⟨_, sameEvent, sameGate⟩ := DescendantOrigin.allocated.inj same
          cases sameEvent
          cases sameGate
          rfl

theorem lift_originals (ledger : PersistentOwnership initialGates physicalGates)
    (position : Nat) :
    (ambientOriginals physicalGates).map (ledger.liftOrigin position) = ledger.live := by
  rw [ambientOriginals, List.map_ofFn]
  rfl

variable {inputs outputs : Nat} {source : Implementation inputs outputs} {stage : RawStage}

/-- Follow the exact local compiler map and append its real charge/removal
lists. Previously removed identities never re-enter the live-position map. -/
def advance (ledger : PersistentOwnership initialGates source.gateCount) (position : Nat)
    (compiled : StageCompilation source stage) :
    PersistentOwnership initialGates compiled.result.gateCount :=
  ⟨fun gate => ledger.liftOrigin position (compiled.ledger.origin gate),
    ledger.charged ++ compiled.ledger.charged.map (ledger.liftOrigin position),
    ledger.removed ++ compiled.ledger.removed.map (ledger.liftOrigin position)⟩

theorem advance_live (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage) :
    (ledger.advance position compiled).live =
      compiled.ledger.live.map (ledger.liftOrigin position) := by
  rw [PhysicalOwnership.live, List.map_ofFn]
  rfl

theorem advance_charged_length (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage) :
    (ledger.advance position compiled).charged.length =
      ledger.charged.length + compiled.chargedCount := by
  change (ledger.charged ++ compiled.ledger.charged.map (ledger.liftOrigin position)).length = _
  rw [List.length_append, List.length_map, compiled.physical_ownership.2.1]

theorem advance_removed_length (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage) :
    (ledger.advance position compiled).removed.length =
      ledger.removed.length + compiled.removedCount := by
  change (ledger.removed ++ compiled.ledger.removed.map (ledger.liftOrigin position)).length = _
  rw [List.length_append, List.length_map, compiled.physical_ownership.2.2.1]

/-- This equality ties global identities to the actual literal compiler,
including its computed topological reordering of exterior and history gates. -/
theorem advance_physicalOrigin_position
    (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage)
    (node : Fin ((ArbitrarySupportSplice.exterior compiled.records).length +
      compiled.owned.history.state.current.implementation.gateCount)) :
    (ledger.advance position compiled).origin (compiled.owned.compiled.position node) =
      ledger.liftOrigin position
        (rawNodeOrigin source.candidate compiled.records compiled.owned.history node) :=
  congrArg (ledger.liftOrigin position) (compiled.physicalOrigin_position node)

theorem advance_charge_origin (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage)
    (origin : DescendantOrigin initialGates)
    (member : origin ∈ compiled.ledger.charged.map (ledger.liftOrigin position)) :
    ∃ event ∈ stage.events, ∃ localGate,
      origin = .allocated position event.identity localGate := by
  obtain ⟨innerOrigin, member, lifted⟩ := List.mem_map.mp member
  obtain ⟨event, eventMember, localGate, allocated⟩ := compiled.charged_origin innerOrigin member
  refine ⟨event, eventMember, localGate, ?_⟩
  rw [← lifted, allocated]
  rfl

theorem advance_partition (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage)
    (checked : WellFormed ledger position) :
    ((ledger.advance position compiled).live ++
      (ledger.advance position compiled).removed).Perm
        (originalOrigins initialGates ++ (ledger.advance position compiled).charged) := by
  have inside := compiled.physical_ownership.2.2.2.2.map (ledger.liftOrigin position)
  simp only [List.map_append] at inside
  rw [ledger.lift_originals position] at inside
  have first := swap_suffixes
    (compiled.ledger.live.map (ledger.liftOrigin position))
    ledger.removed (compiled.ledger.removed.map (ledger.liftOrigin position))
  have second := inside.append_right ledger.removed
  have third := swap_suffixes ledger.live
    (compiled.ledger.charged.map (ledger.liftOrigin position)) ledger.removed
  have last := checked.conserved.append_right
    (compiled.ledger.charged.map (ledger.liftOrigin position))
  rw [advance_live]
  change (compiled.ledger.live.map (ledger.liftOrigin position) ++
    (ledger.removed ++ compiled.ledger.removed.map (ledger.liftOrigin position))).Perm
      (originalOrigins initialGates ++
        (ledger.charged ++ compiled.ledger.charged.map (ledger.liftOrigin position)))
  have first' :
      (compiled.ledger.live.map (ledger.liftOrigin position) ++
        (ledger.removed ++ compiled.ledger.removed.map (ledger.liftOrigin position))).Perm
      ((compiled.ledger.live.map (ledger.liftOrigin position) ++
        compiled.ledger.removed.map (ledger.liftOrigin position)) ++ ledger.removed) := by
    simpa only [List.append_assoc] using first
  simpa only [List.append_assoc] using first'.trans (second.trans (third.trans last))

theorem advance_wellFormed (ledger : PersistentOwnership initialGates source.gateCount)
    (position : Nat) (compiled : StageCompilation source stage)
    (checked : WellFormed ledger position) :
    WellFormed (ledger.advance position compiled) (position + 1) := by
  have conserved := ledger.advance_partition position compiled checked
  have localChecked := compiled.physical_ownership
  have localChargedDistinct := (List.nodup_append.mp
    (localChecked.2.2.2.2.nodup localChecked.2.2.2.1)).2.1
  have mappedDistinct :
      (compiled.ledger.charged.map (ledger.liftOrigin position)).Nodup :=
    List.Pairwise.map (ledger.liftOrigin position)
      (fun _ _ different same => different (ledger.liftOrigin_injective position checked same))
      localChargedDistinct
  have totalDistinct :
      (originalOrigins initialGates ++
        (ledger.charged ++ compiled.ledger.charged.map (ledger.liftOrigin position))).Nodup := by
    rw [← List.append_assoc]
    apply List.nodup_append.mpr
    refine ⟨checked.conserved.nodup checked.distinct, mappedDistinct, ?_⟩
    intro old oldMember fresh freshMember same
    have before := ledger.accounted_before position checked old oldMember
    obtain ⟨event, _eventMember, localGate, freshAt⟩ :=
      ledger.advance_charge_origin position compiled fresh freshMember
    rw [same, freshAt] at before
    exact Nat.lt_irrefl position before
  refine ⟨conserved.symm.nodup totalDistinct, conserved, ?_⟩
  intro origin member
  change origin ∈ ledger.charged ++
    compiled.ledger.charged.map (ledger.liftOrigin position) at member
  rcases List.mem_append.mp member with old | fresh
  · exact createdBefore_mono origin (checked.chargedBefore origin old) (Nat.le_succ position)
  · obtain ⟨event, _eventMember, localGate, originAt⟩ :=
      ledger.advance_charge_origin position compiled origin fresh
    rw [originAt]
    exact Nat.lt_succ_self position

end PersistentOwnership

end PNP.DirectWire.WireDescendantHistory
