/-
Copyright (c) 2026 PNP Labs.

Transport every original and historical descendant allocation through the
actual one-copy outer splice while the ambient obligation ledger may be open.
The physical-position map follows the very compiler which builds the result.

These are actual ownership facts for an offered nested computational program,
not global certificate discovery, full manuscript profiles, ZeroSlack or
polynomial execution.
-/

import PNP.NANDWireOpenSupportSplice
import PNP.NANDWireDescendantOwnership
import PNP.NANDCompiledGateProvenance

namespace PNP.DirectWire.WireOpenSupportSplice

open WireObligationHistory (State)
open WireDescendantProperSupport (SplicedRun localSource)
open WireDescendantHistory (DescendantOrigin PersistentOwnership originalOrigins)

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

private theorem ofFn_get {alpha : Type} (items : List alpha) :
    List.ofFn items.get = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.ofFn_succ]
      change head :: List.ofFn tail.get = head :: tail
      rw [ih]

private theorem ofFn_get_map {alpha beta : Type} (items : List alpha) (value : alpha → beta) :
    List.ofFn (fun index => value (items.get index)) = items.map value :=
  (List.map_ofFn (f := items.get) (g := value)).symm.trans
    (congrArg (List.map value) (ofFn_get items))

private theorem labelled_permutation {alpha : Type} {left right : Nat}
    (index : Fin left → Fin right) (labels : Fin right → alpha)
    (permutation : ((allFin left).map index).Perm (allFin right))
    (target : List alpha) (targetAt : List.ofFn labels = target) :
    (List.ofFn (fun position => labels (index position))).Perm target := by
  have moved := permutation.map labels
  rw [List.map_map, ← ofFn_eq_map_allFin, ← ofFn_eq_map_allFin, targetAt] at moved
  exact moved

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

variable {inputs outputs fields : Nat} {source : WireCarrier inputs outputs fields}
variable (before : State source)
variable (records : List (TerminalPrimitiveRecord inputs
  before.current.implementation.gateCount (outputs + fields) 0))
variable {stages : List WireDescendantHistory.RawStage}

/-- Extracted originals regain their actual outer coordinates; allocation
names retain the inner stage, event and local physical position. -/
def ownershipLift :
    DescendantOrigin (localSource before.current records).gateCount →
      DescendantOrigin before.current.implementation.gateCount
  | .original gate =>
      .original (terminalExtractionOrigin before.current.exposed.candidate records gate)
  | .allocated stage event localGate => .allocated stage event localGate

theorem ownershipLift_original
    (gate : Fin (localSource before.current records).gateCount) :
    ownershipLift before records (.original gate) =
      .original (terminalExtractionOrigin before.current.exposed.candidate records gate) := rfl

theorem ownershipLift_allocated (stage event localGate : Nat) :
    ownershipLift before records (.allocated stage event localGate) =
      .allocated stage event localGate := rfl

theorem ownershipLift_injective : Function.Injective (ownershipLift before records) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right =>
          have equal := terminalExtractionOrigin_injective before.current.exposed.candidate records
            (DescendantOrigin.original.inj same)
          exact congrArg DescendantOrigin.original equal
      | allocated stage event localGate => cases same
  | allocated stage event localGate =>
      cases right with
      | original right => cases same
      | allocated otherStage otherEvent otherGate =>
          obtain ⟨sameStage, sameEvent, sameGate⟩ := DescendantOrigin.allocated.inj same
          cases sameStage
          cases sameEvent
          cases sameGate
          rfl

private theorem ownership_original_partition :
    ((ArbitrarySupportSplice.exterior records).map DescendantOrigin.original ++
      (originalOrigins (localSource before.current records).gateCount).map
        (ownershipLift before records)).Perm
      (originalOrigins before.current.implementation.gateCount) := by
  have lifted :
      (originalOrigins (localSource before.current records).gateCount).map
          (ownershipLift before records) =
        ((allFin (extractTerminalSupport before.current.exposed.candidate records).gateCount).map
          (terminalExtractionOrigin before.current.exposed.candidate records)).map
            DescendantOrigin.original := by
    rw [originalOrigins, ofFn_eq_map_allFin, List.map_map, List.map_map]
    rfl
  rw [lifted, originalOrigins, ofFn_eq_map_allFin]
  let candidate : Candidate inputs before.current.implementation.gateCount (outputs + fields) :=
    before.current.exposed.candidate
  have mapped := (WireHistoryAmbientOwnership.original_coordinate_partition
    candidate records).2.map DescendantOrigin.original
  simp only [List.map_append, WireHistoryAmbientOwnership.extractedOrigins, candidate] at mapped
  exact mapped

/-- Raw graph nodes are exactly the unchanged exterior plus the actual final
nested program, with its persistent historical ownership. -/
def ownershipRawNode (executed : SplicedRun before.current records stages) :
    Fin ((ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount) →
      DescendantOrigin before.current.implementation.gateCount :=
  splitFin (fun index => .original ((ArbitrarySupportSplice.exterior records).get index))
    (fun index => ownershipLift before records (executed.run.ledger.origin index))

theorem ownershipRawNode_exterior (executed : SplicedRun before.current records stages)
    (index : Fin (ArbitrarySupportSplice.exterior records).length) :
    ownershipRawNode before records executed (Fin.castAdd executed.run.result.gateCount index) =
      .original ((ArbitrarySupportSplice.exterior records).get index) :=
  splitFin_left
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      DescendantOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin executed.run.result.gateCount =>
      ownershipLift before records (executed.run.ledger.origin position)) index

theorem ownershipRawNode_nested (executed : SplicedRun before.current records stages)
    (index : Fin executed.run.result.gateCount) :
    ownershipRawNode before records executed
        (Fin.natAdd (ArbitrarySupportSplice.exterior records).length index) =
      ownershipLift before records (executed.run.ledger.origin index) :=
  splitFin_right
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      DescendantOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin executed.run.result.gateCount =>
      ownershipLift before records (executed.run.ledger.origin position)) index

private theorem ownership_raw_list (executed : SplicedRun before.current records stages) :
    List.ofFn (ownershipRawNode before records executed) =
      (ArbitrarySupportSplice.exterior records).map DescendantOrigin.original ++
        executed.run.ledger.live.map (ownershipLift before records) := by
  rw [ownershipRawNode, ofFn_splitFin, ofFn_get_map]
  rw [PersistentOwnership.live, List.map_ofFn]
  rfl

/-- Follow the inverse of the actual compiler's physical position map. -/
def ownership (executed : SplicedRun before.current records stages) :
    PersistentOwnership before.current.implementation.gateCount executed.result.implementation.gateCount :=
  ⟨fun position => ownershipRawNode before records executed (executed.compiled.physicalOrigin position),
    executed.run.ledger.charged.map (ownershipLift before records),
    executed.run.ledger.removed.map (ownershipLift before records)⟩

theorem ownership_compiled_position (executed : SplicedRun before.current records stages)
    (node : Fin ((ArbitrarySupportSplice.exterior records).length + executed.run.result.gateCount)) :
    (ownership before records executed).origin (executed.compiled.position node) =
      ownershipRawNode before records executed node := by
  change ownershipRawNode before records executed
    (executed.compiled.physicalOrigin (executed.compiled.position node)) = _
  rw [executed.compiled.physicalOrigin_position]

private theorem ownership_live_partition (executed : SplicedRun before.current records stages) :
    (ownership before records executed).live.Perm
      ((ArbitrarySupportSplice.exterior records).map DescendantOrigin.original ++
        executed.run.ledger.live.map (ownershipLift before records)) := by
  exact labelled_permutation executed.compiled.physicalOrigin
    (ownershipRawNode before records executed) executed.compiled.physicalOrigins_perm _
    (ownership_raw_list before records executed)

theorem ownership_partition (executed : SplicedRun before.current records stages) :
    ((ownership before records executed).live ++
      (ownership before records executed).removed).Perm
        (originalOrigins before.current.implementation.gateCount ++
          (ownership before records executed).charged) := by
  have inside := executed.run.physical_ownership.2.2.2.2.map (ownershipLift before records)
  simp only [List.map_append] at inside
  have joined := inside.append_left
    ((ArbitrarySupportSplice.exterior records).map DescendantOrigin.original)
  have first := (ownership_live_partition before records executed).append_right
    (executed.run.ledger.removed.map (ownershipLift before records))
  have last := (ownership_original_partition before records).append_right
    (executed.run.ledger.charged.map (ownershipLift before records))
  have joined' :
      (((ArbitrarySupportSplice.exterior records).map DescendantOrigin.original ++
        executed.run.ledger.live.map (ownershipLift before records)) ++
          executed.run.ledger.removed.map (ownershipLift before records)).Perm
      (((ArbitrarySupportSplice.exterior records).map DescendantOrigin.original ++
        (originalOrigins (localSource before.current records).gateCount).map
          (ownershipLift before records)) ++
          executed.run.ledger.charged.map (ownershipLift before records)) := by
    simpa only [List.append_assoc] using joined
  exact first.trans (joined'.trans last)

/-- A historical charge is a real inner allocation, never an original gate
relabeled as new. Its stage lies inside the complete executed program. -/
theorem ownership_charged_origin (executed : SplicedRun before.current records stages)
    (origin : DescendantOrigin before.current.implementation.gateCount)
    (member : origin ∈ (ownership before records executed).charged) :
    ∃ stage event localGate, stage < stages.length ∧ origin = .allocated stage event localGate := by
  obtain ⟨inner, present, equation⟩ := List.mem_map.mp member
  cases inner with
  | original gate =>
      have checked := executed.run.physical_ownership
      have separate := (List.nodup_append.mp (checked.2.2.2.2.nodup checked.2.2.2.1)).2.2
      exact False.elim (separate (.original gate) (List.mem_ofFn.mpr ⟨gate, rfl⟩)
        (.original gate) present rfl)
  | allocated stage event localGate =>
      exact ⟨stage, event, localGate,
        executed.run.ledger_charged_before (.allocated stage event localGate) present, equation.symm⟩

theorem ownership_distinct (executed : SplicedRun before.current records stages) :
    ((ownership before records executed).live ++
      (ownership before records executed).removed).Nodup := by
  have checked := executed.run.physical_ownership
  have chargesDistinct := (List.nodup_append.mp
    (checked.2.2.2.2.nodup checked.2.2.2.1)).2.1
  have mappedDistinct :
      (executed.run.ledger.charged.map (ownershipLift before records)).Nodup :=
    List.Pairwise.map (ownershipLift before records)
      (fun _ _ different same => different (ownershipLift_injective before records same))
      chargesDistinct
  have totalDistinct :
      (originalOrigins before.current.implementation.gateCount ++
        (ownership before records executed).charged).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ofFn_nodup DescendantOrigin.original
      (fun _ _ same => DescendantOrigin.original.inj same), mappedDistinct, ?_⟩
    intro old oldMember fresh freshMember same
    obtain ⟨gate, oldAt⟩ := List.mem_ofFn.mp oldMember
    obtain ⟨stage, event, localGate, _inside, freshAt⟩ :=
      ownership_charged_origin before records executed fresh freshMember
    rw [← oldAt, freshAt] at same
    cases same
  exact (ownership_partition before records executed).symm.nodup totalDistinct

/-- Counts are inherited from actual execution; identity conservation also
tracks every allocation which a later nested stage removes. -/
theorem physical_ownership (executed : SplicedRun before.current records stages) :
    let ledger := ownership before records executed
    ledger.live.length = executed.result.implementation.gateCount ∧
      ledger.charged.length = executed.run.chargedCount ∧
      ledger.removed.length = executed.run.removedCount ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ ledger.charged) := by
  refine ⟨List.length_ofFn, ?_, ?_, ownership_distinct before records executed,
    ownership_partition before records executed⟩
  · change (executed.run.ledger.charged.map (ownershipLift before records)).length = _
    rw [List.length_map]
    exact executed.run.physical_ownership.2.1
  · change (executed.run.ledger.removed.map (ownershipLift before records)).length = _
    rw [List.length_map]
    exact executed.run.physical_ownership.2.2.1

namespace Receipt

variable {before} {raw : WireDescendantCertificate.RawCertificate}

def ownership (receipt : Receipt before raw) :
    PersistentOwnership before.current.implementation.gateCount receipt.next.current.implementation.gateCount :=
  WireOpenSupportSplice.ownership before receipt.records receipt.executed

theorem physical_ownership (receipt : Receipt before raw) :
    receipt.ownership.live.length = receipt.next.current.implementation.gateCount ∧
      receipt.ownership.charged.length = receipt.executed.run.chargedCount ∧
      receipt.ownership.removed.length = receipt.executed.run.removedCount ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Nodup ∧
      (receipt.ownership.live ++ receipt.ownership.removed).Perm
        (originalOrigins before.current.implementation.gateCount ++ receipt.ownership.charged) :=
  WireOpenSupportSplice.physical_ownership before receipt.records receipt.executed

end Receipt
end PNP.DirectWire.WireOpenSupportSplice
