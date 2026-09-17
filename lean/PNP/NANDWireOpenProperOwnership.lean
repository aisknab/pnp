/-
Copyright (c) 2026 PNP Labs.

Carry every original gate and historical mixed-program allocation through the
actual final one-copy proper-support embedding. The computed compiler position
map transports physical identities; later removals never erase prior charges.
No ownership map, allocation namespace or execution totals are caller inputs.

This proves accounting for an offered program, not global certificate discovery,
full manuscript profiles, unconditional ZeroSlack or polynomial bounds.
-/

import PNP.NANDWireOpenProperSupport

namespace PNP.DirectWire.WireOpenProperSupport

open WireOpenProgram (ProgramOrigin ProgramOwnership programOriginals)

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

variable {inputs outputs fields : Nat}
variable (carrier : WireCarrier inputs outputs fields)
variable (records : List (TerminalPrimitiveRecord inputs
  carrier.implementation.gateCount (outputs + fields) 0))
variable {raw : List WireOpenProgram.RawEvent}

/-- Extracted originals regain their actual outer coordinates; allocation
names retain their computed program position, inner stage, event and local gate. -/
def ownershipLift :
    ProgramOrigin (localSource carrier records).implementation.gateCount →
      ProgramOrigin carrier.implementation.gateCount
  | .original gate =>
      .original (terminalExtractionOrigin carrier.exposed.candidate records gate)
  | .allocated position stage event localGate => .allocated position stage event localGate

theorem ownershipLift_original
    (gate : Fin (localSource carrier records).implementation.gateCount) :
    ownershipLift carrier records (.original gate) =
      .original (terminalExtractionOrigin carrier.exposed.candidate records gate) := rfl

theorem ownershipLift_allocated (position stage event localGate : Nat) :
    ownershipLift carrier records (.allocated position stage event localGate) =
      .allocated position stage event localGate := rfl

theorem ownershipLift_injective : Function.Injective (ownershipLift carrier records) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right =>
          have equal := terminalExtractionOrigin_injective carrier.exposed.candidate records
            (ProgramOrigin.original.inj same)
          exact congrArg ProgramOrigin.original equal
      | allocated position stage event localGate => cases same
  | allocated position stage event localGate =>
      cases right with
      | original right => cases same
      | allocated otherPosition otherStage otherEvent otherGate =>
          obtain ⟨samePosition, sameStage, sameEvent, sameGate⟩ := ProgramOrigin.allocated.inj same
          cases samePosition
          cases sameStage
          cases sameEvent
          cases sameGate
          rfl

private theorem ownership_original_partition :
    ((ArbitrarySupportSplice.exterior records).map ProgramOrigin.original ++
      (programOriginals (localSource carrier records).implementation.gateCount).map
        (ownershipLift carrier records)).Perm
      (programOriginals carrier.implementation.gateCount) := by
  have lifted :
      (programOriginals (localSource carrier records).implementation.gateCount).map
          (ownershipLift carrier records) =
        ((allFin (extractTerminalSupport carrier.exposed.candidate records).gateCount).map
          (terminalExtractionOrigin carrier.exposed.candidate records)).map
            ProgramOrigin.original := by
    rw [programOriginals, ofFn_eq_map_allFin, List.map_map, List.map_map]
    rfl
  rw [lifted, programOriginals, ofFn_eq_map_allFin]
  let candidate : Candidate inputs carrier.implementation.gateCount (outputs + fields) :=
    carrier.exposed.candidate
  have mapped := (WireHistoryAmbientOwnership.original_coordinate_partition
    candidate records).2.map ProgramOrigin.original
  simp only [List.map_append, WireHistoryAmbientOwnership.extractedOrigins, candidate] at mapped
  exact mapped

/-- Raw graph nodes are exactly the unchanged exterior plus the actual final
mixed program, with its persistent historical ownership. -/
def ownershipRawNode (executed : SplicedProgram carrier records raw) :
    Fin ((ArbitrarySupportSplice.exterior records).length + executed.program.result.implementation.gateCount) →
      ProgramOrigin carrier.implementation.gateCount :=
  splitFin (fun index => .original ((ArbitrarySupportSplice.exterior records).get index))
    (fun index => ownershipLift carrier records (executed.program.ownership.origin index))

theorem ownershipRawNode_exterior (executed : SplicedProgram carrier records raw)
    (index : Fin (ArbitrarySupportSplice.exterior records).length) :
    ownershipRawNode carrier records executed (Fin.castAdd executed.program.result.implementation.gateCount index) =
      .original ((ArbitrarySupportSplice.exterior records).get index) :=
  splitFin_left
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      ProgramOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin executed.program.result.implementation.gateCount =>
      ownershipLift carrier records (executed.program.ownership.origin position)) index

theorem ownershipRawNode_program (executed : SplicedProgram carrier records raw)
    (index : Fin executed.program.result.implementation.gateCount) :
    ownershipRawNode carrier records executed
        (Fin.natAdd (ArbitrarySupportSplice.exterior records).length index) =
      ownershipLift carrier records (executed.program.ownership.origin index) :=
  splitFin_right
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      ProgramOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin executed.program.result.implementation.gateCount =>
      ownershipLift carrier records (executed.program.ownership.origin position)) index

private theorem ownership_raw_list (executed : SplicedProgram carrier records raw) :
    List.ofFn (ownershipRawNode carrier records executed) =
      (ArbitrarySupportSplice.exterior records).map ProgramOrigin.original ++
        executed.program.ownership.live.map (ownershipLift carrier records) := by
  rw [ownershipRawNode, ofFn_splitFin, ofFn_get_map]
  rw [ProgramOwnership.live, List.map_ofFn]
  rfl

/-- Follow the inverse of the actual compiler's physical position map. -/
def ownership (executed : SplicedProgram carrier records raw) :
    ProgramOwnership carrier.implementation.gateCount executed.result.implementation.gateCount :=
  ⟨fun position => ownershipRawNode carrier records executed (executed.compiled.physicalOrigin position),
    executed.program.ownership.charged.map (ownershipLift carrier records),
    executed.program.ownership.removed.map (ownershipLift carrier records)⟩

theorem ownership_compiled_position (executed : SplicedProgram carrier records raw)
    (node : Fin ((ArbitrarySupportSplice.exterior records).length + executed.program.result.implementation.gateCount)) :
    (ownership carrier records executed).origin (executed.compiled.position node) =
      ownershipRawNode carrier records executed node := by
  change ownershipRawNode carrier records executed
    (executed.compiled.physicalOrigin (executed.compiled.position node)) = _
  rw [executed.compiled.physicalOrigin_position]

private theorem ownership_live_partition (executed : SplicedProgram carrier records raw) :
    (ownership carrier records executed).live.Perm
      ((ArbitrarySupportSplice.exterior records).map ProgramOrigin.original ++
        executed.program.ownership.live.map (ownershipLift carrier records)) := by
  exact labelled_permutation executed.compiled.physicalOrigin
    (ownershipRawNode carrier records executed) executed.compiled.physicalOrigins_perm _
    (ownership_raw_list carrier records executed)

theorem ownership_partition (executed : SplicedProgram carrier records raw) :
    ((ownership carrier records executed).live ++
      (ownership carrier records executed).removed).Perm
        (programOriginals carrier.implementation.gateCount ++
          (ownership carrier records executed).charged) := by
  have inside := executed.program.physical_ownership.2.2.2.2.map (ownershipLift carrier records)
  simp only [List.map_append] at inside
  have joined := inside.append_left
    ((ArbitrarySupportSplice.exterior records).map ProgramOrigin.original)
  have first := (ownership_live_partition carrier records executed).append_right
    (executed.program.ownership.removed.map (ownershipLift carrier records))
  have last := (ownership_original_partition carrier records).append_right
    (executed.program.ownership.charged.map (ownershipLift carrier records))
  have joined' :
      (((ArbitrarySupportSplice.exterior records).map ProgramOrigin.original ++
        executed.program.ownership.live.map (ownershipLift carrier records)) ++
          executed.program.ownership.removed.map (ownershipLift carrier records)).Perm
      (((ArbitrarySupportSplice.exterior records).map ProgramOrigin.original ++
        (programOriginals (localSource carrier records).implementation.gateCount).map
          (ownershipLift carrier records)) ++
          executed.program.ownership.charged.map (ownershipLift carrier records)) := by
    simpa only [List.append_assoc] using joined
  exact first.trans (joined'.trans last)

/-- Historical costs remain allocations at real computed execution positions,
never original gates relabelled as fresh work. -/
theorem ownership_charged_origin (executed : SplicedProgram carrier records raw)
    (origin : ProgramOrigin carrier.implementation.gateCount)
    (member : origin ∈ (ownership carrier records executed).charged) :
    ∃ position stage event localGate,
      position < raw.length ∧ origin = .allocated position stage event localGate := by
  obtain ⟨inner, present, equation⟩ := List.mem_map.mp member
  obtain ⟨position, stage, event, localGate, inside, innerAt⟩ :=
    executed.program.ownership_charge_origin inner present
  refine ⟨position, stage, event, localGate, inside, ?_⟩
  rw [← equation, innerAt]
  rfl

theorem ownership_distinct (executed : SplicedProgram carrier records raw) :
    ((ownership carrier records executed).live ++
      (ownership carrier records executed).removed).Nodup := by
  have checked := executed.program.physical_ownership
  have chargesDistinct := (List.nodup_append.mp
    (checked.2.2.2.2.nodup checked.2.2.2.1)).2.1
  have mappedDistinct :
      (executed.program.ownership.charged.map (ownershipLift carrier records)).Nodup :=
    List.Pairwise.map (ownershipLift carrier records)
      (fun _ _ different same => different (ownershipLift_injective carrier records same))
      chargesDistinct
  have totalDistinct :
      (programOriginals carrier.implementation.gateCount ++
        (ownership carrier records executed).charged).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨ofFn_nodup ProgramOrigin.original
      (fun _ _ same => ProgramOrigin.original.inj same), mappedDistinct, ?_⟩
    intro old oldMember fresh freshMember same
    obtain ⟨gate, oldAt⟩ := List.mem_ofFn.mp oldMember
    obtain ⟨position, stage, event, localGate, _inside, freshAt⟩ :=
      ownership_charged_origin carrier records executed fresh freshMember
    rw [← oldAt, freshAt] at same
    cases same
  exact (ownership_partition carrier records executed).symm.nodup totalDistinct

/-- Counts are inherited from actual execution; identity conservation also
tracks every allocation which a later operation removes. -/
theorem physical_ownership (executed : SplicedProgram carrier records raw) :
    let ledger := ownership carrier records executed
    ledger.live.length = executed.result.implementation.gateCount ∧
      ledger.charged.length = executed.program.execution.charged ∧
      ledger.removed.length = executed.program.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm
        (programOriginals carrier.implementation.gateCount ++ ledger.charged) := by
  refine ⟨List.length_ofFn, ?_, ?_, ownership_distinct carrier records executed,
    ownership_partition carrier records executed⟩
  · change (executed.program.ownership.charged.map (ownershipLift carrier records)).length = _
    rw [List.length_map]
    exact executed.program.physical_ownership.2.1
  · change (executed.program.ownership.removed.map (ownershipLift carrier records)).length = _
    rw [List.length_map]
    exact executed.program.physical_ownership.2.2.1

end PNP.DirectWire.WireOpenProperSupport
