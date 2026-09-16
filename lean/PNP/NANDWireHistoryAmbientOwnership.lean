/-
Copyright (c) 2026 PNP Labs.

Carry computed history allocation identities through the literal arbitrary-
support splice. Original extracted gates map back through the actual extractor;
exterior gates occur once; new allocations retain their executing-event ID.
The final physical-position map follows the actual topological compiler.

This is physical ownership for the existing computational history route, not
complete manuscript routing, unconditional ZeroSlack or polynomial PCCMin.
-/

import PNP.NANDWireHistoryArbitrarySupport
import PNP.NANDWireHistoryPhysicalOwnership
import PNP.NANDCompiledGateProvenance

namespace PNP.DirectWire.WireHistoryAmbientOwnership

open WireObligationHistory WireHistoryArbitrarySupport

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

private theorem ofFn_get {alpha : Type} (items : List alpha) :
    List.ofFn items.get = items := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      rw [List.ofFn_succ]
      change head :: List.ofFn tail.get = head :: tail
      rw [ih]

private theorem ofFn_get_map {alpha beta : Type} (items : List alpha) (value : alpha → beta) :
    List.ofFn (fun index => value (items.get index)) = items.map value := by
  exact (List.map_ofFn (f := items.get) (g := value)).symm.trans
    (congrArg (List.map value) (ofFn_get items))

variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

/-- Original ambient gates, independently of any selected support or history. -/
def ambientOriginals (gates : Nat) : List (PhysicalOrigin gates) :=
  List.ofFn PhysicalOrigin.original

/-- Lift actual extracted source positions back to the original ambient circuit.
Fresh allocations remain identified by their executing event and local gate. -/
def liftOrigin :
    PhysicalOrigin (extractedCarrier candidate records).implementation.gateCount →
      PhysicalOrigin gates
  | .original gate => .original (terminalExtractionOrigin candidate records gate)
  | .allocated event localGate => .allocated event localGate

theorem liftOrigin_injective : Function.Injective (liftOrigin candidate records) := by
  intro left right same
  cases left with
  | original left =>
      cases right with
      | original right =>
          have equal := terminalExtractionOrigin_injective candidate records
            (PhysicalOrigin.original.inj same)
          exact congrArg PhysicalOrigin.original equal
      | allocated event localGate => cases same
  | allocated event localGate =>
      cases right with
      | original right => cases same
      | allocated otherEvent otherGate =>
          obtain ⟨sameEvent, sameGate⟩ := PhysicalOrigin.allocated.inj same
          cases sameEvent
          cases sameGate
          rfl

/-- Source coordinates of the extracted gates in their actual physical order. -/
def extractedOrigins : List (Fin gates) :=
  (allFin (extractTerminalSupport candidate records).gateCount).map
    (terminalExtractionOrigin candidate records)

/-- Every original gate is either an unchanged exterior gate or an actual
extracted origin, once each. No ordering equality is assumed. -/
theorem original_coordinate_partition :
    (ArbitrarySupportSplice.exterior records ++ extractedOrigins candidate records).Nodup ∧
      (ArbitrarySupportSplice.exterior records ++ extractedOrigins candidate records).Perm
        (allFin gates) := by
  have exteriorDistinct : (ArbitrarySupportSplice.exterior records).Nodup :=
    terminalSelectedGateIndices_nodup _
  have extractedDistinct : (extractedOrigins candidate records).Nodup :=
    List.Pairwise.map (terminalExtractionOrigin candidate records)
      (fun _ _ different same => different (terminalExtractionOrigin_injective candidate records same))
      (allFin_nodup _)
  have distinct : (ArbitrarySupportSplice.exterior records ++
      extractedOrigins candidate records).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨exteriorDistinct, extractedDistinct, ?_⟩
    intro outside outsideMember inside insideMember same
    obtain ⟨position, _, origin⟩ := List.mem_map.mp insideMember
    have selected := terminalExtractionOrigin_selected candidate records position
    have unselected := (ArbitrarySupportSplice.mem_exterior_iff records outside).mp outsideMember
    have equal : terminalExtractionOrigin candidate records position = outside := origin.trans same.symm
    rw [equal, unselected] at selected
    cases selected
  refine ⟨distinct, ?_⟩
  apply perm_of_nodup_members distinct (allFin_nodup gates)
  intro gate
  constructor
  · intro _member
    exact mem_allFin gate
  · intro _member
    cases selected : terminalGateSelected records gate with
    | false =>
        exact List.mem_append_left _ ((ArbitrarySupportSplice.mem_exterior_iff records gate).mpr selected)
    | true =>
        exact List.mem_append_right _ (List.mem_map.mpr
          ⟨terminalExtractionGateIndex candidate records gate selected, mem_allFin _,
            terminalExtractionOrigin_gateIndex candidate records gate selected⟩)

private theorem original_label_partition :
    ((ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original ++
      (sourcePhysicalOrigins (extractedCarrier candidate records)).map (liftOrigin candidate records)).Perm
        (ambientOriginals gates) := by
  have lifted :
      (sourcePhysicalOrigins (extractedCarrier candidate records)).map (liftOrigin candidate records) =
        ((allFin (extractTerminalSupport candidate records).gateCount).map
          (terminalExtractionOrigin candidate records)).map PhysicalOrigin.original := by
    rw [sourcePhysicalOrigins, ofFn_eq_map_allFin, List.map_map, List.map_map]
    rfl
  rw [lifted, ambientOriginals, ofFn_eq_map_allFin]
  have mapped := ((original_coordinate_partition candidate records).2).map PhysicalOrigin.original
  simpa only [List.map_append, extractedOrigins] using mapped

variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}

/-- Label the literal graph's exterior prefix and actual history-result suffix. -/
def rawNodeOrigin (history : ClosedHistory (extractedCarrier candidate records) raw) :
    Fin ((ArbitrarySupportSplice.exterior records).length +
      history.state.current.implementation.gateCount) → PhysicalOrigin gates :=
  splitFin (fun index => .original ((ArbitrarySupportSplice.exterior records).get index))
    (fun index => liftOrigin candidate records (history.physicalOwnership.origin index))

theorem rawNodeOrigin_exterior (history : ClosedHistory (extractedCarrier candidate records) raw)
    (index : Fin (ArbitrarySupportSplice.exterior records).length) :
    rawNodeOrigin candidate records history
      (Fin.castAdd history.state.current.implementation.gateCount index) =
        .original ((ArbitrarySupportSplice.exterior records).get index) :=
  splitFin_left
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      PhysicalOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin history.state.current.implementation.gateCount =>
      liftOrigin candidate records (history.physicalOwnership.origin position)) index

theorem rawNodeOrigin_history (history : ClosedHistory (extractedCarrier candidate records) raw)
    (index : Fin history.state.current.implementation.gateCount) :
    rawNodeOrigin candidate records history
      (Fin.natAdd (ArbitrarySupportSplice.exterior records).length index) =
        liftOrigin candidate records (history.physicalOwnership.origin index) :=
  splitFin_right
    (fun position : Fin (ArbitrarySupportSplice.exterior records).length =>
      PhysicalOrigin.original ((ArbitrarySupportSplice.exterior records).get position))
    (fun position : Fin history.state.current.implementation.gateCount =>
      liftOrigin candidate records (history.physicalOwnership.origin position)) index

private theorem rawNodeOrigins_list (history : ClosedHistory (extractedCarrier candidate records) raw) :
    List.ofFn (rawNodeOrigin candidate records history) =
      (ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original ++
        history.physicalOwnership.live.map (liftOrigin candidate records) := by
  rw [rawNodeOrigin, ofFn_splitFin, ofFn_get_map]
  rw [PhysicalOwnership.live, List.map_ofFn]
  rfl

/-- Actual compiled result positions are labelled using the computed inverse of
the same compiler position map that builds this result program. -/
def physicalOwnership (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    PhysicalOwnership gates compiled.count :=
  ⟨fun position => rawNodeOrigin candidate records history (compiled.physicalOrigin position),
    history.physicalOwnership.charged.map (liftOrigin candidate records),
    history.physicalOwnership.removed.map (liftOrigin candidate records)⟩

theorem physicalOrigin_position (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current)))
    (node : Fin ((ArbitrarySupportSplice.exterior records).length +
      history.state.current.implementation.gateCount)) :
    (physicalOwnership candidate records history compiled).origin (compiled.position node) =
      rawNodeOrigin candidate records history node := by
  change rawNodeOrigin candidate records history
    (compiled.physicalOrigin (compiled.position node)) = _
  rw [compiled.physicalOrigin_position]

private theorem compiled_live_partition (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    (physicalOwnership candidate records history compiled).live.Perm
      ((ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original ++
        history.physicalOwnership.live.map (liftOrigin candidate records)) := by
  have permuted := compiled.physicalOrigins_perm.map (rawNodeOrigin candidate records history)
  change (((allFin compiled.count).map compiled.physicalOrigin).map
    (rawNodeOrigin candidate records history)).Perm _ at permuted
  rw [List.map_map] at permuted
  rw [← ofFn_eq_map_allFin, ← ofFn_eq_map_allFin, rawNodeOrigins_list] at permuted
  exact permuted

/-- Complete identity conservation in the actual whole-circuit physical order. -/
theorem physical_partition (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    ((physicalOwnership candidate records history compiled).live ++
      (physicalOwnership candidate records history compiled).removed).Perm
        (ambientOriginals gates ++ (physicalOwnership candidate records history compiled).charged) := by
  have inside := history.physical_partition.map (liftOrigin candidate records)
  simp only [List.map_append] at inside
  have joined := inside.append_left
    ((ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original)
  have first := (compiled_live_partition candidate records history compiled).append_right
    (history.physicalOwnership.removed.map (liftOrigin candidate records))
  have last := (original_label_partition candidate records).append_right
    (history.physicalOwnership.charged.map (liftOrigin candidate records))
  have joined' :
      (((ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original ++
        history.physicalOwnership.live.map (liftOrigin candidate records)) ++
          history.physicalOwnership.removed.map (liftOrigin candidate records)).Perm
      (((ArbitrarySupportSplice.exterior records).map PhysicalOrigin.original ++
        (sourcePhysicalOrigins (extractedCarrier candidate records)).map (liftOrigin candidate records)) ++
          history.physicalOwnership.charged.map (liftOrigin candidate records)) := by
    simpa only [List.append_assoc] using joined
  exact first.trans (joined'.trans last)

/-- No original or event-allocated gate is lost or double counted. Historical
charges remain counted even when their gates were subsequently removed. -/
theorem physical_ownership (history : ClosedHistory (extractedCarrier candidate records) raw)
    (compiled : CompiledRawNandGraph
      (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))) :
    let ledger := physicalOwnership candidate records history compiled
    ledger.live.length = compiled.count ∧
      ledger.charged.length = history.execution.charged ∧
      ledger.removed.length = history.execution.removed ∧
      (ledger.live ++ ledger.removed).Nodup ∧
      (ledger.live ++ ledger.removed).Perm (ambientOriginals gates ++ ledger.charged) := by
  have conserved := physical_partition candidate records history compiled
  have historyChecked := history.physical_ownership
  have chargedDistinct := (List.nodup_append.mp
    (history.physical_partition.nodup historyChecked.2.2.2.1)).2.1
  have originalDistinct : (ambientOriginals gates).Nodup := by
    rw [ambientOriginals, ofFn_eq_map_allFin]
    exact List.Pairwise.map PhysicalOrigin.original
      (fun _ _ different same => different (PhysicalOrigin.original.inj same)) (allFin_nodup gates)
  have totalDistinct : (ambientOriginals gates ++
      (physicalOwnership candidate records history compiled).charged).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨originalDistinct, ?_, ?_⟩
    · exact List.Pairwise.map (liftOrigin candidate records)
        (fun _ _ different same => different (liftOrigin_injective candidate records same)) chargedDistinct
    · intro original originalMember allocated allocatedMember same
      obtain ⟨gate, originalAt⟩ := List.mem_ofFn.mp originalMember
      obtain ⟨inner, member, lifted⟩ := List.mem_map.mp allocatedMember
      rw [history.physical_charged] at member
      obtain ⟨identity, localGate, innerAt, _⟩ := history.execution.allocations_member inner member
      rw [innerAt] at lifted
      have impossible := originalAt.trans (same.trans lifted.symm)
      cases impossible
  refine ⟨List.length_ofFn, ?_, ?_, conserved.symm.nodup totalDistinct, conserved⟩
  · change (history.physicalOwnership.charged.map (liftOrigin candidate records)).length = _
    rw [List.length_map]
    exact historyChecked.2.1
  · change (history.physicalOwnership.removed.map (liftOrigin candidate records)).length = _
    rw [List.length_map]
    exact historyChecked.2.2.1

/-- The output retains evidence of the exact two computations it came from.
These fields are produced internally; raw inputs supply no owner map or order. -/
structure OwnedCompilation (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) where
  history : ClosedHistory (extractedCarrier candidate records) raw
  compiled : CompiledRawNandGraph
    (ArbitrarySupportSplice.graph candidate records (fieldCandidate history.state.current))
  executed : compileHistory (extractedCarrier candidate records) raw = some history
  compiledAt : ArbitrarySupportSplice.compile candidate records
    (fieldCandidate history.state.current) = some compiled

namespace OwnedCompilation

def result (owned : OwnedCompilation candidate records raw) : Implementation inputs outputs :=
  (ArbitrarySupportSplice.result candidate records
    (fieldCandidate owned.history.state.current) owned.compiled).toImplementation

def ledger (owned : OwnedCompilation candidate records raw) :
    PhysicalOwnership gates (owned.result candidate records).gateCount :=
  physicalOwnership candidate records owned.history owned.compiled

theorem ownership (owned : OwnedCompilation candidate records raw) :
    let accounting := owned.ledger candidate records
    accounting.live.length = (owned.result candidate records).gateCount ∧
      accounting.charged.length = owned.history.execution.charged ∧
      accounting.removed.length = owned.history.execution.removed ∧
      (accounting.live ++ accounting.removed).Nodup ∧
      (accounting.live ++ accounting.removed).Perm (ambientOriginals gates ++ accounting.charged) :=
  physical_ownership candidate records owned.history owned.compiled

theorem semantics (owned : OwnedCompilation candidate records raw)
    (valuation : Valuation inputs) (output : Fin outputs) :
    (owned.result candidate records).candidate.semantics valuation output =
      candidate.semantics valuation output :=
  closedHistory_result_semantics candidate records owned.history owned.compiled valuation output

end OwnedCompilation

/-- Execute the existing history and literal splice algorithms and attach their
derived ownership. No supplied history, order, charge, map or successful splice
is accepted as an input. -/
def compileOwned (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) :
    Option (OwnedCompilation candidate records raw) :=
  match executed : compileHistory (extractedCarrier candidate records) raw with
  | none => none
  | some history =>
      match compiledAt : ArbitrarySupportSplice.compile candidate records
          (fieldCandidate history.state.current) with
      | none => none
      | some compiled => some ⟨history, compiled, executed, compiledAt⟩

/-- Adding ownership changes neither the accepted input language nor the
literal implementation returned by the existing source-only constructor. -/
theorem compileOwned_result (raw : List (RawEvent (terminalInterfacePorts candidate records).length)) :
    (compileOwned candidate records raw).map (OwnedCompilation.result candidate records) =
      WireHistoryArbitrarySupport.compile candidate records raw := by
  unfold compileOwned
  split
  · rename_i failed
    simp only [Option.map_none, WireHistoryArbitrarySupport.compile, failed]
  · rename_i history executed
    split
    · rename_i failed
      simp only [Option.map_none, WireHistoryArbitrarySupport.compile, executed, failed]
    · rename_i compiled built
      simp only [Option.map_some, OwnedCompilation.result,
        WireHistoryArbitrarySupport.compile, executed, built]

end PNP.DirectWire.WireHistoryAmbientOwnership
