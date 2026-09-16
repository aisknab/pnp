/-
Copyright (c) 2026 PNP Labs.

Derive physical owner requests from the literal ambient compilation's origin
ledger. Reuse the existing ownership/extracted-charge kernel, with no supplied
request family and no first-requester overlap hidden as physical ownership.
Historical allocations remain distinct from surviving owned piece sizes.

This does not prove complete manuscript routing, unconditional ZeroSlack or
encoded polynomial bounds for the complete PCCMin construction.
-/

import PNP.NANDWireHistoryAmbientOwnership
import PNP.ResidualTerminalPhysicalOwnership

namespace PNP.DirectWire.WireHistoryAmbientOwnership

open WireObligationHistory WireHistoryArbitrarySupport

/-- Original gates have no allocating event; new gates retain the executing ID. -/
def allocationEvent {gates : Nat} : PhysicalOrigin gates → Option Nat
  | .original _ => none
  | .allocated identity _ => some identity

namespace OwnedCompilation

variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
variable {raw : List (RawEvent (terminalInterfacePorts candidate records).length)}
variable (owned : OwnedCompilation candidate records raw)

/-- A raw event requests precisely its surviving physical allocation positions.
The family is computed before any result support is selected. -/
def eventRequests (owner : Fin raw.length) :
    List (Fin (owned.result candidate records).gateCount) :=
  (allFin (owned.result candidate records).gateCount).filter fun gate =>
    decide (allocationEvent ((owned.ledger candidate records).origin gate) =
      some (raw.get owner).identity)

theorem eventRequests_member (owner : Fin raw.length)
    (gate : Fin (owned.result candidate records).gateCount) :
    gate ∈ owned.eventRequests candidate records owner ↔
      allocationEvent ((owned.ledger candidate records).origin gate) =
        some (raw.get owner).identity := by
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro assigned
    exact List.mem_filter.mpr ⟨mem_allFin gate, by
      simpa only [decide_eq_true_eq] using assigned⟩

/-- Distinct raw events never request the same live physical gate. The old
first-requester kernel therefore cannot hide overlapping derived owners. -/
theorem eventRequests_disjoint (left right : Fin raw.length) (different : left ≠ right)
    (gate : Fin (owned.result candidate records).gateCount)
    (inLeft : gate ∈ owned.eventRequests candidate records left) :
    gate ∉ owned.eventRequests candidate records right := by
  intro inRight
  have leftAt := (owned.eventRequests_member candidate records left gate).mp inLeft
  have rightAt := (owned.eventRequests_member candidate records right gate).mp inRight
  exact different (owned.history.ordered.unique left right
    (Option.some.inj (leftAt.symm.trans rightAt)))

/-- The existing owner selector returns exactly the event named by the actual
physical origin, independent of first-requester precedence. -/
theorem eventOwner_some_iff (owner : Fin raw.length)
    (gate : Fin (owned.result candidate records).gateCount) :
    terminalPhysicalOwner (owned.eventRequests candidate records) gate = some owner ↔
      allocationEvent ((owned.ledger candidate records).origin gate) =
        some (raw.get owner).identity := by
  constructor
  · intro assigned
    exact (owned.eventRequests_member candidate records owner gate).mp
      (terminalPhysicalOwner_first (owned.eventRequests candidate records) gate owner assigned).1
  · intro originAt
    have requested := (owned.eventRequests_member candidate records owner gate).mpr originAt
    cases assigned : terminalPhysicalOwner (owned.eventRequests candidate records) gate with
    | none =>
        exact False.elim
          (((terminalPhysicalOwner_none_iff (owned.eventRequests candidate records) gate).mp
            assigned) owner requested)
    | some other =>
        have otherAt := (owned.eventRequests_member candidate records other gate).mp
          (terminalPhysicalOwner_first (owned.eventRequests candidate records) gate other assigned).1
        have same : other = owner := owned.history.ordered.unique other owner
          (Option.some.inj (otherAt.symm.trans originAt))
        exact congrArg some same

/-- Every historical charge names an actual input event, not a fabricated ID
or the creation snapshot reused in place of the executing allocation event. -/
theorem charged_origin (origin : PhysicalOrigin gates)
    (member : origin ∈ (owned.ledger candidate records).charged) :
    ∃ owner : Fin raw.length, ∃ localGate,
      origin = .allocated (raw.get owner).identity localGate := by
  change origin ∈ owned.history.physicalOwnership.charged.map (liftOrigin candidate records) at member
  obtain ⟨inner, charged, lifted⟩ := List.mem_map.mp member
  rw [owned.history.physical_charged] at charged
  obtain ⟨identity, localGate, innerAt, eventMember⟩ :=
    owned.history.execution.allocations_member inner charged
  obtain ⟨event, eventMember, identityAt⟩ := List.mem_map.mp eventMember
  obtain ⟨owner, _scheduled, eventAt⟩ := List.mem_map.mp eventMember
  have sameIdentity : (raw.get owner).identity = identity :=
    (congrArg (fun event => event.identity) eventAt).trans identityAt
  refine ⟨owner, localGate, ?_⟩
  rw [← lifted, innerAt]
  change PhysicalOrigin.allocated identity localGate =
    PhysicalOrigin.allocated (raw.get owner).identity localGate
  rw [sameIdentity]

/-- An allocated live position cannot escape the raw-event owner family. -/
theorem live_allocated_event (gate : Fin (owned.result candidate records).gateCount)
    (identity localGate : Nat)
    (originAt : (owned.ledger candidate records).origin gate = .allocated identity localGate) :
    ∃ owner : Fin raw.length, (raw.get owner).identity = identity := by
  have live : PhysicalOrigin.allocated identity localGate ∈
      (owned.ledger candidate records).live :=
    List.mem_ofFn.mpr ⟨gate, originAt⟩
  have complete := (owned.ownership candidate records).2.2.2.2
  have present := complete.subset (List.mem_append_left _ live)
  rcases List.mem_append.mp present with original | charged
  · obtain ⟨originalGate, impossible⟩ := List.mem_ofFn.mp original
    cases impossible
  · obtain ⟨owner, otherGate, assigned⟩ :=
      owned.charged_origin candidate records _ charged
    exact ⟨owner, (PhysicalOrigin.allocated.inj assigned).1.symm⟩

/-- Exactly original source/exterior gates belong to the fixed remainder.
Every surviving allocation has a unique actual executing-event owner. -/
theorem eventOwner_none_iff (gate : Fin (owned.result candidate records).gateCount) :
    terminalPhysicalOwner (owned.eventRequests candidate records) gate = none ↔
      allocationEvent ((owned.ledger candidate records).origin gate) = none := by
  rw [terminalPhysicalOwner_none_iff]
  constructor
  · intro unrequested
    cases originAt : (owned.ledger candidate records).origin gate with
    | original originalGate => rfl
    | allocated identity localGate =>
        obtain ⟨owner, identityAt⟩ :=
          owned.live_allocated_event candidate records gate identity localGate originAt
        exact False.elim (unrequested owner
          ((owned.eventRequests_member candidate records owner gate).mpr (by
            rw [originAt, allocationEvent, identityAt])))
  · intro original owner requested
    have assigned := (owned.eventRequests_member candidate records owner gate).mp requested
    rw [original] at assigned
    cases assigned

variable {supportWidth : Nat}

/-- Each piece is the existing extractor applied to the derived owner bucket,
not a supplied weight or an alternative implementation of the ownership kernel. -/
def materializer
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (owner : Option (Fin raw.length)) :
    TerminalExtractedSupport (profileWidth := supportWidth)
      (owned.result candidate records).candidate :=
  terminalOwnedPhysicalMaterializer (owned.result candidate records).candidate
    (owned.eventRequests candidate records) support owner

theorem support_membership
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (owner : Fin raw.length) (gate : Fin (owned.result candidate records).gateCount) :
    gate ∈ terminalOwnedPhysicalGates (owned.eventRequests candidate records) support (some owner) ↔
      gate ∈ terminalSelectedGates support ∧
        allocationEvent ((owned.ledger candidate records).origin gate) =
          some (raw.get owner).identity := by
  rw [terminalOwnedPhysicalGates_partition, owned.eventOwner_some_iff candidate records]

/-- Restriction chooses fewer physical gates but never recalculates their owners. -/
theorem support_restrict
    (larger smaller : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (included : ∀ gate, gate ∈ terminalSelectedGates smaller →
      gate ∈ terminalSelectedGates larger)
    (owner : Option (Fin raw.length)) (gate : Fin (owned.result candidate records).gateCount)
    (member : gate ∈ terminalOwnedPhysicalGates (owned.eventRequests candidate records) smaller owner) :
    gate ∈ terminalOwnedPhysicalGates (owned.eventRequests candidate records) larger owner :=
  terminalOwnedPhysicalGates_restrict (owned.eventRequests candidate records)
    larger smaller included owner gate member

theorem materializer_gateCount
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (owner : Option (Fin raw.length)) :
    (owned.materializer candidate records support owner).gateCount =
      (terminalOwnedPhysicalGates (owned.eventRequests candidate records) support owner).length :=
  terminalOwnedPhysicalMaterializer_gateCount (owned.result candidate records).candidate
    (owned.eventRequests candidate records) support owner

/-- Sum actual extracted surviving piece sizes, including the fixed remainder.
This is not the history's charged sum: removed allocations remain historical. -/
theorem materializer_chargeIdentity
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth)) :
    ((terminalPhysicalOwners raw.length).map (fun owner =>
      (owned.materializer candidate records support owner).gateCount)).sum =
        (extractTerminalSupport (owned.result candidate records).candidate support).gateCount :=
  terminalOwnedPhysicalMaterializer_chargeIdentity (owned.result candidate records).candidate
    (owned.eventRequests candidate records) support

theorem materializer_wholeCharge :
    ((terminalPhysicalOwners raw.length).map (fun owner =>
      (owned.materializer candidate records
        ((allFin (owned.result candidate records).gateCount).map
          (TerminalPrimitiveRecord.gate (profileWidth := supportWidth))) owner).gateCount)).sum =
      (owned.result candidate records).gateCount :=
  terminalOwnedPhysicalMaterializer_wholeCharge (owned.result candidate records).candidate
    (owned.eventRequests candidate records)

/-- Preserve independent open-boundary semantics for every extracted owner piece. -/
theorem materializer_semantics
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (owner : Option (Fin raw.length))
    (boundaryValuation : Valuation (terminalBoundaryPorts
      (owned.result candidate records).candidate.program
      (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner)).length)
    (output : Fin (terminalInterfacePorts (owned.result candidate records).candidate
      (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner)).length) :
    (owned.materializer candidate records support owner).extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics (owned.result candidate records).candidate
        (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner)
        boundaryValuation output :=
  terminalOwnedPhysicalMaterializer_semantics (owned.result candidate records).candidate
    (owned.eventRequests candidate records) support owner boundaryValuation output

theorem materializer_induced
    (support : List (TerminalPrimitiveRecord inputs (owned.result candidate records).gateCount
      outputs supportWidth))
    (owner : Option (Fin raw.length)) (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts (owned.result candidate records).candidate
      (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner)).length) :
    (owned.materializer candidate records support owner).extractedCandidate.semantics
        (terminalInducedBoundaryValuation (owned.result candidate records).candidate
          (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner) input) output =
      (owned.result candidate records).candidate.program.eval input
        ((terminalInterfacePorts (owned.result candidate records).candidate
          (terminalOwnedPhysicalRecords (owned.eventRequests candidate records) support owner)).get output) :=
  terminalOwnedPhysicalMaterializer_induced (owned.result candidate records).candidate
    (owned.eventRequests candidate records) support owner input output

end OwnedCompilation
end PNP.DirectWire.WireHistoryAmbientOwnership
