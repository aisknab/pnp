/-
Copyright (c) 2026 PNP Labs.

Compute support-independent physical owners from the complete raw descendant
program. Reuse the existing physical ownership and open-boundary extraction
kernel. Historical allocation charges and surviving extracted piece sizes
remain separate quantities.

This is not full manuscript materializer admissibility, profile/carrier
compatibility, global route coverage, unconditional ZeroSlack or polynomial
PCCMin. No new owner map, piece weight or correctness premise is a raw input.
-/

import PNP.NANDWireDescendantEvents

namespace PNP.DirectWire.WireDescendantHistory

def allocationEventKey {initialGates : Nat} : DescendantOrigin initialGates → Option (Nat × Nat)
  | .original _ => none
  | .allocated position identity _ => some (position, identity)

namespace CompiledRun

variable {inputs outputs : Nat}
variable {source : Implementation inputs outputs} {stages : List RawStage}
variable (run : CompiledRun source stages)

/-- Each raw input event requests exactly its surviving allocation positions.
The full family is derived before any result support is selected. -/
def eventRequests (owner : Fin (inputEventKeys 0 stages).length) :
    List (Fin run.result.gateCount) :=
  (allFin run.result.gateCount).filter fun gate =>
    decide (allocationEventKey (run.ledger.origin gate) =
      some ((inputEventKeys 0 stages).get owner))

theorem eventRequests_member (owner : Fin (inputEventKeys 0 stages).length)
    (gate : Fin run.result.gateCount) :
    gate ∈ run.eventRequests owner ↔
      allocationEventKey (run.ledger.origin gate) =
        some ((inputEventKeys 0 stages).get owner) := by
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro assigned
    exact List.mem_filter.mpr ⟨mem_allFin gate, by
      simpa only [decide_eq_true_eq] using assigned⟩

/-- No first-requester precedence can conceal overlapping derived owners. -/
theorem eventRequests_disjoint (left right : Fin (inputEventKeys 0 stages).length)
    (different : left ≠ right) (gate : Fin run.result.gateCount)
    (inLeft : gate ∈ run.eventRequests left) : gate ∉ run.eventRequests right := by
  intro inRight
  have leftAt := (run.eventRequests_member left gate).mp inLeft
  have rightAt := (run.eventRequests_member right gate).mp inRight
  exact different (run.inputEventKeys_unique 0 left right
    (Option.some.inj (leftAt.symm.trans rightAt)))

theorem eventOwner_some_iff (owner : Fin (inputEventKeys 0 stages).length)
    (gate : Fin run.result.gateCount) :
    terminalPhysicalOwner run.eventRequests gate = some owner ↔
      allocationEventKey (run.ledger.origin gate) =
        some ((inputEventKeys 0 stages).get owner) := by
  constructor
  · intro assigned
    exact (run.eventRequests_member owner gate).mp
      (terminalPhysicalOwner_first run.eventRequests gate owner assigned).1
  · intro originAt
    have requested := (run.eventRequests_member owner gate).mpr originAt
    cases assigned : terminalPhysicalOwner run.eventRequests gate with
    | none =>
        exact False.elim
          (((terminalPhysicalOwner_none_iff run.eventRequests gate).mp assigned) owner requested)
    | some other =>
        have otherAt := (run.eventRequests_member other gate).mp
          (terminalPhysicalOwner_first run.eventRequests gate other assigned).1
        have same : other = owner := run.inputEventKeys_unique 0 other owner
          (Option.some.inj (otherAt.symm.trans originAt))
        exact congrArg some same

/-- Exactly surviving initial-source gates belong to the fixed remainder.
Every live allocation belongs to its unique actual raw input event. -/
theorem eventOwner_none_iff (gate : Fin run.result.gateCount) :
    terminalPhysicalOwner run.eventRequests gate = none ↔
      allocationEventKey (run.ledger.origin gate) = none := by
  rw [terminalPhysicalOwner_none_iff]
  constructor
  · intro unrequested
    cases originAt : run.ledger.origin gate with
    | original originalGate => rfl
    | allocated position identity localGate =>
        have actual := run.ledger_live_allocated_event gate position identity localGate originAt
        obtain ⟨index, bound, keyAt⟩ := List.mem_iff_getElem.mp actual
        let owner : Fin (inputEventKeys 0 stages).length := ⟨index, bound⟩
        have ownerAt : (inputEventKeys 0 stages).get owner = (position, identity) := keyAt
        exact False.elim (unrequested owner
          ((run.eventRequests_member owner gate).mpr (by
            rw [originAt, allocationEventKey, ownerAt])))
  · intro original owner requested
    have assigned := (run.eventRequests_member owner gate).mp requested
    rw [original] at assigned
    cases assigned

variable {supportWidth : Nat}

/-- Actual existing extractor, applied to a source-derived owner bucket. -/
def materializer
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (owner : Option (Fin (inputEventKeys 0 stages).length)) :
    TerminalExtractedSupport (profileWidth := supportWidth) run.result.candidate :=
  terminalOwnedPhysicalMaterializer run.result.candidate run.eventRequests support owner

theorem support_membership
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (owner : Fin (inputEventKeys 0 stages).length) (gate : Fin run.result.gateCount) :
    gate ∈ terminalOwnedPhysicalGates run.eventRequests support (some owner) ↔
      gate ∈ terminalSelectedGates support ∧
        allocationEventKey (run.ledger.origin gate) =
          some ((inputEventKeys 0 stages).get owner) := by
  rw [terminalOwnedPhysicalGates_partition, run.eventOwner_some_iff]

/-- Restriction selects fewer gates without recomputing ownership. -/
theorem support_restrict
    (larger smaller : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (included : ∀ gate, gate ∈ terminalSelectedGates smaller →
      gate ∈ terminalSelectedGates larger)
    (owner : Option (Fin (inputEventKeys 0 stages).length)) (gate : Fin run.result.gateCount)
    (member : gate ∈ terminalOwnedPhysicalGates run.eventRequests smaller owner) :
    gate ∈ terminalOwnedPhysicalGates run.eventRequests larger owner :=
  terminalOwnedPhysicalGates_restrict run.eventRequests larger smaller included owner gate member

theorem materializer_gateCount
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (owner : Option (Fin (inputEventKeys 0 stages).length)) :
    (run.materializer support owner).gateCount =
      (terminalOwnedPhysicalGates run.eventRequests support owner).length :=
  terminalOwnedPhysicalMaterializer_gateCount run.result.candidate run.eventRequests support owner

/-- Sum surviving extracted sizes including the initial-source remainder.
This need not equal the historical allocation total. -/
theorem materializer_chargeIdentity
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth)) :
    ((terminalPhysicalOwners (inputEventKeys 0 stages).length).map (fun owner =>
      (run.materializer support owner).gateCount)).sum =
        (extractTerminalSupport run.result.candidate support).gateCount :=
  terminalOwnedPhysicalMaterializer_chargeIdentity run.result.candidate run.eventRequests support

theorem materializer_wholeCharge :
    ((terminalPhysicalOwners (inputEventKeys 0 stages).length).map (fun owner =>
      (run.materializer ((allFin run.result.gateCount).map
        (TerminalPrimitiveRecord.gate (profileWidth := supportWidth))) owner).gateCount)).sum =
      run.result.gateCount :=
  terminalOwnedPhysicalMaterializer_wholeCharge run.result.candidate run.eventRequests

theorem materializer_semantics
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (owner : Option (Fin (inputEventKeys 0 stages).length))
    (boundaryValuation : Valuation (terminalBoundaryPorts run.result.candidate.program
      (terminalOwnedPhysicalRecords run.eventRequests support owner)).length)
    (output : Fin (terminalInterfacePorts run.result.candidate
      (terminalOwnedPhysicalRecords run.eventRequests support owner)).length) :
    (run.materializer support owner).extractedCandidate.semantics boundaryValuation output =
      terminalOpenSupportSemantics run.result.candidate
        (terminalOwnedPhysicalRecords run.eventRequests support owner) boundaryValuation output :=
  terminalOwnedPhysicalMaterializer_semantics run.result.candidate
    run.eventRequests support owner boundaryValuation output

theorem materializer_induced
    (support : List (TerminalPrimitiveRecord inputs run.result.gateCount outputs supportWidth))
    (owner : Option (Fin (inputEventKeys 0 stages).length)) (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts run.result.candidate
      (terminalOwnedPhysicalRecords run.eventRequests support owner)).length) :
    (run.materializer support owner).extractedCandidate.semantics
        (terminalInducedBoundaryValuation run.result.candidate
          (terminalOwnedPhysicalRecords run.eventRequests support owner) input) output =
      run.result.candidate.program.eval input
        ((terminalInterfacePorts run.result.candidate
          (terminalOwnedPhysicalRecords run.eventRequests support owner)).get output) :=
  terminalOwnedPhysicalMaterializer_induced run.result.candidate
    run.eventRequests support owner input output

end CompiledRun
end PNP.DirectWire.WireDescendantHistory
