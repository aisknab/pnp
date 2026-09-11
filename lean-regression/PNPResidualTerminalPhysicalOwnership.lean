import PNP.ResidualTerminalPhysicalOwnership
import PNP.ResidualTerminalSaturationCostBalance

namespace PNP.DirectWire

-- Exact arbitrary-dimension public interfaces.
example {gates ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) :
    terminalPhysicalOwner requests gate = none ↔
      ∀ owner, gate ∉ requests owner :=
  terminalPhysicalOwner_none_iff requests gate

example {gates ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates)
    (owner : Fin ownerCount)
    (assigned : terminalPhysicalOwner requests gate = some owner) :
    gate ∈ requests owner ∧
      ∃ earlier later, allFin ownerCount = earlier ++ owner :: later ∧
        ∀ previous, previous ∈ earlier → gate ∉ requests previous :=
  terminalPhysicalOwner_first requests gate owner assigned

example {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) (gate : Fin gates) :
    gate ∈ terminalOwnedPhysicalGates requests records owner ↔
      gate ∈ terminalSelectedGates records ∧ terminalPhysicalOwner requests gate = owner :=
  terminalOwnedPhysicalGates_partition requests records owner gate

example {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (left right : Option (Fin ownerCount)) (different : left ≠ right)
    (gate : Fin gates) (member : gate ∈ terminalOwnedPhysicalGates requests records left) :
    gate ∉ terminalOwnedPhysicalGates requests records right :=
  terminalOwnedPhysicalGates_disjoint requests records left right different gate member

example {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (larger smaller : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : ∀ gate, gate ∈ terminalSelectedGates smaller →
      gate ∈ terminalSelectedGates larger)
    (owner : Option (Fin ownerCount)) (gate : Fin gates)
    (member : gate ∈ terminalOwnedPhysicalGates requests smaller owner) :
    gate ∈ terminalOwnedPhysicalGates requests larger owner :=
  terminalOwnedPhysicalGates_restrict requests larger smaller included owner gate member

example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) :
    (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount =
      (terminalOwnedPhysicalGates requests records owner).length :=
  terminalOwnedPhysicalMaterializer_gateCount candidate requests records owner

example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalPhysicalOwners ownerCount).map (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount)).sum =
      (extractTerminalSupport candidate records).gateCount :=
  terminalOwnedPhysicalMaterializer_chargeIdentity candidate requests records

example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount))
    (boundaryValuation : Valuation (terminalBoundaryPorts candidate.program
      (terminalOwnedPhysicalRecords requests records owner)).length)
    (output : Fin (terminalInterfacePorts candidate
      (terminalOwnedPhysicalRecords requests records owner)).length) :
    (terminalOwnedPhysicalMaterializer candidate requests records owner).extractedCandidate.semantics
        boundaryValuation output =
      terminalOpenSupportSemantics candidate
        (terminalOwnedPhysicalRecords requests records owner) boundaryValuation output :=
  terminalOwnedPhysicalMaterializer_semantics candidate requests records owner boundaryValuation output

example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) (input : Valuation inputs)
    (output : Fin (terminalInterfacePorts candidate
      (terminalOwnedPhysicalRecords requests records owner)).length) :
    (terminalOwnedPhysicalMaterializer candidate requests records owner).extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate
          (terminalOwnedPhysicalRecords requests records owner) input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate
          (terminalOwnedPhysicalRecords requests records owner)).get output) :=
  terminalOwnedPhysicalMaterializer_induced candidate requests records owner input output

example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates)) :
    ((terminalPhysicalOwners ownerCount).map (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests
        ((allFin gates).map (TerminalPrimitiveRecord.gate (profileWidth := profileWidth)))
        owner).gateCount)).sum = gates :=
  terminalOwnedPhysicalMaterializer_wholeCharge candidate requests

-- A canonical assignment does not discharge the old unique-active-owner condition.
-- No minimum calculation or finite transparency search is needed for this guard.
example {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (model : TerminalCandidateSaturationModel (profileWidth := profileWidth) candidate)
    (event : TerminalSaturationTraceEvent inputs gates outputs profileWidth)
    (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates)
    (required : event.required = .gate gate)
    (ambiguous : (terminalSaturationEventOwners
      (terminalCandidateSaturationSystem candidate model) event).length ≠ 1) :
    ∃ owner, terminalPhysicalOwner requests gate = owner ∧
      ¬ TerminalTransparentSaturationStep candidate model event := by
  refine ⟨terminalPhysicalOwner requests gate, rfl, ?_⟩
  intro transparent
  have unique := transparent.uniqueMaterializerOwner
  rw [required] at unique
  exact ambiguous unique

namespace PhysicalOwnershipRegression

abbrev Record := TerminalPrimitiveRecord 1 4 1 1

def candidate : Candidate 1 4 1 :=
  Candidate.ofDirectWireWord
    (.snoc
      (.snoc
        (.snoc
          (.snoc .empty { left := .input 0, right := .input 0 })
          { left := .gate 0, right := .constant false })
        { left := .gate 0, right := .gate 1 })
      { left := .gate 2, right := .gate 2 })
    ⟨fun _ => .gate 3⟩

-- Gate 1 has overlapping requests; gate 2 has a duplicate request.
-- Gate 3 is not requested and must remain in the fixed remainder.
def requests : Fin 2 → List (Fin 4) :=
  fun owner => if owner.val = 0 then [0, 1] else [1, 2, 2]

def fullRecords : List Record := [.gate 0, .gate 1, .gate 2, .gate 3]
def restrictedRecords : List Record := [.gate 2, .profile 0, .gate 1, .gate 2]
def reorderedRecords : List Record := [.gate 1, .gate 2]
def metadataOnly : List Record := [.boundary 0, .interface 0, .profile 0]

example : terminalPhysicalOwner requests 1 = some 0 := by decide
example : terminalPhysicalOwner requests 3 = none := by decide
example : terminalOwnedPhysicalGates requests fullRecords (some 0) = [0, 1] := by decide
example : terminalOwnedPhysicalGates requests fullRecords (some 1) = [2] := by decide
example : terminalOwnedPhysicalGates requests fullRecords none = [3] := by decide

example : terminalOwnedPhysicalGates requests restrictedRecords (some 0) = [1] := by decide
example : terminalOwnedPhysicalGates requests restrictedRecords (some 1) = [2] := by decide
example (owner : Option (Fin 2)) :
    terminalOwnedPhysicalGates requests restrictedRecords owner =
      terminalOwnedPhysicalGates requests reorderedRecords owner := by
  cases owner with
  | none => decide
  | some index =>
      refine Fin.cases ?_ (fun last => ?_) index
      · decide
      · have lastZero : last = 0 := by
          apply Fin.ext
          have bound := last.isLt
          omega
        subst last
        decide

example :
    ((terminalPhysicalOwners 2).map (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests fullRecords owner).gateCount)).sum = 4 :=
  (terminalOwnedPhysicalMaterializer_chargeIdentity candidate requests fullRecords).trans (by decide)

example (owner : Option (Fin 2)) :
    (terminalOwnedPhysicalMaterializer candidate requests metadataOnly owner).gateCount = 0 := by
  rw [terminalOwnedPhysicalMaterializer_gateCount]
  rfl

example :
    (terminalOwnedPhysicalMaterializer candidate (fun index : Fin 0 => Fin.elim0 index)
      fullRecords none).gateCount = 4 := by
  rw [terminalOwnedPhysicalMaterializer_gateCount]
  decide

def emptyCandidate : Candidate 0 0 0 :=
  Candidate.ofDirectWireWord .empty ⟨Fin.elim0⟩

example (ownerCount : Nat) (requests : Fin ownerCount → List (Fin 0)) :
    ((terminalPhysicalOwners ownerCount).map (fun owner =>
      (terminalOwnedPhysicalMaterializer emptyCandidate requests
        ([] : List (TerminalPrimitiveRecord 0 0 0 0)) owner).gateCount)).sum = 0 :=
  terminalOwnedPhysicalMaterializer_chargeIdentity emptyCandidate requests []

-- The owner-1 piece consumes values computed in the owner-0 piece.
-- Its boundary is physically derived, not an independent guessed annotation.
example :
    (terminalOwnedPhysicalMaterializer candidate requests fullRecords (some 1)).boundary =
      [.gate 0, .gate 1] := by decide

example (input : Valuation 1)
    (output : Fin (terminalInterfacePorts candidate
      (terminalOwnedPhysicalRecords requests fullRecords (some 1))).length) :
    (terminalOwnedPhysicalMaterializer candidate requests fullRecords (some 1)).extractedCandidate.semantics
        (terminalInducedBoundaryValuation candidate
          (terminalOwnedPhysicalRecords requests fullRecords (some 1)) input) output =
      candidate.program.eval input
        ((terminalInterfacePorts candidate
          (terminalOwnedPhysicalRecords requests fullRecords (some 1))).get output) :=
  terminalOwnedPhysicalMaterializer_induced candidate requests fullRecords (some 1) input output

-- Bounded execution only; the universal kernel theorems above own proof authority.
#eval do
  let counts := (terminalPhysicalOwners 2).map fun owner =>
    (terminalOwnedPhysicalMaterializer candidate requests fullRecords owner).gateCount
  unless counts == [1, 2, 1] do
    throw (IO.userError "physical ownership counts mismatch")
  let emptyCounts := (terminalPhysicalOwners 2).map fun owner =>
    (terminalOwnedPhysicalMaterializer candidate requests ([] : List Record) owner).gateCount
  unless emptyCounts == [0, 0, 0] do
    throw (IO.userError "empty physical ownership counts mismatch")
  IO.println "physical-ownership-regression: exact counts and empty support passed"

end PhysicalOwnershipRegression
end PNP.DirectWire
