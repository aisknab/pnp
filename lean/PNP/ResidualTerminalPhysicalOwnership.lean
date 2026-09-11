/-
Copyright (c) 2026 PNP Labs.

Support-independent physical ownership and exact extracted materializer charges.
An assigned owner is not automatically an admissible manuscript materializer.
The existing saturation owner rejection and all semantic minima are unchanged.
-/

import PNP.DirectWireBaseline
import PNP.ResidualTerminalSupportExtraction

namespace PNP
namespace DirectWire

/-- Select the first raw requesting owner before any support is chosen.
    Unrequested physical gates belong to the fixed remainder `none`. -/
def terminalPhysicalOwner {gates ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) :
    Option (Fin ownerCount) :=
  (allFin ownerCount).find? fun owner => decide (gate ∈ requests owner)

/-- Canonical owner buckets, including the fixed remainder. -/
def terminalPhysicalOwners (ownerCount : Nat) : List (Option (Fin ownerCount)) :=
  none :: (allFin ownerCount).map some

/-- Restrict the ambient assignment to the actual selected physical gates.
    Metadata does not create a physical charge. -/
def terminalOwnedPhysicalGates
    {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) : List (Fin gates) :=
  (terminalSelectedGates records).filter fun gate =>
    decide (terminalPhysicalOwner requests gate = owner)

/-- Computed physical records of one owned piece; no weights are supplied. -/
def terminalOwnedPhysicalRecords
    {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (terminalOwnedPhysicalGates requests records owner).map TerminalPrimitiveRecord.gate

/-- Extract the owned piece as an actual open-boundary NAND circuit. -/
def terminalOwnedPhysicalMaterializer
    {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) :
    TerminalExtractedSupport (profileWidth := profileWidth) candidate :=
  extractTerminalSupport candidate (terminalOwnedPhysicalRecords requests records owner)

/-- The fixed remainder consists exactly of gates that no owner requests. -/
theorem terminalPhysicalOwner_none_iff {gates ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates)) (gate : Fin gates) :
    terminalPhysicalOwner requests gate = none ↔
      ∀ owner, gate ∉ requests owner := by
  unfold terminalPhysicalOwner
  constructor
  · intro result owner
    have absent := (List.find?_eq_none.mp result) owner (mem_allFin owner)
    simpa only [decide_eq_true_eq] using absent
  · intro absent
    apply List.find?_eq_none.mpr
    intro owner _member
    simpa only [decide_eq_true_eq] using absent owner

/-- A named owner really requests the gate, and all earlier canonical owners
    do not. Overlap is resolved deterministically, not treated as admissibility. -/
theorem terminalPhysicalOwner_first {gates ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (gate : Fin gates) (owner : Fin ownerCount)
    (assigned : terminalPhysicalOwner requests gate = some owner) :
    gate ∈ requests owner ∧
      ∃ earlier later, allFin ownerCount = earlier ++ owner :: later ∧
        ∀ previous, previous ∈ earlier → gate ∉ requests previous := by
  obtain ⟨requested, earlier, later, shape, first⟩ :=
    List.find?_eq_some_iff_append.mp assigned
  refine ⟨of_decide_eq_true requested, earlier, later, shape, ?_⟩
  intro previous member
  have missing := first previous member
  intro requestedEarlier
  simp only [requestedEarlier, decide_true, Bool.not_true, Bool.false_eq_true] at missing

/-- Exact partition membership in the ambient, support-independent assignment. -/
theorem terminalOwnedPhysicalGates_partition
    {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) (gate : Fin gates) :
    gate ∈ terminalOwnedPhysicalGates requests records owner ↔
      gate ∈ terminalSelectedGates records ∧
        terminalPhysicalOwner requests gate = owner := by
  simp only [terminalOwnedPhysicalGates, List.mem_filter, decide_eq_true_eq]

/-- Two distinct buckets cannot charge the same selected physical gate. -/
theorem terminalOwnedPhysicalGates_disjoint
    {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (left right : Option (Fin ownerCount)) (different : left ≠ right)
    (gate : Fin gates) (inLeft : gate ∈ terminalOwnedPhysicalGates requests records left) :
    gate ∉ terminalOwnedPhysicalGates requests records right := by
  intro inRight
  exact different
    (((terminalOwnedPhysicalGates_partition requests records left gate).mp inLeft).2.symm.trans
      ((terminalOwnedPhysicalGates_partition requests records right gate).mp inRight).2)

/-- Restricting a support never reassigns a retained gate to another owner. -/
theorem terminalOwnedPhysicalGates_restrict
    {inputs gates outputs profileWidth ownerCount : Nat}
    (requests : Fin ownerCount → List (Fin gates))
    (larger smaller : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : ∀ gate, gate ∈ terminalSelectedGates smaller →
      gate ∈ terminalSelectedGates larger)
    (owner : Option (Fin ownerCount)) (gate : Fin gates)
    (member : gate ∈ terminalOwnedPhysicalGates requests smaller owner) :
    gate ∈ terminalOwnedPhysicalGates requests larger owner := by
  obtain ⟨selected, assigned⟩ :=
    (terminalOwnedPhysicalGates_partition requests smaller owner gate).mp member
  exact (terminalOwnedPhysicalGates_partition requests larger owner gate).mpr
    ⟨included gate selected, assigned⟩

private theorem ownership_listNoDuplicates_of_nodup {alpha : Type}
    {items : List alpha} (distinct : items.Nodup) : ListNoDuplicates items := by
  induction items with
  | nil => exact ListNoDuplicates.nil
  | cons head tail ih =>
      have parts := List.nodup_cons.mp distinct
      exact ListNoDuplicates.cons parts.1 (ih parts.2)

private theorem ownership_selected_gate_records
    {inputs gates outputs profileWidth : Nat}
    (items : List (Fin gates)) (gate : Fin gates) :
    gate ∈ terminalSelectedGates
      (items.map (TerminalPrimitiveRecord.gate (inputs := inputs)
        (outputs := outputs) (profileWidth := profileWidth))) ↔ gate ∈ items := by
  rw [mem_terminalSelectedGates_iff, terminalGateSelected_eq_true_iff]
  constructor
  · intro member
    obtain ⟨original, present, same⟩ := List.mem_map.mp member
    have equal : original = gate := TerminalPrimitiveRecord.gate.inj same
    exact equal ▸ present
  · intro member
    exact List.mem_map.mpr ⟨gate, member, rfl⟩

private theorem ownership_selected_gate_records_length
    {inputs gates outputs profileWidth : Nat}
    (items : List (Fin gates)) (distinct : ListNoDuplicates items) :
    (terminalSelectedGates
      (items.map (TerminalPrimitiveRecord.gate (inputs := inputs)
        (outputs := outputs) (profileWidth := profileWidth)))).length = items.length := by
  let records := items.map (TerminalPrimitiveRecord.gate (inputs := inputs)
    (outputs := outputs) (profileWidth := profileWidth))
  apply Nat.le_antisymm
  · exact noDuplicatesSubset_length_le (terminalSelectedGates records) items
      (ownership_listNoDuplicates_of_nodup (terminalSelectedGates_nodup records))
      (fun gate member => (ownership_selected_gate_records items gate).mp member)
  · exact noDuplicatesSubset_length_le items (terminalSelectedGates records) distinct
      (fun gate member => (ownership_selected_gate_records items gate).mpr member)

/-- The weight is the actual extracted NAND gate count, computed once per gate. -/
theorem terminalOwnedPhysicalMaterializer_gateCount
    {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (owner : Option (Fin ownerCount)) :
    (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount =
      (terminalOwnedPhysicalGates requests records owner).length := by
  unfold terminalOwnedPhysicalMaterializer
  rw [extractTerminalSupport_gateCount]
  exact ownership_selected_gate_records_length _
    (ownership_listNoDuplicates_of_nodup
      ((terminalSelectedGates_nodup records).filter _))

private theorem ownership_all_owners_distinct (ownerCount : Nat) :
    ListNoDuplicates (terminalPhysicalOwners ownerCount) := by
  apply ListNoDuplicates.cons
  · intro member
    obtain ⟨owner, _present, impossible⟩ := List.mem_map.mp member
    cases impossible
  · exact noDuplicates_map_of_injective some (fun _ _ same => Option.some.inj same)
      (allFin ownerCount) (allFin_noDuplicates ownerCount)

private theorem ownership_all_owners_member {ownerCount : Nat}
    (owner : Option (Fin ownerCount)) :
    owner ∈ terminalPhysicalOwners ownerCount := by
  cases owner with
  | none => exact List.Mem.head _
  | some index =>
      exact List.Mem.tail none (List.mem_map.mpr ⟨index, mem_allFin index, rfl⟩)

private theorem ownership_sum_map_add {alpha : Type}
    (items : List alpha) (left right : alpha → Nat) :
    (items.map (fun item => left item + right item)).sum =
      (items.map left).sum + (items.map right).sum := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

private theorem ownership_sum_zero {alpha : Type} (items : List alpha) :
    (items.map (fun _ => (0 : Nat))).sum = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      simpa only [List.map_cons, List.sum_cons, Nat.zero_add] using ih

private theorem ownership_indicator_absent {alpha : Type} [DecidableEq alpha]
    (items : List alpha) (target : alpha) (absent : target ∉ items) :
    (items.map (fun item => if target = item then 1 else 0)).sum = 0 := by
  induction items with
  | nil => rfl
  | cons head tail ih =>
      have different : target ≠ head := fun equal =>
        absent (List.mem_cons.mpr (Or.inl equal))
      have tailAbsent : target ∉ tail := fun member => absent (List.Mem.tail head member)
      simp only [List.map_cons, List.sum_cons, if_neg different, Nat.zero_add]
      exact ih tailAbsent

private theorem ownership_indicator_once {alpha : Type} [DecidableEq alpha]
    (items : List alpha) (distinct : ListNoDuplicates items)
    (target : alpha) (member : target ∈ items) :
    (items.map (fun item => if target = item then 1 else 0)).sum = 1 := by
  induction distinct with
  | nil => exact False.elim (List.not_mem_nil member)
  | @cons head tail absent tailDistinct ih =>
      by_cases same : target = head
      · subst target
        change (if head = head then 1 else 0) +
          (tail.map (fun item => if head = item then 1 else 0)).sum = 1
        rw [if_pos rfl, ownership_indicator_absent tail head absent, Nat.add_zero]
      · have inTail : target ∈ tail := (List.mem_cons.mp member).resolve_left same
        simp only [List.map_cons, List.sum_cons, if_neg same, Nat.zero_add]
        exact ih inTail

private theorem ownership_partition_length
    {alpha beta : Type} [DecidableEq beta]
    (owners : List beta) (distinct : ListNoDuplicates owners)
    (assignment : alpha → beta) (complete : ∀ gate, assignment gate ∈ owners)
    (gates : List alpha) :
    (owners.map (fun owner =>
      (gates.filter (fun gate => decide (assignment gate = owner))).length)).sum =
      gates.length := by
  induction gates with
  | nil =>
      simpa only [List.filter_nil, List.length_nil] using ownership_sum_zero owners
  | cons gate remaining ih =>
      have step : (owners.map (fun owner =>
          ((gate :: remaining).filter
            (fun current => decide (assignment current = owner))).length)).sum =
          (owners.map (fun owner => (if assignment gate = owner then 1 else 0) +
            (remaining.filter
              (fun current => decide (assignment current = owner))).length)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro owner _present
        by_cases equal : assignment gate = owner
        · simp only [List.filter_cons, equal, decide_true,
            if_true, List.length_cons]
          omega
        · simp only [List.filter_cons, equal, decide_false, Bool.false_eq_true,
            if_false, Nat.zero_add]
      rw [step, ownership_sum_map_add,
        ownership_indicator_once owners distinct (assignment gate) (complete gate), ih]
      simp only [List.length_cons]
      omega

/-- Exact integer charge identity for arbitrary overlaps and unrequested gates.
    Every summand is an extracted circuit's actual NAND gate count. -/
theorem terminalOwnedPhysicalMaterializer_chargeIdentity
    {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates))
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    ((terminalPhysicalOwners ownerCount).map (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount)).sum =
      (extractTerminalSupport candidate records).gateCount := by
  have counts : (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests records owner).gateCount) =
      (fun owner => (terminalOwnedPhysicalGates requests records owner).length) := by
    funext owner
    exact terminalOwnedPhysicalMaterializer_gateCount candidate requests records owner
  rw [counts, extractTerminalSupport_gateCount]
  exact ownership_partition_length (terminalPhysicalOwners ownerCount)
    (ownership_all_owners_distinct ownerCount) (terminalPhysicalOwner requests)
    (fun gate => ownership_all_owners_member (terminalPhysicalOwner requests gate))
    (terminalSelectedGates records)

/-- Each owned materializer denotes the independent open semantics of its
    computed physical records for every boundary valuation. -/
theorem terminalOwnedPhysicalMaterializer_semantics
    {inputs gates outputs profileWidth ownerCount : Nat}
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
  extractTerminalSupport_semantics candidate
    (terminalOwnedPhysicalRecords requests records owner) boundaryValuation output

/-- Induced boundaries reconnect each interface output to its original gate. -/
theorem terminalOwnedPhysicalMaterializer_induced
    {inputs gates outputs profileWidth ownerCount : Nat}
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
  extractTerminalSupport_induced candidate
    (terminalOwnedPhysicalRecords requests records owner) input output

/-- The full physical circuit is partitioned without losing or inventing cost. -/
theorem terminalOwnedPhysicalMaterializer_wholeCharge
    {inputs gates outputs profileWidth ownerCount : Nat}
    (candidate : Candidate inputs gates outputs)
    (requests : Fin ownerCount → List (Fin gates)) :
    ((terminalPhysicalOwners ownerCount).map (fun owner =>
      (terminalOwnedPhysicalMaterializer candidate requests
        ((allFin gates).map (TerminalPrimitiveRecord.gate (profileWidth := profileWidth)))
        owner).gateCount)).sum = gates := by
  rw [terminalOwnedPhysicalMaterializer_chargeIdentity, extractTerminalSupport_gateCount,
    ownership_selected_gate_records_length _ (allFin_noDuplicates gates), allFin_length]

end DirectWire
end PNP
