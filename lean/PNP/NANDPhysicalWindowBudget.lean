/-
Copyright (c) 2026 PNP Labs.

Physical-window dimension and explicit candidate-count bounds, derived from
selected NAND gates rather than ambient declared input width. The bound is a
constant only for a fixed window schema. It is not a complete encoded-runtime
or global selector-completeness theorem.
-/

import PNP.NANDBoundedPhysicalWindowSearch

namespace PNP.DirectWire.PhysicalWindowSearch

private theorem nodup_length_le_subset {alpha : Type}
    {left right : List alpha} (distinct : left.Nodup)
    (included : ∀ item, item ∈ left → item ∈ right) :
    left.length ≤ right.length := by
  induction left generalizing right with
  | nil => exact Nat.zero_le _
  | cons head tail ih =>
      obtain ⟨absent, tailDistinct⟩ := List.nodup_cons.mp distinct
      obtain ⟨before, after, rfl⟩ :=
        List.append_of_mem (included head (List.Mem.head tail))
      have tailIncluded : ∀ item, item ∈ tail → item ∈ before ++ after := by
        intro item member
        have present := included item (List.Mem.tail head member)
        rcases List.mem_append.mp present with earlier | later
        · exact List.mem_append_left _ earlier
        · rcases List.mem_cons.mp later with same | remaining
          · exact False.elim (absent (same ▸ member))
          · exact List.mem_append_right _ remaining
      have bound := ih tailDistinct tailIncluded
      simp only [List.length_append, List.length_cons] at bound ⊢
      omega

private theorem allFin_nodup (width : Nat) : (allFin width).Nodup := by
  induction width with
  | zero => exact List.nodup_nil
  | succ width ih =>
      change (0 :: (allFin width).map Fin.succ).Nodup
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨index, _, same⟩ := List.mem_map.mp member
        have impossible := congrArg Fin.val same
        change index.val + 1 = 0 at impossible
        omega
      · exact List.Pairwise.map Fin.succ
          (fun left right different same =>
            different (Fin.ext (Nat.succ.inj (congrArg Fin.val same)))) ih

private theorem flatMap_length_le {alpha beta : Type}
    (items : List alpha) (mapping : alpha → List beta) (bound : Nat)
    (each : ∀ item, item ∈ items → (mapping item).length ≤ bound) :
    (items.flatMap mapping).length ≤ items.length * bound := by
  induction items with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun item member => each item (List.mem_cons_of_mem head member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add first rest) (Nat.le_of_eq (Nat.add_comm _ _))

private theorem flatMap_length_eq {alpha beta : Type}
    (items : List alpha) (mapping : alpha → List beta) (size : Nat)
    (each : ∀ item, item ∈ items → (mapping item).length = size) :
    (items.flatMap mapping).length = items.length * size := by
  induction items with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      rw [List.flatMap_cons, List.length_append, each head List.mem_cons_self,
        ih (fun item member => each item (List.mem_cons_of_mem head member))]
      simp only [List.length_cons, Nat.succ_mul, Nat.add_comm]

variable {inputs gates outputs profileWidth : Nat}
variable (candidate : Candidate inputs gates outputs)
variable (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))

/-- Only the selected gates' two physical source positions contribute boundary ports. -/
def selectedOccurrences : List (TerminalSupportWire inputs gates) :=
  (terminalSelectedGates records).flatMap fun consumer =>
    (candidate.program.terminalGateSources consumer).1.terminalWireOccurrences ++
      (candidate.program.terminalGateSources consumer).2.terminalWireOccurrences

theorem boundary_mem_selectedOccurrences (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts candidate.program records) :
    wire ∈ selectedOccurrences candidate records := by
  obtain ⟨_external, consumer, _enumerated, selected, used⟩ :=
    (terminalBoundaryWire_eq_true_iff candidate.program records wire).mp
      ((mem_terminalBoundaryPorts_iff candidate.program records wire).mp member)
  apply List.mem_flatMap.mpr
  refine ⟨consumer, (mem_terminalSelectedGates_iff records consumer).mpr selected, ?_⟩
  change (decide ((candidate.program.terminalGateSources consumer).1.terminalSupportWire? = some wire) ||
    decide ((candidate.program.terminalGateSources consumer).2.terminalSupportWire? = some wire)) = true at used
  simp only [Bool.or_eq_true] at used
  rcases used with left | right
  · exact List.mem_append_left _
      ((Source.mem_terminalWireOccurrences_iff _ wire).mpr (of_decide_eq_true left))
  · exact List.mem_append_right _
      ((Source.mem_terminalWireOccurrences_iff _ wire).mpr (of_decide_eq_true right))

theorem selectedOccurrences_length :
    (selectedOccurrences candidate records).length ≤ 2 * (terminalSelectedGates records).length := by
  have bound := flatMap_length_le (terminalSelectedGates records)
    (fun consumer =>
      (candidate.program.terminalGateSources consumer).1.terminalWireOccurrences ++
        (candidate.program.terminalGateSources consumer).2.terminalWireOccurrences) 2
    (fun consumer _member => by
      rw [List.length_append]
      exact Nat.add_le_add (Source.terminalWireOccurrences_length _)
        (Source.terminalWireOccurrences_length _))
  simpa only [selectedOccurrences, Nat.mul_comm] using bound

/-- Incoming dimension depends on this window, not the surrounding input declaration. -/
theorem boundary_length_le_selected :
    (terminalBoundaryPorts candidate.program records).length ≤
      2 * (extractTerminalSupport candidate records).gateCount := by
  rw [extractTerminalSupport_gateCount]
  exact Nat.le_trans
    (nodup_length_le_subset (terminalBoundaryPorts_nodup candidate.program records)
      (boundary_mem_selectedOccurrences candidate records))
    (selectedOccurrences_length candidate records)

/-- Every outgoing interface position names a selected physical gate. -/
theorem interface_length_le_selected :
    (terminalInterfacePorts candidate records).length ≤
      (extractTerminalSupport candidate records).gateCount := by
  rw [extractTerminalSupport_gateCount]
  apply nodup_length_le_subset
    (List.Pairwise.filter (terminalInterfaceGate candidate records) (allFin_nodup gates))
  intro producer member
  have checked := (mem_terminalInterfacePorts_iff candidate records producer).mp member
  simp only [terminalInterfaceGate, Bool.and_eq_true] at checked
  have selected := checked.1
  exact (mem_terminalSelectedGates_iff records producer).mpr selected

theorem window_dimensions (limit : Nat)
    (bounded : (extractTerminalSupport candidate records).gateCount ≤ limit) :
    (terminalBoundaryPorts candidate.program records).length ≤ 2 * limit ∧
      (terminalInterfacePorts candidate records).length ≤ limit :=
  ⟨Nat.le_trans (boundary_length_le_selected candidate records)
      (Nat.mul_le_mul_left 2 bounded),
    Nat.le_trans (interface_length_le_selected candidate records) bounded⟩

private theorem allSources_length (inputs gates : Nat) :
    (allSources inputs gates).length = inputs + gates + 2 := by
  simp only [allSources, List.length_append, List.length_map, allFin_length,
    List.length_cons, List.length_nil]
  omega

private theorem allGates_length (inputs gates : Nat) :
    (allGates inputs gates).length = (inputs + gates + 2) ^ 2 := by
  calc
    _ = (allSources inputs gates).length * (allSources inputs gates).length :=
      flatMap_length_eq _ _ _ (fun _ _ => List.length_map _)
    _ = (inputs + gates + 2) ^ 2 := by
      rw [allSources_length, Nat.pow_two]

private theorem allOutputWords_length (inputs gates outputs : Nat) :
    (allOutputWords inputs gates outputs).length = (inputs + gates + 2) ^ outputs := by
  induction outputs with
  | zero => rfl
  | succ outputs ih =>
      calc
        _ = (allSources inputs gates).length * (inputs + gates + 2) ^ outputs := by
          apply flatMap_length_eq
          intro _head _member
          rw [List.length_map, ih]
        _ = (inputs + gates + 2) ^ (outputs + 1) := by
          rw [allSources_length, Nat.pow_succ, Nat.mul_comm]

private theorem allPrograms_length_le (inputs gates base : Nat)
    (room : inputs + gates + 2 ≤ base) :
    (allPrograms inputs gates).length ≤ base ^ (2 * gates) := by
  induction gates with
  | zero => exact Nat.le_refl 1
  | succ gates ih =>
      have earlierRoom : inputs + gates + 2 ≤ base := by omega
      calc
        _ = (allPrograms inputs gates).length * (allGates inputs gates).length :=
          flatMap_length_eq _ _ _ (fun _ _ => List.length_map _)
        _ ≤ base ^ (2 * gates) * base ^ 2 :=
          Nat.mul_le_mul (ih earlierRoom) (by
            rw [allGates_length]
            exact Nat.pow_le_pow_left earlierRoom 2)
        _ = base ^ (2 * (gates + 1)) := by
          rw [← Nat.pow_add]
          have same : 2 * gates + 2 = 2 * (gates + 1) := by omega
          rw [same]

/-- Count the actual enumerator, including duplicate syntax; no quotient is assumed. -/
theorem allCandidates_length_le (inputs gates outputs base : Nat)
    (room : inputs + gates + 2 ≤ base) :
    (allCandidates inputs gates outputs).length ≤ base ^ (2 * gates + outputs) := by
  calc
    _ = (allPrograms inputs gates).length * (allOutputWords inputs gates outputs).length :=
      flatMap_length_eq _ _ _ (fun _ _ => List.length_map _)
    _ ≤ base ^ (2 * gates) * base ^ outputs :=
      Nat.mul_le_mul (allPrograms_length_le inputs gates base room) (by
        rw [allOutputWords_length]
        exact Nat.pow_le_pow_left room outputs)
    _ = base ^ (2 * gates + outputs) := (Nat.pow_add _ _ _).symm

/-- Exponential in a variable window size, constant only for a fixed FT schema. -/
def fixedWindowBudget (limit : Nat) : Nat :=
  limit * (3 * limit + 2) ^ (3 * limit)

theorem smallerCandidates_length_le (boundary outputs budget limit : Nat)
    (boundaryBound : boundary ≤ 2 * limit) (outputBound : outputs ≤ limit)
    (budgetBound : budget ≤ limit) :
    (smallerCandidates boundary outputs budget).length ≤ fixedWindowBudget limit := by
  have each : ∀ size, size ∈ List.range budget →
      ((allCandidates boundary size outputs).map Candidate.toImplementation).length ≤
        (3 * limit + 2) ^ (3 * limit) := by
    intro size member
    have sizeBound := List.mem_range.mp member
    rw [List.length_map]
    have room : boundary + size + 2 ≤ 3 * limit + 2 := by omega
    have exponent : 2 * size + outputs ≤ 3 * limit := by omega
    exact Nat.le_trans (allCandidates_length_le boundary size outputs _ room)
      (Nat.pow_le_pow_right (by omega) exponent)
  have bound := flatMap_length_le (List.range budget)
    (fun size => (allCandidates boundary size outputs).map Candidate.toImplementation)
    ((3 * limit + 2) ^ (3 * limit)) each
  simp only [List.length_range] at bound
  exact Nat.le_trans bound (Nat.mul_le_mul_right _ budgetBound)

/-- The source-generated local universe obeys the fixed-schema candidate budget. -/
theorem candidateUniverse_length_le (limit : Nat)
    (bounded : (extractTerminalSupport candidate records).gateCount ≤ limit) :
    (candidateUniverse candidate records).length ≤ fixedWindowBudget limit :=
  smallerCandidates_length_le _ _ _ limit
    (window_dimensions candidate records limit bounded).1
    (window_dimensions candidate records limit bounded).2 bounded

end PNP.DirectWire.PhysicalWindowSearch
