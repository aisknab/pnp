/-
Copyright (c) 2026 PNP Labs.

Source-derived search for proper constant/unary computational R7 gains.
The maximal scan uses only actual gate sources, one optional boundary wire
and one omitted original gate. The complete search derives its support
family; no supplied support-completeness certificate is proof authority.

Candidate counts are not a complete encoded-size runtime theorem. This does
not establish the full manuscript carrier, Package E or global ZeroSlack.
-/

import PNP.NANDWireUnaryArbitrarySupport
import PNP.ResidualTerminalFrontierPushout

namespace PNP.DirectWire.WireUnarySupportSearch

abbrev BoundaryChoice (inputs gates : Nat) :=
  Option (TerminalSupportWire inputs gates)

variable {inputs gates total outputs profileWidth : Nat}

private def boundaryGate (choice : BoundaryChoice inputs total) (index : Nat) : Bool :=
  match choice with
  | some (.gate gate) => decide (gate.val = index)
  | _ => false

private def sourceAdmitted (choice : BoundaryChoice inputs total)
    (selected : Valuation gates) : Source inputs gates → Bool
  | .constant _ => true
  | .input index => decide (choice = some (.input index))
  | .gate index => selected index || boundaryGate choice index.val

/-- Topological maximal support avoiding a gate and every chosen boundary gate. -/
def maximalSelection : {gates : Nat} → Program inputs gates →
    BoundaryChoice inputs total → Nat → Valuation gates
  | 0, .empty, _choice, _omitted => Fin.elim0
  | gates + 1, .snoc initial gate, choice, omitted =>
      let earlier := maximalSelection initial choice omitted
      Valuation.snoc earlier
        (if gates ≠ omitted ∧ boundaryGate choice gates = false then
          sourceAdmitted choice earlier gate.left &&
            sourceAdmitted choice earlier gate.right
        else false)

private theorem selection_earlier (initial : Program inputs gates)
    (gate : Gate inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) (index : Fin gates) :
    maximalSelection (initial.snoc gate) choice omitted index.castSucc =
      maximalSelection initial choice omitted index :=
  Valuation.snoc_castSucc _ _ index

private theorem selection_last (initial : Program inputs gates)
    (gate : Gate inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) :
    maximalSelection (initial.snoc gate) choice omitted (Fin.last gates) =
      if gates ≠ omitted ∧ boundaryGate choice gates = false then
        sourceAdmitted choice (maximalSelection initial choice omitted) gate.left &&
          sourceAdmitted choice (maximalSelection initial choice omitted) gate.right
      else false :=
  Valuation.snoc_last _ _

private theorem selection_last_iff (initial : Program inputs gates)
    (gate : Gate inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) :
    maximalSelection (initial.snoc gate) choice omitted (Fin.last gates) = true ↔
      (gates ≠ omitted ∧ boundaryGate choice gates = false) ∧
        sourceAdmitted choice (maximalSelection initial choice omitted) gate.left = true ∧
        sourceAdmitted choice (maximalSelection initial choice omitted) gate.right = true := by
  rw [selection_last]
  by_cases eligible : gates ≠ omitted ∧ boundaryGate choice gates = false
  · rw [if_pos eligible, Bool.and_eq_true]
    exact ⟨fun both => ⟨eligible, both⟩, fun all => all.2⟩
  · rw [if_neg eligible]
    constructor
    · intro impossible
      cases impossible
    · intro all
      exact False.elim (eligible all.1)

private theorem sources_earlier (initial : Program inputs gates)
    (gate : Gate inputs gates) (index : Fin gates) :
    (initial.snoc gate).terminalGateSources index.castSucc =
      ((initial.terminalGateSources index).1.weakenGates 1,
        (initial.terminalGateSources index).2.weakenGates 1) := by
  change (if within : index.castSucc.val < gates then
    let pair := initial.terminalGateSources ⟨index.castSucc.val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rfl
  · rename_i outside
    exact False.elim (outside index.isLt)

private theorem sources_last (initial : Program inputs gates)
    (gate : Gate inputs gates) :
    (initial.snoc gate).terminalGateSources (Fin.last gates) =
      (gate.left.weakenGates 1, gate.right.weakenGates 1) := by
  change (if within : (Fin.last gates).val < gates then
    let pair := initial.terminalGateSources ⟨(Fin.last gates).val, within⟩
    (pair.1.weakenGates 1, pair.2.weakenGates 1)
    else (gate.left.weakenGates 1, gate.right.weakenGates 1)) = _
  split
  · rename_i impossible
    exact False.elim (Nat.lt_irrefl gates impossible)
  · rfl

private theorem admitted_weaken (choice : BoundaryChoice inputs total)
    (selected : Valuation (gates + 1)) (source : Source inputs gates) :
    sourceAdmitted choice selected (source.weakenGates 1) =
      sourceAdmitted choice (fun index => selected index.castSucc) source := by
  cases source with
  | input index => rfl
  | constant value => rfl
  | gate index => rfl

private theorem admitted_selection_snoc (initial : Program inputs gates)
    (gate : Gate inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) (source : Source inputs gates) :
    sourceAdmitted choice (maximalSelection (initial.snoc gate) choice omitted)
        (source.weakenGates 1) =
      sourceAdmitted choice (maximalSelection initial choice omitted) source := by
  rw [admitted_weaken]
  have prefixEq :
      (fun index : Fin gates =>
        maximalSelection (initial.snoc gate) choice omitted index.castSucc) =
      maximalSelection initial choice omitted :=
    funext (selection_earlier initial gate choice omitted)
  rw [prefixEq]

private theorem admitted_mono (choice : BoundaryChoice inputs total)
    (left right : Valuation gates)
    (included : ∀ index, left index = true → right index = true)
    (source : Source inputs gates) :
    sourceAdmitted choice left source = true →
      sourceAdmitted choice right source = true := by
  cases source with
  | input index => exact fun accepted => accepted
  | constant value => exact fun _ => rfl
  | gate index =>
      intro accepted
      simp only [sourceAdmitted, Bool.or_eq_true] at accepted ⊢
      rcases accepted with selected | boundary
      · exact Or.inl (included index selected)
      · exact Or.inr boundary

/-- Exact physical closure conditions for the chosen boundary and omitted gate. -/
def Admissible (program : Program inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) (selected : Valuation gates) : Prop :=
  (∀ index, selected index = true →
    index.val ≠ omitted ∧ boundaryGate choice index.val = false) ∧
  (∀ index, selected index = true →
    sourceAdmitted choice selected (program.terminalGateSources index).1 = true ∧
    sourceAdmitted choice selected (program.terminalGateSources index).2 = true)

/-- The computed scan is admissible without a supplied closure witness. -/
theorem maximalSelection_admissible (program : Program inputs gates)
    (choice : BoundaryChoice inputs total) (omitted : Nat) :
    Admissible program choice omitted (maximalSelection program choice omitted) := by
  induction program with
  | empty =>
      exact ⟨fun index => Fin.elim0 index, fun index => Fin.elim0 index⟩
  | @snoc gates initial gate ih =>
      constructor
      · intro index
        refine Fin.lastCases ?_ (fun earlier => ?_) index
        · intro checked
          exact ((selection_last_iff initial gate choice omitted).1 checked).1
        · intro checked
          rw [selection_earlier] at checked
          exact ih.1 earlier checked
      · intro index
        refine Fin.lastCases ?_ (fun earlier => ?_) index
        · intro checked
          have both := ((selection_last_iff initial gate choice omitted).1 checked).2
          simpa only [sources_last, admitted_selection_snoc] using both
        · intro checked
          rw [selection_earlier] at checked
          simpa only [sources_earlier, admitted_selection_snoc] using ih.2 earlier checked

private theorem admissible_prefix (initial : Program inputs gates)
    (gate : Gate inputs gates) (choice : BoundaryChoice inputs total)
    (omitted : Nat) (selected : Valuation (gates + 1))
    (lawful : Admissible (initial.snoc gate) choice omitted selected) :
    Admissible initial choice omitted (fun index => selected index.castSucc) := by
  constructor
  · intro index checked
    exact lawful.1 index.castSucc checked
  · intro index checked
    simpa only [sources_earlier, admitted_weaken] using lawful.2 index.castSucc checked

/-- Every physically admissible support is contained in the source-derived scan. -/
theorem maximalSelection_contains (program : Program inputs gates)
    (choice : BoundaryChoice inputs total) (omitted : Nat) :
    ∀ selected : Valuation gates, Admissible program choice omitted selected →
      ∀ index, selected index = true →
        maximalSelection program choice omitted index = true := by
  induction program with
  | empty =>
      intro _selected _lawful index
      exact Fin.elim0 index
  | @snoc gates initial gate ih =>
      intro selected lawful index
      let earlier : Valuation gates := fun prior => selected prior.castSucc
      have prefixLawful : Admissible initial choice omitted earlier :=
        admissible_prefix initial gate choice omitted selected lawful
      have included := ih earlier prefixLawful
      refine Fin.lastCases ?_ (fun prior => ?_) index
      · intro checked
        have both := lawful.2 (Fin.last gates) checked
        have left : sourceAdmitted choice earlier gate.left = true := by
          simpa only [sources_last, admitted_weaken] using both.1
        have right : sourceAdmitted choice earlier gate.right = true := by
          simpa only [sources_last, admitted_weaken] using both.2
        exact (selection_last_iff initial gate choice omitted).2
          ⟨lawful.1 (Fin.last gates) checked,
            admitted_mono choice earlier _ included gate.left left,
            admitted_mono choice earlier _ included gate.right right⟩
      · intro checked
        rw [selection_earlier]
        exact included prior checked

/-- Canonical gate records, with no caller-supplied metadata selecting extra gates. -/
def gateRecords (selected : Valuation gates) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  (terminalSelectedGateIndices selected).map TerminalPrimitiveRecord.gate

theorem gateRecords_selected_iff (selected : Valuation gates) (index : Fin gates) :
    terminalGateSelected
        (gateRecords (inputs := inputs) (outputs := outputs)
          (profileWidth := profileWidth) selected) index = true ↔ selected index = true := by
  rw [terminalGateSelected_eq_true_iff]
  constructor
  · intro member
    obtain ⟨found, foundMember, equal⟩ := List.mem_map.mp member
    have same : found = index := TerminalPrimitiveRecord.gate.inj equal
    subst found
    exact (mem_terminalSelectedGateIndices_iff selected index).1 foundMember
  · intro checked
    exact List.mem_map.mpr
      ⟨index, (mem_terminalSelectedGateIndices_iff selected index).2 checked, rfl⟩

private theorem bool_eq_of_true_iff {left right : Bool}
    (same : left = true ↔ right = true) : left = right := by
  cases left with
  | false =>
      cases right with
      | false => rfl
      | true => exact False.elim (Bool.noConfusion (same.2 rfl))
  | true =>
      cases right with
      | false => exact False.elim (Bool.noConfusion (same.1 rfl))
      | true => rfl

/-- Canonicalization preserves the exact selected-gate predicate. -/
theorem gateRecords_selected (selected : Valuation gates) :
    terminalGateSelected
        (gateRecords (inputs := inputs) (outputs := outputs)
          (profileWidth := profileWidth) selected) = selected :=
  funext fun index => bool_eq_of_true_iff (gateRecords_selected_iff selected index)


private theorem admitted_external_boundary
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (choice : BoundaryChoice inputs gates) (source : Source inputs gates)
    (wire : TerminalSupportWire inputs gates)
    (atWire : source.terminalSupportWire? = some wire)
    (external : terminalWireExternal records wire = true)
    (admitted : sourceAdmitted choice (terminalGateSelected records) source = true) :
    choice = some wire := by
  cases source with
  | constant value => cases atWire
  | input index =>
      have equal : wire = .input index := (Option.some.inj atWire).symm
      subst wire
      exact of_decide_eq_true admitted
  | gate index =>
      have equal : wire = .gate index := (Option.some.inj atWire).symm
      subst wire
      have unselected : terminalGateSelected records index = false :=
        (terminalWireExternal_eq_true_iff records (.gate index)).1 external
      change (terminalGateSelected records index || boundaryGate choice index.val) = true
        at admitted
      rw [unselected, Bool.false_or] at admitted
      cases choice with
      | none => cases admitted
      | some picked =>
          cases picked with
          | input other => cases admitted
          | gate other =>
              have equalValue : other.val = index.val := of_decide_eq_true admitted
              have equalIndex : other = index := Fin.ext equalValue
              cases equalIndex
              rfl

/-- Every actual incoming boundary wire is the selected optional boundary. -/
theorem admissible_boundary
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (choice : BoundaryChoice inputs gates) (omitted : Nat)
    (lawful : Admissible program choice omitted (terminalGateSelected records))
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts program records) :
    choice = some wire := by
  have checked := (mem_terminalBoundaryPorts_iff program records wire).1 member
  obtain ⟨external, consumer, _enumerated, selected, used⟩ :=
    (terminalBoundaryWire_eq_true_iff program records wire).1 checked
  have admitted := lawful.2 consumer selected
  change (decide ((program.terminalGateSources consumer).1.terminalSupportWire? = some wire) ||
    decide ((program.terminalGateSources consumer).2.terminalSupportWire? = some wire)) = true
    at used
  simp only [Bool.or_eq_true] at used
  rcases used with left | right
  · exact admitted_external_boundary records choice _ wire
      (of_decide_eq_true left) external admitted.1
  · exact admitted_external_boundary records choice _ wire
      (of_decide_eq_true right) external admitted.2

/-- The physical boundary has no duplicate ports and contains at most one wire. -/
theorem admissible_boundary_small
    (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (choice : BoundaryChoice inputs gates) (omitted : Nat)
    (lawful : Admissible program choice omitted (terminalGateSelected records)) :
    (terminalBoundaryPorts program records).length ≤ 1 := by
  have distinct : (terminalBoundaryPorts program records).Nodup :=
    terminalBoundaryPorts_nodup program records
  cases boundaryAt : terminalBoundaryPorts program records with
  | nil => exact Nat.zero_le 1
  | cons head tail =>
      cases tail with
      | nil => exact Nat.le_refl 1
      | cons next rest =>
          have first : head ∈ terminalBoundaryPorts program records := by
            rw [boundaryAt]
            exact List.mem_cons_self
          have second : next ∈ terminalBoundaryPorts program records := by
            rw [boundaryAt]
            exact List.mem_cons_of_mem head List.mem_cons_self
          have equal : head = next := Option.some.inj
            ((admissible_boundary program records choice omitted lawful head first).symm.trans
              (admissible_boundary program records choice omitted lawful next second))
          subst next
          rw [boundaryAt] at distinct
          exact False.elim ((List.nodup_cons.mp distinct).1 List.mem_cons_self)

/-- One canonical maximal support, constructed entirely from the actual program. -/
def candidateRecords (program : Program inputs gates) (choice : BoundaryChoice inputs gates)
    (omitted : Fin gates) :
    List (TerminalPrimitiveRecord inputs gates outputs profileWidth) :=
  gateRecords (maximalSelection program choice omitted.val)

/-- Every generated maximal candidate is recognized by the zero/unary rule. -/
theorem candidateRecords_boundary (program : Program inputs gates)
    (choice : BoundaryChoice inputs gates) (omitted : Fin gates) :
    (terminalBoundaryPorts program
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth)
        program choice omitted)).length ≤ 1 := by
  apply admissible_boundary_small program _ choice omitted.val
  simpa only [candidateRecords, gateRecords_selected] using
    maximalSelection_admissible program choice omitted.val

/-- The explicitly omitted gate remains in the actual physical exterior. -/
theorem candidateRecords_proper (program : Program inputs gates)
    (choice : BoundaryChoice inputs gates) (omitted : Fin gates) :
    0 < (ArbitrarySupportSplice.exterior
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth)
        program choice omitted)).length := by
  have omittedFalse : maximalSelection program choice omitted.val omitted = false := by
    cases atOmitted : maximalSelection program choice omitted.val omitted with
    | false => rfl
    | true =>
        have impossible :=
          (maximalSelection_admissible program choice omitted.val).1 omitted atOmitted
        exact False.elim (impossible.1 rfl)
  have outside : omitted ∈ ArbitrarySupportSplice.exterior
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth)
        program choice omitted) := by
    apply (ArbitrarySupportSplice.mem_exterior_iff _ omitted).2
    simpa only [candidateRecords, gateRecords_selected] using omittedFalse
  cases exteriorAt : ArbitrarySupportSplice.exterior
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth)
        program choice omitted) with
  | nil =>
      rw [exteriorAt] at outside
      exact False.elim (List.not_mem_nil outside)
  | cons head tail => exact Nat.zero_lt_succ tail.length


/-- Only the physical wire actually named by a source; constants name none. -/
def sourceWires : Source inputs gates → List (TerminalSupportWire inputs gates)
  | .constant _ => []
  | .input index => [.input index]
  | .gate index => [.gate index]

private theorem mem_sourceWires_iff (source : Source inputs gates)
    (wire : TerminalSupportWire inputs gates) :
    wire ∈ sourceWires source ↔ source.terminalSupportWire? = some wire := by
  cases source with
  | constant value =>
      constructor
      · intro impossible
        exact False.elim (List.not_mem_nil impossible)
      · intro impossible
        cases impossible
  | input index =>
      constructor
      · intro member
        have equal : wire = .input index := List.mem_singleton.mp member
        cases equal
        rfl
      · intro atWire
        have equal : TerminalSupportWire.input index = wire := Option.some.inj atWire
        cases equal
        exact List.mem_cons_self
  | gate index =>
      constructor
      · intro member
        have equal : wire = .gate index := List.mem_singleton.mp member
        cases equal
        rfl
      · intro atWire
        have equal : TerminalSupportWire.gate index = wire := Option.some.inj atWire
        cases equal
        exact List.mem_cons_self

private theorem sourceWires_length (source : Source inputs gates) :
    (sourceWires source).length ≤ 1 := by
  cases source with
  | constant value => exact Nat.zero_le 1
  | input index => exact Nat.le_refl 1
  | gate index => exact Nat.le_refl 1

private theorem flatMap_length_le {α β : Type} (items : List α)
    (f : α → List β) (bound : Nat)
    (each : ∀ item, item ∈ items → (f item).length ≤ bound) :
    (items.flatMap f).length ≤ items.length * bound := by
  induction items with
  | nil =>
      simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul, Nat.le_refl]
  | cons head tail ih =>
      have first := each head List.mem_cons_self
      have rest := ih (fun item member => each item (List.mem_cons_of_mem head member))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      exact Nat.le_trans (Nat.add_le_add first rest) (Nat.le_of_eq (Nat.add_comm _ _))

/-- Enumerate consumed wires, not all declared inputs or all physical subsets. -/
def consumedWires (program : Program inputs gates) :
    List (TerminalSupportWire inputs gates) :=
  (allFin gates).flatMap fun consumer =>
    sourceWires (program.terminalGateSources consumer).1 ++
      sourceWires (program.terminalGateSources consumer).2

/-- There are at most two consumed physical source occurrences per gate. -/
theorem consumedWires_length (program : Program inputs gates) :
    (consumedWires program).length ≤ 2 * gates := by
  have bound := flatMap_length_le (allFin gates)
    (fun consumer =>
      sourceWires (program.terminalGateSources consumer).1 ++
        sourceWires (program.terminalGateSources consumer).2) 2
    (fun consumer _member => by
      rw [List.length_append]
      exact Nat.add_le_add (sourceWires_length _) (sourceWires_length _))
  simpa only [consumedWires, allFin_length, Nat.mul_comm] using bound

/-- Every actual support boundary wire occurs in the source-derived list. -/
theorem boundary_mem_consumedWires (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts program records) :
    wire ∈ consumedWires program := by
  have checked := (mem_terminalBoundaryPorts_iff program records wire).1 member
  obtain ⟨_external, consumer, enumerated, _selected, used⟩ :=
    (terminalBoundaryWire_eq_true_iff program records wire).1 checked
  change wire ∈ (allFin gates).flatMap _
  apply List.mem_flatMap.mpr
  refine ⟨consumer, enumerated, ?_⟩
  change (decide ((program.terminalGateSources consumer).1.terminalSupportWire? = some wire) ||
    decide ((program.terminalGateSources consumer).2.terminalSupportWire? = some wire)) = true
    at used
  simp only [Bool.or_eq_true] at used
  rcases used with left | right
  · exact List.mem_append_left _
      ((mem_sourceWires_iff _ wire).2 (of_decide_eq_true left))
  · exact List.mem_append_right _
      ((mem_sourceWires_iff _ wire).2 (of_decide_eq_true right))

/-- All relevant optional boundaries, allowing harmless repeated occurrences. -/
def boundaryChoices (program : Program inputs gates) :
    List (BoundaryChoice inputs gates) :=
  none :: (consumedWires program).map Option.some

theorem boundaryChoices_length (program : Program inputs gates) :
    (boundaryChoices program).length ≤ 2 * gates + 1 := by
  simpa only [boundaryChoices, List.length_cons, List.length_map] using
    Nat.add_le_add_right (consumedWires_length program) 1

/-- Computed maximal supports and all singleton supports; no supplied family. -/
def candidateFamily (program : Program inputs gates) :
    List (List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :=
  (boundaryChoices program).flatMap
      (fun choice => (allFin gates).map (candidateRecords program choice)) ++
    (allFin gates).map (fun index => [TerminalPrimitiveRecord.gate index])

/-- A physical candidate-count bound, not a complete encoded runtime theorem. -/
theorem candidateFamily_length (program : Program inputs gates) :
    (candidateFamily (outputs := outputs) (profileWidth := profileWidth) program).length ≤
      (2 * gates + 1) * gates + gates := by
  have bounded := flatMap_length_le (boundaryChoices program)
    (fun choice => (allFin gates).map
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth) program choice))
    gates (fun _choice _member => by
      rw [List.length_map, allFin_length]
      exact Nat.le_refl gates)
  change ((_ : List (List (TerminalPrimitiveRecord inputs gates outputs profileWidth))) ++
    (allFin gates).map (fun index => [TerminalPrimitiveRecord.gate index])).length ≤ _
  rw [List.length_append, List.length_map, allFin_length]
  exact Nat.le_trans (Nat.add_le_add_right bounded gates)
    (Nat.add_le_add_right
      (Nat.mul_le_mul_right gates (boundaryChoices_length program)) gates)

theorem candidateFamily_maximal_mem (program : Program inputs gates)
    (choice : BoundaryChoice inputs gates) (chosen : choice ∈ boundaryChoices program)
    (omitted : Fin gates) :
    candidateRecords (outputs := outputs) (profileWidth := profileWidth)
      program choice omitted ∈ candidateFamily program :=
  List.mem_append_left _
    (List.mem_flatMap.mpr
      ⟨choice, chosen, List.mem_map.mpr ⟨omitted, mem_allFin omitted, rfl⟩⟩)

theorem candidateFamily_singleton_mem (program : Program inputs gates) (index : Fin gates) :
    [TerminalPrimitiveRecord.gate index] ∈
      candidateFamily (outputs := outputs) (profileWidth := profileWidth) program :=
  List.mem_append_right _
    (List.mem_map.mpr ⟨index, mem_allFin index, rfl⟩)


/-- Choose the actual sole boundary when it exists; never invent a free input. -/
def supportChoice (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    BoundaryChoice inputs gates :=
  (terminalBoundaryPorts program records).head?

theorem supportChoice_wire_mem (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (chosen : supportChoice program records = some wire) :
    wire ∈ terminalBoundaryPorts program records := by
  unfold supportChoice at chosen
  cases boundaryAt : terminalBoundaryPorts program records with
  | nil =>
      rw [boundaryAt] at chosen
      cases chosen
  | cons head tail =>
      rw [boundaryAt] at chosen
      have equal : head = wire := Option.some.inj chosen
      cases equal
      exact List.mem_cons_self

theorem supportChoice_of_mem (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (small : (terminalBoundaryPorts program records).length ≤ 1)
    (wire : TerminalSupportWire inputs gates)
    (member : wire ∈ terminalBoundaryPorts program records) :
    supportChoice program records = some wire := by
  unfold supportChoice
  cases boundaryAt : terminalBoundaryPorts program records with
  | nil =>
      rw [boundaryAt] at member
      exact False.elim (List.not_mem_nil member)
  | cons head tail =>
      cases tail with
      | nil =>
          rw [boundaryAt] at member
          have equal : wire = head := List.mem_singleton.mp member
          cases equal
          rfl
      | cons next rest =>
          rw [boundaryAt] at small
          simp only [List.length_cons] at small
          omega

/-- Every actual chosen boundary is external to the same selected support. -/
theorem supportChoice_external (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (chosen : supportChoice program records = some wire) :
    terminalWireExternal records wire = true := by
  have member := supportChoice_wire_mem program records wire chosen
  exact ((terminalBoundaryWire_eq_true_iff program records wire).1
    ((mem_terminalBoundaryPorts_iff program records wire).1 member)).1

/-- The needed choice occurs in the bounded source-derived boundary list. -/
theorem supportChoice_mem (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    supportChoice program records ∈ boundaryChoices program := by
  unfold supportChoice
  cases boundaryAt : terminalBoundaryPorts program records with
  | nil => exact List.mem_cons_self
  | cons head tail =>
      apply List.mem_cons_of_mem none
      apply List.mem_map.mpr
      refine ⟨head, ?_, rfl⟩
      apply boundary_mem_consumedWires program records head
      rw [boundaryAt]
      exact List.mem_cons_self

private theorem selected_not_boundaryGate
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (choice : BoundaryChoice inputs gates)
    (external : ∀ wire, choice = some wire → terminalWireExternal records wire = true)
    (index : Fin gates) (selected : terminalGateSelected records index = true) :
    boundaryGate choice index.val = false := by
  cases choice with
  | none => rfl
  | some wire =>
      cases wire with
      | input inputIndex => rfl
      | gate boundary =>
          cases picked : boundaryGate (some (.gate boundary)) index.val with
          | false => rfl
          | true =>
              have equalValue : boundary.val = index.val := of_decide_eq_true picked
              have equal : boundary = index := Fin.ext equalValue
              subst boundary
              have unselected : terminalGateSelected records index = false :=
                (terminalWireExternal_eq_true_iff records (.gate index)).1
                  (external (.gate index) rfl)
              rw [selected] at unselected
              cases unselected

private theorem admitted_of_accounted (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (choice : BoundaryChoice inputs gates)
    (covers : ∀ wire, wire ∈ terminalBoundaryPorts candidate.program records →
      choice = some wire)
    (source : Source inputs gates)
    (accounted : (completeTerminalPhysicalSupport candidate records).SourceAccounted source) :
    sourceAdmitted choice (terminalGateSelected records) source = true := by
  cases source with
  | constant value => rfl
  | input index => exact decide_eq_true (covers (.input index) accounted)
  | gate index =>
      change terminalGateSelected records index = true ∨
        .gate index ∈ terminalBoundaryPorts candidate.program records at accounted
      change (terminalGateSelected records index || boundaryGate choice index.val) = true
      rw [Bool.or_eq_true]
      rcases accounted with selected | incoming
      · exact Or.inl selected
      · apply Or.inr
        rw [covers (.gate index) incoming]
        exact decide_eq_true rfl

/-- Every arbitrary zero/unary support is admissible for its actual boundary. -/
theorem support_admissible (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (small : (terminalBoundaryPorts candidate.program records).length ≤ 1)
    (omitted : Fin gates) (outside : terminalGateSelected records omitted = false) :
    Admissible candidate.program (supportChoice candidate.program records) omitted.val
      (terminalGateSelected records) := by
  constructor
  · intro index selected
    constructor
    · intro equalValue
      have equal : index = omitted := Fin.ext equalValue
      cases equal
      rw [outside] at selected
      cases selected
    · exact selected_not_boundaryGate records _
        (supportChoice_external candidate.program records) index selected
  · intro consumer selected
    have both := completeTerminalPhysicalSupport_incoming_complete
      candidate records consumer selected
    exact ⟨admitted_of_accounted candidate records _
        (supportChoice_of_mem candidate.program records small) _ both.1,
      admitted_of_accounted candidate records _
        (supportChoice_of_mem candidate.program records small) _ both.2⟩

/-- The relevant maximal family entry contains every gate of the original support. -/
theorem support_contained_in_candidate (candidate : Candidate inputs gates outputs)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (small : (terminalBoundaryPorts candidate.program records).length ≤ 1)
    (omitted : Fin gates) (outside : terminalGateSelected records omitted = false)
    (index : Fin gates) (selected : terminalGateSelected records index = true) :
    terminalGateSelected
      (candidateRecords (outputs := outputs) (profileWidth := profileWidth)
        candidate.program (supportChoice candidate.program records) omitted) index = true := by
  simpa only [candidateRecords, gateRecords_selected] using
    maximalSelection_contains candidate.program (supportChoice candidate.program records)
      omitted.val (terminalGateSelected records)
      (support_admissible candidate records small omitted outside) index selected


private theorem selected_length_succ (selected : Valuation (gates + 1)) :
    (terminalSelectedGateIndices selected).length =
      (terminalSelectedGateIndices (fun index : Fin gates => selected index.castSucc)).length +
        (if selected (Fin.last gates) then 1 else 0) := by
  change (if selected (Fin.last gates) then
      (terminalSelectedGateIndices (fun index : Fin gates => selected index.castSucc)).map
        Fin.castSucc ++ [Fin.last gates]
    else (terminalSelectedGateIndices (fun index : Fin gates => selected index.castSucc)).map
        Fin.castSucc).length = _
  by_cases checked : selected (Fin.last gates) = true
  · simp only [if_pos checked, List.length_append, List.length_map,
      List.length_cons, List.length_nil]
  · simp only [if_neg checked, List.length_map, Nat.add_zero]

/-- Physical inclusion implies an inequality of actual selected-gate counts. -/
theorem selected_length_mono (left right : Valuation gates)
    (included : ∀ index, left index = true → right index = true) :
    (terminalSelectedGateIndices left).length ≤
      (terminalSelectedGateIndices right).length := by
  induction gates with
  | zero => exact Nat.le_refl 0
  | succ gates ih =>
      rw [selected_length_succ left, selected_length_succ right]
      have earlier := ih (fun index => left index.castSucc) (fun index => right index.castSucc)
        (fun index checked => included index.castSucc checked)
      apply Nat.add_le_add earlier
      by_cases checked : left (Fin.last gates) = true
      · rw [if_pos checked, if_pos (included (Fin.last gates) checked)]
        exact Nat.le_refl 1
      · rw [if_neg checked]
        exact Nat.zero_le _

theorem selected_length_le (selected : Valuation gates) :
    (terminalSelectedGateIndices selected).length ≤ gates := by
  induction gates with
  | zero => exact Nat.le_refl 0
  | succ gates ih =>
      rw [selected_length_succ selected]
      have earlier := ih (fun index => selected index.castSucc)
      by_cases checked : selected (Fin.last gates) = true
      · rw [if_pos checked]
        exact Nat.add_le_add_right earlier 1
      · rw [if_neg checked, Nat.add_zero]
        exact Nat.le_trans earlier (Nat.le_succ gates)

/-- Each computed support entry contains at most one record per original gate. -/
theorem candidateFamily_entry_length (program : Program inputs gates)
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (member : records ∈ candidateFamily program) :
    records.length ≤ gates := by
  rcases List.mem_append.mp member with maximal | singleton
  · obtain ⟨choice, _chosen, found⟩ := List.mem_flatMap.mp maximal
    obtain ⟨omitted, _enumerated, equal⟩ := List.mem_map.mp found
    cases equal
    simpa only [candidateRecords, gateRecords, List.length_map] using
      selected_length_le (maximalSelection program choice omitted.val)
  · obtain ⟨index, _enumerated, equal⟩ := List.mem_map.mp singleton
    cases equal
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le index.val) index.isLt)

/-- Count monotonicity concerns actual physical extraction, not record multiplicity. -/
theorem extracted_gateCount_mono (candidate : Candidate inputs gates outputs)
    (left right : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (included : ∀ index, terminalGateSelected left index = true →
      terminalGateSelected right index = true) :
    (extractTerminalSupport candidate left).gateCount ≤
      (extractTerminalSupport candidate right).gateCount := by
  rw [extractTerminalSupport_gateCount, extractTerminalSupport_gateCount]
  exact selected_length_mono (terminalGateSelected left) (terminalGateSelected right) included


/-- One selected physical gate has a canonical singleton with the same selection. -/
theorem singleton_selection
    (records : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (one : (terminalSelectedGates records).length = 1) :
    ∃ picked : Fin gates,
      terminalGateSelected
        ([.gate picked] : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) =
      terminalGateSelected records := by
  cases selectedAt : terminalSelectedGates records with
  | nil =>
      rw [selectedAt] at one
      cases one
  | cons head tail =>
      cases tail with
      | nil =>
          refine ⟨head, ?_⟩
          have canonical := gateRecords_selected (inputs := inputs) (outputs := outputs)
            (profileWidth := profileWidth) (terminalGateSelected records)
          change terminalGateSelected
            ((terminalSelectedGates records).map TerminalPrimitiveRecord.gate) =
              terminalGateSelected records at canonical
          rw [selectedAt] at canonical
          exact canonical
      | cons next rest =>
          rw [selectedAt] at one
          have impossible : Nat.succ rest.length = 0 := Nat.succ.inj one
          exact False.elim (Nat.noConfusion impossible)

variable {fields : Nat}

/-- Actual gain acceptance is invariant under duplicate or metadata record changes
    that preserve selection. The complete open function and frontier are retained. -/
theorem checkedGain_selection_invariant (carrier : WireCarrier inputs outputs fields)
    (left right : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (sameSelection : terminalGateSelected left = terminalGateSelected right)
    (accepted : (WireUnaryArbitrarySupport.checkedProperGain carrier left).isSome = true) :
    (WireUnaryArbitrarySupport.checkedProperGain carrier right).isSome = true := by
  obtain ⟨small, proper, smaller⟩ :=
    (WireUnaryArbitrarySupport.checkedProperGain_isSome_iff carrier left).1 accepted
  let property (support : TerminalExtractedSupport (profileWidth := 0)
      carrier.exposed.candidate) : Prop :=
    ∃ small : support.boundary.length ≤ 1,
      support.gateCount < carrier.implementation.gateCount ∧
        (WireUnaryFrontier.localWord support.extractedCandidate.toImplementation small).gateCount <
          support.gateCount
  have leftProperty : property (WireUnaryArbitrarySupport.pulled carrier left) :=
    ⟨small, (WireUnaryArbitrarySupport.proper_iff_exterior_positive carrier left).2 proper,
      smaller⟩
  have equal := extractTerminalSupport_eq_of_gateSelected_eq
    carrier.exposed.candidate left right sameSelection
  have rightProperty : property (WireUnaryArbitrarySupport.pulled carrier right) := by
    change property (extractTerminalSupport carrier.exposed.candidate right)
    rw [← equal]
    exact leftProperty
  obtain ⟨rightSmall, rightProper, rightSmaller⟩ := rightProperty
  exact (WireUnaryArbitrarySupport.checkedProperGain_isSome_iff carrier right).2
    ⟨rightSmall, (WireUnaryArbitrarySupport.proper_iff_exterior_positive carrier right).1
      rightProper, rightSmaller⟩


/-- Any actual proper zero/unary gain has an accepted representative in the
    computed family, including the one-gate case and arbitrary repeated records. -/
theorem candidateFamily_complete (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (accepted : (WireUnaryArbitrarySupport.checkedProperGain carrier records).isSome = true) :
    ∃ generated : List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0),
      generated ∈ candidateFamily carrier.exposed.candidate.program ∧
        (WireUnaryArbitrarySupport.checkedProperGain carrier generated).isSome = true := by
  obtain ⟨small, proper, smaller⟩ :=
    (WireUnaryArbitrarySupport.checkedProperGain_isSome_iff carrier records).1 accepted
  have positive : 0 < (WireUnaryArbitrarySupport.pulled carrier records).gateCount :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) smaller
  by_cases one : (WireUnaryArbitrarySupport.pulled carrier records).gateCount = 1
  · have oneSelected : (terminalSelectedGates records).length = 1 :=
      (WireUnaryArbitrarySupport.pulled carrier records).gateCount_eq_selected.symm.trans one
    obtain ⟨picked, sameSelection⟩ := singleton_selection records oneSelected
    exact ⟨[.gate picked], candidateFamily_singleton_mem carrier.exposed.candidate.program picked,
      checkedGain_selection_invariant carrier records [.gate picked] sameSelection.symm accepted⟩
  · have atLeastTwo : 1 < (WireUnaryArbitrarySupport.pulled carrier records).gateCount := by
      omega
    have exteriorPositive : 0 < (ArbitrarySupportSplice.exterior records).length := proper
    obtain ⟨omitted, exteriorMember⟩ :=
      List.length_pos_iff_exists_mem.mp exteriorPositive
    have outside : terminalGateSelected records omitted = false :=
      (ArbitrarySupportSplice.mem_exterior_iff records omitted).1 exteriorMember
    let choice := supportChoice carrier.exposed.candidate.program records
    let generated : List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0) :=
      candidateRecords carrier.exposed.candidate.program choice omitted
    have generatedSmall :
        (WireUnaryArbitrarySupport.pulled carrier generated).boundary.length ≤ 1 :=
      candidateRecords_boundary carrier.exposed.candidate.program choice omitted
    have generatedProper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier generated :=
      candidateRecords_proper carrier.exposed.candidate.program choice omitted
    have included : ∀ index, terminalGateSelected records index = true →
        terminalGateSelected generated index = true :=
      support_contained_in_candidate carrier.exposed.candidate records small omitted outside
    have countLe : (WireUnaryArbitrarySupport.pulled carrier records).gateCount ≤
        (WireUnaryArbitrarySupport.pulled carrier generated).gateCount :=
      extracted_gateCount_mono carrier.exposed.candidate records generated included
    have generatedSaving :
        (WireUnaryArbitrarySupport.replacement carrier generated generatedSmall).gateCount <
          (WireUnaryArbitrarySupport.pulled carrier generated).gateCount :=
      Nat.lt_of_le_of_lt
        (WireUnaryArbitrarySupport.replacement_gate_bound carrier generated generatedSmall)
        (Nat.lt_of_lt_of_le atLeastTwo countLe)
    exact ⟨generated,
      candidateFamily_maximal_mem carrier.exposed.candidate.program choice
        (supportChoice_mem carrier.exposed.candidate.program records) omitted,
      (WireUnaryArbitrarySupport.checkedProperGain_isSome_iff carrier generated).2
        ⟨generatedSmall, generatedProper, generatedSaving⟩⟩

/-- An actual support returned with the computed zero/unary strict-gain witness. -/
structure GainResult (carrier : WireCarrier inputs outputs fields) where
  records : List (TerminalPrimitiveRecord inputs
    carrier.implementation.gateCount (outputs + fields) 0)
  gain : WireUnaryArbitrarySupport.ProperGain carrier records

private def firstGain (carrier : WireCarrier inputs outputs fields) :
    List (List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0)) → Option (GainResult carrier)
  | [] => none
  | records :: rest =>
      match WireUnaryArbitrarySupport.checkedProperGain carrier records with
      | some gain => some ⟨records, gain⟩
      | none => firstGain carrier rest

private theorem firstGain_complete (carrier : WireCarrier inputs outputs fields) :
    ∀ (family : List (List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0)))
      (records : List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0)),
      records ∈ family →
      (WireUnaryArbitrarySupport.checkedProperGain carrier records).isSome = true →
      (firstGain carrier family).isSome = true := by
  intro family
  induction family with
  | nil =>
      intro records member
      exact False.elim (List.not_mem_nil member)
  | cons head tail ih =>
      intro records member accepted
      change (match WireUnaryArbitrarySupport.checkedProperGain carrier head with
        | some gain => some (GainResult.mk head gain)
        | none => firstGain carrier tail).isSome = true
      cases checkedAt : WireUnaryArbitrarySupport.checkedProperGain carrier head with
      | none =>
          have different : records ≠ head := by
            intro equal
            subst records
            rw [checkedAt] at accepted
            cases accepted
          have inTail := (List.mem_cons.mp member).resolve_left different
          exact ih records inTail accepted
      | some gain => rfl

private theorem firstGain_member (carrier : WireCarrier inputs outputs fields) :
    ∀ (family : List (List (TerminalPrimitiveRecord inputs
        carrier.implementation.gateCount (outputs + fields) 0)))
      (result : GainResult carrier),
      firstGain carrier family = some result → result.records ∈ family := by
  intro family
  induction family with
  | nil =>
      intro result impossible
      cases impossible
  | cons head tail ih =>
      intro result found
      change (match WireUnaryArbitrarySupport.checkedProperGain carrier head with
        | some gain => some (GainResult.mk head gain)
        | none => firstGain carrier tail) = some result at found
      cases checkedAt : WireUnaryArbitrarySupport.checkedProperGain carrier head with
      | none =>
          rw [checkedAt] at found
          exact List.mem_cons_of_mem head (ih result found)
      | some gain =>
          rw [checkedAt] at found
          have equal : GainResult.mk head gain = result := Option.some.inj found
          cases equal
          exact List.mem_cons_self

/-- Search only the bounded family computed from the original carrier. -/
def findGain (carrier : WireCarrier inputs outputs fields) : Option (GainResult carrier) :=
  firstGain carrier (candidateFamily carrier.exposed.candidate.program)

/-- Construct the actual expanded carrier from the computed support and witness. -/
def GainResult.expanded {carrier : WireCarrier inputs outputs fields}
    (result : GainResult carrier) : WireCarrier inputs outputs fields :=
  WireUnaryArbitrarySupport.expanded carrier result.records result.gain.small

/-- Optional executable replacement, with no supplied support or agreement. -/
def findReplacement (carrier : WireCarrier inputs outputs fields) :
    Option (WireCarrier inputs outputs fields) :=
  (findGain carrier).map GainResult.expanded

/-- Full completeness for every proper zero/unary support admitting any strictly
    smaller equivalent complete local word. The comparison word is not a search input. -/
theorem findGain_complete (carrier : WireCarrier inputs outputs fields)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (proper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier records)
    (other : Implementation (WireUnaryArbitrarySupport.pulled carrier records).boundary.length
      (WireUnaryArbitrarySupport.pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics)
    (smaller : other.gateCount < (WireUnaryArbitrarySupport.pulled carrier records).gateCount) :
    (findGain carrier).isSome = true := by
  have accepted := WireUnaryArbitrarySupport.checkedProperGain_complete
    carrier records small proper other sameOpen smaller
  obtain ⟨generated, member, checked⟩ := candidateFamily_complete carrier records accepted
  exact firstGain_complete carrier _ generated member checked

theorem findGain_member (carrier : WireCarrier inputs outputs fields)
    (result : GainResult carrier) (found : findGain carrier = some result) :
    result.records ∈ candidateFamily carrier.exposed.candidate.program :=
  firstGain_member carrier _ result found

theorem findGain_records_bound (carrier : WireCarrier inputs outputs fields)
    (result : GainResult carrier) (found : findGain carrier = some result) :
    result.records.length ≤ carrier.implementation.gateCount :=
  candidateFamily_entry_length carrier.exposed.candidate.program result.records
    (findGain_member carrier result found)

/-- Acceptance preserves every output and field, with a strict fully paid saving. -/
theorem GainResult.checked {carrier : WireCarrier inputs outputs fields}
    (result : GainResult carrier) :
    (WireUnaryArbitrarySupport.pulled carrier result.records).boundary.length ≤ 1 ∧
      (WireUnaryArbitrarySupport.pulled carrier result.records).gateCount <
        carrier.implementation.gateCount ∧
      StrictEquivalentGain carrier.implementation result.expanded.implementation ∧
      (∀ valuation field, result.expanded.fieldValue valuation field =
        carrier.fieldValue valuation field) ∧
      result.expanded.implementation.gateCount =
        (WireUnaryArbitrarySupport.replacement carrier result.records result.gain.small).gateCount +
          WireUnaryArbitrarySupport.exteriorCharge carrier result.records :=
  ⟨result.gain.small, result.gain.checked⟩

/-- A negative result excludes every proper zero/unary local gain in this scope.
    It is not a global minimum or an unconditional ZeroSlack theorem. -/
theorem findGain_none_excludes (carrier : WireCarrier inputs outputs fields)
    (notFound : findGain carrier = none)
    (records : List (TerminalPrimitiveRecord inputs
      carrier.implementation.gateCount (outputs + fields) 0))
    (small : (WireUnaryArbitrarySupport.pulled carrier records).boundary.length ≤ 1)
    (proper : 0 < WireUnaryArbitrarySupport.exteriorCharge carrier records)
    (other : Implementation (WireUnaryArbitrarySupport.pulled carrier records).boundary.length
      (WireUnaryArbitrarySupport.pulled carrier records).interface.length)
    (sameOpen : other.candidate.semantics =
      (WireUnaryArbitrarySupport.pulled carrier records).extractedCandidate.semantics) :
    (WireUnaryArbitrarySupport.pulled carrier records).gateCount ≤ other.gateCount := by
  by_cases smaller : other.gateCount < (WireUnaryArbitrarySupport.pulled carrier records).gateCount
  · have accepted := findGain_complete carrier records small proper other sameOpen smaller
    rw [notFound] at accepted
    cases accepted
  · omega


/-- A found support provides the same source-exact R7 discharge as the checked
    arbitrary-support compiler, now without supplying that support to the search. -/
def GainResult.dischargeR7 {carrier : WireCarrier inputs outputs fields}
    (result : GainResult carrier) (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    WireUnaryArbitrarySupport.ExpandedDischarge carrier result.records result.gain.small
      keep creation :=
  WireUnaryArbitrarySupport.dischargeR7 carrier result.records result.gain.small keep creation

theorem GainResult.dischargeR7_source_exact {carrier : WireCarrier inputs outputs fields}
    (result : GainResult carrier) (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep) :
    (result.dischargeR7 keep creation).actualSource =
      result.expanded.source creation.coordinate := rfl

theorem GainResult.dischargeR7_full_value {carrier : WireCarrier inputs outputs fields}
    (result : GainResult carrier) (keep : Fin fields → Bool)
    (creation : WireObligationRestoration.R5Creation carrier keep)
    (valuation : Valuation inputs) :
    (result.dischargeR7 keep creation).actualSource.eval valuation
        (result.expanded.implementation.candidate.program.eval valuation) =
      carrier.fieldValue valuation creation.coordinate :=
  WireUnaryArbitrarySupport.dischargeR7_full_value
    carrier result.records result.gain.small keep creation valuation

/-- Constructing the expanded carrier neither loses nor invents a search success. -/
theorem findReplacement_isSome (carrier : WireCarrier inputs outputs fields) :
    (findReplacement carrier).isSome = (findGain carrier).isSome := by
  unfold findReplacement
  cases findGain carrier <;> rfl

/-- The optional public replacement preserves all computational fields and gives
    a strictly smaller complete ordinary-output implementation. -/
theorem findReplacement_sound (carrier : WireCarrier inputs outputs fields)
    (replacement : WireCarrier inputs outputs fields)
    (found : findReplacement carrier = some replacement) :
    StrictEquivalentGain carrier.implementation replacement.implementation ∧
      (∀ valuation field, replacement.fieldValue valuation field =
        carrier.fieldValue valuation field) := by
  unfold findReplacement at found
  cases gainAt : findGain carrier with
  | none =>
      rw [gainAt] at found
      cases found
  | some result =>
      rw [gainAt] at found
      have equal : result.expanded = replacement := Option.some.inj found
      cases equal
      exact ⟨result.gain.strictGain,
        WireUnaryArbitrarySupport.expanded_field carrier result.records result.gain.small⟩

end PNP.DirectWire.WireUnarySupportSearch
