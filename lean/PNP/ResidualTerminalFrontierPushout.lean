/-
Copyright (c) 2026 PNP Labs.

Exact governed-frontier gluing for finite saturated terminal support squares.
The left and right completed supports determine one canonical physical and
profile frontier.  Incoming wires and outgoing gates survive precisely when
they remain external after the two record sets are combined; profile
coordinates are glued by their shared ambient coordinate and terminal role.

This reconstructs the frontier-pushout condition in Section 3 of the pinned
manuscript.  The operation below never reads the join frontier.  The join is
used only on the theorem side, where Lean proves that its independently
computed governed frontier equals the gluing.  The terminal dependency system
remains explicit data.  No obstruction routing, projection commutation,
square legitimacy, side-tight minima, SaturatePositive, BCELReady, ZeroSlack,
PCCMin, polynomial-runtime, or P = NP claim is made.
-/

import PNP.ResidualTerminalGovernedSupportCompletion

namespace PNP
namespace DirectWire

/-- A side-frontier item either survives on the glued exterior or becomes an
    internal wire of the combined support. -/
inductive TerminalFrontierDisposition where
  | retained
  | internalized
  deriving Repr, DecidableEq

private theorem nodup_of_listNoDuplicates {alpha : Type}
    {items : List alpha} (distinct : ListNoDuplicates items) :
    items.Nodup := by
  induction distinct with
  | nil => exact List.nodup_nil
  | cons headAbsent _tailDistinct ih =>
      exact List.nodup_cons.mpr ⟨headAbsent, ih⟩

private theorem nodup_map_injective {alpha beta : Type}
    (mapping : alpha → beta) (injective : Function.Injective mapping)
    {items : List alpha} (distinct : items.Nodup) :
    (items.map mapping).Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
      have split := List.nodup_cons.mp distinct
      apply List.nodup_cons.mpr
      constructor
      · intro member
        obtain ⟨item, itemMember, equal⟩ := List.mem_map.mp member
        exact split.1 (injective equal.symm ▸ itemMember)
      · exact ih split.2

/-- The canonical physical-wire enumeration has no duplicate coordinate. -/
theorem allTerminalSupportWires_nodup (inputs gates : Nat) :
    (allTerminalSupportWires inputs gates).Nodup := by
  unfold allTerminalSupportWires
  have inputDistinct :
      ((allFin inputs).map
        (TerminalSupportWire.input (gates := gates))).Nodup :=
    nodup_map_injective (TerminalSupportWire.input (gates := gates))
      (fun (left right : Fin inputs) equal => by cases equal; rfl)
      (nodup_of_listNoDuplicates (allFin_noDuplicates inputs))
  have gateDistinct :
      ((allFin gates).map
        (TerminalSupportWire.gate (inputs := inputs))).Nodup :=
    nodup_map_injective (TerminalSupportWire.gate (inputs := inputs))
      (fun (left right : Fin gates) equal => by cases equal; rfl)
      (nodup_of_listNoDuplicates (allFin_noDuplicates gates))
  apply List.nodup_append.mpr
  refine ⟨inputDistinct, gateDistinct, ?_⟩
  intro inputWire inputMember gateWire gateMember equal
  obtain ⟨input, _inputMember, inputEqual⟩ := List.mem_map.mp inputMember
  obtain ⟨gate, _gateMember, gateEqual⟩ := List.mem_map.mp gateMember
  rw [← inputEqual, ← gateEqual] at equal
  cases equal

/-- Canonical gluing of the two incoming physical frontiers.  A side boundary
    wire is retained only while it remains external to the combined record
    set. -/
def terminalBoundaryFrontierPushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    List (TerminalSupportWire inputs gates) :=
  (allTerminalSupportWires inputs gates).filter fun wire => decide
    ((wire ∈ left.frontier.boundary ∨ wire ∈ right.frontier.boundary) ∧
      terminalWireExternal (left.records ++ right.records) wire = true)

/-- Canonical gluing of the two outgoing physical frontiers.  A side interface
    gate is retained only while it still has an external consumer or is a
    global output of the ambient candidate. -/
def terminalInterfaceFrontierPushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    List (Fin gates) :=
  (allFin gates).filter fun producer => decide
    ((producer ∈ left.frontier.interface ∨
        producer ∈ right.frontier.interface) ∧
      (terminalGateHasExternalConsumer candidate.program
          (left.records ++ right.records) producer = true ∨
        terminalGateIsGlobalOutput candidate.directWireWord producer = true))

/-- Canonical role-preserving gluing of one profile frontier. -/
def terminalProfileFrontierPushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) : List (Fin profileWidth) :=
  (allFin profileWidth).filter fun coordinate => decide
    (coordinate ∈ left.profileCoordinates role ∨
      coordinate ∈ right.profileCoordinates role)

/-- The manuscript's concrete governed-frontier star operation.  It uses only
    the two side completions; no join data or caller certificate occurs in the
    construction. -/
def terminalGovernedFrontierPushout
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    TerminalGovernedFrontier inputs gates profileWidth :=
  { boundary := terminalBoundaryFrontierPushout left right
    interface := terminalInterfaceFrontierPushout left right
    profiles := terminalProfileFrontierPushout left right }

/-- Constructive fieldwise equality for governed frontiers. -/
theorem TerminalGovernedFrontier.extensionality
    {inputs gates profileWidth : Nat}
    (left right : TerminalGovernedFrontier inputs gates profileWidth)
    (boundaryEqual : left.boundary = right.boundary)
    (interfaceEqual : left.interface = right.interface)
    (profilesEqual : left.profiles = right.profiles) :
    left = right := by
  cases left with
  | mk leftBoundary leftInterface leftProfiles =>
      cases right with
      | mk rightBoundary rightInterface rightProfiles =>
          change leftBoundary = rightBoundary at boundaryEqual
          change leftInterface = rightInterface at interfaceEqual
          change leftProfiles = rightProfiles at profilesEqual
          cases boundaryEqual
          cases interfaceEqual
          cases profilesEqual
          rfl

/-- Boundary membership in the computed pushout is exact. -/
theorem mem_terminalBoundaryFrontierPushout_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (wire : TerminalSupportWire inputs gates) :
    wire ∈ terminalBoundaryFrontierPushout left right ↔
      (wire ∈ left.frontier.boundary ∨ wire ∈ right.frontier.boundary) ∧
        terminalWireExternal (left.records ++ right.records) wire = true := by
  unfold terminalBoundaryFrontierPushout
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro selected
    exact List.mem_filter.mpr
      ⟨mem_allTerminalSupportWires wire, decide_eq_true selected⟩

/-- Interface membership in the computed pushout is exact. -/
theorem mem_terminalInterfaceFrontierPushout_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (producer : Fin gates) :
    producer ∈ terminalInterfaceFrontierPushout left right ↔
      (producer ∈ left.frontier.interface ∨
          producer ∈ right.frontier.interface) ∧
        (terminalGateHasExternalConsumer candidate.program
            (left.records ++ right.records) producer = true ∨
          terminalGateIsGlobalOutput candidate.directWireWord producer = true) := by
  unfold terminalInterfaceFrontierPushout
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro selected
    exact List.mem_filter.mpr ⟨mem_allFin producer, decide_eq_true selected⟩

/-- Profile membership in the computed pushout is exact. -/
theorem mem_terminalProfileFrontierPushout_iff
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ terminalProfileFrontierPushout left right role ↔
      coordinate ∈ left.profileCoordinates role ∨
        coordinate ∈ right.profileCoordinates role := by
  unfold terminalProfileFrontierPushout
  constructor
  · intro member
    exact of_decide_eq_true (List.mem_filter.mp member).2
  · intro selected
    exact List.mem_filter.mpr ⟨mem_allFin coordinate, decide_eq_true selected⟩

/-- The glued boundary retains canonical order and has no duplicate wire. -/
theorem terminalBoundaryFrontierPushout_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    (terminalBoundaryFrontierPushout left right).Nodup :=
  (allTerminalSupportWires_nodup inputs gates).sublist List.filter_sublist

/-- The glued interface retains canonical order and has no duplicate gate. -/
theorem terminalInterfaceFrontierPushout_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    (terminalInterfaceFrontierPushout left right).Nodup :=
  (nodup_of_listNoDuplicates (allFin_noDuplicates gates)).sublist
    List.filter_sublist

/-- Every glued role frontier retains canonical order and is duplicate-free. -/
theorem terminalProfileFrontierPushout_nodup
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (role : TerminalProfileRole) :
    (terminalProfileFrontierPushout left right role).Nodup :=
  (nodup_of_listNoDuplicates (allFin_noDuplicates profileWidth)).sublist
    List.filter_sublist

/-- Computed boundary disposition relative to the combined side records. -/
def terminalBoundaryFrontierDisposition
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (wire : TerminalSupportWire inputs gates) : TerminalFrontierDisposition :=
  if terminalWireExternal (left.records ++ right.records) wire
    then .retained else .internalized

/-- Computed interface disposition relative to the combined side records. -/
def terminalInterfaceFrontierDisposition
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system)
    (producer : Fin gates) : TerminalFrontierDisposition :=
  if terminalGateHasExternalConsumer candidate.program
        (left.records ++ right.records) producer ||
      terminalGateIsGlobalOutput candidate.directWireWord producer
    then .retained else .internalized

private theorem terminalGateSelected_append_true_iff
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates) :
    terminalGateSelected (left ++ right) gate = true ↔
      terminalGateSelected left gate = true ∨
        terminalGateSelected right gate = true := by
  rw [terminalGateSelected_eq_true_iff, terminalGateSelected_eq_true_iff,
    terminalGateSelected_eq_true_iff, List.mem_append]

private theorem bool_not_eq_false_implies_true (value : Bool)
    (notFalse : (!value) = false) : value = true := by
  cases value with
  | false => exact False.elim (Bool.noConfusion notFalse)
  | true => rfl

private theorem terminalGateSelected_left_false_of_append_false
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates)
    (combinedFalse : terminalGateSelected (left ++ right) gate = false) :
    terminalGateSelected left gate = false := by
  cases leftCheck : terminalGateSelected left gate with
  | false => rfl
  | true =>
      have combinedTrue :=
        (terminalGateSelected_append_true_iff left right gate).2
          (Or.inl leftCheck)
      rw [combinedFalse] at combinedTrue
      exact Bool.noConfusion combinedTrue

private theorem terminalGateSelected_right_false_of_append_false
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (gate : Fin gates)
    (combinedFalse : terminalGateSelected (left ++ right) gate = false) :
    terminalGateSelected right gate = false := by
  cases rightCheck : terminalGateSelected right gate with
  | false => rfl
  | true =>
      have combinedTrue :=
        (terminalGateSelected_append_true_iff left right gate).2
          (Or.inr rightCheck)
      rw [combinedFalse] at combinedTrue
      exact Bool.noConfusion combinedTrue

private theorem terminalWireExternal_left_of_append
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (combinedExternal : terminalWireExternal (left ++ right) wire = true) :
    terminalWireExternal left wire = true := by
  cases wire with
  | input index => rfl
  | gate gate =>
      apply (terminalWireExternal_eq_true_iff left (.gate gate)).2
      have combinedFalse :=
        (terminalWireExternal_eq_true_iff (left ++ right) (.gate gate)).1
          combinedExternal
      exact terminalGateSelected_left_false_of_append_false left right gate
        combinedFalse

private theorem terminalWireExternal_right_of_append
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates)
    (combinedExternal : terminalWireExternal (left ++ right) wire = true) :
    terminalWireExternal right wire = true := by
  cases wire with
  | input index => rfl
  | gate gate =>
      apply (terminalWireExternal_eq_true_iff right (.gate gate)).2
      have combinedFalse :=
        (terminalWireExternal_eq_true_iff (left ++ right) (.gate gate)).1
          combinedExternal
      exact terminalGateSelected_right_false_of_append_false left right gate
        combinedFalse

private theorem terminalBoundaryPorts_append_iff
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (wire : TerminalSupportWire inputs gates) :
    wire ∈ terminalBoundaryPorts program (left ++ right) ↔
      (wire ∈ terminalBoundaryPorts program left ∨
          wire ∈ terminalBoundaryPorts program right) ∧
        terminalWireExternal (left ++ right) wire = true := by
  constructor
  · intro combinedMember
    have combinedChecked :=
      (mem_terminalBoundaryPorts_iff program (left ++ right) wire).1
        combinedMember
    obtain ⟨combinedExternal, consumer, consumerMember, selected, uses⟩ :=
      (terminalBoundaryWire_eq_true_iff program (left ++ right) wire).1
        combinedChecked
    have selectedSide :=
      (terminalGateSelected_append_true_iff left right consumer).1 selected
    constructor
    · cases selectedSide with
      | inl leftSelected =>
          apply Or.inl
          apply (mem_terminalBoundaryPorts_iff program left wire).2
          apply (terminalBoundaryWire_eq_true_iff program left wire).2
          exact ⟨terminalWireExternal_left_of_append left right wire
            combinedExternal, consumer, consumerMember, leftSelected, uses⟩
      | inr rightSelected =>
          apply Or.inr
          apply (mem_terminalBoundaryPorts_iff program right wire).2
          apply (terminalBoundaryWire_eq_true_iff program right wire).2
          exact ⟨terminalWireExternal_right_of_append left right wire
            combinedExternal, consumer, consumerMember, rightSelected, uses⟩
    · exact combinedExternal
  · rintro ⟨sideMember, combinedExternal⟩
    apply (mem_terminalBoundaryPorts_iff program (left ++ right) wire).2
    apply (terminalBoundaryWire_eq_true_iff program (left ++ right) wire).2
    cases sideMember with
    | inl leftMember =>
        obtain ⟨_leftExternal, consumer, consumerMember, selected, uses⟩ :=
          (terminalBoundaryWire_eq_true_iff program left wire).1
            ((mem_terminalBoundaryPorts_iff program left wire).1 leftMember)
        exact ⟨combinedExternal, consumer, consumerMember,
          (terminalGateSelected_append_true_iff left right consumer).2
            (Or.inl selected), uses⟩
    | inr rightMember =>
        obtain ⟨_rightExternal, consumer, consumerMember, selected, uses⟩ :=
          (terminalBoundaryWire_eq_true_iff program right wire).1
            ((mem_terminalBoundaryPorts_iff program right wire).1 rightMember)
        exact ⟨combinedExternal, consumer, consumerMember,
          (terminalGateSelected_append_true_iff left right consumer).2
            (Or.inr selected), uses⟩

private theorem terminalGateHasExternalConsumer_left_of_append
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates)
    (combinedExternal :
      terminalGateHasExternalConsumer program (left ++ right) producer = true) :
    terminalGateHasExternalConsumer program left producer = true := by
  obtain ⟨consumer, consumerMember, combinedFalse, uses⟩ :=
    (terminalGateHasExternalConsumer_eq_true_iff program (left ++ right)
      producer).1 combinedExternal
  apply (terminalGateHasExternalConsumer_eq_true_iff program left producer).2
  have leftFalse := terminalGateSelected_left_false_of_append_false
    left right consumer combinedFalse
  exact ⟨consumer, consumerMember, leftFalse, uses⟩

private theorem terminalGateHasExternalConsumer_right_of_append
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates)
    (combinedExternal :
      terminalGateHasExternalConsumer program (left ++ right) producer = true) :
    terminalGateHasExternalConsumer program right producer = true := by
  obtain ⟨consumer, consumerMember, combinedFalse, uses⟩ :=
    (terminalGateHasExternalConsumer_eq_true_iff program (left ++ right)
      producer).1 combinedExternal
  apply (terminalGateHasExternalConsumer_eq_true_iff program right producer).2
  have rightFalse := terminalGateSelected_right_false_of_append_false
    left right consumer combinedFalse
  exact ⟨consumer, consumerMember, rightFalse, uses⟩

private theorem terminalInterfacePorts_append_iff
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (producer : Fin gates) :
    producer ∈ terminalInterfacePorts candidate (left ++ right) ↔
      (producer ∈ terminalInterfacePorts candidate left ∨
          producer ∈ terminalInterfacePorts candidate right) ∧
        (terminalGateHasExternalConsumer candidate.program
            (left ++ right) producer = true ∨
          terminalGateIsGlobalOutput candidate.directWireWord producer = true) := by
  constructor
  · intro combinedMember
    have combinedChecked :=
      (mem_terminalInterfacePorts_iff candidate (left ++ right) producer).1
        combinedMember
    obtain ⟨selected, exposed⟩ :=
      (terminalInterfaceGate_eq_true_iff candidate (left ++ right) producer).1
        combinedChecked
    have selectedSide :=
      (terminalGateSelected_append_true_iff left right producer).1 selected
    constructor
    · cases selectedSide with
      | inl leftSelected =>
          apply Or.inl
          apply (mem_terminalInterfacePorts_iff candidate left producer).2
          apply (terminalInterfaceGate_eq_true_iff candidate left producer).2
          refine ⟨leftSelected, ?_⟩
          cases exposed with
          | inl external =>
              apply Or.inl
              exact terminalGateHasExternalConsumer_left_of_append
                candidate.program left right producer external
          | inr output => exact Or.inr output
      | inr rightSelected =>
          apply Or.inr
          apply (mem_terminalInterfacePorts_iff candidate right producer).2
          apply (terminalInterfaceGate_eq_true_iff candidate right producer).2
          refine ⟨rightSelected, ?_⟩
          cases exposed with
          | inl external =>
              apply Or.inl
              exact terminalGateHasExternalConsumer_right_of_append
                candidate.program left right producer external
          | inr output => exact Or.inr output
    · exact exposed
  · rintro ⟨sideMember, combinedExposed⟩
    apply (mem_terminalInterfacePorts_iff candidate (left ++ right) producer).2
    apply (terminalInterfaceGate_eq_true_iff candidate (left ++ right)
      producer).2
    cases sideMember with
    | inl leftMember =>
        have leftChecked :=
          (terminalInterfaceGate_eq_true_iff candidate left producer).1
            ((mem_terminalInterfacePorts_iff candidate left producer).1
              leftMember)
        exact ⟨(terminalGateSelected_append_true_iff left right producer).2
          (Or.inl leftChecked.1), combinedExposed⟩
    | inr rightMember =>
        have rightChecked :=
          (terminalInterfaceGate_eq_true_iff candidate right producer).1
            ((mem_terminalInterfacePorts_iff candidate right producer).1
              rightMember)
        exact ⟨(terminalGateSelected_append_true_iff left right producer).2
          (Or.inr rightChecked.1), combinedExposed⟩

private theorem terminalGateSelected_function_congr
    {inputs gates outputs profileWidth : Nat}
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (sameGates : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right) :
    terminalGateSelected left = terminalGateSelected right := by
  funext gate
  apply Bool.eq_iff_iff.mpr
  exact (terminalGateSelected_eq_true_iff left gate).trans
    ((sameGates gate).trans
      (terminalGateSelected_eq_true_iff right gate).symm)

private theorem terminalBoundaryPorts_congr
    {inputs gates outputs profileWidth : Nat}
    (program : Program inputs gates)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (sameGates : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right) :
    terminalBoundaryPorts program left = terminalBoundaryPorts program right := by
  have selectedEqual := terminalGateSelected_function_congr left right sameGates
  unfold terminalBoundaryPorts
  apply congrArg (fun predicate =>
    (allTerminalSupportWires inputs gates).filter predicate)
  funext wire
  cases wire with
  | input index =>
      unfold terminalBoundaryWire terminalWireExternal
      rw [selectedEqual]
  | gate gate =>
      unfold terminalBoundaryWire terminalWireExternal
      rw [selectedEqual]

private theorem terminalInterfacePorts_congr
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (left right : List
      (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (sameGates : ∀ gate,
      TerminalPrimitiveRecord.gate gate ∈ left ↔
        TerminalPrimitiveRecord.gate gate ∈ right) :
    terminalInterfacePorts candidate left = terminalInterfacePorts candidate right := by
  have selectedEqual := terminalGateSelected_function_congr left right sameGates
  unfold terminalInterfacePorts terminalInterfaceGate
    terminalGateHasExternalConsumer
  rw [selectedEqual]

private theorem terminalBoundaryFrontierPushout_eq_ports_append
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    terminalBoundaryFrontierPushout left right =
      terminalBoundaryPorts candidate.program (left.records ++ right.records) := by
  unfold terminalBoundaryFrontierPushout terminalBoundaryPorts
  apply congrArg (fun predicate =>
    (allTerminalSupportWires inputs gates).filter predicate)
  funext wire
  apply Bool.eq_iff_iff.mpr
  have leftBoundary : left.frontier.boundary =
      terminalBoundaryPorts candidate.program left.records :=
    left.frontier_boundary
  have rightBoundary : right.frontier.boundary =
      terminalBoundaryPorts candidate.program right.records :=
    right.frontier_boundary
  constructor
  · intro pushoutChecked
    have pushoutMember := of_decide_eq_true pushoutChecked
    rw [leftBoundary, rightBoundary] at pushoutMember
    have combinedMember :=
      (terminalBoundaryPorts_append_iff candidate.program left.records
        right.records wire).2 pushoutMember
    exact (mem_terminalBoundaryPorts_iff candidate.program
      (left.records ++ right.records) wire).1 combinedMember
  · intro combinedChecked
    have combinedMember :=
      (mem_terminalBoundaryPorts_iff candidate.program
        (left.records ++ right.records) wire).2 combinedChecked
    have pushoutMember :=
      (terminalBoundaryPorts_append_iff candidate.program left.records
        right.records wire).1 combinedMember
    rw [← leftBoundary, ← rightBoundary] at pushoutMember
    exact decide_eq_true pushoutMember

private theorem terminalInterfaceFrontierPushout_eq_ports_append
    {inputs gates outputs profileWidth : Nat}
    {candidate : Candidate inputs gates outputs}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (left right : TerminalGovernedCompletedSupport candidate system) :
    terminalInterfaceFrontierPushout left right =
      terminalInterfacePorts candidate (left.records ++ right.records) := by
  unfold terminalInterfaceFrontierPushout terminalInterfacePorts
  apply congrArg (fun predicate => (allFin gates).filter predicate)
  funext producer
  apply Bool.eq_iff_iff.mpr
  have leftInterface : left.frontier.interface =
      terminalInterfacePorts candidate left.records :=
    left.frontier_interface
  have rightInterface : right.frontier.interface =
      terminalInterfacePorts candidate right.records :=
    right.frontier_interface
  constructor
  · intro pushoutChecked
    have pushoutMember := of_decide_eq_true pushoutChecked
    rw [leftInterface, rightInterface] at pushoutMember
    have combinedMember :=
      (terminalInterfacePorts_append_iff candidate left.records right.records
        producer).2 pushoutMember
    exact (mem_terminalInterfacePorts_iff candidate
      (left.records ++ right.records) producer).1 combinedMember
  · intro combinedChecked
    have combinedMember :=
      (mem_terminalInterfacePorts_iff candidate
        (left.records ++ right.records) producer).2 combinedChecked
    have pushoutMember :=
      (terminalInterfacePorts_append_iff candidate left.records right.records
        producer).1 combinedMember
    rw [← leftInterface, ← rightInterface] at pushoutMember
    exact decide_eq_true pushoutMember

private theorem squareJoin_append_same_gates
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system) (gate : Fin gates) :
    TerminalPrimitiveRecord.gate gate ∈ square.joinRecords ↔
      TerminalPrimitiveRecord.gate gate ∈
        (square.leftRecords ++ square.rightRecords) := by
  rw [square.mem_joinRecords_iff, List.mem_append]

/-- The independently computed join boundary is exactly the physical frontier
    gluing of the two sides. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_join_boundary_eq_pushout
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs) :
    (square.governedCompleted candidate .join).frontier.boundary =
      terminalBoundaryFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) := by
  let left := square.governedCompleted candidate .left
  let right := square.governedCompleted candidate .right
  have joinToAppend :
      terminalBoundaryPorts candidate.program square.joinRecords =
        terminalBoundaryPorts candidate.program
          (square.leftRecords ++ square.rightRecords) :=
    terminalBoundaryPorts_congr candidate.program square.joinRecords
      (square.leftRecords ++ square.rightRecords)
      (squareJoin_append_same_gates square)
  rw [TerminalGovernedCompletedSupport.frontier_boundary]
  change terminalBoundaryPorts candidate.program square.joinRecords = _
  rw [joinToAppend]
  exact (terminalBoundaryFrontierPushout_eq_ports_append left right).symm

/-- The independently computed join interface is exactly the physical
    interface gluing of the two sides. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_join_interface_eq_pushout
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs) :
    (square.governedCompleted candidate .join).frontier.interface =
      terminalInterfaceFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) := by
  let left := square.governedCompleted candidate .left
  let right := square.governedCompleted candidate .right
  have joinToAppend :
      terminalInterfacePorts candidate square.joinRecords =
        terminalInterfacePorts candidate
          (square.leftRecords ++ square.rightRecords) :=
    terminalInterfacePorts_congr candidate square.joinRecords
      (square.leftRecords ++ square.rightRecords)
      (squareJoin_append_same_gates square)
  rw [TerminalGovernedCompletedSupport.frontier_interface]
  change terminalInterfacePorts candidate square.joinRecords = _
  rw [joinToAppend]
  exact (terminalInterfaceFrontierPushout_eq_ports_append left right).symm

/-- One profile coordinate lies in the meet frontier exactly when it lies in
    both side frontiers with the same computed role. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_meet_profile_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (square.governedCompleted candidate .meet).profileCoordinates role ↔
      coordinate ∈ (square.governedCompleted candidate .left).profileCoordinates role ∧
        coordinate ∈ (square.governedCompleted candidate .right).profileCoordinates role := by
  rw [square.governedCompleted_profile_iff,
    square.governedCompleted_profile_iff,
    square.governedCompleted_profile_iff]
  change (TerminalPrimitiveRecord.profile coordinate ∈ square.meetRecords ∧
      system.profileSystem.role coordinate = role) ↔
    (TerminalPrimitiveRecord.profile coordinate ∈ square.leftRecords ∧
      system.profileSystem.role coordinate = role) ∧
    TerminalPrimitiveRecord.profile coordinate ∈ square.rightRecords ∧
      system.profileSystem.role coordinate = role
  rw [square.mem_meetRecords_iff]
  constructor
  · rintro ⟨⟨leftMember, rightMember⟩, roleEqual⟩
    exact ⟨⟨leftMember, roleEqual⟩, rightMember, roleEqual⟩
  · rintro ⟨⟨leftMember, roleEqual⟩, rightMember, _rightRole⟩
    exact ⟨⟨leftMember, rightMember⟩, roleEqual⟩

/-- One profile coordinate lies in the join frontier exactly when it lies in
    either side frontier with the same computed role. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_join_profile_iff
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth) :
    coordinate ∈ (square.governedCompleted candidate .join).profileCoordinates role ↔
      coordinate ∈ (square.governedCompleted candidate .left).profileCoordinates role ∨
        coordinate ∈ (square.governedCompleted candidate .right).profileCoordinates role := by
  rw [square.governedCompleted_profile_iff,
    square.governedCompleted_profile_iff,
    square.governedCompleted_profile_iff]
  change (TerminalPrimitiveRecord.profile coordinate ∈ square.joinRecords ∧
      system.profileSystem.role coordinate = role) ↔
    (TerminalPrimitiveRecord.profile coordinate ∈ square.leftRecords ∧
        system.profileSystem.role coordinate = role) ∨
      TerminalPrimitiveRecord.profile coordinate ∈ square.rightRecords ∧
        system.profileSystem.role coordinate = role
  rw [square.mem_joinRecords_iff]
  constructor
  · rintro ⟨recordMember, roleEqual⟩
    cases recordMember with
    | inl leftMember => exact Or.inl ⟨leftMember, roleEqual⟩
    | inr rightMember => exact Or.inr ⟨rightMember, roleEqual⟩
  · intro sideMember
    cases sideMember with
    | inl leftMember => exact ⟨Or.inl leftMember.1, leftMember.2⟩
    | inr rightMember => exact ⟨Or.inr rightMember.1, rightMember.2⟩

/-- The independently computed join profile is exactly the role-preserving
    profile gluing of the two sides. -/
theorem TerminalSaturatedSupportSquare.governedCompleted_join_profile_eq_pushout
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (role : TerminalProfileRole) :
    (square.governedCompleted candidate .join).profileCoordinates role =
      terminalProfileFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) role := by
  unfold TerminalGovernedCompletedSupport.profileCoordinates
    terminalProfileCoordinatesForRole terminalProfileFrontierPushout
  apply congrArg (fun predicate => (allFin profileWidth).filter predicate)
  funext coordinate
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro joinChecked
    have joinProfile := of_decide_eq_true joinChecked
    have sideRecord :=
      (square.mem_joinRecords_iff
        (TerminalPrimitiveRecord.profile coordinate)).1 joinProfile.1
    apply decide_eq_true
    cases sideRecord with
    | inl leftMember =>
        exact Or.inl
          ((square.governedCompleted_profile_iff candidate .left role coordinate).2
            ⟨leftMember, joinProfile.2⟩)
    | inr rightMember =>
        exact Or.inr
          ((square.governedCompleted_profile_iff candidate .right role coordinate).2
            ⟨rightMember, joinProfile.2⟩)
  · intro sideChecked
    have sideProfile := of_decide_eq_true sideChecked
    apply decide_eq_true
    cases sideProfile with
    | inl leftMember =>
        have leftData :=
          (square.governedCompleted_profile_iff candidate .left role coordinate).1
            leftMember
        exact ⟨
          (square.mem_joinRecords_iff
            (TerminalPrimitiveRecord.profile coordinate)).2
              (Or.inl leftData.1), leftData.2⟩
    | inr rightMember =>
        have rightData :=
          (square.governedCompleted_profile_iff candidate .right role coordinate).1
            rightMember
        exact ⟨
          (square.mem_joinRecords_iff
            (TerminalPrimitiveRecord.profile coordinate)).2
              (Or.inr rightData.1), rightData.2⟩

/-- Every profile coordinate on either side is transported unchanged to the
    glued join frontier. -/
theorem TerminalSaturatedSupportSquare.side_profile_mem_join
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (role : TerminalProfileRole) (coordinate : Fin profileWidth)
    (sideMember :
      coordinate ∈ (square.governedCompleted candidate .left).profileCoordinates role ∨
        coordinate ∈ (square.governedCompleted candidate .right).profileCoordinates role) :
    coordinate ∈ (square.governedCompleted candidate .join).profileCoordinates role :=
  (square.governedCompleted_join_profile_iff candidate role coordinate).2
    sideMember

/-- A left boundary wire retained by the disposition occurs on the glued
    exterior; an internalized one is the output of a gate selected on the
    right. -/
theorem TerminalSaturatedSupportSquare.left_boundary_disposition
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (wire : TerminalSupportWire inputs gates)
    (leftMember : wire ∈
      (square.governedCompleted candidate .left).frontier.boundary) :
    (terminalBoundaryFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) wire = .retained ∧
      wire ∈ terminalBoundaryFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right)) ∨
    (terminalBoundaryFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) wire = .internalized ∧
      ∃ gate, wire = .gate gate ∧
        terminalGateSelected square.rightRecords gate = true) := by
  let left := square.governedCompleted candidate .left
  let right := square.governedCompleted candidate .right
  cases external : terminalWireExternal (left.records ++ right.records) wire with
  | true =>
      apply Or.inl
      constructor
      · change (if terminalWireExternal (left.records ++ right.records) wire = true
            then TerminalFrontierDisposition.retained
            else TerminalFrontierDisposition.internalized) =
          TerminalFrontierDisposition.retained
        rw [external]
        rfl
      · exact (mem_terminalBoundaryFrontierPushout_iff left right wire).2
          ⟨Or.inl leftMember, external⟩
  | false =>
      apply Or.inr
      constructor
      · change (if terminalWireExternal (left.records ++ right.records) wire = true
            then TerminalFrontierDisposition.retained
            else TerminalFrontierDisposition.internalized) =
          TerminalFrontierDisposition.internalized
        rw [external]
        rfl
      · cases wire with
        | input index =>
            unfold terminalWireExternal at external
            exact False.elim (Bool.noConfusion external)
        | gate gate =>
            refine ⟨gate, rfl, ?_⟩
            have combinedTrue :
                terminalGateSelected (left.records ++ right.records) gate = true := by
              change (!terminalGateSelected (left.records ++ right.records) gate) =
                false at external
              exact bool_not_eq_false_implies_true _ external
            have split := (terminalGateSelected_append_true_iff
              left.records right.records gate).1 combinedTrue
            cases split with
            | inl selectedLeft =>
                have leftChecked :=
                  (mem_terminalBoundaryPorts_iff candidate.program
                    square.leftRecords (.gate gate)).1 leftMember
                have leftExternal :=
                  (terminalBoundaryWire_eq_true_iff candidate.program
                    square.leftRecords (.gate gate)).1 leftChecked |>.1
                have leftFalse :=
                  (terminalWireExternal_eq_true_iff square.leftRecords
                    (.gate gate)).1 leftExternal
                change terminalGateSelected left.records gate = false at leftFalse
                rw [selectedLeft] at leftFalse
                exact False.elim (Bool.noConfusion leftFalse)
            | inr selectedRight => exact selectedRight

/-- The right-boundary internalization statement is symmetric. -/
theorem TerminalSaturatedSupportSquare.right_boundary_disposition
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (wire : TerminalSupportWire inputs gates)
    (rightMember : wire ∈
      (square.governedCompleted candidate .right).frontier.boundary) :
    (terminalBoundaryFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) wire = .retained ∧
      wire ∈ terminalBoundaryFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right)) ∨
    (terminalBoundaryFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) wire = .internalized ∧
      ∃ gate, wire = .gate gate ∧
        terminalGateSelected square.leftRecords gate = true) := by
  let left := square.governedCompleted candidate .left
  let right := square.governedCompleted candidate .right
  cases external : terminalWireExternal (left.records ++ right.records) wire with
  | true =>
      apply Or.inl
      constructor
      · change (if terminalWireExternal (left.records ++ right.records) wire = true
            then TerminalFrontierDisposition.retained
            else TerminalFrontierDisposition.internalized) =
          TerminalFrontierDisposition.retained
        rw [external]
        rfl
      · exact (mem_terminalBoundaryFrontierPushout_iff left right wire).2
          ⟨Or.inr rightMember, external⟩
  | false =>
      apply Or.inr
      constructor
      · change (if terminalWireExternal (left.records ++ right.records) wire = true
            then TerminalFrontierDisposition.retained
            else TerminalFrontierDisposition.internalized) =
          TerminalFrontierDisposition.internalized
        rw [external]
        rfl
      · cases wire with
        | input index =>
            unfold terminalWireExternal at external
            exact False.elim (Bool.noConfusion external)
        | gate gate =>
            refine ⟨gate, rfl, ?_⟩
            have combinedTrue :
                terminalGateSelected (left.records ++ right.records) gate = true := by
              change (!terminalGateSelected (left.records ++ right.records) gate) =
                false at external
              exact bool_not_eq_false_implies_true _ external
            have split := (terminalGateSelected_append_true_iff
              left.records right.records gate).1 combinedTrue
            cases split with
            | inl selectedLeft => exact selectedLeft
            | inr selectedRight =>
                have rightChecked :=
                  (mem_terminalBoundaryPorts_iff candidate.program
                    square.rightRecords (.gate gate)).1 rightMember
                have rightExternal :=
                  (terminalBoundaryWire_eq_true_iff candidate.program
                    square.rightRecords (.gate gate)).1 rightChecked |>.1
                have rightFalse :=
                  (terminalWireExternal_eq_true_iff square.rightRecords
                    (.gate gate)).1 rightExternal
                change terminalGateSelected right.records gate = false at rightFalse
                rw [selectedRight] at rightFalse
                exact False.elim (Bool.noConfusion rightFalse)

/-- A side-interface producer is retained exactly when it remains externally
    observable; otherwise it has no external consumer and is not a global
    output in the combined support. -/
theorem TerminalSaturatedSupportSquare.side_interface_disposition
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs)
    (producer : Fin gates)
    (sideMember : producer ∈
        (square.governedCompleted candidate .left).frontier.interface ∨
      producer ∈
        (square.governedCompleted candidate .right).frontier.interface) :
    (terminalInterfaceFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) producer = .retained ∧
      producer ∈ terminalInterfaceFrontierPushout
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right)) ∨
    (terminalInterfaceFrontierDisposition
        (square.governedCompleted candidate .left)
        (square.governedCompleted candidate .right) producer = .internalized ∧
      terminalGateHasExternalConsumer candidate.program
        (square.leftRecords ++ square.rightRecords) producer = false ∧
      terminalGateIsGlobalOutput candidate.directWireWord producer = false) := by
  let left := square.governedCompleted candidate .left
  let right := square.governedCompleted candidate .right
  cases external : terminalGateHasExternalConsumer candidate.program
      (left.records ++ right.records) producer with
  | true =>
      apply Or.inl
      constructor
      · change (if
            (terminalGateHasExternalConsumer candidate.program
                (left.records ++ right.records) producer ||
              terminalGateIsGlobalOutput candidate.directWireWord producer) = true
            then TerminalFrontierDisposition.retained
            else TerminalFrontierDisposition.internalized) =
          TerminalFrontierDisposition.retained
        rw [external]
        rfl
      · exact (mem_terminalInterfaceFrontierPushout_iff left right producer).2
          ⟨sideMember, Or.inl external⟩
  | false =>
      cases output : terminalGateIsGlobalOutput candidate.directWireWord producer with
      | true =>
          apply Or.inl
          constructor
          · change (if
                (terminalGateHasExternalConsumer candidate.program
                    (left.records ++ right.records) producer ||
                  terminalGateIsGlobalOutput candidate.directWireWord producer) = true
                then TerminalFrontierDisposition.retained
                else TerminalFrontierDisposition.internalized) =
              TerminalFrontierDisposition.retained
            rw [external, output]
            rfl
          · exact (mem_terminalInterfaceFrontierPushout_iff left right producer).2
              ⟨sideMember, Or.inr output⟩
      | false =>
          apply Or.inr
          refine ⟨?_, external, rfl⟩
          change (if
              (terminalGateHasExternalConsumer candidate.program
                  (left.records ++ right.records) producer ||
                terminalGateIsGlobalOutput candidate.directWireWord producer) = true
              then TerminalFrontierDisposition.retained
              else TerminalFrontierDisposition.internalized) =
            TerminalFrontierDisposition.internalized
          rw [external, output]
          rfl

/-- Legacy Section 3 frontier-pushout law.  The meet is the exact shared
    profile overlap, and the independently completed join frontier is exactly
    the canonical gluing of the two sides. -/
theorem TerminalSaturatedSupportSquare.governed_frontier_pushout
    {inputs gates outputs profileWidth : Nat}
    {system : TerminalSaturationSystem inputs gates outputs profileWidth}
    (square : TerminalSaturatedSupportSquare system)
    (candidate : Candidate inputs gates outputs) :
    (square.governedCompleted candidate .join).frontier =
        terminalGovernedFrontierPushout
          (square.governedCompleted candidate .left)
          (square.governedCompleted candidate .right) ∧
      ∀ role coordinate,
        coordinate ∈
            (square.governedCompleted candidate .meet).profileCoordinates role ↔
          coordinate ∈
              (square.governedCompleted candidate .left).profileCoordinates role ∧
            coordinate ∈
              (square.governedCompleted candidate .right).profileCoordinates role := by
  constructor
  · apply TerminalGovernedFrontier.extensionality
    · exact square.governedCompleted_join_boundary_eq_pushout candidate
    · exact square.governedCompleted_join_interface_eq_pushout candidate
    · funext role
      exact square.governedCompleted_join_profile_eq_pushout candidate role
  · intro role coordinate
    exact square.governedCompleted_meet_profile_iff candidate role coordinate

end DirectWire
end PNP
