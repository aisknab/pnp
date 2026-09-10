/-
Copyright (c) 2026 PNP Labs.

Physical request dispatch for every paired initial cell. One fixed program walks
the seven canonical encoding segments using actual register comparisons and
residuals. It preserves all seven incoming metadata/cell fields and returns a
request kind and argument. Source-bit requests are indices, never supplied bits.
Source-machine, reader and payload-writer integration remain downstream.
-/

import PNP.Concrete.CookLevinBuilderInitialCellHandoff

namespace PNP.Concrete.CookLevin.BuilderInitialPairedRequest

open BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderArbitrarySlotHeaderRouter
open BuilderInitialCellDecoder (comparisonValues residual)
open WorkMachineProgramGraph (Node Endpoint Graph)
open WorkMachineProgramPath (AcceptPath)

abbrev Metadata := BuilderInitialCellHandoff.Metadata

inductive Width where
  | fuel | input | one | certificate
  deriving DecidableEq, Repr

def Width.value : Width → Metadata → Nat
  | .fuel, metadata => metadata.fuel
  | .input, metadata => metadata.inputLength
  | .one, _ => 1
  | .certificate, metadata => metadata.length

def Width.field : Width → BuilderRegisterPack.Field 8
  | .fuel => .argument ⟨1, by decide⟩
  | .input => .argument ⟨0, by decide⟩
  | .one => .constant 1
  | .certificate => .argument ⟨2, by decide⟩

inductive Payload where
  | blank | fixed (value : Bool) | source | certificate
  deriving DecidableEq, Repr

def Payload.kind : Payload → Nat
  | .blank => 0 | .fixed _ => 1 | .source => 2 | .certificate => 3
def Payload.argument : Payload → Nat → Nat
  | .blank, _ => 0
  | .fixed value, _ => if value then 1 else 0
  | .source, cursor => cursor
  | .certificate, cursor => cursor
def Payload.result (payload : Payload) (cursor : Nat) : Nat × Nat :=
  (payload.kind, payload.argument cursor)

structure Entry where
  width : Width
  payload : Payload
  deriving DecidableEq, Repr

def certificateEntries : List Entry :=
  [⟨.certificate, .fixed true⟩, ⟨.one, .fixed false⟩, ⟨.certificate, .certificate⟩]
def fixedEntries : List Entry :=
  ⟨.input, .fixed true⟩ :: ⟨.one, .fixed false⟩ :: ⟨.input, .source⟩ :: certificateEntries
def entries : List Entry := ⟨.fuel, .blank⟩ :: fixedEntries

def inputValues (metadata : Metadata) (position offset : Nat) : List Nat :=
  metadata.values ++ [position, offset]
def frame (metadata : Metadata) (position offset cursor : Nat) : List Nat :=
  inputValues metadata position offset ++ [cursor]
def comparisonFrame (width : Width) (metadata : Metadata) (position offset cursor : Nat) : List Nat :=
  frame metadata position offset cursor ++ comparisonValues cursor (width.value metadata)
def requestValues (metadata : Metadata) (position offset : Nat) (request : Nat × Nat) : List Nat :=
  inputValues metadata position offset ++ [request.1, request.2]

def selectFor : List Entry → Metadata → Nat → Nat × Nat
  | [], _, _ => Payload.blank.result 0
  | entry :: rest, metadata, cursor =>
      if cursor < entry.width.value metadata then entry.payload.result cursor
      else selectFor rest metadata (cursor - entry.width.value metadata)
def requestCode (metadata : Metadata) (position : Nat) : Nat × Nat :=
  selectFor entries metadata position

def encodeRequest : BuilderInitialCellCoordinates.Request certificateWidth → Nat × Nat
  | .blank => (0, 0)
  | .fixed value => (1, if value then 1 else 0)
  | .sourceBit index => (2, index)
  | .certificate index => (3, index.val)

def initialFields : List (BuilderRegisterPack.Field 7) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .argument ⟨5, by decide⟩,
   .argument ⟨6, by decide⟩, .argument ⟨5, by decide⟩]
def comparisonFields (width : Width) : List (BuilderRegisterPack.Field 8) :=
  [.argument ⟨7, by decide⟩, width.field]
def carryFields : List (BuilderRegisterPack.Field 13) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .argument ⟨5, by decide⟩,
   .argument ⟨6, by decide⟩, .argument ⟨12, by decide⟩]
def payloadArgumentField : Payload → BuilderRegisterPack.Field 13
  | .blank => .constant 0
  | .fixed value => .constant (if value then 1 else 0)
  | .source => .argument ⟨12, by decide⟩
  | .certificate => .argument ⟨12, by decide⟩
def reportFields (payload : Payload) : List (BuilderRegisterPack.Field 13) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .argument ⟨5, by decide⟩,
   .argument ⟨6, by decide⟩, .constant payload.kind, payloadArgumentField payload]
def baseFields : List (BuilderRegisterPack.Field 8) :=
  [.argument ⟨0, by decide⟩, .argument ⟨1, by decide⟩, .argument ⟨2, by decide⟩,
   .argument ⟨3, by decide⟩, .argument ⟨4, by decide⟩, .argument ⟨5, by decide⟩,
   .argument ⟨6, by decide⟩, .constant 0, .constant 0]

theorem entries_length : entries.length = 7 := rfl
theorem inputValues_length (metadata : Metadata) (position offset : Nat) :
    (inputValues metadata position offset).length = 7 := rfl
theorem frame_length (metadata : Metadata) (position offset cursor : Nat) :
    (frame metadata position offset cursor).length = 8 := rfl
theorem comparisonFrame_length (width : Width) (metadata : Metadata) (position offset cursor : Nat) :
    (comparisonFrame width metadata position offset cursor).length = 13 := rfl
theorem requestValues_length (metadata : Metadata) (position offset : Nat) (request : Nat × Nat) :
    (requestValues metadata position offset request).length = 9 := rfl

private def view {arity : Nat} (data : List Nat) (index : Fin arity) : Nat :=
  data[index.val]?.getD 0

private theorem view_ofFn {arity : Nat} (data : List Nat) (hLength : data.length = arity) :
    List.ofFn (view data : Fin arity → Nat) = data := by
  subst arity
  have h : (view data : Fin data.length → Nat) = fun index => data[index.val] := by
    funext index
    simp only [view, List.getElem?_eq_getElem index.isLt, Option.getD_some]
  rw [h]
  exact List.ofFn_getElem


theorem initial_values (metadata : Metadata) (position offset : Nat) :
    BuilderRegisterPack.values initialFields (view (inputValues metadata position offset)) =
      frame metadata position offset position := rfl
theorem comparison_values (width : Width) (metadata : Metadata) (position offset cursor : Nat) :
    BuilderRegisterPack.values (comparisonFields width) (view (frame metadata position offset cursor)) =
      [cursor, width.value metadata] := by cases width <;> rfl
theorem carry_values (width : Width) (metadata : Metadata) (position offset cursor : Nat) :
    BuilderRegisterPack.values carryFields (view (comparisonFrame width metadata position offset cursor)) =
      frame metadata position offset (residual cursor (width.value metadata)) := rfl
theorem report_values (payload : Payload) (width : Width) (metadata : Metadata) (position offset cursor : Nat) :
    BuilderRegisterPack.values (reportFields payload) (view (comparisonFrame width metadata position offset cursor)) =
      requestValues metadata position offset (payload.result (residual cursor (width.value metadata))) := by
  cases payload <;> rfl
theorem base_values (metadata : Metadata) (position offset cursor : Nat) :
    BuilderRegisterPack.values baseFields (view (frame metadata position offset cursor)) =
      requestValues metadata position offset (Payload.blank.result 0) := rfl

def tailNode (next : WorkMachine) : Node :=
  {name := 4, program := next, onAccept := .accept, onReject := .dead}
def carryNode (next : WorkMachine) : Node :=
  {name := 3, program := BuilderRegisterPack.machine carryFields 0,
   onAccept := .node (tailNode next).reference, onReject := .dead}
def reportNode (payload : Payload) : Node :=
  {name := 2, program := BuilderRegisterPack.machine (reportFields payload) 0,
   onAccept := .accept, onReject := .dead}
def compareNode (entry : Entry) (next : WorkMachine) : Node :=
  {name := 1, program := BuilderRegisterCompareResidual.machine,
   onAccept := .node (reportNode entry.payload).reference, onReject := .node (carryNode next).reference}
def packNode (entry : Entry) (next : WorkMachine) : Node :=
  {name := 0, program := BuilderRegisterPack.machine (comparisonFields entry.width) 0,
   onAccept := .node (compareNode entry next).reference, onReject := .dead}
def branchGraph (entry : Entry) (next : WorkMachine) : Graph :=
  {nodes := [packNode entry next, compareNode entry next, reportNode entry.payload, carryNode next, tailNode next],
   entry := (packNode entry next).reference}

def machineFor : List Entry → WorkMachine
  | [] => BuilderRegisterPack.machine baseFields 0
  | entry :: rest => WorkMachineProgramGraph.machine (branchGraph entry (machineFor rest))

private theorem pack_mem (entry : Entry) (next : WorkMachine) :
    packNode entry next ∈ (branchGraph entry next).nodes := List.Mem.head _
private theorem compare_mem (entry : Entry) (next : WorkMachine) :
    compareNode entry next ∈ (branchGraph entry next).nodes := List.Mem.tail _ (List.Mem.head _)
private theorem report_mem (entry : Entry) (next : WorkMachine) :
    reportNode entry.payload ∈ (branchGraph entry next).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
private theorem carry_mem (entry : Entry) (next : WorkMachine) :
    carryNode next ∈ (branchGraph entry next).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
private theorem tail_mem (entry : Entry) (next : WorkMachine) :
    tailNode next ∈ (branchGraph entry next).nodes := List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))

private def Good (program : WorkMachine) : Prop :=
  program.rules.Pairwise WorkMachineProgramGraph.QueryDistinct ∧
    WorkMachineProgramGraph.NoRuleAt program program.acceptState ∧
    WorkMachineProgramGraph.NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

private theorem pack_good {arity : Nat} (fields : List (BuilderRegisterPack.Field arity)) :
    Good (BuilderRegisterPack.machine fields 0) :=
  ⟨BuilderRegisterPack.rules_pairwise_query_distinct fields 0,
    BuilderRegisterPack.noRuleAtAccept fields 0, BuilderRegisterPack.noRuleAtReject fields 0,
    BuilderRegisterPack.acceptState_ne_rejectState fields 0⟩

private theorem comparison_good : Good BuilderRegisterCompareResidual.machine :=
  ⟨BuilderRegisterCompareResidual.rules_pairwise_query_distinct,
    BuilderRegisterCompareResidual.noRuleAtAccept, BuilderRegisterCompareResidual.noRuleAtReject,
    BuilderRegisterCompareResidual.acceptState_ne_rejectState⟩


private theorem branch_wellFormed (entry : Entry) (next : WorkMachine) (hNext : Good next) :
    (branchGraph entry next).WellFormed := by
  have hNames : ((branchGraph entry next).nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1, 2, 3, 4] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [branchGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact pack_good (comparisonFields entry.width)
    · exact comparison_good
    · exact pack_good (reportFields entry.payload)
    · exact pack_good carryFields
    · exact hNext
  · exact ⟨packNode entry next, pack_mem entry next, rfl, rfl⟩
  · intro node hMem
    simp only [branchGraph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨compareNode entry next, compare_mem entry next, rfl, rfl⟩, True.intro⟩
    · exact ⟨⟨reportNode entry.payload, report_mem entry next, rfl, rfl⟩,
        ⟨carryNode next, carry_mem entry next, rfl, rfl⟩⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨⟨tailNode next, tail_mem entry next, rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

private theorem machineFor_good (stages : List Entry) : Good (machineFor stages) := by
  induction stages with
  | nil => exact pack_good baseFields
  | cons entry rest ih =>
      exact ⟨WorkMachineProgramGraph.rules_pairwise _ (branch_wellFormed entry _ ih),
        WorkMachineProgramGraph.noRuleAt_globalAccept _, WorkMachineProgramGraph.noRuleAt_globalReject _,
        by change (0 : Nat) ≠ 1; decide⟩

def valuesFor : List Entry → Metadata → Nat → Nat → Nat → List Nat
  | [], metadata, position, offset, cursor =>
      frame metadata position offset cursor ++ requestValues metadata position offset (Payload.blank.result 0)
  | entry :: rest, metadata, position, offset, cursor =>
      comparisonFrame entry.width metadata position offset cursor ++
        if cursor < entry.width.value metadata then
          requestValues metadata position offset (entry.payload.result cursor)
        else valuesFor rest metadata position offset (cursor - entry.width.value metadata)

def comparisonPackSteps (width : Width) (metadata : Metadata) (position offset cursor : Nat) : Nat :=
  BuilderRegisterPack.workSteps (comparisonFields width) (view (frame metadata position offset cursor)) []
def reportSteps (entry : Entry) (metadata : Metadata) (position offset cursor : Nat) : Nat :=
  BuilderRegisterPack.workSteps (reportFields entry.payload) (view (comparisonFrame entry.width metadata position offset cursor)) []
def carrySteps (width : Width) (metadata : Metadata) (position offset cursor : Nat) : Nat :=
  BuilderRegisterPack.workSteps carryFields (view (comparisonFrame width metadata position offset cursor)) []
def stepsFor : List Entry → Metadata → Nat → Nat → Nat → Nat
  | [], metadata, position, offset, cursor =>
      BuilderRegisterPack.workSteps baseFields (view (frame metadata position offset cursor)) []
  | entry :: rest, metadata, position, offset, cursor =>
      comparisonPackSteps entry.width metadata position offset cursor + 1 +
        (BuilderRegisterCompareResidual.workSteps cursor (entry.width.value metadata) + 1 +
          if cursor < entry.width.value metadata then
            reportSteps entry metadata position offset cursor + 1
          else carrySteps entry.width metadata position offset cursor + 1 +
            (stepsFor rest metadata position offset (cursor - entry.width.value metadata) + 1))

private theorem pack_run {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (inside : List WorkSymbol) (hLength : data.length = arity) :
    workRunExact? (BuilderRegisterPack.machine fields 0)
      (BuilderRegisterPack.workSteps fields (view data) [])
      (workStartConfiguration (BuilderRegisterPack.machine fields 0) (endTape (older ++ data) inside [])) =
      some {
        state := (BuilderRegisterPack.machine fields 0).acceptState
        tape := endTape (older ++ data ++ BuilderRegisterPack.values fields (view data)) inside [] } := by
  have h := BuilderRegisterPack.workRunExact fields 0 older (view data) [] inside [] rfl
  simpa only [BuilderRegisterPack.initialConfiguration, BuilderRegisterPack.finalConfiguration,
    view_ofFn data hLength, List.append_nil, List.drop_nil] using h

private theorem pack_bounds {arity : Nat} (fields : List (BuilderRegisterPack.Field arity))
    (data older : List Nat) (bound : NatPolynomial) (inputLength : Nat)
    (hLength : data.length = arity)
    (hSpan : (registerWord (older ++ data)).length ≤ bound.eval inputLength) :
    (registerWord (older ++ data ++ BuilderRegisterPack.values fields (view data))).length ≤
        (BuilderRegisterPack.spanPolynomial fields bound).eval inputLength ∧
      6 * BuilderRegisterPack.workSteps fields (view data) [] ≤
        (BuilderRegisterPack.rawTimePolynomial fields bound).eval inputLength := by
  have h := BuilderRegisterPack.source_polynomial_bounds fields bound inputLength older (view data) [] (by
    simpa only [view_ofFn data hLength, List.append_nil] using hSpan)
  simpa only [view_ofFn data hLength, List.append_nil] using h

private theorem configuration_eq_of_fields (config : WorkConfiguration) (state : Nat) (tape : WorkTape)
    (hState : config.state = state) (hTape : config.tape = tape) :
    config = {state := state, tape := tape} := by
  cases config with
  | mk currentState currentTape =>
      change currentState = state at hState
      change currentTape = tape at hTape
      subst currentState
      subst currentTape
      rfl

private theorem comparison_run (coordinate boundary : Nat) (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? BuilderRegisterCompareResidual.machine
      (BuilderRegisterCompareResidual.workSteps coordinate boundary)
      (workStartConfiguration BuilderRegisterCompareResidual.machine (endTape (older ++ [coordinate, boundary]) inside [])) =
      some {
        state := if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
          else BuilderRegisterCompareResidual.machine.rejectState
        tape := endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] } := by
  have hState : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).state =
      if coordinate < boundary then BuilderRegisterCompareResidual.machine.acceptState
      else BuilderRegisterCompareResidual.machine.rejectState := by
    by_cases hLess : coordinate < boundary
    · rw [if_pos hLess]
      exact (BuilderRegisterCompareResidual.final_accept_iff coordinate boundary older inside []).mpr hLess
    · rw [if_neg hLess]
      exact (BuilderRegisterCompareResidual.final_reject_iff coordinate boundary older inside []).mpr (by omega)
  have hTape : (BuilderRegisterCompareResidual.finalConfiguration coordinate boundary older inside []).tape =
      endTape (older ++ BuilderInitialCellDecoder.comparisonValues coordinate boundary) inside [] := by
    rw [BuilderRegisterCompareResidual.final_tape, BuilderInitialCellDecoder.comparisonValues_eq]
    simp only [BuilderRegisterCompareResidual.outputValues, BuilderRegisterCompareResidual.resultBoundary_eq,
      BuilderRegisterCompareResidual.resultCoordinate_eq, List.drop_nil, List.append_assoc]
  have h := BuilderRegisterCompareResidual.workRunExact coordinate boundary older inside []
  rw [configuration_eq_of_fields _ _ _ hState hTape] at h
  exact h


private theorem runFor (stages : List Entry) (metadata : Metadata) (position offset cursor : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? (machineFor stages) (stepsFor stages metadata position offset cursor)
      (workStartConfiguration (machineFor stages) (endTape (older ++ frame metadata position offset cursor) inside [])) =
      some {
        state := (machineFor stages).acceptState
        tape := endTape (older ++ valuesFor stages metadata position offset cursor) inside []} := by
  induction stages generalizing cursor older with
  | nil =>
      have h := pack_run baseFields (frame metadata position offset cursor) older inside rfl
      rw [base_values] at h
      simpa only [machineFor, stepsFor, valuesFor, List.append_assoc] using h
  | cons entry rest ih =>
      have hCompare : workRunExact? BuilderRegisterCompareResidual.machine
          (BuilderRegisterCompareResidual.workSteps cursor (entry.width.value metadata))
          (workStartConfiguration BuilderRegisterCompareResidual.machine
            (endTape (older ++ frame metadata position offset cursor ++ [cursor, entry.width.value metadata]) inside [])) =
          some {
            state := if cursor < entry.width.value metadata then BuilderRegisterCompareResidual.machine.acceptState
              else BuilderRegisterCompareResidual.machine.rejectState
            tape := endTape (older ++ comparisonFrame entry.width metadata position offset cursor) inside []} := by
        simpa only [comparisonFrame, List.append_assoc] using
          comparison_run cursor (entry.width.value metadata) (older ++ frame metadata position offset cursor) inside
      have hC : AcceptPath (branchGraph entry (machineFor rest))
          (.node (compareNode entry (machineFor rest)).reference) .accept
          (BuilderRegisterCompareResidual.workSteps cursor (entry.width.value metadata) + 1 +
            if cursor < entry.width.value metadata then reportSteps entry metadata position offset cursor + 1
            else carrySteps entry.width metadata position offset cursor + 1 +
              (stepsFor rest metadata position offset (cursor - entry.width.value metadata) + 1))
          (endTape (older ++ frame metadata position offset cursor ++ [cursor, entry.width.value metadata]) inside [])
          (endTape (older ++ valuesFor (entry :: rest) metadata position offset cursor) inside []) := by
        by_cases hLess : cursor < entry.width.value metadata
        · simp only [if_pos hLess] at hCompare ⊢
          have hReport := pack_run (reportFields entry.payload)
            (comparisonFrame entry.width metadata position offset cursor) older inside rfl
          rw [report_values] at hReport
          simp only [residual, if_pos hLess, List.append_assoc] at hReport
          have hR := AcceptPath.step (reportNode entry.payload) .accept _ 0 _ _ _
            (report_mem entry (machineFor rest)) hReport (.terminal .accept _)
          have h := AcceptPath.step (compareNode entry (machineFor rest)) .accept _ _ _ _ _
            (compare_mem entry (machineFor rest)) hCompare hR
          simpa only [valuesFor, if_pos hLess, reportSteps, List.append_assoc, Nat.add_zero] using h
        · simp only [if_neg hLess] at hCompare ⊢
          have hCarry := pack_run carryFields
            (comparisonFrame entry.width metadata position offset cursor) older inside rfl
          rw [carry_values] at hCarry
          simp only [residual, if_neg hLess, List.append_assoc] at hCarry
          have hTail := ih (cursor - entry.width.value metadata)
            (older ++ comparisonFrame entry.width metadata position offset cursor)
          simp only [List.append_assoc] at hTail
          have hT := AcceptPath.step (tailNode (machineFor rest)) .accept _ 0 _ _ _
            (tail_mem entry (machineFor rest)) hTail (.terminal .accept _)
          have hK := AcceptPath.step (carryNode (machineFor rest)) .accept _ _ _ _ _
            (carry_mem entry (machineFor rest)) hCarry hT
          have h := AcceptPath.stepReject (compareNode entry (machineFor rest)) .accept _ _ _ _ _
            (compare_mem entry (machineFor rest)) hCompare hK
          simpa only [valuesFor, if_neg hLess, carrySteps, List.append_assoc, Nat.add_zero] using h
      have hPack := pack_run (comparisonFields entry.width) (frame metadata position offset cursor) older inside rfl
      rw [comparison_values] at hPack
      simp only [List.append_assoc] at hPack hC
      have hP := AcceptPath.step (packNode entry (machineFor rest)) .accept _ _ _ _ _
        (pack_mem entry (machineFor rest)) hPack hC
      have h := WorkMachineProgramPath.runExact (branchGraph entry (machineFor rest)) _ _ _ _ _
        (branch_wellFormed entry _ (machineFor_good rest)) hP
      have hStart (tape : WorkTape) :
          WorkMachineProgramGraph.endpointConfiguration (.node (packNode entry (machineFor rest)).reference) tape =
            workStartConfiguration (machineFor (entry :: rest)) tape := rfl
      have hMachine : WorkMachineProgramGraph.machine (branchGraph entry (machineFor rest)) =
          machineFor (entry :: rest) := rfl
      have hAccept (tape : WorkTape) :
          WorkMachineProgramGraph.endpointConfiguration .accept tape =
            {state := (machineFor (entry :: rest)).acceptState, tape := tape} := rfl
      rw [hStart, hMachine, hAccept] at h
      simpa only [stepsFor, comparisonPackSteps] using h

private theorem suffixFor (stages : List Entry) (metadata : Metadata) (position offset cursor : Nat) :
    ∃ history : List Nat, valuesFor stages metadata position offset cursor =
      history ++ requestValues metadata position offset (selectFor stages metadata cursor) := by
  induction stages generalizing cursor with
  | nil => exact ⟨_, rfl⟩
  | cons entry rest ih =>
      by_cases hLess : cursor < entry.width.value metadata
      · exact ⟨comparisonFrame entry.width metadata position offset cursor,
          by simp only [valuesFor, selectFor, if_pos hLess]⟩
      · obtain ⟨history, h⟩ := ih (cursor - entry.width.value metadata)
        refine ⟨comparisonFrame entry.width metadata position offset cursor ++ history, ?_⟩
        simp only [valuesFor, selectFor, if_neg hLess, h, List.append_assoc]

def dispatchNode : Node :=
  {name := 1, program := machineFor entries, onAccept := .accept, onReject := .dead}
def initialNode : Node :=
  {name := 0, program := BuilderRegisterPack.machine initialFields 0,
   onAccept := .node dispatchNode.reference, onReject := .dead}
def graph : Graph := {nodes := [initialNode, dispatchNode], entry := initialNode.reference}
def machine : WorkMachine := WorkMachineProgramGraph.machine graph

private theorem initial_mem : initialNode ∈ graph.nodes := List.Mem.head _
private theorem dispatch_mem : dispatchNode ∈ graph.nodes := List.Mem.tail _ (List.Mem.head _)

theorem graph_wellFormed : graph.WellFormed := by
  have hNames : (graph.nodes.map Node.name).Pairwise (fun a b : Nat => a ≠ b) := by
    change ([0, 1] : List Nat).Pairwise _
    decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [List.pairwise_map] using hNames
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact pack_good initialFields
    · exact machineFor_good entries
  · exact ⟨initialNode, List.Mem.head _, rfl, rfl⟩
  · intro node hMem
    simp only [graph, List.mem_cons, List.not_mem_nil, or_false] at hMem
    rcases hMem with rfl | rfl
    · exact ⟨⟨dispatchNode, List.Mem.tail _ (List.Mem.head _), rfl, rfl⟩, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def outputValues (metadata : Metadata) (position offset : Nat) : List Nat :=
  inputValues metadata position offset ++ valuesFor entries metadata position offset position
def initialSteps (metadata : Metadata) (position offset : Nat) : Nat :=
  BuilderRegisterPack.workSteps initialFields (view (inputValues metadata position offset)) []
def workSteps (metadata : Metadata) (position offset : Nat) : Nat :=
  initialSteps metadata position offset + 1 + (stepsFor entries metadata position offset position + 1)
def initialConfiguration (metadata : Metadata) (position offset : Nat)
    (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ inputValues metadata position offset) inside [])
def finalConfiguration (metadata : Metadata) (position offset : Nat)
    (older : List Nat) (inside : List WorkSymbol) : WorkConfiguration :=
  {state := machine.acceptState, tape := endTape (older ++ outputValues metadata position offset) inside []}

/-- The complete fixed dispatcher reads every branch and index from its actual registers. -/
theorem workRunExact (metadata : Metadata) (position offset : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    workRunExact? machine (workSteps metadata position offset)
      (initialConfiguration metadata position offset older inside) =
      some (finalConfiguration metadata position offset older inside) := by
  have hDispatch := runFor entries metadata position offset position
    (older ++ inputValues metadata position offset) inside
  simp only [List.append_assoc] at hDispatch
  have hD := AcceptPath.step dispatchNode .accept _ 0 _ _ _
    dispatch_mem hDispatch (.terminal .accept _)
  have hInitial := pack_run initialFields (inputValues metadata position offset) older inside rfl
  rw [initial_values] at hInitial
  simp only [List.append_assoc] at hInitial
  have hI := AcceptPath.step initialNode .accept _ _ _ _ _
    initial_mem hInitial hD
  have h := WorkMachineProgramPath.runExact graph _ _ _ _ _ graph_wellFormed hI
  have hStart (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration (.node initialNode.reference) tape =
        workStartConfiguration machine tape := rfl
  have hMachine : WorkMachineProgramGraph.machine graph = machine := rfl
  have hAccept (tape : WorkTape) :
      WorkMachineProgramGraph.endpointConfiguration .accept tape =
        {state := machine.acceptState, tape := tape} := rfl
  rw [hStart, hMachine, hAccept] at h
  simpa only [workSteps, initialSteps, initialConfiguration, finalConfiguration,
    outputValues, List.append_assoc, Nat.add_zero] using h

theorem run_compile_exact (metadata : Metadata) (position offset : Nat)
    (older : List Nat) (inside : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps metadata position offset)
      (encodeWorkConfiguration (initialConfiguration metadata position offset older inside)) =
      encodeWorkConfiguration (finalConfiguration metadata position offset older inside) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact metadata position offset older inside)
theorem final_tape (metadata : Metadata) (position offset : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).tape =
      endTape (older ++ outputValues metadata position offset) inside [] := rfl
theorem final_frontier (metadata : Metadata) (position offset : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).tape.left = [] := rfl
theorem final_accept (metadata : Metadata) (position offset : Nat) (older : List Nat) (inside : List WorkSymbol) :
    (finalConfiguration metadata position offset older inside).state = machine.acceptState := rfl

theorem output_suffix (metadata : Metadata) (position offset : Nat) :
    ∃ history : List Nat, outputValues metadata position offset =
      history ++ requestValues metadata position offset (requestCode metadata position) := by
  obtain ⟨history, h⟩ := suffixFor entries metadata position offset position
  exact ⟨inputValues metadata position offset ++ history, by
    simpa only [outputValues, requestCode, h, List.append_assoc]⟩

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed
theorem noRuleAtAccept : WorkMachineProgramGraph.NoRuleAt machine machine.acceptState :=
  WorkMachineProgramGraph.noRuleAt_globalAccept graph
theorem noRuleAtReject : WorkMachineProgramGraph.NoRuleAt machine machine.rejectState :=
  WorkMachineProgramGraph.noRuleAt_globalReject graph
theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by
  change (0 : Nat) ≠ 1
  decide


def packedSpan (width : Width) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (comparisonFields width) bound
def comparedSpan (width : Width) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterCompareResidual.spanPolynomial (packedSpan width bound)
def reportedSpan (entry : Entry) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial (reportFields entry.payload) (comparedSpan entry.width bound)
def carriedSpan (width : Width) (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial carryFields (comparedSpan width bound)

def spanFor : List Entry → NatPolynomial → NatPolynomial
  | [], bound => BuilderRegisterPack.spanPolynomial baseFields bound
  | entry :: rest, bound =>
      .add (reportedSpan entry bound) (spanFor rest (carriedSpan entry.width bound))
def rawTimeFor : List Entry → NatPolynomial → NatPolynomial
  | [], bound => BuilderRegisterPack.rawTimePolynomial baseFields bound
  | entry :: rest, bound =>
      .add (BuilderRegisterPack.rawTimePolynomial (comparisonFields entry.width) bound)
        (.add (BuilderRegisterCompareResidual.rawTimePolynomial (packedSpan entry.width bound))
        (.add (BuilderRegisterPack.rawTimePolynomial (reportFields entry.payload) (comparedSpan entry.width bound))
        (.add (BuilderRegisterPack.rawTimePolynomial carryFields (comparedSpan entry.width bound))
        (.add (rawTimeFor rest (carriedSpan entry.width bound)) (.constant 24)))))

private theorem boundsFor (stages : List Entry) (metadata : Metadata) (position offset cursor : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ frame metadata position offset cursor)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ valuesFor stages metadata position offset cursor)).length ≤
        (spanFor stages bound).eval inputSize ∧
      6 * stepsFor stages metadata position offset cursor ≤ (rawTimeFor stages bound).eval inputSize := by
  induction stages generalizing cursor older bound with
  | nil =>
      have h := pack_bounds baseFields (frame metadata position offset cursor) older bound inputSize rfl hSpan
      rw [base_values] at h
      simpa only [valuesFor, stepsFor, spanFor, rawTimeFor, List.append_assoc] using h
  | cons entry rest ih =>
      have hPack := pack_bounds (comparisonFields entry.width) (frame metadata position offset cursor)
        older bound inputSize rfl hSpan
      rw [comparison_values] at hPack
      have hCompare := BuilderRegisterCompareResidual.source_polynomial_bounds cursor (entry.width.value metadata)
        (older ++ frame metadata position offset cursor) (packedSpan entry.width bound) inputSize hPack.1
      have hCompared : (registerWord (older ++ comparisonFrame entry.width metadata position offset cursor)).length ≤
          (comparedSpan entry.width bound).eval inputSize := by
        rw [comparisonFrame, BuilderInitialCellDecoder.comparisonValues_eq]
        simpa only [comparedSpan, List.append_assoc] using hCompare.1
      by_cases hLess : cursor < entry.width.value metadata
      · have hReport := pack_bounds (reportFields entry.payload)
          (comparisonFrame entry.width metadata position offset cursor) older
          (comparedSpan entry.width bound) inputSize rfl hCompared
        rw [report_values] at hReport
        simp only [residual, if_pos hLess] at hReport
        constructor
        · have hFinal : (registerWord (older ++ valuesFor (entry :: rest) metadata position offset cursor)).length ≤
              (reportedSpan entry bound).eval inputSize := by
            simpa only [valuesFor, if_pos hLess, reportedSpan, List.append_assoc] using hReport.1
          simp only [spanFor, NatPolynomial.eval_add]
          omega
        · simp only [stepsFor, if_pos hLess, comparisonPackSteps, reportSteps, rawTimeFor,
            NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega
      · have hCarry := pack_bounds carryFields
          (comparisonFrame entry.width metadata position offset cursor) older
          (comparedSpan entry.width bound) inputSize rfl hCompared
        rw [carry_values] at hCarry
        simp only [residual, if_neg hLess] at hCarry
        have hRest := ih (cursor - entry.width.value metadata)
          (older ++ comparisonFrame entry.width metadata position offset cursor)
          (carriedSpan entry.width bound) (by
            simpa only [carriedSpan, List.append_assoc] using hCarry.1)
        constructor
        · have hFinal : (registerWord (older ++ valuesFor (entry :: rest) metadata position offset cursor)).length ≤
              (spanFor rest (carriedSpan entry.width bound)).eval inputSize := by
            simpa only [valuesFor, if_neg hLess, List.append_assoc] using hRest.1
          simp only [spanFor, NatPolynomial.eval_add]
          omega
        · simp only [stepsFor, if_neg hLess, comparisonPackSteps, carrySteps, rawTimeFor,
            NatPolynomial.eval_add, NatPolynomial.eval_constant]
          omega

def preparedSpan (bound : NatPolynomial) : NatPolynomial :=
  BuilderRegisterPack.spanPolynomial initialFields bound
def spanPolynomial (bound : NatPolynomial) : NatPolynomial :=
  spanFor entries (preparedSpan bound)
def rawTimePolynomial (bound : NatPolynomial) : NatPolynomial :=
  .add (BuilderRegisterPack.rawTimePolynomial initialFields bound)
    (.add (rawTimeFor entries (preparedSpan bound)) (.constant 12))

/-- Every comparison, copy, retained register and graph bridge belongs to this bound. -/
theorem source_polynomial_bounds (metadata : Metadata) (position offset : Nat)
    (older : List Nat) (bound : NatPolynomial) (inputSize : Nat)
    (hSpan : (registerWord (older ++ inputValues metadata position offset)).length ≤ bound.eval inputSize) :
    (registerWord (older ++ outputValues metadata position offset)).length ≤
        (spanPolynomial bound).eval inputSize ∧
      6 * workSteps metadata position offset ≤ (rawTimePolynomial bound).eval inputSize := by
  have hInitial := pack_bounds initialFields (inputValues metadata position offset) older bound inputSize rfl hSpan
  rw [initial_values] at hInitial
  have hDispatch := boundsFor entries metadata position offset position
    (older ++ inputValues metadata position offset) (preparedSpan bound) inputSize hInitial.1
  constructor
  · simpa only [outputValues, spanPolynomial, List.append_assoc] using hDispatch.1
  · simp only [workSteps, initialSteps, rawTimePolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant]
    omega

theorem request_span_le_output (metadata : Metadata) (position offset : Nat) :
    (registerWord (requestValues metadata position offset (requestCode metadata position))).length ≤
      (registerWord (outputValues metadata position offset)).length := by
  obtain ⟨history, h⟩ := output_suffix metadata position offset
  rw [h, registerWord_append, List.length_append]
  omega


private theorem certificate_correct (metadata : Metadata) {certificateWidth : Nat}
    (length : Fin (certificateWidth + 1)) (cursor : Nat) (hLength : metadata.length = length.val) :
    selectFor certificateEntries metadata cursor =
      encodeRequest (BuilderInitialCellCoordinates.certificateRequest length cursor) := by
  have hSelect : selectFor certificateEntries metadata cursor =
      if cursor < metadata.length then (1, 1)
      else if cursor - metadata.length < 1 then (1, 0)
      else if cursor - metadata.length - 1 < metadata.length then (3, cursor - metadata.length - 1)
      else (0, 0) := rfl
  rw [hSelect, hLength]
  unfold BuilderInitialCellCoordinates.certificateRequest
  by_cases hFirst : cursor < length.val
  · simp only [if_pos hFirst, encodeRequest]
    rfl
  · by_cases hDelimiter : cursor = length.val
    · subst cursor
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Nat.zero_lt_succ, if_true, encodeRequest]
      rfl
    · have hTest : ¬ cursor - length.val < 1 := by omega
      have hShift : cursor - length.val - 1 = cursor - (length.val + 1) := by omega
      simp only [if_neg hFirst, if_neg hDelimiter, if_neg hTest, hShift]
      by_cases hIndex : cursor - (length.val + 1) < length.val
      · simp only [if_pos hIndex, dif_pos hIndex, encodeRequest]
      · simp only [if_neg hIndex, dif_neg hIndex, encodeRequest]

private theorem fixed_correct (metadata : Metadata) (cursor : Nat) {certificateWidth : Nat} :
    selectFor fixedEntries metadata cursor =
      if cursor < 2 * metadata.inputLength + 1 then
        encodeRequest (BuilderInitialCellCoordinates.fixedRequest metadata.inputLength cursor :
          BuilderInitialCellCoordinates.Request certificateWidth)
      else selectFor certificateEntries metadata (cursor - (2 * metadata.inputLength + 1)) := by
  have hSelect : selectFor fixedEntries metadata cursor =
      if cursor < metadata.inputLength then (1, 1)
      else if cursor - metadata.inputLength < 1 then (1, 0)
      else if cursor - metadata.inputLength - 1 < metadata.inputLength then (2, cursor - metadata.inputLength - 1)
      else selectFor certificateEntries metadata (cursor - metadata.inputLength - 1 - metadata.inputLength) := rfl
  rw [hSelect]
  by_cases hFirst : cursor < metadata.inputLength
  · have hBlock : cursor < 2 * metadata.inputLength + 1 := by omega
    simp only [if_pos hFirst, if_pos hBlock, BuilderInitialCellCoordinates.fixedRequest, encodeRequest]
    rfl
  · by_cases hDelimiter : cursor = metadata.inputLength
    · subst cursor
      have hBlock : metadata.inputLength < 2 * metadata.inputLength + 1 := by omega
      simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Nat.zero_lt_succ, if_true, if_pos hBlock,
        BuilderInitialCellCoordinates.fixedRequest, encodeRequest]
      rfl
    · have hTest : ¬ cursor - metadata.inputLength < 1 := by omega
      by_cases hBlock : cursor < 2 * metadata.inputLength + 1
      · have hIndex : cursor - (metadata.inputLength + 1) < metadata.inputLength := by omega
        have hShift : cursor - metadata.inputLength - 1 = cursor - (metadata.inputLength + 1) := by omega
        simp only [if_neg hFirst, if_neg hTest, if_pos hIndex, if_pos hBlock,
          BuilderInitialCellCoordinates.fixedRequest, if_neg hDelimiter, encodeRequest, hShift]
      · have hIndex : ¬ cursor - metadata.inputLength - 1 < metadata.inputLength := by omega
        have hShift : cursor - metadata.inputLength - 1 - metadata.inputLength =
            cursor - (2 * metadata.inputLength + 1) := by omega
        simp only [if_neg hFirst, if_neg hTest, if_neg hIndex, if_neg hBlock, hShift]

/-- All runtime request kinds and arguments agree with the unchanged paired-cell specification. -/
theorem request_canonical (metadata : Metadata) {certificateWidth : Nat}
    (length : Fin (certificateWidth + 1)) (position : Nat) (hLength : metadata.length = length.val) :
    requestCode metadata position =
      encodeRequest (BuilderInitialCellCoordinates.pairedRequest metadata.inputLength length metadata.fuel position) := by
  have hSelect : requestCode metadata position =
      if position < metadata.fuel then (0, 0)
      else selectFor fixedEntries metadata (position - metadata.fuel) := rfl
  rw [hSelect]
  unfold BuilderInitialCellCoordinates.pairedRequest
  by_cases hCenter : metadata.fuel ≤ position
  · have hLess : ¬ position < metadata.fuel := by omega
    rw [if_neg hLess, if_pos hCenter, fixed_correct (certificateWidth := certificateWidth)]
    unfold BuilderInitialCellCoordinates.pairedOffsetRequest
    by_cases hBlock : position - metadata.fuel < 2 * metadata.inputLength + 1
    · simp only [if_pos hBlock]
    · simp only [if_neg hBlock]
      exact certificate_correct metadata length _ hLength
  · have hLess : position < metadata.fuel := by omega
    simp only [if_pos hLess, if_neg hCenter, encodeRequest]

theorem canonical_output_suffix (metadata : Metadata) {certificateWidth : Nat}
    (length : Fin (certificateWidth + 1)) (position offset : Nat) (hLength : metadata.length = length.val) :
    ∃ history : List Nat, outputValues metadata position offset =
      history ++ requestValues metadata position offset
        (encodeRequest (BuilderInitialCellCoordinates.pairedRequest metadata.inputLength length metadata.fuel position)) := by
  obtain ⟨history, h⟩ := output_suffix metadata position offset
  exact ⟨history, by simpa only [request_canonical metadata length position hLength] using h⟩

theorem certificate_index_bound (metadata : Metadata) {certificateWidth : Nat}
    (length : Fin (certificateWidth + 1)) (position : Nat) (hLength : metadata.length = length.val)
    (hCertificate : (requestCode metadata position).1 = 3) :
    (requestCode metadata position).2 < certificateWidth := by
  rw [request_canonical metadata length position hLength] at hCertificate ⊢
  cases hRequest : BuilderInitialCellCoordinates.pairedRequest metadata.inputLength length metadata.fuel position with
  | blank => simp only [hRequest, encodeRequest] at hCertificate; omega
  | fixed value => simp only [hRequest, encodeRequest] at hCertificate; omega
  | sourceBit index => simp only [hRequest, encodeRequest] at hCertificate; omega
  | certificate index => exact index.isLt

end PNP.Concrete.CookLevin.BuilderInitialPairedRequest
