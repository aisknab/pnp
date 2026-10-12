/-
Copyright (c) 2026 PNP Labs.

One finite register compiler with literal raw input loading and output packing.
A three-node graph preserves the source accept/reject distinction. Every graph
handoff is a real transition and is charged in the exact trace.

The semantics below are relative to a finite source run. They do not assert
termination of an arbitrary register program or implement the closed normalizer.
-/

import PNP.Concrete.BitRegisterIOBounds

namespace PNP.Concrete.BitRegister.CompilerIO

open IOAdapter Operation WorkMachineProgramGraph PipelineStateNamespace

def outputNode {count : Nat} (program : Program count) : Node :=
  ⟨2, outputAt program.output.succ.val, .accept, .reject⟩

def executionNode {count : Nat} (program : Program count) : Node :=
  ⟨1, Compiler.machine program, .node (outputNode program).reference, .reject⟩

def inputNode {count : Nat} (program : Program count) : Node :=
  ⟨0, inputAdapter program, .node (executionNode program).reference, .reject⟩

def graph {count : Nat} (program : Program count) : Graph :=
  ⟨[inputNode program, executionNode program, outputNode program], (inputNode program).reference⟩

def machine {count : Nat} (program : Program count) : WorkMachine :=
  WorkMachineProgramGraph.machine (graph program)

theorem input_member {count : Nat} (program : Program count) :
    inputNode program ∈ (graph program).nodes := by
  simp only [graph, List.mem_cons, List.mem_nil_iff, or_false, true_or]

theorem execution_member {count : Nat} (program : Program count) :
    executionNode program ∈ (graph program).nodes := by
  simp only [graph, List.mem_cons, List.mem_nil_iff, or_false, true_or, or_true]

theorem output_member {count : Nat} (program : Program count) :
    outputNode program ∈ (graph program).nodes := by
  simp only [graph, List.mem_cons, List.mem_nil_iff, or_false, or_true]

private theorem member_resolves (nodes : List Node) (node : Node) (member : node ∈ nodes) :
    Endpoint.Resolves nodes (.node node.reference) :=
  ⟨node, member, rfl, rfl⟩

theorem graph_wellFormed {count : Nat} (program : Program count) : (graph program).WellFormed := by
  refine ⟨?_, ?_, member_resolves _ _ (input_member program), ?_⟩
  · change [inputNode program, executionNode program, outputNode program].Pairwise _
    constructor
    · intro node member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl
      · change (0 : Nat) ≠ 1; decide
      · change (0 : Nat) ≠ 2; decide
    · constructor
      · intro node member
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
        subst node
        change (1 : Nat) ≠ 2
        decide
      · constructor
        · intro node impossible
          exact False.elim (List.not_mem_nil impossible)
        · exact List.Pairwise.nil
  · intro node member
    simp only [graph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact inputAdapter_wellFormed program
    · exact Compiler.machine_wellFormed program
    · exact outputAt_wellFormed program.output.succ.val
  · intro node member
    simp only [graph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨member_resolves _ _ (execution_member program), True.intro⟩
    · exact ⟨member_resolves _ _ (output_member program), True.intro⟩
    · exact ⟨True.intro, True.intro⟩

theorem machine_wellFormed {count : Nat} (program : Program count) :
    ProgramWellFormed (machine program) :=
  ⟨WorkMachineProgramGraph.rules_pairwise _ (graph_wellFormed program),
    noRuleAt_globalAccept _, noRuleAt_globalReject _, machine_accept_ne_reject _⟩

theorem graph_node_count {count : Nat} (program : Program count) :
    (graph program).nodes.length = 3 := rfl

def sourceResult {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    Configuration count :=
  BitRegister.run program fuel (initial program input)

def finalStore {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : Store (count + 1) :=
  Compiler.scratchStore (sourceResult program fuel input).store

def finalSlack {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : Nat :=
  Compiler.traceSlack program fuel (initial program input) 0

def executionTape {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : WorkTape :=
  (finalStore program fuel input).tape (inputOutside program input) (finalSlack program fuel input)

def packedTape {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : WorkTape :=
  outputTape (finalStore program fuel input) program.output.succ
    (inputOutside program input) (finalSlack program fuel input)

def acceptingSteps {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : Nat :=
  (inputAdapterSteps program input + 1) +
    ((Compiler.traceSteps program fuel (initial program input) + 1) +
      (outputAtSteps (finalStore program fuel input) program.output.succ + 1))

def rejectingSteps {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) : Nat :=
  (inputAdapterSteps program input + 1) +
    (Compiler.traceSteps program fuel (initial program input) + 1)

theorem input_run {count : Nat} (program : Program count) (input : BitString) :
    workRunExact? (machine program) (inputAdapterSteps program input + 1)
      ⟨(machine program).startState, rawInputWorkTape input⟩ =
      some (endpointConfiguration (.node (executionNode program).reference)
        ((Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0)) :=
  local_then_accept (graph program) (inputNode program) _ _ _
    (graph_wellFormed program) (input_member program) (inputAdapter_run program input) rfl

theorem execution_accept_run {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    workRunExact? (machine program) (Compiler.traceSteps program fuel (initial program input) + 1)
      (endpointConfiguration (.node (executionNode program).reference)
        ((Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0)) =
      some (endpointConfiguration (.node (outputNode program).reference) (executionTape program fuel input)) := by
  have atAccept :
      (Compiler.encodeConfiguration program (sourceResult program fuel input)
        (inputOutside program input) (finalSlack program fuel input)).state =
      (Compiler.machine program).acceptState := by
    change endpointState (Compiler.controlEndpoint program (sourceResult program fuel input).control) = _
    rw [accepted]
    rfl
  exact local_then_accept (graph program) (executionNode program) _ _ _
    (graph_wellFormed program) (execution_member program)
    (Compiler.initial_run program fuel input (inputOutside program input) 0) atAccept

theorem execution_reject_run {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (rejected : (sourceResult program fuel input).control = .rejected) :
    workRunExact? (machine program) (Compiler.traceSteps program fuel (initial program input) + 1)
      (endpointConfiguration (.node (executionNode program).reference)
        ((Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0)) =
      some ⟨(machine program).rejectState, executionTape program fuel input⟩ := by
  have atReject :
      (Compiler.encodeConfiguration program (sourceResult program fuel input)
        (inputOutside program input) (finalSlack program fuel input)).state =
      (Compiler.machine program).rejectState := by
    change endpointState (Compiler.controlEndpoint program (sourceResult program fuel input).control) = _
    rw [rejected]
    rfl
  exact local_then_reject (graph program) (executionNode program) _ _ _
    (graph_wellFormed program) (execution_member program)
    (Compiler.initial_run program fuel input (inputOutside program input) 0) atReject

theorem output_run {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    workRunExact? (machine program) (outputAtSteps (finalStore program fuel input) program.output.succ + 1)
      (endpointConfiguration (.node (outputNode program).reference) (executionTape program fuel input)) =
      some ⟨(machine program).acceptState, packedTape program fuel input⟩ :=
  local_then_accept (graph program) (outputNode program) _ _ _
    (graph_wellFormed program) (output_member program)
    (outputAt_run (finalStore program fuel input) program.output.succ
      (inputOutside program input) (finalSlack program fuel input)) rfl

theorem work_run_accept {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (accepted : (sourceResult program fuel input).control = .accepted) :
    workRunExact? (machine program) (acceptingSteps program fuel input)
      ⟨(machine program).startState, rawInputWorkTape input⟩ =
      some ⟨(machine program).acceptState, packedTape program fuel input⟩ := by
  have afterInput := PipelineMachineSimulation.workRunExact?_compose (machine program)
    (Compiler.traceSteps program fuel (initial program input) + 1)
    (outputAtSteps (finalStore program fuel input) program.output.succ + 1) _ _ _
    (execution_accept_run program fuel input accepted) (output_run program fuel input)
  exact PipelineMachineSimulation.workRunExact?_compose (machine program)
    (inputAdapterSteps program input + 1) _ _ _ _ (input_run program input) afterInput

theorem work_run_reject {count : Nat} (program : Program count) (fuel : Nat) (input : BitString)
    (rejected : (sourceResult program fuel input).control = .rejected) :
    workRunExact? (machine program) (rejectingSteps program fuel input)
      ⟨(machine program).startState, rawInputWorkTape input⟩ =
      some ⟨(machine program).rejectState, executionTape program fuel input⟩ :=
  PipelineMachineSimulation.workRunExact?_compose (machine program)
    (inputAdapterSteps program input + 1) _ _ _ _
    (input_run program input) (execution_reject_run program fuel input rejected)

theorem packedTape_output {count : Nat} (program : Program count) (fuel : Nat) (input : BitString) :
    (encodeWorkTape (packedTape program fuel input)).outputBits =
      (sourceResult program fuel input).store.get program.output := by
  exact outputTape_output (finalStore program fuel input) program.output.succ
    (inputOutside program input) (finalSlack program fuel input)

end PNP.Concrete.BitRegister.CompilerIO
