/-
Copyright (c) 2026 PNP Labs.

Exact semantics of the computed cut and its smaller open replacement.
The port-typed view is definitionally the existing extractor's candidate.
The attempted literal substitution cannot compile into an acyclic circuit.
These facts do not refute the checked acyclic framed law or a correctly
restricted full/admissible-support law.
-/

import PNP.NANDCompatibleSupportSlackMinimum

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.CompatibleSupportSlackObstruction

private def literalSources (index : Fin 11) : Source 4 11 × Source 4 11 :=
  match index.val with
  | 0 => (.input 0, .input 1)
  | 1 => (.gate 0, .gate 0)
  | 2 => (.gate 1, .input 2)
  | 3 => (.gate 2, .input 3)
  | 4 => (.input 0, .gate 3)
  | 5 => (.gate 4, .gate 4)
  | 6 => (.gate 5, .input 1)
  | 7 => (.gate 3, .gate 3)
  | 8 => (.input 0, .gate 7)
  | 9 => (.gate 8, .gate 8)
  | _ => (.gate 9, .input 1)

private theorem original_gate_sources (index : Fin 11) :
    original.program.terminalGateSources index = literalSources index := by
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem original_output_source (output : Fin 10) :
    original.directWireWord.source output = .gate output.succ :=
  Candidate.ofDirectWireWord_pointwise originalProgram
    ⟨fun index => .gate index.succ⟩ output

private def selectedMask (index : Fin 11) : Bool :=
  !(index.val == 2 || index.val == 3)

private def interfaceMask (index : Fin 11) : Bool :=
  index.val != 0 && selectedMask index

private theorem selected_mask_eq : terminalGateSelected records = selectedMask := by
  funext index
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem interface_mask_eq :
    terminalInterfaceGate original records = interfaceMask := by
  funext index
  simp only [terminalInterfaceGate, terminalGateHasExternalConsumer,
    Program.terminalGateUsesWire, original_gate_sources, terminalGateIsGlobalOutput,
    original_output_source, selected_mask_eq]
  have options : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 ∨ index = 5 ∨ index = 6 ∨ index = 7 ∨ index = 8 ∨ index = 9 ∨ index = 10 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem boundary_exact : support.boundary = [.input 0, .input 1, .gate 3] :=
  (extractTerminalSupport_boundary original records).trans
    ((terminalBoundaryPorts_reference original.program records).trans (by decide +kernel))

theorem interface_exact : support.interface = [1, 4, 5, 6, 7, 8, 9, 10] :=
  (extractTerminalSupport_interface original records).trans (by
    unfold terminalInterfacePorts
    rw [interface_mask_eq]
    decide +kernel)

theorem selected_gate_count : support.gateCount = 9 :=
  (extractTerminalSupport_gateCount original records).trans (by
    unfold terminalSelectedGates
    rw [selected_mask_eq]
    decide +kernel)

private theorem boundaryPorts_exact :
    terminalBoundaryPorts original.program records = [.input 0, .input 1, .gate 3] :=
  (extractTerminalSupport_boundary original records).symm.trans boundary_exact

private theorem interfacePorts_exact :
    terminalInterfacePorts original records = [1, 4, 5, 6, 7, 8, 9, 10] :=
  (extractTerminalSupport_interface original records).symm.trans interface_exact

private theorem boundaryWidth :
    (terminalBoundaryPorts original.program records).length = 3 :=
  congrArg List.length boundaryPorts_exact

private theorem interfaceWidth :
    (terminalInterfacePorts original records).length = 8 :=
  congrArg List.length interfacePorts_exact

private theorem get_cast_of_eq {α : Type} {left right : List α}
    (same : left = right) (index : Fin right.length) :
    left.get (Fin.cast (congrArg List.length same).symm index) = right.get index := by
  cases same
  rfl

private def fitCandidate {inputs outputs gates nextInputs nextOutputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (inputWidth : nextInputs = inputs) (outputWidth : nextOutputs = outputs) :
    Candidate nextInputs gates nextOutputs := by
  cases inputWidth
  cases outputWidth
  exact candidate

private theorem fitCandidate_semantics
    {inputs outputs gates nextInputs nextOutputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (inputWidth : nextInputs = inputs) (outputWidth : nextOutputs = outputs)
    (input : Valuation nextInputs) (output : Fin nextOutputs) :
    (fitCandidate candidate inputWidth outputWidth).semantics input output =
      candidate.semantics (fun index => input (Fin.cast inputWidth.symm index))
        (Fin.cast outputWidth output) := by
  cases inputWidth
  cases outputWidth
  rfl

private def openInputs
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    Valuation 3 :=
  fun index => input (Fin.cast boundaryWidth.symm index)

def offered : Candidate
    (terminalBoundaryPorts original.program records).length 8
    (terminalInterfacePorts original records).length :=
  fitCandidate smaller boundaryWidth interfaceWidth

private theorem boundary_wire_value
    (input : Valuation (terminalBoundaryPorts original.program records).length)
    (index : Fin 3) :
    terminalOpenWireValue original records input
      (([.input 0, .input 1, .gate 3] : List (TerminalSupportWire 4 11)).get index) =
      openInputs input index := by
  rw [← get_cast_of_eq boundaryPorts_exact index]
  exact terminalOpenWireValue_boundary_get original records input
    (Fin.cast boundaryWidth.symm index)

private theorem boundary_input_zero
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenWireValue original records input (.input 0) = openInputs input 0 :=
  boundary_wire_value input 0

private theorem boundary_input_one
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenWireValue original records input (.input 1) = openInputs input 1 :=
  boundary_wire_value input 1

private theorem boundary_gate_three
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenWireValue original records input (.gate 3) = openInputs input 2 :=
  boundary_wire_value input 2

private theorem selected_source_value
    (input : Valuation (terminalBoundaryPorts original.program records).length)
    (node : Fin 11) (selected : selectedMask node = true) :
    terminalOpenSourceValue original records input (.gate node) =
      terminalOpenGateEvaluation original records input node := by
  simp only [terminalOpenSourceValue, terminalOpenWireValue, selected_mask_eq,
    selected, if_true]

private theorem gate_equation
    (input : Valuation (terminalBoundaryPorts original.program records).length)
    (node : Fin 11) :
    terminalOpenGateEvaluation original records input node =
      if selectedMask node then
        boolNand
          (terminalOpenSourceValue original records input (literalSources node).1)
          (terminalOpenSourceValue original records input (literalSources node).2)
      else false := by
  rw [terminalOpenGateEvaluation_sourceEquation, selected_mask_eq, original_gate_sources]

private theorem first_open_gate
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 0 =
      boolNand (openInputs input 0) (openInputs input 1) := by
  have equation := gate_equation input 0
  change terminalOpenGateEvaluation original records input 0 =
    boolNand (terminalOpenWireValue original records input (.input 0))
      (terminalOpenWireValue original records input (.input 1)) at equation
  rw [boundary_input_zero input, boundary_input_one input] at equation
  exact equation

def openFormula (input : Valuation 3) (output : Fin 8) : Bool :=
  let hidden := boolNand (input 0) (input 1)
  let ab := boolNand hidden hidden
  let azNot := boolNand (input 0) (input 2)
  let az := boolNand azNot azNot
  let azbNot := boolNand az (input 1)
  let zNot := boolNand (input 2) (input 2)
  let anNot := boolNand (input 0) zNot
  let an := boolNand anNot anNot
  let anbNot := boolNand an (input 1)
  match output.val with
  | 0 => ab | 1 => azNot | 2 => az | 3 => azbNot
  | 4 => zNot | 5 => anNot | 6 => an | _ => anbNot

theorem smaller_formula_exact (input : Valuation 3) (output : Fin 8) :
    smaller.semantics input output = openFormula input output := by
  have options : output = 0 ∨ output = 1 ∨ output = 2 ∨ output = 3 ∨
      output = 4 ∨ output = 5 ∨ output = 6 ∨ output = 7 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change boolNand
      (boolNand (boolNand (boolNand (input 0) (input 2))
        (boolNand (input 0) (input 2))) (input 1))
      (boolNand (boolNand
        (boolNand (input 0) (boolNand (input 2) (input 2)))
        (boolNand (input 0) (boolNand (input 2) (input 2)))) (input 1)) =
      boolNand (boolNand (input 0) (input 1)) (boolNand (input 0) (input 1))
    cases input (0 : Fin 3) <;> cases input (1 : Fin 3) <;>
      cases input (2 : Fin 3) <;> rfl
  all_goals rfl

private theorem open_gate_1
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 1 = openFormula (openInputs input) 0 := by
  have equation := gate_equation input 1
  change terminalOpenGateEvaluation original records input 1 =
    boolNand (terminalOpenSourceValue original records input (.gate 0)) (terminalOpenSourceValue original records input (.gate 0)) at equation
  rw [selected_source_value input 0 rfl, first_open_gate] at equation
  exact equation

private theorem open_gate_4
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 4 = openFormula (openInputs input) 1 := by
  have equation := gate_equation input 4
  change terminalOpenGateEvaluation original records input 4 =
    boolNand (terminalOpenWireValue original records input (.input 0)) (terminalOpenWireValue original records input (.gate 3)) at equation
  rw [boundary_input_zero, boundary_gate_three] at equation
  exact equation

private theorem open_gate_5
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 5 = openFormula (openInputs input) 2 := by
  have equation := gate_equation input 5
  change terminalOpenGateEvaluation original records input 5 =
    boolNand (terminalOpenSourceValue original records input (.gate 4)) (terminalOpenSourceValue original records input (.gate 4)) at equation
  rw [selected_source_value input 4 rfl, open_gate_4] at equation
  exact equation

private theorem open_gate_6
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 6 = openFormula (openInputs input) 3 := by
  have equation := gate_equation input 6
  change terminalOpenGateEvaluation original records input 6 =
    boolNand (terminalOpenSourceValue original records input (.gate 5)) (terminalOpenWireValue original records input (.input 1)) at equation
  rw [selected_source_value input 5 rfl, open_gate_5, boundary_input_one] at equation
  exact equation

private theorem open_gate_7
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 7 = openFormula (openInputs input) 4 := by
  have equation := gate_equation input 7
  change terminalOpenGateEvaluation original records input 7 =
    boolNand (terminalOpenWireValue original records input (.gate 3)) (terminalOpenWireValue original records input (.gate 3)) at equation
  rw [boundary_gate_three] at equation
  exact equation

private theorem open_gate_8
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 8 = openFormula (openInputs input) 5 := by
  have equation := gate_equation input 8
  change terminalOpenGateEvaluation original records input 8 =
    boolNand (terminalOpenWireValue original records input (.input 0)) (terminalOpenSourceValue original records input (.gate 7)) at equation
  rw [boundary_input_zero, selected_source_value input 7 rfl, open_gate_7] at equation
  exact equation

private theorem open_gate_9
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 9 = openFormula (openInputs input) 6 := by
  have equation := gate_equation input 9
  change terminalOpenGateEvaluation original records input 9 =
    boolNand (terminalOpenSourceValue original records input (.gate 8)) (terminalOpenSourceValue original records input (.gate 8)) at equation
  rw [selected_source_value input 8 rfl, open_gate_8] at equation
  exact equation

private theorem open_gate_10
    (input : Valuation (terminalBoundaryPorts original.program records).length) :
    terminalOpenGateEvaluation original records input 10 = openFormula (openInputs input) 7 := by
  have equation := gate_equation input 10
  change terminalOpenGateEvaluation original records input 10 =
    boolNand (terminalOpenSourceValue original records input (.gate 9)) (terminalOpenWireValue original records input (.input 1)) at equation
  rw [selected_source_value input 9 rfl, open_gate_9, boundary_input_one] at equation
  exact equation

private theorem get_eq_of_eq {α : Type} {left right : List α}
    (same : left = right) (index : Fin left.length) :
    left.get index = right.get (Fin.cast (congrArg List.length same) index) := by
  cases same
  rfl

private theorem literal_interface_formula
    (input : Valuation (terminalBoundaryPorts original.program records).length)
    (output : Fin 8) :
    terminalOpenGateEvaluation original records input
      (([1, 4, 5, 6, 7, 8, 9, 10] : List (Fin 11)).get output) =
      openFormula (openInputs input) output := by
  have options : output = 0 ∨ output = 1 ∨ output = 2 ∨ output = 3 ∨
      output = 4 ∨ output = 5 ∨ output = 6 ∨ output = 7 := by omega
  rcases options with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact open_gate_1 input
  · exact open_gate_4 input
  · exact open_gate_5 input
  · exact open_gate_6 input
  · exact open_gate_7 input
  · exact open_gate_8 input
  · exact open_gate_9 input
  · exact open_gate_10 input

private theorem gate_interface_formula
    (input : Valuation (terminalBoundaryPorts original.program records).length)
    (output : Fin (terminalInterfacePorts original records).length) :
    terminalOpenGateEvaluation original records input
      ((terminalInterfacePorts original records).get output) =
      openFormula (openInputs input) (Fin.cast interfaceWidth output) :=
  (congrArg (terminalOpenGateEvaluation original records input)
    (get_eq_of_eq interfacePorts_exact output)).trans
      (literal_interface_formula input (Fin.cast interfaceWidth output))

/-- Expose the existing extracted candidate at its proved canonical port types.
    This is the same candidate, not a hand-written replacement of the extractor. -/
private def extractedAtPorts
    {inputs gates outputs profileWidth : Nat}
    (candidate : Candidate inputs gates outputs)
    (selected : List (TerminalPrimitiveRecord inputs gates outputs profileWidth)) :
    Candidate (terminalBoundaryPorts candidate.program selected).length
      (extractTerminalSupport candidate selected).gateCount
      (terminalInterfacePorts candidate selected).length :=
  (extractTerminalSupport candidate selected).extractedCandidate

def comparison := extractedAtPorts original records

private theorem equivalent_of_open_gate_equations
    {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (selected : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program selected).length replacementGates
      (terminalInterfacePorts candidate selected).length)
    (same : ∀ input output,
      replacement.semantics input output =
        terminalOpenGateEvaluation candidate selected input
          ((terminalInterfacePorts candidate selected).get output)) :
    Equivalent replacement.program replacement.directWireWord
      (extractedAtPorts candidate selected).program
      (extractedAtPorts candidate selected).directWireWord := by
  intro input output
  exact (same input output).trans
    (extractTerminalSupport_semantics candidate selected input output).symm

theorem same_open_function :
    Equivalent offered.program offered.directWireWord
      comparison.program comparison.directWireWord := by
  apply equivalent_of_open_gate_equations original records offered
  intro input output
  exact (fitCandidate_semantics smaller boundaryWidth interfaceWidth input output).trans
    ((smaller_formula_exact (openInputs input) (Fin.cast interfaceWidth output)).trans
      (gate_interface_formula input output).symm)

private theorem fitCandidate_minimum
    {inputs outputs gates nextInputs nextOutputs : Nat}
    (candidate : Candidate inputs gates outputs)
    (inputWidth : nextInputs = inputs) (outputWidth : nextOutputs = outputs) :
    referenceMinimum (fitCandidate candidate inputWidth outputWidth).toImplementation =
      referenceMinimum candidate.toImplementation := by
  cases inputWidth
  cases outputWidth
  rfl

private theorem extracted_minimum_of_equivalent
    {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (selected : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program selected).length replacementGates
      (terminalInterfacePorts candidate selected).length)
    (same : Equivalent replacement.program replacement.directWireWord
      (extractedAtPorts candidate selected).program
      (extractedAtPorts candidate selected).directWireWord) :
    referenceMinimum (extractTerminalSupport candidate selected).extractedCandidate.toImplementation =
      referenceMinimum replacement.toImplementation :=
  (referenceMinimum_invariant replacement.toImplementation
    (extractTerminalSupport candidate selected).extractedCandidate.toImplementation same).symm


/-- Exact comparison with the actual extractor; no reference minimum is evaluated. -/
theorem comparison_reference_minimum :
    referenceMinimum support.extractedCandidate.toImplementation =
      referenceMinimum smaller.toImplementation :=
  (extracted_minimum_of_equivalent original records offered same_open_function).trans
    (fitCandidate_minimum smaller boundaryWidth interfaceWidth)

private theorem minimum_rejects_smaller_splice
    {inputs gates outputs profileWidth replacementGates : Nat}
    (candidate : Candidate inputs gates outputs)
    (selected : List (TerminalPrimitiveRecord inputs gates outputs profileWidth))
    (replacement : Candidate
      (terminalBoundaryPorts candidate.program selected).length replacementGates
      (terminalInterfacePorts candidate selected).length)
    (minimum : IsSemanticallyMinimum candidate.toImplementation)
    (saving : replacementGates < (extractTerminalSupport candidate selected).gateCount)
    (same : Equivalent replacement.program replacement.directWireWord
      (extractedAtPorts candidate selected).program
      (extractedAtPorts candidate selected).directWireWord) :
    (ArbitrarySupportSplice.compile candidate selected replacement).isNone = true := by
  cases found : ArbitrarySupportSplice.compile candidate selected replacement with
  | none => rfl
  | some compiled =>
      have preservation := ArbitrarySupportSplice.result_semantics candidate selected replacement
        (funext fun input => funext fun output => same input output) compiled
      have lower := minimum (ArbitrarySupportSplice.result candidate selected replacement compiled)
        preservation
      have gain := ArbitrarySupportSplice.result_strict_gain candidate selected replacement
        saving compiled
      exact False.elim (Nat.not_lt_of_ge lower gain)

theorem literal_splice_is_cyclic :
    (ArbitrarySupportSplice.compile original records offered).isNone = true :=
  minimum_rejects_smaller_splice original records offered original_is_minimum
    (by
      have count : (extractTerminalSupport original records).gateCount = 9 := selected_gate_count
      omega) same_open_function

end PNP.DirectWire.CompatibleSupportSlackObstruction
