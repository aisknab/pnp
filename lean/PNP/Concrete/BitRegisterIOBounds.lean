/-
Copyright (c) 2026 PNP Labs.

Uniform encoded-size bounds for the literal register input/output adapters.
The input theorem starts at ordinary raw input, including odd and empty words.
The output budget is quadratic in the complete encoded store span.
These adapters do not establish source-program termination.
-/

import PNP.Concrete.BitRegisterOutput

namespace PNP.Concrete.BitRegister.IOAdapter

open Operation

def inputRawBound (count : Nat) : NatPolynomial :=
  .add PipelineInputFramer.totalInputFramerRawTimeBound (.linear 12 (18 * count + 54))

theorem inputAdapter_rawSteps_le {count : Nat} (program : Program count) (input : BitString) :
    6 * inputAdapterSteps program input ≤ (inputRawBound count).eval input.length := by
  have framed := PipelineInputFramer.totalInputFramerRawTimeBound_le input
  have loaded := loadProgramSteps_le program input.length
  simp only [inputAdapterSteps, inputRawBound, NatPolynomial.eval_add,
    NatPolynomial.eval_linear, BitString.size] at *
  omega

theorem accept_isHalted (machine : WorkMachine) (tape : WorkTape) :
    machine.isHalted ⟨machine.acceptState, tape⟩ = true := by
  change ((machine.acceptState == machine.acceptState) || _) = true
  rw [(nat_beq_true_iff machine.acceptState machine.acceptState).mpr rfl]
  rfl

theorem inputAdapter_run_budget {count : Nat} (program : Program count) (input : BitString) :
    PNP.Concrete.run (compileWorkMachine (inputAdapter program))
      ((inputRawBound count).eval input.length)
      (encodeWorkConfiguration ⟨(inputAdapter program).startState, rawInputWorkTape input⟩) =
      encodeWorkConfiguration ⟨(inputAdapter program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0⟩ :=
  run_compileWorkMachine_of_workRunExact_halted_le _ _ _ _ _
    (inputAdapter_run program input) (accept_isHalted _ _)
    (inputAdapter_rawSteps_le program input)

theorem inputAdapter_start_run {count : Nat} (program : Program count) (input : BitString) :
    PNP.Concrete.Configuration.BlankEquivalent
      (PNP.Concrete.run (compileWorkMachine (inputAdapter program))
        ((inputRawBound count).eval input.length)
        (startConfig (compileWorkMachine (inputAdapter program)) input))
      (encodeWorkConfiguration ⟨(inputAdapter program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0⟩) := by
  have checked := run_blankEquivalent (compileWorkMachine (inputAdapter program))
    ((inputRawBound count).eval input.length)
    (startConfig_compileWorkMachine_blankEquivalent (inputAdapter program) input)
  simp only [workStartConfiguration] at checked
  rw [inputAdapter_run_budget program input] at checked
  exact checked

theorem inputAdapter_accepts {count : Nat} (program : Program count) (input : BitString) :
    boundedDecide (compileWorkMachine (inputAdapter program))
      ((inputRawBound count).eval input.length) input = .accept := by
  apply (boundedDecide_accept_iff_final _ _ _).mpr
  exact (inputAdapter_start_run program input).1

def outputRawBound : NatPolynomial :=
  .add TerminalOutputPacker.terminalOutputPackerRawTimeBound (.linear 12 48)

theorem outputRawBound_eval (span : Nat) :
    outputRawBound.eval span = 18 * span * span + 48 * span + 54 := by
  simp only [outputRawBound, TerminalOutputPacker.terminalOutputPackerRawTimeBound,
    NatPolynomial.eval_add, NatPolynomial.eval_quadratic, NatPolynomial.eval_linear]
  omega

theorem get_length_le_span {count : Nat} (store : Store count) (index : Fin count) :
    (store.get index).length ≤ store.span := by
  have split := Store.span_split store index
  omega

theorem seekSteps_le_span {count : Nat} (store : Store count) (index : Fin count) :
    seekSteps (store.beforeFields index) ≤ 2 * store.span := by
  have split := Store.span_split store index
  have delimiters := fieldCells_length_ge (store.beforeFields index)
  simp only [seekSteps, fieldWord_length]
  omega

theorem outputAt_rawSteps_le {count : Nat} (store : Store count) (index : Fin count) :
    6 * outputAtSteps store index ≤ outputRawBound.eval store.span := by
  have sought := seekSteps_le_span store index
  have framed := frameWordSteps_le (store.get index)
  have packed := Nat.le_trans (TerminalOutputPacker.terminalOutputPacker_runtime_le (store.get index))
    (NatPolynomial.eval_mono TerminalOutputPacker.terminalOutputPackerRawTimeBound
      (get_length_le_span store index))
  simp only [outputAtSteps, outputRawBound, NatPolynomial.eval_add, NatPolynomial.eval_linear]
  omega

theorem outputAt_run_budget {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (outputAt index.val))
      (outputRawBound.eval store.span)
      (encodeWorkConfiguration ⟨(outputAt index.val).startState, store.tape outside slack⟩) =
      encodeWorkConfiguration ⟨(outputAt index.val).acceptState, outputTape store index outside slack⟩ :=
  run_compileWorkMachine_of_workRunExact_halted_le _ _ _ _ _
    (outputAt_run store index outside slack) (accept_isHalted _ _)
    (outputAt_rawSteps_le store index)

theorem outputAt_output_budget {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    (PNP.Concrete.run (compileWorkMachine (outputAt index.val))
      (outputRawBound.eval store.span)
      (encodeWorkConfiguration ⟨(outputAt index.val).startState, store.tape outside slack⟩)).tape.outputBits =
      store.get index := by
  rw [outputAt_run_budget store index outside slack]
  exact outputTape_output store index outside slack

end PNP.Concrete.BitRegister.IOAdapter
