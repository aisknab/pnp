/-
Copyright (c) 2026 PNP Labs.

Literal loading from the existing all-input frame into a register bank.
Empty input is normalized by a transition; fixed empty fields and the outer
bank marker are written by finite machines. The final store is derived from
the program input index. Exterior cells consumed by prefix installation are
recorded exactly. No layout or correctness certificate is an input.
-/

import PNP.Concrete.BitRegisterIOPrimitives

namespace PNP.Concrete.BitRegister.IOAdapter

open TapePrimitive Mutation Operation WorkMachineProgramGraph PipelineStateNamespace

private theorem pipeline_bit (bit : Bool) :
    PipelineTape.dataSymbol (TapeSymbol.ofBool bit) = Store.bitSymbol bit := rfl

private theorem pipeline_bits :
    (PipelineTape.dataSymbol ∘ TapeSymbol.ofBool) = Store.bitSymbol := rfl

private theorem pipeline_left : PipelineTape.leftMarker = WorkSymbol.blankZero := rfl
private theorem pipeline_right : PipelineTape.rightMarker = Store.separator := rfl
private theorem home_start : home.startState = 4 := rfl
private theorem home_accept : home.acceptState = 1 := rfl
private theorem scan_start : scanInput.startState = 0 := rfl

theorem replicate_cons (count : Nat) (symbol : WorkSymbol) (right : List WorkSymbol) :
    List.replicate count symbol ++ symbol :: right =
      symbol :: (List.replicate count symbol ++ right) := by
  calc
    _ = (List.replicate count symbol ++ [symbol]) ++ right :=
      (List.append_assoc _ _ _).symm
    _ = List.replicate (count + 1) symbol ++ right := by rw [List.replicate_succ']
    _ = symbol :: (List.replicate count symbol ++ right) := by
      rw [List.replicate_succ]
      rfl

theorem reverseOnto_replicate (count : Nat) (symbol : WorkSymbol) (right : List WorkSymbol) :
    reverseOnto (List.replicate count symbol) right = List.replicate count symbol ++ right := by
  induction count generalizing right with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, reverseOnto, ih, List.cons_append]
      exact replicate_cons count symbol right

def scanFinalTape (input : BitString) (outside : List WorkSymbol) : WorkTape :=
  ⟨Store.separator :: reverseOnto (input.map Store.bitSymbol) (WorkSymbol.blankZero :: outside),
    if input.isEmpty then Store.separator else WorkSymbol.blank, []⟩

theorem scanInput_framed_run (input : BitString) (outside : List WorkSymbol) :
    workRunExact? scanInput (input.length + 1)
      ⟨0, PipelineTape.frameWithGarbage (Tape.ofInput input) outside []⟩ =
      some ⟨1, scanFinalTape input outside⟩ := by
  cases input with
  | nil => rfl
  | cons bit rest =>
      simpa only [PipelineTape.frameWithGarbage, Tape.ofInput, List.map_map, List.map_cons,
        List.map_nil, List.nil_append, List.cons_append, scanFinalTape,
        List.isEmpty_cons, Bool.false_eq_true, ite_false, focus,
        pipeline_bit, pipeline_bits, pipeline_left, pipeline_right] using
        scanInput_word_run (bit :: rest) (WorkSymbol.blankZero :: outside) []

def suffixTape (input : BitString) (afterCount : Nat) (outside : List WorkSymbol) : WorkTape :=
  focus (reverseOnto (input.map Store.bitSymbol ++ List.replicate afterCount Store.separator)
    (WorkSymbol.blankZero :: outside)) [Store.separator, rightBoundary]

theorem appendFields_framed_run (input : BitString) (afterCount : Nat) (outside : List WorkSymbol) :
    workRunExact? (appendFields afterCount) (2 * afterCount + 1)
      ⟨(appendFields afterCount).startState, scanFinalTape input outside⟩ =
      some ⟨(appendFields afterCount).acceptState, suffixTape input afterCount outside⟩ := by
  simpa only [scanFinalTape, suffixTape, reverseOnto_append, reverseOnto_replicate,
    replicate_cons, focusLeft, focus] using
    appendFields_run afterCount
      (Store.separator :: reverseOnto (input.map Store.bitSymbol) (WorkSymbol.blankZero :: outside))
      (if input.isEmpty then Store.separator else WorkSymbol.blank)

def loadedTape (input : BitString) (beforeCount afterCount : Nat)
    (outside : List WorkSymbol) : WorkTape :=
  ⟨outside.drop beforeCount, WorkSymbol.blankZero,
    List.replicate beforeCount Store.separator ++ input.map Store.bitSymbol ++
      List.replicate (afterCount + 1) Store.separator ++ [rightBoundary]⟩

theorem home_suffix_run (input : BitString) (afterCount : Nat) (outside : List WorkSymbol) :
    workRunExact? home (input.length + afterCount + 2)
      ⟨home.startState, suffixTape input afterCount outside⟩ =
      some ⟨home.acceptState, loadedTape input 0 afterCount outside⟩ := by
  have h := home_run (bitCells input ++ List.replicate afterCount Cell.separator)
    Cell.separator outside [rightBoundary]
  simpa only [suffixTape, loadedTape, home_start, home_accept, List.drop_zero, List.replicate_zero, List.nil_append,
    List.length_append, bitCells_length, List.length_replicate, List.map_append,
    bitCells_symbols, List.map_replicate, Cell.symbol, List.replicate_succ',
    List.append_assoc, List.cons_append, List.nil_append] using h

def loadFields (beforeCount afterCount : Nat) : WorkMachine :=
  WorkMachineChain.machine scanInput (WorkMachineChain.machine (appendFields afterCount)
    (WorkMachineChain.machine home (prependFields beforeCount)))

theorem loadFields_wellFormed (beforeCount afterCount : Nat) :
    ProgramWellFormed (loadFields beforeCount afterCount) :=
  chain_wellFormed _ _ scanInput_wellFormed
    (chain_wellFormed _ _ (appendFields_wellFormed afterCount)
      (chain_wellFormed _ _ home_wellFormed (prependFields_wellFormed beforeCount)))

def loadFieldsSteps (inputLength beforeCount afterCount : Nat) : Nat :=
  2 * inputLength + 3 * afterCount + 2 * beforeCount + 8

theorem loadFields_run (input : BitString) (beforeCount afterCount : Nat)
    (outside : List WorkSymbol) :
    workRunExact? (loadFields beforeCount afterCount)
      (loadFieldsSteps input.length beforeCount afterCount)
      ⟨(loadFields beforeCount afterCount).startState,
        PipelineTape.frameWithGarbage (Tape.ofInput input) outside []⟩ =
      some ⟨(loadFields beforeCount afterCount).acceptState,
        loadedTape input beforeCount afterCount outside⟩ := by
  have hScan := scanInput_framed_run input outside
  have hAppend := appendFields_framed_run input afterCount outside
  have hHome := home_suffix_run input afterCount outside
  have hPrefix := prependFields_run beforeCount outside WorkSymbol.blankZero
    (input.map Store.bitSymbol ++ List.replicate (afterCount + 1) Store.separator ++ [rightBoundary])
  have hEnd := WorkMachineChain.workRunExact home (prependFields beforeCount)
    (input.length + afterCount + 2) (2 * beforeCount + 1) _ _ _ hHome rfl hPrefix
  have hBody := WorkMachineChain.workRunExact (appendFields afterCount)
    (WorkMachineChain.machine home (prependFields beforeCount))
    (2 * afterCount + 1) (input.length + afterCount + 2 + 1 + (2 * beforeCount + 1))
    _ _ _ hAppend rfl hEnd
  have hAll := WorkMachineChain.workRunExact scanInput
    (WorkMachineChain.machine (appendFields afterCount)
      (WorkMachineChain.machine home (prependFields beforeCount)))
    (input.length + 1)
    (2 * afterCount + 1 + 1 + (input.length + afterCount + 2 + 1 + (2 * beforeCount + 1)))
    _ _ _ hScan rfl hBody
  have cost : input.length + 1 + 1 +
      (2 * afterCount + 1 + 1 + (input.length + afterCount + 2 + 1 + (2 * beforeCount + 1))) =
      loadFieldsSteps input.length beforeCount afterCount := by
    unfold loadFieldsSteps
    omega
  rw [cost] at hAll
  simpa only [loadFields, WorkMachineChain.machine, renameConfiguration, loadedTape,
    List.append_assoc, scan_start] using hAll

theorem empty_encode (count : Nat) :
    (Store.empty count).encode = List.replicate count Store.separator := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [Store.empty, Store.encode, List.map_nil, List.nil_append, ih, List.replicate_succ]

theorem initial_encode (count : Nat) (index : Fin count) (input : BitString) :
    ((Store.empty count).set index input).encode =
      List.replicate index.val Store.separator ++ input.map Store.bitSymbol ++
        Store.separator :: List.replicate (count - index.val - 1) Store.separator := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count ih =>
      cases index using Fin.cases with
      | zero =>
          simp only [Store.empty, Store.set_cons_zero, Store.encode, empty_encode, Fin.val_zero,
            List.replicate_zero, List.nil_append, Nat.sub_zero, Nat.add_sub_cancel]
      | succ index =>
          simp only [Store.empty, Store.set_cons_succ, Store.encode, List.map_nil, List.nil_append,
            ih, Fin.val_succ, List.replicate_succ, List.cons_append, Nat.add_sub_add_right]

theorem loadedTape_initial {count : Nat} (program : Program count) (input : BitString)
    (outside : List WorkSymbol) :
    loadedTape input (program.input.val + 1) (count - program.input.val - 1) outside =
      (Compiler.scratchStore (initial program input).store).tape
        (outside.drop (program.input.val + 1)) 0 := by
  simp only [loadedTape, Compiler.scratchStore, initial, Store.tape, Store.encode,
    List.map_nil, List.nil_append, initial_encode, tail, List.replicate_zero,
    List.replicate_succ, List.cons_append, List.append_assoc]

def loadProgram {count : Nat} (program : Program count) : WorkMachine :=
  loadFields (program.input.val + 1) (count - program.input.val - 1)

theorem loadProgram_wellFormed {count : Nat} (program : Program count) :
    ProgramWellFormed (loadProgram program) :=
  loadFields_wellFormed _ _

def loadProgramSteps {count : Nat} (program : Program count) (inputLength : Nat) : Nat :=
  loadFieldsSteps inputLength (program.input.val + 1) (count - program.input.val - 1)

theorem loadProgram_run {count : Nat} (program : Program count) (input : BitString)
    (outside : List WorkSymbol) :
    workRunExact? (loadProgram program) (loadProgramSteps program input.length)
      ⟨(loadProgram program).startState, PipelineTape.frameWithGarbage (Tape.ofInput input) outside []⟩ =
      some ⟨(loadProgram program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape
          (outside.drop (program.input.val + 1)) 0⟩ := by
  have h := loadFields_run input (program.input.val + 1) (count - program.input.val - 1) outside
  rw [loadedTape_initial] at h
  exact h

theorem loadProgramSteps_le {count : Nat} (program : Program count) (inputLength : Nat) :
    loadProgramSteps program inputLength ≤ 2 * inputLength + 3 * count + 8 := by
  have indexBound := program.input.isLt
  simp only [loadProgramSteps, loadFieldsSteps]
  omega

def inputAdapter {count : Nat} (program : Program count) : WorkMachine :=
  WorkMachineChain.machine PipelineInputFramer.pairedInputFramer (loadProgram program)

theorem inputAdapter_wellFormed {count : Nat} (program : Program count) :
    ProgramWellFormed (inputAdapter program) :=
  chain_wellFormed _ _ inputFramer_wellFormed (loadProgram_wellFormed program)

def inputAdapterSteps {count : Nat} (program : Program count) (input : BitString) : Nat :=
  PipelineInputFramer.totalInputFramerWorkSteps input + 1 + loadProgramSteps program input.length

def inputOutside {count : Nat} (program : Program count) (input : BitString) : List WorkSymbol :=
  (PipelineInputFramer.totalInputFramerOutsideLeft input).drop (program.input.val + 1)

theorem inputAdapter_run {count : Nat} (program : Program count) (input : BitString) :
    workRunExact? (inputAdapter program) (inputAdapterSteps program input)
      ⟨(inputAdapter program).startState, rawInputWorkTape input⟩ =
      some ⟨(inputAdapter program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0⟩ := by
  have h := WorkMachineChain.workRunExact PipelineInputFramer.pairedInputFramer (loadProgram program)
    (PipelineInputFramer.totalInputFramerWorkSteps input) (loadProgramSteps program input.length)
    _ _ _ (PipelineInputFramer.totalInputFramer_workRunExact input) rfl
    (loadProgram_run program input (PipelineInputFramer.totalInputFramerOutsideLeft input))
  exact h

theorem inputAdapter_raw_run {count : Nat} (program : Program count) (input : BitString) :
    PNP.Concrete.run (compileWorkMachine (inputAdapter program)) (6 * inputAdapterSteps program input)
      (encodeWorkConfiguration ⟨(inputAdapter program).startState, rawInputWorkTape input⟩) =
      encodeWorkConfiguration ⟨(inputAdapter program).acceptState,
        (Compiler.scratchStore (initial program input).store).tape (inputOutside program input) 0⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (inputAdapter_run program input)

end PNP.Concrete.BitRegister.IOAdapter
