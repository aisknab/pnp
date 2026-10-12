/-
Copyright (c) 2026 PNP Labs.

Literal selected-register output extraction and raw packing.
The output stage deliberately reclaims adjacent workspace cells to install
the packer's markers. Every consumed exterior cell is recorded in the exact
final tape; no tape identity is silently strengthened. Empty words require
four preparation transitions, while nonempty words require two.
-/

import PNP.Concrete.BitRegisterInput

namespace PNP.Concrete.BitRegister.IOAdapter

open TapePrimitive Mutation Operation WorkMachineProgramGraph PipelineStateNamespace

theorem packerInput_nil (left right : List WorkSymbol) :
    TerminalOutputPacker.terminalOutputPackerInputTape [] left right =
      ⟨WorkSymbol.blankZero :: left, WorkSymbol.blank, Store.separator :: right⟩ := rfl

theorem packerInput_cons (bit : Bool) (rest : BitString) (left right : List WorkSymbol) :
    TerminalOutputPacker.terminalOutputPackerInputTape (bit :: rest) left right =
      ⟨WorkSymbol.blankZero :: left, Store.bitSymbol bit,
        rest.map Store.bitSymbol ++ Store.separator :: right⟩ := by
  simp only [TerminalOutputPacker.terminalOutputPackerInputTape,
    PipelineTape.frameWithGarbage, Tape.ofInput, List.map_map, List.map_nil, List.nil_append]
  rfl

def frameWord : WorkMachine :=
  { rules := [
      ⟨0, Store.bitSymbol false, 1, Store.bitSymbol false, .left⟩,
      ⟨0, Store.bitSymbol true, 1, Store.bitSymbol true, .left⟩,
      ⟨0, Store.separator, 2, WorkSymbol.blank, .left⟩] ++
      PipelineMachineSimulation.allWorkSymbols.map (fun read => ⟨1, read, 5, WorkSymbol.blankZero, .right⟩) ++
      PipelineMachineSimulation.allWorkSymbols.map (fun read => ⟨2, read, 3, WorkSymbol.blankZero, .right⟩) ++
      [⟨3, WorkSymbol.blank, 4, WorkSymbol.blank, .right⟩] ++
      PipelineMachineSimulation.allWorkSymbols.map (fun read => ⟨4, read, 5, Store.separator, .left⟩)
    startState := 0, acceptState := 5, rejectState := 6 }

set_option maxRecDepth 4096 in
theorem frameWord_wellFormed : ProgramWellFormed frameWord := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

theorem frameWord_bit_step (bit : Bool) (left right : List WorkSymbol) :
    workStep? frameWord ⟨0, ⟨left, Store.bitSymbol bit, right⟩⟩ =
      some ⟨1, (⟨left, Store.bitSymbol bit, right⟩ : WorkTape).moveLeft⟩ := by
  cases bit <;> rfl

theorem frameWord_empty_step (left right : List WorkSymbol) :
    workStep? frameWord ⟨0, ⟨left, Store.separator, right⟩⟩ =
      some ⟨2, (⟨left, WorkSymbol.blank, right⟩ : WorkTape).moveLeft⟩ := rfl

theorem frameWord_accept_left_step (tape : WorkTape) :
    workStep? frameWord ⟨1, tape⟩ =
      some ⟨5, (tape.write WorkSymbol.blankZero).moveRight⟩ := by
  cases tape with
  | mk left head right =>
      cases head with
      | mk first second => cases first <;> cases second <;> rfl

theorem frameWord_continue_left_step (tape : WorkTape) :
    workStep? frameWord ⟨2, tape⟩ =
      some ⟨3, (tape.write WorkSymbol.blankZero).moveRight⟩ := by
  cases tape with
  | mk left head right =>
      cases head with
      | mk first second => cases first <;> cases second <;> rfl

theorem frameWord_blank_step (left right : List WorkSymbol) :
    workStep? frameWord ⟨3, ⟨left, WorkSymbol.blank, right⟩⟩ =
      some ⟨4, (⟨left, WorkSymbol.blank, right⟩ : WorkTape).moveRight⟩ := rfl

theorem frameWord_right_step (tape : WorkTape) :
    workStep? frameWord ⟨4, tape⟩ =
      some ⟨5, (tape.write Store.separator).moveLeft⟩ := by
  cases tape with
  | mk left head right =>
      cases head with
      | mk first second => cases first <;> cases second <;> rfl

theorem frameWord_cons_run (bit : Bool) (rest : BitString) (left right : List WorkSymbol) :
    workRunExact? frameWord 2
      ⟨0, focus left ((bit :: rest).map Store.bitSymbol ++ Store.separator :: right)⟩ =
      some ⟨5, TerminalOutputPacker.terminalOutputPackerInputTape (bit :: rest) left.tail right⟩ := by
  have first := exact_one (frameWord_bit_step bit left (rest.map Store.bitSymbol ++ Store.separator :: right))
  have second := exact_one (frameWord_accept_left_step
    ((⟨left, Store.bitSymbol bit, rest.map Store.bitSymbol ++ Store.separator :: right⟩ : WorkTape).moveLeft))
  have checked := PipelineMachineSimulation.workRunExact?_compose frameWord 1 1 _ _ _ first second
  cases left <;>
    simpa only [packerInput_cons, List.map_cons, List.cons_append, focus,
      List.tail_nil, List.tail_cons, WorkTape.moveLeft, WorkTape.write, WorkTape.moveRight] using checked

theorem frameWord_empty_prepare_run (left right : List WorkSymbol) :
    workRunExact? frameWord 2 ⟨0, ⟨left, Store.separator, right⟩⟩ =
      some ⟨3, ⟨WorkSymbol.blankZero :: left.tail, WorkSymbol.blank, right⟩⟩ := by
  have first := exact_one (frameWord_empty_step left right)
  have second := exact_one (frameWord_continue_left_step
    ((⟨left, WorkSymbol.blank, right⟩ : WorkTape).moveLeft))
  have checked := PipelineMachineSimulation.workRunExact?_compose frameWord 1 1 _ _ _ first second
  cases left <;>
    simpa only [List.tail_nil, List.tail_cons, WorkTape.moveLeft, WorkTape.write, WorkTape.moveRight] using checked

theorem frameWord_empty_finish_run (left right : List WorkSymbol) :
    workRunExact? frameWord 2 ⟨3, ⟨left, WorkSymbol.blank, right⟩⟩ =
      some ⟨5, ⟨left, WorkSymbol.blank, Store.separator :: right.tail⟩⟩ := by
  have first := exact_one (frameWord_blank_step left right)
  have second := exact_one (frameWord_right_step
    ((⟨left, WorkSymbol.blank, right⟩ : WorkTape).moveRight))
  have checked := PipelineMachineSimulation.workRunExact?_compose frameWord 1 1 _ _ _ first second
  cases right <;>
    simpa only [List.tail_nil, List.tail_cons, WorkTape.moveLeft, WorkTape.write, WorkTape.moveRight] using checked

theorem frameWord_nil_run (left right : List WorkSymbol) :
    workRunExact? frameWord 4 ⟨0, focus left (Store.separator :: right)⟩ =
      some ⟨5, TerminalOutputPacker.terminalOutputPackerInputTape [] left.tail right.tail⟩ := by
  rw [packerInput_nil]
  exact PipelineMachineSimulation.workRunExact?_compose frameWord 2 2 _ _ _
    (frameWord_empty_prepare_run left right)
    (frameWord_empty_finish_run (WorkSymbol.blankZero :: left.tail) right)

def frameWordSteps (bits : BitString) : Nat := if bits.isEmpty then 4 else 2

def frameRight (bits : BitString) (right : List WorkSymbol) : List WorkSymbol :=
  if bits.isEmpty then right.tail else right

theorem frameWord_run (bits : BitString) (left right : List WorkSymbol) :
    workRunExact? frameWord (frameWordSteps bits)
      ⟨0, focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩ =
      some ⟨5, TerminalOutputPacker.terminalOutputPackerInputTape bits left.tail (frameRight bits right)⟩ := by
  cases bits with
  | nil => exact frameWord_nil_run left right
  | cons bit rest => exact frameWord_cons_run bit rest left right

theorem frameWordSteps_le (bits : BitString) : frameWordSteps bits ≤ 4 := by
  unfold frameWordSteps; split <;> decide

def outputAt (index : Nat) : WorkMachine :=
  WorkMachineChain.machine (seekFromBoundary index)
    (WorkMachineChain.machine frameWord TerminalOutputPacker.terminalOutputPacker)

theorem outputAt_wellFormed (index : Nat) : ProgramWellFormed (outputAt index) :=
  chain_wellFormed _ _ (seekFromBoundary_wellFormed index)
    (chain_wellFormed _ _ frameWord_wellFormed outputPacker_wellFormed)

def outputAtSteps {count : Nat} (store : Store count) (index : Fin count) : Nat :=
  (2 + seekSteps (store.beforeFields index)) + 1 +
    (frameWordSteps (store.get index) + 1 +
      TerminalOutputPacker.terminalOutputPackerWorkSteps (store.get index))

def outputLeft {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) : List WorkSymbol :=
  (reverseOnto (fieldWord (store.beforeFields index)) (WorkSymbol.blankZero :: outside)).tail

def outputRight {count : Nat} (store : Store count) (index : Fin count) (slack : Nat) : List WorkSymbol :=
  frameRight (store.get index) ((fieldCells (store.afterFields index)).map Cell.symbol ++ tail slack)

def outputTape {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) : WorkTape :=
  TerminalOutputPacker.terminalOutputPackerFinalTape (store.get index)
    (outputLeft store index outside) (outputRight store index slack)

theorem outputAt_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? (outputAt index.val) (outputAtSteps store index)
      ⟨(outputAt index.val).startState, store.tape outside slack⟩ =
      some ⟨(outputAt index.val).acceptState, outputTape store index outside slack⟩ := by
  have hSeek := seekFromBoundary_run (store.beforeFields index) outside
    ((store.get index).map Store.bitSymbol ++ Store.separator ::
      ((fieldCells (store.afterFields index)).map Cell.symbol ++ tail slack))
  have hFrame := frameWord_run (store.get index)
    (reverseOnto (fieldWord (store.beforeFields index)) (WorkSymbol.blankZero :: outside))
    ((fieldCells (store.afterFields index)).map Cell.symbol ++ tail slack)
  have hPack := TerminalOutputPacker.terminalOutputPacker_workRunExact (store.get index)
    (outputLeft store index outside) (outputRight store index slack)
  have hEnd := WorkMachineChain.workRunExact frameWord TerminalOutputPacker.terminalOutputPacker
    (frameWordSteps (store.get index))
    (TerminalOutputPacker.terminalOutputPackerWorkSteps (store.get index)) _ _ _ hFrame rfl hPack
  have hAll := WorkMachineChain.workRunExact (seekFromBoundary (store.beforeFields index).length)
    (WorkMachineChain.machine frameWord TerminalOutputPacker.terminalOutputPacker)
    (2 + seekSteps (store.beforeFields index))
    (frameWordSteps (store.get index) + 1 + TerminalOutputPacker.terminalOutputPackerWorkSteps (store.get index))
    _ _ _ hSeek rfl hEnd
  rw [Store.tape_boundary store index outside slack]
  simpa only [outputAt, outputAtSteps, outputTape, Store.beforeFields_length,
    WorkMachineChain.machine, renameConfiguration, atBoundary, content,
    TerminalOutputPacker.terminalOutputPackerFinalConfiguration] using hAll

theorem outputAt_raw_run {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine (outputAt index.val)) (6 * outputAtSteps store index)
      (encodeWorkConfiguration ⟨(outputAt index.val).startState, store.tape outside slack⟩) =
      encodeWorkConfiguration ⟨(outputAt index.val).acceptState, outputTape store index outside slack⟩ :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (outputAt_run store index outside slack)

theorem outputTape_output {count : Nat} (store : Store count) (index : Fin count)
    (outside : List WorkSymbol) (slack : Nat) :
    (encodeWorkTape (outputTape store index outside slack)).outputBits = store.get index :=
  TerminalOutputPacker.terminalOutputPacker_output_eq _ _ _

end PNP.Concrete.BitRegister.IOAdapter
