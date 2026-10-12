/-
Copyright (c) 2026 PNP Labs.

Finite layout writers for the register compiler input/output boundary.
Every write has a literal nine-symbol rule table. Fixed register counts
determine program syntax; input lengths do not unroll the machine.

The prefix writer records which exterior cells it consumes. The suffix
writer installs the distinct bank boundary. These are layout components,
not a claim that the complete input/output adapter is already connected.
-/

import PNP.Concrete.BitRegisterCompilerExecution
import PNP.Concrete.PipelineInputFramer
import PNP.Concrete.TerminalOutputPacker

namespace PNP.Concrete.BitRegister.IOAdapter

open TapePrimitive Mutation Operation WorkMachineProgramGraph PipelineStateNamespace

theorem inputFramer_wellFormed : ProgramWellFormed PipelineInputFramer.pairedInputFramer := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

set_option maxRecDepth 4096 in
theorem outputPacker_wellFormed : ProgramWellFormed TerminalOutputPacker.terminalOutputPacker := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

def writeAny (symbol : WorkSymbol) (move : HeadMove) : WorkMachine :=
  { rules := PipelineMachineSimulation.allWorkSymbols.map
      (fun read => ⟨0, read, 1, symbol, move⟩)
    startState := 0, acceptState := 1, rejectState := 2 }

theorem writeAny_start (symbol : WorkSymbol) (move : HeadMove) :
    (writeAny symbol move).startState = 0 := rfl

theorem writeAny_wellFormed (symbol : WorkSymbol) (move : HeadMove) :
    ProgramWellFormed (writeAny symbol move) := by
  refine ⟨?_, noRuleAt_of_all _ _ (by rfl), noRuleAt_of_all _ _ (by rfl), ?_⟩
  · have distinct : PipelineMachineSimulation.allWorkSymbols.Pairwise
        (fun left right => ((0, left) : Nat × WorkSymbol) ≠ (0, right)) := by decide
    exact List.Pairwise.map (fun read => (⟨0, read, 1, symbol, move⟩ : WorkRule))
      (fun _ _ h => h) distinct
  · change (1 : Nat) ≠ 2
    decide

theorem writeAny_run (symbol : WorkSymbol) (move : HeadMove) (tape : WorkTape) :
    workRunExact? (writeAny symbol move) 1 ⟨0, tape⟩ =
      some ⟨1, (tape.write symbol).move move⟩ := by
  cases tape with
  | mk left head right =>
      cases head with
      | mk first second => cases first <;> cases second <;> rfl

theorem writeAny_left_run (symbol : WorkSymbol) (left : List WorkSymbol)
    (head : WorkSymbol) (right : List WorkSymbol) :
    workRunExact? (writeAny symbol .left) 1 ⟨0, ⟨left, head, right⟩⟩ =
      some ⟨1, ⟨left.tail, left.headD WorkSymbol.blank, symbol :: right⟩⟩ := by
  cases left <;> exact writeAny_run symbol .left _

def prependFields : Nat → WorkMachine
  | 0 => writeAny WorkSymbol.blankZero .stay
  | count + 1 => WorkMachineChain.machine (writeAny Store.separator .left) (prependFields count)

theorem prependFields_wellFormed (count : Nat) : ProgramWellFormed (prependFields count) := by
  induction count with
  | zero => exact writeAny_wellFormed _ _
  | succ count ih => exact chain_wellFormed _ _ (writeAny_wellFormed _ _) ih

theorem prependFields_run (count : Nat) (left : List WorkSymbol)
    (head : WorkSymbol) (right : List WorkSymbol) :
    workRunExact? (prependFields count) (2 * count + 1)
      ⟨(prependFields count).startState, ⟨left, head, right⟩⟩ =
      some ⟨(prependFields count).acceptState,
        ⟨left.drop count, WorkSymbol.blankZero, List.replicate count Store.separator ++ right⟩⟩ := by
  induction count generalizing left head right with
  | zero => exact writeAny_run WorkSymbol.blankZero .stay _
  | succ count ih =>
      have hFirst := writeAny_left_run Store.separator left head right
      have hNext := ih left.tail (left.headD WorkSymbol.blank) (Store.separator :: right)
      have hAll := WorkMachineChain.workRunExact (writeAny Store.separator .left) (prependFields count)
        1 (2 * count + 1) _ _ _ hFirst rfl hNext
      have cost : 1 + 1 + (2 * count + 1) = 2 * (count + 1) + 1 := by omega
      rw [cost] at hAll
      have word : List.replicate (count + 1) Store.separator ++ right =
          List.replicate count Store.separator ++ Store.separator :: right := by
        rw [List.replicate_succ', List.append_assoc]
        rfl
      rw [word]
      cases left <;>
        simpa only [prependFields, WorkMachineChain.machine, renameConfiguration, writeAny_start,
          List.tail_nil, List.headD_nil, List.drop_nil, List.tail_cons, List.headD_cons,
          List.drop_succ_cons] using hAll

def appendFields : Nat → WorkMachine
  | 0 => writeAny rightBoundary .left
  | count + 1 => WorkMachineChain.machine (writeAny Store.separator .right) (appendFields count)

theorem appendFields_wellFormed (count : Nat) : ProgramWellFormed (appendFields count) := by
  induction count with
  | zero => exact writeAny_wellFormed _ _
  | succ count ih => exact chain_wellFormed _ _ (writeAny_wellFormed _ _) ih

theorem appendFields_run (count : Nat) (left : List WorkSymbol) (head : WorkSymbol) :
    workRunExact? (appendFields count) (2 * count + 1)
      ⟨(appendFields count).startState, ⟨left, head, []⟩⟩ =
      some ⟨(appendFields count).acceptState,
        focusLeft (reverseOnto (List.replicate count Store.separator) left) [rightBoundary]⟩ := by
  induction count generalizing left head with
  | zero =>
      cases left <;> exact writeAny_run rightBoundary .left _
  | succ count ih =>
      have hFirst := writeAny_run Store.separator .right (⟨left, head, []⟩ : WorkTape)
      have hNext := ih (Store.separator :: left) WorkSymbol.blank
      have hAll := WorkMachineChain.workRunExact (writeAny Store.separator .right) (appendFields count)
        1 (2 * count + 1) _ _ _ hFirst rfl hNext
      have cost : 1 + 1 + (2 * count + 1) = 2 * (count + 1) + 1 := by omega
      rw [cost] at hAll
      simpa only [appendFields, WorkMachineChain.machine, renameConfiguration, writeAny_start,
        List.replicate_succ, reverseOnto] using hAll

def scanInput : WorkMachine :=
  { rules := [
      ⟨0, Store.bitSymbol false, 0, Store.bitSymbol false, .right⟩,
      ⟨0, Store.bitSymbol true, 0, Store.bitSymbol true, .right⟩,
      ⟨0, Store.separator, 1, Store.separator, .right⟩,
      ⟨0, WorkSymbol.blank, 1, Store.separator, .right⟩]
    startState := 0, acceptState := 1, rejectState := 2 }

theorem scanInput_wellFormed : ProgramWellFormed scanInput := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

theorem scanInput_bit_step (bit : Bool) (left right : List WorkSymbol) :
    workStep? scanInput ⟨0, focus left (Store.bitSymbol bit :: right)⟩ =
      some ⟨0, focus (Store.bitSymbol bit :: left) right⟩ := by
  cases bit <;> cases right <;> rfl

theorem scanInput_separator_step (left right : List WorkSymbol) :
    workStep? scanInput ⟨0, focus left (Store.separator :: right)⟩ =
      some ⟨1, focus (Store.separator :: left) right⟩ := by
  cases right <;> rfl

theorem scanInput_word_run (bits : BitString) (left right : List WorkSymbol) :
    workRunExact? scanInput (bits.length + 1)
      ⟨0, focus left (bits.map Store.bitSymbol ++ Store.separator :: right)⟩ =
      some ⟨1, focus (Store.separator :: reverseOnto (bits.map Store.bitSymbol) left) right⟩ := by
  induction bits generalizing left with
  | nil =>
      change (match workStep? scanInput ⟨0, focus left (Store.separator :: right)⟩ with
        | none => none | some next => some next) = _
      rw [scanInput_separator_step]
      rfl
  | cons bit rest ih =>
      change (match workStep? scanInput
          ⟨0, focus left (Store.bitSymbol bit ::
            (rest.map Store.bitSymbol ++ Store.separator :: right))⟩ with
        | none => none | some next => workRunExact? scanInput (rest.length + 1) next) = _
      rw [scanInput_bit_step]
      exact ih (Store.bitSymbol bit :: left)

end PNP.Concrete.BitRegister.IOAdapter
