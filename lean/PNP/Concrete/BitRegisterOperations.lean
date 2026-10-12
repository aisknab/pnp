/-
Copyright (c) 2026 PNP Labs.

Whole register operations assembled from literal finite work machines.
Navigation is fixed by a register index, not by a supplied input-dependent
machine. Empty pop preserves its delimiter. Every operation accounts for
bridges and represented blank slack. Composition reuses the existing graph
compiler and its permitted standard logical axiom boundary.
-/

import PNP.Concrete.BitRegisterMutation
import PNP.Concrete.WorkMachineChain
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete.BitRegister.Operation

open TapePrimitive Mutation WorkMachineProgramGraph
open PipelineStateNamespace

def bitCell : Bool → Cell
  | false => .zero
  | true => .one

def bitCells (bits : BitString) : List Cell := bits.map bitCell

theorem bitCells_length (bits : BitString) : (bitCells bits).length = bits.length := by
  exact List.length_map bitCell

theorem bitCells_symbols (bits : BitString) :
    (bitCells bits).map Cell.symbol = bits.map Store.bitSymbol := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit <;> exact congrArg (List.cons _) ih

def fieldCells : List BitString → List Cell
  | [] => []
  | bits :: rest => bitCells bits ++ .separator :: fieldCells rest

def fieldWord (fields : List BitString) : List WorkSymbol :=
  (fieldCells fields).map Cell.symbol

theorem fieldWord_cons (bits : BitString) (rest : List BitString) :
    fieldWord (bits :: rest) =
      bits.map Store.bitSymbol ++ Store.separator :: fieldWord rest := by
  simp only [fieldWord, fieldCells, List.map_append, List.map_cons, bitCells_symbols]
  rfl

theorem fieldWord_length (fields : List BitString) :
    (fieldWord fields).length = (fieldCells fields).length :=
  List.length_map Cell.symbol

theorem reverseOnto_append (first second suffix : List WorkSymbol) :
    reverseOnto (first ++ second) suffix = reverseOnto second (reverseOnto first suffix) := by
  induction first generalizing suffix with
  | nil => rfl
  | cons head rest ih => exact ih (head :: suffix)

def ProgramWellFormed (program : WorkMachine) : Prop :=
  program.rules.Pairwise QueryDistinct ∧
    NoRuleAt program program.acceptState ∧
    NoRuleAt program program.rejectState ∧
    program.acceptState ≠ program.rejectState

theorem chain_wellFormed (first second : WorkMachine)
    (hFirst : ProgramWellFormed first) (hSecond : ProgramWellFormed second) :
    ProgramWellFormed (WorkMachineChain.machine first second) := by
  refine ⟨WorkMachineChain.rules_pairwise_query_distinct first second
    hFirst.1 hSecond.1 hFirst.2.1, ?_, ?_, ?_⟩
  · exact WorkMachineChain.noRuleAtAccept first second hSecond.2.1
  · exact WorkMachineChain.noRuleAtAccept first
      { second with acceptState := second.rejectState } hSecond.2.2.1
  · exact WorkMachineChain.machine_acceptState_ne_rejectState first second hSecond.2.2.2

def idle : WorkMachine :=
  { rules := [], startState := 0, acceptState := 0, rejectState := 1 }

theorem noRuleAt_of_all (program : WorkMachine) (state : Nat)
    (checked : program.rules.all (fun rule => decide (rule.sourceState ≠ state)) = true) :
    NoRuleAt program state := by
  intro rule member
  exact of_decide_eq_true ((List.all_eq_true.mp checked) rule member)

theorem idle_wellFormed : ProgramWellFormed idle := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

theorem skip_wellFormed : ProgramWellFormed skip := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

/-- Starts at the first register; each compile-time index adds one finite scan. -/
def seek : Nat → WorkMachine
  | 0 => idle
  | index + 1 => WorkMachineChain.machine skip (seek index)

theorem seek_wellFormed (index : Nat) : ProgramWellFormed (seek index) := by
  induction index with
  | zero => exact idle_wellFormed
  | succ index ih => exact chain_wellFormed skip (seek index) skip_wellFormed ih

def seekSteps (fields : List BitString) : Nat :=
  (fieldWord fields).length + fields.length

theorem seek_run (fields : List BitString) (left right : List WorkSymbol) :
    workRunExact? (seek fields.length) (seekSteps fields)
      ⟨(seek fields.length).startState, focus left (fieldWord fields ++ right)⟩ =
    some ⟨(seek fields.length).acceptState,
      focus (reverseOnto (fieldWord fields) left) right⟩ := by
  induction fields generalizing left with
  | nil => rfl
  | cons bits rest ih =>
      have hFirst := skip_run bits left (fieldWord rest ++ right)
      have hNext := ih (Store.separator :: reverseOnto (bits.map Store.bitSymbol) left)
      have hAll := WorkMachineChain.workRunExact skip (seek rest.length)
        (bits.length + 1) (seekSteps rest) _ _ _ hFirst rfl hNext
      have hSteps : bits.length + 1 + 1 + seekSteps rest = seekSteps (bits :: rest) := by
        simp only [seekSteps, fieldWord_cons, List.length_append, List.length_map,
          List.length_cons]
        omega
      rw [hSteps] at hAll
      have hStart : skip.startState = 0 := rfl
      simpa only [seek, List.length_cons, WorkMachineChain.machine, hStart,
        renameConfiguration, fieldWord_cons, List.append_assoc, List.cons_append,
        reverseOnto_append, reverseOnto] using hAll

/-- One literal move from the left boundary to the first register. -/
def enter : WorkMachine :=
  { rules := [⟨0, WorkSymbol.blankZero, 1, WorkSymbol.blankZero, .right⟩]
    startState := 0, acceptState := 1, rejectState := 2 }

theorem enter_wellFormed : ProgramWellFormed enter := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

theorem enter_run (outside right : List WorkSymbol) :
    workRunExact? enter 1 ⟨0, ⟨outside, WorkSymbol.blankZero, right⟩⟩ =
      some ⟨1, focus (WorkSymbol.blankZero :: outside) right⟩ := by
  cases right <;> rfl

def seekFromBoundary (index : Nat) : WorkMachine :=
  WorkMachineChain.machine enter (seek index)

theorem seekFromBoundary_wellFormed (index : Nat) :
    ProgramWellFormed (seekFromBoundary index) :=
  chain_wellFormed enter (seek index) enter_wellFormed (seek_wellFormed index)

theorem seekFromBoundary_run (fields : List BitString)
    (outside right : List WorkSymbol) :
    workRunExact? (seekFromBoundary fields.length) (2 + seekSteps fields)
      ⟨(seekFromBoundary fields.length).startState,
        ⟨outside, WorkSymbol.blankZero, fieldWord fields ++ right⟩⟩ =
    some ⟨(seekFromBoundary fields.length).acceptState,
      focus (reverseOnto (fieldWord fields) (WorkSymbol.blankZero :: outside)) right⟩ := by
  exact WorkMachineChain.workRunExact enter (seek fields.length) 1 (seekSteps fields)
    _ _ _ (enter_run outside (fieldWord fields ++ right)) rfl
    (seek_run fields (WorkSymbol.blankZero :: outside) right)

theorem erase_wellFormed : ProgramWellFormed eraseCell := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

/-- The designated entry point does not alter execution from an explicit configuration. -/
theorem workRunExact_start (program : WorkMachine) (start steps : Nat)
    (config : WorkConfiguration) :
    workRunExact? { program with startState := start } steps config =
      workRunExact? program steps config := by
  induction steps generalizing config with
  | zero => rfl
  | succ steps ih =>
      have hStep : workStep? { program with startState := start } config =
          workStep? program config := rfl
      simp only [workRunExact?, hStep]
      cases workStep? program config with
      | none => rfl
      | some next => exact ih next

def home : WorkMachine := { eraseCell with startState := 4 }

theorem home_wellFormed : ProgramWellFormed home := erase_wellFormed

theorem home_run (before : List Cell) (current : Cell)
    (outside right : List WorkSymbol) :
    workRunExact? home (before.length + 2)
      ⟨4, focus (reverseOnto (before.map Cell.symbol) (WorkSymbol.blankZero :: outside))
        (current.symbol :: right)⟩ =
    some ⟨1, ⟨outside, WorkSymbol.blankZero,
      before.map Cell.symbol ++ current.symbol :: right⟩⟩ := by
  have hStart := exact_one (erase_return_step current
    (reverseOnto (before.map Cell.symbol) (WorkSymbol.blankZero :: outside)) right)
  have hReturn := erase_return before (WorkSymbol.blankZero :: outside) (current.symbol :: right)
  have hStop := erase_stop outside (before.map Cell.symbol ++ current.symbol :: right)
  have hFirst := PipelineMachineSimulation.workRunExact?_compose eraseCell
    1 before.length _ _ _ hStart hReturn
  have hAll := PipelineMachineSimulation.workRunExact?_compose eraseCell
    (1 + before.length) 1 _ _ _ hFirst hStop
  have hSteps : 1 + before.length + 1 = before.length + 2 := by omega
  rw [hSteps] at hAll
  simp only [home, workRunExact_start]
  exact hAll

theorem isEmpty_wellFormed : ProgramWellFormed isEmpty := by
  refine ⟨?_, noRuleAt_of_all _ _ (by decide), noRuleAt_of_all _ _ (by decide), by decide⟩
  unfold QueryDistinct
  decide

def homeNode : Node :=
  { name := 2, program := home, onAccept := .accept, onReject := .reject }

def eraseNode : Node :=
  { name := 1, program := eraseCell, onAccept := .accept, onReject := .reject }

def popTestNode : Node :=
  Node.conditional 0 isEmpty homeNode.reference eraseNode.reference

def popGraph : Graph :=
  { nodes := [popTestNode, eraseNode, homeNode], entry := popTestNode.reference }

theorem resolves_member (nodes : List Node) (node : Node) (h : node ∈ nodes) :
    Endpoint.Resolves nodes (.node node.reference) :=
  ⟨node, h, rfl, rfl⟩

theorem popGraph_wellFormed : popGraph.WellFormed := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · intro node member
    simp only [popGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact isEmpty_wellFormed
    · exact erase_wellFormed
    · exact home_wellFormed
  · exact resolves_member _ popTestNode (by simp [popGraph])
  · intro node member
    simp only [popGraph, List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨resolves_member _ homeNode (by simp [popGraph]),
        resolves_member _ eraseNode (by simp [popGraph])⟩
    · exact ⟨True.intro, True.intro⟩
    · exact ⟨True.intro, True.intro⟩

def pop : WorkMachine := WorkMachineProgramGraph.machine popGraph

def content (bits : BitString) (after : List Cell) (slack : Nat) : List WorkSymbol :=
  bits.map Store.bitSymbol ++ Store.separator :: (after.map Cell.symbol ++ tail slack)

def cursor (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) : WorkTape :=
  focus (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
    (content bits after slack)

def atBoundary (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) : WorkTape :=
  ⟨outside, WorkSymbol.blankZero, fieldWord before ++ content bits after slack⟩

def popSlack : BitString → Nat → Nat
  | [], slack => slack
  | _ :: _, slack => slack + 1

def popSteps (before : List BitString) : BitString → List Cell → Nat
  | [], _ => (fieldCells before).length + 5
  | _ :: rest, after => 4 * (rest.length + 1 + after.length) + (fieldCells before).length + 7

theorem pop_empty_run (before : List BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? pop ((fieldCells before).length + 5)
      ⟨pop.startState, cursor before [] after outside slack⟩ =
    some ⟨pop.acceptState, atBoundary before [] after outside slack⟩ := by
  have hTest := WorkMachineProgramGraph.local_then_accept popGraph popTestNode 1
    _ _ popGraph_wellFormed (by simp [popGraph])
    (isEmpty_run [] (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
      (after.map Cell.symbol ++ tail slack)) rfl
  have hHome := WorkMachineProgramGraph.local_then_accept popGraph homeNode
    ((fieldCells before).length + 2) _ _ popGraph_wellFormed (by simp [popGraph])
    (home_run (fieldCells before) .separator outside (after.map Cell.symbol ++ tail slack)) rfl
  have hAll := PipelineMachineSimulation.workRunExact?_compose pop
    2 ((fieldCells before).length + 2 + 1) _ _ _ hTest hHome
  have hSteps : 2 + ((fieldCells before).length + 2 + 1) = (fieldCells before).length + 5 := by omega
  rw [hSteps] at hAll
  exact hAll

/-- Guarded deletion at a nonempty register, preserving its delimiter and neighbours. -/
theorem erase_register_run (before : List BitString) (bit : Bool) (rest : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? eraseCell
      (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4)
      ⟨0, cursor before (bit :: rest) after outside slack⟩ =
    some ⟨1, atBoundary before rest after outside (slack + 1)⟩ := by
  have hErase := erase_run (bitCell bit) (fieldCells before) (bitCells rest ++ .separator :: after)
    outside slack
  cases bit <;>
    simpa only [bitCell, Cell.symbol, cursor, atBoundary, fieldWord, content,
      List.map_cons, List.map_append, bitCells_symbols, List.cons_append,
      List.append_assoc, List.length_append, List.length_cons, bitCells_length,
      Nat.add_assoc, Nat.add_comm 1] using hErase

theorem pop_nonempty_run (before : List BitString) (bit : Bool) (rest : BitString)
    (after : List Cell) (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? pop (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 7)
      ⟨pop.startState, cursor before (bit :: rest) after outside slack⟩ =
    some ⟨pop.acceptState, atBoundary before rest after outside (slack + 1)⟩ := by
  have hTest := WorkMachineProgramGraph.local_then_reject popGraph popTestNode 1
    _ _ popGraph_wellFormed (by simp [popGraph])
    (isEmpty_run (bit :: rest) (reverseOnto (fieldWord before) (WorkSymbol.blankZero :: outside))
      (after.map Cell.symbol ++ tail slack)) rfl
  have hLocal := erase_register_run before bit rest after outside slack
  have hRun := WorkMachineProgramGraph.local_then_accept popGraph eraseNode
    (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4)
    _ _ popGraph_wellFormed (by simp [popGraph]) hLocal rfl
  have hAll := PipelineMachineSimulation.workRunExact?_compose pop
    2 (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4 + 1)
    _ _ _ hTest hRun
  have hSteps : 2 + (4 * (rest.length + 1 + after.length) + (fieldCells before).length + 4 + 1) =
      4 * (rest.length + 1 + after.length) + (fieldCells before).length + 7 := by omega
  rw [hSteps] at hAll
  exact hAll

/-- A total pop on every register word, including the empty word. -/
theorem pop_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    workRunExact? pop (popSteps before bits after)
      ⟨pop.startState, cursor before bits after outside slack⟩ =
    some ⟨pop.acceptState, atBoundary before bits.tail after outside (popSlack bits slack)⟩ := by
  cases bits with
  | nil => exact pop_empty_run before after outside slack
  | cons bit rest => exact pop_nonempty_run before bit rest after outside slack

theorem pop_raw_run (before : List BitString) (bits : BitString) (after : List Cell)
    (outside : List WorkSymbol) (slack : Nat) :
    PNP.Concrete.run (compileWorkMachine pop) (6 * popSteps before bits after)
      (encodeWorkConfiguration ⟨pop.startState, cursor before bits after outside slack⟩) =
    encodeWorkConfiguration
      ⟨pop.acceptState, atBoundary before bits.tail after outside (popSlack bits slack)⟩ :=
  run_compileWorkMachine_mul_of_workRunExact pop _ _ _ (pop_run before bits after outside slack)

end PNP.Concrete.BitRegister.Operation
