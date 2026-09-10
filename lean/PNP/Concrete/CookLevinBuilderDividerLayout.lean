/-
Copyright (c) 2026 PNP Labs.

Literal conversion of the appended [clauseCount, 0, index, tokenWidth] registers
into a reflected divider word with two protective boundaries and a count sidecar.
The eleven-rule machine changes only three copied delimiters, preserves the
original word and inside tape, and accounts for every scan and transition.
Source binding and actual divider execution are provided by the next layer.
-/

import PNP.Concrete.CookLevinBuilderDividerOperands

namespace PNP.Concrete.CookLevin.BuilderDividerLayout

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := write, move := move }

def rules : List WorkRule :=
  [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
   rule 1 1 unitSymbol unitSymbol .right,
   rule 1 2 separatorSymbol separatorSymbol .right,
   rule 2 2 unitSymbol unitSymbol .right,
   rule 2 3 separatorSymbol leftMarker .right,
   rule 3 4 separatorSymbol leftMarker .right,
   rule 4 4 unitSymbol unitSymbol .right,
   rule 4 5 separatorSymbol scratchEndSymbol .left,
   rule 5 5 unitSymbol unitSymbol .left,
   rule 5 6 leftMarker leftMarker .left,
   rule 6 7 leftMarker leftMarker .left]

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 7, rejectState := 8 }

theorem rules_length : rules.length = 11 := rfl

theorem rules_pairwise_query_distinct : rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro selected hMem
  change selected.sourceState ≠ 7
  change selected ∈ rules at hMem
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private def rightFocus (left word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

def leftFocus (word right : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := [], head := .blank, right := right }
  | symbol :: rest => { left := rest, head := symbol, right := right }

def dividerWord (index width : Nat) : List WorkSymbol :=
  List.replicate index unitSymbol ++
    separatorSymbol :: (List.replicate width unitSymbol ++ [scratchEndSymbol])

/-- One boundary shields the divider, the other is retained for the count classifier. -/
def protectedSide (count : Nat) (workspace : List WorkSymbol) : List WorkSymbol :=
  leftMarker :: leftMarker :: (List.replicate count unitSymbol ++ scratchEndSymbol :: workspace)

def convertedTape (count index width : Nat) (workspace tail : List WorkSymbol) : WorkTape :=
  leftFocus (dividerWord index width ++ tail) (protectedSide count workspace)

def initialConfiguration (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine
    (BuilderDividerOperands.endTape (older ++ [count, 0, index, width]) inside tail)

def finalConfiguration (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) : WorkConfiguration :=
  {
    state := 7
    tape := convertedTape count index width ((registerWord older).reverse ++ inside) tail
  }

def workSteps (count index width : Nat) : Nat := width + index + 2 * count + 7

theorem initial_tape_layout (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) :
    (initialConfiguration count index width older inside tail).tape =
      {
        left := tail
        head := scratchEndSymbol
        right := List.replicate width unitSymbol ++ separatorSymbol ::
          (List.replicate index unitSymbol ++ separatorSymbol :: separatorSymbol ::
            (List.replicate count unitSymbol ++ separatorSymbol ::
              ((registerWord older).reverse ++ inside)))
      } := by
  simp only [initialConfiguration, workStartConfiguration, BuilderDividerOperands.endTape,
    registerWord_append, registerWord, List.replicate_zero, List.nil_append, List.append_nil,
    List.reverse_append, List.reverse_cons, List.reverse_nil, List.reverse_replicate,
    List.append_assoc, List.cons_append]

private theorem scan_right (state : Nat) (word remainder left : List WorkSymbol)
    (hState : state = 1 ∨ state = 2 ∨ state = 4)
    (hUnits : ∀ symbol ∈ word, symbol = unitSymbol) :
    workRunExact? machine word.length
      {
        state := state
        tape := rightFocus left (word ++ separatorSymbol :: remainder)
      } =
      some {
        state := state
        tape := {
          left := word.reverse ++ left
          head := separatorSymbol
          right := remainder
        }
      } := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
    have hSymbol := hUnits symbol List.mem_cons_self
    have hRest : ∀ item ∈ rest, item = unitSymbol := by
      intro item hItem
      exact hUnits item (List.mem_cons_of_mem symbol hItem)
    subst symbol
    have hStep : workStep? machine
        {
          state := state
          tape := { left := left, head := unitSymbol, right := rest ++ separatorSymbol :: remainder }
        } =
        some {
          state := state
          tape := rightFocus (unitSymbol :: left) (rest ++ separatorSymbol :: remainder)
        } := by
      rcases hState with hState | hState | hState <;> subst state <;> rfl
    simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (unitSymbol :: left) hRest

private theorem scan_left (word remainder right : List WorkSymbol)
    (hUnits : ∀ symbol ∈ word, symbol = unitSymbol) :
    workRunExact? machine word.length
      {
        state := 5
        tape := leftFocus (word ++ leftMarker :: remainder) right
      } =
      some {
        state := 5
        tape := {
          left := remainder
          head := leftMarker
          right := word.reverse ++ right
        }
      } := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hSymbol := hUnits symbol List.mem_cons_self
    have hRest : ∀ item ∈ rest, item = unitSymbol := by
      intro item hItem
      exact hUnits item (List.mem_cons_of_mem symbol hItem)
    subst symbol
    have hStep : workStep? machine
        {
          state := 5
          tape := { left := rest ++ leftMarker :: remainder, head := unitSymbol, right := right }
        } =
        some {
          state := 5
          tape := leftFocus (rest ++ leftMarker :: remainder) (unitSymbol :: right)
        } := by rfl
    simp only [List.length_cons, List.cons_append, leftFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (unitSymbol :: right) hRest

theorem workRunExact (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) :
    workRunExact? machine (workSteps count index width)
        (initialConfiguration count index width older inside tail) =
      some (finalConfiguration count index width older inside tail) := by
  let workspace := (registerWord older).reverse ++ inside
  let payload := List.replicate index unitSymbol ++
    separatorSymbol :: (List.replicate width unitSymbol ++ scratchEndSymbol :: tail)
  let afterIndex := separatorSymbol :: separatorSymbol ::
    (List.replicate count unitSymbol ++ separatorSymbol :: workspace)
  let widthScan : WorkConfiguration :=
    {
      state := 1
      tape := rightFocus (scratchEndSymbol :: tail)
        (List.replicate width unitSymbol ++ separatorSymbol ::
          (List.replicate index unitSymbol ++ afterIndex))
    }
  let widthEnd : WorkConfiguration :=
    {
      state := 1
      tape := {
        left := List.replicate width unitSymbol ++ scratchEndSymbol :: tail
        head := separatorSymbol
        right := List.replicate index unitSymbol ++ afterIndex
      }
    }
  let indexScan : WorkConfiguration :=
    {
      state := 2
      tape := rightFocus
        (separatorSymbol :: (List.replicate width unitSymbol ++ scratchEndSymbol :: tail))
        (List.replicate index unitSymbol ++ afterIndex)
    }
  let indexEnd : WorkConfiguration :=
    {
      state := 2
      tape := {
        left := payload
        head := separatorSymbol
        right := separatorSymbol :: (List.replicate count unitSymbol ++ separatorSymbol :: workspace)
      }
    }
  let countScan : WorkConfiguration :=
    {
      state := 4
      tape := rightFocus (leftMarker :: leftMarker :: payload)
        (List.replicate count unitSymbol ++ separatorSymbol :: workspace)
    }
  let countEnd : WorkConfiguration :=
    {
      state := 4
      tape := {
        left := List.replicate count unitSymbol ++ leftMarker :: leftMarker :: payload
        head := separatorSymbol
        right := workspace
      }
    }
  let countBack : WorkConfiguration :=
    {
      state := 5
      tape := leftFocus (List.replicate count unitSymbol ++ leftMarker :: leftMarker :: payload)
        (scratchEndSymbol :: workspace)
    }
  let sideBoundary : WorkConfiguration :=
    {
      state := 5
      tape := {
        left := leftMarker :: payload
        head := leftMarker
        right := List.replicate count unitSymbol ++ scratchEndSymbol :: workspace
      }
    }
  have hStart : workRunExact? machine 1
      (initialConfiguration count index width older inside tail) = some widthScan := by
    change workRunExact? machine 1
      {
        state := 0
        tape := (initialConfiguration count index width older inside tail).tape
      } = some widthScan
    rw [initial_tape_layout]
    rfl
  have hWidth : workRunExact? machine width widthScan = some widthEnd := by
    have h := scan_right 1 (List.replicate width unitSymbol)
      (List.replicate index unitSymbol ++ afterIndex) (scratchEndSymbol :: tail)
      (Or.inl rfl) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [widthScan, widthEnd, List.length_replicate, List.reverse_replicate] using h
  have hToIndex : workRunExact? machine 1 widthEnd = some indexScan := by rfl
  have hIndex : workRunExact? machine index indexScan = some indexEnd := by
    have h := scan_right 2 (List.replicate index unitSymbol)
      (separatorSymbol :: (List.replicate count unitSymbol ++ separatorSymbol :: workspace))
      (separatorSymbol :: (List.replicate width unitSymbol ++ scratchEndSymbol :: tail))
      (Or.inr (Or.inl rfl)) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [indexScan, indexEnd, payload, afterIndex,
      List.length_replicate, List.reverse_replicate] using h
  have hToCount : workRunExact? machine 2 indexEnd = some countScan := by rfl
  have hCount : workRunExact? machine count countScan = some countEnd := by
    have h := scan_right 4 (List.replicate count unitSymbol) workspace
      (leftMarker :: leftMarker :: payload)
      (Or.inr (Or.inr rfl)) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [countScan, countEnd, List.length_replicate, List.reverse_replicate] using h
  have hTurn : workRunExact? machine 1 countEnd = some countBack := by rfl
  have hBack : workRunExact? machine count countBack = some sideBoundary := by
    have h := scan_left (List.replicate count unitSymbol) (leftMarker :: payload)
      (scratchEndSymbol :: workspace) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [countBack, sideBoundary, List.length_replicate, List.reverse_replicate] using h
  have hFinish : workRunExact? machine 2 sideBoundary =
      some (finalConfiguration count index width older inside tail) := by
    have hPayload : dividerWord index width ++ tail = payload := by
      simp only [dividerWord, payload, List.append_assoc, List.cons_append, List.nil_append]
    unfold finalConfiguration convertedTape
    rw [hPayload]
    rfl
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine 1 width
    _ _ _ hStart hWidth
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine (1 + width) 1
    _ _ _ h01 hToIndex
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine (1 + width + 1) index
    _ _ _ h02 hIndex
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine (1 + width + 1 + index) 2
    _ _ _ h03 hToCount
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine (1 + width + 1 + index + 2) count
    _ _ _ h04 hCount
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + width + 1 + index + 2 + count) 1 _ _ _ h05 hTurn
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + width + 1 + index + 2 + count + 1) count _ _ _ h06 hBack
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + width + 1 + index + 2 + count + 1 + count) 2 _ _ _ h07 hFinish
  have hCost : 1 + width + 1 + index + 2 + count + 1 + count + 2 =
      workSteps count index width := by
    unfold workSteps
    omega
  rw [hCost] at hAll
  exact hAll

theorem finalConfiguration_state (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) :
    (finalConfiguration count index width older inside tail).state = machine.acceptState := rfl

theorem run_compile_exact (count index width : Nat) (older : List Nat)
    (inside tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps count index width)
        (encodeWorkConfiguration (initialConfiguration count index width older inside tail)) =
      encodeWorkConfiguration (finalConfiguration count index width older inside tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact count index width older inside tail)

theorem workSteps_le (count index width bound : Nat)
    (hCount : count ≤ bound) (hIndex : index ≤ bound) (hWidth : width ≤ bound) :
    workSteps count index width ≤ 4 * bound + 7 := by
  unfold workSteps
  omega

end PNP.Concrete.CookLevin.BuilderDividerLayout
