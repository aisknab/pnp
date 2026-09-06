/-
Copyright (c) 2026 PNP Labs.

Compare two disposable ordinary unary registers using the existing general
comparator. Five fixed rules orient the pair and seal its inner delimiter;
spatial reflection reuses the already-proved exterior-shielded execution.
The older registers and arbitrary source workspace remain behind that boundary.

This layer starts with the copied pair and an empty outer tape, as produced by
the source assembly/copy path. It does not itself copy the operands, restore a
residual register, select a region, or implement the complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderConstraintRegionAssembly

namespace PNP.Concrete.CookLevin.BuilderRegionPairComparison

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial
open BuilderDividerOperands (endTape)
open BuilderPhysicalClassifierFinishMirroredDispatch
  (mirrorTape mirrorRule mirrorMachine mirrorConfiguration workRunExact?_mirror_of_some
    mirrorRules_pairwise_query_distinct mirrorMachine_acceptState_ne_rejectState)

def exterior (older : List Nat) (workspace : List WorkSymbol) : List WorkSymbol :=
  (registerWord older).reverse ++ workspace

namespace Layout

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := write, move := move }

def rules : List WorkRule :=
  [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
   rule 1 1 unitSymbol unitSymbol .right,
   rule 1 2 separatorSymbol separatorSymbol .right,
   rule 2 2 unitSymbol unitSymbol .right,
   rule 2 3 separatorSymbol leftMarker .left]

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 3, rejectState := 4 }

theorem rules_length : rules.length = 5 := rfl

theorem rules_pairwise_query_distinct : rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro selected hMem
  change selected.sourceState ≠ 3
  change selected ∈ rules at hMem
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

private def rightFocus (left word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

def comparisonWord (coordinate boundary : Nat) : List WorkSymbol :=
  List.replicate coordinate unitSymbol ++
    separatorSymbol :: (List.replicate boundary unitSymbol ++ [scratchEndSymbol])

def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) workspace [])

def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  {
    state := machine.acceptState
    tape := BuilderDividerLayout.leftFocus (comparisonWord coordinate boundary)
      (leftMarker :: exterior older workspace)
  }

def workSteps (coordinate boundary : Nat) : Nat := boundary + coordinate + 3

theorem initial_tape_layout (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (initialConfiguration coordinate boundary older workspace).tape =
      {
        left := []
        head := scratchEndSymbol
        right := List.replicate boundary unitSymbol ++ separatorSymbol ::
          (List.replicate coordinate unitSymbol ++ separatorSymbol :: exterior older workspace)
      } := by
  simp only [initialConfiguration, workStartConfiguration, endTape, exterior,
    registerWord_append, registerWord, List.append_nil, List.reverse_append,
    List.reverse_cons, List.reverse_replicate,
    List.append_assoc, List.cons_append, List.nil_append]

private theorem scan_right (state : Nat) (word remainder left : List WorkSymbol)
    (hState : state = 1 ∨ state = 2)
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
      rcases hState with hState | hState <;> subst state <;> rfl
    simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (unitSymbol :: left) hRest

theorem workRunExact (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
        (initialConfiguration coordinate boundary older workspace) =
      some (finalConfiguration coordinate boundary older workspace) := by
  let afterCoordinate := separatorSymbol :: exterior older workspace
  let boundaryScan : WorkConfiguration :=
    {
      state := 1
      tape := rightFocus [scratchEndSymbol]
        (List.replicate boundary unitSymbol ++ separatorSymbol ::
          (List.replicate coordinate unitSymbol ++ afterCoordinate))
    }
  let boundaryEnd : WorkConfiguration :=
    {
      state := 1
      tape := {
        left := List.replicate boundary unitSymbol ++ [scratchEndSymbol]
        head := separatorSymbol
        right := List.replicate coordinate unitSymbol ++ afterCoordinate
      }
    }
  let coordinateScan : WorkConfiguration :=
    {
      state := 2
      tape := rightFocus
        (separatorSymbol :: (List.replicate boundary unitSymbol ++ [scratchEndSymbol]))
        (List.replicate coordinate unitSymbol ++ afterCoordinate)
    }
  let coordinateEnd : WorkConfiguration :=
    {
      state := 2
      tape := {
        left := comparisonWord coordinate boundary
        head := separatorSymbol
        right := exterior older workspace
      }
    }
  have hStart : workRunExact? machine 1
      (initialConfiguration coordinate boundary older workspace) = some boundaryScan := by
    change workRunExact? machine 1
      {
        state := 0
        tape := (initialConfiguration coordinate boundary older workspace).tape
      } = some boundaryScan
    rw [initial_tape_layout]
    rfl
  have hBoundary : workRunExact? machine boundary boundaryScan = some boundaryEnd := by
    have h := scan_right 1 (List.replicate boundary unitSymbol)
      (List.replicate coordinate unitSymbol ++ afterCoordinate) [scratchEndSymbol]
      (Or.inl rfl) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [boundaryScan, boundaryEnd, List.length_replicate, List.reverse_replicate] using h
  have hToCoordinate : workRunExact? machine 1 boundaryEnd = some coordinateScan := by rfl
  have hCoordinate : workRunExact? machine coordinate coordinateScan = some coordinateEnd := by
    have h := scan_right 2 (List.replicate coordinate unitSymbol) (exterior older workspace)
      (separatorSymbol :: (List.replicate boundary unitSymbol ++ [scratchEndSymbol]))
      (Or.inr rfl) (fun _ hMem => List.eq_of_mem_replicate hMem)
    simpa only [coordinateScan, coordinateEnd, comparisonWord, afterCoordinate,
      List.length_replicate, List.reverse_replicate] using h
  have hSeal : workRunExact? machine 1 coordinateEnd =
      some (finalConfiguration coordinate boundary older workspace) := by rfl
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine 1 boundary
    _ _ _ hStart hBoundary
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine (1 + boundary) 1
    _ _ _ h01 hToCoordinate
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine (1 + boundary + 1) coordinate
    _ _ _ h02 hCoordinate
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + boundary + 1 + coordinate) 1 _ _ _ h03 hSeal
  have hCost : 1 + boundary + 1 + coordinate + 1 = workSteps coordinate boundary := by
    unfold workSteps
    omega
  rw [hCost] at hAll
  exact hAll

end Layout

def comparatorMachine : WorkMachine :=
  mirrorMachine BuilderArbitrarySlotHeaderRouter.RawRouter.machine

def machine : WorkMachine := WorkMachineChain.machine Layout.machine comparatorMachine

def initialConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (endTape (older ++ [coordinate, boundary]) workspace [])

def finalConfiguration (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  renameConfiguration WorkMachineChain.secondState
    (mirrorConfiguration
      (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
        coordinate boundary (exterior older workspace)))

def workSteps (coordinate boundary : Nat) : Nat :=
  Layout.workSteps coordinate boundary + 1 +
    BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary

/-- The existing left-shielded theorem becomes right-shielding after reflection. -/
theorem layout_tape_eq_mirrored_comparator_input (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (Layout.finalConfiguration coordinate boundary older workspace).tape =
      mirrorTape
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
          coordinate boundary (exterior older workspace)).tape := by
  cases coordinate <;>
    simp only [Layout.finalConfiguration, Layout.comparisonWord,
      BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration,
      BuilderPostDividerRawRouteClassifier.appendExteriorTape,
      BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape,
      BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonTape,
      BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonWord,
      List.replicate_zero, List.replicate_succ, List.nil_append] <;> rfl

theorem workRunExact (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine (workSteps coordinate boundary)
        (initialConfiguration coordinate boundary older workspace) =
      some (finalConfiguration coordinate boundary older workspace) := by
  have hLayout := Layout.workRunExact coordinate boundary older workspace
  have hComparator := workRunExact?_mirror_of_some
    BuilderPostDividerRawRouteClassifier.comparatorMachine
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorStartConfiguration
      coordinate boundary (exterior older workspace))
    (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
      coordinate boundary (exterior older workspace))
    (BuilderPostDividerRawRouteClassifier.shielded_comparator_workRunExact
      coordinate boundary (exterior older workspace))
  have hSecond : workRunExact? comparatorMachine
      (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
      {
        state := comparatorMachine.startState
        tape := (Layout.finalConfiguration coordinate boundary older workspace).tape
      } =
      some (mirrorConfiguration
        (BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration
          coordinate boundary (exterior older workspace))) := by
    rw [layout_tape_eq_mirrored_comparator_input]
    exact hComparator
  exact WorkMachineChain.workRunExact Layout.machine comparatorMachine
    (Layout.workSteps coordinate boundary)
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary)
    _ _ _ hLayout rfl hSecond

theorem run_compile_exact (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
        (encodeWorkConfiguration (initialConfiguration coordinate boundary older workspace)) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary older workspace) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _
    (workRunExact coordinate boundary older workspace)

theorem final_accept_iff (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.acceptState ↔
      coordinate < boundary := by
  change WorkMachineChain.secondState
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).state =
    WorkMachineChain.secondState BuilderArbitrarySlotHeaderRouter.RawRouter.machine.acceptState ↔ _
  constructor
  · intro h
    exact (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_accept_iff
      coordinate boundary).1 (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_accept_iff
        coordinate boundary).2 h)

theorem final_reject_iff (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).state = machine.rejectState ↔
      boundary ≤ coordinate := by
  change WorkMachineChain.secondState
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).state =
    WorkMachineChain.secondState BuilderArbitrarySlotHeaderRouter.RawRouter.machine.rejectState ↔ _
  constructor
  · intro h
    exact (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_reject_iff
      coordinate boundary).1 (WorkMachineChain.secondState_injective h)
  · intro h
    exact congrArg WorkMachineChain.secondState
      ((BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_reject_iff
        coordinate boundary).2 h)

/-- Exact preserved suffix, including every older register and arbitrary workspace cell. -/
theorem final_exterior_preserved (coordinate boundary : Nat) (older : List Nat)
    (workspace : List WorkSymbol) :
    (finalConfiguration coordinate boundary older workspace).tape.right =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration coordinate boundary).tape.left ++
        ((registerWord older).reverse ++ workspace) := rfl

private theorem comparator_noRule : WorkMachineChain.NoRuleAtAccept comparatorMachine := by
  intro selected hMem
  change selected ∈ BuilderArbitrarySlotHeaderRouter.RawRouter.machine.rules.map mirrorRule at hMem
  rcases List.mem_map.mp hMem with ⟨original, hOriginal, hEqual⟩
  subst selected
  exact BuilderArbitrarySlotHeaderRouter.RawRouter.rule_source_ne_acceptState original hOriginal

theorem rules_pairwise_query_distinct : machine.rules.Pairwise WorkMachineChain.QueryDistinct :=
  WorkMachineChain.rules_pairwise_query_distinct Layout.machine comparatorMachine
    Layout.rules_pairwise_query_distinct
    (mirrorRules_pairwise_query_distinct BuilderArbitrarySlotHeaderRouter.RawRouter.machine
      BuilderArbitrarySlotHeaderRouter.RawRouter.rules_pairwise_query_distinct)
    Layout.noRuleAtAccept

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine :=
  WorkMachineChain.noRuleAtAccept Layout.machine comparatorMachine comparator_noRule

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState :=
  WorkMachineChain.machine_acceptState_ne_rejectState _ _
    (mirrorMachine_acceptState_ne_rejectState BuilderArbitrarySlotHeaderRouter.RawRouter.machine
      BuilderArbitrarySlotHeaderRouter.RawRouter.machine_acceptState_ne_rejectState)

theorem workSteps_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    workSteps coordinate boundary ≤ 2 * bound + 4 + 6 * (bound + 1) * (bound + 1) := by
  have hRaw := BuilderArbitrarySlotHeaderRouter.RawRouter.loopSteps_le 0 coordinate boundary
  have hCoordinate' := Nat.add_le_add_right hCoordinate 1
  have hProduct := Nat.mul_le_mul (Nat.mul_le_mul_left 6 hCoordinate') hCoordinate'
  have hComparator : BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps coordinate boundary ≤
      6 * (bound + 1) * (bound + 1) := by
    exact Nat.le_trans (by simpa only [BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps,
      Nat.zero_add] using hRaw) hProduct
  unfold workSteps Layout.workSteps
  omega

def rawTimeBound (bound : Nat) : Nat :=
  6 * (2 * bound + 4 + 6 * (bound + 1) * (bound + 1))

theorem rawTimeBound_le (coordinate boundary bound : Nat)
    (hCoordinate : coordinate ≤ bound) (hBoundary : boundary ≤ bound) :
    6 * workSteps coordinate boundary ≤ rawTimeBound bound :=
  Nat.mul_le_mul_left 6 (workSteps_le coordinate boundary bound hCoordinate hBoundary)

end PNP.Concrete.CookLevin.BuilderRegionPairComparison
