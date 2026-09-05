/-
Copyright (c) 2026 PNP Labs.

A fixed physical zero-versus-positive body-remainder split after M228's
all-route derived-Finish classifier.  The splitter traverses only the literal
ledger retained by M214; no route, remainder, or request is staged on tape.
-/

import PNP.Concrete.CookLevinBuilderPhysicalClassifierAllRouteDerivedFinishSplit
import PNP.Concrete.WorkMachineProgramGraph

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPhysicalClassifierAllRouteBodyRemainderSplit

open PipelineTape PipelineStateNamespace PipelineStageBridges
open BuilderPostDividerSelectedTokenLaunch

namespace Splitter

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

private def keepAction := BuilderUnaryPolynomial.keepAction
private def deadAction := BuilderUnaryPolynomial.deadAction

abbrev bodyPendingSymbol : WorkSymbol :=
  BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyPendingSymbol
abbrev leftBoundary : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.leftBoundary
abbrev consumedDividend : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.consumedDividend
abbrev unitSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.unitSymbol
abbrev separatorSymbol : WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.separatorSymbol

def startSpec : StateSpec := fun read =>
  if read = bodyPendingSymbol then keepAction 1 .right read
  else deadAction 6 read

def firstBoundarySpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 2 .right read
  else keepAction 1 .right read

def secondBoundarySpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 3 .right read
  else keepAction 2 .right read

def inspectRemainderSpec : StateSpec := fun read =>
  if read = consumedDividend then keepAction 3 .right read
  else if read = separatorSymbol then keepAction 4 .stay read
  else if read = unitSymbol then keepAction 5 .stay read
  else deadAction 6 read

def stateSpecs : List StateSpec :=
  [startSpec, firstBoundarySpec, secondBoundarySpec, inspectRemainderSpec]

def rules : List WorkRule :=
  BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 4
    rejectState := 5 }

theorem rules_length : rules.length = 36 := by
  rw [rules, BuilderUnaryPolynomial.rulesFrom_length]
  rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderUnaryPolynomial.rulesFrom_pairwise_query_distinct 0 stateSpecs

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by decide

private theorem rulesFrom_source_lt (base : Nat)
    (specs : List StateSpec) (rule : WorkRule)
    (hRule : rule ∈ BuilderUnaryPolynomial.rulesFrom base specs) :
    rule.sourceState < base + specs.length := by
  induction specs generalizing base with
  | nil => contradiction
  | cons spec rest ih =>
      simp only [BuilderUnaryPolynomial.rulesFrom,
        List.mem_append] at hRule
      rcases hRule with hHead | hTail
      · rcases List.mem_map.mp hHead with ⟨symbol, _hSymbol, hRule⟩
        rw [← hRule]
        simp [BuilderUnaryPolynomial.ruleOf]
      · have hBound := ih (base := base + 1) hTail
        simp only [List.length_cons]
        omega

theorem noRuleAtAccept :
    WorkMachineProgramGraph.NoRuleAt machine machine.acceptState := by
  intro rule hRule
  have hBound := rulesFrom_source_lt 0 stateSpecs rule (by
    simpa [machine, rules] using hRule)
  simpa [machine, stateSpecs] using Nat.ne_of_lt hBound

theorem noRuleAtReject :
    WorkMachineProgramGraph.NoRuleAt machine machine.rejectState := by
  intro rule hRule
  have hBound := rulesFrom_source_lt 0 stateSpecs rule (by
    simpa [machine, rules] using hRule)
  simp only [stateSpecs, List.length_cons, List.length_nil,
    Nat.zero_add] at hBound
  have hNe : rule.sourceState ≠ 5 := by omega
  simpa [machine] using hNe

private def specMachine (specs : List StateSpec) : WorkMachine :=
  { rules := BuilderUnaryPolynomial.rulesFrom 0 specs
    startState := 0
    acceptState := specs.length
    rejectState := specs.length + 1 }

private theorem specMachine_step
    (before : List StateSpec) (spec : StateSpec)
    (after : List StateSpec) (tape : WorkTape) :
    workStep? (specMachine (before ++ spec :: after))
        { state := before.length, tape := tape } =
      some
        { state := (spec tape.head).targetState
          tape := (tape.write (spec tape.head).writeSymbol).move
            (spec tape.head).move } := by
  have hHalted :
      (specMachine (before ++ spec :: after)).isHalted
        { state := before.length, tape := tape } = false := by
    unfold WorkMachine.isHalted specMachine
    rw [PipelineSequentialStateNamespace.nat_beq_false_of_ne,
      PipelineSequentialStateNamespace.nat_beq_false_of_ne]
    · rfl
    · simp only [List.length_append, List.length_cons]
      omega
    · simp only [List.length_append, List.length_cons]
      omega
  have hFind : findWorkRule
      (specMachine (before ++ spec :: after)).rules
        before.length tape.head =
      some (BuilderUnaryPolynomial.ruleOf before.length spec tape.head) := by
    unfold specMachine
    simpa using
      (BuilderUnaryPolynomial.findWorkRule_rulesFrom_at_append
        0 before spec after tape.head)
  have hStep := workStep?_eq_apply_of_find
    (specMachine (before ++ spec :: after))
    { state := before.length, tape := tape }
    (BuilderUnaryPolynomial.ruleOf before.length spec tape.head)
    hHalted hFind
  simpa [BuilderUnaryPolynomial.ruleOf, applyWorkRule] using hStep

private theorem machine_eq_specMachine :
    machine = specMachine stateSpecs := by rfl

private theorem write_head_eq (tape : WorkTape) :
    tape.write tape.head = tape := by
  cases tape
  rfl

private theorem start_step (tape : WorkTape)
    (hHead : tape.head = bodyPendingSymbol) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 1, tape := tape.moveRight } := by
  have hStep := specMachine_step [] startSpec
    [firstBoundarySpec, secondBoundarySpec, inspectRemainderSpec] tape
  have hWrite : tape.write bodyPendingSymbol = tape := by
    rw [← hHead]
    exact write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, startSpec, hHead, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

private theorem first_scan_step (tape : WorkTape)
    (hHead : tape.head ≠ leftBoundary) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 1, tape := tape.moveRight } := by
  have hStep := specMachine_step [startSpec] firstBoundarySpec
    [secondBoundarySpec, inspectRemainderSpec] tape
  have hWrite : tape.write tape.head = tape := write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, firstBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move,
    hWrite] using hStep

private theorem first_boundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step [startSpec] firstBoundarySpec
    [secondBoundarySpec, inspectRemainderSpec] tape
  have hWrite : tape.write leftBoundary = tape := by
    rw [← hHead]
    exact write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, firstBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move,
    hWrite] using hStep

private theorem second_scan_step (tape : WorkTape)
    (hHead : tape.head ≠ leftBoundary) :
    workStep? machine { state := 2, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [startSpec, firstBoundarySpec] secondBoundarySpec
    [inspectRemainderSpec] tape
  have hWrite : tape.write tape.head = tape := write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, secondBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move,
    hWrite] using hStep

private theorem second_boundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 2, tape := tape } =
      some { state := 3, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [startSpec, firstBoundarySpec] secondBoundarySpec
    [inspectRemainderSpec] tape
  have hWrite : tape.write leftBoundary = tape := by
    rw [← hHead]
    exact write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, secondBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move,
    hWrite] using hStep

private theorem consumed_step (tape : WorkTape)
    (hHead : tape.head = consumedDividend) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 3, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [startSpec, firstBoundarySpec, secondBoundarySpec]
    inspectRemainderSpec [] tape
  have hConsumedSeparator : consumedDividend ≠ separatorSymbol := by decide
  have hConsumedUnit : consumedDividend ≠ unitSymbol := by decide
  have hWrite : tape.write consumedDividend = tape := by
    rw [← hHead]
    exact write_head_eq tape
  simpa [machine_eq_specMachine, stateSpecs, inspectRemainderSpec, hHead,
    hConsumedSeparator, hConsumedUnit, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

private theorem zero_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 3, tape := tape } =
      some { state := machine.acceptState, tape := tape } := by
  have hStep := specMachine_step
    [startSpec, firstBoundarySpec, secondBoundarySpec]
    inspectRemainderSpec [] tape
  have hNotConsumed : separatorSymbol ≠ consumedDividend := by decide
  have hWrite : tape.write separatorSymbol = tape := by
    rw [← hHead]
    exact write_head_eq tape
  rw [machine_eq_specMachine]
  simpa [specMachine, stateSpecs, inspectRemainderSpec, hHead,
    hNotConsumed, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move, hWrite] using hStep

private theorem positive_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 3, tape := tape } =
      some { state := machine.rejectState, tape := tape } := by
  have hStep := specMachine_step
    [startSpec, firstBoundarySpec, secondBoundarySpec]
    inspectRemainderSpec [] tape
  have hNotConsumed : unitSymbol ≠ consumedDividend := by decide
  have hNotSeparator : unitSymbol ≠ separatorSymbol := by decide
  have hWrite : tape.write unitSymbol = tape := by
    rw [← hHead]
    exact write_head_eq tape
  rw [machine_eq_specMachine]
  simpa [specMachine, stateSpecs, inspectRemainderSpec, hHead,
    hNotConsumed, hNotSeparator, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move,
    hWrite] using hStep

private def rightPathTape (leftSide : List WorkSymbol) :
    List WorkSymbol -> WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

@[simp] private theorem rightPathTape_moveRight_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape leftSide (head :: right)).moveRight =
      rightPathTape (head :: leftSide) right := by
  cases right <;> rfl

@[simp] private theorem workTape_moveRight_eq_rightPathTape
    (left : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    ({ left := left, head := head, right := right } : WorkTape).moveRight =
      rightPathTape (head :: left) right := by
  cases right <;> rfl

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem scanRight_list_exact
    (state : Nat) (word leftSide rightTail : List WorkSymbol)
    (hStep : forall symbol left right, symbol ∈ word ->
      workStep? machine
          { state := state
            tape := rightPathTape left (symbol :: right) } =
        some
          { state := state
            tape := rightPathTape (symbol :: left) right }) :
    workRunExact? machine word.length
        { state := state
          tape := rightPathTape leftSide (word ++ rightTail) } =
      some
        { state := state
          tape := rightPathTape (word.reverse ++ leftSide) rightTail } := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons symbol rest ih =>
      have hOne := workRunExact_one
        { state := state
          tape := rightPathTape leftSide
            (symbol :: rest ++ rightTail) }
        { state := state
          tape := rightPathTape (symbol :: leftSide)
            (rest ++ rightTail) }
        (by simpa using hStep symbol leftSide (rest ++ rightTail) (by simp))
      have hRest : forall item left right, item ∈ rest ->
          workStep? machine
              { state := state
                tape := rightPathTape left (item :: right) } =
            some
              { state := state
                tape := rightPathTape (item :: left) right } := by
        intro item left right hMem
        exact hStep item left right (by simp [hMem])
      have hTail := ih (symbol :: leftSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 rest.length _ _ _ hOne hTail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem first_scan_exact (word leftSide rightTail : List WorkSymbol)
    (hWord : forall symbol, symbol ∈ word -> symbol ≠ leftBoundary) :
    workRunExact? machine word.length
        { state := 1
          tape := rightPathTape leftSide (word ++ rightTail) } =
      some
        { state := 1
          tape := rightPathTape (word.reverse ++ leftSide) rightTail } := by
  apply scanRight_list_exact 1 word leftSide rightTail
  · intro symbol left right hMem
    simpa using first_scan_step
      (rightPathTape left (symbol :: right)) (hWord symbol hMem)

private theorem second_scan_exact (word leftSide rightTail : List WorkSymbol)
    (hWord : forall symbol, symbol ∈ word -> symbol ≠ leftBoundary) :
    workRunExact? machine word.length
        { state := 2
          tape := rightPathTape leftSide (word ++ rightTail) } =
      some
        { state := 2
          tape := rightPathTape (word.reverse ++ leftSide) rightTail } := by
  apply scanRight_list_exact 2 word leftSide rightTail
  · intro symbol left right hMem
    simpa using second_scan_step
      (rightPathTape left (symbol :: right)) (hWord symbol hMem)

private theorem consumed_scan_exact (count : Nat)
    (leftSide rightTail : List WorkSymbol) :
    workRunExact? machine count
        { state := 3
          tape := rightPathTape leftSide
            (List.replicate count consumedDividend ++ rightTail) } =
      some
        { state := 3
          tape := rightPathTape
            (List.replicate count consumedDividend ++ leftSide) rightTail } := by
  have hRun := scanRight_list_exact 3
    (List.replicate count consumedDividend) leftSide rightTail
    (by
      intro symbol left right hMem
      have hSymbol : symbol = consumedDividend :=
        List.eq_of_mem_replicate hMem
      simpa [hSymbol] using consumed_step
        (rightPathTape left (symbol :: right)) hSymbol)
  simpa using hRun

def scannedLeft (builder first exterior : List WorkSymbol)
    (consumed : Nat) : List WorkSymbol :=
  List.replicate consumed consumedDividend ++
    leftBoundary :: exterior.reverse ++
      leftBoundary :: first.reverse ++ bodyPendingSymbol :: builder

def finalConfiguration (builder first exterior tail : List WorkSymbol)
    (consumed remainder : Nat) : WorkConfiguration :=
  match remainder with
  | 0 =>
      { state := machine.acceptState
        tape :=
          { left := scannedLeft builder first exterior consumed
            head := separatorSymbol
            right := tail } }
  | remaining + 1 =>
      { state := machine.rejectState
        tape :=
          { left := scannedLeft builder first exterior consumed
            head := unitSymbol
            right := List.replicate remaining unitSymbol ++
              separatorSymbol :: tail } }

def workSteps (first exterior : List WorkSymbol) (consumed : Nat) : Nat :=
  1 + (((first.length + 1) + (exterior.length + 1)) + (consumed + 1))

theorem split_exact (builder first exterior tail : List WorkSymbol)
    (consumed remainder : Nat)
    (hFirst : forall symbol, symbol ∈ first -> symbol ≠ leftBoundary)
    (hExterior : forall symbol, symbol ∈ exterior -> symbol ≠ leftBoundary) :
    workRunExact? machine (workSteps first exterior consumed)
        { state := machine.startState
          tape :=
            { left := builder
              head := bodyPendingSymbol
              right := first ++ leftBoundary :: exterior ++
                leftBoundary :: List.replicate consumed consumedDividend ++
                  List.replicate remainder unitSymbol ++
                    separatorSymbol :: tail } } =
      some (finalConfiguration builder first exterior tail consumed remainder) := by
  let afterStart := first ++ leftBoundary :: exterior ++
    leftBoundary :: List.replicate consumed consumedDividend ++
      List.replicate remainder unitSymbol ++ separatorSymbol :: tail
  let startTape : WorkTape :=
    { left := builder
      head := bodyPendingSymbol
      right := afterStart }
  let initial : WorkConfiguration :=
    { state := machine.startState
      tape := startTape }
  let afterInitial : WorkConfiguration :=
    { state := 1
      tape := rightPathTape (bodyPendingSymbol :: builder) afterStart }
  have h0 := workRunExact_one
    initial afterInitial
    (by
      have hStart := start_step startTape (by rfl)
      simpa [initial, afterInitial, startTape, machine,
        workTape_moveRight_eq_rightPathTape] using hStart)
  have h1scan := first_scan_exact first (bodyPendingSymbol :: builder)
    (leftBoundary :: exterior ++ leftBoundary ::
      List.replicate consumed consumedDividend ++
        List.replicate remainder unitSymbol ++ separatorSymbol :: tail) hFirst
  have h1boundary := workRunExact_one
    { state := 1
      tape := rightPathTape (first.reverse ++ bodyPendingSymbol :: builder)
        (leftBoundary :: exterior ++ leftBoundary ::
          List.replicate consumed consumedDividend ++
            List.replicate remainder unitSymbol ++ separatorSymbol :: tail) }
    { state := 2
      tape := rightPathTape
        (leftBoundary :: first.reverse ++ bodyPendingSymbol :: builder)
        (exterior ++ leftBoundary ::
          List.replicate consumed consumedDividend ++
            List.replicate remainder unitSymbol ++ separatorSymbol :: tail) }
    (by simpa using (first_boundary_step
      (rightPathTape (first.reverse ++ bodyPendingSymbol :: builder)
        (leftBoundary :: exterior ++ leftBoundary ::
          List.replicate consumed consumedDividend ++
            List.replicate remainder unitSymbol ++ separatorSymbol :: tail)) rfl))
  have h1 := PipelineMachineSimulation.workRunExact?_compose machine
    first.length 1 _ _ _ h1scan h1boundary
  have h2scan := second_scan_exact exterior
    (leftBoundary :: first.reverse ++ bodyPendingSymbol :: builder)
    (leftBoundary :: List.replicate consumed consumedDividend ++
      List.replicate remainder unitSymbol ++ separatorSymbol :: tail) hExterior
  have h2boundary := workRunExact_one
    { state := 2
      tape := rightPathTape
        (exterior.reverse ++
          (leftBoundary :: first.reverse ++ bodyPendingSymbol :: builder))
        (leftBoundary :: List.replicate consumed consumedDividend ++
          List.replicate remainder unitSymbol ++ separatorSymbol :: tail) }
    { state := 3
      tape := rightPathTape
        (leftBoundary :: exterior.reverse ++ leftBoundary ::
          first.reverse ++ bodyPendingSymbol :: builder)
        (List.replicate consumed consumedDividend ++
          List.replicate remainder unitSymbol ++ separatorSymbol :: tail) }
    (by simpa using (second_boundary_step
      (rightPathTape
        (exterior.reverse ++
          (leftBoundary :: first.reverse ++ bodyPendingSymbol :: builder))
        (leftBoundary :: List.replicate consumed consumedDividend ++
          List.replicate remainder unitSymbol ++ separatorSymbol :: tail)) rfl))
  have h2 := PipelineMachineSimulation.workRunExact?_compose machine
    exterior.length 1 _ _ _ h2scan h2boundary
  have hConsumed := consumed_scan_exact consumed
    (leftBoundary :: exterior.reverse ++ leftBoundary ::
      first.reverse ++ bodyPendingSymbol :: builder)
    (List.replicate remainder unitSymbol ++ separatorSymbol :: tail)
  cases remainder with
  | zero =>
      have hInspect := workRunExact_one
        { state := 3
          tape := rightPathTape
            (List.replicate consumed consumedDividend ++
              leftBoundary :: exterior.reverse ++ leftBoundary ::
                first.reverse ++ bodyPendingSymbol :: builder)
            (separatorSymbol :: tail) }
        (finalConfiguration builder first exterior tail consumed 0)
        (by simpa [finalConfiguration, scannedLeft, rightPathTape] using (zero_step
          (rightPathTape
            (List.replicate consumed consumedDividend ++
              leftBoundary :: exterior.reverse ++ leftBoundary ::
                first.reverse ++ bodyPendingSymbol :: builder)
            (separatorSymbol :: tail)) rfl))
      have h3 := PipelineMachineSimulation.workRunExact?_compose machine
        consumed 1 _ _ _ (by simpa using hConsumed) hInspect
      have h12 := PipelineMachineSimulation.workRunExact?_compose machine
        (first.length + 1) (exterior.length + 1) _ _ _ h1
        (by simpa [List.append_assoc] using h2)
      have h123 := PipelineMachineSimulation.workRunExact?_compose machine
        ((first.length + 1) + (exterior.length + 1)) (consumed + 1)
        _ _ _ h12 (by simpa [List.append_assoc] using h3)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 (((first.length + 1) + (exterior.length + 1)) + (consumed + 1))
        _ _ _ h0 (by
          simpa [afterInitial, afterStart, List.append_assoc] using h123)
      simpa [workSteps, initial, startTape, afterStart, List.append_assoc,
        Nat.add_assoc] using hAll
  | succ remaining =>
      have hInspect := workRunExact_one
        { state := 3
          tape := rightPathTape
            (List.replicate consumed consumedDividend ++
              leftBoundary :: exterior.reverse ++ leftBoundary ::
                first.reverse ++ bodyPendingSymbol :: builder)
            (unitSymbol :: List.replicate remaining unitSymbol ++
              separatorSymbol :: tail) }
        (finalConfiguration builder first exterior tail consumed
          (remaining + 1))
        (by simpa [finalConfiguration, scannedLeft, rightPathTape] using (positive_step
          (rightPathTape
            (List.replicate consumed consumedDividend ++
              leftBoundary :: exterior.reverse ++ leftBoundary ::
                first.reverse ++ bodyPendingSymbol :: builder)
            (unitSymbol :: List.replicate remaining unitSymbol ++
              separatorSymbol :: tail)) rfl))
      have h3 := PipelineMachineSimulation.workRunExact?_compose machine
        consumed 1 _ _ _ (by simpa [List.replicate_succ] using hConsumed)
        hInspect
      have h12 := PipelineMachineSimulation.workRunExact?_compose machine
        (first.length + 1) (exterior.length + 1) _ _ _ h1
        (by simpa [List.append_assoc] using h2)
      have h123 := PipelineMachineSimulation.workRunExact?_compose machine
        ((first.length + 1) + (exterior.length + 1)) (consumed + 1)
        _ _ _ h12 (by
          simpa [List.append_assoc, List.replicate_succ] using h3)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 (((first.length + 1) + (exterior.length + 1)) + (consumed + 1))
        _ _ _ h0 (by
          simpa [afterInitial, afterStart, List.append_assoc,
            List.replicate_succ] using h123)
      simpa [workSteps, initial, startTape, afterStart, List.append_assoc,
        List.replicate_succ, Nat.add_assoc] using hAll

end Splitter

abbrev sourceMachine : WorkMachine :=
  BuilderPhysicalClassifierAllRouteDerivedFinishSplit.machine

def width {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaTokensPerClause

def clauseCount {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  problem.formulaClauseSlotCount

def quotient {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  index.val / width problem

def remainder {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  index.val % width problem

def consumed {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  quotient problem index * width problem

def exteriorPrefix {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  match index.val with
  | 0 =>
      BuilderPostDividerRawRouteClassifier.equalExteriorPrefix
        (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
        (width problem)
  | remaining + 1 =>
      BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix
        (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
        remaining (width problem)

def firstScanWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderPostDividerRawRouteClassifier.endSymbol ::
    List.replicate (clauseCount problem)
      BuilderPostDividerRawRouteClassifier.unitSymbol

def comparatorFinal {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
    (quotient problem index) (clauseCount problem)

def remainderTail {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  List.replicate (width problem)
      BuilderPostDividerRawRouteClassifier.unitSymbol ++
    (comparatorFinal problem index).tape.left.reverse ++
      (comparatorFinal problem index).tape.head ::
        (comparatorFinal problem index).tape.right

def physicalTrail {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    List WorkSymbol :=
  firstScanWord problem ++
    BuilderPostDividerRawRouteClassifier.leftBoundary ::
      (exteriorPrefix problem index).reverse ++
        BuilderPostDividerRawRouteClassifier.leftBoundary ::
          List.replicate (consumed problem index)
              BuilderPostDividerRawRouteClassifier.consumedDividend ++
            List.replicate (remainder problem index)
                BuilderPostDividerRawRouteClassifier.unitSymbol ++
              BuilderPostDividerRawRouteClassifier.separatorSymbol ::
                remainderTail problem index

theorem exteriorPrefix_safe {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderPostDividerRawRouteClassifier.SafeExteriorPrefix
      (exteriorPrefix problem index) := by
  cases hIndex : index.val with
  | zero =>
      simpa [exteriorPrefix, hIndex, width] using
        (BuilderPostDividerRawRouteClassifier.equalExteriorPrefix_safe
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
          problem.formulaTokensPerClause)
  | succ remaining =>
      simpa [exteriorPrefix, hIndex, width] using
        (BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix_safe
          (BuilderPhysicalClassifierPipeline.firstBodySlot problem)
          remaining problem.formulaTokensPerClause)

theorem firstScanWord_no_leftBoundary {language : Language}
    (problem : VerifierTableauProblem language) :
    forall symbol, symbol ∈ firstScanWord problem ->
      symbol ≠ BuilderPostDividerRawRouteClassifier.leftBoundary := by
  intro symbol hSymbol
  simp only [firstScanWord, List.mem_cons, List.mem_replicate] at hSymbol
  rcases hSymbol with hEnd | ⟨_hCount, hUnit⟩
  · subst symbol
    decide
  · subst symbol
    decide

theorem exteriorPrefix_reverse_no_leftBoundary {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    forall symbol, symbol ∈ (exteriorPrefix problem index).reverse ->
      symbol ≠ BuilderPostDividerRawRouteClassifier.leftBoundary := by
  intro symbol hSymbol
  have hOriginal : symbol ∈ exteriorPrefix problem index := by
    simpa using hSymbol
  exact BuilderPostDividerRawRouteClassifier.exteriorSymbol_ne_leftBoundary
    symbol (exteriorPrefix_safe problem index symbol hOriginal)

set_option maxRecDepth 1000000 in
theorem classifierTrail_eq_physicalTrail {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail
        problem index =
      physicalTrail problem index := by
  cases hIndex : index.val with
  | zero =>
      simp [BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierPrefix,
        BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
        BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierPrefix,
        BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierBaseFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hIndex,
        BuilderPhysicalClassifierPipeline.equalFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.equalClassifierExterior,
        BuilderPhysicalClassifierPipeline.width,
        BuilderPhysicalClassifierPipeline.clauseCount,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.sidecar,
        physicalTrail, firstScanWord, exteriorPrefix, remainderTail,
        comparatorFinal, consumed, remainder, quotient, width, clauseCount,
        renameConfiguration, List.reverse_append, List.append_assoc]
  | succ remaining =>
      simp [BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierPrefix,
        BuilderPhysicalClassifierTerminalJoin.finalConfiguration,
        BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierPrefix,
        BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.classifierBaseFinalConfiguration,
        BuilderPhysicalClassifierPipeline.finalConfiguration, hIndex,
        BuilderPhysicalClassifierPipeline.greaterFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterComparatorFinalConfiguration,
        BuilderPhysicalClassifierPipeline.greaterClassifierExterior,
        BuilderPhysicalClassifierPipeline.width,
        BuilderPhysicalClassifierPipeline.clauseCount,
        BuilderPhysicalClassifierPipeline.greaterConsumed,
        BuilderPhysicalClassifierPipeline.greaterRemainder,
        BuilderPhysicalClassifierPipeline.greaterQuotient,
        BuilderPostDividerRawRouteClassifier.shieldedComparatorFinalConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorConfiguration,
        BuilderPostDividerRawRouteClassifier.appendExteriorTape,
        BuilderPostDividerRawRouteClassifier.preservedExterior,
        BuilderPostDividerRawRouteClassifier.terminalPrefix,
        BuilderPostDividerRawRouteClassifier.sidecar,
        physicalTrail, firstScanWord, exteriorPrefix, remainderTail,
        comparatorFinal, consumed, remainder, quotient, width, clauseCount,
        renameConfiguration, List.reverse_append, List.append_assoc]

def splitterEntryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  { state := Splitter.machine.startState
    tape :=
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration
        problem index).tape }

def splitterFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  Splitter.finalConfiguration
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.builderWord
      problem index)
    (firstScanWord problem) (exteriorPrefix problem index).reverse
    (remainderTail problem index) (consumed problem index)
    (remainder problem index)

def splitterWorkSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  Splitter.workSteps (firstScanWord problem)
    (exteriorPrefix problem index).reverse (consumed problem index)

theorem splitter_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    workRunExact? Splitter.machine (splitterWorkSteps problem index)
        (splitterEntryConfiguration problem index) =
      some (splitterFinalConfiguration problem index) := by
  have hSplit := Splitter.split_exact
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.builderWord
      problem index)
    (firstScanWord problem) (exteriorPrefix problem index).reverse
    (remainderTail problem index) (consumed problem index)
    (remainder problem index) (firstScanWord_no_leftBoundary problem)
    (exteriorPrefix_reverse_no_leftBoundary problem index)
  simpa [splitterWorkSteps, splitterEntryConfiguration,
    splitterFinalConfiguration,
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration,
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.relayFinalConfiguration,
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeCell,
    hRoute,
    physicalTrail, classifierTrail_eq_physicalTrail problem index,
    List.append_assoc] using hSplit

/-! ## One fixed graph: M228, then the physical body splitter -/

open WorkMachineProgramGraph

def sourceRef : NodeRef :=
  { name := 0
    startState := sourceMachine.startState }

def splitterRef : NodeRef :=
  { name := 1
    startState := Splitter.machine.startState }

def sourceNode : Node :=
  { name := 0
    program := sourceMachine
    onAccept := .accept
    onReject := .node splitterRef }

def splitterNode : Node :=
  { name := 1
    program := Splitter.machine
    onAccept := .reject
    onReject := .reject }

def nodes : List Node := [sourceNode, splitterNode]

def graph : Graph :=
  { nodes := nodes
    entry := sourceRef }

private theorem source_noRuleAtAccept :
    NoRuleAt sourceMachine sourceMachine.acceptState := by
  exact WorkMachineChain.noRuleAtAccept
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierRelayMachine
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.dispatchMachine
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.dispatch_noRuleAtAccept

set_option maxRecDepth 1000000 in
private theorem source_noRuleAtReject :
    NoRuleAt sourceMachine sourceMachine.rejectState := by
  intro rule hRule
  change rule ∈
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.machine.rules at hRule
  change rule.sourceState ≠
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.machine.rejectState
  decide +revert

private theorem sourceNode_wellFormed : sourceNode.WellFormed := by
  exact
    ⟨BuilderPhysicalClassifierAllRouteDerivedFinishSplit.rules_pairwise_query_distinct,
      source_noRuleAtAccept, source_noRuleAtReject,
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.machine_acceptState_ne_rejectState⟩

private theorem splitterNode_wellFormed : splitterNode.WellFormed := by
  exact ⟨Splitter.rules_pairwise_query_distinct,
    Splitter.noRuleAtAccept, Splitter.noRuleAtReject,
    Splitter.machine_acceptState_ne_rejectState⟩

theorem graph_wellFormed : graph.WellFormed := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [graph, nodes, sourceNode, splitterNode]
  · intro node hNode
    simp [graph, nodes] at hNode
    rcases hNode with rfl | rfl
    · exact sourceNode_wellFormed
    · exact splitterNode_wellFormed
  · refine ⟨sourceNode, ?_, ?_, ?_⟩
    · simp [graph, nodes]
    · rfl
    · rfl
  · intro node hNode
    simp [graph, nodes] at hNode
    rcases hNode with rfl | rfl
    ·
      constructor
      · trivial
      · refine ⟨splitterNode, ?_, ?_, ?_⟩
        · simp [graph, nodes]
        · rfl
        · rfl
    ·
      exact ⟨trivial, trivial⟩

def machine : WorkMachine :=
  WorkMachineProgramGraph.machine graph

def compiledMachine : Machine := compileWorkMachine machine

set_option maxRecDepth 1000000 in
theorem rules_length : machine.rules.length = 895 := by
  rfl

theorem rules_pairwise_query_distinct :
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_accept_ne_reject graph

private theorem sourceNode_mem : sourceNode ∈ graph.nodes := by
  simp [graph, nodes]

private theorem splitterNode_mem : splitterNode ∈ graph.nodes := by
  simp [graph, nodes]

def entryConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  renameConfiguration sourceNode.encode
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.entryConfiguration
      problem index)

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    WorkConfiguration :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ =>
      endpointConfiguration .reject
        (splitterFinalConfiguration problem index).tape
  | .finish =>
      endpointConfiguration .accept
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape
  | .outOfRange =>
      endpointConfiguration .reject
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape

def workSteps {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Nat :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ _ =>
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index + 1 + splitterWorkSteps problem index + 1
  | .finish =>
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index + 1
  | .outOfRange => 0

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem configuration_ext (left right : WorkConfiguration)
    (hState : left.state = right.state)
    (hTape : left.tape = right.tape) : left = right := by
  cases left
  cases right
  simp_all

private theorem tape_ext (left right : WorkTape)
    (hLeft : left.left = right.left)
    (hHead : left.head = right.head)
    (hRight : left.right = right.right) : left = right := by
  cases left
  cases right
  simp_all

theorem source_graph_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? machine
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index)
        (entryConfiguration problem index) =
      some (renameConfiguration sourceNode.encode
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index)) := by
  exact WorkMachineProgramGraph.local_workRunExact graph sourceNode
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps problem index)
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.entryConfiguration
      problem index)
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
      problem index)
    graph_wellFormed sourceNode_mem
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workRunExact
      problem index)

private theorem source_finish_bridge_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .finish) :
    workRunExact? machine 1
        (renameConfiguration sourceNode.encode
          (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
            problem index)) =
      some (endpointConfiguration .accept
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape) := by
  have hTerminal :=
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeTerminalHolds
      problem index
  have hFinish :
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).state = sourceMachine.acceptState ∧
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape =
          (BuilderPhysicalClassifierFinishMirroredDispatch.mirrorConfiguration
            (renameConfiguration BuilderPhysicalOptionalTokenDispatch.appenderState
              (BuilderTokenAppender.finalConfiguration problem.input
                (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail
                  problem index)
                (emittedPrefix problem (index.val + 1))))).tape := by
    simpa [BuilderPhysicalClassifierAllRouteDerivedFinishSplit.RouteTerminalHolds,
      hRoute, sourceMachine] using hTerminal
  have hState :
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
        problem index).state = sourceMachine.acceptState := by
    exact hFinish.1
  have hConfiguration :
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index =
        { state := sourceMachine.acceptState
          tape :=
            (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
              problem index).tape } := by
    apply configuration_ext
    · exact hState
    · rfl
  have hStep := WorkMachineProgramGraph.accept_bridge_step graph sourceNode
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
      problem index).tape graph_wellFormed sourceNode_mem
  apply workRunExact_one
  rw [hConfiguration]
  simpa only [machine, sourceNode] using hStep

private theorem source_body_bridge_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    workRunExact? machine 1
        (renameConfiguration sourceNode.encode
          (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
            problem index)) =
      some (renameConfiguration splitterNode.encode
        (splitterEntryConfiguration problem index)) := by
  have hTerminal :=
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeTerminalHolds
      problem index
  have hBody :
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).state = sourceMachine.rejectState ∧
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape.left =
          BuilderPhysicalClassifierAllRouteDerivedFinishSplit.builderWord
            problem index ∧
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape.head =
          BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyPendingSymbol ∧
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape.right =
          BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierTrail
            problem index := by
    simpa [BuilderPhysicalClassifierAllRouteDerivedFinishSplit.RouteTerminalHolds,
      hRoute, sourceMachine] using hTerminal
  have hState :
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
        problem index).state = sourceMachine.rejectState := by
    exact hBody.1
  have hTape :
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
        problem index).tape =
      (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration
        problem index).tape := by
    apply tape_ext
    · simpa [
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.relayFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeCell,
        hRoute] using hBody.2.1
    · simpa [
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.relayFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeCell,
        hRoute] using hBody.2.2.1
    · simpa [
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.relayFinalConfiguration,
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.routeCell,
        hRoute] using hBody.2.2.2
  have hConfiguration :
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index =
        { state := sourceMachine.rejectState
          tape :=
            (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration
              problem index).tape } := by
    apply configuration_ext
    · exact hState
    · exact hTape
  have hStep := WorkMachineProgramGraph.reject_bridge_step graph sourceNode
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyFinalConfiguration
      problem index).tape graph_wellFormed sourceNode_mem
  apply workRunExact_one
  rw [hConfiguration]
  simpa only [machine, sourceNode, splitterNode, splitterRef,
    splitterEntryConfiguration, Node.encode, endpointConfiguration,
    endpointState, renameConfiguration] using hStep

theorem splitter_graph_workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem))
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val = .body clauseCoordinate tokenCoordinate) :
    workRunExact? machine (splitterWorkSteps problem index)
        (renameConfiguration splitterNode.encode
          (splitterEntryConfiguration problem index)) =
      some (renameConfiguration splitterNode.encode
        (splitterFinalConfiguration problem index)) := by
  exact WorkMachineProgramGraph.local_workRunExact graph splitterNode
    (splitterWorkSteps problem index)
    (splitterEntryConfiguration problem index)
    (splitterFinalConfiguration problem index)
    graph_wellFormed splitterNode_mem
    (splitter_workRunExact problem index clauseCoordinate tokenCoordinate hRoute)

private theorem splitter_reject_bridge_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? machine 1
        (renameConfiguration splitterNode.encode
          (splitterFinalConfiguration problem index)) =
      some (endpointConfiguration .reject
        (splitterFinalConfiguration problem index).tape) := by
  cases hRemainder : remainder problem index with
  | zero =>
      have hStep := WorkMachineProgramGraph.accept_bridge_step graph
        splitterNode (splitterFinalConfiguration problem index).tape
        graph_wellFormed splitterNode_mem
      apply workRunExact_one
      simpa [splitterFinalConfiguration, Splitter.finalConfiguration,
        hRemainder, splitterNode, endpointConfiguration, machine] using hStep
  | succ remaining =>
      have hStep := WorkMachineProgramGraph.reject_bridge_step graph
        splitterNode (splitterFinalConfiguration problem index).tape
        graph_wellFormed splitterNode_mem
      apply workRunExact_one
      simpa [splitterFinalConfiguration, Splitter.finalConfiguration,
        hRemainder, splitterNode, endpointConfiguration, machine] using hStep

theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) := by
  have hSource := source_graph_workRunExact problem index
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      have hBodyBridge := source_body_bridge_exact problem index
        clauseCoordinate tokenCoordinate hRoute
      have hSourceBody := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index) 1 _ _ _ hSource hBodyBridge
      have hSplitter := splitter_graph_workRunExact problem index
        clauseCoordinate tokenCoordinate hRoute
      have hBody := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index + 1) (splitterWorkSteps problem index)
        _ _ _ hSourceBody hSplitter
      have hFinal := splitter_reject_bridge_exact problem index
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
            problem index + 1 + splitterWorkSteps problem index)
        1 _ _ _ hBody hFinal
      simpa [workSteps, finalConfiguration, hRoute, Nat.add_assoc] using hAll
  | finish =>
      have hBridge := source_finish_bridge_exact problem index hRoute
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.workSteps
          problem index) 1 _ _ _ hSource hBridge
      simpa [workSteps, finalConfiguration, hRoute] using hAll
  | outOfRange =>
      exact False.elim
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.route_ne_outOfRange
          problem index hRoute)

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    run compiledMachine (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps problem index) (entryConfiguration problem index)
    (finalConfiguration problem index) (workRunExact problem index)

private theorem workRunExact_succ_split_last (selectedMachine : WorkMachine) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? selectedMachine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? selectedMachine steps initial = some before ∧
          workStep? selectedMachine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? selectedMachine initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps inductionHypothesis =>
      intro initial final hRun
      cases hStep : workStep? selectedMachine initial with
      | none =>
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some next => workRunExact? selectedMachine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? selectedMachine (steps + 1) next =
              some final := by
            change
              (match workStep? selectedMachine initial with
               | none => none
               | some result =>
                   workRunExact? selectedMachine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases inductionHypothesis next final hTail with
            ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? selectedMachine initial with
             | none => none
             | some result => workRunExact? selectedMachine steps result) =
              some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (selectedMachine : WorkMachine) (configuration next : WorkConfiguration)
    (hStep : workStep? selectedMachine configuration = some next) :
    selectedMachine.isHalted configuration = false := by
  cases hHalted : selectedMachine.isHalted configuration with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    0 < workSteps problem index := by
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      simp [workSteps, hRoute]
  | finish =>
      simp [workSteps, hRoute]
  | outOfRange =>
      exact False.elim
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.route_ne_outOfRange
          problem index hRoute)

theorem one_step_short_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false := by
  let short := workSteps problem index - 1
  have hSucc : short + 1 = workSteps problem index := by
    have hPositive := workSteps_positive problem index
    dsimp [short]
    omega
  have hExact := workRunExact problem index
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last machine short
      (entryConfiguration problem index) (finalConfiguration problem index)
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short (entryConfiguration problem index) =
      before :=
    workRun_eq_of_workRunExact machine short (entryConfiguration problem index)
      before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some machine before
    (finalConfiguration problem index) hLast

/-! ## Route-specific terminal contract -/

def RouteTerminalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    Prop :=
  match BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute problem index.val with
  | .body _ tokenCoordinate =>
      (finalConfiguration problem index).state = machine.rejectState ∧
      remainder problem index = tokenCoordinate.val ∧
      (finalConfiguration problem index).tape.head =
        (if tokenCoordinate.val = 0 then
          BuilderPostDividerRawRouteClassifier.separatorSymbol
        else BuilderPostDividerRawRouteClassifier.unitSymbol) ∧
      (finalConfiguration problem index).tape =
        (splitterFinalConfiguration problem index).tape
  | .finish =>
      (finalConfiguration problem index).state = machine.acceptState ∧
      (finalConfiguration problem index).tape =
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.finalConfiguration
          problem index).tape
  | .outOfRange => False

set_option maxRecDepth 1000000 in
theorem routeTerminalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    RouteTerminalHolds problem index := by
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      simp only [RouteTerminalHolds, hRoute]
      have hDecoded :=
        BuilderPostDividerRawRouteClassifier.decodedRouteHolds_of_not_outOfRange
          problem index.val (by simp [hRoute])
      have hDecodedBody :
          index.val / problem.formulaTokensPerClause = clauseCoordinate.val ∧
          index.val % problem.formulaTokensPerClause = tokenCoordinate.val ∧
          (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
            (index.val / problem.formulaTokensPerClause)
            problem.formulaClauseSlotCount).state =
              BuilderPostDividerRawRouteClassifier.comparatorMachine.acceptState := by
        simpa [BuilderPostDividerRawRouteClassifier.DecodedRouteHolds,
          hRoute] using hDecoded
      have hRemainder : remainder problem index = tokenCoordinate.val := by
        simpa [remainder, width] using hDecodedBody.2.1
      refine ⟨?_, hRemainder, ?_, ?_⟩
      · simp [hRoute, finalConfiguration,
          endpointConfiguration, endpointState, machine,
          WorkMachineProgramGraph.machine]
      · rw [← hRemainder]
        cases hValue : remainder problem index with
        | zero =>
            simp [finalConfiguration, hRoute, endpointConfiguration,
              splitterFinalConfiguration, Splitter.finalConfiguration, hValue]
        | succ remaining =>
            simp [finalConfiguration, hRoute, endpointConfiguration,
              splitterFinalConfiguration, Splitter.finalConfiguration, hValue]
      · simp [finalConfiguration, hRoute, endpointConfiguration]
  | finish =>
      simp [RouteTerminalHolds, hRoute, finalConfiguration,
        endpointConfiguration, endpointState, machine,
        WorkMachineProgramGraph.machine]
  | outOfRange =>
      exact False.elim
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.route_ne_outOfRange
          problem index hRoute)

/-! ## Polynomial overhead of the physical split -/

theorem splitterWorkSteps_le_size {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    splitterWorkSteps problem index ≤
      8 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
        BuilderFullScheduleCursorController.bodySlotCount problem +
        width problem + 1) := by
  have hWidth : 0 < width problem :=
    BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hCount : clauseCount problem ≤
      BuilderFullScheduleCursorController.bodySlotCount problem := by
    rw [BuilderFullScheduleCursorController.bodySlotCount_eq]
    change clauseCount problem ≤ clauseCount problem * width problem + 1
    have hMul := Nat.mul_le_mul_left (clauseCount problem) hWidth
    simp only [Nat.mul_one] at hMul
    omega
  have hIndex : index.val ≤
      BuilderFullScheduleCursorController.bodySlotCount problem :=
    Nat.le_of_lt index.isLt
  have hConsumed : consumed problem index ≤ index.val :=
    Nat.div_mul_le_self _ _
  cases hIndexVal : index.val with
  | zero =>
      simp only [splitterWorkSteps, Splitter.workSteps, firstScanWord,
        exteriorPrefix, hIndexVal,
        BuilderPostDividerRawRouteClassifier.equalExteriorPrefix,
        List.length_reverse, List.length_append, List.length_cons,
        List.length_replicate]
      omega
  | succ remaining =>
      simp only [splitterWorkSteps, Splitter.workSteps, firstScanWord,
        exteriorPrefix, hIndexVal,
        BuilderPostDividerRawRouteClassifier.greaterExteriorPrefix,
        List.length_reverse, List.length_append, List.length_cons,
        List.length_replicate]
      omega

def splitterRawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 60)
    (BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.sizePolynomial
      verifier)

theorem splitterCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * (splitterWorkSteps problem index + 2) ≤
      (splitterRawTimeBound problem.verifier).eval problem.input.length := by
  have hSplit := splitterWorkSteps_le_size problem index
  unfold splitterRawTimeBound
  simp only [NatPolynomial.eval_mul, NatPolynomial.eval_constant]
  rw [BuilderPhysicalClassifierAllRouteStagedRequestMirroredDispatch.sizePolynomial_eval]
  change 6 * (splitterWorkSteps problem index + 2) ≤
    60 * (BuilderPhysicalClassifierPipeline.firstBodySlot problem +
      BuilderFullScheduleCursorController.bodySlotCount problem +
      width problem + 1)
  omega

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.rawTimeBound verifier)
    (splitterRawTimeBound verifier)

theorem compiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language)
    (index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem)) :
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hSource :=
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.compiledSteps_le_rawTimeBound
      problem index
  have hSplit := splitterCompiledSteps_le_rawTimeBound problem index
  simp only [rawTimeBound, NatPolynomial.eval_add]
  cases hRoute : BuilderArbitrarySlotPostHeaderDecoder.postHeaderRoute
      problem index.val with
  | body clauseCoordinate tokenCoordinate =>
      simp only [workSteps, hRoute]
      omega
  | finish =>
      simp only [workSteps, hRoute]
      omega
  | outOfRange =>
      exact False.elim
        (BuilderPhysicalClassifierAllRouteDerivedFinishSplit.route_ne_outOfRange
          problem index hRoute)

def AllRouteBodyRemainderSplitHolds {language : Language}
    (problem : VerifierTableauProblem language) : Prop :=
  ∀ index : Fin (BuilderFullScheduleCursorController.bodySlotCount problem),
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.classifierWorkspace
        problem index =
      WorkSymbol.blank ::
        BuilderPhysicalClassifierAllRouteDerivedFinishSplit.builderWord
          problem index ∧
    workRunExact? machine (workSteps problem index)
        (entryConfiguration problem index) =
      some (finalConfiguration problem index) ∧
    run compiledMachine (6 * workSteps problem index)
        (encodeWorkConfiguration (entryConfiguration problem index)) =
      encodeWorkConfiguration (finalConfiguration problem index) ∧
    machine.isHalted
      (workRun machine (workSteps problem index - 1)
        (entryConfiguration problem index)) = false ∧
    RouteTerminalHolds problem index ∧
    6 * workSteps problem index ≤
      (rawTimeBound problem.verifier).eval problem.input.length

theorem allRouteBodyRemainderSplitHolds {language : Language}
    (problem : VerifierTableauProblem language) :
    AllRouteBodyRemainderSplitHolds problem := by
  intro index
  exact ⟨rfl, workRunExact problem index, run_compile_exact problem index,
    one_step_short_not_halted problem index, routeTerminalHolds problem index,
    compiledSteps_le_rawTimeBound problem index⟩

/-- M229 closes the physical zero-versus-positive body-remainder read edge
after M228. One fixed collision-free 895-rule graph preserves the derived
Finish endpoint and runs a 36-rule splitter over the actual retained divider
ledger for every body coordinate. The terminal tape distinguishes zero from
positive token coordinates, with exact work and compiled execution,
one-step-short nonhalting, and an encoded-source-size polynomial bound.
Clause occupancy, body-token and padding synthesis, successive-coordinate
connection, the repeated builder loop, builder RawRefinement, and the packaged
Cook--Levin reduction remain open. -/
theorem cook_levin_builder_physical_classifier_all_route_body_remainder_split_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    Splitter.rules.length = 36 ∧
    machine.rules.length = 895 ∧
    machine.rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    machine.acceptState ≠ machine.rejectState ∧
    (∀ request,
      BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyPendingSymbol ≠
        BuilderPhysicalOptionalTokenDispatch.requestSymbol request) ∧
    AllRouteBodyRemainderSplitHolds problem := by
  exact ⟨Splitter.rules_length, rules_length, rules_pairwise_query_distinct,
    machine_acceptState_ne_rejectState,
    BuilderPhysicalClassifierAllRouteDerivedFinishSplit.bodyPendingSymbol_ne_requestSymbol,
    allRouteBodyRemainderSplitHolds problem⟩

end BuilderPhysicalClassifierAllRouteBodyRemainderSplit

end CookLevin

end PNP.Concrete
