/-
Copyright (c) 2026 PNP Labs.

An arbitrary-coordinate outer router for the concrete Cook--Levin token
schedule.

The semantic router decomposes every direct token coordinate at the exact
header boundary.  A separate literal finite work machine compares two unary
numbers and therefore decides the same header/post-header branch without a
coordinate-specific transition table.  This module does not decode a body
coordinate or emit a token.
-/

import PNP.Concrete.CookLevinBuilderFullScheduleCursorController

namespace PNP.Concrete

namespace CookLevin

namespace BuilderArbitrarySlotHeaderRouter

open PipelineTape PipelineStateNamespace PipelineStageBridges

/-! ## Exact semantic outer route -/

/-- The two top-level regions of the complete direct token schedule. -/
inductive OuterRoute where
  | header (coordinate : Nat)
  | postHeader (remainder : Nat)
  deriving DecidableEq, Repr

/-- Direct lookup after the header: the complete rectangular clause-token
region followed by the unique final `Finish` slot. -/
def postHeaderSlotDirect {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) :
    Option (Option CNFToken) :=
  DirectSlot.append
    (problem.formulaClauseSlotCount * problem.formulaTokensPerClause)
    problem.formulaClauseTokenSlotDirect
    (DirectSlot.singleton (some CNFToken.finish)) index

/-- Route an arbitrary natural coordinate at the exact first-body boundary. -/
def outerRoute {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    OuterRoute :=
  if coordinate < BuilderFullScheduleCursorController.firstBodySlot problem then
    .header coordinate
  else
    .postHeader
      (coordinate - BuilderFullScheduleCursorController.firstBodySlot problem)

/-- The router is definitionally faithful to the top-level `DirectSlot.append`
used by `formulaTokenSlotDirect`; no schedule list is materialized. -/
theorem formulaTokenSlotDirect_route {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    problem.formulaTokenSlotDirect coordinate =
      match outerRoute problem coordinate with
      | .header headerCoordinate =>
          problem.formulaHeaderTokenSlotDirect headerCoordinate
      | .postHeader remainder => postHeaderSlotDirect problem remainder := by
  unfold VerifierTableauProblem.formulaTokenSlotDirect outerRoute
    postHeaderSlotDirect
  rw [BuilderFullScheduleCursorController.firstBodySlot_eq]
  unfold DirectSlot.append
  split <;> rfl

theorem outerRoute_eq_header_iff {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate headerCoordinate : Nat) :
    outerRoute problem coordinate = .header headerCoordinate ↔
      coordinate < BuilderFullScheduleCursorController.firstBodySlot problem ∧
        headerCoordinate = coordinate := by
  unfold outerRoute
  by_cases hLess :
      coordinate < BuilderFullScheduleCursorController.firstBodySlot problem
  · simp [hLess, eq_comm]
  · simp [hLess]

theorem outerRoute_eq_postHeader_iff {language : Language}
    (problem : VerifierTableauProblem language) (coordinate remainder : Nat) :
    outerRoute problem coordinate = .postHeader remainder ↔
      BuilderFullScheduleCursorController.firstBodySlot problem ≤ coordinate ∧
        remainder = coordinate -
          BuilderFullScheduleCursorController.firstBodySlot problem := by
  unfold outerRoute
  by_cases hLess :
      coordinate < BuilderFullScheduleCursorController.firstBodySlot problem
  · simp [hLess]
    omega
  · have hLe : BuilderFullScheduleCursorController.firstBodySlot problem ≤
        coordinate := by omega
    simp [hLess, hLe, eq_comm]

/-! ## Literal unary comparison table -/

namespace RawRouter

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

abbrev unitSymbol : WorkSymbol := BuilderUnaryPolynomial.unitSymbol
abbrev separatorSymbol : WorkSymbol := BuilderUnaryPolynomial.separatorSymbol
abbrev endSymbol : WorkSymbol := BuilderUnaryPolynomial.scratchEndSymbol
abbrev coordinateMark : WorkSymbol := BuilderUnaryPolynomial.registerMarkSymbol
def boundaryMark : WorkSymbol := WorkSymbol.oneZero
def leftBoundary : WorkSymbol := leftMarker

private def keepAction := BuilderUnaryPolynomial.keepAction
private def writeAction := BuilderUnaryPolynomial.writeAction
private def deadAction := BuilderUnaryPolynomial.deadAction

private def seekCoordinateSpec : StateSpec := fun read =>
  if read = coordinateMark then
    keepAction 0 .right read
  else if read = unitSymbol then
    writeAction 1 coordinateMark .right
  else if read = separatorSymbol then
    keepAction 4 .right read
  else
    deadAction 5 read

private def seekSeparatorSpec : StateSpec := fun read =>
  if read = unitSymbol then
    keepAction 1 .right read
  else if read = separatorSymbol then
    keepAction 2 .right read
  else
    deadAction 5 read

private def seekBoundarySpec : StateSpec := fun read =>
  if read = boundaryMark then
    keepAction 2 .right read
  else if read = unitSymbol then
    writeAction 3 boundaryMark .left
  else if read = endSymbol then
    keepAction 7 .stay read
  else
    deadAction 5 read

private def rewindSpec : StateSpec := fun read =>
  if read = boundaryMark ∨ read = separatorSymbol ∨
      read = unitSymbol ∨ read = coordinateMark then
    keepAction 3 .left read
  else if read = leftBoundary then
    keepAction 0 .right read
  else
    deadAction 5 read

private def checkBoundarySpec : StateSpec := fun read =>
  if read = boundaryMark then
    keepAction 4 .right read
  else if read = unitSymbol then
    keepAction 6 .stay read
  else if read = endSymbol then
    keepAction 7 .stay read
  else
    deadAction 5 read

private def deadSpec : StateSpec := fun read => deadAction 5 read

private def stateSpecs : List StateSpec :=
  [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec,
    checkBoundarySpec, deadSpec]

def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

/-- A fixed 54-rule machine.  States 6 and 7 are respectively accept and
reject; state 5 is an explicit nonhalting dead self-loop. -/
def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 6
    rejectState := 7 }

theorem rules_length : rules.length = 54 := by
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

theorem rule_source_ne_acceptState (rule : WorkRule)
    (hRule : rule ∈ machine.rules) :
    rule.sourceState ≠ machine.acceptState := by
  have hBound := rulesFrom_source_lt 0 stateSpecs rule (by
    simpa [machine, rules] using hRule)
  simpa [machine, stateSpecs] using Nat.ne_of_lt hBound

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

private theorem machine_eq_specMachine : machine = specMachine stateSpecs := by
  rfl

private theorem seekCoordinate_mark_step (tape : WorkTape)
    (hHead : tape.head = coordinateMark) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step [] seekCoordinateSpec
    [seekSeparatorSpec, seekBoundarySpec, rewindSpec, checkBoundarySpec,
      deadSpec] tape
  have hWrite : tape.write coordinateMark = tape := by
    rw [← hHead]
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, seekCoordinateSpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite]
    using hStep

private theorem seekCoordinate_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 0, tape := tape } =
      some
        { state := 1
          tape := (tape.write coordinateMark).moveRight } := by
  have hStep := specMachine_step [] seekCoordinateSpec
    [seekSeparatorSpec, seekBoundarySpec, rewindSpec, checkBoundarySpec,
      deadSpec] tape
  have hUnitCoordinate : unitSymbol ≠ coordinateMark := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekCoordinateSpec, hHead,
    hUnitCoordinate, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem seekCoordinate_separator_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 4, tape := tape.moveRight } := by
  have hStep := specMachine_step [] seekCoordinateSpec
    [seekSeparatorSpec, seekBoundarySpec, rewindSpec, checkBoundarySpec,
      deadSpec] tape
  have hWrite : tape.write separatorSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  have hSeparatorCoordinate : separatorSymbol ≠ coordinateMark := by decide
  have hSeparatorUnit : separatorSymbol ≠ unitSymbol := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekCoordinateSpec, hHead,
    hSeparatorCoordinate, hSeparatorUnit, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

private theorem seekSeparator_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 1, tape := tape.moveRight } := by
  have hStep := specMachine_step [seekCoordinateSpec] seekSeparatorSpec
    [seekBoundarySpec, rewindSpec, checkBoundarySpec, deadSpec] tape
  have hWrite : tape.write unitSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, seekSeparatorSpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite]
    using hStep

private theorem seekSeparator_separator_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step [seekCoordinateSpec] seekSeparatorSpec
    [seekBoundarySpec, rewindSpec, checkBoundarySpec, deadSpec] tape
  have hWrite : tape.write separatorSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  have hSeparatorUnit : separatorSymbol ≠ unitSymbol := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekSeparatorSpec, hHead,
    hSeparatorUnit, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move, hWrite] using hStep

private theorem seekBoundary_mark_step (tape : WorkTape)
    (hHead : tape.head = boundaryMark) :
    workStep? machine { state := 2, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec] seekBoundarySpec
    [rewindSpec, checkBoundarySpec, deadSpec] tape
  have hWrite : tape.write boundaryMark = tape := by
    rw [← hHead]
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, seekBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite]
    using hStep

private theorem seekBoundary_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 2, tape := tape } =
      some
        { state := 3
          tape := (tape.write boundaryMark).moveLeft } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec] seekBoundarySpec
    [rewindSpec, checkBoundarySpec, deadSpec] tape
  have hUnitBoundary : unitSymbol ≠ boundaryMark := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekBoundarySpec, hHead,
    hUnitBoundary, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem seekBoundary_end_step (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workStep? machine { state := 2, tape := tape } =
      some { state := 7, tape := tape } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec] seekBoundarySpec
    [rewindSpec, checkBoundarySpec, deadSpec] tape
  have hWrite : tape.write endSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  have hEndBoundary : endSymbol ≠ boundaryMark := by decide
  have hEndUnit : endSymbol ≠ unitSymbol := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move, hWrite, hEndBoundary, hEndUnit] using hStep

private theorem rewind_payload_step (tape : WorkTape)
    (hHead : tape.head = boundaryMark ∨ tape.head = separatorSymbol ∨
      tape.head = unitSymbol ∨ tape.head = coordinateMark) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 3, tape := tape.moveLeft } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec] rewindSpec
    [checkBoundarySpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, rewindSpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem rewind_leftBoundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec] rewindSpec
    [checkBoundarySpec, deadSpec] tape
  have hBoundary : leftBoundary ≠ boundaryMark := by decide
  have hSeparator : leftBoundary ≠ separatorSymbol := by decide
  have hUnit : leftBoundary ≠ unitSymbol := by decide
  have hCoordinate : leftBoundary ≠ coordinateMark := by decide
  have hWrite : tape.write leftBoundary = tape := by
    rw [← hHead]
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, rewindSpec, hHead,
    hBoundary, hSeparator, hUnit, hCoordinate, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

private theorem checkBoundary_mark_step (tape : WorkTape)
    (hHead : tape.head = boundaryMark) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 4, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec]
    checkBoundarySpec [deadSpec] tape
  have hWrite : tape.write boundaryMark = tape := by
    rw [← hHead]
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, checkBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite]
    using hStep

private theorem checkBoundary_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 6, tape := tape } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec]
    checkBoundarySpec [deadSpec] tape
  have hWrite : tape.write unitSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  have hUnitBoundary : unitSymbol ≠ boundaryMark := by decide
  simpa [machine_eq_specMachine, stateSpecs, checkBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite,
    hUnitBoundary] using hStep

private theorem checkBoundary_end_step (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 7, tape := tape } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec]
    checkBoundarySpec [deadSpec] tape
  have hWrite : tape.write endSymbol = tape := by
    rw [← hHead]
    cases tape
    rfl
  have hEndBoundary : endSymbol ≠ boundaryMark := by decide
  have hEndUnit : endSymbol ≠ unitSymbol := by decide
  simpa [machine_eq_specMachine, stateSpecs, checkBoundarySpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move, hWrite, hEndBoundary, hEndUnit] using hStep

/-! ### Exact generic traces -/

private def rightPathTape (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

private def leftPathTape (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: left => { left := left, head := head, right := rightSide }

@[simp] private theorem rightPathTape_moveRight_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape leftSide (head :: right)).moveRight =
      rightPathTape (head :: leftSide) right := by
  cases right <;> rfl

@[simp] private theorem rightPathTape_write_cons
    (leftSide : List WorkSymbol) (head write : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape leftSide (head :: right)).write write =
      rightPathTape leftSide (write :: right) := by
  rfl

@[simp] private theorem rightPathTape_write_moveLeft_append_singleton
    (leftPrefix : List WorkSymbol) (leftEnd head write : WorkSymbol)
    (right : List WorkSymbol) :
    ((rightPathTape (leftPrefix ++ [leftEnd])
      (head :: right)).write write).moveLeft =
      leftPathTape (write :: right) (leftPrefix ++ [leftEnd]) := by
  cases leftPrefix <;> rfl

@[simp] private theorem rightPathTape_moveLeft_append_singleton
    (leftPrefix : List WorkSymbol) (leftEnd head : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape (leftPrefix ++ [leftEnd]) (head :: right)).moveLeft =
      leftPathTape (head :: right) (leftPrefix ++ [leftEnd]) := by
  cases leftPrefix <;> rfl

@[simp] private theorem leftPathTape_moveLeft_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).moveLeft =
      leftPathTape (head :: rightSide) left := by
  cases left <;> rfl

@[simp] private theorem leftPathTape_moveRight_singleton
    (rightSide : List WorkSymbol) (head : WorkSymbol) :
    (leftPathTape rightSide [head]).moveRight =
      rightPathTape [head] rightSide := by
  cases rightSide <;> rfl

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem replicate_append_self_cons (count : Nat) (item : α)
    (tail : List α) :
    List.replicate count item ++ item :: tail =
      item :: (List.replicate count item ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: (List.replicate count item ++ item :: tail) =
        item :: item :: (List.replicate count item ++ tail)
      exact congrArg (List.cons item) ih

private theorem coordinate_marks_exact (count : Nat)
    (leftSide rightTail : List WorkSymbol) :
    workRunExact? machine count
        { state := 0
          tape := rightPathTape leftSide
            (List.replicate count coordinateMark ++ rightTail) } =
      some
        { state := 0
          tape := rightPathTape
            ((List.replicate count coordinateMark).reverse ++ leftSide)
            rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hOne := workRunExact_one
        { state := 0
          tape := rightPathTape leftSide
            (coordinateMark ::
              (List.replicate count coordinateMark ++ rightTail)) }
        { state := 0
          tape := rightPathTape (coordinateMark :: leftSide)
            (List.replicate count coordinateMark ++ rightTail) } (by
          apply seekCoordinate_mark_step
          rfl)
      have hTail := ih (coordinateMark :: leftSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count
        { state := 0
          tape := rightPathTape leftSide
            (coordinateMark ::
              (List.replicate count coordinateMark ++ rightTail)) }
        { state := 0
          tape := rightPathTape (coordinateMark :: leftSide)
            (List.replicate count coordinateMark ++ rightTail) }
        { state := 0
          tape := rightPathTape
            ((List.replicate count coordinateMark).reverse ++
              coordinateMark :: leftSide) rightTail }
        hOne hTail
      simpa [List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem separator_units_exact (count : Nat)
    (leftSide rightTail : List WorkSymbol) :
    workRunExact? machine count
        { state := 1
          tape := rightPathTape leftSide
            (List.replicate count unitSymbol ++ rightTail) } =
      some
        { state := 1
          tape := rightPathTape
            ((List.replicate count unitSymbol).reverse ++ leftSide)
            rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hOne := workRunExact_one
        { state := 1
          tape := rightPathTape leftSide
            (unitSymbol :: (List.replicate count unitSymbol ++ rightTail)) }
        { state := 1
          tape := rightPathTape (unitSymbol :: leftSide)
            (List.replicate count unitSymbol ++ rightTail) } (by
          apply seekSeparator_unit_step
          rfl)
      have hTail := ih (unitSymbol :: leftSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count _ _ _ hOne hTail
      simpa [List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem boundary_marks_exact (count : Nat)
    (leftSide rightTail : List WorkSymbol) :
    workRunExact? machine count
        { state := 2
          tape := rightPathTape leftSide
            (List.replicate count boundaryMark ++ rightTail) } =
      some
        { state := 2
          tape := rightPathTape
            ((List.replicate count boundaryMark).reverse ++ leftSide)
            rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hOne := workRunExact_one
        { state := 2
          tape := rightPathTape leftSide
            (boundaryMark ::
              (List.replicate count boundaryMark ++ rightTail)) }
        { state := 2
          tape := rightPathTape (boundaryMark :: leftSide)
            (List.replicate count boundaryMark ++ rightTail) } (by
          apply seekBoundary_mark_step
          rfl)
      have hTail := ih (boundaryMark :: leftSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count _ _ _ hOne hTail
      simpa [List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem check_marks_exact (count : Nat)
    (leftSide rightTail : List WorkSymbol) :
    workRunExact? machine count
        { state := 4
          tape := rightPathTape leftSide
            (List.replicate count boundaryMark ++ rightTail) } =
      some
        { state := 4
          tape := rightPathTape
            ((List.replicate count boundaryMark).reverse ++ leftSide)
            rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hOne := workRunExact_one
        { state := 4
          tape := rightPathTape leftSide
            (boundaryMark ::
              (List.replicate count boundaryMark ++ rightTail)) }
        { state := 4
          tape := rightPathTape (boundaryMark :: leftSide)
            (List.replicate count boundaryMark ++ rightTail) } (by
          apply checkBoundary_mark_step
          rfl)
      have hTail := ih (boundaryMark :: leftSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count _ _ _ hOne hTail
      simpa [List.replicate_succ, List.reverse_cons, List.append_assoc,
        Nat.add_comm] using hAll

private theorem rewind_exact (symbols : List WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ symbols,
      symbol = boundaryMark ∨ symbol = separatorSymbol ∨
      symbol = unitSymbol ∨ symbol = coordinateMark) :
    workRunExact? machine symbols.length
        { state := 3
          tape := leftPathTape rightSide (symbols ++ leftTail) } =
      some
        { state := 3
          tape := leftPathTape (symbols.reverse ++ rightSide) leftTail } := by
  induction symbols generalizing rightSide with
  | nil => rfl
  | cons first rest ih =>
      have hFirst := hSymbols first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest,
          symbol = boundaryMark ∨ symbol = separatorSymbol ∨
          symbol = unitSymbol ∨ symbol = coordinateMark := by
        intro symbol hMem
        exact hSymbols symbol (List.Mem.tail first hMem)
      have hOne := workRunExact_one
        { state := 3
          tape := leftPathTape rightSide (first :: rest ++ leftTail) }
        { state := 3
          tape := leftPathTape (first :: rightSide) (rest ++ leftTail) } (by
          simpa using rewind_payload_step
            (leftPathTape rightSide (first :: rest ++ leftTail)) hFirst)
      have hTail := ih (first :: rightSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 rest.length _ _ _ hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

/-! ### Canonical comparison configurations -/

def comparisonWord (processed coordinate boundary : Nat) :
    List WorkSymbol :=
  List.replicate processed coordinateMark ++
    List.replicate coordinate unitSymbol ++
    separatorSymbol ::
      (List.replicate processed boundaryMark ++
        List.replicate boundary unitSymbol ++ [endSymbol])

def comparisonTape (processed coordinate boundary : Nat) : WorkTape :=
  rightPathTape [leftBoundary]
    (comparisonWord processed coordinate boundary)

def loopConfiguration (processed coordinate boundary : Nat) :
    WorkConfiguration :=
  { state := 0, tape := comparisonTape processed coordinate boundary }

inductive ComparisonResult where
  | less (processed remainingBoundary : Nat)
  | equal (processed : Nat)
  | greater (processed remainingCoordinate : Nat)
  deriving DecidableEq, Repr

def ComparisonResult.isLess : ComparisonResult → Bool
  | .less _ _ => true
  | .equal _ => false
  | .greater _ _ => false

def resultConfiguration : ComparisonResult → WorkConfiguration
  | .less processed remainingBoundary =>
      { state := machine.acceptState
        tape :=
          { left := List.replicate processed boundaryMark ++
              separatorSymbol ::
                (List.replicate processed coordinateMark ++ [leftBoundary])
            head := unitSymbol
            right := List.replicate remainingBoundary unitSymbol ++ [endSymbol] } }
  | .equal processed =>
      { state := machine.rejectState
        tape :=
          { left := List.replicate processed boundaryMark ++
              separatorSymbol ::
                (List.replicate processed coordinateMark ++ [leftBoundary])
            head := endSymbol
            right := [] } }
  | .greater processed remainingCoordinate =>
      { state := machine.rejectState
        tape :=
          { left := List.replicate processed boundaryMark ++
              separatorSymbol ::
                (List.replicate remainingCoordinate unitSymbol ++
                  List.replicate (processed + 1) coordinateMark ++
                    [leftBoundary])
            head := endSymbol
            right := [] } }

def compareResult : Nat → Nat → Nat → ComparisonResult
  | processed, 0, 0 => .equal processed
  | processed, 0, boundary + 1 => .less processed boundary
  | processed, coordinate + 1, 0 => .greater processed coordinate
  | processed, coordinate + 1, boundary + 1 =>
      compareResult (processed + 1) coordinate boundary

def loopSteps : Nat → Nat → Nat → Nat
  | processed, 0, 0 => 2 * processed + 2
  | processed, 0, _boundary + 1 => 2 * processed + 2
  | processed, coordinate + 1, 0 => 2 * processed + coordinate + 3
  | processed, coordinate + 1, boundary + 1 =>
      4 * processed + 2 * coordinate + 6 +
        loopSteps (processed + 1) coordinate boundary

private theorem less_terminal_exact (processed remainingBoundary : Nat) :
    workRunExact? machine (2 * processed + 2)
        (loopConfiguration processed 0 (remainingBoundary + 1)) =
      some (resultConfiguration (.less processed remainingBoundary)) := by
  let coordinateLeft :=
    (List.replicate processed coordinateMark).reverse ++ [leftBoundary]
  let boundaryTail :=
    List.replicate processed boundaryMark ++
      unitSymbol :: List.replicate remainingBoundary unitSymbol ++ [endSymbol]
  let c0 := loopConfiguration processed 0 (remainingBoundary + 1)
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape coordinateLeft
        (separatorSymbol :: boundaryTail) }
  let c2 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape (separatorSymbol :: coordinateLeft) boundaryTail }
  let c3 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape
        ((List.replicate processed boundaryMark).reverse ++
          separatorSymbol :: coordinateLeft)
        (unitSymbol ::
          List.replicate remainingBoundary unitSymbol ++ [endSymbol]) }
  let c4 := resultConfiguration (.less processed remainingBoundary)
  have h01 : workRunExact? machine processed c0 = some c1 := by
    simpa [c0, c1, coordinateLeft, boundaryTail, loopConfiguration,
      comparisonTape, comparisonWord, List.replicate_succ,
      List.append_assoc] using
        coordinate_marks_exact processed [leftBoundary]
          (separatorSymbol :: boundaryTail)
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    simpa [c1, c2] using
      seekCoordinate_separator_step c1.tape (by rfl)
  have h23 : workRunExact? machine processed c2 = some c3 := by
    simpa [c2, c3, boundaryTail] using
      check_marks_exact processed (separatorSymbol :: coordinateLeft)
        (unitSymbol ::
          List.replicate remainingBoundary unitSymbol ++ [endSymbol])
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    have hStep := checkBoundary_unit_step c3.tape (by rfl)
    simpa [c3, c4, coordinateLeft, resultConfiguration, rightPathTape,
      machine, List.append_assoc] using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    processed 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1) processed c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + processed) 1 c0 c3 c4 h03 h34
  have hCount : processed + 1 + processed + 1 = 2 * processed + 2 := by
    omega
  rw [← hCount]
  simpa [c0, c4] using h04

private theorem equal_terminal_exact (processed : Nat) :
    workRunExact? machine (2 * processed + 2)
        (loopConfiguration processed 0 0) =
      some (resultConfiguration (.equal processed)) := by
  let coordinateLeft :=
    (List.replicate processed coordinateMark).reverse ++ [leftBoundary]
  let boundaryTail :=
    List.replicate processed boundaryMark ++ [endSymbol]
  let c0 := loopConfiguration processed 0 0
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape coordinateLeft
        (separatorSymbol :: boundaryTail) }
  let c2 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape (separatorSymbol :: coordinateLeft) boundaryTail }
  let c3 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape
        ((List.replicate processed boundaryMark).reverse ++
          separatorSymbol :: coordinateLeft) [endSymbol] }
  let c4 := resultConfiguration (.equal processed)
  have h01 : workRunExact? machine processed c0 = some c1 := by
    simpa [c0, c1, coordinateLeft, boundaryTail, loopConfiguration,
      comparisonTape, comparisonWord, List.append_assoc] using
        coordinate_marks_exact processed [leftBoundary]
          (separatorSymbol :: boundaryTail)
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    simpa [c1, c2] using
      seekCoordinate_separator_step c1.tape (by rfl)
  have h23 : workRunExact? machine processed c2 = some c3 := by
    simpa [c2, c3, boundaryTail] using
      check_marks_exact processed (separatorSymbol :: coordinateLeft)
        [endSymbol]
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    have hStep := checkBoundary_end_step c3.tape (by rfl)
    simpa [c3, c4, coordinateLeft, resultConfiguration, rightPathTape,
      machine, List.append_assoc] using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    processed 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1) processed c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + processed) 1 c0 c3 c4 h03 h34
  have hCount : processed + 1 + processed + 1 = 2 * processed + 2 := by
    omega
  rw [← hCount]
  simpa [c0, c4] using h04

private theorem greater_terminal_exact (processed remainingCoordinate : Nat) :
    workRunExact? machine (2 * processed + remainingCoordinate + 3)
        (loopConfiguration processed (remainingCoordinate + 1) 0) =
      some (resultConfiguration
        (.greater processed remainingCoordinate)) := by
  let coordinateLeft :=
    (List.replicate processed coordinateMark).reverse ++ [leftBoundary]
  let boundaryTail := List.replicate processed boundaryMark ++ [endSymbol]
  let remainingTail :=
    List.replicate remainingCoordinate unitSymbol ++
      separatorSymbol :: boundaryTail
  let c0 := loopConfiguration processed (remainingCoordinate + 1) 0
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape coordinateLeft (unitSymbol :: remainingTail) }
  let c2 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape (coordinateMark :: coordinateLeft) remainingTail }
  let c3 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        ((List.replicate remainingCoordinate unitSymbol).reverse ++
          coordinateMark :: coordinateLeft)
        (separatorSymbol :: boundaryTail) }
  let c4 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (separatorSymbol ::
          (List.replicate remainingCoordinate unitSymbol).reverse ++
            coordinateMark :: coordinateLeft) boundaryTail }
  let c5 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        ((List.replicate processed boundaryMark).reverse ++
          separatorSymbol ::
            (List.replicate remainingCoordinate unitSymbol).reverse ++
              coordinateMark :: coordinateLeft) [endSymbol] }
  let c6 := resultConfiguration
    (.greater processed remainingCoordinate)
  have h01 : workRunExact? machine processed c0 = some c1 := by
    simpa [c0, c1, coordinateLeft, remainingTail, boundaryTail,
      loopConfiguration, comparisonTape, comparisonWord,
      List.replicate_succ, List.append_assoc] using
        coordinate_marks_exact processed [leftBoundary]
          (unitSymbol :: remainingTail)
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    simpa [c1, c2] using seekCoordinate_unit_step c1.tape (by rfl)
  have h23 : workRunExact? machine remainingCoordinate c2 = some c3 := by
    simpa [c2, c3, remainingTail] using
      separator_units_exact remainingCoordinate
        (coordinateMark :: coordinateLeft) (separatorSymbol :: boundaryTail)
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    simpa [c3, c4] using seekSeparator_separator_step c3.tape (by rfl)
  have h45 : workRunExact? machine processed c4 = some c5 := by
    simpa [c4, c5, boundaryTail] using
      boundary_marks_exact processed
        (separatorSymbol ::
          (List.replicate remainingCoordinate unitSymbol).reverse ++
            coordinateMark :: coordinateLeft) [endSymbol]
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    have hStep := seekBoundary_end_step c5.tape (by rfl)
    simpa [c5, c6, coordinateLeft, resultConfiguration, rightPathTape,
      machine, List.replicate_succ, List.append_assoc] using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    processed 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1) remainingCoordinate c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + remainingCoordinate) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + remainingCoordinate + 1) processed
    c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + remainingCoordinate + 1 + processed) 1
    c0 c5 c6 h05 h56
  have hCount :
      processed + 1 + remainingCoordinate + 1 + processed + 1 =
        2 * processed + remainingCoordinate + 3 := by
    omega
  rw [← hCount]
  simpa [c0, c6] using h06

private theorem cycle_exact (processed coordinate boundary : Nat) :
    workRunExact? machine (4 * processed + 2 * coordinate + 6)
        (loopConfiguration processed (coordinate + 1) (boundary + 1)) =
      some (loopConfiguration (processed + 1) coordinate boundary) := by
  let coordinateLeft :=
    (List.replicate processed coordinateMark).reverse ++ [leftBoundary]
  let boundaryTail :=
    List.replicate processed boundaryMark ++
      unitSymbol :: List.replicate boundary unitSymbol ++ [endSymbol]
  let remainingTail :=
    List.replicate coordinate unitSymbol ++
      separatorSymbol :: boundaryTail
  let rewindSymbols :=
    (List.replicate processed boundaryMark).reverse ++
      [separatorSymbol] ++
      (List.replicate coordinate unitSymbol).reverse ++
      [coordinateMark] ++
      (List.replicate processed coordinateMark).reverse
  let afterBoundary :=
    boundaryMark :: List.replicate boundary unitSymbol ++ [endSymbol]
  let c0 := loopConfiguration processed (coordinate + 1) (boundary + 1)
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape coordinateLeft (unitSymbol :: remainingTail) }
  let c2 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape (coordinateMark :: coordinateLeft) remainingTail }
  let c3 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        ((List.replicate coordinate unitSymbol).reverse ++
          coordinateMark :: coordinateLeft)
        (separatorSymbol :: boundaryTail) }
  let c4 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (separatorSymbol ::
          (List.replicate coordinate unitSymbol).reverse ++
            coordinateMark :: coordinateLeft) boundaryTail }
  let c5 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape (rewindSymbols ++ [leftBoundary])
        (unitSymbol :: List.replicate boundary unitSymbol ++ [endSymbol]) }
  let c6 : WorkConfiguration :=
    { state := 3
      tape := leftPathTape afterBoundary
        (rewindSymbols ++ [leftBoundary]) }
  let c7 : WorkConfiguration :=
    { state := 3
      tape := leftPathTape (rewindSymbols.reverse ++ afterBoundary)
        [leftBoundary] }
  let c8 := loopConfiguration (processed + 1) coordinate boundary
  have h01 : workRunExact? machine processed c0 = some c1 := by
    simpa [c0, c1, coordinateLeft, remainingTail, boundaryTail,
      loopConfiguration, comparisonTape, comparisonWord,
      List.replicate_succ, List.append_assoc] using
        coordinate_marks_exact processed [leftBoundary]
          (unitSymbol :: remainingTail)
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    simpa [c1, c2] using seekCoordinate_unit_step c1.tape (by rfl)
  have h23 : workRunExact? machine coordinate c2 = some c3 := by
    simpa [c2, c3, remainingTail] using
      separator_units_exact coordinate (coordinateMark :: coordinateLeft)
        (separatorSymbol :: boundaryTail)
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    simpa [c3, c4] using seekSeparator_separator_step c3.tape (by rfl)
  have h45 : workRunExact? machine processed c4 = some c5 := by
    simpa [c4, c5, rewindSymbols, boundaryTail, coordinateLeft,
      List.append_assoc] using
      boundary_marks_exact processed
        (separatorSymbol ::
          (List.replicate coordinate unitSymbol).reverse ++
            coordinateMark :: coordinateLeft)
        (unitSymbol :: List.replicate boundary unitSymbol ++ [endSymbol])
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    have hStep := seekBoundary_unit_step c5.tape (by rfl)
    simpa [c5, c6, afterBoundary] using hStep
  have hRewindSymbols : ∀ symbol ∈ rewindSymbols,
      symbol = boundaryMark ∨ symbol = separatorSymbol ∨
      symbol = unitSymbol ∨ symbol = coordinateMark := by
    intro symbol hMem
    dsimp [rewindSymbols] at hMem
    rcases List.mem_append.mp hMem with hPrefix | hMark
    · rcases List.mem_append.mp hPrefix with hPrefix | hCoordinate
      · rcases List.mem_append.mp hPrefix with hPrefix | hUnit
        · rcases List.mem_append.mp hPrefix with hBoundary | hSeparator
          · exact Or.inl
              (List.eq_of_mem_replicate (List.mem_reverse.mp hBoundary))
          · exact Or.inr (Or.inl (List.mem_singleton.mp hSeparator))
        · exact Or.inr (Or.inr (Or.inl
            (List.eq_of_mem_replicate (List.mem_reverse.mp hUnit))))
      · exact Or.inr (Or.inr (Or.inr
          (List.mem_singleton.mp hCoordinate)))
    · exact Or.inr (Or.inr (Or.inr
        (List.eq_of_mem_replicate (List.mem_reverse.mp hMark))))
  have h67 : workRunExact? machine rewindSymbols.length c6 = some c7 := by
    simpa [c6, c7] using
      rewind_exact rewindSymbols [leftBoundary] afterBoundary hRewindSymbols
  have hWord : rewindSymbols.reverse ++ afterBoundary =
      comparisonWord (processed + 1) coordinate boundary := by
    simp [rewindSymbols, afterBoundary, comparisonWord,
      List.reverse_append, List.replicate_succ, List.append_assoc,
      replicate_append_self_cons]
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    have hStep := rewind_leftBoundary_step c7.tape (by rfl)
    simpa [c7, c8, loopConfiguration, comparisonTape, hWord] using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    processed 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1) coordinate c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + coordinate) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + coordinate + 1) processed c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + coordinate + 1 + processed) 1
    c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + coordinate + 1 + processed + 1)
    rewindSymbols.length c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (processed + 1 + coordinate + 1 + processed + 1 +
      rewindSymbols.length) 1 c0 c7 c8 h07 h78
  have hRewindLength : rewindSymbols.length =
      2 * processed + coordinate + 2 := by
    simp [rewindSymbols]
    omega
  have hCount :
      processed + 1 + coordinate + 1 + processed + 1 +
          rewindSymbols.length + 1 =
        4 * processed + 2 * coordinate + 6 := by
    rw [hRewindLength]
    omega
  rw [← hCount]
  simpa [c0, c8] using h08

set_option maxRecDepth 100000 in
theorem loop_workRunExact (processed coordinate boundary : Nat) :
    workRunExact? machine (loopSteps processed coordinate boundary)
        (loopConfiguration processed coordinate boundary) =
      some (resultConfiguration
        (compareResult processed coordinate boundary)) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary with
      | zero => exact equal_terminal_exact processed
      | succ boundary => exact less_terminal_exact processed boundary
  | succ coordinate ih =>
      cases boundary with
      | zero => exact greater_terminal_exact processed coordinate
      | succ boundary =>
          have hCycle := cycle_exact processed coordinate boundary
          have hTail := ih (processed + 1) boundary
          have hAll := PipelineMachineSimulation.workRunExact?_compose machine
            (4 * processed + 2 * coordinate + 6)
            (loopSteps (processed + 1) coordinate boundary)
            (loopConfiguration processed (coordinate + 1) (boundary + 1))
            (loopConfiguration (processed + 1) coordinate boundary)
            (resultConfiguration
              (compareResult (processed + 1) coordinate boundary))
            hCycle hTail
          simpa [loopSteps, compareResult] using hAll

theorem compareResult_isLess_iff (processed coordinate boundary : Nat) :
    (compareResult processed coordinate boundary).isLess = true ↔
      coordinate < boundary := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;> simp [compareResult, ComparisonResult.isLess]
  | succ coordinate ih =>
      cases boundary with
      | zero => simp [compareResult, ComparisonResult.isLess]
      | succ boundary =>
          simpa [compareResult] using ih (processed + 1) boundary

theorem resultConfiguration_state (result : ComparisonResult) :
    (resultConfiguration result).state =
      if result.isLess then machine.acceptState else machine.rejectState := by
  cases result <;> rfl

def workSteps (coordinate boundary : Nat) : Nat :=
  loopSteps 0 coordinate boundary

def inputTape (coordinate boundary : Nat) : WorkTape :=
  comparisonTape 0 coordinate boundary

def finalConfiguration (coordinate boundary : Nat) : WorkConfiguration :=
  resultConfiguration (compareResult 0 coordinate boundary)

theorem workRunExact (coordinate boundary : Nat) :
    workRunExact? machine (workSteps coordinate boundary)
        (workStartConfiguration machine (inputTape coordinate boundary)) =
      some (finalConfiguration coordinate boundary) := by
  simpa [workSteps, inputTape, finalConfiguration, loopConfiguration,
    machine, workStartConfiguration] using
      loop_workRunExact 0 coordinate boundary

theorem finalConfiguration_accept_iff (coordinate boundary : Nat) :
    (finalConfiguration coordinate boundary).state = machine.acceptState ↔
      coordinate < boundary := by
  rw [finalConfiguration, resultConfiguration_state]
  by_cases hLess : coordinate < boundary
  · rw [if_pos ((compareResult_isLess_iff 0 coordinate boundary).2 hLess)]
    exact iff_of_true rfl hLess
  · rw [if_neg (by
      intro hResult
      exact hLess ((compareResult_isLess_iff 0 coordinate boundary).1 hResult))]
    constructor
    · intro hEqual
      exact False.elim (machine_acceptState_ne_rejectState hEqual.symm)
    · intro h
      exact False.elim (hLess h)

theorem finalConfiguration_reject_iff (coordinate boundary : Nat) :
    (finalConfiguration coordinate boundary).state = machine.rejectState ↔
      boundary ≤ coordinate := by
  rw [finalConfiguration, resultConfiguration_state]
  by_cases hLess : coordinate < boundary
  · rw [if_pos ((compareResult_isLess_iff 0 coordinate boundary).2 hLess)]
    constructor
    · intro hEqual
      exact False.elim (machine_acceptState_ne_rejectState hEqual)
    · intro hLe
      omega
  · rw [if_neg (by
      intro hResult
      exact hLess ((compareResult_isLess_iff 0 coordinate boundary).1 hResult))]
    exact iff_of_true rfl (by omega)

theorem finalConfiguration_isHalted (coordinate boundary : Nat) :
    machine.isHalted (finalConfiguration coordinate boundary) = true := by
  unfold finalConfiguration
  cases hResult : compareResult 0 coordinate boundary <;> rfl

theorem run_compile_exact (coordinate boundary : Nat) :
    run (compileWorkMachine machine) (6 * workSteps coordinate boundary)
        (encodeWorkConfiguration
          (workStartConfiguration machine (inputTape coordinate boundary))) =
      encodeWorkConfiguration (finalConfiguration coordinate boundary) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps coordinate boundary)
    (workStartConfiguration machine (inputTape coordinate boundary))
    (finalConfiguration coordinate boundary) (workRunExact coordinate boundary)

/-! ### Uniform encoded-size bound for in-range problem coordinates -/

theorem loopSteps_le (processed coordinate boundary : Nat) :
    loopSteps processed coordinate boundary ≤
      6 * (coordinate + 1) * (processed + coordinate + 1) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary <;> simp [loopSteps]
      <;> omega
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          simp only [loopSteps]
          have hLinear : 2 * processed + coordinate + 3 ≤
              6 * (processed + (coordinate + 1) + 1) := by
            omega
          have hCoefficient : 6 ≤ 6 * (coordinate + 1 + 1) := by
            have hPositive : 1 ≤ coordinate + 1 + 1 := by omega
            simpa using Nat.mul_le_mul_left 6 hPositive
          have hProduct := Nat.mul_le_mul_right
            (processed + (coordinate + 1) + 1) hCoefficient
          exact Nat.le_trans hLinear (by
            simpa only [Nat.mul_assoc] using hProduct)
      | succ boundary =>
          have hTail := ih (processed + 1) boundary
          have hCycle : 4 * processed + 2 * coordinate + 6 ≤
              6 * (processed + coordinate + 2) := by
            omega
          rw [loopSteps]
          calc
            4 * processed + 2 * coordinate + 6 +
                loopSteps (processed + 1) coordinate boundary ≤
              6 * (processed + coordinate + 2) +
                6 * (coordinate + 1) *
                  (processed + coordinate + 2) := by
                    have hTail' : loopSteps (processed + 1) coordinate boundary ≤
                        6 * (coordinate + 1) *
                          (processed + coordinate + 2) := by
                      simpa [Nat.add_assoc, Nat.add_comm,
                        Nat.add_left_comm] using hTail
                    exact Nat.add_le_add hCycle hTail'
            _ ≤ 6 * (coordinate + 1 + 1) *
                (processed + (coordinate + 1) + 1) := by
                  let total := processed + coordinate + 2
                  have hCoefficient :
                      6 + 6 * (coordinate + 1) =
                        6 * (coordinate + 2) := by
                    omega
                  have hCoordinateShape :
                      coordinate + 2 = coordinate + 1 + 1 := by
                    omega
                  have hTotalShape : total =
                      processed + (coordinate + 1) + 1 := by
                    dsimp [total]
                    omega
                  calc
                    6 * (processed + coordinate + 2) +
                        6 * (coordinate + 1) *
                          (processed + coordinate + 2) =
                      (6 + 6 * (coordinate + 1)) * total := by
                        simp [total, Nat.add_mul]
                    _ = (6 * (coordinate + 2)) * total := by
                      rw [hCoefficient]
                    _ ≤ 6 * (coordinate + 1 + 1) *
                        (processed + (coordinate + 1) + 1) := by
                      rw [hCoordinateShape, hTotalShape]
                      exact Nat.le_refl _

theorem workSteps_le (coordinate boundary : Nat) :
    workSteps coordinate boundary ≤
      6 * (coordinate + 1) * (coordinate + 1) := by
  simpa [workSteps] using loopSteps_le 0 coordinate boundary

/-- A source-size polynomial dominating the compiled comparison trace for
every coordinate inside the complete token schedule. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .mul (.constant 36)
    (.mul
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier)
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      36 *
        (BuilderFullScheduleCursorController.terminalSlot problem *
          BuilderFullScheduleCursorController.terminalSlot problem) := by
  rfl

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    6 * workSteps coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem) ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hWork := workSteps_le coordinate
    (BuilderFullScheduleCursorController.firstBodySlot problem)
  have hCoordinateSucc : coordinate + 1 ≤
      BuilderFullScheduleCursorController.terminalSlot problem := by
    omega
  have hSquare : (coordinate + 1) * (coordinate + 1) ≤
      BuilderFullScheduleCursorController.terminalSlot problem *
        BuilderFullScheduleCursorController.terminalSlot problem :=
    Nat.mul_le_mul hCoordinateSucc hCoordinateSucc
  rw [rawTimeBound_eval]
  have hScaled := Nat.mul_le_mul_left 6 hWork
  calc
    6 * workSteps coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem) ≤
      36 * ((coordinate + 1) * (coordinate + 1)) := by
        simpa only [← Nat.mul_assoc] using hScaled
    _ ≤ 36 *
        (BuilderFullScheduleCursorController.terminalSlot problem *
          BuilderFullScheduleCursorController.terminalSlot problem) := by
        exact Nat.mul_le_mul_left 36 hSquare

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    run (compileWorkMachine machine)
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (inputTape coordinate
              (BuilderFullScheduleCursorController.firstBodySlot problem)))) =
      encodeWorkConfiguration
        (finalConfiguration coordinate
          (BuilderFullScheduleCursorController.firstBodySlot problem)) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le machine
    (workSteps coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration machine
      (inputTape coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem)))
    (finalConfiguration coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem))
    (workRunExact coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem))
    (finalConfiguration_isHalted coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem))
    (rawTimeBound_le problem coordinate hCoordinate)

theorem workBoundedDecide_eq (coordinate boundary : Nat) :
    workBoundedDecide machine (workSteps coordinate boundary)
        (inputTape coordinate boundary) =
      if coordinate < boundary then .accept else .reject := by
  have hRun := workRun_eq_of_workRunExact machine
    (workSteps coordinate boundary)
    (workStartConfiguration machine (inputTape coordinate boundary))
    (finalConfiguration coordinate boundary)
    (workRunExact coordinate boundary)
  unfold workBoundedDecide
  rw [hRun]
  dsimp
  by_cases hLess : coordinate < boundary
  · rw [if_pos hLess]
    have hState :=
      (finalConfiguration_accept_iff coordinate boundary).2 hLess
    rw [hState]
    rfl
  · rw [if_neg hLess]
    have hState :=
      (finalConfiguration_reject_iff coordinate boundary).2 (by omega)
    rw [hState]
    rfl

private theorem verdict_timeout_of_not_halted
    (config : WorkConfiguration)
    (hHalted : machine.isHalted config = false) :
    (if config.state == machine.acceptState then WorkVerdict.accept
     else if config.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == machine.acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == machine.rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem workRunExact_succ_split_last :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? machine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? machine steps initial = some before ∧
        workStep? machine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine (steps + 1) next =
              some final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => workRunExact? machine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? machine initial with
             | none => none
             | some result => workRunExact? machine steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    machine.isHalted config = false := by
  cases hHalted : machine.isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive (coordinate boundary : Nat) :
    0 < workSteps coordinate boundary := by
  cases coordinate <;> cases boundary <;>
    simp [workSteps, loopSteps] <;> omega

/-- The exact comparator cannot halt one transition before its certified
endpoint. -/
theorem work_one_step_short_timeout (coordinate boundary : Nat) :
    workBoundedDecide machine (workSteps coordinate boundary - 1)
        (inputTape coordinate boundary) = .timeout := by
  let short := workSteps coordinate boundary - 1
  let initial := workStartConfiguration machine (inputTape coordinate boundary)
  let final := finalConfiguration coordinate boundary
  have hSucc : short + 1 = workSteps coordinate boundary := by
    dsimp [short]
    have hPositive := workSteps_positive coordinate boundary
    omega
  have hExact := workRunExact coordinate boundary
  change workRunExact? machine (workSteps coordinate boundary) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short initial = before :=
    workRun_eq_of_workRunExact machine short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun machine short initial
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted before hNotHalted

/-! ### Fail-closed malformed dispatch -/

def malformedConfiguration (left right : List WorkSymbol) :
    WorkConfiguration :=
  { state := 0
    tape := { left := left, head := endSymbol, right := right } }

private def deadConfiguration (tape : WorkTape) : WorkConfiguration :=
  { state := 5, tape := tape }

theorem malformed_enters_dead (left right : List WorkSymbol) :
    workStep? machine (malformedConfiguration left right) =
      some (deadConfiguration (malformedConfiguration left right).tape) := by
  have hStep := specMachine_step [] seekCoordinateSpec
    [seekSeparatorSpec, seekBoundarySpec, rewindSpec, checkBoundarySpec,
      deadSpec] (malformedConfiguration left right).tape
  have hWrite :
      (malformedConfiguration left right).tape.write endSymbol =
        (malformedConfiguration left right).tape := by
    rfl
  have hRaw :
      workStep? machine (malformedConfiguration left right) =
        some
          { state := 5
            tape :=
              (malformedConfiguration left right).tape.write endSymbol } := by
    simpa [machine_eq_specMachine, stateSpecs, malformedConfiguration,
      seekCoordinateSpec, coordinateMark, unitSymbol,
      separatorSymbol, endSymbol, BuilderUnaryPolynomial.registerMarkSymbol,
      BuilderUnaryPolynomial.unitSymbol,
      BuilderUnaryPolynomial.separatorSymbol,
      BuilderUnaryPolynomial.scratchEndSymbol, WorkSymbol.zeroZero,
      WorkSymbol.oneOne, WorkSymbol.zeroOne, WorkSymbol.blankOne,
      deadAction, BuilderUnaryPolynomial.deadAction,
      BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep
  rw [hWrite] at hRaw
  simpa [deadConfiguration] using hRaw

theorem deadState_workStep (tape : WorkTape) :
    workStep? machine { state := 5, tape := tape } =
      some { state := 5, tape := tape } := by
  have hStep := specMachine_step
    [seekCoordinateSpec, seekSeparatorSpec, seekBoundarySpec, rewindSpec,
      checkBoundarySpec] deadSpec [] tape
  have hWrite : tape.write tape.head = tape := by cases tape; rfl
  simpa [machine_eq_specMachine, stateSpecs, deadSpec, deadAction,
    BuilderUnaryPolynomial.deadAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move, hWrite] using hStep

private theorem dead_workRun (fuel : Nat) (tape : WorkTape) :
    workRun machine fuel (deadConfiguration tape) = deadConfiguration tape := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      unfold workRun
      rw [show workStep? machine (deadConfiguration tape) =
          some (deadConfiguration tape) by
        simpa [deadConfiguration] using deadState_workStep tape]
      exact ih

/-- An invalid top-level input symbol enters the explicit dead loop and never
produces a false accept or reject verdict. -/
theorem malformed_timeout (fuel : Nat) (left right : List WorkSymbol) :
    workBoundedDecide machine fuel
        (malformedConfiguration left right).tape = .timeout := by
  let bad := malformedConfiguration left right
  let dead := deadConfiguration bad.tape
  cases fuel with
  | zero =>
      change
        (if bad.state == machine.acceptState then WorkVerdict.accept
         else if bad.state == machine.rejectState then WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rfl
  | succ fuel =>
      have hRun : workRun machine (fuel + 1) bad = dead := by
        unfold workRun
        rw [show workStep? machine bad = some dead by
          simpa [bad, dead] using malformed_enters_dead left right]
        simpa [dead] using dead_workRun fuel bad.tape
      unfold workBoundedDecide
      change
        (let result := workRun machine (fuel + 1) bad
         if result.state == machine.acceptState then WorkVerdict.accept
         else if result.state == machine.rejectState then WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      rfl

end RawRouter

/-! ## Problem-specific routing endpoint -/

/-- The literal router compares any supplied natural coordinate with the exact
problem-derived header boundary.  Its result agrees with the semantic outer
route. -/
theorem rawRouter_accept_iff_header {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) :
    (RawRouter.finalConfiguration coordinate
      (BuilderFullScheduleCursorController.firstBodySlot problem)).state =
        RawRouter.machine.acceptState ↔
      ∃ headerCoordinate,
        outerRoute problem coordinate = .header headerCoordinate := by
  rw [RawRouter.finalConfiguration_accept_iff]
  constructor
  · intro hLess
    exact ⟨coordinate,
      (outerRoute_eq_header_iff problem coordinate coordinate).2
        ⟨hLess, rfl⟩⟩
  · rintro ⟨headerCoordinate, hRoute⟩
    exact
      (outerRoute_eq_header_iff problem coordinate headerCoordinate).1 hRoute |>.1

/-- M209 closes the first non-repeatable raw decoder boundary: one fixed
finite table routes every natural coordinate at the exact direct-schedule
header boundary, with an exact trace and compiled simulation.  It does not
decode the post-header quotient/remainder or emit any token. -/
theorem cook_levin_arbitrary_slot_header_router_checked_complete
    {language : Language} (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem)) :
    (problem.formulaTokenSlotDirect coordinate.val =
        match outerRoute problem coordinate.val with
        | .header headerCoordinate =>
            problem.formulaHeaderTokenSlotDirect headerCoordinate
        | .postHeader remainder => postHeaderSlotDirect problem remainder) ∧
    workRunExact? RawRouter.machine
        (RawRouter.workSteps coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem))
        (workStartConfiguration RawRouter.machine
          (RawRouter.inputTape coordinate.val
            (BuilderFullScheduleCursorController.firstBodySlot problem))) =
      some
        (RawRouter.finalConfiguration coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) ∧
    ((RawRouter.finalConfiguration coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)).state =
        RawRouter.machine.acceptState ↔
      ∃ headerCoordinate,
        outerRoute problem coordinate.val = .header headerCoordinate) ∧
    (workBoundedDecide RawRouter.machine
        (RawRouter.workSteps coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem))
        (RawRouter.inputTape coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) =
      if coordinate.val <
          BuilderFullScheduleCursorController.firstBodySlot problem then
        .accept
      else .reject) ∧
    run (compileWorkMachine RawRouter.machine)
        ((RawRouter.rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration RawRouter.machine
            (RawRouter.inputTape coordinate.val
              (BuilderFullScheduleCursorController.firstBodySlot problem)))) =
      encodeWorkConfiguration
        (RawRouter.finalConfiguration coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) ∧
    workBoundedDecide RawRouter.machine
        (RawRouter.workSteps coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem) - 1)
        (RawRouter.inputTape coordinate.val
          (BuilderFullScheduleCursorController.firstBodySlot problem)) =
      .timeout ∧
    RawRouter.rules.length = 54 := by
  exact ⟨formulaTokenSlotDirect_route problem coordinate.val,
    RawRouter.workRunExact coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem),
    rawRouter_accept_iff_header problem coordinate.val,
    RawRouter.workBoundedDecide_eq coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem),
    RawRouter.run_compile_rawTimeBound problem coordinate.val coordinate.isLt,
    RawRouter.work_one_step_short_timeout coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem),
    RawRouter.rules_length⟩

end BuilderArbitrarySlotHeaderRouter

end CookLevin

end PNP.Concrete
