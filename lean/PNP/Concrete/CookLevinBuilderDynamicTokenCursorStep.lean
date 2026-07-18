/-
Copyright (c) 2026 PNP Labs.

One literal token-cursor transition after the first canonical Cook--Levin
clause.

The machine in this file consumes the unary token coordinate retained by the
first-clause prefix, advances it by one cell, and restores the represented
input focus.  At this exact coordinate the direct rectangular schedule proves
that the decoded opportunity is padding, so the existing formula output is
left unchanged.  This is one cursor transition, not a complete cursor loop or
a complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderFirstClausePrefix

namespace PNP.Concrete

namespace CookLevin

namespace BuilderDynamicTokenCursorStep

open PipelineTape PipelineStateNamespace PipelineStageBridges

namespace Unary

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

private def keepAction := BuilderUnaryPolynomial.keepAction
private def writeAction := BuilderUnaryPolynomial.writeAction
private def deadAction := BuilderUnaryPolynomial.deadAction

end Unary

/-! ### Literal padding-step table -/

namespace CursorAdvance

private def startSpec : Unary.StateSpec := fun read =>
  if read = WorkSymbol.blank ∨ read = WorkSymbol.zeroBlank ∨
      read = WorkSymbol.oneBlank then
    Unary.keepAction 1 .left read
  else
    Unary.deadAction 4 read

private def seekEndSpec : Unary.StateSpec := fun read =>
  if read = leftMarker ∨ read = BuilderUnaryPolynomial.unitSymbol ∨
      read = BuilderUnaryPolynomial.separatorSymbol then
    Unary.keepAction 1 .left read
  else if read = BuilderUnaryPolynomial.scratchEndSymbol then
    Unary.writeAction 2 BuilderUnaryPolynomial.unitSymbol .left
  else
    Unary.deadAction 4 read

private def installEndSpec : Unary.StateSpec := fun _read =>
  Unary.writeAction 3 BuilderUnaryPolynomial.scratchEndSymbol .stay

private def rewindSpec : Unary.StateSpec := fun read =>
  if read = BuilderUnaryPolynomial.scratchEndSymbol ∨
      read = BuilderUnaryPolynomial.unitSymbol ∨
      read = BuilderUnaryPolynomial.separatorSymbol then
    Unary.keepAction 3 .right read
  else if read = leftMarker then
    Unary.keepAction 5 .right read
  else
    Unary.deadAction 4 read

private def deadSpec : Unary.StateSpec := fun read => Unary.deadAction 4 read

private def stateSpecs : List Unary.StateSpec :=
  [startSpec, seekEndSpec, installEndSpec, rewindSpec, deadSpec]

def rules : List WorkRule :=
  BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

/-- The accept state denotes a successfully consumed padding opportunity.
The reject state is intentionally unreachable on every well-formed endpoint. -/
def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 5
    rejectState := 6 }

theorem rules_length : rules.length = 45 := by
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
    (specs : List Unary.StateSpec) (rule : WorkRule)
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

private def specMachine (specs : List Unary.StateSpec) : WorkMachine :=
  { rules := BuilderUnaryPolynomial.rulesFrom 0 specs
    startState := 0
    acceptState := specs.length
    rejectState := specs.length + 1 }

private theorem specMachine_step
    (before : List Unary.StateSpec) (spec : Unary.StateSpec)
    (after : List Unary.StateSpec) (tape : WorkTape) :
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

private theorem start_step (tape : WorkTape)
    (hHead : tape.head = WorkSymbol.blank ∨
      tape.head = WorkSymbol.zeroBlank ∨
      tape.head = WorkSymbol.oneBlank) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 1, tape := tape.moveLeft } := by
  have hStep := specMachine_step [] startSpec
    [seekEndSpec, installEndSpec, rewindSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, startSpec, hHead, Unary.keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem seek_step (tape : WorkTape)
    (hHead : tape.head = leftMarker ∨
      tape.head = BuilderUnaryPolynomial.unitSymbol ∨
      tape.head = BuilderUnaryPolynomial.separatorSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 1, tape := tape.moveLeft } := by
  have hStep := specMachine_step [startSpec] seekEndSpec
    [installEndSpec, rewindSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, seekEndSpec, hHead, Unary.keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem append_step (tape : WorkTape)
    (hHead : tape.head = BuilderUnaryPolynomial.scratchEndSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some
        { state := 2
          tape := (tape.write BuilderUnaryPolynomial.unitSymbol).moveLeft } := by
  have hStep := specMachine_step [startSpec] seekEndSpec
    [installEndSpec, rewindSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, seekEndSpec, hHead,
    BuilderUnaryPolynomial.scratchEndSymbol,
    BuilderUnaryPolynomial.unitSymbol,
    BuilderUnaryPolynomial.separatorSymbol, leftMarker,
    WorkSymbol.blankOne, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    WorkSymbol.blankZero, Unary.writeAction,
    BuilderUnaryPolynomial.writeAction, WorkTape.move] using hStep

private theorem install_step (tape : WorkTape) :
    workStep? machine { state := 2, tape := tape } =
      some
        { state := 3
          tape := tape.write BuilderUnaryPolynomial.scratchEndSymbol } := by
  have hStep := specMachine_step [startSpec, seekEndSpec] installEndSpec
    [rewindSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, installEndSpec, Unary.writeAction,
    BuilderUnaryPolynomial.writeAction, WorkTape.move] using hStep

private theorem rewind_step (tape : WorkTape)
    (hHead : tape.head = BuilderUnaryPolynomial.scratchEndSymbol ∨
      tape.head = BuilderUnaryPolynomial.unitSymbol ∨
      tape.head = BuilderUnaryPolynomial.separatorSymbol) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 3, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [startSpec, seekEndSpec, installEndSpec] rewindSpec [deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, rewindSpec, hHead, Unary.keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem finish_step (tape : WorkTape)
    (hHead : tape.head = leftMarker) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 5, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [startSpec, seekEndSpec, installEndSpec] rewindSpec [deadSpec] tape
  have hWrite : tape.write leftMarker = tape := by
    cases tape
    cases hHead
    rfl
  have hEnd : leftMarker ≠ BuilderUnaryPolynomial.scratchEndSymbol := by decide
  have hUnit : leftMarker ≠ BuilderUnaryPolynomial.unitSymbol := by decide
  have hSeparator :
      leftMarker ≠ BuilderUnaryPolynomial.separatorSymbol := by decide
  simpa [machine_eq_specMachine, stateSpecs, rewindSpec, hHead,
    hEnd, hUnit, hSeparator, Unary.keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

/-! ### Exact generic cursor advancement -/

private def leftPathTape (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: left => { left := left, head := head, right := rightSide }

private def rightPathTape (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

@[simp] private theorem leftPathTape_moveLeft_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).moveLeft =
      leftPathTape (head :: rightSide) left := by
  cases left <;> rfl

@[simp] private theorem rightPathTape_moveRight_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    (rightPathTape leftSide (head :: right)).moveRight =
      rightPathTape (head :: leftSide) right := by
  cases right <;> rfl

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem seek_scan_exact (symbols : List WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ symbols,
      symbol = leftMarker ∨
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    workRunExact? machine symbols.length
        { state := 1
          tape := leftPathTape rightSide (symbols ++ leftTail) } =
      some
        { state := 1
          tape := leftPathTape (symbols.reverse ++ rightSide) leftTail } := by
  induction symbols generalizing rightSide with
  | nil => rfl
  | cons first rest ih =>
      have hFirst := hSymbols first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest,
          symbol = leftMarker ∨
          symbol = BuilderUnaryPolynomial.unitSymbol ∨
          symbol = BuilderUnaryPolynomial.separatorSymbol := by
        intro symbol hMem
        exact hSymbols symbol (List.Mem.tail first hMem)
      have hOne := workRunExact_one
        { state := 1
          tape := leftPathTape rightSide
            (first :: rest ++ leftTail) }
        { state := 1
          tape := leftPathTape (first :: rightSide)
            (rest ++ leftTail) } (by
          simpa using seek_step
            (leftPathTape rightSide (first :: rest ++ leftTail)) hFirst)
      have hTail := ih (first :: rightSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 rest.length
        { state := 1
          tape := leftPathTape rightSide
            (first :: rest ++ leftTail) }
        { state := 1
          tape := leftPathTape (first :: rightSide)
            (rest ++ leftTail) }
        { state := 1
          tape := leftPathTape
            (rest.reverse ++ first :: rightSide) leftTail }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

private theorem rewind_scan_exact (symbols : List WorkSymbol)
    (leftSide rightTail : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ symbols,
      symbol = BuilderUnaryPolynomial.scratchEndSymbol ∨
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    workRunExact? machine symbols.length
        { state := 3
          tape := rightPathTape leftSide (symbols ++ rightTail) } =
      some
        { state := 3
          tape := rightPathTape (symbols.reverse ++ leftSide) rightTail } := by
  induction symbols generalizing leftSide with
  | nil => rfl
  | cons first rest ih =>
      have hFirst := hSymbols first (List.Mem.head rest)
      have hRest : ∀ symbol ∈ rest,
          symbol = BuilderUnaryPolynomial.scratchEndSymbol ∨
          symbol = BuilderUnaryPolynomial.unitSymbol ∨
          symbol = BuilderUnaryPolynomial.separatorSymbol := by
        intro symbol hMem
        exact hSymbols symbol (List.Mem.tail first hMem)
      have hOne := workRunExact_one
        { state := 3
          tape := rightPathTape leftSide
            (first :: rest ++ rightTail) }
        { state := 3
          tape := rightPathTape (first :: leftSide)
            (rest ++ rightTail) } (by
          simpa using rewind_step
            (rightPathTape leftSide (first :: rest ++ rightTail)) hFirst)
      have hTail := ih (first :: leftSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 rest.length
        { state := 3
          tape := rightPathTape leftSide
            (first :: rest ++ rightTail) }
        { state := 3
          tape := rightPathTape (first :: leftSide)
            (rest ++ rightTail) }
        { state := 3
          tape := rightPathTape
            (rest.reverse ++ first :: leftSide) rightTail }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm] using hAll

/-- Exact cost for advancing one unary coordinate stored immediately before
the active scratch-end marker. -/
def advanceWorkSteps (word : List WorkSymbol) : Nat :=
  2 * word.length + 7

private theorem workspace_head_allowed (input : BitString)
    (outside : List WorkSymbol) (output : List CNFToken) :
    let tape := BuilderTokenAppender.workspaceTape input outside output
    tape.head = WorkSymbol.blank ∨ tape.head = WorkSymbol.zeroBlank ∨
      tape.head = WorkSymbol.oneBlank := by
  cases input with
  | nil => simp [BuilderTokenAppender.workspaceTape, frameWithGarbage,
      Tape.ofInput, Tape.blank, dataSymbol, WorkSymbol.blank]
  | cons first rest =>
      cases first <;>
        simp [BuilderTokenAppender.workspaceTape, frameWithGarbage,
          Tape.ofInput, dataSymbol, TapeSymbol.ofBool,
          WorkSymbol.zeroBlank, WorkSymbol.oneBlank]

private theorem advance_tape_workRunExact
    (sourceHead : WorkSymbol) (sourceRight word outsideTail : List WorkSymbol)
    (hHead : sourceHead = WorkSymbol.blank ∨
      sourceHead = WorkSymbol.zeroBlank ∨
      sourceHead = WorkSymbol.oneBlank)
    (hWord : ∀ symbol ∈ word,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    workRunExact? machine (advanceWorkSteps word)
        { state := machine.startState
          tape :=
            { left := leftMarker ::
                (word ++ BuilderUnaryPolynomial.scratchEndSymbol ::
                  outsideTail)
              head := sourceHead
              right := sourceRight } } =
      some
        { state := machine.acceptState
          tape :=
            { left := leftMarker ::
                (word ++ BuilderUnaryPolynomial.unitSymbol ::
                  BuilderUnaryPolynomial.scratchEndSymbol ::
                    outsideTail.drop 1)
              head := sourceHead
              right := sourceRight } } := by
  let marker := BuilderUnaryPolynomial.scratchEndSymbol
  let unit := BuilderUnaryPolynomial.unitSymbol
  let leftScan := leftMarker :: word
  let rightScan := marker :: unit :: word.reverse
  let c0 : WorkConfiguration :=
    { state := machine.startState
      tape :=
        { left := leftMarker :: (word ++ marker :: outsideTail)
          head := sourceHead
          right := sourceRight } }
  let c1 : WorkConfiguration :=
    { state := 1
      tape := leftPathTape (sourceHead :: sourceRight)
        (leftMarker :: word ++ marker :: outsideTail) }
  let c2 : WorkConfiguration :=
    { state := 1
      tape := leftPathTape
        (leftScan.reverse ++ sourceHead :: sourceRight)
        (marker :: outsideTail) }
  let c3 : WorkConfiguration :=
    { state := 2
      tape := leftPathTape
        (unit :: leftScan.reverse ++ sourceHead :: sourceRight)
        outsideTail }
  let c4 : WorkConfiguration :=
    { state := 3
      tape := rightPathTape (outsideTail.drop 1)
        (marker :: unit :: leftScan.reverse ++ sourceHead :: sourceRight) }
  let c5 : WorkConfiguration :=
    { state := 3
      tape := rightPathTape
        (rightScan.reverse ++ outsideTail.drop 1)
        (leftMarker :: sourceHead :: sourceRight) }
  let c6 : WorkConfiguration :=
    { state := machine.acceptState
      tape :=
        { left := leftMarker ::
            (word ++ unit :: marker :: outsideTail.drop 1)
          head := sourceHead
          right := sourceRight } }
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    have hStep := start_step c0.tape (by
      simpa [c0] using hHead)
    simpa [c0, c1, machine, leftPathTape, WorkTape.moveLeft] using hStep
  have hLeftSymbols : ∀ symbol ∈ leftScan,
      symbol = leftMarker ∨
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol := by
    intro symbol hMem
    simp only [leftScan, List.mem_cons] at hMem
    rcases hMem with hMarker | hScratch
    · exact Or.inl hMarker
    · rcases hWord symbol hScratch with hUnit | hSeparator
      · exact Or.inr (Or.inl hUnit)
      · exact Or.inr (Or.inr hSeparator)
  have h12 : workRunExact? machine leftScan.length c1 = some c2 := by
    simpa [c1, c2, leftScan, List.append_assoc] using
      seek_scan_exact leftScan
      (marker :: outsideTail) (sourceHead :: sourceRight) hLeftSymbols
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    have hStep := append_step c2.tape (by simp [c2, leftPathTape, marker])
    cases outsideTail <;>
      simpa [c2, c3, leftPathTape, marker, unit,
        WorkTape.write, WorkTape.moveLeft] using hStep
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    have hStep := install_step c3.tape
    cases outsideTail <;>
      simpa [c3, c4, leftPathTape, rightPathTape, marker, unit,
        WorkTape.write, WorkTape.move] using hStep
  have hRightSymbols : ∀ symbol ∈ rightScan,
      symbol = BuilderUnaryPolynomial.scratchEndSymbol ∨
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol := by
    intro symbol hMem
    simp only [rightScan, List.mem_cons, List.mem_reverse] at hMem
    rcases hMem with hMarker | hUnit | hScratch
    · exact Or.inl hMarker
    · exact Or.inr (Or.inl hUnit)
    · rcases hWord symbol hScratch with hWordUnit | hSeparator
      · exact Or.inr (Or.inl hWordUnit)
      · exact Or.inr (Or.inr hSeparator)
  have h45 : workRunExact? machine rightScan.length c4 = some c5 := by
    simpa [c4, c5, rightScan, leftScan, List.append_assoc] using
      rewind_scan_exact rightScan (outsideTail.drop 1)
      (leftMarker :: sourceHead :: sourceRight) hRightSymbols
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    have hStep := finish_step c5.tape (by
      simp [c5, rightPathTape])
    simpa [c5, c6, machine, rightPathTape, rightScan, leftScan, marker, unit,
      List.reverse_cons, List.append_assoc, WorkTape.moveRight] using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 leftScan.length c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + leftScan.length) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + leftScan.length + 1) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + leftScan.length + 1 + 1) rightScan.length c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + leftScan.length + 1 + 1 + rightScan.length) 1
    c0 c5 c6 h05 h56
  have hCount :
      1 + leftScan.length + 1 + 1 + rightScan.length + 1 =
        advanceWorkSteps word := by
    simp [leftScan, rightScan, advanceWorkSteps]
    omega
  rw [← hCount]
  simpa [c0, c6, marker, unit, machine] using h06

/-- The five-state literal table advances any well-formed unary scratch word,
consumes one exterior garbage cell for the relocated end marker, and restores
the represented input and output workspace exactly. -/
theorem advance_workRunExact (input : BitString)
    (word outsideTail : List WorkSymbol) (output : List CNFToken)
    (hWord : ∀ symbol ∈ word,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol) :
    workRunExact? machine (advanceWorkSteps word)
        (workStartConfiguration machine
          (BuilderTokenAppender.workspaceTape input
            (word ++ BuilderUnaryPolynomial.scratchEndSymbol :: outsideTail)
            output)) =
      some
        { state := machine.acceptState
          tape := BuilderTokenAppender.workspaceTape input
            (word ++ BuilderUnaryPolynomial.unitSymbol ::
              BuilderUnaryPolynomial.scratchEndSymbol :: outsideTail.drop 1)
            output } := by
  have hExact := advance_tape_workRunExact
    (BuilderTokenAppender.workspaceTape input
      (word ++ BuilderUnaryPolynomial.scratchEndSymbol :: outsideTail)
      output).head
    (BuilderTokenAppender.workspaceTape input
      (word ++ BuilderUnaryPolynomial.scratchEndSymbol :: outsideTail)
      output).right word outsideTail
    (workspace_head_allowed input
      (word ++ BuilderUnaryPolynomial.scratchEndSymbol :: outsideTail)
      output) hWord
  cases input with
  | nil =>
      simpa [BuilderTokenAppender.workspaceTape, frameWithGarbage,
        Tape.ofInput, Tape.blank, dataSymbol, WorkSymbol.blank,
        workStartConfiguration] using hExact
  | cons first rest =>
      simpa [BuilderTokenAppender.workspaceTape, frameWithGarbage,
        Tape.ofInput, dataSymbol, workStartConfiguration] using hExact

/-- A phase-local malformed cursor configuration used to audit fail-closed
dispatch.  `zeroZero` is neither a durable unit, separator, boundary, nor the
active scratch-end marker. -/
def malformedScratchConfiguration (left right : List WorkSymbol) :
    WorkConfiguration :=
  { state := 1
    tape := { left := left, head := WorkSymbol.zeroZero, right := right } }

private def deadConfiguration (tape : WorkTape) : WorkConfiguration :=
  { state := 4, tape := tape }

private theorem malformedScratch_workStep (left right : List WorkSymbol) :
    workStep? machine (malformedScratchConfiguration left right) =
      some (deadConfiguration
        (malformedScratchConfiguration left right).tape) := by
  have hStep := specMachine_step [startSpec] seekEndSpec
    [installEndSpec, rewindSpec, deadSpec]
    (malformedScratchConfiguration left right).tape
  simpa [machine_eq_specMachine, stateSpecs, malformedScratchConfiguration,
    deadConfiguration, seekEndSpec, leftMarker,
    BuilderUnaryPolynomial.unitSymbol,
    BuilderUnaryPolynomial.separatorSymbol,
    BuilderUnaryPolynomial.scratchEndSymbol, WorkSymbol.zeroZero,
    WorkSymbol.blankZero, WorkSymbol.oneOne, WorkSymbol.zeroOne,
    WorkSymbol.blankOne, Unary.deadAction,
    BuilderUnaryPolynomial.deadAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.write, WorkTape.move] using hStep

private theorem dead_workStep (tape : WorkTape) :
    workStep? machine (deadConfiguration tape) =
      some (deadConfiguration tape) := by
  have hStep := specMachine_step
    [startSpec, seekEndSpec, installEndSpec, rewindSpec] deadSpec [] tape
  have hWrite : tape.write tape.head = tape := by
    cases tape
    rfl
  simpa [machine_eq_specMachine, stateSpecs, deadConfiguration, deadSpec,
    Unary.deadAction, BuilderUnaryPolynomial.deadAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move, hWrite] using hStep

/-- Public phase-local dispatch fact used by later literal compositions:
an invalid seek symbol enters the explicit dead state without halting. -/
theorem malformedScratch_enters_dead (left right : List WorkSymbol) :
    workStep? machine (malformedScratchConfiguration left right) =
      some
        { state := 4
          tape := (malformedScratchConfiguration left right).tape } := by
  simpa [deadConfiguration] using malformedScratch_workStep left right

/-- Public phase-local dispatch fact used by later literal compositions:
the explicit cursor dead state is a nonhalting self-loop. -/
theorem deadState_workStep (tape : WorkTape) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 4, tape := tape } := by
  simpa [deadConfiguration] using dead_workStep tape

private theorem dead_workRun (fuel : Nat) (tape : WorkTape) :
    workRun machine fuel (deadConfiguration tape) = deadConfiguration tape := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      unfold workRun
      rw [dead_workStep]
      exact ih

end CursorAdvance

/-! ### First-clause endpoint and direct cursor semantics -/

def cursorWord {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  BuilderUnaryPolynomial.scratchWord
    (BuilderFirstClausePrefix.nextTokenSlotPolynomial problem.verifier)
    problem.input.length

private def cursorOutsideTail {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  (BuilderFirstLiteralPrefix.finalOutside problem).drop
    (cursorWord problem).length |>.drop 1

def finalOutside {language : Language}
    (problem : VerifierTableauProblem language) : List WorkSymbol :=
  cursorWord problem ++ BuilderUnaryPolynomial.unitSymbol ::
    BuilderUnaryPolynomial.scratchEndSymbol ::
      (cursorOutsideTail problem).drop 1

def finalTape {language : Language}
    (problem : VerifierTableauProblem language) : WorkTape :=
  BuilderTokenAppender.workspaceTape problem.input (finalOutside problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem)

def cursorFinalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := CursorAdvance.machine.acceptState, tape := finalTape problem }

def cursorWorkSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  CursorAdvance.advanceWorkSteps (cursorWord problem)

private theorem firstClause_finalOutside_eq_cursor {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.finalOutside problem =
      cursorWord problem ++
        BuilderUnaryPolynomial.scratchEndSymbol :: cursorOutsideTail problem := by
  unfold BuilderFirstClausePrefix.finalOutside
    BuilderUnaryPolynomial.finalOutsideLeft
    BuilderUnaryPolynomial.overlayScratch cursorWord cursorOutsideTail
  rw [List.drop_drop]
  rfl

theorem cursor_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? CursorAdvance.machine (cursorWorkSteps problem)
        (workStartConfiguration CursorAdvance.machine
          (BuilderFirstClausePrefix.finalTape problem)) =
      some (cursorFinalConfiguration problem) := by
  have hWord : ∀ symbol ∈ cursorWord problem,
      symbol = BuilderUnaryPolynomial.unitSymbol ∨
      symbol = BuilderUnaryPolynomial.separatorSymbol := by
    intro symbol hMem
    exact BuilderUnaryPolynomial.scratchWord_symbol
      (BuilderFirstClausePrefix.nextTokenSlotPolynomial problem.verifier)
      problem.input.length symbol (by simpa [cursorWord] using hMem)
  have hExact := CursorAdvance.advance_workRunExact problem.input
    (cursorWord problem) (cursorOutsideTail problem)
    (BuilderFirstClausePrefix.firstClauseTokens problem) hWord
  rw [BuilderFirstClausePrefix.finalTape,
    firstClause_finalOutside_eq_cursor]
  simpa [cursorWorkSteps, cursorFinalConfiguration, finalTape, finalOutside,
    BuilderFirstClausePrefix.finalTape] using hExact

theorem directOutcome_is_padding {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaTokenSlotDirect
        (BuilderFirstClausePrefix.nextTokenSlot problem) = some none :=
  BuilderFirstClausePrefix.nextTokenSlot_direct_eq_padding problem

theorem specification_step {language : Language}
    (problem : VerifierTableauProblem language) :
    VerifierTableauProblem.FormulaTokenCursor.step problem
        ⟨BuilderFirstClausePrefix.nextTokenSlot problem⟩ =
      some (none,
        ⟨BuilderFirstClausePrefix.nextTokenSlot problem + 1⟩) := by
  unfold VerifierTableauProblem.FormulaTokenCursor.step
  rw [directOutcome_is_padding]

/-! ### Composition with the complete first-clause prefix -/

private theorem prefix_noRuleAtAccept {language : Language}
    (problem : VerifierTableauProblem language) :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept
      (BuilderFirstClausePrefix.machine problem) := by
  exact BuilderFirstClausePrefix.rule_source_ne_acceptState problem

private theorem cursor_noRuleAtAccept :
    BuilderFirstClausePrefix.WorkChain.NoRuleAtAccept CursorAdvance.machine := by
  exact CursorAdvance.rule_source_ne_acceptState

/-- One bridge-first literal machine from raw input through one successful
padding cursor transition.  Only the cursor component contributes global
halts. -/
def machine {language : Language}
    (problem : VerifierTableauProblem language) : WorkMachine :=
  BuilderFirstClausePrefix.WorkChain.machine
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine

def finalConfiguration {language : Language}
    (problem : VerifierTableauProblem language) : WorkConfiguration :=
  { state := (machine problem).acceptState
    tape := finalTape problem }

def workSteps {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstClausePrefix.workSteps problem + 1 + cursorWorkSteps problem

theorem rules_length {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.length =
      1192 +
        BuilderUnaryPolynomial.ruleCount
          (BuilderCompleteHeader.widthPolynomial problem) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderBodyStartPrefix.nextTokenSlotPolynomial problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstLiteralPrefix.nextTokenSlotPolynomial
            problem.verifier) +
        BuilderUnaryPolynomial.ruleCount
          (BuilderFirstClausePrefix.nextTokenSlotPolynomial
            problem.verifier) := by
  have hPrefix := BuilderFirstClausePrefix.rules_length problem
  have hCursor := CursorAdvance.rules_length
  have hCursorMachine : CursorAdvance.machine.rules.length = 45 := by
    simpa [CursorAdvance.machine] using hCursor
  have hLaunch : ∀ source target,
      (launchRules source target).length = 9 := by
    intro source target
    rfl
  unfold machine BuilderFirstClausePrefix.WorkChain.machine
    BuilderFirstClausePrefix.WorkChain.rules
    BuilderFirstClausePrefix.WorkChain.bridgeRules
  simp only [List.length_append, List.length_map]
  rw [hPrefix, hCursorMachine, hLaunch]
  omega

theorem rules_pairwise_query_distinct {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderFirstClausePrefix.WorkChain.rules_pairwise_query_distinct
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    (BuilderFirstClausePrefix.rules_pairwise_query_distinct problem)
    CursorAdvance.rules_pairwise_query_distinct
    (prefix_noRuleAtAccept problem)

theorem machine_acceptState_ne_rejectState {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).acceptState ≠ (machine problem).rejectState := by
  exact BuilderFirstClausePrefix.WorkChain.machine_acceptState_ne_rejectState
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    CursorAdvance.machine_acceptState_ne_rejectState

theorem rule_source_ne_acceptState {language : Language}
    (problem : VerifierTableauProblem language) (rule : WorkRule)
    (hRule : rule ∈ (machine problem).rules) :
    rule.sourceState ≠ (machine problem).acceptState := by
  exact BuilderFirstClausePrefix.WorkChain.noRuleAtAccept
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    cursor_noRuleAtAccept rule hRule

theorem finalTape_represents {language : Language}
    (problem : VerifierTableauProblem language) :
    Represents (Tape.ofInput problem.input) (finalTape problem) := by
  exact BuilderTokenAppender.workspaceTape_represents problem.input
    (finalOutside problem) (BuilderFirstClausePrefix.firstClauseTokens problem)

theorem prefix_workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem)
        (BuilderFirstClausePrefix.workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.firstState
        (BuilderFirstClausePrefix.finalConfiguration problem)) := by
  have hTransport := PipelineStageBridges.workRunExact?_transport
    (BuilderFirstClausePrefix.machine problem) (machine problem)
    BuilderFirstClausePrefix.WorkChain.firstState
    (BuilderFirstClausePrefix.WorkChain.first_workStep_of_some
      (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine)
    (BuilderFirstClausePrefix.workSteps problem)
    (workStartConfiguration (BuilderFirstClausePrefix.machine problem)
      (rawInputWorkTape problem.input))
    (BuilderFirstClausePrefix.finalConfiguration problem)
    (BuilderFirstClausePrefix.workRunExact problem)
  simpa [machine, BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hTransport

/-- The bridge preserves the complete first-clause workspace and launches the
literal padding-step table. -/
theorem launch_workStep {language : Language}
    (problem : VerifierTableauProblem language) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          (BuilderFirstClausePrefix.finalConfiguration problem)) =
      some (renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (workStartConfiguration CursorAdvance.machine
          (BuilderFirstClausePrefix.finalTape problem))) := by
  have hLaunch := BuilderFirstClausePrefix.WorkChain.launch_workStep
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    (BuilderFirstClausePrefix.finalTape problem)
  simpa [machine, BuilderFirstClausePrefix.finalConfiguration,
    workStartConfiguration] using hLaunch

set_option maxRecDepth 1000000 in
/-- Every raw input follows one exact trace through the first canonical clause
and then through the first dynamic token-coordinate advancement. -/
theorem workRunExact {language : Language}
    (problem : VerifierTableauProblem language) :
    workRunExact? (machine problem) (workSteps problem)
        (workStartConfiguration (machine problem)
          (rawInputWorkTape problem.input)) =
      some (finalConfiguration problem) := by
  let prefixInitial := workStartConfiguration
    (BuilderFirstClausePrefix.machine problem)
    (rawInputWorkTape problem.input)
  let prefixFinal := BuilderFirstClausePrefix.finalConfiguration problem
  let cursorFinal := cursorFinalConfiguration problem
  have hPrefix : workRunExact? (BuilderFirstClausePrefix.machine problem)
      (BuilderFirstClausePrefix.workSteps problem) prefixInitial =
        some prefixFinal := by
    simpa [prefixInitial, prefixFinal] using
      BuilderFirstClausePrefix.workRunExact problem
  have hCursor : workRunExact? CursorAdvance.machine
      (cursorWorkSteps problem)
      { state := CursorAdvance.machine.startState,
        tape := prefixFinal.tape } = some cursorFinal := by
    simpa [prefixFinal, cursorFinal,
      BuilderFirstClausePrefix.finalConfiguration,
      workStartConfiguration] using cursor_workRunExact problem
  have hCombined := BuilderFirstClausePrefix.WorkChain.workRunExact
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    (BuilderFirstClausePrefix.workSteps problem) (cursorWorkSteps problem)
    prefixInitial prefixFinal cursorFinal hPrefix rfl hCursor
  simpa [machine, workSteps, prefixInitial, cursorFinal,
    cursorFinalConfiguration, finalConfiguration,
    BuilderFirstClausePrefix.WorkChain.machine,
    workStartConfiguration, renameConfiguration] using hCombined

/-- Padding emits no token, so the exact canonical formula prefix remains the
complete first clause proved by the predecessor milestone. -/
theorem finalTokenBits_eq_encodedFormula_firstClause
    {language : Language} (problem : VerifierTableauProblem language) :
    encodeTokenPairs (BuilderFirstClausePrefix.firstClauseTokens problem) =
      problem.encodedFormula.take (2 * (problem.FormulaWidth + 12)) :=
  BuilderFirstClausePrefix.finalTokenBits_eq_encodedFormula_firstClause problem

/-- The next cursor coordinate after the successful padding transition. -/
def finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) : Nat :=
  BuilderFirstClausePrefix.nextTokenSlot problem + 1

theorem finalTokenSlot_eq_formulaVariableSlotBound_add_thirteen
    {language : Language} (problem : VerifierTableauProblem language) :
    finalTokenSlot problem = problem.formulaVariableSlotBound + 13 := by
  rw [finalTokenSlot,
    BuilderFirstClausePrefix.nextTokenSlot_eq_formulaVariableSlotBound_add_twelve]

/-- The endpoint exterior contains the advanced cursor as the final unary
root register immediately before the unique active scratch marker. -/
theorem finalOutside_contains_finalTokenSlot {language : Language}
    (problem : VerifierTableauProblem language) :
    ∃ wordPrefix tail,
      finalOutside problem =
        wordPrefix ++ BuilderUnaryPolynomial.separatorSymbol ::
          List.replicate (finalTokenSlot problem)
            BuilderUnaryPolynomial.unitSymbol ++
          BuilderUnaryPolynomial.scratchEndSymbol :: tail := by
  rcases BuilderUnaryPolynomial.scratchWord_eq_root
      (BuilderFirstClausePrefix.nextTokenSlotPolynomial problem.verifier)
      problem.input.length with ⟨wordPrefix, hPrefix⟩
  refine ⟨wordPrefix, (cursorOutsideTail problem).drop 1, ?_⟩
  unfold finalOutside cursorWord finalTokenSlot
  rw [hPrefix, List.replicate_succ']
  simp [BuilderFirstClausePrefix.nextTokenSlot, List.append_assoc]

theorem finalConfiguration_state {language : Language}
    (problem : VerifierTableauProblem language) :
    (finalConfiguration problem).state = (machine problem).acceptState := rfl

private theorem finalConfiguration_isHalted {language : Language}
    (problem : VerifierTableauProblem language) :
    (machine problem).isHalted (finalConfiguration problem) = true := by
  rfl

/-! ### External compiled-time polynomial -/

private def scalePolynomial (coefficient : Nat)
    (polynomial : NatPolynomial) : NatPolynomial :=
  .mul (.constant coefficient) polynomial

/-- Six raw transitions implement one work transition.  The additive term
accounts exactly for the outer bridge and the complete bidirectional cursor
scan. -/
def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderFirstClausePrefix.rawTimeBound verifier)
    (.add (.constant 48)
      (scalePolynomial 12
        (BuilderUnaryPolynomial.registerSpanPolynomial
          (BuilderFirstClausePrefix.nextTokenSlotPolynomial verifier))))

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderFirstClausePrefix.rawTimeBound problem.verifier).eval
          problem.input.length + 48 +
        12 * (cursorWord problem).length := by
  rw [rawTimeBound]
  simp only [NatPolynomial.eval_add, NatPolynomial.eval_constant,
    NatPolynomial.eval_mul, scalePolynomial]
  rw [← BuilderUnaryPolynomial.scratchWord_length
    (BuilderFirstClausePrefix.nextTokenSlotPolynomial problem.verifier)
    problem.input.length]
  simp only [cursorWord]
  omega

theorem rawTimeBound_le {language : Language}
    (problem : VerifierTableauProblem language) :
    6 * workSteps problem ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hPrefix := BuilderFirstClausePrefix.rawTimeBound_le problem
  rw [rawTimeBound_eval]
  unfold workSteps cursorWorkSteps CursorAdvance.advanceWorkSteps
  omega

/-! ### Compiled execution -/

theorem run_compile_exact {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem)) (6 * workSteps problem)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)

theorem run_compile_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) :
    run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (encodeWorkConfiguration
          (workStartConfiguration (machine problem)
            (rawInputWorkTape problem.input))) =
      encodeWorkConfiguration (finalConfiguration problem) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    (machine problem) (workSteps problem)
    ((rawTimeBound problem.verifier).eval problem.input.length)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)
    (finalConfiguration_isHalted problem) (rawTimeBound_le problem)

theorem run_compile_rawTimeBound_blankEquivalent {language : Language}
    (problem : VerifierTableauProblem language) :
    Configuration.BlankEquivalent
      (run (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        (startConfig (compileWorkMachine (machine problem)) problem.input))
      (encodeWorkConfiguration (finalConfiguration problem)) := by
  have hStart := startConfig_compileWorkMachine_blankEquivalent
    (machine problem) problem.input
  have hRun := run_blankEquivalent (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length) hStart
  rw [run_compile_rawTimeBound problem] at hRun
  exact hRun

private theorem blankEquivalent_state {first second : Configuration}
    (hEquivalent : Configuration.BlankEquivalent first second) :
    first.state = second.state :=
  hEquivalent.1

private theorem blankEquivalent_accept_of_encoded
    (localMachine : WorkMachine) (first : Configuration)
    (final : WorkConfiguration)
    (hEquivalent : Configuration.BlankEquivalent first
      (encodeWorkConfiguration final))
    (hFinal : final.state = localMachine.acceptState) :
    first.state = (compileWorkMachine localMachine).acceptState := by
  have hState := blankEquivalent_state hEquivalent
  have hEncoded := (encodeWorkConfiguration_accept_iff
    localMachine final).mpr hFinal
  exact hState.trans hEncoded

set_option maxRecDepth 100000 in
theorem boundedDecide_compile_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input = .accept := by
  apply (boundedDecide_accept_iff_final
    (compileWorkMachine (machine problem))
    ((rawTimeBound problem.verifier).eval problem.input.length)
    problem.input).mpr
  exact blankEquivalent_accept_of_encoded (machine problem) _
    (finalConfiguration problem)
    (run_compile_rawTimeBound_blankEquivalent problem)
    (finalConfiguration_state problem)

theorem boundedDecide_compile_ne_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    boundedDecide (compileWorkMachine (machine problem))
        ((rawTimeBound problem.verifier).eval problem.input.length)
        problem.input ≠ .timeout := by
  rw [boundedDecide_compile_accept]
  intro impossible
  contradiction

theorem workBoundedDecide_accept {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem)
      (rawInputWorkTape problem.input) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem) (workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (finalConfiguration problem) (workRunExact problem)]
  dsimp only
  rw [finalConfiguration_state]
  rw [(nat_beq_true_iff _ _).mpr rfl]
  rfl

/-! ### Fail-closed boundaries -/

private theorem verdict_timeout_of_not_halted {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration)
    (hHalted : (machine problem).isHalted config = false) :
    (if config.state == (machine problem).acceptState then WorkVerdict.accept
     else if config.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (config.state == (machine problem).acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (config.state == (machine problem).rejectState) with
      | true =>
          rw [hAccept, hReject] at hHalted
          contradiction
      | false => rfl

private theorem machine_isHalted_prefix_false {language : Language}
    (problem : VerifierTableauProblem language)
    (config : WorkConfiguration) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
          config) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_first_false
      (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine config
  simpa [machine] using hHalted

/-- The complete first-clause endpoint is still globally nonhalting until the
new symbol-preserving bridge launches the cursor table. -/
theorem prefixEndpoint_before_launch_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem)
        (BuilderFirstClausePrefix.workSteps problem)
        (rawInputWorkTape problem.input) = .timeout := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact (machine problem)
    (BuilderFirstClausePrefix.workSteps problem)
    (workStartConfiguration (machine problem)
      (rawInputWorkTape problem.input))
    (renameConfiguration BuilderFirstClausePrefix.WorkChain.firstState
      (BuilderFirstClausePrefix.finalConfiguration problem))
    (prefix_workRunExact problem)]
  exact verdict_timeout_of_not_halted problem _
    (machine_isHalted_prefix_false problem
      (BuilderFirstClausePrefix.finalConfiguration problem))

private theorem localMalformed_isHalted_false
    (left right : List WorkSymbol) :
    CursorAdvance.machine.isHalted
      (CursorAdvance.malformedScratchConfiguration left right) = false := by
  rfl

private theorem localDead_isHalted_false (tape : WorkTape) :
    CursorAdvance.machine.isHalted
      (CursorAdvance.deadConfiguration tape) = false := by
  rfl

private theorem globalMalformed_workStep {language : Language}
    (problem : VerifierTableauProblem language)
    (left right : List WorkSymbol) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.malformedScratchConfiguration left right)) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.deadConfiguration
            (CursorAdvance.malformedScratchConfiguration left right).tape)) := by
  have hStep := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    (CursorAdvance.malformedScratchConfiguration left right)
    (CursorAdvance.deadConfiguration
      (CursorAdvance.malformedScratchConfiguration left right).tape)
    (CursorAdvance.malformedScratch_workStep left right)
  simpa [machine] using hStep

private theorem globalDead_workStep {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    workStep? (machine problem)
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.deadConfiguration tape)) =
      some
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.deadConfiguration tape)) := by
  have hStep := BuilderFirstClausePrefix.WorkChain.second_workStep_of_some
    (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
    (CursorAdvance.deadConfiguration tape)
    (CursorAdvance.deadConfiguration tape) (CursorAdvance.dead_workStep tape)
  simpa [machine] using hStep

private theorem globalDead_workRun {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (tape : WorkTape) :
    workRun (machine problem) fuel
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.deadConfiguration tape)) =
      renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
        (CursorAdvance.deadConfiguration tape) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      unfold workRun
      rw [globalDead_workStep]
      exact ih

private theorem globalMalformed_isHalted_false {language : Language}
    (problem : VerifierTableauProblem language)
    (left right : List WorkSymbol) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.malformedScratchConfiguration left right)) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
      (CursorAdvance.malformedScratchConfiguration left right)
      (localMalformed_isHalted_false left right)
  simpa [machine] using hHalted

private theorem globalDead_isHalted_false {language : Language}
    (problem : VerifierTableauProblem language) (tape : WorkTape) :
    (machine problem).isHalted
        (renameConfiguration BuilderFirstClausePrefix.WorkChain.secondState
          (CursorAdvance.deadConfiguration tape)) = false := by
  have hHalted :=
    BuilderFirstClausePrefix.WorkChain.machine_isHalted_second_false_of_local
      (BuilderFirstClausePrefix.machine problem) CursorAdvance.machine
      (CursorAdvance.deadConfiguration tape)
      (localDead_isHalted_false tape)
  simpa [machine] using hHalted

/-- A malformed scratch symbol enters the explicit nonhalting dead state and
remains timeout for every fuel budget. -/
theorem malformedCursorScratch_timeout {language : Language}
    (problem : VerifierTableauProblem language) (fuel : Nat)
    (left right : List WorkSymbol) :
    (let config := renameConfiguration
        BuilderFirstClausePrefix.WorkChain.secondState
        (CursorAdvance.malformedScratchConfiguration left right)
     let result := workRun (machine problem) fuel config
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  let bad := CursorAdvance.malformedScratchConfiguration left right
  let dead := CursorAdvance.deadConfiguration bad.tape
  let globalBad := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState bad
  let globalDead := renameConfiguration
    BuilderFirstClausePrefix.WorkChain.secondState dead
  cases fuel with
  | zero =>
      change
        (if globalBad.state == (machine problem).acceptState then
          WorkVerdict.accept
         else if globalBad.state == (machine problem).rejectState then
          WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      exact verdict_timeout_of_not_halted problem globalBad (by
        simpa [globalBad, bad] using
          globalMalformed_isHalted_false problem left right)
  | succ fuel =>
      have hRun : workRun (machine problem) (fuel + 1) globalBad =
          globalDead := by
        unfold workRun
        rw [show workStep? (machine problem) globalBad = some globalDead by
          simpa [globalBad, globalDead, bad, dead] using
            globalMalformed_workStep problem left right]
        simpa [globalDead, dead] using
          globalDead_workRun problem fuel bad.tape
      change
        (let result := workRun (machine problem) (fuel + 1) globalBad
         if result.state == (machine problem).acceptState then
           WorkVerdict.accept
         else if result.state == (machine problem).rejectState then
           WorkVerdict.reject
         else WorkVerdict.timeout) = WorkVerdict.timeout
      rw [hRun]
      exact verdict_timeout_of_not_halted problem globalDead (by
        simpa [globalDead, dead] using
          globalDead_isHalted_false problem bad.tape)

private theorem workRunExact_succ_split_last {language : Language}
    (problem : VerifierTableauProblem language) :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? (machine problem) (steps + 1) initial = some final →
      ∃ before,
        workRunExact? (machine problem) steps initial = some before ∧
        workStep? (machine problem) before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? (machine problem) initial with
      | none =>
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some next =>
                 workRunExact? (machine problem) (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? (machine problem) (steps + 1) next =
              some final := by
            change
              (match workStep? (machine problem) initial with
               | none => none
               | some result =>
                   workRunExact? (machine problem) (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? (machine problem) initial with
             | none => none
             | some result =>
                 workRunExact? (machine problem) steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some {language : Language}
    (problem : VerifierTableauProblem language)
    (config next : WorkConfiguration)
    (hStep : workStep? (machine problem) config = some next) :
    (machine problem).isHalted config = false := by
  cases hHalted : (machine problem).isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive {language : Language}
    (problem : VerifierTableauProblem language) : 0 < workSteps problem := by
  unfold workSteps
  omega

/-- Removing the final successful cursor transition leaves a nonhalting state,
so the exact composed trace cannot accept one work step early. -/
theorem work_one_step_short_timeout {language : Language}
    (problem : VerifierTableauProblem language) :
    workBoundedDecide (machine problem) (workSteps problem - 1)
        (rawInputWorkTape problem.input) = .timeout := by
  let short := workSteps problem - 1
  let initial := workStartConfiguration (machine problem)
    (rawInputWorkTape problem.input)
  let final := finalConfiguration problem
  have hSucc : short + 1 = workSteps problem := by
    dsimp [short]
    have hPositive := workSteps_positive problem
    omega
  have hExact := workRunExact problem
  change workRunExact? (machine problem) (workSteps problem) initial =
    some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last problem short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun (machine problem) short initial = before :=
    workRun_eq_of_workRunExact (machine problem) short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some
    problem before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun (machine problem) short initial
     if result.state == (machine problem).acceptState then WorkVerdict.accept
     else if result.state == (machine problem).rejectState then
       WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  exact verdict_timeout_of_not_halted problem before hNotHalted

end BuilderDynamicTokenCursorStep

end CookLevin

end PNP.Concrete
