/-
Copyright (c) 2026 PNP Labs.

A fixed literal bridge from the canonical post-header divider endpoint to the
existing arbitrary-coordinate unary comparator.  The bridge copies the exact
formula-clause count from a protected workspace sidecar, preserves the divider
remainder/exterior ledger behind a fresh boundary, and exposes the literal
divider quotient marks as the comparator coordinate.

This module classifies body versus the unique Finish route.  It does not select
or emit a CNF token and does not construct the complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderPostHeaderRawTapeBridge

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPostDividerRawRouteClassifier

open BuilderArbitrarySlotPostHeaderDecoder

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

abbrev unitSymbol : WorkSymbol := BuilderUnaryPolynomial.unitSymbol
abbrev separatorSymbol : WorkSymbol := BuilderUnaryPolynomial.separatorSymbol
abbrev endSymbol : WorkSymbol := BuilderUnaryPolynomial.scratchEndSymbol
abbrev coordinateMark : WorkSymbol := BuilderUnaryPolynomial.registerMarkSymbol
abbrev consumedDividend : WorkSymbol :=
  BuilderPostHeaderRawDivider.consumedDividend
abbrev countMark : WorkSymbol := WorkSymbol.zeroBlank
abbrev leftBoundary : WorkSymbol := PipelineTape.leftMarker

private def keepAction := BuilderUnaryPolynomial.keepAction
private def writeAction := BuilderUnaryPolynomial.writeAction
private def deadAction := BuilderUnaryPolynomial.deadAction

/-! ## Fixed literal bridge table -/

private def startSpec : StateSpec := fun read =>
  if read = endSymbol then
    writeAction 1 leftBoundary .right
  else
    deadAction 19 read

private def scanQuotientSpec : StateSpec := fun read =>
  if read = coordinateMark then
    writeAction 1 unitSymbol .right
  else if read = WorkSymbol.blank then
    writeAction 2 separatorSymbol .right
  else
    deadAction 19 read

private def writeOutputEndSpec : StateSpec := fun read =>
  if read = WorkSymbol.blank then
    writeAction 3 endSymbol .left
  else
    deadAction 19 read

private def rewindOutputSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol then
    keepAction 3 .left read
  else if read = leftBoundary then
    keepAction 4 .left read
  else
    deadAction 19 read

private def seekDividerBoundarySpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = consumedDividend then
    keepAction 4 .left read
  else if read = leftBoundary then
    keepAction 5 .left read
  else
    deadAction 19 read

private def seekExteriorBoundarySpec : StateSpec := fun read =>
  if read = leftBoundary then
    keepAction 6 .left read
  else
    keepAction 5 .left read

private def selectCountSpec : StateSpec := fun read =>
  if read = countMark then
    keepAction 6 .left read
  else if read = unitSymbol then
    writeAction 7 countMark .right
  else if read = endSymbol then
    keepAction 16 .right read
  else
    deadAction 19 read

private def countToExteriorBoundarySpec : StateSpec := fun read =>
  if read = countMark then
    keepAction 7 .right read
  else if read = leftBoundary then
    keepAction 8 .right read
  else
    deadAction 19 read

private def exteriorToDividerBoundarySpec : StateSpec := fun read =>
  if read = leftBoundary then
    keepAction 9 .right read
  else
    keepAction 8 .right read

private def dividerToFreshBoundarySpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = consumedDividend then
    keepAction 9 .right read
  else if read = leftBoundary then
    keepAction 10 .right read
  else
    deadAction 19 read

private def seekOutputEndSpec : StateSpec := fun read =>
  if read = coordinateMark ∨ read = separatorSymbol ∨ read = unitSymbol then
    keepAction 10 .right read
  else if read = endSymbol then
    writeAction 11 unitSymbol .right
  else
    deadAction 19 read

private def extendOutputEndSpec : StateSpec := fun read =>
  if read = WorkSymbol.blank then
    writeAction 12 endSymbol .left
  else
    deadAction 19 read

private def outputToFreshBoundarySpec : StateSpec := fun read =>
  if read = coordinateMark ∨ read = separatorSymbol ∨ read = unitSymbol then
    keepAction 12 .left read
  else if read = leftBoundary then
    keepAction 13 .left read
  else
    deadAction 19 read

private def freshToDividerBoundarySpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = consumedDividend then
    keepAction 13 .left read
  else if read = leftBoundary then
    keepAction 14 .left read
  else
    deadAction 19 read

private def dividerToExteriorBoundarySpec : StateSpec := fun read =>
  if read = leftBoundary then
    keepAction 6 .left read
  else
    keepAction 14 .left read

private def unusedSpec : StateSpec := fun read => deadAction 19 read

private def restoreCountSpec : StateSpec := fun read =>
  if read = countMark then
    writeAction 16 unitSymbol .right
  else if read = leftBoundary then
    keepAction 17 .right read
  else
    deadAction 19 read

private def restoreExteriorSpec : StateSpec := fun read =>
  if read = leftBoundary then
    keepAction 18 .right read
  else
    keepAction 17 .right read

private def restoreTerminalSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol ∨
      read = consumedDividend then
    keepAction 18 .right read
  else if read = leftBoundary then
    keepAction 20 .right read
  else
    deadAction 19 read

private def deadSpec : StateSpec := fun read => deadAction 19 read

private def stateSpecs : List StateSpec :=
  [startSpec, scanQuotientSpec, writeOutputEndSpec, rewindOutputSpec,
    seekDividerBoundarySpec, seekExteriorBoundarySpec, selectCountSpec,
    countToExteriorBoundarySpec, exteriorToDividerBoundarySpec,
    dividerToFreshBoundarySpec, seekOutputEndSpec, extendOutputEndSpec,
    outputToFreshBoundarySpec, freshToDividerBoundarySpec,
    dividerToExteriorBoundarySpec, unusedSpec, restoreCountSpec,
    restoreExteriorSpec, restoreTerminalSpec, deadSpec]

def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

/-- A fixed 180-rule bridge.  State 20 accepts the exact comparator input,
state 21 is unused rejection, and state 19 is a malformed-input sink. -/
def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 20
    rejectState := 21 }

theorem rules_length : rules.length = 180 := by
  rw [rules, BuilderUnaryPolynomial.rulesFrom_length]
  rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderUnaryPolynomial.rulesFrom_pairwise_query_distinct 0 stateSpecs

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by decide

private def specMachine (specs : List StateSpec) : WorkMachine :=
  { rules := BuilderUnaryPolynomial.rulesFrom 0 specs
    startState := 0
    acceptState := specs.length
    rejectState := specs.length + 1 }

private theorem machine_eq_specMachine : machine = specMachine stateSpecs := by
  rfl

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

private theorem tape_write_eq_self (tape : WorkTape)
    (symbol : WorkSymbol) (hHead : tape.head = symbol) :
    tape.write symbol = tape := by
  rw [← hHead]
  cases tape
  rfl

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

/-! ## Canonical input and output geometry -/

private def rightPathTape (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: right => { left := leftSide, head := head, right := right }

private def leftPathTape (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: left => { left := left, head := head, right := rightSide }

@[simp] private theorem rightPathTape_cons
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) :
    rightPathTape leftSide (head :: right) =
      { left := leftSide, head := head, right := right } := by
  rfl

@[simp] private theorem leftPathTape_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    leftPathTape rightSide (head :: left) =
      { left := left, head := head, right := rightSide } := by
  rfl

private theorem scanRight_replicate_exact
    (state : Nat) (symbol : WorkSymbol) (count : Nat)
    (leftSide rightTail : List WorkSymbol)
    (hStep : ∀ left right,
      workStep? machine
          { state := state
            tape := rightPathTape left (symbol :: right) } =
        some
          { state := state
            tape := rightPathTape (symbol :: left) right }) :
    workRunExact? machine count
        { state := state
          tape := rightPathTape leftSide
            (List.replicate count symbol ++ rightTail) } =
      some
        { state := state
          tape := rightPathTape
            (List.replicate count symbol ++ leftSide) rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change
        (match workStep? machine
            { state := state
              tape := rightPathTape leftSide
                (symbol :: (List.replicate count symbol ++ rightTail)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      rw [hStep]
      have hTail := ih (symbol :: leftSide)
      rw [replicate_append_self_cons] at hTail
      exact hTail

private theorem scanRight_rewrite_replicate_exact
    (state : Nat) (read write : WorkSymbol) (count : Nat)
    (leftSide rightTail : List WorkSymbol)
    (hStep : ∀ left right,
      workStep? machine
          { state := state
            tape := rightPathTape left (read :: right) } =
        some
          { state := state
            tape := rightPathTape (write :: left) right }) :
    workRunExact? machine count
        { state := state
          tape := rightPathTape leftSide
            (List.replicate count read ++ rightTail) } =
      some
        { state := state
          tape := rightPathTape
            (List.replicate count write ++ leftSide) rightTail } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change
        (match workStep? machine
            { state := state
              tape := rightPathTape leftSide
                (read :: (List.replicate count read ++ rightTail)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      rw [hStep]
      have hTail := ih (write :: leftSide)
      rw [replicate_append_self_cons] at hTail
      exact hTail

private theorem scanLeft_replicate_exact
    (state : Nat) (symbol : WorkSymbol) (count : Nat)
    (rightSide leftTail : List WorkSymbol)
    (hStep : ∀ left right,
      workStep? machine
          { state := state
            tape := leftPathTape right (symbol :: left) } =
        some
          { state := state
            tape := leftPathTape (symbol :: right) left }) :
    workRunExact? machine count
        { state := state
          tape := leftPathTape rightSide
            (List.replicate count symbol ++ leftTail) } =
      some
        { state := state
          tape := leftPathTape
            (List.replicate count symbol ++ rightSide) leftTail } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, List.cons_append]
      change
        (match workStep? machine
            { state := state
              tape := leftPathTape rightSide
                (symbol :: (List.replicate count symbol ++ leftTail)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      rw [hStep]
      have hTail := ih (symbol :: rightSide)
      rw [replicate_append_self_cons] at hTail
      exact hTail

private theorem scanLeft_list_exact
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (word rightSide leftTail : List WorkSymbol)
    (hAllowed : ∀ symbol ∈ word, Allowed symbol)
    (hStep : ∀ symbol left right, Allowed symbol →
      workStep? machine
          { state := state
            tape := leftPathTape right (symbol :: left) } =
        some
          { state := state
            tape := leftPathTape (symbol :: right) left }) :
    workRunExact? machine word.length
        { state := state
          tape := leftPathTape rightSide (word ++ leftTail) } =
      some
        { state := state
          tape := leftPathTape (word.reverse ++ rightSide) leftTail } := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons symbol rest ih =>
      have hSymbol : Allowed symbol := hAllowed symbol (by simp)
      have hRest : ∀ item ∈ rest, Allowed item := by
        intro item hItem
        exact hAllowed item (by simp [hItem])
      change
        (match workStep? machine
            { state := state
              tape := leftPathTape rightSide
                (symbol :: (rest ++ leftTail)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep symbol _ _ hSymbol]
      have hTail := ih (symbol :: rightSide) hRest
      simpa [List.reverse_cons, List.append_assoc] using hTail

private theorem scanRight_list_exact
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (word leftSide rightTail : List WorkSymbol)
    (hAllowed : ∀ symbol ∈ word, Allowed symbol)
    (hStep : ∀ symbol left right, Allowed symbol →
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
      have hSymbol : Allowed symbol := hAllowed symbol (by simp)
      have hRest : ∀ item ∈ rest, Allowed item := by
        intro item hItem
        exact hAllowed item (by simp [hItem])
      change
        (match workStep? machine
            { state := state
              tape := rightPathTape leftSide
                (symbol :: (rest ++ rightTail)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep symbol _ _ hSymbol]
      have hTail := ih (symbol :: leftSide) hRest
      simpa [List.reverse_cons, List.append_assoc] using hTail

def ExteriorSymbol (symbol : WorkSymbol) : Prop :=
  symbol = separatorSymbol ∨ symbol = countMark ∨ symbol = endSymbol ∨
    symbol = WorkSymbol.oneZero ∨ symbol = coordinateMark ∨
      symbol = consumedDividend

def SafeExteriorPrefix (items : List WorkSymbol) : Prop :=
  ∀ symbol ∈ items, ExteriorSymbol symbol

theorem exteriorSymbol_ne_leftBoundary (symbol : WorkSymbol)
    (hSymbol : ExteriorSymbol symbol) : symbol ≠ leftBoundary := by
  rcases hSymbol with h | h | h | h | h | h <;> subst symbol <;> decide

def terminalPrefix (consumed remainder width : Nat) : List WorkSymbol :=
  List.replicate width unitSymbol ++
    separatorSymbol ::
      (List.replicate remainder unitSymbol ++
        List.replicate consumed consumedDividend)

def sidecar (count : Nat) (workspace : List WorkSymbol) : List WorkSymbol :=
  List.replicate count unitSymbol ++ endSymbol :: workspace

def inputTape (consumed remainder width quotient : Nat)
    (exteriorPrefix : List WorkSymbol) (count : Nat)
    (workspace : List WorkSymbol) : WorkTape :=
  { left := terminalPrefix consumed remainder width ++
      leftBoundary ::
        (exteriorPrefix ++ leftBoundary :: sidecar count workspace)
    head := endSymbol
    right := List.replicate quotient coordinateMark }

def inputConfiguration (consumed remainder width quotient : Nat)
    (exteriorPrefix : List WorkSymbol) (count : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := 0
    tape := inputTape consumed remainder width quotient exteriorPrefix count
      workspace }

def appendExteriorTape (tape : WorkTape)
    (exterior : List WorkSymbol) : WorkTape :=
  { left := tape.left ++ exterior
    head := tape.head
    right := tape.right }

def appendExteriorConfiguration (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := configuration.state
    tape := appendExteriorTape configuration.tape exterior }

abbrev comparatorMachine : WorkMachine :=
  BuilderArbitrarySlotHeaderRouter.RawRouter.machine

def comparatorInputConfiguration (quotient count : Nat)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := appendExteriorTape
      (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape quotient count)
      exterior }

def dividerExterior (exteriorPrefix : List WorkSymbol) (count : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  exteriorPrefix ++ leftBoundary :: sidecar count workspace

def outputWord (quotient copied : Nat) : List WorkSymbol :=
  List.replicate quotient unitSymbol ++
    separatorSymbol :: (List.replicate copied unitSymbol ++ [endSymbol])

def outputPayload (quotient copied : Nat) : List WorkSymbol :=
  List.replicate quotient unitSymbol ++
    separatorSymbol :: List.replicate copied unitSymbol

theorem outputWord_eq_payload (quotient copied : Nat) :
    outputWord quotient copied = outputPayload quotient copied ++ [endSymbol] := by
  simp [outputWord, outputPayload, List.append_assoc]

def routeRight (consumed remainder width quotient copied : Nat)
    (exteriorPrefix : List WorkSymbol) : List WorkSymbol :=
  leftBoundary ::
    (exteriorPrefix.reverse ++
      leftBoundary ::
        (terminalPrefix consumed remainder width).reverse ++
          leftBoundary :: outputWord quotient copied)

def copyLoopConfiguration (consumed remainder width quotient copied
    remaining : Nat) (exteriorPrefix : List WorkSymbol)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := 6
    tape := leftPathTape
      (List.replicate copied countMark ++
        routeRight consumed remainder width quotient copied exteriorPrefix)
      (List.replicate remaining unitSymbol ++ endSymbol :: workspace) }

def terminalLength (consumed remainder width : Nat) : Nat :=
  width + remainder + consumed + 1

def setupSteps (consumed remainder width quotient : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat :=
  2 * quotient + terminalLength consumed remainder width +
    exteriorPrefix.length + 7

def copyCycleSteps (consumed remainder width quotient copied : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat :=
  4 * copied + 2 * exteriorPrefix.length +
    2 * terminalLength consumed remainder width + 2 * quotient + 13

def restoreSteps (consumed remainder width count : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat :=
  count + exteriorPrefix.length +
    terminalLength consumed remainder width + 4

def copyAllSteps (consumed remainder width quotient count copied : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat → Nat
  | 0 => restoreSteps consumed remainder width count exteriorPrefix
  | remaining + 1 =>
      copyCycleSteps consumed remainder width quotient copied exteriorPrefix +
        copyAllSteps consumed remainder width quotient count (copied + 1)
          exteriorPrefix remaining

/-- Exact bridge cost for a canonical divider terminal geometry. -/
def workSteps (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat :=
  setupSteps consumed remainder width quotient exteriorPrefix +
    copyAllSteps consumed remainder width quotient count 0 exteriorPrefix count

def TerminalSymbol (symbol : WorkSymbol) : Prop :=
  symbol = unitSymbol ∨ symbol = separatorSymbol ∨
    symbol = consumedDividend

def OutputSymbol (symbol : WorkSymbol) : Prop :=
  symbol = coordinateMark ∨ symbol = separatorSymbol ∨
    symbol = unitSymbol

theorem terminalPrefix_length (consumed remainder width : Nat) :
    (terminalPrefix consumed remainder width).length =
      terminalLength consumed remainder width := by
  simp [terminalPrefix, terminalLength]
  omega

theorem terminalPrefix_symbols (consumed remainder width : Nat) :
    ∀ symbol ∈ terminalPrefix consumed remainder width,
      TerminalSymbol symbol := by
  intro symbol hSymbol
  simp only [terminalPrefix, List.mem_append, List.mem_cons,
    List.mem_replicate] at hSymbol
  rcases hSymbol with h | h | h
  · exact Or.inl h.2
  · exact Or.inr (Or.inl h)
  · rcases h with h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inr h.2)

theorem outputPayload_symbols (quotient copied : Nat) :
    ∀ symbol ∈ outputPayload quotient copied, OutputSymbol symbol := by
  intro symbol hSymbol
  simp only [outputPayload, List.mem_append, List.mem_cons,
    List.mem_replicate] at hSymbol
  rcases hSymbol with h | h | h
  · exact Or.inr (Or.inr h.2)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.2)

private theorem setup_exact (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    workRunExact? machine
        (setupSteps consumed remainder width quotient exteriorPrefix)
        (inputConfiguration consumed remainder width quotient exteriorPrefix
          count workspace) =
      some (copyLoopConfiguration consumed remainder width quotient 0 count
        exteriorPrefix workspace) := by
  let terminal := terminalPrefix consumed remainder width
  let exterior := exteriorPrefix ++
    leftBoundary :: sidecar count workspace
  let originalLeft := terminal ++ leftBoundary :: exterior
  let c0 := inputConfiguration consumed remainder width quotient
    exteriorPrefix count workspace
  let c1 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape (leftBoundary :: originalLeft)
        (List.replicate quotient coordinateMark) }
  let c2 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        (List.replicate quotient unitSymbol ++
          leftBoundary :: originalLeft) [] }
  let c3 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (separatorSymbol ::
          (List.replicate quotient unitSymbol ++
            leftBoundary :: originalLeft)) [] }
  let c4 : WorkConfiguration :=
    { state := 3
      tape := leftPathTape [endSymbol]
        (separatorSymbol ::
          (List.replicate quotient unitSymbol ++
            leftBoundary :: originalLeft)) }
  let c5 : WorkConfiguration :=
    { state := 3
      tape := leftPathTape
        (List.replicate quotient unitSymbol ++
          [separatorSymbol, endSymbol])
        (leftBoundary :: originalLeft) }
  let c6 : WorkConfiguration :=
    { state := 4
      tape := leftPathTape
        (leftBoundary ::
          (List.replicate quotient unitSymbol ++
            [separatorSymbol, endSymbol])) originalLeft }
  let c7 : WorkConfiguration :=
    { state := 4
      tape := leftPathTape
        (terminal.reverse ++
          leftBoundary ::
            (List.replicate quotient unitSymbol ++
              [separatorSymbol, endSymbol]))
        (leftBoundary :: exterior) }
  let c8 : WorkConfiguration :=
    { state := 5
      tape := leftPathTape
        (leftBoundary ::
          (terminal.reverse ++
            leftBoundary ::
              (List.replicate quotient unitSymbol ++
                [separatorSymbol, endSymbol]))) exterior }
  let c9 : WorkConfiguration :=
    { state := 5
      tape := leftPathTape
        (exteriorPrefix.reverse ++
          leftBoundary ::
            (terminal.reverse ++
              leftBoundary ::
                (List.replicate quotient unitSymbol ++
                  [separatorSymbol, endSymbol])))
        (leftBoundary :: sidecar count workspace) }
  let c10 := copyLoopConfiguration consumed remainder width quotient 0 count
    exteriorPrefix workspace
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    simp [c0, c1, inputConfiguration, inputTape, originalLeft, exterior,
      terminal, sidecar]
    rfl
  have h12 : workRunExact? machine quotient c1 = some c2 := by
    simpa [c1, c2] using
      (scanRight_rewrite_replicate_exact 1 coordinateMark unitSymbol quotient
        (leftBoundary :: originalLeft) [] (by intro left right; rfl))
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    rfl
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    rfl
  have h45 : workRunExact? machine (quotient + 1) c4 = some c5 := by
    have hScan := scanLeft_list_exact 3
      (fun symbol => symbol = separatorSymbol ∨ symbol = unitSymbol)
      (separatorSymbol :: List.replicate quotient unitSymbol)
      [endSymbol] (leftBoundary :: originalLeft) (by
        intro symbol hSymbol
        simp only [List.mem_cons, List.mem_replicate] at hSymbol
        rcases hSymbol with h | h
        · exact Or.inl h
        · exact Or.inr h.2) (by
          intro symbol left right hSymbol
          rcases hSymbol with h | h <;> subst symbol <;> rfl)
    simpa [c4, c5, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, Nat.add_comm] using hScan
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    rfl
  have h67 : workRunExact? machine terminal.length c6 = some c7 := by
    exact scanLeft_list_exact 4 TerminalSymbol terminal
      (leftBoundary ::
        (List.replicate quotient unitSymbol ++
          [separatorSymbol, endSymbol]))
      (leftBoundary :: exterior)
      (by simpa [terminal] using
        terminalPrefix_symbols consumed remainder width)
      (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h <;> subst symbol <;> rfl)
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    rfl
  have h89 : workRunExact? machine exteriorPrefix.length c8 = some c9 := by
    exact scanLeft_list_exact 5 ExteriorSymbol exteriorPrefix
      (leftBoundary ::
        (terminal.reverse ++
          leftBoundary ::
            (List.replicate quotient unitSymbol ++
              [separatorSymbol, endSymbol])))
      (leftBoundary :: sidecar count workspace) hPrefix (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h | h | h | h <;>
          subst symbol <;> rfl)
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    simp [c9, c10, copyLoopConfiguration, routeRight, outputWord,
      sidecar, terminal, List.append_assoc]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 quotient c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1) (quotient + 1) c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1 + (quotient + 1)) 1 c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1 + (quotient + 1) + 1) terminal.length
    c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1 + (quotient + 1) + 1 + terminal.length)
    1 c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1 + (quotient + 1) + 1 + terminal.length + 1)
    exteriorPrefix.length c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + quotient + 1 + 1 + (quotient + 1) + 1 + terminal.length + 1 +
      exteriorPrefix.length) 1 c0 c9 c10 h09 h910
  have hCount :
      1 + quotient + 1 + 1 + (quotient + 1) + 1 + terminal.length + 1 +
          exteriorPrefix.length + 1 =
        setupSteps consumed remainder width quotient exteriorPrefix := by
    rw [terminalPrefix_length]
    unfold setupSteps
    omega
  rw [← hCount]
  simpa [c0, c10] using h010

private theorem copy_cycle_exact
    (consumed remainder width quotient copied remaining : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    workRunExact? machine
        (copyCycleSteps consumed remainder width quotient copied
          exteriorPrefix)
        (copyLoopConfiguration consumed remainder width quotient copied
          (remaining + 1) exteriorPrefix workspace) =
      some (copyLoopConfiguration consumed remainder width quotient
        (copied + 1) remaining exteriorPrefix workspace) := by
  let terminal := terminalPrefix consumed remainder width
  let payload := outputPayload quotient copied
  let markedLeft :=
    List.replicate copied countMark ++
      countMark ::
        (List.replicate remaining unitSymbol ++ endSymbol :: workspace)
  let route := routeRight consumed remainder width quotient copied
    exteriorPrefix
  let nextRoute := routeRight consumed remainder width quotient (copied + 1)
    exteriorPrefix
  let c0 := copyLoopConfiguration consumed remainder width quotient copied
    (remaining + 1) exteriorPrefix workspace
  let c1 : WorkConfiguration :=
    { state := 7
      tape := rightPathTape
        (countMark ::
          (List.replicate remaining unitSymbol ++ endSymbol :: workspace))
        (List.replicate copied countMark ++ route) }
  let c2 : WorkConfiguration :=
    { state := 7
      tape := rightPathTape markedLeft route }
  let c3 : WorkConfiguration :=
    { state := 8
      tape := rightPathTape (leftBoundary :: markedLeft)
        (exteriorPrefix.reverse ++
          leftBoundary ::
            (terminal.reverse ++ leftBoundary :: outputWord quotient copied)) }
  let c4 : WorkConfiguration :=
    { state := 8
      tape := rightPathTape
        (exteriorPrefix ++ leftBoundary :: markedLeft)
        (leftBoundary ::
          (terminal.reverse ++ leftBoundary :: outputWord quotient copied)) }
  let c5 : WorkConfiguration :=
    { state := 9
      tape := rightPathTape
        (leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        (terminal.reverse ++ leftBoundary :: outputWord quotient copied) }
  let c6 : WorkConfiguration :=
    { state := 9
      tape := rightPathTape
        (terminal ++
          leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        (leftBoundary :: outputWord quotient copied) }
  let c7 : WorkConfiguration :=
    { state := 10
      tape := rightPathTape
        (leftBoundary :: terminal ++
          leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        (outputWord quotient copied) }
  let c8 : WorkConfiguration :=
    { state := 10
      tape := rightPathTape
        (payload.reverse ++
          leftBoundary :: terminal ++
            leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        [endSymbol] }
  let c9 : WorkConfiguration :=
    { state := 11
      tape := rightPathTape
        (unitSymbol ::
          payload.reverse ++
            leftBoundary :: terminal ++
              leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        [] }
  let c10 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape [endSymbol]
        (unitSymbol ::
          payload.reverse ++
            leftBoundary :: terminal ++
              leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft) }
  let backWord := unitSymbol :: payload.reverse
  let c11 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (backWord.reverse ++ [endSymbol])
        (leftBoundary :: terminal ++
          leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft) }
  let c12 : WorkConfiguration :=
    { state := 13
      tape := leftPathTape
        (leftBoundary :: backWord.reverse ++ [endSymbol])
        (terminal ++
          leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft) }
  let c13 : WorkConfiguration :=
    { state := 13
      tape := leftPathTape
        (terminal.reverse ++
          leftBoundary :: backWord.reverse ++ [endSymbol])
        (leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft) }
  let c14 : WorkConfiguration :=
    { state := 14
      tape := leftPathTape
        (leftBoundary :: terminal.reverse ++
          leftBoundary :: backWord.reverse ++ [endSymbol])
        (exteriorPrefix ++ leftBoundary :: markedLeft) }
  let c15 : WorkConfiguration :=
    { state := 14
      tape := leftPathTape
        (exteriorPrefix.reverse ++
          leftBoundary :: terminal.reverse ++
            leftBoundary :: backWord.reverse ++ [endSymbol])
        (leftBoundary :: markedLeft) }
  let c16 : WorkConfiguration :=
    { state := 6
      tape := leftPathTape nextRoute
        (List.replicate (copied + 1) countMark ++
          List.replicate remaining unitSymbol ++ endSymbol :: workspace) }
  let c17 := copyLoopConfiguration consumed remainder width quotient
    (copied + 1) remaining exteriorPrefix workspace
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    simp [c0, c1, copyLoopConfiguration, route, List.replicate_succ]
    rfl
  have h12 : workRunExact? machine copied c1 = some c2 := by
    simpa [c1, c2, markedLeft] using
      (scanRight_replicate_exact 7 countMark copied
        (countMark ::
          (List.replicate remaining unitSymbol ++ endSymbol :: workspace))
        route (by intro left right; rfl))
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    simp [c2, c3, route, routeRight, List.append_assoc]
    rfl
  have h34 : workRunExact? machine exteriorPrefix.length c3 = some c4 := by
    have hReverse : SafeExteriorPrefix exteriorPrefix.reverse := by
      intro symbol hSymbol
      exact hPrefix symbol (by simpa using hSymbol)
    have hScan := scanRight_list_exact 8 ExteriorSymbol
      exteriorPrefix.reverse (leftBoundary :: markedLeft)
      (leftBoundary ::
        (terminal.reverse ++ leftBoundary :: outputWord quotient copied))
      hReverse (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h | h | h | h <;>
          subst symbol <;> rfl)
    simpa [c3, c4] using hScan
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    rfl
  have h56 : workRunExact? machine terminal.length c5 = some c6 := by
    have hReverse : ∀ symbol ∈ terminal.reverse,
        TerminalSymbol symbol := by
      intro symbol hSymbol
      exact terminalPrefix_symbols consumed remainder width symbol
        (by simpa [terminal] using hSymbol)
    have hScan := scanRight_list_exact 9 TerminalSymbol terminal.reverse
      (leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
      (leftBoundary :: outputWord quotient copied) hReverse (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h <;> subst symbol <;> rfl)
    simpa [c5, c6] using hScan
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    rfl
  have h78 : workRunExact? machine payload.length c7 = some c8 := by
    have hScan := scanRight_list_exact 10 OutputSymbol payload
      (leftBoundary :: terminal ++
        leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
      [endSymbol] (by simpa [payload] using
        outputPayload_symbols quotient copied) (by
          intro symbol left right hSymbol
          rcases hSymbol with h | h | h <;> subst symbol <;> rfl)
    simpa [c7, c8, outputWord_eq_payload, payload] using hScan
  have h89 : workRunExact? machine 1 c8 = some c9 := by
    apply workRunExact_one
    rfl
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    rfl
  have h1011 : workRunExact? machine backWord.length c10 = some c11 := by
    have hBack : ∀ symbol ∈ backWord, OutputSymbol symbol := by
      intro symbol hSymbol
      simp only [backWord, List.mem_cons] at hSymbol
      rcases hSymbol with h | h
      · exact Or.inr (Or.inr h)
      · exact outputPayload_symbols quotient copied symbol
          (by simpa [payload] using h)
    simpa [c10, c11, backWord] using
      (scanLeft_list_exact 12 OutputSymbol backWord [endSymbol]
        (leftBoundary :: terminal ++
          leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        hBack (by
          intro symbol left right hSymbol
          rcases hSymbol with h | h | h <;> subst symbol <;> rfl))
  have h1112 : workRunExact? machine 1 c11 = some c12 := by
    apply workRunExact_one
    rfl
  have h1213 : workRunExact? machine terminal.length c12 = some c13 := by
    simpa [c12, c13] using
      (scanLeft_list_exact 13 TerminalSymbol terminal
        (leftBoundary :: backWord.reverse ++ [endSymbol])
        (leftBoundary :: exteriorPrefix ++ leftBoundary :: markedLeft)
        (by simpa [terminal] using
          terminalPrefix_symbols consumed remainder width)
        (by
          intro symbol left right hSymbol
          rcases hSymbol with h | h | h <;> subst symbol <;> rfl))
  have h1314 : workRunExact? machine 1 c13 = some c14 := by
    apply workRunExact_one
    rfl
  have h1415 : workRunExact? machine exteriorPrefix.length c14 = some c15 := by
    simpa [c14, c15] using
      (scanLeft_list_exact 14 ExteriorSymbol exteriorPrefix
        (leftBoundary :: terminal.reverse ++
          leftBoundary :: backWord.reverse ++ [endSymbol])
        (leftBoundary :: markedLeft) hPrefix (by
          intro symbol left right hSymbol
          rcases hSymbol with h | h | h | h | h | h <;>
            subst symbol <;> rfl))
  have h1516 : workRunExact? machine 1 c15 = some c16 := by
    apply workRunExact_one
    simp [c15, c16, markedLeft, nextRoute, routeRight, outputWord,
      outputPayload, backWord, payload, replicate_append_self_cons,
      List.replicate_succ, List.append_assoc]
    rfl
  have h1617 : workRunExact? machine (copied + 1) c16 = some c17 := by
    have hScan := scanLeft_replicate_exact 6 countMark (copied + 1)
      nextRoute
      (List.replicate remaining unitSymbol ++ endSymbol :: workspace)
      (by intro left right; rfl)
    simpa [c16, c17, copyLoopConfiguration, nextRoute] using hScan
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 copied c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1) exteriorPrefix.length c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1) terminal.length
    c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length)
    1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1)
    payload.length c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length) 1 c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1) 1 c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1) backWord.length c0 c10 c11 h010 h1011
  have h012 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length) 1 c0 c11 c12 h011 h1112
  have h013 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length + 1) terminal.length
    c0 c12 c13 h012 h1213
  have h014 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length + 1 + terminal.length)
    1 c0 c13 c14 h013 h1314
  have h015 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length + 1 + terminal.length + 1)
    exteriorPrefix.length c0 c14 c15 h014 h1415
  have h016 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length + 1 + terminal.length + 1 +
      exteriorPrefix.length) 1 c0 c15 c16 h015 h1516
  have h017 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
      payload.length + 1 + 1 + backWord.length + 1 + terminal.length + 1 +
      exteriorPrefix.length + 1) (copied + 1) c0 c16 c17 h016 h1617
  have hPayloadLength : payload.length = quotient + 1 + copied := by
    simp [payload, outputPayload]
    omega
  have hBackLength : backWord.length = quotient + copied + 2 := by
    simp [backWord, payload, outputPayload]
    omega
  have hCount :
      1 + copied + 1 + exteriorPrefix.length + 1 + terminal.length + 1 +
          payload.length + 1 + 1 + backWord.length + 1 + terminal.length +
          1 + exteriorPrefix.length + 1 + (copied + 1) =
        copyCycleSteps consumed remainder width quotient copied
          exteriorPrefix := by
    rw [hPayloadLength, hBackLength, terminalPrefix_length]
    unfold copyCycleSteps
    omega
  rw [← hCount]
  simpa [c0, c17] using h017

def preservedExterior (consumed remainder width : Nat)
    (exteriorPrefix : List WorkSymbol) (count : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  terminalPrefix consumed remainder width ++
    leftBoundary ::
      (exteriorPrefix ++ leftBoundary :: sidecar count workspace)

private theorem restore_exact
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    workRunExact? machine
        (restoreSteps consumed remainder width count exteriorPrefix)
        (copyLoopConfiguration consumed remainder width quotient count 0
          exteriorPrefix workspace) =
      some (comparatorInputConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)) := by
  let terminal := terminalPrefix consumed remainder width
  let route := routeRight consumed remainder width quotient count
    exteriorPrefix
  let c0 := copyLoopConfiguration consumed remainder width quotient count 0
    exteriorPrefix workspace
  let c1 : WorkConfiguration :=
    { state := 16
      tape := rightPathTape (endSymbol :: workspace)
        (List.replicate count countMark ++ route) }
  let c2 : WorkConfiguration :=
    { state := 16
      tape := rightPathTape
        (List.replicate count unitSymbol ++ endSymbol :: workspace) route }
  let c3 : WorkConfiguration :=
    { state := 17
      tape := rightPathTape
        (leftBoundary ::
          (List.replicate count unitSymbol ++ endSymbol :: workspace))
        (exteriorPrefix.reverse ++
          leftBoundary ::
            (terminal.reverse ++ leftBoundary :: outputWord quotient count)) }
  let c4 : WorkConfiguration :=
    { state := 17
      tape := rightPathTape
        (exteriorPrefix ++
          leftBoundary ::
            (List.replicate count unitSymbol ++ endSymbol :: workspace))
        (leftBoundary ::
          (terminal.reverse ++ leftBoundary :: outputWord quotient count)) }
  let c5 : WorkConfiguration :=
    { state := 18
      tape := rightPathTape
        (leftBoundary ::
          (exteriorPrefix ++
            leftBoundary ::
              (List.replicate count unitSymbol ++ endSymbol :: workspace)))
        (terminal.reverse ++ leftBoundary :: outputWord quotient count) }
  let c6 : WorkConfiguration :=
    { state := 18
      tape := rightPathTape
        (terminal ++
          leftBoundary ::
            (exteriorPrefix ++
              leftBoundary ::
                (List.replicate count unitSymbol ++ endSymbol :: workspace)))
        (leftBoundary :: outputWord quotient count) }
  let c7 := comparatorInputConfiguration quotient count
    (preservedExterior consumed remainder width exteriorPrefix count workspace)
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    simp [c0, c1, copyLoopConfiguration, route]
    rfl
  have h12 : workRunExact? machine count c1 = some c2 := by
    simpa [c1, c2] using
      (scanRight_rewrite_replicate_exact 16 countMark unitSymbol count
        (endSymbol :: workspace) route (by intro left right; rfl))
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    simp [c2, c3, route, routeRight, List.append_assoc]
    rfl
  have h34 : workRunExact? machine exteriorPrefix.length c3 = some c4 := by
    have hReverse : SafeExteriorPrefix exteriorPrefix.reverse := by
      intro symbol hSymbol
      exact hPrefix symbol (by simpa using hSymbol)
    have hScan := scanRight_list_exact 17 ExteriorSymbol
      exteriorPrefix.reverse
      (leftBoundary ::
        (List.replicate count unitSymbol ++ endSymbol :: workspace))
      (leftBoundary ::
        (terminal.reverse ++ leftBoundary :: outputWord quotient count))
      hReverse (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h | h | h | h <;>
          subst symbol <;> rfl)
    simpa [c3, c4] using hScan
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    rfl
  have h56 : workRunExact? machine terminal.length c5 = some c6 := by
    have hReverse : ∀ symbol ∈ terminal.reverse,
        TerminalSymbol symbol := by
      intro symbol hSymbol
      exact terminalPrefix_symbols consumed remainder width symbol
        (by simpa [terminal] using hSymbol)
    have hScan := scanRight_list_exact 18 TerminalSymbol terminal.reverse
      (leftBoundary ::
        (exteriorPrefix ++
          leftBoundary ::
            (List.replicate count unitSymbol ++ endSymbol :: workspace)))
      (leftBoundary :: outputWord quotient count) hReverse (by
        intro symbol left right hSymbol
        rcases hSymbol with h | h | h <;> subst symbol <;> rfl)
    simpa [c5, c6] using hScan
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    cases quotient with
    | zero =>
        simp [c6, c7, comparatorInputConfiguration, appendExteriorTape,
          preservedExterior, outputWord, sidecar, terminal,
          BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape,
          BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonTape,
          BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonWord]
        rfl
    | succ quotient =>
        simp [c6, c7, comparatorInputConfiguration, appendExteriorTape,
          preservedExterior, outputWord, sidecar, terminal,
          BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape,
          BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonTape,
          BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonWord,
          List.replicate_succ]
        rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 count c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + count) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + count + 1) exteriorPrefix.length c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + count + 1 + exteriorPrefix.length) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + count + 1 + exteriorPrefix.length + 1) terminal.length
    c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + count + 1 + exteriorPrefix.length + 1 + terminal.length)
    1 c0 c6 c7 h06 h67
  have hCount :
      1 + count + 1 + exteriorPrefix.length + 1 + terminal.length + 1 =
        restoreSteps consumed remainder width count exteriorPrefix := by
    rw [terminalPrefix_length]
    unfold restoreSteps
    omega
  rw [← hCount]
  simpa [c0, c7] using h07

private theorem copy_all_exact
    (consumed remainder width quotient count copied remaining : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix)
    (hCount : copied + remaining = count) :
    workRunExact? machine
        (copyAllSteps consumed remainder width quotient count copied
          exteriorPrefix remaining)
        (copyLoopConfiguration consumed remainder width quotient copied
          remaining exteriorPrefix workspace) =
      some (comparatorInputConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)) := by
  induction remaining generalizing copied with
  | zero =>
      have hCopied : copied = count := by omega
      subst copied
      simpa [copyAllSteps] using restore_exact consumed remainder width
        quotient count exteriorPrefix workspace hPrefix
  | succ remaining ih =>
      have hCycle := copy_cycle_exact consumed remainder width quotient copied
        remaining exteriorPrefix workspace hPrefix
      have hTail := ih (copied + 1) (by omega)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (copyCycleSteps consumed remainder width quotient copied exteriorPrefix)
        (copyAllSteps consumed remainder width quotient count (copied + 1)
          exteriorPrefix remaining)
        (copyLoopConfiguration consumed remainder width quotient copied
          (remaining + 1) exteriorPrefix workspace)
        (copyLoopConfiguration consumed remainder width quotient (copied + 1)
          remaining exteriorPrefix workspace)
        (comparatorInputConfiguration quotient count
          (preservedExterior consumed remainder width exteriorPrefix count
            workspace)) hCycle hTail
      simpa [copyAllSteps] using hAll

/-- Every canonical divider terminal geometry and safe exterior prefix has one
exact trace to the protected comparator input. -/
theorem workRunExact (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    workRunExact? machine
        (workSteps consumed remainder width quotient count exteriorPrefix)
        (inputConfiguration consumed remainder width quotient exteriorPrefix
          count workspace) =
      some (comparatorInputConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)) := by
  have hSetup := setup_exact consumed remainder width quotient count
    exteriorPrefix workspace hPrefix
  have hCopy := copy_all_exact consumed remainder width quotient count 0 count
    exteriorPrefix workspace hPrefix (by omega)
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine
    (setupSteps consumed remainder width quotient exteriorPrefix)
    (copyAllSteps consumed remainder width quotient count 0 exteriorPrefix
      count)
    (inputConfiguration consumed remainder width quotient exteriorPrefix count
      workspace)
    (copyLoopConfiguration consumed remainder width quotient 0 count
      exteriorPrefix workspace)
    (comparatorInputConfiguration quotient count
      (preservedExterior consumed remainder width exteriorPrefix count
        workspace)) hSetup hCopy
  simpa [workSteps] using hAll

/-! ## Shielded M209 comparator transport -/

private def ComparatorBoundaryProtected (tape : WorkTape) : Prop :=
  (∃ leftPrefix, tape.left = leftPrefix ++ [leftBoundary]) ∨
    (tape.left = [] ∧ tape.head = leftBoundary)

private def comparatorBoundaryRuleSafe (rule : WorkRule) : Bool :=
  if rule.readSymbol == leftBoundary then
    (rule.writeSymbol == leftBoundary) && !(rule.move == .left)
  else
    true

private theorem comparator_rules_boundary_safe :
    BuilderArbitrarySlotHeaderRouter.RawRouter.rules.all
      comparatorBoundaryRuleSafe = true := by
  decide

private theorem findWorkRule_some_mem {rules : List WorkRule}
    {state : Nat} {symbol : WorkSymbol} {selected : WorkRule}
    (hFind : findWorkRule rules state symbol = some selected) :
    selected ∈ rules := by
  induction rules with
  | nil => contradiction
  | cons first rest ih =>
      by_cases hMatches :
          first.sourceState = state ∧ first.readSymbol = symbol
      · have hHead := findWorkRule_cons_of_matches first rest state symbol
          hMatches
        have hEqual : first = selected := Option.some.inj (hHead.symm.trans hFind)
        subst selected
        exact List.Mem.head rest
      · have hTail := findWorkRule_cons_of_not_matches first rest state symbol
          hMatches
        exact List.Mem.tail first (ih (hTail.symm.trans hFind))

private theorem comparator_rule_safe_at_boundary (rule : WorkRule)
    (hRule : rule ∈ BuilderArbitrarySlotHeaderRouter.RawRouter.rules)
    (hRead : rule.readSymbol = leftBoundary) :
    rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left := by
  have hSafe := (List.all_eq_true.mp comparator_rules_boundary_safe) rule hRule
  simp [comparatorBoundaryRuleSafe, hRead] at hSafe
  refine ⟨hSafe.1, ?_⟩
  cases hMove : rule.move with
  | left =>
      intro _
      rw [hMove] at hSafe
      have hFalse : (true : Bool) = false := hSafe.2
      exact Bool.noConfusion hFalse
  | stay =>
      intro hImpossible
      cases hImpossible
  | right =>
      intro hImpossible
      cases hImpossible

private theorem comparatorBoundaryProtected_head_of_left_nil
    (tape : WorkTape) (hProtected : ComparatorBoundaryProtected tape)
    (hLeft : tape.left = []) : tape.head = leftBoundary := by
  rcases hProtected with ⟨leftPrefix, hPrefix⟩ | hHead
  · have hImpossible : ([] : List WorkSymbol) =
        leftPrefix ++ [leftBoundary] := hLeft.symm.trans hPrefix
    cases leftPrefix with
    | nil => cases hImpossible
    | cons _ _ => cases hImpossible
  · exact hHead.2

private theorem appendExteriorTape_write (tape : WorkTape)
    (symbol : WorkSymbol) (exterior : List WorkSymbol) :
    appendExteriorTape (tape.write symbol) exterior =
      (appendExteriorTape tape exterior).write symbol := by
  rfl

private theorem appendExteriorTape_moveRight (tape : WorkTape)
    (exterior : List WorkSymbol) :
    appendExteriorTape tape.moveRight exterior =
      (appendExteriorTape tape exterior).moveRight := by
  rcases tape with ⟨left, head, right⟩
  cases right <;> rfl

private theorem appendExteriorTape_moveLeft (tape : WorkTape)
    (exterior : List WorkSymbol) (hLeft : tape.left ≠ []) :
    appendExteriorTape tape.moveLeft exterior =
      (appendExteriorTape tape exterior).moveLeft := by
  cases hTape : tape.left with
  | nil => contradiction
  | cons symbol rest =>
      simp [appendExteriorTape, WorkTape.moveLeft, hTape]

private theorem comparatorBoundaryProtected_apply
    (configuration : WorkConfiguration) (rule : WorkRule)
    (hProtected : ComparatorBoundaryProtected configuration.tape)
    (hBoundary : configuration.tape.head = leftBoundary →
      rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left) :
    ComparatorBoundaryProtected (applyWorkRule rule configuration).tape := by
  rcases hProtected with ⟨leftPrefix, hPrefix⟩ | hAtBoundary
  · cases hMove : rule.move with
    | stay =>
        exact Or.inl ⟨leftPrefix, by
          simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove, hPrefix]⟩
    | right =>
        exact Or.inl ⟨rule.writeSymbol :: leftPrefix, by
          cases hRight : configuration.tape.right <;>
            simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveRight, hPrefix, hRight]⟩
    | left =>
        cases leftPrefix with
        | nil =>
            exact Or.inr (by
              simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveLeft, hPrefix])
        | cons symbol rest =>
            exact Or.inl ⟨rest, by
              simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
                WorkTape.moveLeft, hPrefix]⟩
  · have hSafe := hBoundary hAtBoundary.2
    cases hMove : rule.move with
    | left => exact False.elim (hSafe.2 hMove)
    | stay =>
        exact Or.inr (by
          simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
            hAtBoundary, hSafe.1])
    | right =>
        exact Or.inl ⟨[], by
          cases hRight : configuration.tape.right <;>
            simp [applyWorkRule, WorkTape.write, WorkTape.move, hMove,
              WorkTape.moveRight, hAtBoundary, hSafe.1, hRight]⟩

private theorem comparator_step_transport
    (configuration next : WorkConfiguration)
    (exterior : List WorkSymbol)
    (hProtected : ComparatorBoundaryProtected configuration.tape)
    (hStep : workStep? comparatorMachine configuration = some next) :
    ComparatorBoundaryProtected next.tape ∧
      workStep? comparatorMachine
          (appendExteriorConfiguration configuration exterior) =
        some (appendExteriorConfiguration next exterior) := by
  rcases workStep?_some_exists comparatorMachine configuration next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hRule := findWorkRule_some_mem hFind
  have hMatches := findWorkRule_some_matches hFind
  have hBoundary : configuration.tape.head = leftBoundary →
      rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left := by
    intro hHead
    exact comparator_rule_safe_at_boundary rule hRule (hMatches.2.trans hHead)
  have hNextProtected : ComparatorBoundaryProtected next.tape := by
    rw [hNext]
    exact comparatorBoundaryProtected_apply configuration rule hProtected
      hBoundary
  have hLeftNonempty : rule.move = .left → configuration.tape.left ≠ [] := by
    intro hMove hLeft
    have hHead := comparatorBoundaryProtected_head_of_left_nil
      configuration.tape hProtected hLeft
    exact (hBoundary hHead).2 hMove
  have hTapeCommute :
      appendExteriorTape
          ((configuration.tape.write rule.writeSymbol).move rule.move)
          exterior =
        ((appendExteriorTape configuration.tape exterior).write
          rule.writeSymbol).move rule.move := by
    cases hMove : rule.move with
    | stay => rfl
    | right =>
        simpa [WorkTape.move, hMove, appendExteriorTape_write] using
          appendExteriorTape_moveRight
            (configuration.tape.write rule.writeSymbol) exterior
    | left =>
        have hNonempty :
            (configuration.tape.write rule.writeSymbol).left ≠ [] := by
          simpa [WorkTape.write] using hLeftNonempty hMove
        simpa [WorkTape.move, hMove, appendExteriorTape_write] using
          appendExteriorTape_moveLeft
            (configuration.tape.write rule.writeSymbol) exterior hNonempty
  have hHaltedExterior :
      comparatorMachine.isHalted
          (appendExteriorConfiguration configuration exterior) = false := by
    simpa [WorkMachine.isHalted, appendExteriorConfiguration,
      appendExteriorTape] using hHalted
  have hFindExterior :
      findWorkRule comparatorMachine.rules
          (appendExteriorConfiguration configuration exterior).state
          (appendExteriorConfiguration configuration exterior).tape.head =
        some rule := by
    simpa [appendExteriorConfiguration, appendExteriorTape] using hFind
  have hExteriorStep := workStep?_eq_apply_of_find comparatorMachine
    (appendExteriorConfiguration configuration exterior) rule
    hHaltedExterior hFindExterior
  refine ⟨hNextProtected, ?_⟩
  rw [hExteriorStep]
  apply congrArg Option.some
  rw [hNext]
  cases configuration
  simp only [appendExteriorConfiguration, applyWorkRule]
  exact congrArg (fun tape => WorkConfiguration.mk rule.targetState tape)
    hTapeCommute.symm

private theorem comparator_workRunExact_transport :
    ∀ (steps : Nat) (initial final : WorkConfiguration)
      (exterior : List WorkSymbol),
      ComparatorBoundaryProtected initial.tape →
      workRunExact? comparatorMachine steps initial = some final →
      workRunExact? comparatorMachine steps
          (appendExteriorConfiguration initial exterior) =
        some (appendExteriorConfiguration final exterior) := by
  intro steps
  induction steps with
  | zero =>
      intro initial final exterior _hProtected hRun
      have hEqual : initial = final := Option.some.inj hRun
      subst final
      rfl
  | succ steps ih =>
      intro initial final exterior hProtected hRun
      cases hStep : workStep? comparatorMachine initial with
      | none =>
          change
            (match workStep? comparatorMachine initial with
             | none => none
             | some next => workRunExact? comparatorMachine steps next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? comparatorMachine steps next =
              some final := by
            change
              (match workStep? comparatorMachine initial with
               | none => none
               | some result => workRunExact? comparatorMachine steps result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          have hTransport := comparator_step_transport initial next exterior
            hProtected hStep
          change
            (match workStep? comparatorMachine
                (appendExteriorConfiguration initial exterior) with
             | none => none
             | some result => workRunExact? comparatorMachine steps result) =
              some (appendExteriorConfiguration final exterior)
          rw [hTransport.2]
          exact ih next final exterior hTransport.1 hTail

def shieldedComparatorStartConfiguration (quotient count : Nat)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := comparatorMachine.startState
    tape := appendExteriorTape
      (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape quotient count)
      exterior }

def shieldedComparatorFinalConfiguration (quotient count : Nat)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  appendExteriorConfiguration
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
      quotient count) exterior

private theorem comparator_input_boundary_protected (quotient count : Nat) :
    ComparatorBoundaryProtected
      (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape quotient count) := by
  refine Or.inl ⟨[], ?_⟩
  cases quotient <;>
    simp [BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape,
      BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonTape,
      BuilderArbitrarySlotHeaderRouter.RawRouter.comparisonWord,
      BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary,
      List.replicate_succ] <;> rfl

/-- M209's exact comparator trace transports across the fresh boundary without
reading, writing, or crossing any preserved M213 cell. -/
theorem shielded_comparator_workRunExact (quotient count : Nat)
    (exterior : List WorkSymbol) :
    workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
        (shieldedComparatorStartConfiguration quotient count exterior) =
      some (shieldedComparatorFinalConfiguration quotient count exterior) := by
  have hCanonical :=
    BuilderArbitrarySlotHeaderRouter.RawRouter.workRunExact quotient count
  have hTransport := comparator_workRunExact_transport
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
    (workStartConfiguration comparatorMachine
      (BuilderArbitrarySlotHeaderRouter.RawRouter.inputTape quotient count))
    (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
      quotient count)
    exterior (comparator_input_boundary_protected quotient count) hCanonical
  simpa [shieldedComparatorStartConfiguration,
    shieldedComparatorFinalConfiguration, workStartConfiguration,
    appendExteriorConfiguration] using hTransport

theorem shieldedComparatorFinal_exterior_preserved
    (quotient count : Nat) (exterior : List WorkSymbol) :
    (shieldedComparatorFinalConfiguration quotient count exterior).tape.left =
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
        quotient count).tape.left ++ exterior := by
  rfl

theorem inputTape_eq_divider_terminal_with_exterior
    (consumed remainder width quotient : Nat)
    (exteriorPrefix : List WorkSymbol) (count : Nat)
    (workspace : List WorkSymbol) :
    inputTape consumed remainder width quotient exteriorPrefix count workspace =
      appendExteriorTape
        (BuilderPostHeaderRawDivider.terminalTape consumed remainder width
          quotient)
        (dividerExterior exteriorPrefix count workspace) := by
  have hBoundary :
      leftBoundary = BuilderPostHeaderRawDivider.leftBoundary := rfl
  have hQuotientMark :
      coordinateMark = BuilderPostHeaderRawDivider.quotientMark := rfl
  simp [inputTape, appendExteriorTape, terminalPrefix, dividerExterior,
    sidecar, BuilderPostHeaderRawDivider.terminalTape, List.append_assoc,
    hBoundary, hQuotientMark]

/-! ## Exact M213 branch geometry -/

def equalExteriorPrefix (processed width : Nat) : List WorkSymbol :=
  separatorSymbol ::
    (List.replicate width
        BuilderPostHeaderRawTapeBridge.copiedWidthMark ++
      endSymbol ::
        (List.replicate processed
            BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark ++
          separatorSymbol ::
            List.replicate processed coordinateMark))

def greaterExteriorPrefix (processed remainingCoordinate width : Nat) :
    List WorkSymbol :=
  separatorSymbol ::
    (List.replicate width
        BuilderPostHeaderRawTapeBridge.copiedWidthMark ++
      endSymbol ::
        (List.replicate processed
            BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark ++
          separatorSymbol ::
            (List.replicate remainingCoordinate
                BuilderPostHeaderRawTapeBridge.copiedRemainderMark ++
              List.replicate (processed + 1) coordinateMark)))

theorem equalExteriorPrefix_safe (processed width : Nat) :
    SafeExteriorPrefix (equalExteriorPrefix processed width) := by
  intro symbol hSymbol
  simp only [equalExteriorPrefix, List.mem_cons, List.mem_append,
    List.mem_replicate] at hSymbol
  rcases hSymbol with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  · rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))

theorem greaterExteriorPrefix_safe (processed remainingCoordinate width : Nat) :
    SafeExteriorPrefix
      (greaterExteriorPrefix processed remainingCoordinate width) := by
  intro symbol hSymbol
  simp only [greaterExteriorPrefix, List.mem_cons, List.mem_append,
    List.mem_replicate] at hSymbol
  rcases hSymbol with h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h.2)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
  · rcases h with h | h
    · exact Or.inl h
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h.2))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h.2))))

theorem equal_dividerExterior_eq_m213
    (processed width count : Nat) (workspace : List WorkSymbol) :
    dividerExterior (equalExteriorPrefix processed width) count workspace =
      BuilderPostHeaderRawTapeBridge.equalExterior processed width
        (sidecar count workspace) := by
  have hBoundary :
      leftBoundary =
        BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := rfl
  simp [dividerExterior, equalExteriorPrefix,
    BuilderPostHeaderRawTapeBridge.equalExterior,
    BuilderPostHeaderRawTapeBridge.copiedWidthMark,
    BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
    sidecar, List.append_assoc, hBoundary]

theorem greater_dividerExterior_eq_m213
    (processed remainingCoordinate width count : Nat)
    (workspace : List WorkSymbol) :
    dividerExterior
        (greaterExteriorPrefix processed remainingCoordinate width)
        count workspace =
      BuilderPostHeaderRawTapeBridge.greaterExterior processed
        remainingCoordinate width (sidecar count workspace) := by
  have hBoundary :
      leftBoundary =
        BuilderArbitrarySlotHeaderRouter.RawRouter.leftBoundary := rfl
  simp [dividerExterior, greaterExteriorPrefix,
    BuilderPostHeaderRawTapeBridge.greaterExterior,
    BuilderPostHeaderRawTapeBridge.copiedWidthMark,
    BuilderPostHeaderRawTapeBridge.copiedRemainderMark,
    sidecar, List.append_assoc, hBoundary]

theorem equal_input_tape_is_exact_m213_final
    (processed width count : Nat) (workspace : List WorkSymbol) :
    (inputConfiguration 0 0 width 0
      (equalExteriorPrefix processed width) count workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
        0 width
        (BuilderPostHeaderRawTapeBridge.equalExterior processed width
          (sidecar count workspace))).tape := by
  change inputTape 0 0 width 0 (equalExteriorPrefix processed width)
      count workspace = _
  rw [inputTape_eq_divider_terminal_with_exterior,
    equal_dividerExterior_eq_m213]
  simp [appendExteriorTape,
    BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorTape,
    BuilderPostHeaderRawDivider.finalConfiguration,
    BuilderPostHeaderRawDivider.terminalConfiguration]

theorem greater_input_tape_is_exact_m213_final
    (processed remainingCoordinate width count : Nat)
    (workspace : List WorkSymbol) :
    (inputConfiguration
      (((remainingCoordinate + 1) / width) * width)
      ((remainingCoordinate + 1) % width) width
      ((remainingCoordinate + 1) / width)
      (greaterExteriorPrefix processed remainingCoordinate width)
      count workspace).tape =
      (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
        (remainingCoordinate + 1) width
        (BuilderPostHeaderRawTapeBridge.greaterExterior processed
          remainingCoordinate width (sidecar count workspace))).tape := by
  change inputTape
      ((remainingCoordinate + 1) / width * width)
      ((remainingCoordinate + 1) % width) width
      ((remainingCoordinate + 1) / width)
      (greaterExteriorPrefix processed remainingCoordinate width)
      count workspace = _
  rw [inputTape_eq_divider_terminal_with_exterior,
    greater_dividerExterior_eq_m213]
  simp [appendExteriorTape,
    BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorConfiguration,
    BuilderPostHeaderRawTapeBridge.appendExteriorTape,
    BuilderPostHeaderRawDivider.finalConfiguration,
    BuilderPostHeaderRawDivider.terminalConfiguration]

/-! ## Physical branch and exact typed-route agreement -/

def LiteralClassifierHolds (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol) : Prop :=
  SafeExteriorPrefix exteriorPrefix ∧
    workRunExact? machine
        (workSteps consumed remainder width quotient count exteriorPrefix)
        (inputConfiguration consumed remainder width quotient exteriorPrefix
          count workspace) =
      some (comparatorInputConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)) ∧
    (comparatorInputConfiguration quotient count
      (preservedExterior consumed remainder width exteriorPrefix count
        workspace)).tape =
      (shieldedComparatorStartConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace)).tape ∧
    workRunExact? comparatorMachine
        (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
        (shieldedComparatorStartConfiguration quotient count
          (preservedExterior consumed remainder width exteriorPrefix count
            workspace)) =
      some (shieldedComparatorFinalConfiguration quotient count
        (preservedExterior consumed remainder width exteriorPrefix count
          workspace))

theorem literalClassifierHolds
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    LiteralClassifierHolds consumed remainder width quotient count
      exteriorPrefix workspace := by
  refine ⟨hPrefix,
    workRunExact consumed remainder width quotient count exteriorPrefix
      workspace hPrefix, ?_, ?_⟩
  · rfl
  · exact shielded_comparator_workRunExact quotient count
      (preservedExterior consumed remainder width exteriorPrefix count
        workspace)

def BranchPhysicalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult → Prop
  | .less _ _ => True
  | .equal processed =>
      LiteralClassifierHolds 0 0 problem.formulaTokensPerClause 0
        problem.formulaClauseSlotCount
        (equalExteriorPrefix processed problem.formulaTokensPerClause)
        workspace ∧
      (inputConfiguration 0 0 problem.formulaTokensPerClause 0
        (equalExteriorPrefix processed problem.formulaTokensPerClause)
        problem.formulaClauseSlotCount workspace).tape =
        (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
          0 problem.formulaTokensPerClause
          (BuilderPostHeaderRawTapeBridge.equalExterior processed
            problem.formulaTokensPerClause
            (sidecar problem.formulaClauseSlotCount workspace))).tape
  | .greater processed remainingCoordinate =>
      LiteralClassifierHolds
        (((remainingCoordinate + 1) / problem.formulaTokensPerClause) *
          problem.formulaTokensPerClause)
        ((remainingCoordinate + 1) % problem.formulaTokensPerClause)
        problem.formulaTokensPerClause
        ((remainingCoordinate + 1) / problem.formulaTokensPerClause)
        problem.formulaClauseSlotCount
        (greaterExteriorPrefix processed remainingCoordinate
          problem.formulaTokensPerClause) workspace ∧
      (inputConfiguration
        (((remainingCoordinate + 1) / problem.formulaTokensPerClause) *
          problem.formulaTokensPerClause)
        ((remainingCoordinate + 1) % problem.formulaTokensPerClause)
        problem.formulaTokensPerClause
        ((remainingCoordinate + 1) / problem.formulaTokensPerClause)
        (greaterExteriorPrefix processed remainingCoordinate
          problem.formulaTokensPerClause)
        problem.formulaClauseSlotCount workspace).tape =
        (BuilderPostHeaderRawTapeBridge.shieldedDividerFinalConfiguration
          (remainingCoordinate + 1) problem.formulaTokensPerClause
          (BuilderPostHeaderRawTapeBridge.greaterExterior processed
            remainingCoordinate problem.formulaTokensPerClause
            (sidecar problem.formulaClauseSlotCount workspace))).tape

theorem branchPhysicalHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol)
    (result : BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult) :
    BranchPhysicalHolds problem workspace result := by
  cases result with
  | less processed remainingBoundary => trivial
  | equal processed =>
      exact ⟨literalClassifierHolds 0 0 problem.formulaTokensPerClause 0
          problem.formulaClauseSlotCount
          (equalExteriorPrefix processed problem.formulaTokensPerClause)
          workspace
          (equalExteriorPrefix_safe processed
            problem.formulaTokensPerClause),
        equal_input_tape_is_exact_m213_final processed
          problem.formulaTokensPerClause problem.formulaClauseSlotCount
          workspace⟩
  | greater processed remainingCoordinate =>
      exact ⟨literalClassifierHolds
          (((remainingCoordinate + 1) / problem.formulaTokensPerClause) *
            problem.formulaTokensPerClause)
          ((remainingCoordinate + 1) % problem.formulaTokensPerClause)
          problem.formulaTokensPerClause
          ((remainingCoordinate + 1) / problem.formulaTokensPerClause)
          problem.formulaClauseSlotCount
          (greaterExteriorPrefix processed remainingCoordinate
            problem.formulaTokensPerClause) workspace
          (greaterExteriorPrefix_safe processed remainingCoordinate
            problem.formulaTokensPerClause),
        greater_input_tape_is_exact_m213_final processed remainingCoordinate
          problem.formulaTokensPerClause problem.formulaClauseSlotCount
          workspace⟩

theorem compareResult_self (processed count : Nat) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
        processed count count =
      .equal (processed + count) := by
  induction count generalizing processed with
  | zero => simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
  | succ count ih =>
      simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
        ih (processed + 1)]
      omega

def DecodedRouteHolds {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat) : Prop :=
  let width := problem.formulaTokensPerClause
  let quotient := index / width
  let remainder := index % width
  match postHeaderRoute problem index with
  | .body clauseCoordinate tokenCoordinate =>
      quotient = clauseCoordinate.val ∧
      remainder = tokenCoordinate.val ∧
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
        quotient problem.formulaClauseSlotCount).state =
          comparatorMachine.acceptState
  | .finish =>
      quotient = problem.formulaClauseSlotCount ∧
      remainder = 0 ∧
      BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 quotient
          problem.formulaClauseSlotCount =
        .equal problem.formulaClauseSlotCount ∧
      (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
        quotient problem.formulaClauseSlotCount).state =
          comparatorMachine.rejectState
  | .outOfRange => False

theorem decodedRouteHolds_of_not_outOfRange {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (hInRange : postHeaderRoute problem index ≠ .outOfRange) :
    DecodedRouteHolds problem index := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  cases hRoute : postHeaderRoute problem index with
  | body clauseCoordinate tokenCoordinate =>
      have hCoordinates :=
        BuilderPostHeaderRawDivider.final_quotient_remainder_eq_body_coordinates
          problem index clauseCoordinate tokenCoordinate hRoute
      rw [BuilderPostHeaderRawDivider.final_quotient_remainder] at hCoordinates
      have hQuotient :
          index / problem.formulaTokensPerClause = clauseCoordinate.val := by
        exact congrArg Prod.fst hCoordinates
      have hRemainder :
          index % problem.formulaTokensPerClause = tokenCoordinate.val := by
        exact congrArg Prod.snd hCoordinates
      have hAccept :=
        (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration_accept_iff
          (index / problem.formulaTokensPerClause)
          problem.formulaClauseSlotCount).2 (by
            rw [hQuotient]
            exact clauseCoordinate.isLt)
      simpa [DecodedRouteHolds, hRoute, hQuotient, hRemainder] using
        And.intro hQuotient (And.intro hRemainder hAccept)
  | finish =>
      have hIndex :=
        (postHeaderRoute_eq_finish_iff problem index).1 hRoute
      have hQuotient :
          index / problem.formulaTokensPerClause =
            problem.formulaClauseSlotCount := by
        rw [hIndex]
        simpa [Nat.mul_comm] using
          (Nat.mul_div_right problem.formulaClauseSlotCount hWidth)
      have hRemainder : index % problem.formulaTokensPerClause = 0 := by
        rw [hIndex]
        simp
      have hCompare := compareResult_self 0 problem.formulaClauseSlotCount
      have hReject :
          (BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration
            (index / problem.formulaTokensPerClause)
            problem.formulaClauseSlotCount).state =
              comparatorMachine.rejectState := by
        rw [hQuotient]
        simp [BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
          hCompare,
          BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration]
      simpa [DecodedRouteHolds, hRoute, hQuotient, hRemainder] using
        And.intro hQuotient
          (And.intro hRemainder (And.intro (by simpa [hQuotient] using hCompare)
            hReject))
  | outOfRange => exact False.elim (hInRange hRoute)

def InRangeRouteClassifierHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) : Prop :=
  let result := BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
    coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)
  match BuilderArbitrarySlotHeaderRouter.outerRoute problem coordinate.val with
  | .header _ =>
      BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
        result = none
  | .postHeader index =>
      BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
          result = some index ∧
        BuilderPostHeaderRawTapeBridge.ResultBridgeHolds problem
          (sidecar problem.formulaClauseSlotCount workspace) result ∧
        BranchPhysicalHolds problem workspace result ∧
        DecodedRouteHolds problem index ∧
        postHeaderRoute problem index ≠ .outOfRange

theorem inRangeRouteClassifierHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) :
    InRangeRouteClassifierHolds problem coordinate workspace := by
  let result := BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
    coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)
  have hM213 := BuilderPostHeaderRawTapeBridge.inRangeRouteBridgeHolds problem
    coordinate (sidecar problem.formulaClauseSlotCount workspace)
  have hPhysical := branchPhysicalHolds problem workspace result
  cases hOuter :
      BuilderArbitrarySlotHeaderRouter.outerRoute problem coordinate.val with
  | header headerCoordinate =>
      simpa [InRangeRouteClassifierHolds,
        BuilderPostHeaderRawTapeBridge.InRangeRouteBridgeHolds,
        result, hOuter] using hM213
  | postHeader index =>
      have hM213' :
          BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
              result = some index ∧
            BuilderPostHeaderRawTapeBridge.ResultBridgeHolds problem
              (sidecar problem.formulaClauseSlotCount workspace) result ∧
            BuilderPostHeaderRawLaunch.RouteDecodeHolds problem index ∧
            postHeaderRoute problem index ≠ .outOfRange := by
        simpa [BuilderPostHeaderRawTapeBridge.InRangeRouteBridgeHolds,
          result, hOuter] using hM213
      have hDecoded := decodedRouteHolds_of_not_outOfRange problem index
        hM213'.2.2.2
      simpa [InRangeRouteClassifierHolds, result, hOuter] using
        And.intro hM213'.1
          (And.intro hM213'.2.1
            (And.intro hPhysical (And.intro hDecoded hM213'.2.2.2)))

/-! ## Compiled traces and exact timeout boundary -/

theorem run_compile_exact (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    run (compileWorkMachine machine)
        (6 * workSteps consumed remainder width quotient count exteriorPrefix)
        (encodeWorkConfiguration
          (inputConfiguration consumed remainder width quotient exteriorPrefix
            count workspace)) =
      encodeWorkConfiguration
        (comparatorInputConfiguration quotient count
          (preservedExterior consumed remainder width exteriorPrefix count
            workspace)) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps consumed remainder width quotient count exteriorPrefix)
    (inputConfiguration consumed remainder width quotient exteriorPrefix count
      workspace)
    (comparatorInputConfiguration quotient count
      (preservedExterior consumed remainder width exteriorPrefix count
        workspace))
    (workRunExact consumed remainder width quotient count exteriorPrefix
      workspace hPrefix)

theorem run_compile_shielded_comparator_exact (quotient count : Nat)
    (exterior : List WorkSymbol) :
    run (compileWorkMachine comparatorMachine)
        (6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
        (encodeWorkConfiguration
          (shieldedComparatorStartConfiguration quotient count exterior)) =
      encodeWorkConfiguration
        (shieldedComparatorFinalConfiguration quotient count exterior) := by
  exact run_compileWorkMachine_mul_of_workRunExact comparatorMachine
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
    (shieldedComparatorStartConfiguration quotient count exterior)
    (shieldedComparatorFinalConfiguration quotient count exterior)
    (shielded_comparator_workRunExact quotient count exterior)

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
  | succ steps ih =>
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
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
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

private theorem one_step_short_not_halted_of_exact
    (selectedMachine : WorkMachine) (steps : Nat)
    (initial final : WorkConfiguration)
    (hPositive : 0 < steps)
    (hExact : workRunExact? selectedMachine steps initial = some final) :
    selectedMachine.isHalted
        (workRun selectedMachine (steps - 1) initial) = false := by
  let short := steps - 1
  have hSucc : short + 1 = steps := by
    dsimp [short]
    omega
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last selectedMachine short initial final
      hExact with ⟨before, hPrefix, hLast⟩
  have hRun : workRun selectedMachine short initial = before :=
    workRun_eq_of_workRunExact selectedMachine short initial before hPrefix
  rw [hRun]
  exact isHalted_false_of_workStep_some selectedMachine before final hLast

theorem workSteps_positive (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) :
    0 < workSteps consumed remainder width quotient count exteriorPrefix := by
  unfold workSteps setupSteps terminalLength
  omega

theorem one_step_short_not_halted
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix workspace : List WorkSymbol)
    (hPrefix : SafeExteriorPrefix exteriorPrefix) :
    machine.isHalted
        (workRun machine
          (workSteps consumed remainder width quotient count exteriorPrefix - 1)
          (inputConfiguration consumed remainder width quotient exteriorPrefix
            count workspace)) = false := by
  exact one_step_short_not_halted_of_exact machine
    (workSteps consumed remainder width quotient count exteriorPrefix)
    (inputConfiguration consumed remainder width quotient exteriorPrefix count
      workspace)
    (comparatorInputConfiguration quotient count
      (preservedExterior consumed remainder width exteriorPrefix count
        workspace))
    (workSteps_positive consumed remainder width quotient count exteriorPrefix)
    (workRunExact consumed remainder width quotient count exteriorPrefix
      workspace hPrefix)

private theorem comparator_workSteps_positive (quotient count : Nat)
    (exterior : List WorkSymbol) :
    0 < BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count := by
  cases hSteps :
      BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count with
  | zero =>
      have hExact := shielded_comparator_workRunExact quotient count exterior
      rw [hSteps] at hExact
      have hEqual :
          shieldedComparatorStartConfiguration quotient count exterior =
            shieldedComparatorFinalConfiguration quotient count exterior :=
        Option.some.inj hExact
      have hState := congrArg WorkConfiguration.state hEqual
      cases hResult :
          BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 quotient
            count <;>
        simp [shieldedComparatorStartConfiguration,
          shieldedComparatorFinalConfiguration, appendExteriorConfiguration,
          comparatorMachine,
          BuilderArbitrarySlotHeaderRouter.RawRouter.machine,
          BuilderArbitrarySlotHeaderRouter.RawRouter.finalConfiguration,
          BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
          hResult] at hState
  | succ steps => omega

theorem shielded_comparator_one_step_short_not_halted
    (quotient count : Nat) (exterior : List WorkSymbol) :
    comparatorMachine.isHalted
        (workRun comparatorMachine
          (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count -
            1)
          (shieldedComparatorStartConfiguration quotient count exterior)) =
      false := by
  exact one_step_short_not_halted_of_exact comparatorMachine
    (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count)
    (shieldedComparatorStartConfiguration quotient count exterior)
    (shieldedComparatorFinalConfiguration quotient count exterior)
    (comparator_workSteps_positive quotient count exterior)
    (shielded_comparator_workRunExact quotient count exterior)

/-! ## Explicit polynomial work bounds -/

def bridgeSize (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) : Nat :=
  terminalLength consumed remainder width + quotient + count +
    exteriorPrefix.length + 1

theorem bridgeSize_positive (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) :
    0 < bridgeSize consumed remainder width quotient count exteriorPrefix := by
  unfold bridgeSize
  omega

private theorem setupSteps_le_size
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) :
    setupSteps consumed remainder width quotient exteriorPrefix ≤
      7 * bridgeSize consumed remainder width quotient count exteriorPrefix := by
  unfold setupSteps bridgeSize
  omega

private theorem restoreSteps_le_size
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) :
    restoreSteps consumed remainder width count exteriorPrefix ≤
      13 * bridgeSize consumed remainder width quotient count exteriorPrefix := by
  unfold restoreSteps bridgeSize
  omega

private theorem copyCycleSteps_le_size
    (consumed remainder width quotient count copied : Nat)
    (exteriorPrefix : List WorkSymbol) (hCopied : copied ≤ count) :
    copyCycleSteps consumed remainder width quotient copied exteriorPrefix ≤
      13 * bridgeSize consumed remainder width quotient count exteriorPrefix := by
  unfold copyCycleSteps bridgeSize
  omega

private theorem copyAllSteps_le_size
    (consumed remainder width quotient count copied remaining : Nat)
    (exteriorPrefix : List WorkSymbol)
    (hCount : copied + remaining = count) :
    copyAllSteps consumed remainder width quotient count copied exteriorPrefix
        remaining ≤
      (remaining + 1) *
        (13 * bridgeSize consumed remainder width quotient count
          exteriorPrefix) := by
  induction remaining generalizing copied with
  | zero =>
      simpa [copyAllSteps] using restoreSteps_le_size consumed remainder width
        quotient count exteriorPrefix
  | succ remaining ih =>
      have hCopied : copied ≤ count := by omega
      have hCycle := copyCycleSteps_le_size consumed remainder width quotient
        count copied exteriorPrefix hCopied
      have hTail := ih (copied + 1) (by omega)
      have hAdd := Nat.add_le_add hCycle hTail
      calc
        copyAllSteps consumed remainder width quotient count copied
            exteriorPrefix (remaining + 1) =
            copyCycleSteps consumed remainder width quotient copied
                exteriorPrefix +
              copyAllSteps consumed remainder width quotient count
                (copied + 1) exteriorPrefix remaining := rfl
        _ ≤ 13 * bridgeSize consumed remainder width quotient count
              exteriorPrefix +
            (remaining + 1) *
              (13 * bridgeSize consumed remainder width quotient count
                exteriorPrefix) := hAdd
        _ = Nat.succ (remaining + 1) *
              (13 * bridgeSize consumed remainder width quotient count
                exteriorPrefix) := by
          rw [Nat.succ_mul (remaining + 1)
            (13 * bridgeSize consumed remainder width quotient count
              exteriorPrefix)]
          exact Nat.add_comm _ _

theorem workSteps_le_quadratic
    (consumed remainder width quotient count : Nat)
    (exteriorPrefix : List WorkSymbol) :
    workSteps consumed remainder width quotient count exteriorPrefix ≤
      20 * bridgeSize consumed remainder width quotient count exteriorPrefix *
        bridgeSize consumed remainder width quotient count exteriorPrefix := by
  let size := bridgeSize consumed remainder width quotient count exteriorPrefix
  have hSetup := setupSteps_le_size consumed remainder width quotient count
    exteriorPrefix
  have hCopy := copyAllSteps_le_size consumed remainder width quotient count 0
    count exteriorPrefix (by omega)
  have hCount : count + 1 ≤ size := by
    dsimp [size]
    unfold bridgeSize
    omega
  have hSize : 1 ≤ size := bridgeSize_positive consumed remainder width
    quotient count exteriorPrefix
  have hSetupSquare : 7 * size ≤ 7 * size * size := by
    have hScaled := Nat.mul_le_mul_left (7 * size) hSize
    simpa [Nat.mul_assoc] using hScaled
  have hCopySquare : (count + 1) * (13 * size) ≤ 13 * size * size := by
    calc
      (count + 1) * (13 * size) = 13 * size * (count + 1) := by
        simp [Nat.mul_comm]
      _ ≤ 13 * size * size := Nat.mul_le_mul_left (13 * size) hCount
  have hBoth := Nat.add_le_add
    (Nat.le_trans hSetup hSetupSquare)
    (Nat.le_trans hCopy hCopySquare)
  unfold workSteps
  calc
    setupSteps consumed remainder width quotient exteriorPrefix +
        copyAllSteps consumed remainder width quotient count 0 exteriorPrefix
          count ≤
      7 * size * size + 13 * size * size := hBoth
    _ = 20 * size * size := by
      rw [← Nat.add_mul, ← Nat.add_mul]

/-! ## Uniform source-size bound for the complete post-divider stage -/

def dividerWorkStepsForResult
    (width : Nat) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult → Nat
  | .less _ _ => 0
  | .equal _ => BuilderPostHeaderRawDivider.workSteps 0 width
  | .greater _ remainingCoordinate =>
      BuilderPostHeaderRawDivider.workSteps (remainingCoordinate + 1) width

def classifierWorkStepsForResult
    (width count : Nat) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult → Nat
  | .less _ _ => 0
  | .equal processed =>
      workSteps 0 0 width 0 count (equalExteriorPrefix processed width) +
        BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps 0 count
  | .greater processed remainingCoordinate =>
      workSteps
          (((remainingCoordinate + 1) / width) * width)
          ((remainingCoordinate + 1) % width) width
          ((remainingCoordinate + 1) / width) count
          (greaterExteriorPrefix processed remainingCoordinate width) +
        BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
          ((remainingCoordinate + 1) / width) count

def postDividerWorkStepsForResult
    (width count : Nat)
    (result : BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult) : Nat :=
  dividerWorkStepsForResult width result +
    classifierWorkStepsForResult width count result

private theorem scaled_square_mono (factor left right : Nat)
    (h : left ≤ right) :
    factor * left * left ≤ factor * right * right := by
  have hSquare := Nat.mul_le_mul h h
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left factor hSquare

private theorem scaled_square_coefficient_mono
    (leftFactor rightFactor size : Nat) (h : leftFactor ≤ rightFactor) :
    leftFactor * size * size ≤ rightFactor * size * size := by
  exact Nat.mul_le_mul_right size (Nat.mul_le_mul_right size h)

theorem dividerWorkSteps_compareResult_le
    (processed coordinate boundary width : Nat) (hWidth : 0 < width) :
    dividerWorkStepsForResult width
        (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
          processed coordinate boundary) ≤
      20 * (processed + coordinate + boundary + width + 1) *
        (processed + coordinate + boundary + width + 1) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary with
      | zero =>
          have hWork := BuilderPostHeaderRawDivider.workSteps_le_quadratic
            0 width hWidth
          let small := 0 + width + 1
          let large := processed + 0 + 0 + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 20 small large hSize
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            dividerWorkStepsForResult]
          exact Nat.le_trans (by simpa [small] using hWork)
            (by simpa [small, large] using hScaled)
      | succ boundary =>
          simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            dividerWorkStepsForResult]
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          have hWork := BuilderPostHeaderRawDivider.workSteps_le_quadratic
            (coordinate + 1) width hWidth
          let small := coordinate + 1 + width + 1
          let large := processed + (coordinate + 1) + 0 + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 20 small large hSize
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            dividerWorkStepsForResult]
          exact Nat.le_trans (by simpa [small] using hWork)
            (by simpa [large] using hScaled)
      | succ boundary =>
          have hTail := ih (processed + 1) boundary
          let small := processed + 1 + coordinate + boundary + width + 1
          let large :=
            processed + (coordinate + 1) + (boundary + 1) + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 20 small large hSize
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
          exact Nat.le_trans (by simpa [small] using hTail)
            (by simpa [large] using hScaled)

theorem classifierWorkSteps_compareResult_le
    (processed coordinate boundary width count : Nat)
    (hWidth : 0 < width) :
    classifierWorkStepsForResult width count
        (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
          processed coordinate boundary) ≤
      800 * (processed + coordinate + boundary + width + count + 1) *
        (processed + coordinate + boundary + width + count + 1) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary with
      | zero =>
          let size := processed + 0 + 0 + width + count + 1
          let bridge := bridgeSize 0 0 width 0 count
            (equalExteriorPrefix processed width)
          have hBridgeSize : bridge ≤ 4 * size := by
            dsimp [bridge, size]
            unfold bridgeSize terminalLength
            simp [equalExteriorPrefix]
            omega
          have hBridge := workSteps_le_quadratic 0 0 width 0 count
            (equalExteriorPrefix processed width)
          have hBridgeScaled := scaled_square_mono 20 bridge (4 * size)
            hBridgeSize
          have hBridgeFinal :
              workSteps 0 0 width 0 count
                  (equalExteriorPrefix processed width) ≤
                320 * size * size := by
            calc
              workSteps 0 0 width 0 count
                    (equalExteriorPrefix processed width) ≤
                  20 * bridge * bridge := by simpa [bridge] using hBridge
              _ ≤ 20 * (4 * size) * (4 * size) := hBridgeScaled
              _ = 320 * size * size := by
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          have hComparator :=
            BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps_le 0 count
          have hSizePositive : 1 ≤ size := by
            dsimp [size]
            omega
          have hComparatorScaled := scaled_square_mono 6 1 size hSizePositive
          have hComparatorFinal :
              BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps 0 count ≤
                6 * size * size := by
            exact Nat.le_trans (by simpa using hComparator)
              (by simpa using hComparatorScaled)
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            classifierWorkStepsForResult]
          calc
            workSteps 0 0 width 0 count
                  (equalExteriorPrefix processed width) +
                BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps 0 count ≤
              320 * size * size + 6 * size * size :=
                Nat.add_le_add hBridgeFinal hComparatorFinal
            _ = 326 * size * size := by
              rw [← Nat.add_mul, ← Nat.add_mul]
            _ ≤ 800 * size * size :=
              scaled_square_coefficient_mono 326 800 size (by omega)
            _ = 800 * (processed + 0 + 0 + width + count + 1) *
                (processed + 0 + 0 + width + count + 1) := by rfl
      | succ boundary =>
          simp [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            classifierWorkStepsForResult]
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          let dividend := coordinate + 1
          let quotient := dividend / width
          let remainder := dividend % width
          let size := processed + dividend + 0 + width + count + 1
          let bridge := bridgeSize (quotient * width) remainder width quotient
            count (greaterExteriorPrefix processed coordinate width)
          have hReconstruct :=
            BuilderPostHeaderRawDivider.quotient_remainder_reconstruct
              dividend width
          have hRemainder : remainder < width := by
            dsimp [remainder]
            exact Nat.mod_lt dividend hWidth
          have hQuotient : quotient ≤ dividend := by
            dsimp [quotient]
            exact Nat.div_le_self dividend width
          have hBridgeSize : bridge ≤ 6 * size := by
            dsimp [bridge, size, dividend, quotient, remainder] at *
            unfold bridgeSize terminalLength
            simp [greaterExteriorPrefix]
            omega
          have hBridge := workSteps_le_quadratic
            (quotient * width) remainder width quotient count
            (greaterExteriorPrefix processed coordinate width)
          have hBridgeScaled := scaled_square_mono 20 bridge (6 * size)
            hBridgeSize
          have hBridgeFinal :
              workSteps (quotient * width) remainder width quotient count
                  (greaterExteriorPrefix processed coordinate width) ≤
                720 * size * size := by
            calc
              workSteps (quotient * width) remainder width quotient count
                    (greaterExteriorPrefix processed coordinate width) ≤
                  20 * bridge * bridge := by simpa [bridge] using hBridge
              _ ≤ 20 * (6 * size) * (6 * size) := hBridgeScaled
              _ = 720 * size * size := by
                simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
          have hComparator :=
            BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps_le quotient
              count
          have hQuotientSize : quotient + 1 ≤ size := by
            dsimp [size]
            omega
          have hComparatorScaled := scaled_square_mono 6 (quotient + 1)
            size hQuotientSize
          have hComparatorFinal :
              BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient
                  count ≤ 6 * size * size :=
            Nat.le_trans hComparator hComparatorScaled
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult,
            classifierWorkStepsForResult]
          dsimp [dividend, quotient, remainder] at hBridgeFinal
          dsimp [dividend, quotient] at hComparatorFinal
          calc
            workSteps (((coordinate + 1) / width) * width)
                  ((coordinate + 1) % width) width
                  ((coordinate + 1) / width) count
                  (greaterExteriorPrefix processed coordinate width) +
                BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps
                  ((coordinate + 1) / width) count ≤
              720 * size * size + 6 * size * size :=
                Nat.add_le_add hBridgeFinal hComparatorFinal
            _ = 726 * size * size := by
              rw [← Nat.add_mul, ← Nat.add_mul]
            _ ≤ 800 * size * size :=
              scaled_square_coefficient_mono 726 800 size (by omega)
            _ = 800 *
                (processed + (coordinate + 1) + 0 + width + count + 1) *
                (processed + (coordinate + 1) + 0 + width + count + 1) := by
              rfl
      | succ boundary =>
          have hTail := ih (processed + 1) boundary
          let small := processed + 1 + coordinate + boundary + width + count + 1
          let large :=
            processed + (coordinate + 1) + (boundary + 1) + width + count + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 800 small large hSize
          simp only [BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
          exact Nat.le_trans (by simpa [small] using hTail)
            (by simpa [large] using hScaled)

theorem postDividerWorkSteps_compareResult_le
    (processed coordinate boundary width count : Nat)
    (hWidth : 0 < width) :
    postDividerWorkStepsForResult width count
        (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
          processed coordinate boundary) ≤
      1000 * (processed + coordinate + boundary + width + count + 1) *
        (processed + coordinate + boundary + width + count + 1) := by
  have hDivider := dividerWorkSteps_compareResult_le processed coordinate
    boundary width hWidth
  have hClassifier := classifierWorkSteps_compareResult_le processed
    coordinate boundary width count hWidth
  let size := processed + coordinate + boundary + width + count + 1
  let dividerSize := processed + coordinate + boundary + width + 1
  have hDividerSize : dividerSize ≤ size := by
    dsimp [dividerSize, size]
    omega
  have hDividerScaled := scaled_square_mono 20 dividerSize size hDividerSize
  have hDividerLarge :
      dividerWorkStepsForResult width
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
            processed coordinate boundary) ≤
        20 * size * size := by
    exact Nat.le_trans (by simpa [dividerSize] using hDivider) hDividerScaled
  have hClassifierLarge :
      classifierWorkStepsForResult width count
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
            processed coordinate boundary) ≤
        800 * size * size := by
    simpa [size] using hClassifier
  unfold postDividerWorkStepsForResult
  calc
    dividerWorkStepsForResult width
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
            processed coordinate boundary) +
        classifierWorkStepsForResult width count
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
            processed coordinate boundary) ≤
      20 * size * size + 800 * size * size :=
        Nat.add_le_add hDividerLarge hClassifierLarge
    _ = 820 * size * size := by
      rw [← Nat.add_mul, ← Nat.add_mul]
    _ ≤ 1000 * size * size :=
      scaled_square_coefficient_mono 820 1000 size (by omega)
    _ = 1000 *
        (processed + coordinate + boundary + width + count + 1) *
        (processed + coordinate + boundary + width + count + 1) := by rfl

def classifierSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (.mul (.constant 2)
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier))
    (.add (formulaClauseCountPolynomial verifier)
      (.add (formulaClauseTokenPolynomial verifier) (.constant 1)))

def stagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) : Nat :=
  BuilderPostHeaderRawTapeBridge.stagedCompiledSteps problem coordinate +
    6 * postDividerWorkStepsForResult problem.formulaTokensPerClause
      problem.formulaClauseSlotCount
      (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem))

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPostHeaderRawTapeBridge.rawTimeBound verifier)
    (.mul (.constant 6000)
      (.mul (classifierSizePolynomial verifier)
        (classifierSizePolynomial verifier)))

private theorem formulaClauseCountPolynomial_eval_eq_slotCount
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaClauseCountPolynomial problem.verifier).eval problem.input.length =
      problem.formulaClauseSlotCount := by
  have hCount := problem.formulaClauseCountPolynomial_eval
  simp only [BitString.size] at hCount
  simpa [VerifierTableauProblem.formulaClauseSlotCount,
    VerifierTableauProblem.formulaConstraintSlotCount,
    VerifierTableauProblem.formulaClauseSlotsPerConstraint,
    VerifierTableauProblem.formulaVariableSlotBound, BitString.size] using hCount

private theorem formulaClauseTokenPolynomial_eval_eq_tokensPerClause
    {language : Language} (problem : VerifierTableauProblem language) :
    (formulaClauseTokenPolynomial problem.verifier).eval problem.input.length =
      problem.formulaTokensPerClause := by
  have hTokens := problem.formulaClauseTokenPolynomial_eval
  simp only [BitString.size] at hTokens
  simpa [VerifierTableauProblem.formulaTokensPerClause,
    VerifierTableauProblem.formulaVariableSlotBound, BitString.size] using hTokens

theorem classifierSizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (classifierSizePolynomial problem.verifier).eval problem.input.length =
      2 * BuilderFullScheduleCursorController.terminalSlot problem +
        problem.formulaClauseSlotCount + problem.formulaTokensPerClause + 1 := by
  change
    2 * BuilderFullScheduleCursorController.terminalSlot problem +
        ((formulaClauseCountPolynomial problem.verifier).eval
          problem.input.length +
        ((formulaClauseTokenPolynomial problem.verifier).eval
          problem.input.length + 1)) = _
  rw [formulaClauseCountPolynomial_eval_eq_slotCount,
    formulaClauseTokenPolynomial_eval_eq_tokensPerClause]
  omega

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPostHeaderRawTapeBridge.rawTimeBound problem.verifier).eval
          problem.input.length +
        6000 *
          ((2 * BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaClauseSlotCount +
                problem.formulaTokensPerClause + 1) *
            (2 * BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaClauseSlotCount +
                problem.formulaTokensPerClause + 1)) := by
  change
    (BuilderPostHeaderRawTapeBridge.rawTimeBound problem.verifier).eval
        problem.input.length +
      6000 *
        ((classifierSizePolynomial problem.verifier).eval problem.input.length *
          (classifierSizePolynomial problem.verifier).eval
            problem.input.length) = _
  rw [classifierSizePolynomial_eval]

theorem stagedCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hBase :=
    BuilderPostHeaderRawTapeBridge.stagedCompiledSteps_le_rawTimeBound
      problem coordinate hCoordinate
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  have hFirstBody :
      BuilderFullScheduleCursorController.firstBodySlot problem ≤
        BuilderFullScheduleCursorController.terminalSlot problem := by
    rw [← BuilderFullScheduleCursorController.firstBodySlot_add_bodySlotCount
      problem]
    omega
  have hStage := postDividerWorkSteps_compareResult_le 0 coordinate
    (BuilderFullScheduleCursorController.firstBodySlot problem)
    problem.formulaTokensPerClause problem.formulaClauseSlotCount hWidth
  let small :=
    0 + coordinate +
      BuilderFullScheduleCursorController.firstBodySlot problem +
        problem.formulaTokensPerClause + problem.formulaClauseSlotCount + 1
  let large :=
    2 * BuilderFullScheduleCursorController.terminalSlot problem +
      problem.formulaClauseSlotCount + problem.formulaTokensPerClause + 1
  have hSize : small ≤ large := by
    dsimp [small, large]
    omega
  have hStageLarge :
      postDividerWorkStepsForResult problem.formulaTokensPerClause
          problem.formulaClauseSlotCount
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
        1000 * large * large :=
    Nat.le_trans (by simpa [small] using hStage)
      (scaled_square_mono 1000 small large hSize)
  have hCompiled := Nat.mul_le_mul_left 6 hStageLarge
  have hCompiled' :
      6 * postDividerWorkStepsForResult problem.formulaTokensPerClause
          problem.formulaClauseSlotCount
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
        6000 * (large * large) := by
    calc
      6 * postDividerWorkStepsForResult problem.formulaTokensPerClause
          problem.formulaClauseSlotCount
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
        6 * (1000 * large * large) := hCompiled
      _ = 6000 * (large * large) := by
        rw [Nat.mul_assoc 1000 large large,
          ← Nat.mul_assoc 6 1000 (large * large)]
  unfold stagedCompiledSteps
  rw [rawTimeBound_eval]
  exact Nat.add_le_add hBase (by simpa [large] using hCompiled')

/-! ## Certificate-free public endpoint -/

/-- M214 closes the literal all-coordinate post-divider route-classification
handoff.  It does not select or emit a token, iterate the schedule, construct
the complete formula, or package the Cook-Levin reduction. -/
theorem cook_levin_builder_post_divider_raw_route_classifier_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    rules.length = 180 ∧
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (∀ (workspace : List WorkSymbol) result,
      BranchPhysicalHolds problem workspace result) ∧
    (∀ (workspace : List WorkSymbol)
      (coordinate :
        Fin (BuilderFullScheduleCursorController.terminalSlot problem)),
      InRangeRouteClassifierHolds problem coordinate workspace) ∧
    (∀ consumed remainder width quotient count exteriorPrefix workspace,
      SafeExteriorPrefix exteriorPrefix →
        run (compileWorkMachine machine)
            (6 * workSteps consumed remainder width quotient count
              exteriorPrefix)
            (encodeWorkConfiguration
              (inputConfiguration consumed remainder width quotient
                exteriorPrefix count workspace)) =
          encodeWorkConfiguration
            (comparatorInputConfiguration quotient count
              (preservedExterior consumed remainder width exteriorPrefix count
                workspace)) ∧
        machine.isHalted
            (workRun machine
              (workSteps consumed remainder width quotient count
                exteriorPrefix - 1)
              (inputConfiguration consumed remainder width quotient
                exteriorPrefix count workspace)) = false) ∧
    (∀ quotient count exterior,
      run (compileWorkMachine comparatorMachine)
          (6 * BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient
            count)
          (encodeWorkConfiguration
            (shieldedComparatorStartConfiguration quotient count exterior)) =
        encodeWorkConfiguration
          (shieldedComparatorFinalConfiguration quotient count exterior) ∧
      comparatorMachine.isHalted
          (workRun comparatorMachine
            (BuilderArbitrarySlotHeaderRouter.RawRouter.workSteps quotient count -
              1)
            (shieldedComparatorStartConfiguration quotient count exterior)) =
        false) ∧
    (∀ coordinate,
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem →
        stagedCompiledSteps problem coordinate ≤
          (rawTimeBound problem.verifier).eval problem.input.length) := by
  refine ⟨rules_length, rules_pairwise_query_distinct,
    branchPhysicalHolds problem,
    (fun workspace coordinate =>
      inRangeRouteClassifierHolds problem coordinate workspace), ?_, ?_,
    stagedCompiledSteps_le_rawTimeBound problem⟩
  · intro consumed remainder width quotient count exteriorPrefix workspace
      hPrefix
    exact ⟨run_compile_exact consumed remainder width quotient count
      exteriorPrefix workspace hPrefix,
      one_step_short_not_halted consumed remainder width quotient count
        exteriorPrefix workspace hPrefix⟩
  · intro quotient count exterior
    exact ⟨run_compile_shielded_comparator_exact quotient count exterior,
      shielded_comparator_one_step_short_not_halted quotient count exterior⟩

end BuilderPostDividerRawRouteClassifier

end CookLevin

end PNP.Concrete
