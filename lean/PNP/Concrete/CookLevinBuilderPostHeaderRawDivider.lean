/-
Copyright (c) 2026 PNP Labs.

A fixed literal unary quotient/remainder machine for the Cook-Levin
post-header rectangle.  The machine repeatedly marks one divisor-width block
of the dividend, records one quotient unit, and restores the divisor.  When
the remaining dividend is shorter than the positive divisor it restores the
partial pass and accepts with an explicit consumed-prefix, remainder,
divisor, and quotient ledger.

This module is the standalone raw arithmetic kernel.  It does not splice the
machine onto the M209 result tape and does not emit a Cook-Levin body token.
-/

import PNP.Concrete.CookLevinBuilderArbitrarySlotPostHeaderDecoder

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPostHeaderRawDivider

open BuilderArbitrarySlotPostHeaderDecoder

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

abbrev unitSymbol : WorkSymbol := BuilderUnaryPolynomial.unitSymbol
abbrev separatorSymbol : WorkSymbol := BuilderUnaryPolynomial.separatorSymbol
abbrev endSymbol : WorkSymbol := BuilderUnaryPolynomial.scratchEndSymbol
def leftBoundary : WorkSymbol := PipelineTape.leftMarker
def matchedDividend : WorkSymbol := WorkSymbol.oneZero
def matchedDivisor : WorkSymbol := WorkSymbol.zeroBlank
def consumedDividend : WorkSymbol := WorkSymbol.oneBlank
def quotientMark : WorkSymbol := WorkSymbol.zeroZero

private def keepAction := BuilderUnaryPolynomial.keepAction
private def writeAction := BuilderUnaryPolynomial.writeAction
private def deadAction := BuilderUnaryPolynomial.deadAction

/-! ## Fixed literal program -/

private def scanDividendSpec : StateSpec := fun read =>
  if read = consumedDividend ∨ read = matchedDividend then
    keepAction 0 .right read
  else if read = unitSymbol then
    writeAction 1 matchedDividend .right
  else if read = separatorSymbol then
    keepAction 7 .left read
  else
    deadAction 10 read

private def seekSeparatorSpec : StateSpec := fun read =>
  if read = unitSymbol then
    keepAction 1 .right read
  else if read = separatorSymbol then
    keepAction 2 .right read
  else
    deadAction 10 read

private def scanDivisorSpec : StateSpec := fun read =>
  if read = matchedDivisor then
    keepAction 2 .right read
  else if read = unitSymbol then
    writeAction 3 matchedDivisor .right
  else
    deadAction 10 read

private def checkDivisorSpec : StateSpec := fun read =>
  if read = unitSymbol then
    keepAction 4 .left read
  else if read = endSymbol then
    keepAction 5 .right read
  else
    deadAction 10 read

private def rewindPairSpec : StateSpec := fun read =>
  if read = matchedDivisor ∨ read = separatorSymbol ∨ read = unitSymbol ∨
      read = matchedDividend ∨ read = consumedDividend then
    keepAction 4 .left read
  else if read = leftBoundary then
    keepAction 0 .right read
  else
    deadAction 10 read

private def seekQuotientBlankSpec : StateSpec := fun read =>
  if read = quotientMark then
    keepAction 5 .right read
  else if read = WorkSymbol.blank then
    writeAction 6 quotientMark .left
  else
    deadAction 10 read

private def cleanupFullSpec : StateSpec := fun read =>
  if read = matchedDivisor then
    writeAction 6 unitSymbol .left
  else if read = matchedDividend then
    writeAction 6 consumedDividend .left
  else if read = quotientMark ∨ read = endSymbol ∨
      read = separatorSymbol ∨ read = unitSymbol ∨
      read = consumedDividend then
    keepAction 6 .left read
  else if read = leftBoundary then
    keepAction 0 .right read
  else
    deadAction 10 read

private def restoreDividendSpec : StateSpec := fun read =>
  if read = matchedDividend then
    writeAction 7 unitSymbol .left
  else if read = consumedDividend then
    keepAction 7 .left read
  else if read = leftBoundary then
    keepAction 8 .right read
  else
    deadAction 10 read

private def seekTerminalSeparatorSpec : StateSpec := fun read =>
  if read = consumedDividend ∨ read = unitSymbol then
    keepAction 8 .right read
  else if read = separatorSymbol then
    keepAction 9 .right read
  else
    deadAction 10 read

private def restoreDivisorSpec : StateSpec := fun read =>
  if read = matchedDivisor then
    writeAction 9 unitSymbol .right
  else if read = unitSymbol then
    keepAction 9 .right read
  else if read = endSymbol then
    keepAction 11 .stay read
  else
    deadAction 10 read

private def deadSpec : StateSpec := fun read => deadAction 10 read

private def stateSpecs : List StateSpec :=
  [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
    checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
    cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec,
    restoreDivisorSpec, deadSpec]

def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

/-- A fixed 99-rule unary divider. State 11 accepts a decoded result, state 12
rejects, and state 10 is a nonhalting malformed-input sink. -/
def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 11
    rejectState := 12 }

theorem rules_length : rules.length = 99 := by
  rw [rules, BuilderUnaryPolynomial.rulesFrom_length]
  rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  exact BuilderUnaryPolynomial.rulesFrom_pairwise_query_distinct 0 stateSpecs

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by
  decide

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

@[simp] private theorem tape_write_head (tape : WorkTape) :
    tape.write tape.head = tape := by
  cases tape
  rfl

private theorem tape_write_eq_self (tape : WorkTape) (symbol : WorkSymbol)
    (hHead : tape.head = symbol) :
    tape.write symbol = tape := by
  rw [← hHead]
  exact tape_write_head tape

private theorem scanDividend_consumed_step (tape : WorkTape)
    (hHead : tape.head = consumedDividend) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step [] scanDividendSpec
    [seekSeparatorSpec, scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hWrite := tape_write_eq_self tape consumedDividend hHead
  simpa [machine_eq_specMachine, stateSpecs, scanDividendSpec, hHead, hWrite,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem scanDividend_matched_step (tape : WorkTape)
    (hHead : tape.head = matchedDividend) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step [] scanDividendSpec
    [seekSeparatorSpec, scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hWrite := tape_write_eq_self tape matchedDividend hHead
  simpa [machine_eq_specMachine, stateSpecs, scanDividendSpec, hHead, hWrite,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem scanDividend_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 0, tape := tape } =
      some
        { state := 1
          tape := (tape.write matchedDividend).moveRight } := by
  have hStep := specMachine_step [] scanDividendSpec
    [seekSeparatorSpec, scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hConsumed : unitSymbol ≠ consumedDividend := by decide
  have hMatched : unitSymbol ≠ matchedDividend := by decide
  simpa [machine_eq_specMachine, stateSpecs, scanDividendSpec, hHead,
    hConsumed, hMatched, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem scanDividend_separator_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 0, tape := tape } =
      some { state := 7, tape := tape.moveLeft } := by
  have hStep := specMachine_step [] scanDividendSpec
    [seekSeparatorSpec, scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hConsumed : separatorSymbol ≠ consumedDividend := by decide
  have hMatched : separatorSymbol ≠ matchedDividend := by decide
  have hUnit : separatorSymbol ≠ unitSymbol := by decide
  have hWrite := tape_write_eq_self tape separatorSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, scanDividendSpec, hHead, hWrite,
    hConsumed, hMatched, hUnit, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem seekSeparator_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 1, tape := tape.moveRight } := by
  have hStep := specMachine_step [scanDividendSpec] seekSeparatorSpec
    [scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hWrite := tape_write_eq_self tape unitSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, seekSeparatorSpec, hHead, hWrite,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem seekSeparator_separator_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 1, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step [scanDividendSpec] seekSeparatorSpec
    [scanDivisorSpec, checkDivisorSpec, rewindPairSpec,
      seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hUnit : separatorSymbol ≠ unitSymbol := by decide
  have hWrite := tape_write_eq_self tape separatorSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, seekSeparatorSpec, hHead, hWrite,
    hUnit, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem scanDivisor_matched_step (tape : WorkTape)
    (hHead : tape.head = matchedDivisor) :
    workStep? machine { state := 2, tape := tape } =
      some { state := 2, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec] scanDivisorSpec
    [checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec,
      restoreDivisorSpec, deadSpec] tape
  have hWrite := tape_write_eq_self tape matchedDivisor hHead
  simpa [machine_eq_specMachine, stateSpecs, scanDivisorSpec, hHead, hWrite,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem scanDivisor_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 2, tape := tape } =
      some
        { state := 3
          tape := (tape.write matchedDivisor).moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec] scanDivisorSpec
    [checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec,
      restoreDivisorSpec, deadSpec] tape
  have hMatched : unitSymbol ≠ matchedDivisor := by decide
  simpa [machine_eq_specMachine, stateSpecs, scanDivisorSpec, hHead,
    hMatched, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem checkDivisor_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 4, tape := tape.moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec]
    checkDivisorSpec
    [rewindPairSpec, seekQuotientBlankSpec, cleanupFullSpec,
      restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  have hWrite := tape_write_eq_self tape unitSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, checkDivisorSpec, hHead, hWrite,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem checkDivisor_end_step (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workStep? machine { state := 3, tape := tape } =
      some { state := 5, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec]
    checkDivisorSpec
    [rewindPairSpec, seekQuotientBlankSpec, cleanupFullSpec,
      restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  have hUnit : endSymbol ≠ unitSymbol := by decide
  have hWrite := tape_write_eq_self tape endSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, checkDivisorSpec, hHead, hWrite,
    hUnit, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem rewindPair_keep_step (tape : WorkTape)
    (hHead : tape.head = matchedDivisor ∨ tape.head = separatorSymbol ∨
      tape.head = unitSymbol ∨ tape.head = matchedDividend ∨
      tape.head = consumedDividend) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 4, tape := tape.moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec] rewindPairSpec
    [seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, rewindPairSpec, hHead,
    keepAction, BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem rewindPair_boundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 4, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec] rewindPairSpec
    [seekQuotientBlankSpec, cleanupFullSpec, restoreDividendSpec,
      seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hMatchedDivisor : leftBoundary ≠ matchedDivisor := by decide
  have hSeparator : leftBoundary ≠ separatorSymbol := by decide
  have hUnit : leftBoundary ≠ unitSymbol := by decide
  have hMatchedDividend : leftBoundary ≠ matchedDividend := by decide
  have hConsumed : leftBoundary ≠ consumedDividend := by decide
  have hWrite := tape_write_eq_self tape leftBoundary hHead
  simpa [machine_eq_specMachine, stateSpecs, rewindPairSpec, hHead, hWrite,
    hMatchedDivisor, hSeparator, hUnit, hMatchedDividend, hConsumed,
    keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem seekQuotient_mark_step (tape : WorkTape)
    (hHead : tape.head = quotientMark) :
    workStep? machine { state := 5, tape := tape } =
      some { state := 5, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec] seekQuotientBlankSpec
    [cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec,
      restoreDivisorSpec, deadSpec] tape
  have hWrite := tape_write_eq_self tape quotientMark hHead
  simpa [machine_eq_specMachine, stateSpecs, seekQuotientBlankSpec, hWrite,
    hHead, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem seekQuotient_blank_step (tape : WorkTape)
    (hHead : tape.head = WorkSymbol.blank) :
    workStep? machine { state := 5, tape := tape } =
      some
        { state := 6
          tape := (tape.write quotientMark).moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec] seekQuotientBlankSpec
    [cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec,
      restoreDivisorSpec, deadSpec] tape
  have hQuotient : WorkSymbol.blank ≠ quotientMark := by decide
  simpa [machine_eq_specMachine, stateSpecs, seekQuotientBlankSpec,
    hHead, hQuotient, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem cleanupFull_matchedDivisor_step (tape : WorkTape)
    (hHead : tape.head = matchedDivisor) :
    workStep? machine { state := 6, tape := tape } =
      some
        { state := 6
          tape := (tape.write unitSymbol).moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec]
    cleanupFullSpec
    [restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, cleanupFullSpec, hHead,
    writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem cleanupFull_matchedDividend_step (tape : WorkTape)
    (hHead : tape.head = matchedDividend) :
    workStep? machine { state := 6, tape := tape } =
      some
        { state := 6
          tape := (tape.write consumedDividend).moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec]
    cleanupFullSpec
    [restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  have hDivisor : matchedDividend ≠ matchedDivisor := by decide
  simpa [machine_eq_specMachine, stateSpecs, cleanupFullSpec, hHead,
    hDivisor, writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem cleanupFull_keep_step (tape : WorkTape)
    (hHead : tape.head = quotientMark ∨ tape.head = endSymbol ∨
      tape.head = separatorSymbol ∨ tape.head = unitSymbol ∨
      tape.head = consumedDividend) :
    workStep? machine { state := 6, tape := tape } =
      some { state := 6, tape := tape.moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec]
    cleanupFullSpec
    [restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  have hNotDivisor : tape.head ≠ matchedDivisor := by
    rcases hHead with h | h | h | h | h <;> rw [h] <;> decide
  have hNotDividend : tape.head ≠ matchedDividend := by
    rcases hHead with h | h | h | h | h <;> rw [h] <;> decide
  simpa [machine_eq_specMachine, stateSpecs, cleanupFullSpec, hHead,
    hNotDivisor, hNotDividend, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem cleanupFull_boundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 6, tape := tape } =
      some { state := 0, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec]
    cleanupFullSpec
    [restoreDividendSpec, seekTerminalSeparatorSpec, restoreDivisorSpec,
      deadSpec] tape
  have hNotDivisor : leftBoundary ≠ matchedDivisor := by decide
  have hNotDividend : leftBoundary ≠ matchedDividend := by decide
  have hNotQuotient : leftBoundary ≠ quotientMark := by decide
  have hNotEnd : leftBoundary ≠ endSymbol := by decide
  have hNotSeparator : leftBoundary ≠ separatorSymbol := by decide
  have hNotUnit : leftBoundary ≠ unitSymbol := by decide
  have hNotConsumed : leftBoundary ≠ consumedDividend := by decide
  have hWrite := tape_write_eq_self tape leftBoundary hHead
  simpa [machine_eq_specMachine, stateSpecs, cleanupFullSpec, hHead, hWrite,
    hNotDivisor, hNotDividend, hNotQuotient, hNotEnd, hNotSeparator,
    hNotUnit, hNotConsumed, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem restoreDividend_matched_step (tape : WorkTape)
    (hHead : tape.head = matchedDividend) :
    workStep? machine { state := 7, tape := tape } =
      some
        { state := 7
          tape := (tape.write unitSymbol).moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec] restoreDividendSpec
    [seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, restoreDividendSpec, hHead,
    writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem restoreDividend_consumed_step (tape : WorkTape)
    (hHead : tape.head = consumedDividend) :
    workStep? machine { state := 7, tape := tape } =
      some { state := 7, tape := tape.moveLeft } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec] restoreDividendSpec
    [seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hMatched : consumedDividend ≠ matchedDividend := by decide
  have hWrite := tape_write_eq_self tape consumedDividend hHead
  simpa [machine_eq_specMachine, stateSpecs, restoreDividendSpec, hHead, hWrite,
    hMatched, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem restoreDividend_boundary_step (tape : WorkTape)
    (hHead : tape.head = leftBoundary) :
    workStep? machine { state := 7, tape := tape } =
      some { state := 8, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec] restoreDividendSpec
    [seekTerminalSeparatorSpec, restoreDivisorSpec, deadSpec] tape
  have hMatched : leftBoundary ≠ matchedDividend := by decide
  have hConsumed : leftBoundary ≠ consumedDividend := by decide
  have hWrite := tape_write_eq_self tape leftBoundary hHead
  simpa [machine_eq_specMachine, stateSpecs, restoreDividendSpec, hHead, hWrite,
    hMatched, hConsumed, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem seekTerminal_keep_step (tape : WorkTape)
    (hHead : tape.head = consumedDividend ∨ tape.head = unitSymbol) :
    workStep? machine { state := 8, tape := tape } =
      some { state := 8, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec] seekTerminalSeparatorSpec
    [restoreDivisorSpec, deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, seekTerminalSeparatorSpec,
    hHead, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem seekTerminal_separator_step (tape : WorkTape)
    (hHead : tape.head = separatorSymbol) :
    workStep? machine { state := 8, tape := tape } =
      some { state := 9, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec] seekTerminalSeparatorSpec
    [restoreDivisorSpec, deadSpec] tape
  have hConsumed : separatorSymbol ≠ consumedDividend := by decide
  have hUnit : separatorSymbol ≠ unitSymbol := by decide
  have hWrite := tape_write_eq_self tape separatorSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, seekTerminalSeparatorSpec, hWrite,
    hHead, hConsumed, hUnit, keepAction,
    BuilderUnaryPolynomial.keepAction, WorkTape.move] using hStep

private theorem restoreDivisor_matched_step (tape : WorkTape)
    (hHead : tape.head = matchedDivisor) :
    workStep? machine { state := 9, tape := tape } =
      some
        { state := 9
          tape := (tape.write unitSymbol).moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec]
    restoreDivisorSpec [deadSpec] tape
  simpa [machine_eq_specMachine, stateSpecs, restoreDivisorSpec, hHead,
    writeAction, BuilderUnaryPolynomial.writeAction,
    WorkTape.move] using hStep

private theorem restoreDivisor_unit_step (tape : WorkTape)
    (hHead : tape.head = unitSymbol) :
    workStep? machine { state := 9, tape := tape } =
      some { state := 9, tape := tape.moveRight } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec]
    restoreDivisorSpec [deadSpec] tape
  have hMatched : unitSymbol ≠ matchedDivisor := by decide
  have hWrite := tape_write_eq_self tape unitSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, restoreDivisorSpec, hHead, hWrite,
    hMatched, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

private theorem restoreDivisor_end_step (tape : WorkTape)
    (hHead : tape.head = endSymbol) :
    workStep? machine { state := 9, tape := tape } =
      some { state := 11, tape := tape } := by
  have hStep := specMachine_step
    [scanDividendSpec, seekSeparatorSpec, scanDivisorSpec,
      checkDivisorSpec, rewindPairSpec, seekQuotientBlankSpec,
      cleanupFullSpec, restoreDividendSpec, seekTerminalSeparatorSpec]
    restoreDivisorSpec [deadSpec] tape
  have hMatched : endSymbol ≠ matchedDivisor := by decide
  have hUnit : endSymbol ≠ unitSymbol := by decide
  have hWrite := tape_write_eq_self tape endSymbol hHead
  simpa [machine_eq_specMachine, stateSpecs, restoreDivisorSpec, hHead, hWrite,
    hMatched, hUnit, keepAction, BuilderUnaryPolynomial.keepAction,
    WorkTape.move] using hStep

/-! ## Canonical layouts -/

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

@[simp] private theorem rightPathTape_moveLeft_cons_left
    (leftHead : WorkSymbol) (leftTail : List WorkSymbol)
    (head : WorkSymbol) (right : List WorkSymbol) :
    (rightPathTape (leftHead :: leftTail) (head :: right)).moveLeft =
      leftPathTape (head :: right) (leftHead :: leftTail) := by
  rfl

private theorem rightPathTape_moveLeft_nonempty
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (right : List WorkSymbol) (hLeft : leftSide ≠ []) :
    (rightPathTape leftSide (head :: right)).moveLeft =
      leftPathTape (head :: right) leftSide := by
  cases leftSide with
  | nil => exact False.elim (hLeft rfl)
  | cons first rest => rfl


private theorem rightPathTape_empty_write_moveLeft_nonempty
    (leftSide : List WorkSymbol) (write : WorkSymbol)
    (hLeft : leftSide ≠ []) :
    ((rightPathTape leftSide []).write write).moveLeft =
      leftPathTape [write] leftSide := by
  cases leftSide with
  | nil => exact False.elim (hLeft rfl)
  | cons first rest => rfl

@[simp] private theorem leftPathTape_moveLeft_cons
    (rightSide : List WorkSymbol) (head : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).moveLeft =
      leftPathTape (head :: rightSide) left := by
  cases left <;> rfl

@[simp] private theorem leftPathTape_write_cons
    (rightSide : List WorkSymbol) (head write : WorkSymbol)
    (left : List WorkSymbol) :
    (leftPathTape rightSide (head :: left)).write write =
      leftPathTape rightSide (write :: left) := by
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

private theorem replicate_add (first second : Nat) (item : α) :
    List.replicate (first + second) item =
      List.replicate first item ++ List.replicate second item := by
  induction first with
  | zero => simp
  | succ first ih =>
      simp only [Nat.succ_add, List.replicate_succ, ih, List.cons_append]

private theorem scanRightExact (state : Nat)
    (read write : WorkSymbol) (count : Nat)
    (leftSide rightTail : List WorkSymbol)
    (hStep : ∀ tape : WorkTape, tape.head = read →
      workStep? machine { state := state, tape := tape } =
        some
          { state := state
            tape := (tape.write write).moveRight }) :
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
      have hOne := workRunExact_one
        { state := state
          tape := rightPathTape leftSide
            (read :: (List.replicate count read ++ rightTail)) }
        { state := state
          tape := rightPathTape (write :: leftSide)
            (List.replicate count read ++ rightTail) } (by
          simpa using hStep
            (rightPathTape leftSide
              (read :: (List.replicate count read ++ rightTail))) rfl)
      have hTail := ih (write :: leftSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count
        { state := state
          tape := rightPathTape leftSide
            (read :: (List.replicate count read ++ rightTail)) }
        { state := state
          tape := rightPathTape (write :: leftSide)
            (List.replicate count read ++ rightTail) }
        { state := state
          tape := rightPathTape
            (List.replicate count write ++ write :: leftSide) rightTail }
        hOne hTail
      simpa [List.replicate_succ, replicate_append_self_cons, Nat.add_comm]
        using hAll

private theorem scanLeftExact (state : Nat)
    (read write : WorkSymbol) (count : Nat)
    (rightSide leftTail : List WorkSymbol)
    (hStep : ∀ tape : WorkTape, tape.head = read →
      workStep? machine { state := state, tape := tape } =
        some
          { state := state
            tape := (tape.write write).moveLeft }) :
    workRunExact? machine count
        { state := state
          tape := leftPathTape rightSide
            (List.replicate count read ++ leftTail) } =
      some
        { state := state
          tape := leftPathTape
            (List.replicate count write ++ rightSide) leftTail } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      have hOne := workRunExact_one
        { state := state
          tape := leftPathTape rightSide
            (read :: (List.replicate count read ++ leftTail)) }
        { state := state
          tape := leftPathTape (write :: rightSide)
            (List.replicate count read ++ leftTail) } (by
          simpa using hStep
            (leftPathTape rightSide
              (read :: (List.replicate count read ++ leftTail))) rfl)
      have hTail := ih (write :: rightSide)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 count
        { state := state
          tape := leftPathTape rightSide
            (read :: (List.replicate count read ++ leftTail)) }
        { state := state
          tape := leftPathTape (write :: rightSide)
            (List.replicate count read ++ leftTail) }
        { state := state
          tape := leftPathTape
            (List.replicate count write ++ write :: rightSide) leftTail }
        hOne hTail
      simpa [List.replicate_succ, replicate_append_self_cons, Nat.add_comm]
        using hAll

private theorem rewindPair_exact (symbols rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol ∈ symbols,
      symbol = matchedDivisor ∨ symbol = separatorSymbol ∨
      symbol = unitSymbol ∨ symbol = matchedDividend ∨
      symbol = consumedDividend) :
    workRunExact? machine (symbols.length + 1)
        { state := 4
          tape := leftPathTape rightSide (symbols ++ [leftBoundary]) } =
      some
        { state := 0
          tape := rightPathTape [leftBoundary]
            (symbols.reverse ++ rightSide) } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hOne := workRunExact_one
        { state := 4, tape := leftPathTape rightSide [leftBoundary] }
        { state := 0, tape := rightPathTape [leftBoundary] rightSide } (by
          apply rewindPair_boundary_step
          rfl)
      simpa using hOne
  | cons symbol rest ih =>
      have hSymbol := hAllowed symbol (by simp)
      have hRest : ∀ item ∈ rest,
          item = matchedDivisor ∨ item = separatorSymbol ∨
          item = unitSymbol ∨ item = matchedDividend ∨
          item = consumedDividend := by
        intro item hItem
        exact hAllowed item (by simp [hItem])
      have hOne := workRunExact_one
        { state := 4
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 4
          tape := leftPathTape (symbol :: rightSide)
            (rest ++ [leftBoundary]) } (by
          apply rewindPair_keep_step
          change symbol = matchedDivisor ∨ symbol = separatorSymbol ∨
            symbol = unitSymbol ∨ symbol = matchedDividend ∨
            symbol = consumedDividend
          exact hSymbol)
      have hTail := ih (symbol :: rightSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 (rest.length + 1)
        { state := 4
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 4
          tape := leftPathTape (symbol :: rightSide)
            (rest ++ [leftBoundary]) }
        { state := 0
          tape := rightPathTape [leftBoundary]
            (rest.reverse ++ symbol :: rightSide) }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hAll

private def cleanupFullWrite (symbol : WorkSymbol) : WorkSymbol :=
  if symbol = matchedDivisor then unitSymbol
  else if symbol = matchedDividend then consumedDividend
  else symbol

@[simp] private theorem cleanupFullWrite_matchedDivisor :
    cleanupFullWrite matchedDivisor = unitSymbol := by
  decide

@[simp] private theorem cleanupFullWrite_matchedDividend :
    cleanupFullWrite matchedDividend = consumedDividend := by
  decide

@[simp] private theorem cleanupFullWrite_quotient :
    cleanupFullWrite quotientMark = quotientMark := by
  decide

@[simp] private theorem cleanupFullWrite_end :
    cleanupFullWrite endSymbol = endSymbol := by
  decide

@[simp] private theorem cleanupFullWrite_separator :
    cleanupFullWrite separatorSymbol = separatorSymbol := by
  decide

@[simp] private theorem cleanupFullWrite_unit :
    cleanupFullWrite unitSymbol = unitSymbol := by
  decide

@[simp] private theorem cleanupFullWrite_consumed :
    cleanupFullWrite consumedDividend = consumedDividend := by
  decide

private theorem cleanupFull_symbol_step (tape : WorkTape)
    (hAllowed : tape.head = matchedDivisor ∨
      tape.head = matchedDividend ∨ tape.head = quotientMark ∨
      tape.head = endSymbol ∨ tape.head = separatorSymbol ∨
      tape.head = unitSymbol ∨ tape.head = consumedDividend) :
    workStep? machine { state := 6, tape := tape } =
      some
        { state := 6
          tape := (tape.write (cleanupFullWrite tape.head)).moveLeft } := by
  rcases hAllowed with h | h | h | h | h | h | h
  · simpa [cleanupFullWrite, h] using
      cleanupFull_matchedDivisor_step tape h
  · have hNe : matchedDividend ≠ matchedDivisor := by decide
    simpa [cleanupFullWrite, h, hNe] using
      cleanupFull_matchedDividend_step tape h
  · have hDivisor : quotientMark ≠ matchedDivisor := by decide
    have hDividend : quotientMark ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape quotientMark h
    simpa [cleanupFullWrite, h, hDivisor, hDividend, hWrite] using
      cleanupFull_keep_step tape (Or.inl h)
  · have hDivisor : endSymbol ≠ matchedDivisor := by decide
    have hDividend : endSymbol ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape endSymbol h
    simpa [cleanupFullWrite, h, hDivisor, hDividend, hWrite] using
      cleanupFull_keep_step tape (Or.inr (Or.inl h))
  · have hDivisor : separatorSymbol ≠ matchedDivisor := by decide
    have hDividend : separatorSymbol ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape separatorSymbol h
    simpa [cleanupFullWrite, h, hDivisor, hDividend, hWrite] using
      cleanupFull_keep_step tape (Or.inr (Or.inr (Or.inl h)))
  · have hDivisor : unitSymbol ≠ matchedDivisor := by decide
    have hDividend : unitSymbol ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape unitSymbol h
    simpa [cleanupFullWrite, h, hDivisor, hDividend, hWrite] using
      cleanupFull_keep_step tape
        (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · have hDivisor : consumedDividend ≠ matchedDivisor := by decide
    have hDividend : consumedDividend ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape consumedDividend h
    simpa [cleanupFullWrite, h, hDivisor, hDividend, hWrite] using
      cleanupFull_keep_step tape
        (Or.inr (Or.inr (Or.inr (Or.inr h))))

private theorem cleanupFull_exact (symbols rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol ∈ symbols,
      symbol = matchedDivisor ∨ symbol = matchedDividend ∨
      symbol = quotientMark ∨ symbol = endSymbol ∨
      symbol = separatorSymbol ∨ symbol = unitSymbol ∨
      symbol = consumedDividend) :
    workRunExact? machine (symbols.length + 1)
        { state := 6
          tape := leftPathTape rightSide (symbols ++ [leftBoundary]) } =
      some
        { state := 0
          tape := rightPathTape [leftBoundary]
            ((symbols.map cleanupFullWrite).reverse ++ rightSide) } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hOne := workRunExact_one
        { state := 6, tape := leftPathTape rightSide [leftBoundary] }
        { state := 0, tape := rightPathTape [leftBoundary] rightSide } (by
          apply cleanupFull_boundary_step
          rfl)
      simpa using hOne
  | cons symbol rest ih =>
      have hSymbol := hAllowed symbol (by simp)
      have hRest : ∀ item ∈ rest,
          item = matchedDivisor ∨ item = matchedDividend ∨
          item = quotientMark ∨ item = endSymbol ∨
          item = separatorSymbol ∨ item = unitSymbol ∨
          item = consumedDividend := by
        intro item hItem
        exact hAllowed item (by simp [hItem])
      have hOne := workRunExact_one
        { state := 6
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 6
          tape := leftPathTape (cleanupFullWrite symbol :: rightSide)
            (rest ++ [leftBoundary]) } (by
          apply cleanupFull_symbol_step
          change symbol = matchedDivisor ∨ symbol = matchedDividend ∨
            symbol = quotientMark ∨ symbol = endSymbol ∨
            symbol = separatorSymbol ∨ symbol = unitSymbol ∨
            symbol = consumedDividend
          exact hSymbol)
      have hTail := ih (cleanupFullWrite symbol :: rightSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 (rest.length + 1)
        { state := 6
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 6
          tape := leftPathTape (cleanupFullWrite symbol :: rightSide)
            (rest ++ [leftBoundary]) }
        { state := 0
          tape := rightPathTape [leftBoundary]
            ((rest.map cleanupFullWrite).reverse ++
              cleanupFullWrite symbol :: rightSide) }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hAll

private def restoreDividendWrite (symbol : WorkSymbol) : WorkSymbol :=
  if symbol = matchedDividend then unitSymbol else symbol

@[simp] private theorem restoreDividendWrite_matched :
    restoreDividendWrite matchedDividend = unitSymbol := by
  decide

@[simp] private theorem restoreDividendWrite_consumed :
    restoreDividendWrite consumedDividend = consumedDividend := by
  decide


private theorem restoreDividend_symbol_step (tape : WorkTape)
    (hAllowed : tape.head = matchedDividend ∨
      tape.head = consumedDividend) :
    workStep? machine { state := 7, tape := tape } =
      some
        { state := 7
          tape := (tape.write (restoreDividendWrite tape.head)).moveLeft } := by
  rcases hAllowed with h | h
  · simpa [restoreDividendWrite, h] using
      restoreDividend_matched_step tape h
  · have hNe : consumedDividend ≠ matchedDividend := by decide
    have hWrite := tape_write_eq_self tape consumedDividend h
    simpa [restoreDividendWrite, h, hNe, hWrite] using
      restoreDividend_consumed_step tape h

private theorem restoreDividend_exact (symbols rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol ∈ symbols,
      symbol = matchedDividend ∨ symbol = consumedDividend) :
    workRunExact? machine (symbols.length + 1)
        { state := 7
          tape := leftPathTape rightSide (symbols ++ [leftBoundary]) } =
      some
        { state := 8
          tape := rightPathTape [leftBoundary]
            ((symbols.map restoreDividendWrite).reverse ++ rightSide) } := by
  induction symbols generalizing rightSide with
  | nil =>
      have hOne := workRunExact_one
        { state := 7, tape := leftPathTape rightSide [leftBoundary] }
        { state := 8, tape := rightPathTape [leftBoundary] rightSide } (by
          apply restoreDividend_boundary_step
          rfl)
      simpa using hOne
  | cons symbol rest ih =>
      have hSymbol := hAllowed symbol (by simp)
      have hRest : ∀ item ∈ rest,
          item = matchedDividend ∨ item = consumedDividend := by
        intro item hItem
        exact hAllowed item (by simp [hItem])
      have hOne := workRunExact_one
        { state := 7
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 7
          tape := leftPathTape (restoreDividendWrite symbol :: rightSide)
            (rest ++ [leftBoundary]) } (by
          apply restoreDividend_symbol_step
          change symbol = matchedDividend ∨ symbol = consumedDividend
          exact hSymbol)
      have hTail := ih (restoreDividendWrite symbol :: rightSide) hRest
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        1 (rest.length + 1)
        { state := 7
          tape := leftPathTape rightSide
            (symbol :: (rest ++ [leftBoundary])) }
        { state := 7
          tape := leftPathTape (restoreDividendWrite symbol :: rightSide)
            (rest ++ [leftBoundary]) }
        { state := 8
          tape := rightPathTape [leftBoundary]
            ((rest.map restoreDividendWrite).reverse ++
              restoreDividendWrite symbol :: rightSide) }
        hOne hTail
      simpa [List.reverse_cons, List.append_assoc, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using hAll

/-- A division phase after `consumed` dividend units have been retired,
`matched` units have been paired in the current pass, and `remaining` units
remain unpaired. The divisor carries the same matched prefix. -/
def phaseWord (consumed matched remaining matchedWidth remainingWidth
    quotient : Nat) : List WorkSymbol :=
  List.replicate consumed consumedDividend ++
    List.replicate matched matchedDividend ++
    List.replicate remaining unitSymbol ++
    separatorSymbol ::
      (List.replicate matchedWidth matchedDivisor ++
        List.replicate remainingWidth unitSymbol ++
        endSymbol :: List.replicate quotient quotientMark)

def phaseTape (consumed matched remaining matchedWidth remainingWidth
    quotient : Nat) : WorkTape :=
  rightPathTape [leftBoundary]
    (phaseWord consumed matched remaining matchedWidth remainingWidth quotient)

def phaseConfiguration (consumed matched remaining matchedWidth remainingWidth
    quotient : Nat) : WorkConfiguration :=
  { state := 0
    tape := phaseTape consumed matched remaining matchedWidth remainingWidth
      quotient }

def loopConfiguration (consumed remaining width quotient : Nat) :
    WorkConfiguration :=
  phaseConfiguration consumed 0 remaining 0 width quotient

def inputTape (dividend width : Nat) : WorkTape :=
  phaseTape 0 0 dividend 0 width 0

/-- Public tape-shape view used by later literal bridge modules without
exposing the divider's internal path helper. -/
def inputWordTape (word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := [leftBoundary], head := WorkSymbol.blank, right := [] }
  | head :: right => { left := [leftBoundary], head := head, right := right }

theorem inputTape_eq_inputWordTape (dividend width : Nat) :
    inputTape dividend width =
      inputWordTape (phaseWord 0 0 dividend 0 width 0) := by
  rfl

def terminalTape (consumed remainder width quotient : Nat) : WorkTape :=
  { left :=
      List.replicate width unitSymbol ++
        separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary])
    head := endSymbol
    right := List.replicate quotient quotientMark }

def terminalConfiguration (consumed remainder width quotient : Nat) :
    WorkConfiguration :=
  { state := machine.acceptState
    tape := terminalTape consumed remainder width quotient }

/-! ## Exact repeated-subtraction traces -/

def pairSteps (consumed matched remaining : Nat) : Nat :=
  2 * consumed + 4 * matched + 2 * remaining + 8

/-- Pair one more dividend unit with one divisor unit when at least one divisor
unit remains after the selected unit. -/
theorem pair_iteration_exact (consumed matched remaining divisorTail quotient : Nat) :
    workRunExact? machine (pairSteps consumed matched remaining)
        (phaseConfiguration consumed matched (remaining + 1)
          matched (divisorTail + 2) quotient) =
      some (phaseConfiguration consumed (matched + 1) remaining
        (matched + 1) (divisorTail + 1) quotient) := by
  let quotientTail := endSymbol :: List.replicate quotient quotientMark
  let divisorRight :=
    List.replicate (divisorTail + 2) unitSymbol ++ quotientTail
  let afterSelectedDivisor :=
    List.replicate (divisorTail + 1) unitSymbol ++ quotientTail
  let bodyTail :=
    separatorSymbol ::
      (List.replicate matched matchedDivisor ++ divisorRight)
  let afterBodyTail :=
    separatorSymbol ::
      (List.replicate (matched + 1) matchedDivisor ++
        List.replicate (divisorTail + 1) unitSymbol ++ quotientTail)
  let c0 := phaseConfiguration consumed matched (remaining + 1)
    matched (divisorTail + 2) quotient
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate matched matchedDividend ++
          List.replicate (remaining + 1) unitSymbol ++ bodyTail) }
  let c2 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate matched matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate (remaining + 1) unitSymbol ++ bodyTail) }
  let c3 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        (List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate remaining unitSymbol ++ bodyTail) }
  let c4 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        (List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        bodyTail }
  let c5 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate matched matchedDivisor ++ divisorRight) }
  let c6 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (List.replicate matched matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        divisorRight }
  let c7 : WorkConfiguration :=
    { state := 3
      tape := rightPathTape
        (List.replicate (matched + 1) matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        afterSelectedDivisor }
  let rewindSymbols :=
    List.replicate (matched + 1) matchedDivisor ++
      separatorSymbol ::
        (List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend)
  let c8 : WorkConfiguration :=
    { state := 4
      tape := leftPathTape afterSelectedDivisor
        (rewindSymbols ++ [leftBoundary]) }
  let c9 := phaseConfiguration consumed (matched + 1) remaining
    (matched + 1) (divisorTail + 1) quotient

  have h01 : workRunExact? machine consumed c0 = some c1 := by
    simpa [c0, c1, phaseConfiguration, phaseTape, phaseWord, bodyTail,
      divisorRight, quotientTail, List.append_assoc] using
      scanRightExact 0 consumedDividend consumedDividend consumed
        [leftBoundary]
        (List.replicate matched matchedDividend ++
          List.replicate (remaining + 1) unitSymbol ++ bodyTail)
        (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape consumedDividend hHead
          simpa [hWrite] using scanDividend_consumed_step tape hHead)
  have h12 : workRunExact? machine matched c1 = some c2 := by
    simpa [c1, c2, List.append_assoc] using
      scanRightExact 0 matchedDividend matchedDividend matched
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate (remaining + 1) unitSymbol ++ bodyTail)
        (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape matchedDividend hHead
          simpa [hWrite] using scanDividend_matched_step tape hHead)
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    simpa [c2, c3, List.replicate_succ, List.append_assoc] using
      scanDividend_unit_step c2.tape (by rfl)
  have h34 : workRunExact? machine remaining c3 = some c4 := by
    simpa [c3, c4, List.append_assoc] using
      scanRightExact 1 unitSymbol unitSymbol remaining
        (List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        bodyTail (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape unitSymbol hHead
          simpa [hWrite] using seekSeparator_unit_step tape hHead)
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    simpa [c4, c5, bodyTail, List.append_assoc] using
      seekSeparator_separator_step c4.tape (by rfl)
  have h56 : workRunExact? machine matched c5 = some c6 := by
    simpa [c5, c6, List.append_assoc] using
      scanRightExact 2 matchedDivisor matchedDivisor matched
        (separatorSymbol ::
          List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        divisorRight (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape matchedDivisor hHead
          simpa [hWrite] using scanDivisor_matched_step tape hHead)
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    simpa [c6, c7, divisorRight, afterSelectedDivisor,
      List.replicate_succ, List.append_assoc] using
      scanDivisor_unit_step c6.tape (by rfl)
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    simpa [c7, c8, rewindSymbols, afterSelectedDivisor,
      List.replicate_succ, List.append_assoc] using
      checkDivisor_unit_step c7.tape (by rfl)
  have hAllowed : ∀ symbol ∈ rewindSymbols,
      symbol = matchedDivisor ∨ symbol = separatorSymbol ∨
      symbol = unitSymbol ∨ symbol = matchedDividend ∨
      symbol = consumedDividend := by
    intro symbol hSymbol
    dsimp [rewindSymbols] at hSymbol
    simp only [List.mem_append, List.mem_cons, List.mem_replicate] at hSymbol
    rcases hSymbol with h | h | h | h
    · exact Or.inl h.2
    · exact Or.inr (Or.inl h)
    · rcases h with h | h
      · exact Or.inr (Or.inr (Or.inl h.2))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h.2)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h.2)))
  have h89 : workRunExact? machine (rewindSymbols.length + 1) c8 =
      some c9 := by
    have hRewind := rewindPair_exact rewindSymbols afterSelectedDivisor hAllowed
    have hWord : rewindSymbols.reverse ++ afterSelectedDivisor =
        phaseWord consumed (matched + 1) remaining (matched + 1)
          (divisorTail + 1) quotient := by
      simp [rewindSymbols, afterSelectedDivisor, phaseWord, quotientTail,
        List.reverse_append, List.append_assoc]
    simpa [c8, c9, phaseConfiguration, phaseTape, hWord] using hRewind
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    consumed matched c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1) remaining c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1) matched c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched) 1
    c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1) 1
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1 + 1)
    (rewindSymbols.length + 1) c0 c8 c9 h08 h89
  have hRewindLength : rewindSymbols.length =
      consumed + 2 * matched + remaining + 3 := by
    simp [rewindSymbols]
    omega
  have hCount :
      consumed + matched + 1 + remaining + 1 + matched + 1 + 1 +
          (rewindSymbols.length + 1) =
        pairSteps consumed matched remaining := by
    rw [hRewindLength]
    simp [pairSteps]
    omega
  rw [← hCount]
  simpa [c0, c9] using h09

def finalPairSteps (consumed matched remaining quotient : Nat) : Nat :=
  2 * consumed + 4 * matched + 2 * remaining + 2 * quotient + 10

/-- Select the last divisor unit, record one quotient mark, retire the complete
matched dividend block, and restore the divisor. -/
theorem final_pair_exact (consumed matched remaining quotient : Nat) :
    workRunExact? machine (finalPairSteps consumed matched remaining quotient)
        (phaseConfiguration consumed matched (remaining + 1)
          matched 1 quotient) =
      some (loopConfiguration (consumed + matched + 1) remaining
        (matched + 1) (quotient + 1)) := by
  let quotientTail := endSymbol :: List.replicate quotient quotientMark
  let divisorRight := unitSymbol :: quotientTail
  let bodyTail :=
    separatorSymbol ::
      (List.replicate matched matchedDivisor ++ divisorRight)
  let c0 := phaseConfiguration consumed matched (remaining + 1)
    matched 1 quotient
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate matched matchedDividend ++
          List.replicate (remaining + 1) unitSymbol ++ bodyTail) }
  let c2 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate matched matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate (remaining + 1) unitSymbol ++ bodyTail) }
  let c3 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        (List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate remaining unitSymbol ++ bodyTail) }
  let c4 : WorkConfiguration :=
    { state := 1
      tape := rightPathTape
        (List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        bodyTail }
  let c5 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate matched matchedDivisor ++ divisorRight) }
  let c6 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape
        (List.replicate matched matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        divisorRight }
  let c7 : WorkConfiguration :=
    { state := 3
      tape := rightPathTape
        (List.replicate (matched + 1) matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        quotientTail }
  let c8 : WorkConfiguration :=
    { state := 5
      tape := rightPathTape
        (endSymbol ::
          List.replicate (matched + 1) matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        (List.replicate quotient quotientMark) }
  let c9 : WorkConfiguration :=
    { state := 5
      tape := rightPathTape
        (List.replicate quotient quotientMark ++
          endSymbol ::
            (List.replicate (matched + 1) matchedDivisor ++
              separatorSymbol ::
                (List.replicate remaining unitSymbol ++
                  List.replicate (matched + 1) matchedDividend ++
                  List.replicate consumed consumedDividend ++ [leftBoundary])))
        [] }
  let cleanupSymbols :=
    List.replicate quotient quotientMark ++
      endSymbol ::
        (List.replicate (matched + 1) matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend))
  let c10 : WorkConfiguration :=
    { state := 6
      tape := leftPathTape [quotientMark]
        (cleanupSymbols ++ [leftBoundary]) }
  let c11 := loopConfiguration (consumed + matched + 1) remaining
    (matched + 1) (quotient + 1)

  have h01 : workRunExact? machine consumed c0 = some c1 := by
    simpa [c0, c1, phaseConfiguration, phaseTape, phaseWord, bodyTail,
      divisorRight, quotientTail, List.append_assoc] using
      scanRightExact 0 consumedDividend consumedDividend consumed
        [leftBoundary]
        (List.replicate matched matchedDividend ++
          List.replicate (remaining + 1) unitSymbol ++ bodyTail) (by
            intro tape hHead
            have hWrite := tape_write_eq_self tape consumedDividend hHead
            simpa [hWrite] using scanDividend_consumed_step tape hHead)
  have h12 : workRunExact? machine matched c1 = some c2 := by
    simpa [c1, c2, List.append_assoc] using
      scanRightExact 0 matchedDividend matchedDividend matched
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate (remaining + 1) unitSymbol ++ bodyTail) (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape matchedDividend hHead
          simpa [hWrite] using scanDividend_matched_step tape hHead)
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    simpa [c2, c3, List.replicate_succ, List.append_assoc] using
      scanDividend_unit_step c2.tape (by rfl)
  have h34 : workRunExact? machine remaining c3 = some c4 := by
    simpa [c3, c4, List.append_assoc] using
      scanRightExact 1 unitSymbol unitSymbol remaining
        (List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        bodyTail (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape unitSymbol hHead
          simpa [hWrite] using seekSeparator_unit_step tape hHead)
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    simpa [c4, c5, bodyTail, List.append_assoc] using
      seekSeparator_separator_step c4.tape (by rfl)
  have h56 : workRunExact? machine matched c5 = some c6 := by
    simpa [c5, c6, List.append_assoc] using
      scanRightExact 2 matchedDivisor matchedDivisor matched
        (separatorSymbol ::
          List.replicate remaining unitSymbol ++
          List.replicate (matched + 1) matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        divisorRight (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape matchedDivisor hHead
          simpa [hWrite] using scanDivisor_matched_step tape hHead)
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    simpa [c6, c7, divisorRight, quotientTail, List.replicate_succ,
      List.append_assoc] using scanDivisor_unit_step c6.tape (by rfl)
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    simpa [c7, c8, quotientTail, List.append_assoc] using
      checkDivisor_end_step c7.tape (by rfl)
  have h89 : workRunExact? machine quotient c8 = some c9 := by
    simpa [c8, c9, List.append_assoc] using
      scanRightExact 5 quotientMark quotientMark quotient
        (endSymbol ::
          List.replicate (matched + 1) matchedDivisor ++
          separatorSymbol ::
            (List.replicate remaining unitSymbol ++
              List.replicate (matched + 1) matchedDividend ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        [] (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape quotientMark hHead
          simpa [hWrite] using seekQuotient_mark_step tape hHead)
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    have hStep := seekQuotient_blank_step c9.tape (by
      simp [c9, rightPathTape])
    have hLeft :
        List.replicate quotient quotientMark ++
          endSymbol ::
            (List.replicate (matched + 1) matchedDivisor ++
              separatorSymbol ::
                (List.replicate remaining unitSymbol ++
                  List.replicate (matched + 1) matchedDividend ++
                  List.replicate consumed consumedDividend ++
                  [leftBoundary])) ≠ [] := by
      simp
    have hMove := rightPathTape_empty_write_moveLeft_nonempty
      (List.replicate quotient quotientMark ++
        endSymbol ::
          (List.replicate (matched + 1) matchedDivisor ++
            separatorSymbol ::
              (List.replicate remaining unitSymbol ++
                List.replicate (matched + 1) matchedDividend ++
                List.replicate consumed consumedDividend ++ [leftBoundary])))
      quotientMark hLeft
    dsimp [c9] at hStep
    rw [hMove] at hStep
    simpa [c9, c10, cleanupSymbols, List.append_assoc] using hStep
  have hAllowed : ∀ symbol ∈ cleanupSymbols,
      symbol = matchedDivisor ∨ symbol = matchedDividend ∨
      symbol = quotientMark ∨ symbol = endSymbol ∨
      symbol = separatorSymbol ∨ symbol = unitSymbol ∨
      symbol = consumedDividend := by
    intro symbol hSymbol
    dsimp [cleanupSymbols] at hSymbol
    rcases List.mem_append.mp hSymbol with hQuotient | hRest
    · exact Or.inr (Or.inr (Or.inl
        (List.eq_of_mem_replicate hQuotient)))
    · rcases List.mem_cons.mp hRest with hEnd | hRest
      · exact Or.inr (Or.inr (Or.inr (Or.inl hEnd)))
      · rcases List.mem_append.mp hRest with hDivisor | hRest
        · exact Or.inl (List.eq_of_mem_replicate hDivisor)
        · rcases List.mem_cons.mp hRest with hSeparator | hRest
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hSeparator))))
          · rcases List.mem_append.mp hRest with hUnitOrDividend | hConsumed
            · rcases List.mem_append.mp hUnitOrDividend with hUnit | hDividend
              · exact Or.inr (Or.inr (Or.inr (Or.inr
                  (Or.inr (Or.inl (List.eq_of_mem_replicate hUnit))))))
              · exact Or.inr (Or.inl
                  (List.eq_of_mem_replicate hDividend))
            · exact Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr (Or.inr
                  (List.eq_of_mem_replicate hConsumed))))))
  have h1011 : workRunExact? machine (cleanupSymbols.length + 1) c10 =
      some c11 := by
    have hCleanup := cleanupFull_exact cleanupSymbols [quotientMark] hAllowed
    have hWord : (cleanupSymbols.map cleanupFullWrite).reverse ++
          [quotientMark] =
        phaseWord (consumed + matched + 1) 0 remaining 0 (matched + 1)
          (quotient + 1) := by
      have hBase : (cleanupSymbols.map cleanupFullWrite).reverse ++
            [quotientMark] =
          phaseWord (matched + consumed + 1) 0 remaining 0 (matched + 1)
            (quotient + 1) := by
        simp [cleanupSymbols, phaseWord, List.reverse_append,
          List.append_assoc, List.replicate_succ,
          replicate_append_self_cons]
      have hConsumedCount :
          matched + consumed + 1 = consumed + matched + 1 := by
        omega
      simpa only [hConsumedCount] using hBase
    simpa [c10, c11, loopConfiguration, phaseConfiguration, phaseTape,
      hWord] using hCleanup
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    consumed matched c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1) remaining c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1) matched c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1) 1
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1 + 1)
    quotient c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1 + 1 + quotient)
    1 c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + matched + 1 + remaining + 1 + matched + 1 + 1 +
      quotient + 1) (cleanupSymbols.length + 1) c0 c10 c11 h010 h1011
  have hCleanupLength : cleanupSymbols.length =
      consumed + 2 * matched + remaining + quotient + 4 := by
    simp [cleanupSymbols]
    omega
  have hCount :
      consumed + matched + 1 + remaining + 1 + matched + 1 + 1 +
          quotient + 1 + (cleanupSymbols.length + 1) =
        finalPairSteps consumed matched remaining quotient := by
    rw [hCleanupLength]
    simp [finalPairSteps]
    omega
  rw [← hCount]
  simpa [c0, c11] using h011

/-- Exact work-step count for completing the unpaired suffix of one positive
divisor pass. The argument is the number of divisor units still to match. -/
def passSteps (consumed matched dividendTail quotient : Nat) : Nat → Nat
  | 0 => 0
  | 1 => finalPairSteps consumed matched dividendTail quotient
  | remaining + 2 =>
      pairSteps consumed matched (remaining + 1 + dividendTail) +
        passSteps consumed (matched + 1) dividendTail quotient (remaining + 1)

/-- Complete one full positive-width subtraction pass, append one quotient
mark, restore the divisor, and return to the canonical loop configuration. -/
theorem complete_pass_exact (consumed matched dividendTail quotient
    remaining : Nat) :
    workRunExact? machine
        (passSteps consumed matched dividendTail quotient (remaining + 1))
        (phaseConfiguration consumed matched (remaining + 1 + dividendTail)
          matched (remaining + 1) quotient) =
      some (loopConfiguration (consumed + matched + remaining + 1)
        dividendTail (matched + remaining + 1) (quotient + 1)) := by
  induction remaining generalizing consumed matched with
  | zero =>
      simpa [passSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        final_pair_exact consumed matched dividendTail quotient
  | succ remaining ih =>
      let middle := phaseConfiguration consumed (matched + 1)
        (remaining + 1 + dividendTail) (matched + 1) (remaining + 1)
        quotient
      have hFirst :
          workRunExact? machine
              (pairSteps consumed matched (remaining + 1 + dividendTail))
              (phaseConfiguration consumed matched
                (remaining + 2 + dividendTail) matched (remaining + 2)
                quotient) = some middle := by
        simpa [middle, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          pair_iteration_exact consumed matched
            (remaining + 1 + dividendTail) remaining quotient
      have hRest :
          workRunExact? machine
              (passSteps consumed (matched + 1) dividendTail quotient
                (remaining + 1)) middle =
            some (loopConfiguration
              (consumed + (matched + 1) + remaining + 1) dividendTail
              ((matched + 1) + remaining + 1) (quotient + 1)) := by
        simpa [middle] using
          ih (consumed := consumed) (matched := matched + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (pairSteps consumed matched (remaining + 1 + dividendTail))
        (passSteps consumed (matched + 1) dividendTail quotient
          (remaining + 1)) _ middle _ hFirst hRest
      simpa [passSteps, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hAll

/-- Exact work-step count for restoring a strict final remainder and the
positive divisor before acceptance. -/
def terminalCleanupSteps (consumed remainder divisorTail _quotient : Nat) : Nat :=
  3 * consumed + 4 * remainder + divisorTail + 5

/-- When the current dividend is exhausted before the positive divisor, the
machine restores the partial remainder and divisor and accepts in the canonical
terminal layout. -/
theorem terminal_cleanup_exact (consumed remainder divisorTail quotient : Nat) :
    workRunExact? machine
        (terminalCleanupSteps consumed remainder divisorTail quotient)
        (phaseConfiguration consumed remainder 0 remainder
          (divisorTail + 1) quotient) =
      some (terminalConfiguration consumed remainder
        (remainder + divisorTail + 1) quotient) := by
  let quotientTail := endSymbol :: List.replicate quotient quotientMark
  let divisorRight := List.replicate remainder matchedDivisor ++
    List.replicate (divisorTail + 1) unitSymbol ++ quotientTail
  let afterDividend := separatorSymbol :: divisorRight
  let c0 := phaseConfiguration consumed remainder 0 remainder
    (divisorTail + 1) quotient
  let c1 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate remainder matchedDividend ++ afterDividend) }
  let c2 : WorkConfiguration :=
    { state := 0
      tape := rightPathTape
        (List.replicate remainder matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        afterDividend }
  let c3 : WorkConfiguration :=
    { state := 7
      tape := leftPathTape afterDividend
        (List.replicate remainder matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary]) }
  let c4 : WorkConfiguration :=
    { state := 8
      tape := rightPathTape [leftBoundary]
        (List.replicate consumed consumedDividend ++
          List.replicate remainder unitSymbol ++ afterDividend) }
  let c5 : WorkConfiguration :=
    { state := 8
      tape := rightPathTape
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        (List.replicate remainder unitSymbol ++ afterDividend) }
  let c6 : WorkConfiguration :=
    { state := 8
      tape := rightPathTape
        (List.replicate remainder unitSymbol ++
          List.replicate consumed consumedDividend ++ [leftBoundary])
        afterDividend }
  let c7 : WorkConfiguration :=
    { state := 9
      tape := rightPathTape
        (separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary]))
        divisorRight }
  let c8 : WorkConfiguration :=
    { state := 9
      tape := rightPathTape
        (List.replicate remainder unitSymbol ++
          separatorSymbol ::
            (List.replicate remainder unitSymbol ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        (List.replicate (divisorTail + 1) unitSymbol ++ quotientTail) }
  let c9 : WorkConfiguration :=
    { state := 9
      tape := rightPathTape
        (List.replicate (divisorTail + 1) unitSymbol ++
          (List.replicate remainder unitSymbol ++
            separatorSymbol ::
              (List.replicate remainder unitSymbol ++
                List.replicate consumed consumedDividend ++ [leftBoundary])))
        quotientTail }
  let c10 := terminalConfiguration consumed remainder
    (remainder + divisorTail + 1) quotient
  have h01 : workRunExact? machine consumed c0 = some c1 := by
    simpa [c0, c1, phaseConfiguration, phaseTape, phaseWord,
      afterDividend, divisorRight, quotientTail, List.append_assoc] using
      scanRightExact 0 consumedDividend consumedDividend consumed
        [leftBoundary]
        (List.replicate remainder matchedDividend ++ afterDividend) (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape consumedDividend hHead
          simpa [hWrite] using scanDividend_consumed_step tape hHead)
  have h12 : workRunExact? machine remainder c1 = some c2 := by
    simpa [c1, c2, List.append_assoc] using
      scanRightExact 0 matchedDividend matchedDividend remainder
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        afterDividend (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape matchedDividend hHead
          simpa [hWrite] using scanDividend_matched_step tape hHead)
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    have hStep := scanDividend_separator_step c2.tape (by rfl)
    have hLeft :
        List.replicate remainder matchedDividend ++
          List.replicate consumed consumedDividend ++ [leftBoundary] ≠ [] := by
      simp
    have hMove := rightPathTape_moveLeft_nonempty
      (List.replicate remainder matchedDividend ++
        List.replicate consumed consumedDividend ++ [leftBoundary])
      separatorSymbol divisorRight hLeft
    dsimp [c2] at hStep
    rw [hMove] at hStep
    simpa [c2, c3, afterDividend] using hStep
  have hAllowed : ∀ symbol ∈
        (List.replicate remainder matchedDividend ++
          List.replicate consumed consumedDividend),
      symbol = matchedDividend ∨ symbol = consumedDividend := by
    intro symbol hSymbol
    rcases List.mem_append.mp hSymbol with hMatched | hConsumed
    · exact Or.inl (List.eq_of_mem_replicate hMatched)
    · exact Or.inr (List.eq_of_mem_replicate hConsumed)
  have h34 : workRunExact? machine (remainder + consumed + 1) c3 =
      some c4 := by
    have hRestore := restoreDividend_exact
      (List.replicate remainder matchedDividend ++
        List.replicate consumed consumedDividend) afterDividend hAllowed
    simpa [c3, c4, List.reverse_append, List.append_assoc] using hRestore
  have h45 : workRunExact? machine consumed c4 = some c5 := by
    simpa [c4, c5, List.append_assoc] using
      scanRightExact 8 consumedDividend consumedDividend consumed
        [leftBoundary]
        (List.replicate remainder unitSymbol ++ afterDividend) (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape consumedDividend hHead
          simpa [hWrite] using
            seekTerminal_keep_step tape (Or.inl hHead))
  have h56 : workRunExact? machine remainder c5 = some c6 := by
    simpa [c5, c6, List.append_assoc] using
      scanRightExact 8 unitSymbol unitSymbol remainder
        (List.replicate consumed consumedDividend ++ [leftBoundary])
        afterDividend (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape unitSymbol hHead
          simpa [hWrite] using
            seekTerminal_keep_step tape (Or.inr hHead))
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    simpa [c6, c7, afterDividend, divisorRight] using
      seekTerminal_separator_step c6.tape (by rfl)
  have h78 : workRunExact? machine remainder c7 = some c8 := by
    simpa [c7, c8, divisorRight, List.append_assoc] using
      scanRightExact 9 matchedDivisor unitSymbol remainder
        (separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary]))
        (List.replicate (divisorTail + 1) unitSymbol ++ quotientTail) (by
          intro tape hHead
          simpa using restoreDivisor_matched_step tape hHead)
  have h89 : workRunExact? machine (divisorTail + 1) c8 = some c9 := by
    simpa [c8, c9, List.append_assoc] using
      scanRightExact 9 unitSymbol unitSymbol (divisorTail + 1)
        (List.replicate remainder unitSymbol ++
          separatorSymbol ::
            (List.replicate remainder unitSymbol ++
              List.replicate consumed consumedDividend ++ [leftBoundary]))
        quotientTail (by
          intro tape hHead
          have hWrite := tape_write_eq_self tape unitSymbol hHead
          simpa [hWrite] using restoreDivisor_unit_step tape hHead)
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    have hStep := restoreDivisor_end_step c9.tape (by
      simp [c9, quotientTail, rightPathTape])
    have hWidth :
        List.replicate (divisorTail + 1) unitSymbol ++
            List.replicate remainder unitSymbol =
          List.replicate (remainder + divisorTail + 1) unitSymbol := by
      rw [← replicate_add]
      congr 1
      omega
    have hLeft :
        List.replicate (divisorTail + 1) unitSymbol ++
            (List.replicate remainder unitSymbol ++
              (separatorSymbol ::
                (List.replicate remainder unitSymbol ++
                  List.replicate consumed consumedDividend ++ [leftBoundary]))) =
          List.replicate (remainder + divisorTail + 1) unitSymbol ++
            separatorSymbol ::
              (List.replicate remainder unitSymbol ++
                List.replicate consumed consumedDividend ++ [leftBoundary]) := by
      rw [← List.append_assoc, hWidth]
    dsimp [c9, quotientTail, rightPathTape] at hStep ⊢
    rw [hLeft] at hStep ⊢
    simpa [c10, terminalConfiguration, terminalTape, machine]
      using hStep
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    consumed remainder c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1) (remainder + consumed + 1)
    c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1)) consumed
    c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1) + consumed)
    remainder c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1) + consumed +
      remainder) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1) + consumed +
      remainder + 1) remainder c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1) + consumed +
      remainder + 1 + remainder) (divisorTail + 1)
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (consumed + remainder + 1 + (remainder + consumed + 1) + consumed +
      remainder + 1 + remainder + (divisorTail + 1)) 1
    c0 c9 c10 h09 h910
  have hCount :
      consumed + remainder + 1 + (remainder + consumed + 1) + consumed +
          remainder + 1 + remainder + (divisorTail + 1) + 1 =
        terminalCleanupSteps consumed remainder divisorTail quotient := by
    simp [terminalCleanupSteps]
    omega
  rw [← hCount]
  simpa [c0, c10] using h010

/-- Exact work-step count for exhausting a strict final dividend remainder
before running the terminal restoration pass. -/
def terminalStepsFrom (consumed matched divisorTail quotient : Nat) : Nat → Nat
  | 0 => terminalCleanupSteps consumed matched divisorTail quotient
  | remaining + 1 =>
      pairSteps consumed matched remaining +
        terminalStepsFrom consumed (matched + 1) divisorTail quotient remaining

/-- Exhaust an arbitrary strict remainder, then restore it and the positive
divisor in the canonical accepting layout. -/
theorem terminal_partial_exact (consumed matched divisorTail quotient
    remaining : Nat) :
    workRunExact? machine
        (terminalStepsFrom consumed matched divisorTail quotient remaining)
        (phaseConfiguration consumed matched remaining matched
          (remaining + divisorTail + 1) quotient) =
      some (terminalConfiguration consumed (matched + remaining)
        (matched + remaining + divisorTail + 1) quotient) := by
  induction remaining generalizing matched with
  | zero =>
      simpa [terminalStepsFrom, Nat.add_assoc] using
        terminal_cleanup_exact consumed matched divisorTail quotient
  | succ remaining ih =>
      let middle := phaseConfiguration consumed (matched + 1) remaining
        (matched + 1) (remaining + divisorTail + 1) quotient
      have hFirst :
          workRunExact? machine (pairSteps consumed matched remaining)
              (phaseConfiguration consumed matched (remaining + 1) matched
                (remaining + 1 + divisorTail + 1) quotient) =
            some middle := by
        simpa [middle, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          pair_iteration_exact consumed matched remaining
            (remaining + divisorTail) quotient
      have hRest :
          workRunExact? machine
              (terminalStepsFrom consumed (matched + 1) divisorTail quotient
                remaining) middle =
            some (terminalConfiguration consumed
              ((matched + 1) + remaining)
              ((matched + 1) + remaining + divisorTail + 1) quotient) := by
        simpa [middle] using ih (matched := matched + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (pairSteps consumed matched remaining)
        (terminalStepsFrom consumed (matched + 1) divisorTail quotient
          remaining) _ middle _ hFirst hRest
      simpa [terminalStepsFrom, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using hAll

/-- Exact work-step count for a requested number of full quotient cycles,
followed by the strict-remainder terminal pass. -/
def divisionStepsFrom (consumed remainder divisorTail quotient : Nat) :
    Nat → Nat
  | 0 => terminalStepsFrom consumed 0 divisorTail quotient remainder
  | cycles + 1 =>
      let width := remainder + divisorTail + 1
      passSteps consumed 0 (cycles * width + remainder) quotient width +
        divisionStepsFrom (consumed + width) remainder divisorTail
          (quotient + 1) cycles

/-- Run any number of complete positive-width subtraction cycles and then the
unique strict-remainder cleanup. -/
theorem division_cycles_exact (consumed remainder divisorTail quotient
    cycles : Nat) :
    let width := remainder + divisorTail + 1
    workRunExact? machine
        (divisionStepsFrom consumed remainder divisorTail quotient cycles)
        (loopConfiguration consumed (cycles * width + remainder) width
          quotient) =
      some (terminalConfiguration (consumed + cycles * width) remainder width
        (quotient + cycles)) := by
  let width := remainder + divisorTail + 1
  induction cycles generalizing consumed quotient with
  | zero =>
      simpa [divisionStepsFrom, width, loopConfiguration, Nat.add_assoc] using
        terminal_partial_exact consumed 0 divisorTail quotient remainder
  | succ cycles ih =>
      let middle := loopConfiguration (consumed + width)
        (cycles * width + remainder) width (quotient + 1)
      have hFirst :
          workRunExact? machine
              (passSteps consumed 0 (cycles * width + remainder) quotient width)
              (loopConfiguration consumed
                ((cycles + 1) * width + remainder) width quotient) =
            some middle := by
        simpa [middle, loopConfiguration, width, Nat.succ_mul,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          complete_pass_exact consumed 0 (cycles * width + remainder)
            quotient (remainder + divisorTail)
      have hRest :
          workRunExact? machine
              (divisionStepsFrom (consumed + width) remainder divisorTail
                (quotient + 1) cycles) middle =
            some (terminalConfiguration
              ((consumed + width) + cycles * width) remainder width
              ((quotient + 1) + cycles)) := by
        simpa [middle, width] using
          ih (consumed := consumed + width) (quotient := quotient + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (passSteps consumed 0 (cycles * width + remainder) quotient width)
        (divisionStepsFrom (consumed + width) remainder divisorTail
          (quotient + 1) cycles) _ middle _ hFirst hRest
      simpa [divisionStepsFrom, width, Nat.succ_mul,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hAll

/-- The strict divisor suffix after the natural remainder. -/
def rawDivisorTail (dividend width : Nat) : Nat :=
  width - dividend % width - 1

/-- Exact work-step budget selected from the natural quotient/remainder
decomposition. The correctness theorem requires positive width. -/
def workSteps (dividend width : Nat) : Nat :=
  divisionStepsFrom 0 (dividend % width) (rawDivisorTail dividend width) 0
    (dividend / width)

def finalConfiguration (dividend width : Nat) : WorkConfiguration :=
  terminalConfiguration ((dividend / width) * width) (dividend % width) width
    (dividend / width)

private theorem rawDivisorTail_spec (dividend width : Nat)
    (hWidth : 0 < width) :
    dividend % width + rawDivisorTail dividend width + 1 = width := by
  have hRemainder := Nat.mod_lt dividend hWidth
  simp only [rawDivisorTail]
  omega

theorem quotient_remainder_reconstruct (dividend width : Nat) :
    (dividend / width) * width + dividend % width = dividend := by
  simpa [Nat.mul_comm] using Nat.div_add_mod dividend width

theorem remainder_lt_width (dividend width : Nat) (hWidth : 0 < width) :
    dividend % width < width :=
  Nat.mod_lt dividend hWidth

/-- Every unary dividend and positive unary width has one exact accepting
quotient/remainder trace in the fixed 99-rule machine. -/
theorem workRunExact (dividend width : Nat) (hWidth : 0 < width) :
    workRunExact? machine (workSteps dividend width)
        (workStartConfiguration machine (inputTape dividend width)) =
      some (finalConfiguration dividend width) := by
  have hWidthDecomposition := rawDivisorTail_spec dividend width hWidth
  have hDividend := quotient_remainder_reconstruct dividend width
  have hRun := division_cycles_exact 0 (dividend % width)
    (rawDivisorTail dividend width) 0 (dividend / width)
  dsimp only at hRun
  rw [hWidthDecomposition] at hRun
  rw [hDividend] at hRun
  simpa [workSteps, finalConfiguration, loopConfiguration, inputTape,
    phaseConfiguration, machine, workStartConfiguration, Nat.add_assoc] using
      hRun

theorem finalConfiguration_isHalted (dividend width : Nat) :
    machine.isHalted (finalConfiguration dividend width) = true := by
  rfl

/-- Exact six-raw-transition simulation of every certified work transition. -/
theorem run_compile_exact (dividend width : Nat) (hWidth : 0 < width) :
    run (compileWorkMachine machine) (6 * workSteps dividend width)
        (encodeWorkConfiguration
          (workStartConfiguration machine (inputTape dividend width))) =
      encodeWorkConfiguration (finalConfiguration dividend width) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps dividend width)
    (workStartConfiguration machine (inputTape dividend width))
    (finalConfiguration dividend width) (workRunExact dividend width hWidth)

/-- The public dispatcher refuses the malformed zero-width case before any
division claim is exposed. -/
def divide? (dividend width : Nat) : Option WorkConfiguration :=
  if 0 < width then some (finalConfiguration dividend width) else none

@[simp] theorem divide?_zero (dividend : Nat) : divide? dividend 0 = none := by
  simp [divide?]

theorem divide?_eq_some (dividend width : Nat) (hWidth : 0 < width) :
    divide? dividend width = some (finalConfiguration dividend width) := by
  simp [divide?, hWidth]

/-- Read the quotient and strict remainder from a canonical terminal tape.
The consumed-prefix length remains independently available for reconstruction.
-/
def terminalQuotientRemainder (configuration : WorkConfiguration) : Nat × Nat :=
  (configuration.tape.right.count quotientMark,
    configuration.tape.left.count unitSymbol -
      (configuration.tape.left.takeWhile (· = unitSymbol)).length)

private theorem quotientCount_replicate (count : Nat) :
    (List.replicate count quotientMark).count quotientMark = count := by
  rw [List.count_replicate]
  rfl

private theorem unitCount_replicate (count : Nat) :
    (List.replicate count unitSymbol).count unitSymbol = count := by
  rw [List.count_replicate]
  rfl

private theorem unitCount_consumed_replicate (count : Nat) :
    (List.replicate count consumedDividend).count unitSymbol = 0 := by
  rw [List.count_replicate]
  rfl

private theorem terminalLeft_unitCount (consumed remainder width : Nat) :
    (List.replicate width unitSymbol ++
        separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary])).count
      unitSymbol = width + remainder := by
  have hSeparator : (separatorSymbol == unitSymbol) = false := by rfl
  have hBoundary : (leftBoundary == unitSymbol) = false := by rfl
  simp [List.count_append, List.count_cons,
    unitCount_consumed_replicate, hSeparator, hBoundary]

private theorem terminalLeft_takeWhile_length (consumed remainder width : Nat) :
    ((List.replicate width unitSymbol ++
        separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary])).takeWhile
      (fun symbol => symbol = unitSymbol)).length = width := by
  simp [separatorSymbol, unitSymbol,
    BuilderUnaryPolynomial.separatorSymbol,
    BuilderUnaryPolynomial.unitSymbol, WorkSymbol.zeroOne,
    WorkSymbol.oneOne]

theorem terminalQuotientRemainder_terminal (consumed remainder width
    quotient : Nat) :
    terminalQuotientRemainder
        (terminalConfiguration consumed remainder width quotient) =
      (quotient, remainder) := by
  change
    ((List.replicate quotient quotientMark).count quotientMark,
      (List.replicate width unitSymbol ++ separatorSymbol ::
        (List.replicate remainder unitSymbol ++
          List.replicate consumed consumedDividend ++ [leftBoundary])).count
          unitSymbol -
        ((List.replicate width unitSymbol ++ separatorSymbol ::
          (List.replicate remainder unitSymbol ++
            List.replicate consumed consumedDividend ++ [leftBoundary])).takeWhile
          (fun symbol => symbol = unitSymbol)).length) =
      (quotient, remainder)
  rw [quotientCount_replicate, terminalLeft_unitCount,
    terminalLeft_takeWhile_length]
  simp

/-- The decoded terminal tape is exactly natural-number quotient and
remainder, independently of the internal consumed-prefix ledger. -/
theorem final_quotient_remainder (dividend width : Nat) :
    terminalQuotientRemainder (finalConfiguration dividend width) =
      (dividend / width, dividend % width) := by
  simpa [finalConfiguration] using
    terminalQuotientRemainder_terminal ((dividend / width) * width)
      (dividend % width) width (dividend / width)



/-! ## Explicit encoded-size step bound -/

theorem passSteps_le (consumed matched dividendTail quotient remaining : Nat) :
    passSteps consumed matched dividendTail quotient remaining ≤
      10 * remaining *
        (consumed + matched + remaining + dividendTail + quotient + 1) := by
  induction remaining generalizing matched with
  | zero => simp [passSteps]
  | succ remaining ih =>
      cases remaining with
      | zero =>
          simp [passSteps, finalPairSteps]
          omega
      | succ remaining =>
          let measure := consumed + matched + (remaining + 2) +
            dividendTail + quotient + 1
          have hTail := ih (matched := matched + 1)
          have hMeasure :
              consumed + (matched + 1) + (remaining + 1) + dividendTail +
                  quotient + 1 = measure := by
            dsimp [measure]
            omega
          rw [hMeasure] at hTail
          have hPair :
              pairSteps consumed matched (remaining + 1 + dividendTail) ≤
                10 * measure := by
            simp [pairSteps, measure]
            omega
          simp only [passSteps]
          calc
            pairSteps consumed matched (remaining + 1 + dividendTail) +
                passSteps consumed (matched + 1) dividendTail quotient
                  (remaining + 1) ≤
              10 * measure + 10 * (remaining + 1) * measure :=
                Nat.add_le_add hPair hTail
            _ = 10 * (remaining + 2) * measure := by
              rw [show remaining + 2 = 1 + (remaining + 1) by omega]
              simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem terminalStepsFrom_le (consumed matched divisorTail quotient
    remaining : Nat) :
    terminalStepsFrom consumed matched divisorTail quotient remaining ≤
      10 * (remaining + 1) *
        (consumed + matched + remaining + divisorTail + quotient + 1) := by
  induction remaining generalizing matched with
  | zero =>
      simp [terminalStepsFrom, terminalCleanupSteps]
      omega
  | succ remaining ih =>
      let measure := consumed + matched + (remaining + 1) + divisorTail +
        quotient + 1
      have hTail := ih (matched := matched + 1)
      have hMeasure :
          consumed + (matched + 1) + remaining + divisorTail + quotient + 1 =
            measure := by
        dsimp [measure]
        omega
      rw [hMeasure] at hTail
      have hPair : pairSteps consumed matched remaining ≤ 10 * measure := by
        simp [pairSteps, measure]
        omega
      simp only [terminalStepsFrom]
      calc
        pairSteps consumed matched remaining +
            terminalStepsFrom consumed (matched + 1) divisorTail quotient
              remaining ≤
          10 * measure + 10 * (remaining + 1) * measure :=
            Nat.add_le_add hPair hTail
        _ = 10 * (remaining + 2) * measure := by
          rw [show remaining + 2 = 1 + (remaining + 1) by omega]
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]

theorem divisionStepsFrom_le (consumed remainder divisorTail quotient
    cycles : Nat) :
    let width := remainder + divisorTail + 1
    divisionStepsFrom consumed remainder divisorTail quotient cycles ≤
      10 * (cycles * width + remainder + 1) *
        (consumed + cycles * width + remainder + divisorTail + quotient +
          cycles + 1) := by
  let width := remainder + divisorTail + 1
  induction cycles generalizing consumed quotient with
  | zero =>
      simpa [divisionStepsFrom, width, Nat.add_assoc] using
        terminalStepsFrom_le consumed 0 divisorTail quotient remainder
  | succ cycles ih =>
      let measure := consumed + (cycles + 1) * width + remainder +
        divisorTail + quotient + (cycles + 1) + 1
      have hPass := passSteps_le consumed 0
        (cycles * width + remainder) quotient width
      have hPassMeasure :
          consumed + 0 + width + (cycles * width + remainder) + quotient + 1 ≤
            measure := by
        dsimp [measure]
        rw [Nat.succ_mul]
        omega
      have hPassBound :
          passSteps consumed 0 (cycles * width + remainder) quotient width ≤
            10 * width * measure :=
        Nat.le_trans hPass
          (Nat.mul_le_mul_left (10 * width) hPassMeasure)
      have hTail := ih (consumed := consumed + width)
        (quotient := quotient + 1)
      dsimp only at hTail ⊢
      have hMeasure :
          consumed + width + cycles * width + remainder + divisorTail +
              (quotient + 1) + cycles + 1 = measure := by
        dsimp [measure]
        rw [Nat.succ_mul]
        omega
      rw [hMeasure] at hTail
      simp only [divisionStepsFrom]
      calc
        passSteps consumed 0 (cycles * width + remainder) quotient width +
            divisionStepsFrom (consumed + width) remainder divisorTail
              (quotient + 1) cycles ≤
          10 * width * measure +
            10 * (cycles * width + remainder + 1) * measure :=
              Nat.add_le_add hPassBound hTail
        _ = 10 * ((cycles + 1) * width + remainder + 1) * measure := by
          rw [Nat.succ_mul]
          simp [Nat.mul_add, Nat.add_mul, Nat.mul_assoc,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          omega
/-- A concrete quadratic bound in the unary encoded input size. In particular,
the literal divider does not hide subset, support, payload, or implementation
enumeration. -/
theorem workSteps_le_quadratic (dividend width : Nat) (hWidth : 0 < width) :
    workSteps dividend width ≤
      20 * (dividend + width + 1) * (dividend + width + 1) := by
  let remainder := dividend % width
  let divisorTail := rawDivisorTail dividend width
  let quotient := dividend / width
  have hRunBound := divisionStepsFrom_le 0 remainder divisorTail 0 quotient
  dsimp only at hRunBound
  have hWidthDecomposition := rawDivisorTail_spec dividend width hWidth
  have hDividend := quotient_remainder_reconstruct dividend width
  dsimp [remainder, divisorTail, quotient] at hRunBound
  rw [hWidthDecomposition] at hRunBound
  rw [hDividend] at hRunBound
  simp only [Nat.zero_add] at hRunBound
  rw [hDividend] at hRunBound
  have hRemainder := Nat.mod_lt dividend hWidth
  have hTail : rawDivisorTail dividend width ≤ width := by
    simp only [rawDivisorTail]
    omega
  have hQuotient : dividend / width ≤ dividend :=
    Nat.div_le_self dividend width
  let size := dividend + width + 1
  have hFirst : dividend + 1 ≤ size := by
    dsimp [size]
    omega
  have hSecond :
      dividend + rawDivisorTail dividend width + dividend / width + 1 ≤
        2 * size := by
    dsimp [size]
    omega
  have hProduct := Nat.mul_le_mul hFirst hSecond
  have hScaled := Nat.mul_le_mul_left 10 hProduct
  calc
    workSteps dividend width ≤
        10 * (dividend + 1) *
          (dividend + rawDivisorTail dividend width + dividend / width + 1) := by
            simpa [workSteps] using hRunBound
    _ ≤ 10 * (size * (2 * size)) := by
      simpa [Nat.mul_assoc] using hScaled
    _ = 20 * size * size := by
      simp [Nat.mul_assoc, Nat.mul_comm]


/-! ## Exact-bound minimality -/

private theorem verdict_timeout_of_not_halted
    (configuration : WorkConfiguration)
    (hHalted : machine.isHalted configuration = false) :
    (if configuration.state == machine.acceptState then WorkVerdict.accept
     else if configuration.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  unfold WorkMachine.isHalted at hHalted
  cases hAccept : (configuration.state == machine.acceptState) with
  | true =>
      rw [hAccept] at hHalted
      contradiction
  | false =>
      cases hReject : (configuration.state == machine.rejectState) with
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
    (configuration next : WorkConfiguration)
    (hStep : workStep? machine configuration = some next) :
    machine.isHalted configuration = false := by
  cases hHalted : machine.isHalted configuration with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive (dividend width : Nat)
    (hWidth : 0 < width) : 0 < workSteps dividend width := by
  cases hSteps : workSteps dividend width with
  | zero =>
      have hExact := workRunExact dividend width hWidth
      rw [hSteps] at hExact
      have hEqual :
          workStartConfiguration machine (inputTape dividend width) =
            finalConfiguration dividend width := Option.some.inj hExact
      have hState := congrArg WorkConfiguration.state hEqual
      simp [workStartConfiguration, machine, finalConfiguration,
        terminalConfiguration] at hState
  | succ steps =>
      omega



/-- The fixed divider is not already halted one work transition before its
certified endpoint. -/
theorem work_one_step_short_timeout (dividend width : Nat)
    (hWidth : 0 < width) :
    workBoundedDecide machine (workSteps dividend width - 1)
        (inputTape dividend width) = .timeout := by
  let short := workSteps dividend width - 1
  let initial := workStartConfiguration machine (inputTape dividend width)
  let final := finalConfiguration dividend width
  have hSucc : short + 1 = workSteps dividend width := by
    dsimp [short]
    have hPositive := workSteps_positive dividend width hWidth
    omega
  have hExact := workRunExact dividend width hWidth
  change workRunExact? machine (workSteps dividend width) initial =
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

/-! ## M210 semantic coordinate linkage -/

/-- Whenever M210 decodes a body route, the raw divider's terminal quotient
and remainder are exactly the same typed clause and token coordinates. -/
theorem final_quotient_remainder_eq_body_coordinates {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    terminalQuotientRemainder
        (finalConfiguration index problem.formulaTokensPerClause) =
      (clauseCoordinate.val, tokenCoordinate.val) := by
  have hReconstruct := postHeaderRoute_body_reconstruct problem index
    clauseCoordinate tokenCoordinate hRoute
  have hLower :
      clauseCoordinate.val * problem.formulaTokensPerClause ≤ index := by
    omega
  have hUpper :
      index < (clauseCoordinate.val + 1) *
        problem.formulaTokensPerClause := by
    rw [Nat.succ_mul]
    omega
  have hQuotient :
      index / problem.formulaTokensPerClause = clauseCoordinate.val :=
    Nat.div_eq_of_lt_le hLower hUpper
  have hNatural := quotient_remainder_reconstruct index
    problem.formulaTokensPerClause
  have hRemainder :
      index % problem.formulaTokensPerClause = tokenCoordinate.val := by
    rw [hQuotient] at hNatural
    omega
  simp [final_quotient_remainder, hQuotient, hRemainder]

/-- Public checked endpoint connecting the exact fixed-machine execution to
M210's all-coordinate semantic decoder. -/
theorem workRunExact_body_coordinates {language : Language}
    (problem : VerifierTableauProblem language) (index : Nat)
    (clauseCoordinate : Fin problem.formulaClauseSlotCount)
    (tokenCoordinate : Fin problem.formulaTokensPerClause)
    (hRoute : postHeaderRoute problem index =
      .body clauseCoordinate tokenCoordinate) :
    workRunExact? machine
          (workSteps index problem.formulaTokensPerClause)
          (workStartConfiguration machine
            (inputTape index problem.formulaTokensPerClause)) =
        some (finalConfiguration index problem.formulaTokensPerClause) ∧
      terminalQuotientRemainder
          (finalConfiguration index problem.formulaTokensPerClause) =
        (clauseCoordinate.val, tokenCoordinate.val) := by
  have hWidth : 0 < problem.formulaTokensPerClause := by
    have hTokenLt := tokenCoordinate.isLt
    omega
  exact ⟨workRunExact index problem.formulaTokensPerClause hWidth,
    final_quotient_remainder_eq_body_coordinates problem index
      clauseCoordinate tokenCoordinate hRoute⟩

/-- One reviewed endpoint for the fixed table, all-input exact trace, decoded
arithmetic, explicit polynomial bound, timeout minimality, malformed-width
boundary, compiled simulation, and M210 semantic linkage. -/
theorem cook_levin_builder_post_header_raw_divider_checked_complete :
    rules.length = 99 ∧
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (∀ dividend width, 0 < width →
      workRunExact? machine (workSteps dividend width)
          (workStartConfiguration machine (inputTape dividend width)) =
        some (finalConfiguration dividend width)) ∧
    (∀ dividend width,
      terminalQuotientRemainder (finalConfiguration dividend width) =
        (dividend / width, dividend % width)) ∧
    (∀ dividend width, 0 < width →
      (dividend / width) * width + dividend % width = dividend ∧
      dividend % width < width ∧
      workSteps dividend width ≤
        20 * (dividend + width + 1) * (dividend + width + 1) ∧
      run (compileWorkMachine machine) (6 * workSteps dividend width)
          (encodeWorkConfiguration
            (workStartConfiguration machine (inputTape dividend width))) =
        encodeWorkConfiguration (finalConfiguration dividend width) ∧
      workBoundedDecide machine (workSteps dividend width - 1)
          (inputTape dividend width) = .timeout) ∧
    (∀ dividend, divide? dividend 0 = none) ∧
    (∀ {language : Language} (problem : VerifierTableauProblem language)
      (index : Nat)
      (clauseCoordinate : Fin problem.formulaClauseSlotCount)
      (tokenCoordinate : Fin problem.formulaTokensPerClause),
      postHeaderRoute problem index = .body clauseCoordinate tokenCoordinate →
      workRunExact? machine
            (workSteps index problem.formulaTokensPerClause)
            (workStartConfiguration machine
              (inputTape index problem.formulaTokensPerClause)) =
          some (finalConfiguration index problem.formulaTokensPerClause) ∧
        terminalQuotientRemainder
            (finalConfiguration index problem.formulaTokensPerClause) =
          (clauseCoordinate.val, tokenCoordinate.val)) := by
  refine ⟨rules_length, rules_pairwise_query_distinct, ?_, ?_, ?_, ?_, ?_⟩
  · intro dividend width hWidth
    exact workRunExact dividend width hWidth
  · intro dividend width
    exact final_quotient_remainder dividend width
  · intro dividend width hWidth
    exact ⟨quotient_remainder_reconstruct dividend width,
      remainder_lt_width dividend width hWidth,
      workSteps_le_quadratic dividend width hWidth,
      run_compile_exact dividend width hWidth,
      work_one_step_short_timeout dividend width hWidth⟩
  · intro dividend
    exact divide?_zero dividend
  · intro language problem index clauseCoordinate tokenCoordinate hRoute
    exact workRunExact_body_coordinates problem index clauseCoordinate
      tokenCoordinate hRoute

end BuilderPostHeaderRawDivider

end CookLevin

end PNP.Concrete
