/-
Copyright (c) 2026 PNP Labs.

A literal input-length tally stage for the concrete Cook--Levin builder.

The machine in this file starts from the existing boundary-framed raw input,
uses only finite work-machine rules, appends one unary tally symbol per source
bit beyond the right boundary, restores every source bit, and returns to the
logical input head.  It is an internal builder stage, not a formula builder,
slot interpreter, polynomial reduction, or complexity-class result.
-/

import PNP.Concrete.PipelineInputFramer

namespace PNP.Concrete

namespace CookLevin

namespace BuilderInputLength

open PipelineTape

/-! ### Literal symbols, states, and rules -/

/-- Temporary mark for a processed zero source bit. -/
def markedZeroSymbol : WorkSymbol := WorkSymbol.zeroZero

/-- Temporary mark for a processed one source bit. -/
def markedOneSymbol : WorkSymbol := WorkSymbol.oneZero

/-- One cell of the unary source-length tally. -/
def tallySymbol : WorkSymbol := WorkSymbol.oneOne

def scanState : Nat := 0
def seekRightState : Nat := 1
def seekTallyEndState : Nat := 2
def returnTallyState : Nat := 3
def seekMarkedState : Nat := 4
def rewindState : Nat := 5
def emptyFinishState : Nat := 6
def acceptState : Nat := 7
def rejectState : Nat := 8

def keepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := read
    move := move }

def writeRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

/-- The fixed 19-rule input-length tally program.  Unexpected internal symbols
have no matching rule, so corrupted workspaces stop rather than falling
through to acceptance. -/
def rules : List WorkRule :=
  [writeRule scanState WorkSymbol.zeroBlank seekRightState
      markedZeroSymbol .right,
   writeRule scanState WorkSymbol.oneBlank seekRightState
      markedOneSymbol .right,
   keepRule scanState rightMarker rewindState .left,
   keepRule scanState WorkSymbol.blank emptyFinishState .stay,
   keepRule emptyFinishState WorkSymbol.blank acceptState .stay,
   keepRule seekRightState WorkSymbol.zeroBlank seekRightState .right,
   keepRule seekRightState WorkSymbol.oneBlank seekRightState .right,
   keepRule seekRightState rightMarker seekTallyEndState .right,
   keepRule seekTallyEndState tallySymbol seekTallyEndState .right,
   writeRule seekTallyEndState WorkSymbol.blank returnTallyState
      tallySymbol .left,
   keepRule returnTallyState tallySymbol returnTallyState .left,
   keepRule returnTallyState rightMarker seekMarkedState .left,
   keepRule seekMarkedState WorkSymbol.zeroBlank seekMarkedState .left,
   keepRule seekMarkedState WorkSymbol.oneBlank seekMarkedState .left,
   writeRule seekMarkedState markedZeroSymbol scanState
      WorkSymbol.zeroBlank .right,
   writeRule seekMarkedState markedOneSymbol scanState
      WorkSymbol.oneBlank .right,
   keepRule rewindState WorkSymbol.zeroBlank rewindState .left,
   keepRule rewindState WorkSymbol.oneBlank rewindState .left,
   keepRule rewindState leftMarker acceptState .right]

/-- Literal finite work machine for the input-length tally stage. -/
def machine : WorkMachine :=
  { rules := rules
    startState := scanState
    acceptState := acceptState
    rejectState := rejectState }

theorem rules_length : rules.length = 19 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem markedZeroSymbol_ne_markedOneSymbol :
    markedZeroSymbol ≠ markedOneSymbol := by
  intro h
  have hFirst := congrArg WorkSymbol.first h
  contradiction

theorem tallySymbol_ne_markedZeroSymbol :
    tallySymbol ≠ markedZeroSymbol := by
  intro h
  have hFirst := congrArg WorkSymbol.first h
  contradiction

theorem tallySymbol_ne_markedOneSymbol :
    tallySymbol ≠ markedOneSymbol := by
  intro h
  have hSecond := congrArg WorkSymbol.second h
  contradiction

/-! ### Canonical framed input and endpoint -/

/-- The stage accepts the canonical pipeline frame with fresh right-side
workspace and arbitrary already-isolated garbage beyond the left marker. -/
def inputTape (input : BitString) (outsideLeft : List WorkSymbol) : WorkTape :=
  frameWithGarbage (Tape.ofInput input) outsideLeft []

/-- Exact endpoint: the raw input is restored and `input.length` unary tally
symbols occupy the fresh workspace beyond the right marker. -/
def finalTape (input : BitString) (outsideLeft : List WorkSymbol) : WorkTape :=
  frameWithGarbage (Tape.ofInput input) outsideLeft
    (List.replicate input.length tallySymbol)

def finalConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape input outsideLeft }

theorem finalTape_represents (input : BitString)
    (outsideLeft : List WorkSymbol) :
    Represents (Tape.ofInput input) (finalTape input outsideLeft) := by
  exact frameWithGarbage_represents _ _ _

theorem finalTape_tally_length (input : BitString)
    (_outsideLeft : List WorkSymbol) :
    (List.replicate input.length tallySymbol).length = input.length := by
  simp

/-- Exact number of work transitions on a source word of length `n`. -/
def workSteps (n : Nat) : Nat :=
  2 * n * n + 4 * n + 2

/-- Six raw compiler transitions per work transition, expressed only in the
external encoded input length. -/
def rawTimeBound : NatPolynomial :=
  .add (.quadratic 12 12) (.linear 24 0)

/-- The tally occupies exactly the external source length. -/
def tallySizeBound : NatPolynomial := .variable

theorem tallySizeBound_exact (input : BitString) :
    tallySizeBound.eval (BitString.size input) = input.length := by
  rfl

/-- A source-start cell carrying the one unused work symbol has no transition;
every fuel budget therefore reports timeout rather than acceptance. -/
theorem malformedScanSymbol_timeout (fuel : Nat)
    (leftSide rightSide : List WorkSymbol) :
    workBoundedDecide machine fuel
        { left := leftSide
          head := WorkSymbol.zeroOne
          right := rightSide } = .timeout := by
  let config := workStartConfiguration machine
    { left := leftSide
      head := WorkSymbol.zeroOne
      right := rightSide }
  have hStep : workStep? machine config = none := by rfl
  have hRun := workRun_eq_self_of_workStep?_eq_none machine config fuel hStep
  unfold workBoundedDecide
  change
    (let final := workRun machine fuel config
     if final.state == machine.acceptState then WorkVerdict.accept
     else if final.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  rfl

/-! ### Exact execution infrastructure -/

private def bitSymbol (bit : Bool) : WorkSymbol :=
  dataSymbol (TapeSymbol.ofBool bit)

private def bitSymbols (bits : BitString) : List WorkSymbol :=
  bits.map bitSymbol

private def tapeAtWord (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: rest => { left := leftSide, head := head, right := rest }

private def tapeAtLeftWord (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: rest => { left := rest, head := head, right := rightSide }

private theorem workRunExact_compose (first second : Nat)
    (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      simpa [hStart] using hSecond
  | succ first ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have hTail : workRunExact? machine first next = some middle := by
            change
              (match workStep? machine start with
               | none => none
               | some result => workRunExact? machine first result) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some result => workRunExact? machine (first + second) result) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem bitSymbols_length (bits : BitString) :
    (bitSymbols bits).length = bits.length := by
  simp [bitSymbols]

private theorem bitSymbols_append (left right : BitString) :
    bitSymbols (left ++ right) = bitSymbols left ++ bitSymbols right := by
  simp [bitSymbols]

private theorem bitSymbols_reverse (bits : BitString) :
    bitSymbols bits.reverse = (bitSymbols bits).reverse := by
  simp [bitSymbols]

private theorem replicate_succ_tail {alpha : Type} (count : Nat)
    (value : alpha) :
    List.replicate (count + 1) value =
      List.replicate count value ++ [value] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change value :: List.replicate (count + 1) value =
        value :: (List.replicate count value ++ [value])
      exact congrArg (List.cons value) ih

private theorem step_seekRight_bit (bit : Bool)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekRightState
          tape :=
            { left := leftSide
              head := bitSymbol bit
              right := rightSide } } =
      some
        { state := seekRightState
          tape := tapeAtWord (bitSymbol bit :: leftSide) rightSide } := by
  cases bit <;> rfl

private theorem seekRight_bits_exact (bits : BitString)
    (leftSide suffix : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := seekRightState
          tape := tapeAtWord leftSide (bitSymbols bits ++ suffix) } =
      some
        { state := seekRightState
          tape := tapeAtWord ((bitSymbols bits).reverse ++ leftSide) suffix } := by
  induction bits generalizing leftSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := step_seekRight_bit bit leftSide
        (bitSymbols rest ++ suffix)
      change workRunExact? machine (rest.length + 1)
          { state := seekRightState
            tape := tapeAtWord leftSide
              (bitSymbol bit :: (bitSymbols rest ++ suffix)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := seekRightState
            tape := tapeAtWord leftSide
              (bitSymbol bit :: (bitSymbols rest ++ suffix)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtWord]
      rw [hStep]
      simp only
      rw [ih (bitSymbol bit :: leftSide)]
      cases suffix <;> simp [tapeAtWord, bitSymbols]

private theorem step_seekTally (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekTallyEndState
          tape :=
            { left := leftSide
              head := tallySymbol
              right := rightSide } } =
      some
        { state := seekTallyEndState
          tape := tapeAtWord (tallySymbol :: leftSide) rightSide } := by
  rfl

private theorem seekTally_exact (count : Nat)
    (leftSide : List WorkSymbol) :
    workRunExact? machine count
        { state := seekTallyEndState
          tape := tapeAtWord leftSide
            (List.replicate count tallySymbol) } =
      some
        { state := seekTallyEndState
          tape :=
            { left := List.replicate count tallySymbol ++ leftSide
              head := WorkSymbol.blank
              right := [] } } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hStep := step_seekTally leftSide
        (List.replicate count tallySymbol)
      change
        (match workStep? machine
          { state := seekTallyEndState
            tape := tapeAtWord leftSide
              (tallySymbol :: List.replicate count tallySymbol) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      simp only [tapeAtWord]
      rw [hStep]
      simp only
      rw [ih (tallySymbol :: leftSide)]
      rw [replicate_succ_tail]
      simp [List.append_assoc]

private theorem step_returnTally (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := returnTallyState
          tape :=
            { left := leftSide
              head := tallySymbol
              right := rightSide } } =
      some
        { state := returnTallyState
          tape := tapeAtLeftWord (tallySymbol :: rightSide) leftSide } := by
  rfl

private theorem returnTally_exact (count : Nat)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine count
        { state := returnTallyState
          tape := tapeAtLeftWord rightSide
            (List.replicate count tallySymbol ++ leftSide) } =
      some
        { state := returnTallyState
          tape := tapeAtLeftWord
            (List.replicate count tallySymbol ++ rightSide) leftSide } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      have hStep := step_returnTally
        (List.replicate count tallySymbol ++ leftSide) rightSide
      change
        (match workStep? machine
          { state := returnTallyState
            tape := tapeAtLeftWord rightSide
              (tallySymbol ::
                (List.replicate count tallySymbol ++ leftSide)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (tallySymbol :: rightSide)]
      rw [replicate_succ_tail]
      cases leftSide <;> simp [tapeAtLeftWord, List.append_assoc]

private theorem step_seekMarked_bit (bit : Bool)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekMarkedState
          tape :=
            { left := leftSide
              head := bitSymbol bit
              right := rightSide } } =
      some
        { state := seekMarkedState
          tape := tapeAtLeftWord (bitSymbol bit :: rightSide) leftSide } := by
  cases bit <;> rfl

private theorem seekMarked_scan_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := seekMarkedState
          tape := tapeAtLeftWord rightSide
            (bitSymbols bits ++ leftSide) } =
      some
        { state := seekMarkedState
          tape := tapeAtLeftWord
            (bitSymbols bits.reverse ++ rightSide) leftSide } := by
  induction bits generalizing rightSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := step_seekMarked_bit bit
        (bitSymbols rest ++ leftSide) rightSide
      change workRunExact? machine (rest.length + 1)
          { state := seekMarkedState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := seekMarkedState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (bitSymbol bit :: rightSide)]
      cases leftSide <;>
        simp [tapeAtLeftWord, bitSymbols, List.append_assoc]

private theorem seekMarked_bits_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := seekMarkedState
          tape := tapeAtLeftWord rightSide
            (bitSymbols bits.reverse ++ leftSide) } =
      some
        { state := seekMarkedState
          tape := tapeAtLeftWord
            (bitSymbols bits ++ rightSide) leftSide } := by
  simpa [bitSymbols_length] using
    (seekMarked_scan_exact bits.reverse leftSide rightSide)

private theorem step_rewind_bit (bit : Bool)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindState
          tape :=
            { left := leftSide
              head := bitSymbol bit
              right := rightSide } } =
      some
        { state := rewindState
          tape := tapeAtLeftWord (bitSymbol bit :: rightSide) leftSide } := by
  cases bit <;> rfl

private theorem rewind_scan_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := rewindState
          tape := tapeAtLeftWord rightSide
            (bitSymbols bits ++ leftSide) } =
      some
        { state := rewindState
          tape := tapeAtLeftWord
            (bitSymbols bits.reverse ++ rightSide) leftSide } := by
  induction bits generalizing rightSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := step_rewind_bit bit
        (bitSymbols rest ++ leftSide) rightSide
      change workRunExact? machine (rest.length + 1)
          { state := rewindState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := rewindState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (bitSymbol bit :: rightSide)]
      cases leftSide <;>
        simp [tapeAtLeftWord, bitSymbols, List.append_assoc]

private theorem rewind_bits_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := rewindState
          tape := tapeAtLeftWord rightSide
            (bitSymbols bits.reverse ++ leftSide) } =
      some
        { state := rewindState
          tape := tapeAtLeftWord
            (bitSymbols bits ++ rightSide) leftSide } := by
  simpa [bitSymbols_length] using
    (rewind_scan_exact bits.reverse leftSide rightSide)

private def loopTape (done todo : BitString)
    (outsideLeft : List WorkSymbol) : WorkTape :=
  match todo with
  | [] =>
      { left := bitSymbols done.reverse ++ leftMarker :: outsideLeft
        head := rightMarker
        right := List.replicate done.length tallySymbol }
  | current :: rest =>
      { left := bitSymbols done.reverse ++ leftMarker :: outsideLeft
        head := bitSymbol current
        right := bitSymbols rest ++ rightMarker ::
          List.replicate done.length tallySymbol }

private def loopConfiguration (done todo : BitString)
    (outsideLeft : List WorkSymbol) : WorkConfiguration :=
  { state := scanState
    tape := loopTape done todo outsideLeft }

private def markedSymbol (bit : Bool) : WorkSymbol :=
  if bit then markedOneSymbol else markedZeroSymbol

private theorem step_mark (done rest : BitString) (current : Bool)
    (outsideLeft : List WorkSymbol) :
    workStep? machine (loopConfiguration done (current :: rest) outsideLeft) =
      some
        { state := seekRightState
          tape := tapeAtWord
            (markedSymbol current ::
              bitSymbols done.reverse ++ leftMarker :: outsideLeft)
            (bitSymbols rest ++ rightMarker ::
              List.replicate done.length tallySymbol) } := by
  cases current <;> rfl

private theorem step_rightMarker (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekRightState
          tape :=
            { left := leftSide
              head := rightMarker
              right := rightSide } } =
      some
        { state := seekTallyEndState
          tape := tapeAtWord (rightMarker :: leftSide) rightSide } := by
  rfl

private theorem step_appendTally (leftSide : List WorkSymbol) :
    workStep? machine
        { state := seekTallyEndState
          tape :=
            { left := leftSide
              head := WorkSymbol.blank
              right := [] } } =
      some
        { state := returnTallyState
          tape := tapeAtLeftWord [tallySymbol] leftSide } := by
  rfl

private theorem step_returnMarker (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := returnTallyState
          tape :=
            { left := leftSide
              head := rightMarker
              right := rightSide } } =
      some
        { state := seekMarkedState
          tape := tapeAtLeftWord (rightMarker :: rightSide) leftSide } := by
  rfl

private theorem step_restore (done : BitString) (current : Bool)
    (outsideLeft rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekMarkedState
          tape :=
            { left := bitSymbols done.reverse ++ leftMarker :: outsideLeft
              head := markedSymbol current
              right := rightSide } } =
      some
        { state := scanState
          tape := tapeAtWord
            (bitSymbol current ::
              bitSymbols done.reverse ++ leftMarker :: outsideLeft)
            rightSide } := by
  cases current <;> rfl

private theorem one_iteration_exact (done rest : BitString)
    (current : Bool) (outsideLeft : List WorkSymbol) :
    workRunExact? machine
        (2 * rest.length + 2 * done.length + 5)
        (loopConfiguration done (current :: rest) outsideLeft) =
      some (loopConfiguration (done ++ [current]) rest outsideLeft) := by
  let baseLeft := bitSymbols done.reverse ++ leftMarker :: outsideLeft
  let markedLeft := markedSymbol current :: baseLeft
  let reversedRest := (bitSymbols rest).reverse
  let tallies := List.replicate done.length tallySymbol
  let nextTallies := tallies ++ [tallySymbol]
  let c0 := loopConfiguration done (current :: rest) outsideLeft
  let c1 : WorkConfiguration :=
    { state := seekRightState
      tape := tapeAtWord markedLeft
        (bitSymbols rest ++ rightMarker :: tallies) }
  let c2 : WorkConfiguration :=
    { state := seekRightState
      tape := tapeAtWord (reversedRest ++ markedLeft)
        (rightMarker :: tallies) }
  let c3 : WorkConfiguration :=
    { state := seekTallyEndState
      tape := tapeAtWord
        (rightMarker :: reversedRest ++ markedLeft) tallies }
  let c4 : WorkConfiguration :=
    { state := seekTallyEndState
      tape :=
        { left := tallies ++ rightMarker :: reversedRest ++ markedLeft
          head := WorkSymbol.blank
          right := [] } }
  let c5 : WorkConfiguration :=
    { state := returnTallyState
      tape := tapeAtLeftWord [tallySymbol]
        (tallies ++ rightMarker :: reversedRest ++ markedLeft) }
  let c6 : WorkConfiguration :=
    { state := returnTallyState
      tape := tapeAtLeftWord nextTallies
        (rightMarker :: reversedRest ++ markedLeft) }
  let c7 : WorkConfiguration :=
    { state := seekMarkedState
      tape := tapeAtLeftWord (rightMarker :: nextTallies)
        (reversedRest ++ markedLeft) }
  let c8 : WorkConfiguration :=
    { state := seekMarkedState
      tape := tapeAtLeftWord
        (bitSymbols rest ++ rightMarker :: nextTallies) markedLeft }
  let c9 : WorkConfiguration :=
    { state := scanState
      tape := tapeAtWord (bitSymbol current :: baseLeft)
        (bitSymbols rest ++ rightMarker :: nextTallies) }
  have h0 : c0 = loopConfiguration done (current :: rest) outsideLeft := rfl
  have hMark : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    dsimp [c0, c1, markedLeft, baseLeft, tallies]
    exact step_mark done rest current outsideLeft
  have hSeekRight : workRunExact? machine rest.length c1 = some c2 := by
    dsimp [c1, c2, markedLeft, reversedRest, tallies]
    exact seekRight_bits_exact rest _ _
  have hRightMarker : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    dsimp [c2, c3, markedLeft, reversedRest, tallies]
    exact step_rightMarker _ _
  have hSeekTally : workRunExact? machine done.length c3 = some c4 := by
    dsimp [c3, c4, markedLeft, reversedRest, tallies]
    simpa [List.append_assoc] using
      (seekTally_exact done.length
        (rightMarker :: (bitSymbols rest).reverse ++
          markedSymbol current :: baseLeft))
  have hAppend : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    dsimp [c4, c5, markedLeft, reversedRest, tallies]
    exact step_appendTally _
  have hReturn : workRunExact? machine done.length c5 = some c6 := by
    dsimp [c5, c6, markedLeft, reversedRest, tallies, nextTallies]
    simpa [List.append_assoc] using
      (returnTally_exact done.length
        (rightMarker :: (bitSymbols rest).reverse ++
          markedSymbol current :: baseLeft) [tallySymbol])
  have hReturnMarker : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    dsimp [c6, c7, markedLeft, reversedRest, tallies, nextTallies]
    exact step_returnMarker _ _
  have hSeekMarked : workRunExact? machine rest.length c7 = some c8 := by
    dsimp [c7, c8, markedLeft, reversedRest, tallies, nextTallies]
    rw [← bitSymbols_reverse rest]
    exact seekMarked_bits_exact rest _ _
  have hRestore : workRunExact? machine 1 c8 = some c9 := by
    apply workRunExact_one
    dsimp [c8, c9, markedLeft, baseLeft, reversedRest, tallies,
      nextTallies]
    exact step_restore done current outsideLeft _
  have h01 := workRunExact_compose 1 rest.length c0 c1 c2
    hMark hSeekRight
  have h03 := workRunExact_compose (1 + rest.length) 1 c0 c2 c3
    h01 hRightMarker
  have h04 := workRunExact_compose (1 + rest.length + 1) done.length
    c0 c3 c4 h03 hSeekTally
  have h05 := workRunExact_compose
    (1 + rest.length + 1 + done.length) 1 c0 c4 c5 h04 hAppend
  have h06 := workRunExact_compose
    (1 + rest.length + 1 + done.length + 1) done.length
    c0 c5 c6 h05 hReturn
  have h07 := workRunExact_compose
    (1 + rest.length + 1 + done.length + 1 + done.length) 1
    c0 c6 c7 h06 hReturnMarker
  have h08 := workRunExact_compose
    (1 + rest.length + 1 + done.length + 1 + done.length + 1)
    rest.length c0 c7 c8 h07 hSeekMarked
  have h09 := workRunExact_compose
    (1 + rest.length + 1 + done.length + 1 + done.length + 1 +
      rest.length) 1 c0 c8 c9 h08 hRestore
  have hSteps :
      1 + rest.length + 1 + done.length + 1 + done.length + 1 +
          rest.length + 1 =
        2 * rest.length + 2 * done.length + 5 := by
    omega
  rw [hSteps] at h09
  rw [h0] at h09
  have hFinal : c9 =
      loopConfiguration (done ++ [current]) rest outsideLeft := by
    dsimp [c9, baseLeft, nextTallies, tallies, loopConfiguration, loopTape]
    rw [← replicate_succ_tail]
    cases rest with
    | nil =>
        simp [tapeAtWord, bitSymbols]
    | cons next tail =>
        simp [tapeAtWord, bitSymbols]
  rw [hFinal] at h09
  exact h09

private def remainingSteps (done todo : BitString) : Nat :=
  todo.length * (2 * (done.length + todo.length) + 3)

private theorem loop_exact (done todo : BitString)
    (outsideLeft : List WorkSymbol) :
    workRunExact? machine (remainingSteps done todo)
        (loopConfiguration done todo outsideLeft) =
      some (loopConfiguration (done ++ todo) [] outsideLeft) := by
  induction todo generalizing done with
  | nil =>
      rw [show remainingSteps done [] = 0 by simp [remainingSteps]]
      rw [List.append_nil]
      change workRunExact? machine 0
          (loopConfiguration done [] outsideLeft) =
        some (loopConfiguration done [] outsideLeft)
      rfl
  | cons current rest ih =>
      have hFirst := one_iteration_exact done rest current outsideLeft
      have hSecond := ih (done ++ [current])
      have hComposed := workRunExact_compose
        (2 * rest.length + 2 * done.length + 5)
        (remainingSteps (done ++ [current]) rest)
        (loopConfiguration done (current :: rest) outsideLeft)
        (loopConfiguration (done ++ [current]) rest outsideLeft)
        (loopConfiguration ((done ++ [current]) ++ rest) [] outsideLeft)
        hFirst hSecond
      let width := 2 * (done.length + (current :: rest).length) + 3
      have hIteration :
          2 * rest.length + 2 * done.length + 5 = width := by
        dsimp [width]
        omega
      have hNextWidth :
          2 * ((done ++ [current]).length + rest.length) + 3 = width := by
        dsimp [width]
        simp only [List.length_append, List.length_singleton]
        omega
      have hSteps :
          (2 * rest.length + 2 * done.length + 5) +
              remainingSteps (done ++ [current]) rest =
            remainingSteps done (current :: rest) := by
        unfold remainingSteps
        rw [hIteration, hNextWidth]
        change width + rest.length * width =
          Nat.succ rest.length * width
        rw [Nat.succ_mul]
        exact Nat.add_comm _ _
      rw [hSteps] at hComposed
      simpa [List.append_assoc] using hComposed

private theorem inputTape_eq_loopTape (first : Bool) (rest : BitString)
    (outsideLeft : List WorkSymbol) :
    inputTape (first :: rest) outsideLeft =
      loopTape [] (first :: rest) outsideLeft := by
  cases first <;>
    simp [inputTape, loopTape, frameWithGarbage, Tape.ofInput,
      bitSymbols, bitSymbol, List.map_map, Function.comp_def]

private theorem finalTape_cons_eq (first : Bool) (rest : BitString)
    (outsideLeft : List WorkSymbol) :
    finalTape (first :: rest) outsideLeft =
      { left := leftMarker :: outsideLeft
        head := bitSymbol first
        right := bitSymbols rest ++ rightMarker ::
          List.replicate (first :: rest).length tallySymbol } := by
  cases first <;>
    simp [finalTape, frameWithGarbage, Tape.ofInput,
      bitSymbols, bitSymbol, List.map_map, Function.comp_def]

private theorem step_beginRewind (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workStep? machine (loopConfiguration input [] outsideLeft) =
      some
        { state := rewindState
          tape := tapeAtLeftWord
            (rightMarker :: List.replicate input.length tallySymbol)
            (bitSymbols input.reverse ++ leftMarker :: outsideLeft) } := by
  rfl

private theorem step_finishRewind (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindState
          tape :=
            { left := leftSide
              head := leftMarker
              right := rightSide } } =
      some
        { state := acceptState
          tape := tapeAtWord (leftMarker :: leftSide) rightSide } := by
  rfl

private theorem finish_nonempty_exact (input : BitString)
    (outsideLeft : List WorkSymbol) (hInput : input ≠ []) :
    workRunExact? machine (input.length + 2)
        (loopConfiguration input [] outsideLeft) =
      some (finalConfiguration input outsideLeft) := by
  let c0 := loopConfiguration input [] outsideLeft
  let c1 : WorkConfiguration :=
    { state := rewindState
      tape := tapeAtLeftWord
        (rightMarker :: List.replicate input.length tallySymbol)
        (bitSymbols input.reverse ++ leftMarker :: outsideLeft) }
  let c2 : WorkConfiguration :=
    { state := rewindState
      tape := tapeAtLeftWord
        (bitSymbols input ++ rightMarker ::
          List.replicate input.length tallySymbol)
        (leftMarker :: outsideLeft) }
  let c3 : WorkConfiguration := finalConfiguration input outsideLeft
  have hBegin : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    dsimp [c0, c1]
    exact step_beginRewind input outsideLeft
  have hRewind : workRunExact? machine input.length c1 = some c2 := by
    dsimp [c1, c2]
    exact rewind_bits_exact input _ _
  have hFinish : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    cases input with
    | nil => exact False.elim (hInput rfl)
    | cons first rest =>
        dsimp [c2, c3]
        unfold finalConfiguration
        have hStep := step_finishRewind outsideLeft
          (bitSymbols (first :: rest) ++ rightMarker ::
            List.replicate (first :: rest).length tallySymbol)
        have hFinal := finalTape_cons_eq first rest outsideLeft
        rw [hFinal]
        cases first <;>
          simpa [machine, tapeAtLeftWord, tapeAtWord, bitSymbols] using hStep
  have hFirst := workRunExact_compose 1 input.length c0 c1 c2
    hBegin hRewind
  have hAll := workRunExact_compose (1 + input.length) 1 c0 c2 c3
    hFirst hFinish
  have hSteps : 1 + input.length + 1 = input.length + 2 := by omega
  rw [hSteps] at hAll
  exact hAll

/-- The fixed finite stage handles every source word and reaches the restored
frame with an exact unary length tally in `2*n*n + 4*n + 2` work steps. -/
theorem workRunExact (input : BitString) (outsideLeft : List WorkSymbol) :
    workRunExact? machine (workSteps input.length)
        (workStartConfiguration machine (inputTape input outsideLeft)) =
      some (finalConfiguration input outsideLeft) := by
  cases input with
  | nil => rfl
  | cons first rest =>
      rw [inputTape_eq_loopTape]
      change workRunExact? machine (workSteps (first :: rest).length)
          (loopConfiguration [] (first :: rest) outsideLeft) =
        some (finalConfiguration (first :: rest) outsideLeft)
      have hLoop := loop_exact [] (first :: rest) outsideLeft
      have hFinish := finish_nonempty_exact (first :: rest) outsideLeft
        (by intro impossible; contradiction)
      have hAll := workRunExact_compose
        (remainingSteps [] (first :: rest)) ((first :: rest).length + 2)
        (loopConfiguration [] (first :: rest) outsideLeft)
        (loopConfiguration (first :: rest) [] outsideLeft)
        (finalConfiguration (first :: rest) outsideLeft)
        hLoop hFinish
      have hQuadratic :
          (first :: rest).length * (2 * (first :: rest).length) =
            2 * (first :: rest).length * (first :: rest).length := by
        calc
          (first :: rest).length * (2 * (first :: rest).length) =
              ((first :: rest).length * 2) * (first :: rest).length :=
            (Nat.mul_assoc _ _ _).symm
          _ = (2 * (first :: rest).length) * (first :: rest).length :=
            congrArg (fun value => value * (first :: rest).length)
              (Nat.mul_comm _ 2)
      have hThree : (first :: rest).length * 3 =
          3 * (first :: rest).length := Nat.mul_comm _ _
      have hSteps :
          remainingSteps [] (first :: rest) +
              ((first :: rest).length + 2) =
            workSteps (first :: rest).length := by
        unfold remainingSteps workSteps
        simp only [List.length_nil, Nat.zero_add]
        rw [Nat.mul_add, hQuadratic, hThree]
        omega
      rw [hSteps] at hAll
      exact hAll

theorem finalConfiguration_isHalted (input : BitString)
    (outsideLeft : List WorkSymbol) :
    machine.isHalted (finalConfiguration input outsideLeft) = true := by
  rfl

theorem rawTimeBound_exact (input : BitString) :
    rawTimeBound.eval (BitString.size input) =
      6 * workSteps input.length := by
  simp [rawTimeBound, NatPolynomial.quadratic, NatPolynomial.linear,
    workSteps, BitString.size]
  have hQuadratic :
      6 * (2 * input.length * input.length) =
        12 * input.length * input.length := by
    rw [← Nat.mul_assoc 6 (2 * input.length) input.length,
      ← Nat.mul_assoc 6 2 input.length]
  have hLinear : 6 * (4 * input.length) = 24 * input.length := by
    rw [← Nat.mul_assoc 6 4 input.length]
  rw [Nat.mul_add, Nat.mul_add, hQuadratic, hLinear]
  omega

/-- The compiled three-symbol raw machine reaches the exact encoded endpoint
at the displayed external-size polynomial budget. -/
theorem run_compile (input : BitString) (outsideLeft : List WorkSymbol) :
    run (compileWorkMachine machine)
        (rawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine (inputTape input outsideLeft))) =
      encodeWorkConfiguration (finalConfiguration input outsideLeft) := by
  rw [rawTimeBound_exact]
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps input.length)
    (workStartConfiguration machine (inputTape input outsideLeft))
    (finalConfiguration input outsideLeft)
    (workRunExact input outsideLeft)

theorem workBoundedDecide_accept (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workBoundedDecide machine (workSteps input.length)
        (inputTape input outsideLeft) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact machine (workSteps input.length)
    (workStartConfiguration machine (inputTape input outsideLeft))
    (finalConfiguration input outsideLeft) (workRunExact input outsideLeft)]
  rfl

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

private theorem workSteps_positive (length : Nat) : 0 < workSteps length := by
  unfold workSteps
  omega

/-- Removing exactly one proved work transition leaves a nonhalting state;
the local stage times out rather than accidentally accepting or rejecting. -/
theorem work_one_step_short_timeout (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workBoundedDecide machine (workSteps input.length - 1)
        (inputTape input outsideLeft) = .timeout := by
  let short := workSteps input.length - 1
  let initial := workStartConfiguration machine (inputTape input outsideLeft)
  let final := finalConfiguration input outsideLeft
  have hSucc : short + 1 = workSteps input.length := by
    dsimp [short]
    have hPositive := workSteps_positive input.length
    omega
  have hExact := workRunExact input outsideLeft
  change workRunExact? machine (workSteps input.length) initial =
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
  cases hAccept : (before.state == machine.acceptState) with
  | true =>
      unfold WorkMachine.isHalted at hNotHalted
      rw [hAccept] at hNotHalted
      contradiction
  | false =>
      cases hReject : (before.state == machine.rejectState) with
      | true =>
          unfold WorkMachine.isHalted at hNotHalted
          rw [hAccept, hReject] at hNotHalted
          contradiction
      | false => simp [hAccept, hReject]

/-! ### Exact connection to the already-proved all-input framer endpoint -/

theorem inputTape_eq_totalInputFramerFinalTape (input : BitString) :
    inputTape input (PipelineInputFramer.totalInputFramerOutsideLeft input) =
      PipelineInputFramer.totalInputFramerFinalTape input := by
  rfl

theorem workRunExact_after_totalInputFramer (input : BitString) :
    workRunExact? machine (workSteps input.length)
        (workStartConfiguration machine
          (PipelineInputFramer.totalInputFramerFinalTape input)) =
      some (finalConfiguration input
        (PipelineInputFramer.totalInputFramerOutsideLeft input)) := by
  rw [← inputTape_eq_totalInputFramerFinalTape]
  exact workRunExact input _

end BuilderInputLength

end CookLevin

end PNP.Concrete
