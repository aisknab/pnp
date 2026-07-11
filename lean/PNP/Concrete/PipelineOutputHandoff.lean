/-
Copyright (c) 2026 PNP Labs.

Executable internal handoff inside the boundary-marked pipeline geometry.

From any work tape representing a raw tape, the finite machine below moves
both logical boundaries inward around the raw tape's blank-delimited output.
It halts with a work tape representing `Tape.handoffTarget raw`; every cell
discarded on either side remains permitted exterior garbage.

The compiled endpoint is still the ordinary two-cell encoding of a framed
work tape.  This module does not claim that raw `machineOutput` can directly
decode that interleaved representation, compose the handoff with another rule
table, reset a later machine's state, prove source-machine termination, or
construct a pipeline refinement or complexity-class equality.
-/

import PNP.Concrete.PipelineTapeGeometry

namespace PNP.Concrete

namespace PipelineOutputHandoff

open PipelineTape

/-! ### Finite control and rule table -/

def allWorkSymbols : List WorkSymbol :=
  [WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
   WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

def startState : Nat := 0
def installLeftBitState : Nat := 1
def installLeftEmptyState : Nat := 2
def scanRightState : Nat := 3
def returnLeftState : Nat := 4
def emptyMoveRightState : Nat := 5
def emptyInstallRightState : Nat := 6
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

def installLeftRules (source target : Nat) : List WorkRule :=
  allWorkSymbols.map (fun symbol =>
    writeRule source symbol target leftMarker .right)

def installRightRules (source target : Nat) : List WorkRule :=
  allWorkSymbols.map (fun symbol =>
    writeRule source symbol target rightMarker .left)

def handoffRules : List WorkRule :=
  [keepRule startState WorkSymbol.blank installLeftEmptyState .left,
   keepRule startState WorkSymbol.zeroBlank installLeftBitState .left,
   keepRule startState WorkSymbol.oneBlank installLeftBitState .left] ++
  installLeftRules installLeftBitState scanRightState ++
  installLeftRules installLeftEmptyState emptyMoveRightState ++
  [keepRule scanRightState WorkSymbol.zeroBlank scanRightState .right,
   keepRule scanRightState WorkSymbol.oneBlank scanRightState .right,
   writeRule scanRightState WorkSymbol.blank returnLeftState
      rightMarker .left,
   keepRule scanRightState rightMarker returnLeftState .left,
   keepRule returnLeftState WorkSymbol.zeroBlank returnLeftState .left,
   keepRule returnLeftState WorkSymbol.oneBlank returnLeftState .left,
   keepRule returnLeftState leftMarker acceptState .right,
   keepRule emptyMoveRightState WorkSymbol.blank
      emptyInstallRightState .right] ++
  installRightRules emptyInstallRightState acceptState

/-- A literal finite work machine implementing internal boundary handoff. -/
def framedOutputHandoff : WorkMachine :=
  { rules := handoffRules
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

/-- Exact work-transition count, measured in decoded output length. -/
def framedOutputHandoffWorkSteps (raw : Tape) : Nat :=
  2 * BitString.size raw.outputBits + 4

/-- Exact compiled raw budget, measured in decoded output length. -/
def framedOutputHandoffRawTimeBound : NatPolynomial :=
  .linear 12 24

/-! ### Private exact-run infrastructure -/

private def tapeAtWord (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: suffix => { left := leftSide, head := head, right := suffix }

private def configAtWord (state : Nat) (leftSide word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtWord leftSide word }

private def tapeAtLeftWord (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: leftTail => { left := leftTail, head := head, right := rightSide }

private def configAtLeftWord (state : Nat)
    (leftWord rightSide : List WorkSymbol) : WorkConfiguration :=
  { state := state, tape := tapeAtLeftWord rightSide leftWord }

private def pushLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], leftSide => leftSide
  | symbol :: rest, leftSide => pushLeft rest (symbol :: leftSide)

private theorem pushLeft_append_far (word left right : List WorkSymbol) :
    pushLeft word (left ++ right) = pushLeft word left ++ right := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: left)

private theorem pushLeft_append_word (first second farSide : List WorkSymbol) :
    pushLeft (first ++ second) farSide =
      pushLeft second (pushLeft first farSide) := by
  induction first generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

private theorem pushLeft_cons_far (word : List WorkSymbol)
    (symbol : WorkSymbol) :
    pushLeft word [symbol] = pushLeft word [] ++ [symbol] := by
  change pushLeft word ([] ++ [symbol]) = _
  exact pushLeft_append_far word [] [symbol]

private theorem pushLeft_cancel (word farSide : List WorkSymbol) :
    pushLeft (pushLeft word []) farSide = word ++ farSide := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      change pushLeft (pushLeft rest [symbol]) farSide =
        symbol :: (rest ++ farSide)
      rw [pushLeft_cons_far]
      rw [pushLeft_append_word]
      change symbol :: pushLeft (pushLeft rest []) farSide = _
      exact congrArg (List.cons symbol) ih

private theorem pushLeft_length (word farSide : List WorkSymbol) :
    (pushLeft word farSide).length = word.length + farSide.length := by
  induction word generalizing farSide with
  | nil => exact (Nat.zero_add farSide.length).symm
  | cons first rest ih =>
      change (pushLeft rest (first :: farSide)).length =
        Nat.succ rest.length + farSide.length
      rw [ih]
      rw [Nat.succ_add]
      exact Nat.add_succ rest.length farSide.length

private theorem pushLeft_property (Property : WorkSymbol → Prop)
    (word farSide : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → Property symbol)
    (hFar : ∀ symbol, List.Mem symbol farSide → Property symbol) :
    ∀ symbol, List.Mem symbol (pushLeft word farSide) → Property symbol := by
  induction word generalizing farSide with
  | nil => exact hFar
  | cons first rest ih =>
      apply ih (first :: farSide)
      · intro symbol found
        exact hWord symbol (List.Mem.tail first found)
      · intro symbol found
        cases found with
        | head => exact hWord first (List.Mem.head rest)
        | tail _ tailMem => exact hFar symbol tailMem

private theorem workRunExact_compose (machine : WorkMachine)
    (first second : Nat) (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      rw [Nat.zero_add, hStart]
      exact hSecond
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
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

private theorem scanRightExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtWord state leftSide (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

private theorem scanLeftExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

private inductive DataBit : WorkSymbol → Prop where
  | zero : DataBit WorkSymbol.zeroBlank
  | one : DataBit WorkSymbol.oneBlank

private def bitSymbol : Bool → WorkSymbol
  | false => WorkSymbol.zeroBlank
  | true => WorkSymbol.oneBlank

private def bitSymbols (bits : BitString) : List WorkSymbol :=
  bits.map bitSymbol

private theorem bitSymbol_isDataBit (bit : Bool) :
    DataBit (bitSymbol bit) := by
  cases bit
  · exact .zero
  · exact .one

private theorem bitSymbols_areDataBits (bits : BitString) :
    ∀ symbol, List.Mem symbol (bitSymbols bits) → DataBit symbol := by
  induction bits with
  | nil => intro symbol found; contradiction
  | cons bit rest ih =>
      intro symbol found
      change List.Mem symbol (bitSymbol bit :: bitSymbols rest) at found
      cases found with
      | head => exact bitSymbol_isDataBit bit
      | tail _ tailMem => exact ih symbol tailMem

private theorem bitSymbols_length (bits : BitString) :
    (bitSymbols bits).length = bits.length := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => exact congrArg Nat.succ ih

private theorem bitSymbols_eq_map_data (bits : BitString) :
    bitSymbols bits = (bits.map TapeSymbol.ofBool).map dataSymbol := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
      cases bit with
      | false => exact congrArg (List.cons WorkSymbol.zeroBlank) ih
      | true => exact congrArg (List.cons WorkSymbol.oneBlank) ih

private theorem scan_bits_right_exact (bits : BitString)
    (suffix leftSide : List WorkSymbol) :
    workRunExact? framedOutputHandoff bits.length
        (configAtWord scanRightState leftSide (bitSymbols bits ++ suffix)) =
      some (configAtWord scanRightState
        (pushLeft (bitSymbols bits) leftSide) suffix) := by
  have hScan := scanRightExact framedOutputHandoff scanRightState DataBit
    (by
      intro scanned head remaining hHead
      cases hHead <;> rfl)
    (bitSymbols bits) suffix leftSide (bitSymbols_areDataBits bits)
  rw [bitSymbols_length] at hScan
  exact hScan

private theorem scan_bits_left_exact (bits : BitString)
    (leftSuffix rightSide : List WorkSymbol) :
    workRunExact? framedOutputHandoff bits.length
        (configAtLeftWord returnLeftState
          (pushLeft (bitSymbols bits) [] ++ leftSuffix) rightSide) =
      some (configAtLeftWord returnLeftState leftSuffix
        (bitSymbols bits ++ rightSide)) := by
  have hPushed : ∀ symbol,
      List.Mem symbol (pushLeft (bitSymbols bits) []) → DataBit symbol := by
    apply pushLeft_property DataBit (bitSymbols bits) []
    · exact bitSymbols_areDataBits bits
    · intro symbol found
      contradiction
  have hScan := scanLeftExact framedOutputHandoff returnLeftState DataBit
    (by
      intro head tail remaining hHead
      cases hHead <;> rfl)
    (pushLeft (bitSymbols bits) []) leftSuffix rightSide hPushed
  rw [pushLeft_length, bitSymbols_length] at hScan
  change workRunExact? framedOutputHandoff bits.length
      (configAtLeftWord returnLeftState
        (pushLeft (bitSymbols bits) [] ++ leftSuffix) rightSide) =
    some (configAtLeftWord returnLeftState leftSuffix
      (pushLeft (pushLeft (bitSymbols bits) []) rightSide)) at hScan
  rw [pushLeft_cancel] at hScan
  exact hScan

private theorem start_bit_step (bit : Bool) (leftHead : WorkSymbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := startState
          tape := { left := leftHead :: leftTail,
                    head := bitSymbol bit, right := rightSide } } =
      some
        { state := installLeftBitState
          tape := { left := leftTail, head := leftHead,
                    right := bitSymbol bit :: rightSide } } := by
  cases bit <;> rfl

private theorem start_empty_step (leftHead : WorkSymbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := startState
          tape := { left := leftHead :: leftTail,
                    head := WorkSymbol.blank, right := rightSide } } =
      some
        { state := installLeftEmptyState
          tape := { left := leftTail, head := leftHead,
                    right := WorkSymbol.blank :: rightSide } } := by
  rfl

private theorem install_left_bit_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := installLeftBitState
          tape := { left := leftTail, head := head, right := rightSide } } =
      some
        { state := scanRightState
          tape := { left := leftMarker :: leftTail,
                    head := rightSide.headD WorkSymbol.blank,
                    right := rightSide.tail } } := by
  cases head with
  | mk first second =>
      cases first <;> cases second <;> cases rightSide <;> rfl

private theorem install_left_bit_word_step (head : WorkSymbol)
    (leftTail : List WorkSymbol) (bit : Bool) (rest : BitString)
    (delimiter : WorkSymbol) (rightTail : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := installLeftBitState
          tape := { left := leftTail, head := head,
                    right := bitSymbol bit ::
                      (bitSymbols rest ++ delimiter :: rightTail) } } =
      some (configAtWord scanRightState (leftMarker :: leftTail)
        (bitSymbols (bit :: rest) ++ delimiter :: rightTail)) := by
  cases head with
  | mk first second => cases first <;> cases second <;> cases bit <;> rfl

private theorem install_left_empty_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := installLeftEmptyState
          tape := { left := leftTail, head := head, right := rightSide } } =
      some
        { state := emptyMoveRightState
          tape := { left := leftMarker :: leftTail,
                    head := rightSide.headD WorkSymbol.blank,
                    right := rightSide.tail } } := by
  cases head with
  | mk first second =>
      cases first <;> cases second <;> cases rightSide <;> rfl

private theorem scan_right_step (head : WorkSymbol)
    (hHead : DataBit head) (leftSide rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := scanRightState
          tape := { left := leftSide, head := head, right := rightSide } } =
      some
        { state := scanRightState
          tape := ({ left := leftSide, head := head,
                     right := rightSide } : WorkTape).moveRight } := by
  cases hHead <;> rfl

private theorem return_left_step (head : WorkSymbol)
    (hHead : DataBit head) (leftSide rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := returnLeftState
          tape := { left := leftSide, head := head, right := rightSide } } =
      some
        { state := returnLeftState
          tape := ({ left := leftSide, head := head,
                     right := rightSide } : WorkTape).moveLeft } := by
  cases hHead <;> rfl

private theorem delimiter_step (delimiter : WorkSymbol)
    (hDelimiter : delimiter = WorkSymbol.blank ∨ delimiter = rightMarker)
    (leftSide rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := scanRightState
          tape := { left := leftSide, head := delimiter,
                    right := rightSide } } =
      some
        { state := returnLeftState
          tape := ({ left := leftSide, head := rightMarker,
                     right := rightSide } : WorkTape).moveLeft } := by
  cases hDelimiter with
  | inl hBlank => cases hBlank; rfl
  | inr hRight => cases hRight; rfl

private theorem return_boundary_step (leftTail rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := returnLeftState
          tape := { left := leftTail, head := leftMarker,
                    right := rightSide } } =
      some
        { state := acceptState
          tape := ({ left := leftTail, head := leftMarker,
                     right := rightSide } : WorkTape).moveRight } := by
  rfl

private theorem empty_move_right_step (leftSide rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := emptyMoveRightState
          tape := { left := leftSide, head := WorkSymbol.blank,
                    right := rightSide } } =
      some
        { state := emptyInstallRightState
          tape := ({ left := leftSide, head := WorkSymbol.blank,
                     right := rightSide } : WorkTape).moveRight } := by
  rfl

private theorem empty_install_right_step (head : WorkSymbol)
    (leftSide rightSide : List WorkSymbol) :
    workStep? framedOutputHandoff
        { state := emptyInstallRightState
          tape := { left := leftSide, head := head, right := rightSide } } =
      some
        { state := acceptState
          tape := ({ left := leftSide, head := rightMarker,
                     right := rightSide } : WorkTape).moveLeft } := by
  cases head with
  | mk first second => cases first <;> cases second <;> rfl

private theorem delimiter_bit_word_step (first : Bool) (rest : BitString)
    (delimiter : WorkSymbol)
    (hDelimiter : delimiter = WorkSymbol.blank ∨ delimiter = rightMarker)
    (leftTail rightTail : List WorkSymbol) :
    workStep? framedOutputHandoff
        (configAtWord scanRightState
          (pushLeft (bitSymbols (first :: rest))
            (leftMarker :: leftTail))
          (delimiter :: rightTail)) =
      some
        (configAtLeftWord returnLeftState
          (pushLeft (bitSymbols (first :: rest)) [] ++
            leftMarker :: leftTail)
          (rightMarker :: rightTail)) := by
  have hFar := pushLeft_append_far (bitSymbols (first :: rest)) []
    (leftMarker :: leftTail)
  change pushLeft (bitSymbols (first :: rest))
      (leftMarker :: leftTail) =
    pushLeft (bitSymbols (first :: rest)) [] ++
      leftMarker :: leftTail at hFar
  rw [hFar]
  cases hPushed : pushLeft (bitSymbols (first :: rest)) [] with
  | nil =>
      have hLength := pushLeft_length (bitSymbols (first :: rest)) []
      rw [hPushed, bitSymbols_length] at hLength
      contradiction
  | cons head tail =>
      cases hDelimiter with
      | inl hBlank => cases hBlank; rfl
      | inr hRight => cases hRight; rfl

private theorem return_boundary_bit_word_step (first : Bool)
    (rest : BitString) (leftTail rightTail : List WorkSymbol) :
    workStep? framedOutputHandoff
        (configAtLeftWord returnLeftState (leftMarker :: leftTail)
          (bitSymbols (first :: rest) ++ rightMarker :: rightTail)) =
      some
        { state := acceptState
          tape := { left := leftMarker :: leftTail,
                    head := bitSymbol first,
                    right := bitSymbols rest ++ rightMarker :: rightTail } } := by
  cases first <;> rfl

private theorem zeroAddSafe (value : Nat) : 0 + value = value := by
  induction value with
  | zero => rfl
  | succ value ih => exact congrArg Nat.succ ih

private theorem succAddSafe (left right : Nat) :
    (left + 1) + right = (left + right) + 1 := by
  induction right with
  | zero => rfl
  | succ right ih => exact congrArg Nat.succ ih

private theorem addAssocSafe (left middle right : Nat) :
    (left + middle) + right = left + (middle + right) := by
  induction right with
  | zero => rfl
  | succ right ih => exact congrArg Nat.succ ih

private theorem addCommSafe (left right : Nat) :
    left + right = right + left := by
  induction right with
  | zero => exact (zeroAddSafe left).symm
  | succ right ih =>
      change (left + right) + 1 = (right + 1) + left
      calc
        (left + right) + 1 = (right + left) + 1 :=
          congrArg (fun value => value + 1) ih
        _ = (right + 1) + left := (succAddSafe right left).symm

private theorem addSwapMiddleSafe (left middle right : Nat) :
    (left + middle) + right = (left + right) + middle := by
  calc
    (left + middle) + right = left + (middle + right) :=
      addAssocSafe left middle right
    _ = left + (right + middle) :=
      congrArg (Nat.add left) (addCommSafe middle right)
    _ = (left + right) + middle :=
      (addAssocSafe left right middle).symm

private theorem twoMulSafe (value : Nat) : 2 * value = value + value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      calc
        2 * (value + 1) = 2 * value + 2 := rfl
        _ = (value + value) + 2 :=
          congrArg (fun result => result + 2) ih
        _ = ((value + 1) + value) + 1 :=
          congrArg (fun result => result + 1)
            (succAddSafe value value).symm
        _ = (value + 1) + (value + 1) := rfl

private theorem traceStepsArithmetic (length : Nat) :
    (((((1 + 1) + length) + 1) + length) + 1) =
      2 * length + 4 := by
  calc
    (((((1 + 1) + length) + 1) + length) + 1) =
        ((((length + (1 + 1)) + 1) + length) + 1) :=
      congrArg (fun value => ((value + 1) + length) + 1)
        (addCommSafe (1 + 1) length)
    _ = (((length + ((1 + 1) + 1)) + length) + 1) :=
      congrArg (fun value => (value + length) + 1)
        (addAssocSafe length (1 + 1) 1)
    _ = (((length + 3) + length) + 1) := rfl
    _ = (((length + length) + 3) + 1) :=
      congrArg (fun value => value + 1)
        (addSwapMiddleSafe length 3 length)
    _ = (length + length) + 4 := rfl
    _ = 2 * length + 4 :=
      congrArg (fun value => value + 4) (twoMulSafe length).symm

private theorem nonempty_layout_exact (first : Bool) (rest : BitString)
    (delimiter : WorkSymbol)
    (hDelimiter : delimiter = WorkSymbol.blank ∨ delimiter = rightMarker)
    (leftHead : WorkSymbol) (leftTail rightTail : List WorkSymbol) :
    workRunExact? framedOutputHandoff
        (2 * (first :: rest).length + 4)
        (workStartConfiguration framedOutputHandoff
          { left := leftHead :: leftTail
            head := bitSymbol first
            right := bitSymbols rest ++ delimiter :: rightTail }) =
      some
        { state := acceptState
          tape := { left := leftMarker :: leftTail
                    head := bitSymbol first
                    right := bitSymbols rest ++ rightMarker :: rightTail } } := by
  let initial : WorkConfiguration :=
    workStartConfiguration framedOutputHandoff
      { left := leftHead :: leftTail
        head := bitSymbol first
        right := bitSymbols rest ++ delimiter :: rightTail }
  let afterStart : WorkConfiguration :=
    { state := installLeftBitState
      tape := { left := leftTail, head := leftHead,
                right := bitSymbol first ::
                  (bitSymbols rest ++ delimiter :: rightTail) } }
  let afterInstall : WorkConfiguration :=
    configAtWord scanRightState (leftMarker :: leftTail)
      (bitSymbols (first :: rest) ++ delimiter :: rightTail)
  let afterScan : WorkConfiguration :=
    configAtWord scanRightState
      (pushLeft (bitSymbols (first :: rest)) (leftMarker :: leftTail))
      (delimiter :: rightTail)
  let afterDelimiter : WorkConfiguration :=
    configAtLeftWord returnLeftState
      (pushLeft (bitSymbols (first :: rest)) [] ++ leftMarker :: leftTail)
      (rightMarker :: rightTail)
  let afterReturn : WorkConfiguration :=
    configAtLeftWord returnLeftState (leftMarker :: leftTail)
      (bitSymbols (first :: rest) ++ rightMarker :: rightTail)
  let final : WorkConfiguration :=
    { state := acceptState
      tape := { left := leftMarker :: leftTail
                head := bitSymbol first
                right := bitSymbols rest ++ rightMarker :: rightTail } }
  have hStart : workRunExact? framedOutputHandoff 1 initial =
      some afterStart := by
    apply workRunExact_one
    dsimp [initial, afterStart, workStartConfiguration]
    exact start_bit_step first leftHead leftTail
      (bitSymbols rest ++ delimiter :: rightTail)
  have hInstall : workRunExact? framedOutputHandoff 1 afterStart =
      some afterInstall := by
    apply workRunExact_one
    dsimp [afterStart, afterInstall]
    exact install_left_bit_word_step leftHead leftTail first rest
      delimiter rightTail
  have hScan : workRunExact? framedOutputHandoff (first :: rest).length
      afterInstall = some afterScan := by
    dsimp [afterInstall, afterScan]
    exact scan_bits_right_exact (first :: rest)
      (delimiter :: rightTail) (leftMarker :: leftTail)
  have hDelimiterRun : workRunExact? framedOutputHandoff 1 afterScan =
      some afterDelimiter := by
    apply workRunExact_one
    dsimp [afterScan, afterDelimiter]
    exact delimiter_bit_word_step first rest delimiter hDelimiter
      leftTail rightTail
  have hReturn : workRunExact? framedOutputHandoff (first :: rest).length
      afterDelimiter = some afterReturn := by
    dsimp [afterDelimiter, afterReturn]
    exact scan_bits_left_exact (first :: rest)
      (leftMarker :: leftTail) (rightMarker :: rightTail)
  have hBoundary : workRunExact? framedOutputHandoff 1 afterReturn =
      some final := by
    apply workRunExact_one
    dsimp [afterReturn, final]
    exact return_boundary_bit_word_step first rest leftTail rightTail
  have throughInstall := workRunExact_compose framedOutputHandoff 1 1
    initial afterStart afterInstall hStart hInstall
  have throughScan := workRunExact_compose framedOutputHandoff (1 + 1)
    (first :: rest).length initial afterInstall afterScan throughInstall hScan
  have throughDelimiter := workRunExact_compose framedOutputHandoff
    ((1 + 1) + (first :: rest).length) 1 initial afterScan afterDelimiter
    throughScan hDelimiterRun
  have throughReturn := workRunExact_compose framedOutputHandoff
    (((1 + 1) + (first :: rest).length) + 1) (first :: rest).length
    initial afterDelimiter afterReturn throughDelimiter hReturn
  have complete := workRunExact_compose framedOutputHandoff
    ((((1 + 1) + (first :: rest).length) + 1) + (first :: rest).length) 1
    initial afterReturn final throughReturn hBoundary
  rw [traceStepsArithmetic (first :: rest).length] at complete
  exact complete

private theorem empty_layout_exact (leftHead rightHead : WorkSymbol)
    (leftTail rightTail : List WorkSymbol) :
    workRunExact? framedOutputHandoff 4
        (workStartConfiguration framedOutputHandoff
          { left := leftHead :: leftTail
            head := WorkSymbol.blank
            right := rightHead :: rightTail }) =
      some
        { state := acceptState
          tape := { left := leftMarker :: leftTail
                    head := WorkSymbol.blank
                    right := rightMarker :: rightTail } } := by
  let initial : WorkConfiguration :=
    workStartConfiguration framedOutputHandoff
      { left := leftHead :: leftTail
        head := WorkSymbol.blank
        right := rightHead :: rightTail }
  let afterStart : WorkConfiguration :=
    { state := installLeftEmptyState
      tape := { left := leftTail, head := leftHead,
                right := WorkSymbol.blank :: rightHead :: rightTail } }
  let afterInstall : WorkConfiguration :=
    { state := emptyMoveRightState
      tape := { left := leftMarker :: leftTail,
                head := WorkSymbol.blank, right := rightHead :: rightTail } }
  let afterMove : WorkConfiguration :=
    { state := emptyInstallRightState
      tape := { left := WorkSymbol.blank :: leftMarker :: leftTail,
                head := rightHead, right := rightTail } }
  let final : WorkConfiguration :=
    { state := acceptState
      tape := { left := leftMarker :: leftTail
                head := WorkSymbol.blank
                right := rightMarker :: rightTail } }
  have hStart : workRunExact? framedOutputHandoff 1 initial =
      some afterStart := by
    apply workRunExact_one
    dsimp [initial, afterStart, workStartConfiguration]
    exact start_empty_step leftHead leftTail (rightHead :: rightTail)
  have hInstall : workRunExact? framedOutputHandoff 1 afterStart =
      some afterInstall := by
    apply workRunExact_one
    dsimp [afterStart, afterInstall]
    have hStep := install_left_empty_step leftHead leftTail
      (WorkSymbol.blank :: rightHead :: rightTail)
    exact hStep
  have hMove : workRunExact? framedOutputHandoff 1 afterInstall =
      some afterMove := by
    apply workRunExact_one
    dsimp [afterInstall, afterMove]
    exact empty_move_right_step (leftMarker :: leftTail)
      (rightHead :: rightTail)
  have hRight : workRunExact? framedOutputHandoff 1 afterMove =
      some final := by
    apply workRunExact_one
    dsimp [afterMove, final]
    exact empty_install_right_step rightHead
      (WorkSymbol.blank :: leftMarker :: leftTail) rightTail
  have throughInstall := workRunExact_compose framedOutputHandoff 1 1
    initial afterStart afterInstall hStart hInstall
  have throughMove := workRunExact_compose framedOutputHandoff (1 + 1) 1
    initial afterInstall afterMove throughInstall hMove
  have complete := workRunExact_compose framedOutputHandoff
    ((1 + 1) + 1) 1 initial afterMove final throughMove hRight
  exact complete

private theorem right_output_layout (right : List TapeSymbol)
    (outsideRight : List WorkSymbol) :
    ∃ bits delimiter suffix,
      right.map dataSymbol ++ rightMarker :: outsideRight =
        bitSymbols bits ++ delimiter :: suffix ∧
      (delimiter = WorkSymbol.blank ∨ delimiter = rightMarker) ∧
      Tape.decodeOutputCells right = bits := by
  induction right with
  | nil =>
      exact ⟨[], rightMarker, outsideRight, rfl, Or.inr rfl, rfl⟩
  | cons head rest ih =>
      cases head with
      | blank =>
          exact ⟨[], WorkSymbol.blank,
            rest.map dataSymbol ++ rightMarker :: outsideRight,
            rfl, Or.inl rfl, rfl⟩
      | zero =>
          rcases ih with ⟨bits, delimiter, suffix,
            hLayout, hDelimiter, hDecode⟩
          refine ⟨false :: bits, delimiter, suffix, ?_, hDelimiter, ?_⟩
          · change WorkSymbol.zeroBlank ::
                (rest.map dataSymbol ++ rightMarker :: outsideRight) =
              WorkSymbol.zeroBlank ::
                (bitSymbols bits ++ delimiter :: suffix)
            exact congrArg (List.cons WorkSymbol.zeroBlank) hLayout
          · exact congrArg (List.cons false) hDecode
      | one =>
          rcases ih with ⟨bits, delimiter, suffix,
            hLayout, hDelimiter, hDecode⟩
          refine ⟨true :: bits, delimiter, suffix, ?_, hDelimiter, ?_⟩
          · change WorkSymbol.oneBlank ::
                (rest.map dataSymbol ++ rightMarker :: outsideRight) =
              WorkSymbol.oneBlank ::
                (bitSymbols bits ++ delimiter :: suffix)
            exact congrArg (List.cons WorkSymbol.oneBlank) hLayout
          · exact congrArg (List.cons true) hDecode

private theorem framed_left_split (left : List TapeSymbol)
    (outsideLeft : List WorkSymbol) :
    ∃ head tail,
      left.map dataSymbol ++ leftMarker :: outsideLeft = head :: tail := by
  cases left with
  | nil => exact ⟨leftMarker, outsideLeft, rfl⟩
  | cons head tail =>
      exact ⟨dataSymbol head,
        tail.map dataSymbol ++ leftMarker :: outsideLeft, rfl⟩

private theorem framed_right_split (right : List TapeSymbol)
    (outsideRight : List WorkSymbol) :
    ∃ head tail,
      right.map dataSymbol ++ rightMarker :: outsideRight = head :: tail := by
  cases right with
  | nil => exact ⟨rightMarker, outsideRight, rfl⟩
  | cons head tail =>
      exact ⟨dataSymbol head,
        tail.map dataSymbol ++ rightMarker :: outsideRight, rfl⟩

/-! ### Public exact handoff surface -/

def framedOutputHandoffFinalConfiguration (tape : WorkTape) :
    WorkConfiguration :=
  { state := framedOutputHandoff.acceptState, tape := tape }

/-- Every represented raw tape is handed to a represented canonical output
target in exactly `2 * outputLength + 4` successful work transitions. -/
theorem framedOutputHandoff_workRunExact_of_represents
    {raw : Tape} {work : WorkTape} (hRepresents : Represents raw work) :
    ∃ finalTape,
      Represents raw.handoffTarget finalTape ∧
      workRunExact? framedOutputHandoff
          (framedOutputHandoffWorkSteps raw)
          (workStartConfiguration framedOutputHandoff work) =
        some (framedOutputHandoffFinalConfiguration finalTape) := by
  rcases hRepresents with ⟨outsideLeft, outsideRight, hWork⟩
  subst work
  cases raw with
  | mk rawLeft rawHead rawRight =>
      rcases framed_left_split rawLeft outsideLeft with
        ⟨leftHead, leftTail, hLeft⟩
      cases rawHead with
      | blank =>
          rcases framed_right_split rawRight outsideRight with
            ⟨rightHead, rightTail, hRight⟩
          let finalTape := frameWithGarbage Tape.blank leftTail rightTail
          refine ⟨finalTape, ?_, ?_⟩
          · unfold Tape.handoffTarget Tape.outputBits
            change Represents Tape.blank finalTape
            exact frameWithGarbage_represents Tape.blank leftTail rightTail
          · have hExact := empty_layout_exact leftHead rightHead
                leftTail rightTail
            dsimp [framedOutputHandoffWorkSteps, BitString.size,
              Tape.outputBits, frameWithGarbage, finalTape,
              framedOutputHandoffFinalConfiguration]
            rw [hLeft, hRight]
            exact hExact
      | zero =>
          rcases right_output_layout rawRight outsideRight with
            ⟨rest, delimiter, rightTail, hRight, hDelimiter, hDecode⟩
          have hOutput : Tape.decodeOutputCells
              (TapeSymbol.zero :: rawRight) = false :: rest :=
            congrArg (List.cons false) hDecode
          let finalTape : WorkTape :=
            { left := leftMarker :: leftTail
              head := bitSymbol false
              right := bitSymbols rest ++ rightMarker :: rightTail }
          refine ⟨finalTape, ?_, ?_⟩
          · unfold Tape.handoffTarget Tape.outputBits
            rw [hOutput]
            refine ⟨leftTail, rightTail, ?_⟩
            dsimp [finalTape, frameWithGarbage, Tape.ofInput, bitSymbol]
            rw [← bitSymbols_eq_map_data]
            rfl
          · have hExact := nonempty_layout_exact false rest delimiter
                hDelimiter leftHead leftTail rightTail
            dsimp [framedOutputHandoffWorkSteps, BitString.size,
              Tape.outputBits, frameWithGarbage, finalTape,
              framedOutputHandoffFinalConfiguration, framedOutputHandoff]
            rw [hOutput]
            rw [hLeft, hRight]
            exact hExact
      | one =>
          rcases right_output_layout rawRight outsideRight with
            ⟨rest, delimiter, rightTail, hRight, hDelimiter, hDecode⟩
          have hOutput : Tape.decodeOutputCells
              (TapeSymbol.one :: rawRight) = true :: rest :=
            congrArg (List.cons true) hDecode
          let finalTape : WorkTape :=
            { left := leftMarker :: leftTail
              head := bitSymbol true
              right := bitSymbols rest ++ rightMarker :: rightTail }
          refine ⟨finalTape, ?_, ?_⟩
          · unfold Tape.handoffTarget Tape.outputBits
            rw [hOutput]
            refine ⟨leftTail, rightTail, ?_⟩
            dsimp [finalTape, frameWithGarbage, Tape.ofInput, bitSymbol]
            rw [← bitSymbols_eq_map_data]
            rfl
          · have hExact := nonempty_layout_exact true rest delimiter
                hDelimiter leftHead leftTail rightTail
            dsimp [framedOutputHandoffWorkSteps, BitString.size,
              Tape.outputBits, frameWithGarbage, finalTape,
              framedOutputHandoffFinalConfiguration, framedOutputHandoff]
            rw [hOutput]
            rw [hLeft, hRight]
            exact hExact

/-- Every exported endpoint is the handoff machine's designated accept halt. -/
theorem framedOutputHandoffFinal_isHalted (tape : WorkTape) :
    framedOutputHandoff.isHalted
      (framedOutputHandoffFinalConfiguration tape) = true := by
  rfl

private theorem mulAssocSafe (left middle right : Nat) :
    (left * middle) * right = left * (middle * right) := by
  induction right with
  | zero =>
      rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ right ih =>
      calc
        (left * middle) * Nat.succ right =
            (left * middle) * right + left * middle :=
          Nat.mul_succ _ _
        _ = left * (middle * right) + left * middle :=
          congrArg (fun value => value + left * middle) ih
        _ = left * (middle * right + middle) :=
          (Nat.mul_add _ _ _).symm
        _ = left * (middle * Nat.succ right) :=
          congrArg (Nat.mul left) (Nat.mul_succ middle right).symm

private theorem rawBudgetArithmetic (outputLength : Nat) :
    12 * outputLength + 24 = 6 * (2 * outputLength + 4) := by
  calc
    12 * outputLength + 24 =
        (6 * 2) * outputLength + 6 * 4 := rfl
    _ = 6 * (2 * outputLength) + 6 * 4 :=
      congrArg (fun value => value + 6 * 4)
        (mulAssocSafe 6 2 outputLength)
    _ = 6 * (2 * outputLength + 4) :=
      (Nat.mul_add 6 (2 * outputLength) 4).symm

/-- The displayed linear raw polynomial is exactly six times the proved
work-transition count. -/
theorem framedOutputHandoffRawTimeBound_exact (raw : Tape) :
    framedOutputHandoffRawTimeBound.eval
        (BitString.size raw.outputBits) =
      6 * framedOutputHandoffWorkSteps raw := by
  change 12 * BitString.size raw.outputBits + 24 =
    6 * (2 * BitString.size raw.outputBits + 4)
  exact rawBudgetArithmetic (BitString.size raw.outputBits)

/-- Compilation preserves the exact internal handoff trace at the displayed
linear raw budget.  The starting point is an encoded represented frame, not a
literal external `startConfig`. -/
theorem run_compileFramedOutputHandoff_of_represents
    {raw : Tape} {work : WorkTape} (hRepresents : Represents raw work) :
    ∃ finalTape,
      Represents raw.handoffTarget finalTape ∧
      run (compileWorkMachine framedOutputHandoff)
          (framedOutputHandoffRawTimeBound.eval
            (BitString.size raw.outputBits))
          (encodeWorkConfiguration
            (workStartConfiguration framedOutputHandoff work)) =
        encodeWorkConfiguration
          (framedOutputHandoffFinalConfiguration finalTape) := by
  rcases framedOutputHandoff_workRunExact_of_represents hRepresents with
    ⟨finalTape, hFinalRepresents, hExact⟩
  refine ⟨finalTape, hFinalRepresents, ?_⟩
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    framedOutputHandoff (framedOutputHandoffWorkSteps raw)
    (workStartConfiguration framedOutputHandoff work)
    (framedOutputHandoffFinalConfiguration finalTape) hExact
  rw [← framedOutputHandoffRawTimeBound_exact raw] at hCompiled
  exact hCompiled

end PipelineOutputHandoff

end PNP.Concrete
