/-
Copyright (c) 2026 PNP Labs.

A finite paired-input framer for the boundary-marked pipeline simulator.

Canonical paired inputs have positive even raw length.  The existing work-input
bridge therefore presents them to a compiled work machine as a nonempty word
of two-bit work symbols.  This machine copies that packed word to fresh cells
on its right, one pair at a time, while retaining the consumed source cells as
permitted exterior garbage.  The copied cells are bracketed by the pipeline
markers and the final head is focused on the first copied data cell.

The public exact trace is restricted to `BitString.pair` inputs.  It does not
frame arbitrary empty or odd raw inputs, combine its rules with a simulated
machine, retag its accepting state as another machine's start state, normalize
the exterior garbage, prove target-machine termination or verdict semantics,
construct a pipeline refinement, or establish any complexity-class equality.
-/

import PNP.Concrete.PipelineTapeGeometry
import PNP.Concrete.WorkInput

namespace PNP.Concrete

namespace PipelineInputFramer

open PipelineTape

/-! ### Finite control and rule table -/

def sourceSymbols : List WorkSymbol :=
  [WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneZero, WorkSymbol.oneOne]

inductive SourceSymbol : WorkSymbol → Prop where
  | zeroZero : SourceSymbol WorkSymbol.zeroZero
  | zeroOne : SourceSymbol WorkSymbol.zeroOne
  | oneZero : SourceSymbol WorkSymbol.oneZero
  | oneOne : SourceSymbol WorkSymbol.oneOne

def bootState : Nat := 0
def installOuterState : Nat := 1
def seekSourceEndState : Nat := 2
def installRightState : Nat := 3
def returnOuterState : Nat := 4
def seekUnprocessedState : Nat := 5
def carryZeroZeroState : Nat := 6
def carryZeroOneState : Nat := 7
def carryOneZeroState : Nat := 8
def carryOneOneState : Nat := 9
def appendZeroState : Nat := 10
def appendOneState : Nat := 11
def installMovingRightState : Nat := 12
def acceptState : Nat := 13
def rejectState : Nat := 14

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

def bootRules : List WorkRule :=
  sourceSymbols.map (fun symbol =>
    keepRule bootState symbol installOuterState .left)

def seekSourceEndRules : List WorkRule :=
  sourceSymbols.map (fun symbol =>
    keepRule seekSourceEndState symbol seekSourceEndState .right)

def returnSymbols : List WorkSymbol :=
  [WorkSymbol.blank, leftMarker,
   WorkSymbol.zeroBlank, WorkSymbol.oneBlank,
   WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneZero, WorkSymbol.oneOne]

def returnOuterRules : List WorkRule :=
  returnSymbols.map (fun symbol =>
      keepRule returnOuterState symbol returnOuterState .left) ++
    [keepRule returnOuterState rightMarker seekUnprocessedState .right]

def seekUnprocessedRules : List WorkRule :=
  [keepRule seekUnprocessedState WorkSymbol.blank
      seekUnprocessedState .right,
   writeRule seekUnprocessedState WorkSymbol.zeroZero
      carryZeroZeroState WorkSymbol.blank .right,
   writeRule seekUnprocessedState WorkSymbol.zeroOne
      carryZeroOneState WorkSymbol.blank .right,
   writeRule seekUnprocessedState WorkSymbol.oneZero
      carryOneZeroState WorkSymbol.blank .right,
   writeRule seekUnprocessedState WorkSymbol.oneOne
      carryOneOneState WorkSymbol.blank .right,
   keepRule seekUnprocessedState leftMarker acceptState .right]

def carryScanSymbols : List WorkSymbol :=
  sourceSymbols ++ [leftMarker, WorkSymbol.zeroBlank, WorkSymbol.oneBlank]

def carryScanRules (state : Nat) : List WorkRule :=
  carryScanSymbols.map (fun symbol =>
    keepRule state symbol state .right)

def carryBoundaryRules : List WorkRule :=
  [writeRule carryZeroZeroState rightMarker appendZeroState
      WorkSymbol.zeroBlank .right,
   writeRule carryZeroOneState rightMarker appendOneState
      WorkSymbol.zeroBlank .right,
   writeRule carryOneZeroState rightMarker appendZeroState
      WorkSymbol.oneBlank .right,
   writeRule carryOneOneState rightMarker appendOneState
      WorkSymbol.oneBlank .right]

def framerRules : List WorkRule :=
  bootRules ++
  [writeRule installOuterState WorkSymbol.blank seekSourceEndState
      rightMarker .right] ++
  seekSourceEndRules ++
  [writeRule seekSourceEndState WorkSymbol.blank installRightState
      leftMarker .right,
   writeRule installRightState WorkSymbol.blank returnOuterState
      rightMarker .left] ++
  returnOuterRules ++
  seekUnprocessedRules ++
  carryScanRules carryZeroZeroState ++
  carryScanRules carryZeroOneState ++
  carryScanRules carryOneZeroState ++
  carryScanRules carryOneOneState ++
  carryBoundaryRules ++
  [writeRule appendZeroState WorkSymbol.blank installMovingRightState
      WorkSymbol.zeroBlank .right,
   writeRule appendOneState WorkSymbol.blank installMovingRightState
      WorkSymbol.oneBlank .right,
   writeRule installMovingRightState WorkSymbol.blank returnOuterState
      rightMarker .left]

/-- A literal finite work machine which frames canonical paired input. -/
def pairedInputFramer : WorkMachine :=
  { rules := framerRules
    startState := bootState
    acceptState := acceptState
    rejectState := rejectState }

def packedPairCount (left right : BitString) : Nat :=
  left.length + right.length + 1

def inputFramerWorkSteps (packedCells : Nat) : Nat :=
  4 * packedCells * packedCells + 9 * packedCells + 7

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

private def configAtLeftWord (state : Nat) (leftWord rightSide : List WorkSymbol) :
    WorkConfiguration :=
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

private theorem boot_step {symbol : WorkSymbol} (h : SourceSymbol symbol)
    (leftSide suffix : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := bootState
          tape := { left := leftSide, head := symbol, right := suffix } } =
      some
        { state := installOuterState
          tape := ({ left := leftSide, head := symbol, right := suffix } :
            WorkTape).moveLeft } := by
  cases h <;> rfl

private theorem installOuter_step (suffix : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := installOuterState
          tape := { left := [], head := WorkSymbol.blank, right := suffix } } =
      some
        { state := seekSourceEndState
          tape := { left := [rightMarker]
                    head := suffix.head?.getD WorkSymbol.blank
                    right := suffix.tail } } := by
  cases suffix <;> rfl

private theorem seekSourceEnd_step {symbol : WorkSymbol}
    (h : SourceSymbol symbol) (leftSide suffix : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := seekSourceEndState
          tape := { left := leftSide, head := symbol, right := suffix } } =
      some
        { state := seekSourceEndState
          tape := ({ left := leftSide, head := symbol, right := suffix } :
            WorkTape).moveRight } := by
  cases h <;> rfl

private theorem seekSourceEnd_blank_step (leftSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := seekSourceEndState
          tape := { left := leftSide, head := WorkSymbol.blank, right := [] } } =
      some
        { state := installRightState
          tape := { left := leftMarker :: leftSide
                    head := WorkSymbol.blank
                    right := [] } } := by
  rfl

private theorem installRight_step (leftSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := installRightState
          tape := { left := leftSide, head := WorkSymbol.blank, right := [] } } =
      some
        { state := returnOuterState
          tape := { left := leftSide.tail
                    head := leftSide.head?.getD WorkSymbol.blank
                    right := [rightMarker] } } := by
  cases leftSide <;> rfl

private theorem returnOuter_step {symbol : WorkSymbol}
    (h : symbol ≠ rightMarker) (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := returnOuterState
          tape := { left := leftSide, head := symbol, right := rightSide } } =
      some
        { state := returnOuterState
          tape := ({ left := leftSide, head := symbol, right := rightSide } :
            WorkTape).moveLeft } := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;>
    first | rfl | exact False.elim (h rfl)

private theorem returnOuter_marker_step (rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := returnOuterState
          tape := { left := [], head := rightMarker, right := rightSide } } =
      some
        { state := seekUnprocessedState
          tape := { left := [rightMarker]
                    head := rightSide.head?.getD WorkSymbol.blank
                    right := rightSide.tail } } := by
  cases rightSide <;> rfl

private theorem seek_blank_step (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := seekUnprocessedState
          tape := { left := leftSide, head := WorkSymbol.blank,
                    right := rightSide } } =
      some
        { state := seekUnprocessedState
          tape := ({ left := leftSide, head := WorkSymbol.blank,
                     right := rightSide } : WorkTape).moveRight } := by
  rfl

private def carryStateFor (symbol : WorkSymbol) : Nat :=
  match symbol.first with
  | .blank =>
      match symbol.second with
      | .blank => carryZeroZeroState
      | .zero => carryZeroZeroState
      | .one => carryZeroZeroState
  | .zero =>
      match symbol.second with
      | .blank => carryZeroZeroState
      | .zero => carryZeroZeroState
      | .one => carryZeroOneState
  | .one =>
      match symbol.second with
      | .blank => carryZeroZeroState
      | .zero => carryOneZeroState
      | .one => carryOneOneState

private theorem seek_source_step {symbol : WorkSymbol}
    (h : SourceSymbol symbol) (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := seekUnprocessedState
          tape := { left := leftSide, head := symbol, right := rightSide } } =
      some
        { state := carryStateFor symbol
          tape := ({ left := leftSide, head := WorkSymbol.blank,
                     right := rightSide } : WorkTape).moveRight } := by
  cases h <;> rfl

private theorem seek_leftMarker_step (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := seekUnprocessedState
          tape := { left := leftSide, head := leftMarker, right := rightSide } } =
      some
        { state := acceptState
          tape := ({ left := leftSide, head := leftMarker,
                     right := rightSide } : WorkTape).moveRight } := by
  rfl

private def appendStateFor (symbol : WorkSymbol) : Nat :=
  match symbol.second with
  | .zero => appendZeroState
  | .one => appendOneState
  | .blank => appendZeroState

inductive CarryScanSymbol : WorkSymbol → Prop where
  | zeroZero : CarryScanSymbol WorkSymbol.zeroZero
  | zeroOne : CarryScanSymbol WorkSymbol.zeroOne
  | oneZero : CarryScanSymbol WorkSymbol.oneZero
  | oneOne : CarryScanSymbol WorkSymbol.oneOne
  | leftMarker : CarryScanSymbol PipelineTape.leftMarker
  | dataZero : CarryScanSymbol WorkSymbol.zeroBlank
  | dataOne : CarryScanSymbol WorkSymbol.oneBlank

private theorem carry_scan_step {source scan : WorkSymbol}
    (hSource : SourceSymbol source) (hScan : CarryScanSymbol scan)
    (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := carryStateFor source
          tape := { left := leftSide, head := scan, right := rightSide } } =
      some
        { state := carryStateFor source
          tape := ({ left := leftSide, head := scan, right := rightSide } :
            WorkTape).moveRight } := by
  cases hSource <;> cases hScan <;> rfl

private theorem carry_marker_step {source : WorkSymbol}
    (hSource : SourceSymbol source) (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := carryStateFor source
          tape := { left := leftSide, head := rightMarker,
                    right := rightSide } } =
      some
        { state := appendStateFor source
          tape := ({ left := leftSide,
                     head := dataSymbol source.first,
                     right := rightSide } : WorkTape).moveRight } := by
  cases hSource <;> rfl

private theorem append_second_step {source : WorkSymbol}
    (hSource : SourceSymbol source) (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := appendStateFor source
          tape := { left := leftSide, head := WorkSymbol.blank,
                    right := rightSide } } =
      some
        { state := installMovingRightState
          tape := ({ left := leftSide,
                     head := dataSymbol source.second,
                     right := rightSide } : WorkTape).moveRight } := by
  cases hSource <;> rfl

private theorem install_moving_right_step (leftSide rightSide : List WorkSymbol) :
    workStep? pairedInputFramer
        { state := installMovingRightState
          tape := { left := leftSide, head := WorkSymbol.blank,
                    right := rightSide } } =
      some
        { state := returnOuterState
          tape := ({ left := leftSide, head := rightMarker,
                     right := rightSide } : WorkTape).moveLeft } := by
  rfl

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
          (configAtLeftWord state (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

private def unpackData : List WorkSymbol → List WorkSymbol
  | [] => []
  | symbol :: rest =>
      dataSymbol symbol.first :: dataSymbol symbol.second :: unpackData rest

private def processedCells (done : List WorkSymbol) : List WorkSymbol :=
  List.replicate done.length WorkSymbol.blank

private def iterationTape (done todo : List WorkSymbol) : WorkTape :=
  match todo with
  | [] =>
      { left := processedCells done ++ [rightMarker]
        head := leftMarker
        right := unpackData done ++ [rightMarker] }
  | current :: rest =>
      { left := processedCells done ++ [rightMarker]
        head := current
        right := rest ++ leftMarker :: (unpackData done ++ [rightMarker]) }

private def iterationConfig (done todo : List WorkSymbol) : WorkConfiguration :=
  { state := seekUnprocessedState, tape := iterationTape done todo }

private theorem unpackData_append_one (done : List WorkSymbol)
    (current : WorkSymbol) :
    unpackData (done ++ [current]) =
      unpackData done ++
        [dataSymbol current.first, dataSymbol current.second] := by
  induction done with
  | nil => rfl
  | cons first rest ih =>
      change dataSymbol first.first :: dataSymbol first.second ::
          unpackData (rest ++ [current]) =
        dataSymbol first.first :: dataSymbol first.second ::
          (unpackData rest ++
            [dataSymbol current.first, dataSymbol current.second])
      exact congrArg (List.cons (dataSymbol first.first))
        (congrArg (List.cons (dataSymbol first.second)) ih)

private theorem processedCells_append_one (done : List WorkSymbol)
    (current : WorkSymbol) :
    processedCells (done ++ [current]) =
      WorkSymbol.blank :: processedCells done := by
  unfold processedCells
  induction done with
  | nil => rfl
  | cons first rest ih =>
      change WorkSymbol.blank ::
          List.replicate (rest ++ [current]).length WorkSymbol.blank =
        WorkSymbol.blank :: WorkSymbol.blank ::
          List.replicate rest.length WorkSymbol.blank
      exact congrArg (List.cons WorkSymbol.blank) ih

private theorem workList_append_assoc (left middle right : List WorkSymbol) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

private theorem workList_append_nil (word : List WorkSymbol) :
    word ++ [] = word := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

private theorem workList_length_append (left right : List WorkSymbol) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons symbol rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

private theorem unpackData_length (word : List WorkSymbol) :
    (unpackData word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      change Nat.succ (Nat.succ (unpackData rest).length) =
        2 * Nat.succ rest.length
      rw [ih, Nat.mul_succ]

private theorem processedCells_length (done : List WorkSymbol) :
    (processedCells done).length = done.length := by
  unfold processedCells
  induction done with
  | nil => rfl
  | cons symbol rest ih => exact congrArg Nat.succ ih

private theorem replicateBlank_commute (count : Nat)
    (farSide : List WorkSymbol) :
    List.replicate count WorkSymbol.blank ++ WorkSymbol.blank :: farSide =
      WorkSymbol.blank ::
        (List.replicate count WorkSymbol.blank ++ farSide) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change WorkSymbol.blank ::
          (List.replicate count WorkSymbol.blank ++
            WorkSymbol.blank :: farSide) =
        WorkSymbol.blank :: WorkSymbol.blank ::
          (List.replicate count WorkSymbol.blank ++ farSide)
      exact congrArg (List.cons WorkSymbol.blank) ih

private theorem pushLeft_replicateBlank (count : Nat)
    (farSide : List WorkSymbol) :
    pushLeft (List.replicate count WorkSymbol.blank) farSide =
      List.replicate count WorkSymbol.blank ++ farSide := by
  induction count generalizing farSide with
  | zero => rfl
  | succ count ih =>
      change pushLeft (List.replicate count WorkSymbol.blank)
          (WorkSymbol.blank :: farSide) =
        WorkSymbol.blank ::
          (List.replicate count WorkSymbol.blank ++ farSide)
      rw [ih]
      exact replicateBlank_commute count farSide

private theorem pushLeft_processed (done : List WorkSymbol)
    (farSide : List WorkSymbol) :
    pushLeft (processedCells done) farSide =
      processedCells done ++ farSide := by
  exact pushLeft_replicateBlank done.length farSide

private theorem source_ne_rightMarker {symbol : WorkSymbol}
    (h : SourceSymbol symbol) : symbol ≠ rightMarker := by
  cases h <;> intro impossible <;> contradiction

private theorem carryScan_ne_rightMarker {symbol : WorkSymbol}
    (h : CarryScanSymbol symbol) : symbol ≠ rightMarker := by
  cases h <;> intro impossible <;> contradiction

private theorem source_is_carryScan {symbol : WorkSymbol}
    (h : SourceSymbol symbol) : CarryScanSymbol symbol := by
  cases h
  · exact .zeroZero
  · exact .zeroOne
  · exact .oneZero
  · exact .oneOne

private theorem unpackData_is_carryScan (done : List WorkSymbol)
    (hDone : ∀ symbol, List.Mem symbol done → SourceSymbol symbol) :
    ∀ symbol, List.Mem symbol (unpackData done) → CarryScanSymbol symbol := by
  induction done with
  | nil => intro symbol found; contradiction
  | cons first rest ih =>
      intro symbol found
      have hFirst : SourceSymbol first := hDone first (List.Mem.head rest)
      have hRest : ∀ item, List.Mem item rest → SourceSymbol item := by
        intro item itemMem
        exact hDone item (List.Mem.tail first itemMem)
      change List.Mem symbol
        (dataSymbol first.first :: dataSymbol first.second :: unpackData rest) at found
      cases found with
      | head =>
          cases hFirst
          · exact .dataZero
          · exact .dataZero
          · exact .dataOne
          · exact .dataOne
      | tail _ foundTail =>
          cases foundTail with
          | head =>
              cases hFirst
              · exact .dataZero
              · exact .dataOne
              · exact .dataZero
              · exact .dataOne
          | tail _ foundRest => exact ih hRest symbol foundRest

private theorem carryWord_allowed (done rest : List WorkSymbol)
    (hDone : ∀ symbol, List.Mem symbol done → SourceSymbol symbol)
    (hRest : ∀ symbol, List.Mem symbol rest → SourceSymbol symbol) :
    ∀ symbol,
      List.Mem symbol (rest ++ leftMarker :: unpackData done) →
        CarryScanSymbol symbol := by
  induction rest with
  | nil =>
      intro symbol found
      change List.Mem symbol (leftMarker :: unpackData done) at found
      cases found with
      | head => exact .leftMarker
      | tail _ tailMem => exact unpackData_is_carryScan done hDone symbol tailMem
  | cons first tail ih =>
      intro symbol found
      change List.Mem symbol (first :: (tail ++ leftMarker :: unpackData done)) at found
      cases found with
      | head =>
          exact source_is_carryScan
            (hRest first (List.Mem.head tail))
      | tail _ tailMem =>
          apply ih
          · intro item itemMem
            exact hRest item (List.Mem.tail first itemMem)
          · exact tailMem

private theorem returnWord_allowed (word : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → symbol ≠ rightMarker) :
    ∀ symbol, List.Mem symbol word → symbol ≠ rightMarker :=
  hWord

private theorem central_return_layout (done rest : List WorkSymbol)
    (current : WorkSymbol) :
    let crossed := rest ++ leftMarker :: unpackData done
    let nextProcessed := processedCells (done ++ [current])
    let returnWord :=
      dataSymbol current.second :: dataSymbol current.first ::
        (pushLeft crossed [] ++ nextProcessed)
    pushLeft returnWord [rightMarker] =
      nextProcessed ++ rest ++
        leftMarker :: (unpackData (done ++ [current]) ++ [rightMarker]) := by
  dsimp
  change pushLeft
      (pushLeft (rest ++ leftMarker :: unpackData done) [] ++
        processedCells (done ++ [current]))
      [dataSymbol current.first, dataSymbol current.second, rightMarker] = _
  rw [pushLeft_append_word]
  rw [pushLeft_cancel]
  rw [pushLeft_processed]
  rw [unpackData_append_one]
  repeat' rw [workList_append_assoc]
  rfl

private theorem sourceScan_exact (word suffix leftSide : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → SourceSymbol symbol) :
    workRunExact? pairedInputFramer word.length
        (configAtWord seekSourceEndState leftSide (word ++ suffix)) =
      some (configAtWord seekSourceEndState (pushLeft word leftSide) suffix) := by
  apply scanRightExact pairedInputFramer seekSourceEndState SourceSymbol
  · intro scanned head remaining hHead
    exact seekSourceEnd_step hHead scanned remaining
  · exact hWord

private theorem carryScan_exact (source : WorkSymbol)
    (hSource : SourceSymbol source)
    (word suffix leftSide : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → CarryScanSymbol symbol) :
    workRunExact? pairedInputFramer word.length
        (configAtWord (carryStateFor source) leftSide (word ++ suffix)) =
      some (configAtWord (carryStateFor source)
        (pushLeft word leftSide) suffix) := by
  apply scanRightExact pairedInputFramer (carryStateFor source)
    CarryScanSymbol
  · intro scanned head remaining hHead
    exact carry_scan_step hSource hHead scanned remaining
  · exact hWord

private theorem returnScan_exact (word leftSuffix rightSide : List WorkSymbol)
    (hWord : ∀ symbol, List.Mem symbol word → symbol ≠ rightMarker) :
    workRunExact? pairedInputFramer word.length
        (configAtLeftWord returnOuterState (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord returnOuterState leftSuffix
        (pushLeft word rightSide)) := by
  apply scanLeftExact pairedInputFramer returnOuterState
    (fun symbol => symbol ≠ rightMarker)
  · intro head tail remaining hHead
    exact returnOuter_step hHead tail remaining
  · exact hWord

private theorem seekBlanks_exact (count : Nat)
    (suffix leftSide : List WorkSymbol) :
    workRunExact? pairedInputFramer count
        (configAtWord seekUnprocessedState leftSide
          (List.replicate count WorkSymbol.blank ++ suffix)) =
      some (configAtWord seekUnprocessedState
        (pushLeft (List.replicate count WorkSymbol.blank) leftSide) suffix) := by
  have hAllowed : ∀ symbol,
      List.Mem symbol (List.replicate count WorkSymbol.blank) →
        symbol = WorkSymbol.blank := by
    intro symbol found
    induction count with
    | zero => contradiction
    | succ count ih =>
        change List.Mem symbol
          (WorkSymbol.blank :: List.replicate count WorkSymbol.blank) at found
        cases found with
        | head => rfl
        | tail _ tailMem => exact ih tailMem
  have hLength : (List.replicate count WorkSymbol.blank).length = count := by
    clear hAllowed
    induction count with
    | zero => rfl
    | succ count ih => exact congrArg Nat.succ ih
  have hScan := scanRightExact pairedInputFramer seekUnprocessedState
    (fun symbol => symbol = WorkSymbol.blank)
    (by
      intro scanned head remaining hHead
      cases hHead
      exact seek_blank_step scanned remaining)
    (List.replicate count WorkSymbol.blank) suffix leftSide hAllowed
  rw [hLength] at hScan
  exact hScan

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

private theorem append_property (Property : WorkSymbol → Prop)
    (left right : List WorkSymbol)
    (hLeft : ∀ symbol, List.Mem symbol left → Property symbol)
    (hRight : ∀ symbol, List.Mem symbol right → Property symbol) :
    ∀ symbol, List.Mem symbol (left ++ right) → Property symbol := by
  induction left with
  | nil => exact hRight
  | cons first rest ih =>
      intro symbol found
      cases found with
      | head => exact hLeft first (List.Mem.head rest)
      | tail _ tailMem =>
          apply ih
          · intro item itemMem
            exact hLeft item (List.Mem.tail first itemMem)
          · exact tailMem

private theorem replicateBlank_member (count : Nat) (symbol : WorkSymbol)
    (h : List.Mem symbol (List.replicate count WorkSymbol.blank)) :
    symbol = WorkSymbol.blank := by
  induction count with
  | zero => contradiction
  | succ count ih =>
      change List.Mem symbol
        (WorkSymbol.blank :: List.replicate count WorkSymbol.blank) at h
      cases h with
      | head => rfl
      | tail _ tailMem => exact ih tailMem

private theorem processed_ne_rightMarker (done : List WorkSymbol) :
    ∀ symbol, List.Mem symbol (processedCells done) →
      symbol ≠ rightMarker := by
  intro symbol found
  have hBlank := replicateBlank_member done.length symbol found
  cases hBlank
  intro impossible
  contradiction

private theorem boot_return_layout (word : List WorkSymbol) :
    pushLeft (leftMarker :: pushLeft word []) [rightMarker] =
      word ++ leftMarker :: [rightMarker] := by
  change pushLeft (pushLeft word []) (leftMarker :: [rightMarker]) = _
  exact pushLeft_cancel word (leftMarker :: [rightMarker])

private theorem bootstrapFuel (count : Nat) :
    (((2 + count) + 2) + (count + 1)) + 1 = 2 * count + 6 := by
  rw [Nat.two_mul]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 2 count]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 2 count]
  rw [Nat.add_left_comm 2 count]

private theorem returnLengthArithmetic (restLength doneLength : Nat) :
    Nat.succ
        (Nat.succ
          ((restLength + 1 + 2 * doneLength) + (doneLength + 1))) =
      restLength + 3 * doneLength + 4 := by
  rw [Nat.succ_mul 2 doneLength]
  rw [Nat.two_mul doneLength]
  repeat' rw [Nat.add_assoc]
  change
    (restLength +
      (1 + (doneLength + (doneLength + (doneLength + 1))))) + 2 =
      restLength + (doneLength + (doneLength + (doneLength + 4)))
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 1 doneLength]

private theorem copyOneFuelArithmetic (restLength doneLength : Nat) :
    ((((1 + (restLength + 1 + 2 * doneLength)) + 3) +
        (restLength + 3 * doneLength + 4)) + 1) +
        (doneLength + 1) =
      6 * doneLength + 2 * restLength + 11 := by
  rw [Nat.two_mul restLength]
  rw [Nat.succ_mul 2 doneLength]
  rw [Nat.two_mul doneLength]
  rw [Nat.succ_mul 5 doneLength]
  rw [Nat.succ_mul 4 doneLength]
  rw [Nat.succ_mul 3 doneLength]
  rw [Nat.succ_mul 2 doneLength]
  rw [Nat.two_mul doneLength]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 3 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 3 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 3 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 4 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 3 doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm restLength doneLength]
  rw [Nat.add_left_comm 1 doneLength]
  rw [Nat.add_left_comm 1 restLength]
  rw [Nat.add_left_comm 3 restLength]
  rw [Nat.add_left_comm 1 restLength]
  rw [Nat.add_left_comm 1 restLength]

private theorem bootstrap_exact (current : WorkSymbol)
    (rest : List WorkSymbol)
    (hCurrent : SourceSymbol current)
    (hRest : ∀ symbol, List.Mem symbol rest → SourceSymbol symbol) :
    workRunExact? pairedInputFramer (2 * (current :: rest).length + 6)
        (workStartConfiguration pairedInputFramer
          (WorkTape.ofSymbols (current :: rest))) =
      some (iterationConfig [] (current :: rest)) := by
  let word := current :: rest
  have hWord : ∀ symbol, List.Mem symbol word → SourceSymbol symbol := by
    intro symbol found
    change List.Mem symbol (current :: rest) at found
    cases found with
    | head => exact hCurrent
    | tail _ tailMem => exact hRest symbol tailMem
  have hFirst :
      workRunExact? pairedInputFramer 2
          (workStartConfiguration pairedInputFramer
            (WorkTape.ofSymbols word)) =
        some (configAtWord seekSourceEndState [rightMarker] word) := by
    dsimp [word, workStartConfiguration, WorkTape.ofSymbols, configAtWord,
      tapeAtWord]
    cases hCurrent <;> rfl
  have hScan := sourceScan_exact word [] [rightMarker] hWord
  have hMarkers :
      workRunExact? pairedInputFramer 2
          (configAtWord seekSourceEndState
            (pushLeft word [rightMarker]) []) =
        some (configAtLeftWord returnOuterState
          (leftMarker :: pushLeft word [rightMarker]) [rightMarker]) := by
    rfl
  let returnWord := leftMarker :: pushLeft word []
  have hSplit : pushLeft word [rightMarker] =
      pushLeft word [] ++ [rightMarker] := by
    exact pushLeft_append_far word [] [rightMarker]
  have hReturnAllowed : ∀ symbol, List.Mem symbol returnWord →
      symbol ≠ rightMarker := by
    intro symbol found
    change List.Mem symbol (leftMarker :: pushLeft word []) at found
    cases found with
    | head => exact leftMarker_ne_rightMarker
    | tail _ tailMem =>
        have hPushed := pushLeft_property
          (fun item => item ≠ rightMarker) word []
          (by
            intro item itemMem
            exact source_ne_rightMarker (hWord item itemMem))
          (by intro item impossible; contradiction)
        exact hPushed symbol tailMem
  have hReturnRaw := returnScan_exact returnWord [rightMarker]
    [rightMarker] hReturnAllowed
  have hReturn :
      workRunExact? pairedInputFramer returnWord.length
          (configAtLeftWord returnOuterState
            (leftMarker :: pushLeft word [rightMarker]) [rightMarker]) =
        some (configAtLeftWord returnOuterState [rightMarker]
          (word ++ leftMarker :: [rightMarker])) := by
    rw [hSplit]
    change workRunExact? pairedInputFramer returnWord.length
        (configAtLeftWord returnOuterState
          (returnWord ++ [rightMarker]) [rightMarker]) = _
    rw [boot_return_layout] at hReturnRaw
    exact hReturnRaw
  have hOuter :
      workRunExact? pairedInputFramer 1
          (configAtLeftWord returnOuterState [rightMarker]
            (word ++ leftMarker :: [rightMarker])) =
        some (iterationConfig [] word) := by
    change workRunExact? pairedInputFramer 1
        { state := returnOuterState
          tape := { left := [], head := rightMarker,
                    right := word ++ leftMarker :: [rightMarker] } } = _
    have hStep := returnOuter_marker_step
      (word ++ leftMarker :: [rightMarker])
    have hOne := workRunExact_one pairedInputFramer _ _ hStep
    dsimp [iterationConfig, iterationTape, word, processedCells] at hOne ⊢
    exact hOne
  have hFirstScan := workRunExact_compose pairedInputFramer 2 word.length
    _ _ _ hFirst (by
      rw [workList_append_nil word] at hScan
      exact hScan)
  have hThroughMarkers := workRunExact_compose pairedInputFramer
    (2 + word.length) 2 _ _ _ hFirstScan hMarkers
  have hThroughReturn := workRunExact_compose pairedInputFramer
    ((2 + word.length) + 2) returnWord.length _ _ _
    hThroughMarkers hReturn
  have hAll := workRunExact_compose pairedInputFramer
    (((2 + word.length) + 2) + returnWord.length) 1 _ _ _
    hThroughReturn hOuter
  have hReturnLength : returnWord.length = word.length + 1 := by
    change Nat.succ (pushLeft word []).length = word.length + 1
    have hPushLength : ∀ items far,
        (pushLeft items far).length = items.length + far.length := by
      intro items
      induction items with
      | nil => intro far; exact (Nat.zero_add far.length).symm
      | cons first tail ih =>
          intro far
          change (pushLeft tail (first :: far)).length =
            Nat.succ tail.length + far.length
          rw [ih]
          rw [Nat.succ_add]
          exact Nat.add_succ tail.length far.length
    rw [hPushLength word []]
    rfl
  rw [hReturnLength] at hAll
  have hFuel := bootstrapFuel word.length
  rw [hFuel] at hAll
  dsimp [word] at hAll ⊢
  exact hAll

private theorem copy_one_exact (done : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol)
    (hDone : ∀ symbol, List.Mem symbol done → SourceSymbol symbol)
    (hCurrent : SourceSymbol current)
    (hRest : ∀ symbol, List.Mem symbol rest → SourceSymbol symbol) :
    workRunExact? pairedInputFramer
        (6 * done.length + 2 * rest.length + 11)
        (iterationConfig done (current :: rest)) =
      some (iterationConfig (done ++ [current]) rest) := by
  let crossed := rest ++ leftMarker :: unpackData done
  let capturedLeft := WorkSymbol.blank ::
    (processedCells done ++ [rightMarker])
  have hCapture :
      workRunExact? pairedInputFramer 1
          (iterationConfig done (current :: rest)) =
        some (configAtWord (carryStateFor current) capturedLeft
          (crossed ++ [rightMarker])) := by
    dsimp [iterationConfig, iterationTape, capturedLeft, crossed,
      configAtWord, tapeAtWord]
    cases hCurrent <;>
      repeat' rw [workList_append_assoc] <;> rfl
  have hCrossedAllowed : ∀ symbol, List.Mem symbol crossed →
      CarryScanSymbol symbol := by
    exact carryWord_allowed done rest hDone hRest
  have hCarry := carryScan_exact current hCurrent crossed [rightMarker]
    capturedLeft hCrossedAllowed
  let scannedLeft := pushLeft crossed capturedLeft
  have hAppend :
      workRunExact? pairedInputFramer 3
          (configAtWord (carryStateFor current) scannedLeft [rightMarker]) =
        some
          { state := returnOuterState
            tape :=
              { left := dataSymbol current.first :: scannedLeft
                head := dataSymbol current.second
                right := [rightMarker] } } := by
    dsimp [configAtWord, tapeAtWord, scannedLeft]
    cases hCurrent <;> rfl
  let nextDone := done ++ [current]
  let returnWord :=
    dataSymbol current.second :: dataSymbol current.first ::
      (pushLeft crossed [] ++ processedCells nextDone)
  have hScannedSplit : scannedLeft =
      pushLeft crossed [] ++ capturedLeft := by
    dsimp [scannedLeft]
    exact pushLeft_append_far crossed [] capturedLeft
  have hProcessedNext : processedCells nextDone =
      WorkSymbol.blank :: processedCells done := by
    exact processedCells_append_one done current
  have hReturnStart :
      ({ state := returnOuterState
         tape :=
           { left := dataSymbol current.first :: scannedLeft
             head := dataSymbol current.second
             right := [rightMarker] } } : WorkConfiguration) =
        configAtLeftWord returnOuterState
          (returnWord ++ [rightMarker]) [rightMarker] := by
    dsimp [configAtLeftWord, tapeAtLeftWord, returnWord]
    rw [hScannedSplit, hProcessedNext]
    repeat' rw [workList_append_assoc]
    rfl
  have hReturnAllowed : ∀ symbol, List.Mem symbol returnWord →
      symbol ≠ rightMarker := by
    intro symbol found
    dsimp [returnWord] at found
    cases found with
    | head =>
        cases hCurrent <;> intro impossible <;> contradiction
    | tail _ tailOne =>
        cases tailOne with
        | head =>
            cases hCurrent <;> intro impossible <;> contradiction
        | tail _ tailRest =>
            have hPushAllowed : ∀ item,
                List.Mem item (pushLeft crossed []) →
                  item ≠ rightMarker := by
              apply pushLeft_property (fun item => item ≠ rightMarker)
                crossed []
              · intro item itemMem
                exact carryScan_ne_rightMarker
                  (hCrossedAllowed item itemMem)
              · intro item impossible
                contradiction
            have hProcessedAllowed : ∀ item,
                List.Mem item (processedCells nextDone) →
                  item ≠ rightMarker := by
              exact processed_ne_rightMarker nextDone
            exact append_property (fun item => item ≠ rightMarker)
              (pushLeft crossed []) (processedCells nextDone)
              hPushAllowed hProcessedAllowed symbol tailRest
  have hReturnRaw := returnScan_exact returnWord [rightMarker]
    [rightMarker] hReturnAllowed
  have hLayout := central_return_layout done rest current
  dsimp [crossed, nextDone, returnWord] at hLayout
  have hReturn :
      workRunExact? pairedInputFramer returnWord.length
          { state := returnOuterState
            tape :=
              { left := dataSymbol current.first :: scannedLeft
                head := dataSymbol current.second
                right := [rightMarker] } } =
        some (configAtLeftWord returnOuterState [rightMarker]
          (processedCells nextDone ++ rest ++
            leftMarker :: (unpackData nextDone ++ [rightMarker]))) := by
    rw [hReturnStart]
    rw [hLayout] at hReturnRaw
    exact hReturnRaw
  let afterOuterWord := processedCells nextDone ++ rest ++
    leftMarker :: (unpackData nextDone ++ [rightMarker])
  have hOuter :
      workRunExact? pairedInputFramer 1
          (configAtLeftWord returnOuterState [rightMarker] afterOuterWord) =
        some (configAtWord seekUnprocessedState [rightMarker]
          afterOuterWord) := by
    dsimp [afterOuterWord]
    rw [hProcessedNext]
    rfl
  have hSeekRaw := seekBlanks_exact nextDone.length
    (rest ++ leftMarker :: (unpackData nextDone ++ [rightMarker]))
    [rightMarker]
  have hNextProcessedLength : processedCells nextDone =
      List.replicate nextDone.length WorkSymbol.blank := rfl
  have hSeek :
      workRunExact? pairedInputFramer nextDone.length
        (configAtWord seekUnprocessedState [rightMarker]
            afterOuterWord) =
        some (iterationConfig nextDone rest) := by
    have hAfter : afterOuterWord =
        processedCells nextDone ++
          (rest ++ leftMarker ::
            (unpackData nextDone ++ [rightMarker])) := by
      dsimp [afterOuterWord]
      exact workList_append_assoc (processedCells nextDone) rest
        (leftMarker :: (unpackData nextDone ++ [rightMarker]))
    rw [hAfter]
    change workRunExact? pairedInputFramer nextDone.length
        (configAtWord seekUnprocessedState [rightMarker]
          (List.replicate nextDone.length WorkSymbol.blank ++
            (rest ++ leftMarker ::
              (unpackData nextDone ++ [rightMarker])))) = _
    rw [pushLeft_replicateBlank nextDone.length [rightMarker]] at hSeekRaw
    dsimp [iterationConfig, iterationTape]
    cases rest <;> exact hSeekRaw
  have hCaptureCarry := workRunExact_compose pairedInputFramer 1
    crossed.length _ _ _ hCapture hCarry
  have hThroughAppend := workRunExact_compose pairedInputFramer
    (1 + crossed.length) 3 _ _ _ hCaptureCarry hAppend
  have hThroughReturn := workRunExact_compose pairedInputFramer
    ((1 + crossed.length) + 3) returnWord.length _ _ _
    hThroughAppend hReturn
  have hThroughOuter := workRunExact_compose pairedInputFramer
    (((1 + crossed.length) + 3) + returnWord.length) 1 _ _ _
    hThroughReturn hOuter
  have hAll := workRunExact_compose pairedInputFramer
    ((((1 + crossed.length) + 3) + returnWord.length) + 1)
    nextDone.length _ _ _ hThroughOuter hSeek
  have hCrossedLength : crossed.length =
      rest.length + 1 + 2 * done.length := by
    dsimp [crossed]
    rw [workList_length_append]
    change rest.length + Nat.succ (unpackData done).length = _
    rw [unpackData_length]
    calc
      rest.length + Nat.succ (2 * done.length) =
          Nat.succ (rest.length + 2 * done.length) :=
        Nat.add_succ rest.length (2 * done.length)
      _ = Nat.succ rest.length + 2 * done.length :=
        (Nat.succ_add rest.length (2 * done.length)).symm
      _ = rest.length + 1 + 2 * done.length := by
        rw [Nat.add_one]
  have hNextLength : nextDone.length = done.length + 1 := by
    dsimp [nextDone]
    rw [workList_length_append]
    rfl
  have hReturnLength : returnWord.length =
      rest.length + 3 * done.length + 4 := by
    dsimp [returnWord]
    rw [workList_length_append]
    rw [pushLeft_length]
    rw [processedCells_length]
    change Nat.succ (Nat.succ (crossed.length + nextDone.length)) = _
    rw [hCrossedLength, hNextLength]
    exact returnLengthArithmetic rest.length done.length
  rw [hCrossedLength, hNextLength, hReturnLength] at hAll
  have hFuel :
      ((((1 + (rest.length + 1 + 2 * done.length)) + 3) +
          (rest.length + 3 * done.length + 4)) + 1) +
          (done.length + 1) =
        6 * done.length + 2 * rest.length + 11 := by
    exact copyOneFuelArithmetic rest.length done.length
  rw [hFuel] at hAll
  dsimp [nextDone] at hAll ⊢
  exact hAll

private def framedWordTape (word : List WorkSymbol) : WorkTape :=
  frameWithGarbage (encodeWorkTape (WorkTape.ofSymbols word))
    (processedCells word ++ [rightMarker]) []

private def framedWordFinal (word : List WorkSymbol) : WorkConfiguration :=
  { state := pairedInputFramer.acceptState
    tape := framedWordTape word }

private theorem map_dataSymbol_encodeWorkRight (word : List WorkSymbol) :
    (encodeWorkRight word).map dataSymbol = unpackData word := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      change dataSymbol symbol.first :: dataSymbol symbol.second ::
          (encodeWorkRight rest).map dataSymbol =
        dataSymbol symbol.first :: dataSymbol symbol.second :: unpackData rest
      exact congrArg (List.cons (dataSymbol symbol.first))
        (congrArg (List.cons (dataSymbol symbol.second)) ih)

private theorem finish_exact (current : WorkSymbol)
    (rest : List WorkSymbol) :
    workRunExact? pairedInputFramer 1
        (iterationConfig (current :: rest) []) =
      some (framedWordFinal (current :: rest)) := by
  dsimp [iterationConfig, iterationTape, framedWordFinal, framedWordTape,
    pairedInputFramer, frameWithGarbage, encodeWorkTape,
    WorkTape.ofSymbols, processedCells, unpackData]
  rw [map_dataSymbol_encodeWorkRight]
  rfl

private def copySteps : List WorkSymbol → List WorkSymbol → Nat
  | _, [] => 1
  | done, current :: rest =>
      (6 * done.length + 2 * rest.length + 11) +
        copySteps (done ++ [current]) rest

private theorem append_source_word (done : List WorkSymbol)
    (current : WorkSymbol)
    (hDone : ∀ symbol, List.Mem symbol done → SourceSymbol symbol)
    (hCurrent : SourceSymbol current) :
    ∀ symbol, List.Mem symbol (done ++ [current]) →
      SourceSymbol symbol := by
  induction done with
  | nil =>
      intro symbol found
      cases found with
      | head => exact hCurrent
      | tail _ impossible => contradiction
  | cons first rest ih =>
      intro symbol found
      cases found with
      | head => exact hDone first (List.Mem.head rest)
      | tail _ tailMem =>
          apply ih
          · intro item itemMem
            exact hDone item (List.Mem.tail first itemMem)
          · exact tailMem

private theorem copy_exact (done todo : List WorkSymbol)
    (hDone : ∀ symbol, List.Mem symbol done → SourceSymbol symbol)
    (hTodo : ∀ symbol, List.Mem symbol todo → SourceSymbol symbol)
    (hNonempty : done ++ todo ≠ []) :
    workRunExact? pairedInputFramer (copySteps done todo)
        (iterationConfig done todo) =
      some (framedWordFinal (done ++ todo)) := by
  induction todo generalizing done with
  | nil =>
      cases done with
      | nil => exact False.elim (hNonempty rfl)
      | cons current rest =>
          change workRunExact? pairedInputFramer 1
              (iterationConfig (current :: rest) []) =
            some (framedWordFinal ((current :: rest) ++ []))
          rw [workList_append_nil]
          exact finish_exact current rest
  | cons current rest ih =>
      have hCurrent : SourceSymbol current :=
        hTodo current (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest →
          SourceSymbol symbol := by
        intro symbol found
        exact hTodo symbol (List.Mem.tail current found)
      have hOne := copy_one_exact done current rest hDone hCurrent hRest
      have hNextDone := append_source_word done current hDone hCurrent
      have hNextNonempty : (done ++ [current]) ++ rest ≠ [] := by
        intro impossible
        cases done with
        | nil => contradiction
        | cons first tail => contradiction
      have hTail := ih (done ++ [current]) hNextDone hRest hNextNonempty
      have hComposed := workRunExact_compose pairedInputFramer
        (6 * done.length + 2 * rest.length + 11)
        (copySteps (done ++ [current]) rest) _ _ _ hOne hTail
      change workRunExact? pairedInputFramer
          ((6 * done.length + 2 * rest.length + 11) +
            copySteps (done ++ [current]) rest)
          (iterationConfig done (current :: rest)) =
        some (framedWordFinal (done ++ current :: rest))
      have hWords : (done ++ [current]) ++ rest =
          done ++ current :: rest := by
        exact workList_append_assoc done [current] rest
      rw [hWords] at hComposed
      exact hComposed

private theorem natAddMulConstructive (left right factor : Nat) :
    (left + right) * factor = left * factor + right * factor := by
  induction factor with
  | zero => rfl
  | succ factor ih =>
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_succ, ih]
      rw [Nat.add_assoc]
      rw [Nat.add_assoc]
      rw [Nat.add_left_comm (right * factor) left]

private theorem copyStepsSuccArithmetic (doneLength restLength : Nat) :
    (6 * doneLength + 2 * restLength + 11) +
        (6 * (doneLength + 1) * restLength +
          4 * restLength * restLength + 7 * restLength + 1) =
      6 * doneLength * Nat.succ restLength +
        4 * Nat.succ restLength * Nat.succ restLength +
          7 * Nat.succ restLength + 1 := by
  rw [Nat.mul_succ]
  rw [natAddMulConstructive]
  rw [Nat.mul_succ 4 restLength]
  rw [natAddMulConstructive]
  repeat' rw [Nat.mul_succ]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 11 (6 * doneLength * restLength)]
  rw [Nat.add_left_comm (2 * restLength) (6 * doneLength * restLength)]
  rw [Nat.add_left_comm (6 * doneLength) (6 * doneLength * restLength)]
  rw [Nat.add_left_comm (6 * restLength) (4 * restLength * restLength)]
  rw [Nat.add_left_comm 11 (4 * restLength * restLength)]
  rw [Nat.add_left_comm (2 * restLength) (4 * restLength * restLength)]
  rw [Nat.add_left_comm (6 * restLength) (7 * restLength)]
  rw [Nat.add_left_comm 11 (7 * restLength)]
  rw [Nat.add_left_comm (2 * restLength) (7 * restLength)]
  rw [Nat.add_left_comm 4 (7 * restLength)]
  rw [Nat.add_left_comm (4 * restLength) (7 * restLength)]
  rw [Nat.add_left_comm (4 * restLength) (7 * restLength)]
  rw [Nat.two_mul restLength]
  rw [Nat.succ_mul 5 restLength]
  rw [Nat.succ_mul 4 restLength]
  rw [Nat.succ_mul 3 restLength]
  rw [Nat.succ_mul 2 restLength]
  rw [Nat.two_mul restLength]
  repeat' rw [Nat.succ_mul 3 restLength]
  repeat' rw [Nat.succ_mul 2 restLength]
  repeat' rw [Nat.two_mul restLength]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 11 restLength]
  rw [Nat.add_left_comm 11 restLength]
  rw [Nat.add_left_comm 11 restLength]
  rw [Nat.add_left_comm 11 restLength]
  rw [Nat.add_left_comm 11 restLength]
  rw [Nat.add_left_comm 11 restLength]

private theorem copySteps_closed (done todo : List WorkSymbol) :
    copySteps done todo =
      6 * done.length * todo.length +
        4 * todo.length * todo.length + 7 * todo.length + 1 := by
  induction todo generalizing done with
  | nil => rfl
  | cons current rest ih =>
      unfold copySteps
      rw [ih (done ++ [current])]
      rw [workList_length_append]
      change
        (6 * done.length + 2 * rest.length + 11) +
            (6 * (done.length + 1) * rest.length +
              4 * rest.length * rest.length + 7 * rest.length + 1) =
          6 * done.length * Nat.succ rest.length +
            4 * Nat.succ rest.length * Nat.succ rest.length +
              7 * Nat.succ rest.length + 1
      exact copyStepsSuccArithmetic done.length rest.length

private theorem completeFuelArithmetic (wordLength : Nat) :
    (2 * wordLength + 6) +
        (0 + 4 * wordLength * wordLength + 7 * wordLength + 1) =
      4 * wordLength * wordLength + 9 * wordLength + 7 := by
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 0 (4 * wordLength * wordLength)]
  rw [Nat.add_left_comm 6 (4 * wordLength * wordLength)]
  rw [Nat.add_left_comm (2 * wordLength) (4 * wordLength * wordLength)]
  repeat' rw [Nat.add_assoc]
  rw [Nat.add_left_comm 0 (7 * wordLength)]
  rw [Nat.add_left_comm 6 (7 * wordLength)]
  rw [← Nat.add_assoc (2 * wordLength) (7 * wordLength)]
  rw [show 2 * wordLength + 7 * wordLength = 9 * wordLength from
    (natAddMulConstructive 2 7 wordLength).symm]

private theorem complete_word_exact (current : WorkSymbol)
    (rest : List WorkSymbol)
    (hCurrent : SourceSymbol current)
    (hRest : ∀ symbol, List.Mem symbol rest → SourceSymbol symbol) :
    workRunExact? pairedInputFramer
        (inputFramerWorkSteps (current :: rest).length)
        (workStartConfiguration pairedInputFramer
          (WorkTape.ofSymbols (current :: rest))) =
      some (framedWordFinal (current :: rest)) := by
  have hBoot := bootstrap_exact current rest hCurrent hRest
  have hWord : ∀ symbol, List.Mem symbol (current :: rest) →
      SourceSymbol symbol := by
    intro symbol found
    cases found with
    | head => exact hCurrent
    | tail _ tailMem => exact hRest symbol tailMem
  have hCopy := copy_exact [] (current :: rest)
    (by intro symbol impossible; contradiction) hWord (by intro impossible; contradiction)
  have hComposed := workRunExact_compose pairedInputFramer
    (2 * (current :: rest).length + 6)
    (copySteps [] (current :: rest)) _ _ _ hBoot hCopy
  rw [copySteps_closed [] (current :: rest)] at hComposed
  have hFuel :
      (2 * (current :: rest).length + 6) +
          (6 * ([] : List WorkSymbol).length * (current :: rest).length +
            4 * (current :: rest).length * (current :: rest).length +
              7 * (current :: rest).length + 1) =
        inputFramerWorkSteps (current :: rest).length := by
    have hNil : ([] : List WorkSymbol).length = 0 := rfl
    rw [hNil, Nat.mul_zero, Nat.zero_mul]
    change
      (2 * (current :: rest).length + 6) +
          (0 + 4 * (current :: rest).length * (current :: rest).length +
            7 * (current :: rest).length + 1) =
        inputFramerWorkSteps (current :: rest).length
    unfold inputFramerWorkSteps
    exact completeFuelArithmetic (current :: rest).length
  rw [hFuel] at hComposed
  exact hComposed

private def pairedPackedWord (left right : BitString) : List WorkSymbol :=
  packWorkSymbols
    ((BitString.pair left right).map TapeSymbol.ofBool)

private theorem packMapped_even (bits : BitString) (half : Nat)
    (hLength : bits.length = 2 * half) :
    (packWorkSymbols (bits.map TapeSymbol.ofBool)).length = half ∧
      (∀ symbol,
        List.Mem symbol (packWorkSymbols (bits.map TapeSymbol.ofBool)) →
          SourceSymbol symbol) := by
  induction half generalizing bits with
  | zero =>
      cases bits with
      | nil =>
          exact ⟨rfl, by intro symbol impossible; contradiction⟩
      | cons first rest =>
          change Nat.succ rest.length = 0 at hLength
          contradiction
  | succ half ih =>
      cases bits with
      | nil =>
          rw [Nat.mul_succ] at hLength
          contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              rw [Nat.mul_succ] at hLength
              have hImpossible : 0 = Nat.succ (2 * half) :=
                Nat.succ.inj hLength
              contradiction
          | cons second rest =>
              have hRestLength : rest.length = 2 * half := by
                rw [Nat.mul_succ] at hLength
                exact Nat.succ.inj (Nat.succ.inj hLength)
              rcases ih rest hRestLength with ⟨hPackedLength, hPackedSource⟩
              constructor
              · change Nat.succ
                    (packWorkSymbols (rest.map TapeSymbol.ofBool)).length =
                  Nat.succ half
                exact congrArg Nat.succ hPackedLength
              · intro symbol found
                change List.Mem symbol
                  (⟨TapeSymbol.ofBool first, TapeSymbol.ofBool second⟩ ::
                    packWorkSymbols (rest.map TapeSymbol.ofBool)) at found
                cases found with
                | head =>
                    cases first <;> cases second
                    · exact .zeroZero
                    · exact .zeroOne
                    · exact .oneZero
                    · exact .oneOne
                | tail _ tailMem => exact hPackedSource symbol tailMem

private theorem pairedPackedWord_length (left right : BitString) :
    (pairedPackedWord left right).length = packedPairCount left right := by
  have hPair := pair_length_normalized left right
  have hEven := packMapped_even (BitString.pair left right)
    (packedPairCount left right) hPair
  exact hEven.1

private theorem pairedPackedWord_source (left right : BitString) :
    ∀ symbol, List.Mem symbol (pairedPackedWord left right) →
      SourceSymbol symbol := by
  have hPair := pair_length_normalized left right
  have hEven := packMapped_even (BitString.pair left right)
    (packedPairCount left right) hPair
  exact hEven.2

private theorem pairedPackedWord_ne_nil (left right : BitString) :
    pairedPackedWord left right ≠ [] := by
  exact packWorkSymbols_paired_ne_nil left right

private theorem pairedWorkTape_eq_packedWord (left right : BitString) :
    pairedWorkTape left right = WorkTape.ofSymbols
      (pairedPackedWord left right) := by
  rfl

/-! ### Canonical endpoint and exact budgets -/

def pairedInputFramerOutsideLeft (left right : BitString) : List WorkSymbol :=
  List.replicate (packedPairCount left right) WorkSymbol.blank ++ [rightMarker]

def pairedInputFramerFinalTape (left right : BitString) : WorkTape :=
  frameWithGarbage (Tape.ofInput (BitString.pair left right))
    (pairedInputFramerOutsideLeft left right) []

def pairedInputFramerFinalConfiguration (left right : BitString) :
    WorkConfiguration :=
  { state := pairedInputFramer.acceptState
    tape := pairedInputFramerFinalTape left right }

theorem pairedInputFramerFinal_represents (left right : BitString) :
    Represents (Tape.ofInput (BitString.pair left right))
      (pairedInputFramerFinalTape left right) := by
  exact frameWithGarbage_represents _ _ _

/-- The finite framer consumes every packed cell and reaches a represented
endpoint in exactly `4 * k * k + 9 * k + 7` work transitions. -/
theorem pairedInputFramer_workRunExact (left right : BitString) :
    workRunExact? pairedInputFramer
        (inputFramerWorkSteps (packedPairCount left right))
        (workStartConfiguration pairedInputFramer
          (pairedWorkTape left right)) =
      some (pairedInputFramerFinalConfiguration left right) := by
  let word := pairedPackedWord left right
  have hNonempty : word ≠ [] := pairedPackedWord_ne_nil left right
  cases hWord : word with
  | nil => exact False.elim (hNonempty hWord)
  | cons current rest =>
      have hSource := pairedPackedWord_source left right
      have hSourceWord : ∀ symbol, List.Mem symbol word →
          SourceSymbol symbol := by
        dsimp [word]
        exact hSource
      rw [hWord] at hSourceWord
      have hCurrent : SourceSymbol current := by
        exact hSourceWord current (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest →
          SourceSymbol symbol := by
        intro symbol found
        exact hSourceWord symbol (List.Mem.tail current found)
      have hExact := complete_word_exact current rest hCurrent hRest
      have hLength := pairedPackedWord_length left right
      have hTape := pairedWorkTape_eq_packedWord left right
      have hFinal : framedWordFinal word =
          pairedInputFramerFinalConfiguration left right := by
        dsimp [framedWordFinal, framedWordTape,
          pairedInputFramerFinalConfiguration, pairedInputFramerFinalTape,
          pairedInputFramerOutsideLeft]
        rw [← hTape]
        rw [encodeWorkTape_pairedWorkTape]
        unfold processedCells
        rw [hLength]
      rw [← hWord] at hExact
      rw [hLength] at hExact
      rw [← hTape] at hExact
      rw [hFinal] at hExact
      exact hExact

/-- Exact compiled raw budget as a polynomial in paired raw input length. -/
def pairedInputFramerRawTimeBound : NatPolynomial :=
  .add (.quadratic 6 42) (.linear 27 0)

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

private theorem addSwapMiddleSafe (left middle right : Nat) :
    (left + middle) + right = (left + right) + middle := by
  calc
    (left + middle) + right = left + (middle + right) :=
      Nat.add_assoc _ _ _
    _ = left + (right + middle) :=
      congrArg (Nat.add left) (Nat.add_comm middle right)
    _ = (left + right) + middle :=
      (Nat.add_assoc _ _ _).symm

private theorem twiceSquareSafe (packedCells : Nat) :
    (2 * packedCells) * (2 * packedCells) =
      4 * packedCells * packedCells := by
  calc
    (2 * packedCells) * (2 * packedCells) =
        2 * (packedCells * (2 * packedCells)) :=
      mulAssocSafe 2 packedCells (2 * packedCells)
    _ = 2 * ((packedCells * 2) * packedCells) :=
      congrArg (Nat.mul 2)
        (mulAssocSafe packedCells 2 packedCells).symm
    _ = 2 * ((2 * packedCells) * packedCells) :=
      congrArg (Nat.mul 2)
        (congrArg (fun value => value * packedCells)
          (Nat.mul_comm packedCells 2))
    _ = (2 * (2 * packedCells)) * packedCells :=
      (mulAssocSafe 2 (2 * packedCells) packedCells).symm
    _ = ((2 * 2) * packedCells) * packedCells :=
      congrArg (fun value => value * packedCells)
        (mulAssocSafe 2 2 packedCells).symm
    _ = 4 * packedCells * packedCells := rfl

private theorem quadraticSafe (packedCells : Nat) :
    6 * (2 * packedCells) * (2 * packedCells) =
      6 * (4 * packedCells * packedCells) := by
  calc
    6 * (2 * packedCells) * (2 * packedCells) =
        6 * ((2 * packedCells) * (2 * packedCells)) :=
      mulAssocSafe 6 (2 * packedCells) (2 * packedCells)
    _ = 6 * (4 * packedCells * packedCells) :=
      congrArg (Nat.mul 6) (twiceSquareSafe packedCells)

private theorem linearSafe (packedCells : Nat) :
    27 * (2 * packedCells) = 6 * (9 * packedCells) := by
  calc
    27 * (2 * packedCells) = (27 * 2) * packedCells :=
      (mulAssocSafe 27 2 packedCells).symm
    _ = 54 * packedCells := rfl
    _ = (6 * 9) * packedCells := rfl
    _ = 6 * (9 * packedCells) := mulAssocSafe 6 9 packedCells

private theorem rawBudgetArithmetic (packedCells : Nat) :
    (6 * (2 * packedCells) * (2 * packedCells) + 42) +
        (27 * (2 * packedCells) + 0) =
      6 * inputFramerWorkSteps packedCells := by
  unfold inputFramerWorkSteps
  calc
    (6 * (2 * packedCells) * (2 * packedCells) + 42) +
          (27 * (2 * packedCells) + 0) =
        (6 * (2 * packedCells) * (2 * packedCells) + 42) +
          27 * (2 * packedCells) :=
      congrArg
        (fun value =>
          (6 * (2 * packedCells) * (2 * packedCells) + 42) + value)
        (Nat.add_zero _)
    _ = (6 * (2 * packedCells) * (2 * packedCells) +
          27 * (2 * packedCells)) + 42 :=
      addSwapMiddleSafe _ _ _
    _ = (6 * (4 * packedCells * packedCells) +
          6 * (9 * packedCells)) + 42 :=
      congrArg (fun value => value + 42)
        (Eq.trans
          (congrArg (fun value => value + 27 * (2 * packedCells))
            (quadraticSafe packedCells))
          (congrArg (Nat.add (6 * (4 * packedCells * packedCells)))
            (linearSafe packedCells)))
    _ = 6 * (4 * packedCells * packedCells + 9 * packedCells) + 42 :=
      congrArg (fun value => value + 42)
        (Nat.mul_add 6 (4 * packedCells * packedCells)
          (9 * packedCells)).symm
    _ = 6 * (4 * packedCells * packedCells + 9 * packedCells) +
          6 * 7 := rfl
    _ = 6 * (4 * packedCells * packedCells + 9 * packedCells + 7) :=
      (Nat.mul_add 6
        (4 * packedCells * packedCells + 9 * packedCells) 7).symm

/-- On paired input, the displayed raw polynomial is exactly six times the
proved work-transition count, not merely an asymptotic upper bound. -/
theorem pairedInputFramerRawTimeBound_exact (left right : BitString) :
    pairedInputFramerRawTimeBound.eval
        (BitString.size (BitString.pair left right)) =
      6 * inputFramerWorkSteps (packedPairCount left right) := by
  have hSize := pair_length_normalized left right
  change (BitString.pair left right).length =
      2 * packedPairCount left right at hSize
  change
    (6 * BitString.size (BitString.pair left right) *
          BitString.size (BitString.pair left right) + 42) +
        (27 * BitString.size (BitString.pair left right) + 0) = _
  unfold BitString.size
  rw [hSize]
  exact rawBudgetArithmetic (packedPairCount left right)

/-- The literal compiled raw machine starts from ordinary `startConfig` on
the canonical pair and reaches the encoding of the represented endpoint at
the exact displayed polynomial budget. -/
theorem run_compilePairedInputFramer_rawTimeBound
    (left right : BitString) :
    run (compileWorkMachine pairedInputFramer)
        (pairedInputFramerRawTimeBound.eval
          (BitString.size (BitString.pair left right)))
        (startConfig (compileWorkMachine pairedInputFramer)
          (BitString.pair left right)) =
      encodeWorkConfiguration
        (pairedInputFramerFinalConfiguration left right) := by
  have hExact := pairedInputFramer_workRunExact left right
  have hCompiled := run_compileWorkMachine_mul_of_workRunExact
    pairedInputFramer
    (inputFramerWorkSteps (packedPairCount left right))
    (workStartConfiguration pairedInputFramer (pairedWorkTape left right))
    (pairedInputFramerFinalConfiguration left right) hExact
  rw [← startConfig_compileWorkMachine_paired pairedInputFramer left right]
    at hCompiled
  rw [← pairedInputFramerRawTimeBound_exact left right] at hCompiled
  exact hCompiled

/-- The represented endpoint is the framer's designated accept halt. -/
theorem pairedInputFramerFinal_isHalted (left right : BitString) :
    pairedInputFramer.isHalted
      (pairedInputFramerFinalConfiguration left right) = true := by
  rfl

/-- The compiled finite machine therefore accepts every canonical pair at its
proved local framing budget. -/
theorem boundedDecide_compilePairedInputFramer_accept
    (left right : BitString) :
    boundedDecide (compileWorkMachine pairedInputFramer)
        (pairedInputFramerRawTimeBound.eval
          (BitString.size (BitString.pair left right)))
        (BitString.pair left right) = .accept := by
  unfold boundedDecide
  rw [run_compilePairedInputFramer_rawTimeBound]
  rfl

end PipelineInputFramer

end PNP.Concrete
