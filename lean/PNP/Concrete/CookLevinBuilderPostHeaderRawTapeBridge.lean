/-
Copyright (c) 2026 PNP Labs.

A fixed literal tape bridge from the two post-header terminal paths of the
Cook-Levin raw header router into a shielded input region for the exact unary
quotient/remainder divider.

The bridge consumes the exact M209 equality/greater tape layout through two
raw control-state entries, rather than accepting a supplied remainder. It
copies zero or the exact positive shifted remainder, copies the positive
problem-derived clause width, and preserves arbitrary builder workspace behind
the router boundary. It does not emit a formula token or complete the builder.
-/

import PNP.Concrete.CookLevinBuilderPostHeaderRawLaunch

namespace PNP.Concrete

namespace CookLevin

namespace BuilderPostHeaderRawTapeBridge

open BuilderArbitrarySlotHeaderRouter
  BuilderArbitrarySlotPostHeaderDecoder

private abbrev StateAction := BuilderUnaryPolynomial.StateAction
private abbrev StateSpec := BuilderUnaryPolynomial.StateSpec

abbrev unitSymbol : WorkSymbol := BuilderUnaryPolynomial.unitSymbol
abbrev separatorSymbol : WorkSymbol := BuilderUnaryPolynomial.separatorSymbol
abbrev endSymbol : WorkSymbol := BuilderUnaryPolynomial.scratchEndSymbol
abbrev coordinateMark : WorkSymbol := BuilderUnaryPolynomial.registerMarkSymbol
abbrev boundaryMark : WorkSymbol :=
  BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark
abbrev leftBoundary : WorkSymbol := PipelineTape.leftMarker

/-- Marks one shifted-remainder unit after it has been copied. -/
def copiedRemainderMark : WorkSymbol := WorkSymbol.oneBlank

/-- Marks one width unit after it has been copied. -/
def copiedWidthMark : WorkSymbol := WorkSymbol.zeroBlank

private def keepAction := BuilderUnaryPolynomial.keepAction
private def writeAction := BuilderUnaryPolynomial.writeAction
private def deadAction := BuilderUnaryPolynomial.deadAction

/-! ## Fixed literal bridge table -/

private def equalEntrySpec : StateSpec := fun read =>
  if read = endSymbol then keepAction 2 .right read else deadAction 38 read

private def greaterEntrySpec : StateSpec := fun read =>
  if read = endSymbol then keepAction 3 .right read else deadAction 38 read

private def equalRequireWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 4 .right read else deadAction 38 read

private def greaterRequireWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 5 .right read else deadAction 38 read

private def equalScanWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 4 .right read
  else if read = separatorSymbol then keepAction 22 .right read
  else deadAction 38 read

private def greaterScanWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 5 .right read
  else if read = separatorSymbol then keepAction 6 .right read
  else deadAction 38 read

private def greaterShieldSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 7 .right read else deadAction 38 read

private def greaterWriteLeadingSpec : StateSpec := fun read =>
  if read = WorkSymbol.blank then
    writeAction 8 unitSymbol .left
  else
    deadAction 38 read

private def greaterRewindOutputSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 9 .left read else deadAction 38 read

private def greaterRewindSeparatorSpec : StateSpec := fun read =>
  if read = separatorSymbol then keepAction 10 .left read else deadAction 38 read

private def greaterRewindWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 10 .left read
  else if read = endSymbol then keepAction 11 .stay read
  else deadAction 38 read

private def copyStartSpec : StateSpec := fun read =>
  if read = endSymbol then keepAction 12 .left read else deadAction 38 read

private def copySeekSpec : StateSpec := fun read =>
  if read = boundaryMark ∨ read = separatorSymbol ∨
      read = copiedRemainderMark then
    keepAction 12 .left read
  else if read = unitSymbol then
    writeAction 13 copiedRemainderMark .right
  else if read = coordinateMark then
    keepAction 20 .right read
  else
    deadAction 38 read

private def copyReturnEndSpec : StateSpec := fun read =>
  if read = copiedRemainderMark ∨ read = separatorSymbol ∨
      read = boundaryMark then
    keepAction 13 .right read
  else if read = endSymbol then
    keepAction 14 .right read
  else
    deadAction 38 read

private def copyScanWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 14 .right read
  else if read = separatorSymbol then keepAction 15 .right read
  else deadAction 38 read

private def copyShieldSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 16 .right read else deadAction 38 read

private def copyWriteSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 16 .right read
  else if read = WorkSymbol.blank then
    writeAction 17 unitSymbol .left
  else
    deadAction 38 read

private def copyRewindOutputSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 17 .left read
  else if read = leftBoundary then keepAction 18 .left read
  else deadAction 38 read

private def copyRewindSeparatorSpec : StateSpec := fun read =>
  if read = separatorSymbol then keepAction 19 .left read else deadAction 38 read

private def copyRewindWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 19 .left read
  else if read = endSymbol then keepAction 11 .stay read
  else deadAction 38 read

private def finishReturnEndSpec : StateSpec := fun read =>
  if read = coordinateMark ∨ read = copiedRemainderMark ∨
      read = separatorSymbol ∨ read = boundaryMark then
    keepAction 20 .right read
  else if read = endSymbol then
    keepAction 21 .right read
  else
    deadAction 38 read

private def finishScanWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 21 .right read
  else if read = separatorSymbol then keepAction 22 .right read
  else deadAction 38 read

private def finishShieldSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 23 .right read else deadAction 38 read

private def finishWriteSeparatorSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 23 .right read
  else if read = WorkSymbol.blank then
    writeAction 24 separatorSymbol .left
  else
    deadAction 38 read

private def finishRewindOutputSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 24 .left read
  else if read = leftBoundary then keepAction 25 .left read
  else deadAction 38 read

private def finishRewindSeparatorSpec : StateSpec := fun read =>
  if read = separatorSymbol then keepAction 26 .left read else deadAction 38 read

private def finishRewindWidthSpec : StateSpec := fun read =>
  if read = unitSymbol then keepAction 26 .left read
  else if read = endSymbol then keepAction 27 .stay read
  else deadAction 38 read

private def widthStartSpec : StateSpec := fun read =>
  if read = endSymbol then keepAction 28 .right read else deadAction 38 read

private def widthSeekSpec : StateSpec := fun read =>
  if read = copiedWidthMark then keepAction 28 .right read
  else if read = unitSymbol then
    writeAction 29 copiedWidthMark .right
  else if read = separatorSymbol then
    keepAction 35 .right read
  else
    deadAction 38 read

private def widthReturnSeparatorSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = copiedWidthMark then
    keepAction 29 .right read
  else if read = separatorSymbol then
    keepAction 30 .right read
  else
    deadAction 38 read

private def widthShieldSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 31 .right read else deadAction 38 read

private def widthWriteSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol then
    keepAction 31 .right read
  else if read = WorkSymbol.blank then
    writeAction 32 unitSymbol .left
  else
    deadAction 38 read

private def widthRewindOutputSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol then
    keepAction 32 .left read
  else if read = leftBoundary then
    keepAction 33 .left read
  else
    deadAction 38 read

private def widthRewindSeparatorSpec : StateSpec := fun read =>
  if read = separatorSymbol then keepAction 34 .left read else deadAction 38 read

private def widthRewindSidecarSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = copiedWidthMark then
    keepAction 34 .left read
  else if read = endSymbol then
    keepAction 27 .stay read
  else
    deadAction 38 read

private def finalShieldSpec : StateSpec := fun read =>
  if read = leftBoundary then keepAction 36 .right read else deadAction 38 read

private def finalWriteEndSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol then
    keepAction 36 .right read
  else if read = WorkSymbol.blank then
    writeAction 37 endSymbol .left
  else
    deadAction 38 read

private def finalRewindOutputSpec : StateSpec := fun read =>
  if read = unitSymbol ∨ read = separatorSymbol then
    keepAction 37 .left read
  else if read = leftBoundary then
    keepAction 39 .right read
  else
    deadAction 38 read

private def deadSpec : StateSpec := fun read => deadAction 38 read

private def stateSpecs : List StateSpec :=
  [equalEntrySpec, greaterEntrySpec, equalRequireWidthSpec,
    greaterRequireWidthSpec, equalScanWidthSpec, greaterScanWidthSpec,
    greaterShieldSpec, greaterWriteLeadingSpec,
    greaterRewindOutputSpec, greaterRewindSeparatorSpec,
    greaterRewindWidthSpec, copyStartSpec, copySeekSpec,
    copyReturnEndSpec, copyScanWidthSpec, copyShieldSpec, copyWriteSpec,
    copyRewindOutputSpec, copyRewindSeparatorSpec, copyRewindWidthSpec,
    finishReturnEndSpec, finishScanWidthSpec, finishShieldSpec,
    finishWriteSeparatorSpec, finishRewindOutputSpec,
    finishRewindSeparatorSpec, finishRewindWidthSpec, widthStartSpec,
    widthSeekSpec, widthReturnSeparatorSpec, widthShieldSpec,
    widthWriteSpec, widthRewindOutputSpec, widthRewindSeparatorSpec,
    widthRewindSidecarSpec, finalShieldSpec, finalWriteEndSpec,
    finalRewindOutputSpec, deadSpec]

def rules : List WorkRule := BuilderUnaryPolynomial.rulesFrom 0 stateSpecs

/-- One fixed 351-rule bridge. State 39 accepts, state 40 rejects, and state
38 is a nonhalting malformed-input sink. -/
def machine : WorkMachine :=
  { rules := rules
    startState := 0
    acceptState := 39
    rejectState := 40 }

theorem rules_length : rules.length = 351 := by
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

/-! ## Canonical M209 inputs and shielded M211 endpoint -/

def widthSidecar (width : Nat) : List WorkSymbol :=
  List.replicate width unitSymbol ++ [separatorSymbol, leftBoundary]

def extendRouterResultTape (tape : WorkTape) (width : Nat)
    (workspace : List WorkSymbol) : WorkTape :=
  { left := tape.left ++ workspace
    head := tape.head
    right := widthSidecar width }

def equalInputTape (processed width : Nat)
    (workspace : List WorkSymbol) : WorkTape :=
  extendRouterResultTape
    (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
      (.equal processed)).tape width workspace

def greaterInputTape (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) : WorkTape :=
  extendRouterResultTape
    (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
      (.greater processed remainingCoordinate)).tape width workspace

def equalInputConfiguration (processed width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := 0, tape := equalInputTape processed width workspace }

def greaterInputConfiguration (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := 1
    tape := greaterInputTape processed remainingCoordinate width workspace }

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

def dividerWord (remainder width : Nat) : List WorkSymbol :=
  List.replicate remainder unitSymbol ++
    separatorSymbol ::
      (List.replicate width unitSymbol ++ [endSymbol])

def equalExterior (processed width : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  separatorSymbol ::
    (List.replicate width copiedWidthMark ++
      endSymbol ::
        ((BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
          (.equal processed)).tape.left ++ workspace))

def greaterExterior (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  separatorSymbol ::
    (List.replicate width copiedWidthMark ++
      endSymbol ::
        (List.replicate processed boundaryMark ++
          separatorSymbol ::
            (List.replicate remainingCoordinate copiedRemainderMark ++
              List.replicate (processed + 1) coordinateMark ++
                leftBoundary :: workspace)))

def shieldedDividerInputTape (remainder width : Nat)
    (exterior : List WorkSymbol) : WorkTape :=
  rightPathTape (leftBoundary :: exterior) (dividerWord remainder width)

private def equalRouterLeft (processed : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
    (.equal processed)).tape.left ++ workspace

private def greaterRouterLeft (processed remainingCoordinate : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  List.replicate processed boundaryMark ++
    separatorSymbol ::
      (List.replicate remainingCoordinate unitSymbol ++
        List.replicate (processed + 1) coordinateMark ++
          leftBoundary :: workspace)

private def greaterCopiedRouterLeft (processed copied remaining : Nat)
    (workspace : List WorkSymbol) : List WorkSymbol :=
  List.replicate processed boundaryMark ++
    separatorSymbol ::
      (List.replicate copied copiedRemainderMark ++
        List.replicate remaining unitSymbol ++
          List.replicate (processed + 1) coordinateMark ++
            leftBoundary :: workspace)

private def bridgeRight (width : Nat) (output : List WorkSymbol) :
    List WorkSymbol :=
  List.replicate width unitSymbol ++
    separatorSymbol :: leftBoundary :: output

private def copyLoopConfiguration (processed copied remaining width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := 11
    tape :=
      { left := greaterCopiedRouterLeft processed copied remaining workspace
        head := endSymbol
        right := bridgeRight width
          (List.replicate (copied + 1) unitSymbol) } }

private def widthLoopConfiguration (routerLeft : List WorkSymbol)
    (remainder copied remaining : Nat) : WorkConfiguration :=
  { state := 27
    tape :=
      { left := routerLeft
        head := endSymbol
        right :=
          List.replicate copied copiedWidthMark ++
            List.replicate remaining unitSymbol ++
              separatorSymbol ::
                leftBoundary ::
                  (List.replicate remainder unitSymbol ++
                    separatorSymbol ::
                      List.replicate copied unitSymbol) } }

private def bridgeFinalConfiguration (routerLeft : List WorkSymbol)
    (remainder width : Nat) : WorkConfiguration :=
  { state := machine.acceptState
    tape := shieldedDividerInputTape remainder width
      (separatorSymbol ::
        (List.replicate width copiedWidthMark ++
          endSymbol :: routerLeft)) }

/-- Exact work cost of the equality/greater setup before the copied remainder
has been completed. -/
def prefixWorkSteps (width : Nat) : Nat := 2 * width + 7

/-- One copied tail unit, or the final coordinate-marker boundary, at the
current copied-prefix length. -/
def copyCycleSteps (processed copied width : Nat) : Nat :=
  2 * processed + 4 * copied + 2 * width + 13

/-- Copy every remaining unary tail unit and then consume the coordinate
marker that certifies the strict branch's additional leading unit. -/
def copyAllSteps (processed copied width : Nat) : Nat → Nat
  | 0 => copyCycleSteps processed copied width
  | remaining + 1 =>
      copyCycleSteps processed copied width +
        copyAllSteps processed (copied + 1) width remaining

/-- One sidecar-width copy cycle. -/
def widthCycleSteps (remainder copied remaining : Nat) : Nat :=
  4 * copied + 2 * remaining + 2 * remainder + 9

/-- Final end-marker append and rewind after every width unit was copied. -/
def widthFinishSteps (remainder copied : Nat) : Nat :=
  3 * copied + 2 * remainder + 7

/-- Copy every remaining width unit and finish on the first divider cell. -/
def widthAllSteps (remainder copied : Nat) : Nat → Nat
  | 0 => widthFinishSteps remainder copied
  | remaining + 1 =>
      widthCycleSteps remainder copied (remaining + 1) +
        widthAllSteps remainder (copied + 1) remaining

/-- Exact M213 work cost on an equality endpoint. -/
def equalWorkSteps (width : Nat) : Nat :=
  prefixWorkSteps width + widthAllSteps 0 0 width

/-- Exact M213 work cost on a strict post-header endpoint. -/
def greaterWorkSteps (processed remainingCoordinate width : Nat) : Nat :=
  prefixWorkSteps width +
    copyAllSteps processed 0 width remainingCoordinate +
      widthAllSteps (remainingCoordinate + 1) 0 width

private theorem equal_prefix_exact (processed widthTail : Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine (prefixWorkSteps (widthTail + 1))
        (equalInputConfiguration processed (widthTail + 1) workspace) =
      some (widthLoopConfiguration
        (equalRouterLeft processed workspace) 0 0 (widthTail + 1)) := by
  let routerLeft := equalRouterLeft processed workspace
  let c0 := equalInputConfiguration processed (widthTail + 1) workspace
  let c1 : WorkConfiguration :=
    { state := 2
      tape := rightPathTape (endSymbol :: routerLeft)
        (unitSymbol ::
          (List.replicate widthTail unitSymbol ++
            [separatorSymbol, leftBoundary])) }
  let c2 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape (unitSymbol :: endSymbol :: routerLeft)
        (List.replicate widthTail unitSymbol ++
          [separatorSymbol, leftBoundary]) }
  let c3 : WorkConfiguration :=
    { state := 4
      tape := rightPathTape
        (List.replicate widthTail unitSymbol ++
          unitSymbol :: endSymbol :: routerLeft)
        [separatorSymbol, leftBoundary] }
  let c4 : WorkConfiguration :=
    { state := 22
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft)
        [leftBoundary] }
  let c5 : WorkConfiguration :=
    { state := 23
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) [] }
  let c6 : WorkConfiguration :=
    { state := 24
      tape := leftPathTape [separatorSymbol]
        (leftBoundary :: separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) }
  let c7 : WorkConfiguration :=
    { state := 25
      tape := leftPathTape [leftBoundary, separatorSymbol]
        (separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) }
  let c8 : WorkConfiguration :=
    { state := 26
      tape := leftPathTape
        [separatorSymbol, leftBoundary, separatorSymbol]
        (List.replicate (widthTail + 1) unitSymbol ++
          endSymbol :: routerLeft) }
  let c9 : WorkConfiguration :=
    { state := 26
      tape := leftPathTape
        (List.replicate (widthTail + 1) unitSymbol ++
          [separatorSymbol, leftBoundary, separatorSymbol])
        (endSymbol :: routerLeft) }
  let c10 := widthLoopConfiguration routerLeft 0 0 (widthTail + 1)
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    simp [c0, c1, equalInputConfiguration, equalInputTape,
      extendRouterResultTape, widthSidecar, routerLeft, equalRouterLeft,
      BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
      List.replicate_succ]
    rfl
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    rfl
  have h23 : workRunExact? machine widthTail c2 = some c3 := by
    exact scanRight_replicate_exact 4 unitSymbol widthTail
      (unitSymbol :: endSymbol :: routerLeft)
      [separatorSymbol, leftBoundary] (by intro left right; rfl)
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    rfl
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    rfl
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    rfl
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    rfl
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    simp [c7, c8, replicate_append_self_cons, List.replicate_succ]
    rfl
  have h89 : workRunExact? machine (widthTail + 1) c8 = some c9 := by
    exact scanLeft_replicate_exact 26 unitSymbol (widthTail + 1)
      [separatorSymbol, leftBoundary, separatorSymbol]
      (endSymbol :: routerLeft) (by intro left right; rfl)
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    2 widthTail c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1) 1 c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1) 1 c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1 + 1) (widthTail + 1)
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1 + 1 + (widthTail + 1)) 1
    c0 c9 c10 h09 h910
  have hCount :
      2 + widthTail + 1 + 1 + 1 + 1 + 1 + (widthTail + 1) + 1 =
        prefixWorkSteps (widthTail + 1) := by
    unfold prefixWorkSteps
    omega
  rw [← hCount]
  simpa [c0, c10] using h010

private theorem greater_prefix_exact (processed remainingCoordinate widthTail : Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine (prefixWorkSteps (widthTail + 1))
        (greaterInputConfiguration processed remainingCoordinate
          (widthTail + 1) workspace) =
      some (copyLoopConfiguration processed 0 remainingCoordinate
        (widthTail + 1) workspace) := by
  let routerLeft := greaterRouterLeft processed remainingCoordinate workspace
  let c0 := greaterInputConfiguration processed remainingCoordinate
    (widthTail + 1) workspace
  let c1 : WorkConfiguration :=
    { state := 3
      tape := rightPathTape (endSymbol :: routerLeft)
        (unitSymbol ::
          (List.replicate widthTail unitSymbol ++
            [separatorSymbol, leftBoundary])) }
  let c2 : WorkConfiguration :=
    { state := 5
      tape := rightPathTape (unitSymbol :: endSymbol :: routerLeft)
        (List.replicate widthTail unitSymbol ++
          [separatorSymbol, leftBoundary]) }
  let c3 : WorkConfiguration :=
    { state := 5
      tape := rightPathTape
        (List.replicate widthTail unitSymbol ++
          unitSymbol :: endSymbol :: routerLeft)
        [separatorSymbol, leftBoundary] }
  let c4 : WorkConfiguration :=
    { state := 6
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft)
        [leftBoundary] }
  let c5 : WorkConfiguration :=
    { state := 7
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) [] }
  let c6 : WorkConfiguration :=
    { state := 8
      tape := leftPathTape [unitSymbol]
        (leftBoundary :: separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) }
  let c7 : WorkConfiguration :=
    { state := 9
      tape := leftPathTape [leftBoundary, unitSymbol]
        (separatorSymbol ::
          List.replicate widthTail unitSymbol ++
            unitSymbol :: endSymbol :: routerLeft) }
  let c8 : WorkConfiguration :=
    { state := 10
      tape := leftPathTape
        [separatorSymbol, leftBoundary, unitSymbol]
        (List.replicate (widthTail + 1) unitSymbol ++
          endSymbol :: routerLeft) }
  let c9 : WorkConfiguration :=
    { state := 10
      tape := leftPathTape
        (List.replicate (widthTail + 1) unitSymbol ++
          [separatorSymbol, leftBoundary, unitSymbol])
        (endSymbol :: routerLeft) }
  let c10 := copyLoopConfiguration processed 0 remainingCoordinate
    (widthTail + 1) workspace
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    simp [c0, c1, greaterInputConfiguration, greaterInputTape,
      extendRouterResultTape, widthSidecar, routerLeft, greaterRouterLeft,
      BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration,
      List.replicate_succ]
    rfl
  have h12 : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    rfl
  have h23 : workRunExact? machine widthTail c2 = some c3 := by
    exact scanRight_replicate_exact 5 unitSymbol widthTail
      (unitSymbol :: endSymbol :: routerLeft)
      [separatorSymbol, leftBoundary] (by intro left right; rfl)
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    rfl
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    rfl
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    rfl
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    rfl
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    simp [c7, c8, replicate_append_self_cons, List.replicate_succ]
    rfl
  have h89 : workRunExact? machine (widthTail + 1) c8 = some c9 := by
    exact scanLeft_replicate_exact 10 unitSymbol (widthTail + 1)
      [separatorSymbol, leftBoundary, unitSymbol]
      (endSymbol :: routerLeft) (by intro left right; rfl)
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    simp [c9, c10, copyLoopConfiguration, bridgeRight,
      greaterCopiedRouterLeft, routerLeft, greaterRouterLeft]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 1 c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    2 widthTail c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1) 1 c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1) 1 c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1 + 1) (widthTail + 1)
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (2 + widthTail + 1 + 1 + 1 + 1 + 1 + (widthTail + 1)) 1
    c0 c9 c10 h09 h910
  have hCount :
      2 + widthTail + 1 + 1 + 1 + 1 + 1 + (widthTail + 1) + 1 =
        prefixWorkSteps (widthTail + 1) := by
    unfold prefixWorkSteps
    omega
  rw [← hCount]
  simpa [c0, c10] using h010

private theorem copy_unit_cycle_exact
    (processed copied remainingTail widthTail : Nat)
    (workspace : List WorkSymbol) :
    workRunExact? machine
        (copyCycleSteps processed copied (widthTail + 1))
        (copyLoopConfiguration processed copied (remainingTail + 1)
          (widthTail + 1) workspace) =
      some (copyLoopConfiguration processed (copied + 1) remainingTail
        (widthTail + 1) workspace) := by
  let width := widthTail + 1
  let oldOutput := List.replicate (copied + 1) unitSymbol
  let copiedTail :=
    List.replicate copied copiedRemainderMark ++
      List.replicate (remainingTail + 1) unitSymbol ++
        List.replicate (processed + 1) coordinateMark ++
          leftBoundary :: workspace
  let afterCopiedTail :=
    List.replicate (remainingTail + 1) unitSymbol ++
      List.replicate (processed + 1) coordinateMark ++
        leftBoundary :: workspace
  let afterMarkedTail :=
    List.replicate remainingTail unitSymbol ++
      List.replicate (processed + 1) coordinateMark ++
        leftBoundary :: workspace
  let markedRouterLeft :=
    List.replicate processed boundaryMark ++
      separatorSymbol ::
        (List.replicate copied copiedRemainderMark ++
          copiedRemainderMark :: afterMarkedTail)
  let c0 := copyLoopConfiguration processed copied (remainingTail + 1)
    width workspace
  let c1 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape (endSymbol :: bridgeRight width oldOutput)
        (List.replicate processed boundaryMark ++
          separatorSymbol :: copiedTail) }
  let c2 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
        (separatorSymbol :: copiedTail) }
  let c3 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (separatorSymbol ::
          List.replicate processed boundaryMark ++
            endSymbol :: bridgeRight width oldOutput)
        copiedTail }
  let c4 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (List.replicate copied copiedRemainderMark ++
          separatorSymbol ::
            List.replicate processed boundaryMark ++
              endSymbol :: bridgeRight width oldOutput)
        afterCopiedTail }
  let c5 : WorkConfiguration :=
    { state := 13
      tape := rightPathTape (copiedRemainderMark :: afterMarkedTail)
        (List.replicate copied copiedRemainderMark ++
          separatorSymbol ::
            List.replicate processed boundaryMark ++
              endSymbol :: bridgeRight width oldOutput) }
  let c6 : WorkConfiguration :=
    { state := 13
      tape := rightPathTape
        (List.replicate copied copiedRemainderMark ++
          copiedRemainderMark :: afterMarkedTail)
        (separatorSymbol ::
          List.replicate processed boundaryMark ++
            endSymbol :: bridgeRight width oldOutput) }
  let c7 : WorkConfiguration :=
    { state := 13
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate copied copiedRemainderMark ++
            copiedRemainderMark :: afterMarkedTail)
        (List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput) }
  let c8 : WorkConfiguration :=
    { state := 13
      tape := rightPathTape markedRouterLeft
        (endSymbol :: bridgeRight width oldOutput) }
  let c9 : WorkConfiguration :=
    { state := 14
      tape := rightPathTape (endSymbol :: markedRouterLeft)
        (bridgeRight width oldOutput) }
  let c10 : WorkConfiguration :=
    { state := 14
      tape := rightPathTape
        (List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
        (separatorSymbol :: leftBoundary :: oldOutput) }
  let c11 : WorkConfiguration :=
    { state := 15
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
        (leftBoundary :: oldOutput) }
  let c12 : WorkConfiguration :=
    { state := 16
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
        oldOutput }
  let c13 : WorkConfiguration :=
    { state := 16
      tape := rightPathTape
        (List.replicate (copied + 1) unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
        [] }
  let c14 : WorkConfiguration :=
    { state := 17
      tape := leftPathTape [unitSymbol]
        (List.replicate (copied + 1) unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft) }
  let c15 : WorkConfiguration :=
    { state := 17
      tape := leftPathTape
        (List.replicate (copied + 1) unitSymbol ++ [unitSymbol])
        (leftBoundary :: separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft) }
  let c16 : WorkConfiguration :=
    { state := 18
      tape := leftPathTape
        (leftBoundary ::
          List.replicate (copied + 1) unitSymbol ++ [unitSymbol])
        (separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft) }
  let c17 : WorkConfiguration :=
    { state := 19
      tape := leftPathTape
        (separatorSymbol :: leftBoundary ::
          List.replicate (copied + 1) unitSymbol ++ [unitSymbol])
        (List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft) }
  let c18 : WorkConfiguration :=
    { state := 19
      tape := leftPathTape
        (List.replicate width unitSymbol ++
          separatorSymbol :: leftBoundary ::
            List.replicate (copied + 1) unitSymbol ++ [unitSymbol])
        (endSymbol :: markedRouterLeft) }
  let c19 := copyLoopConfiguration processed (copied + 1) remainingTail
    width workspace
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    cases processed <;>
      simp [c0, c1, copyLoopConfiguration, greaterCopiedRouterLeft,
        bridgeRight, oldOutput, copiedTail, width, leftPathTape,
        List.replicate_succ] <;>
      rfl
  have h12 : workRunExact? machine processed c1 = some c2 := by
    exact scanLeft_replicate_exact 12 boundaryMark processed
      (endSymbol :: bridgeRight width oldOutput)
      (separatorSymbol :: copiedTail) (by intro left right; rfl)
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    cases copied <;>
      simp [c2, c3, copiedTail, leftPathTape,
        List.replicate_succ] <;>
      rfl
  have h34 : workRunExact? machine copied c3 = some c4 := by
    have hScan := scanLeft_replicate_exact 12 copiedRemainderMark copied
      (separatorSymbol ::
        List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
      afterCopiedTail (by intro left right; rfl)
    simpa [c3, c4, copiedTail, afterCopiedTail] using hScan
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    simp [c4, c5, afterCopiedTail, afterMarkedTail,
      List.replicate_succ]
    rfl
  have h56 : workRunExact? machine copied c5 = some c6 := by
    have hScan := scanRight_replicate_exact 13 copiedRemainderMark copied
      (copiedRemainderMark :: afterMarkedTail)
      (separatorSymbol ::
        List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
      (by intro left right; rfl)
    simpa [c5, c6] using hScan
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    cases processed <;>
      simp [c6, c7, rightPathTape, List.replicate_succ] <;>
      rfl
  have h78 : workRunExact? machine processed c7 = some c8 := by
    have hScan := scanRight_replicate_exact 13 boundaryMark processed
      (separatorSymbol ::
        List.replicate copied copiedRemainderMark ++
          copiedRemainderMark :: afterMarkedTail)
      (endSymbol :: bridgeRight width oldOutput)
      (by intro left right; rfl)
    simpa [c7, c8, markedRouterLeft] using hScan
  have h89 : workRunExact? machine 1 c8 = some c9 := by
    apply workRunExact_one
    rfl
  have h910 : workRunExact? machine width c9 = some c10 := by
    exact scanRight_replicate_exact 14 unitSymbol width
      (endSymbol :: markedRouterLeft)
      (separatorSymbol :: leftBoundary :: oldOutput)
      (by intro left right; rfl)
  have h1011 : workRunExact? machine 1 c10 = some c11 := by
    apply workRunExact_one
    rfl
  have h1112 : workRunExact? machine 1 c11 = some c12 := by
    apply workRunExact_one
    simp [c11, c12, oldOutput, List.replicate_succ]
    rfl
  have h1213 : workRunExact? machine (copied + 1) c12 = some c13 := by
    have hScan := scanRight_replicate_exact 16 unitSymbol (copied + 1)
      (leftBoundary :: separatorSymbol ::
        List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
      [] (by intro left right; rfl)
    simpa [c12, c13, oldOutput] using hScan
  have h1314 : workRunExact? machine 1 c13 = some c14 := by
    apply workRunExact_one
    rfl
  have h1415 : workRunExact? machine (copied + 1) c14 = some c15 := by
    have hScan := scanLeft_replicate_exact 17 unitSymbol (copied + 1)
      [unitSymbol]
      (leftBoundary :: separatorSymbol ::
        List.replicate width unitSymbol ++ endSymbol :: markedRouterLeft)
      (by intro left right; rfl)
    simpa [c14, c15] using hScan
  have h1516 : workRunExact? machine 1 c15 = some c16 := by
    apply workRunExact_one
    rfl
  have h1617 : workRunExact? machine 1 c16 = some c17 := by
    apply workRunExact_one
    simp [c16, c17, width, List.replicate_succ]
    rfl
  have h1718 : workRunExact? machine width c17 = some c18 := by
    have hScan := scanLeft_replicate_exact 19 unitSymbol width
      (separatorSymbol :: leftBoundary ::
        List.replicate (copied + 1) unitSymbol ++ [unitSymbol])
      (endSymbol :: markedRouterLeft) (by intro left right; rfl)
    simpa [c17, c18] using hScan
  have h1819 : workRunExact? machine 1 c18 = some c19 := by
    apply workRunExact_one
    simp [c18, c19, copyLoopConfiguration, bridgeRight,
      greaterCopiedRouterLeft, markedRouterLeft, afterMarkedTail, width,
      replicate_append_self_cons, List.replicate_succ]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 processed c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1) copied c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1) copied c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1) processed
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed) 1
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1) width
    c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width) 1
    c0 c10 c11 h010 h1011
  have h012 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1) 1
    c0 c11 c12 h011 h1112
  have h013 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1)
    (copied + 1) c0 c12 c13 h012 h1213
  have h014 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1)) 1 c0 c13 c14 h013 h1314
  have h015 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1) (copied + 1) c0 c14 c15 h014 h1415
  have h016 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1)) 1 c0 c15 c16 h015 h1516
  have h017 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1) 1 c0 c16 c17 h016 h1617
  have h018 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1 + 1) width
    c0 c17 c18 h017 h1718
  have h019 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1 + 1 + width) 1
    c0 c18 c19 h018 h1819
  have hCount :
      1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
          (copied + 1) + 1 + (copied + 1) + 1 + 1 + width + 1 =
        copyCycleSteps processed copied width := by
    unfold copyCycleSteps
    omega
  rw [← hCount]
  simpa [c0, c19] using h019

private theorem copy_finish_cycle_exact
    (processed copied widthTail : Nat) (workspace : List WorkSymbol) :
    workRunExact? machine
        (copyCycleSteps processed copied (widthTail + 1))
        (copyLoopConfiguration processed copied 0 (widthTail + 1) workspace) =
      some (widthLoopConfiguration
        (greaterCopiedRouterLeft processed copied 0 workspace)
        (copied + 1) 0 (widthTail + 1)) := by
  let width := widthTail + 1
  let oldOutput := List.replicate (copied + 1) unitSymbol
  let coordinateTail :=
    List.replicate (processed + 1) coordinateMark ++
      leftBoundary :: workspace
  let copiedTail :=
    List.replicate copied copiedRemainderMark ++ coordinateTail
  let routerLeft := greaterCopiedRouterLeft processed copied 0 workspace
  let c0 := copyLoopConfiguration processed copied 0 width workspace
  let c1 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape (endSymbol :: bridgeRight width oldOutput)
        (List.replicate processed boundaryMark ++
          separatorSymbol :: copiedTail) }
  let c2 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
        (separatorSymbol :: copiedTail) }
  let c3 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (separatorSymbol ::
          List.replicate processed boundaryMark ++
            endSymbol :: bridgeRight width oldOutput)
        copiedTail }
  let c4 : WorkConfiguration :=
    { state := 12
      tape := leftPathTape
        (List.replicate copied copiedRemainderMark ++
          separatorSymbol ::
            List.replicate processed boundaryMark ++
              endSymbol :: bridgeRight width oldOutput)
        coordinateTail }
  let c5 : WorkConfiguration :=
    { state := 20
      tape := rightPathTape
        (coordinateMark ::
          List.replicate processed coordinateMark ++
            leftBoundary :: workspace)
        (List.replicate copied copiedRemainderMark ++
          separatorSymbol ::
            List.replicate processed boundaryMark ++
              endSymbol :: bridgeRight width oldOutput) }
  let c6 : WorkConfiguration :=
    { state := 20
      tape := rightPathTape
        (List.replicate copied copiedRemainderMark ++
          coordinateMark ::
            List.replicate processed coordinateMark ++
              leftBoundary :: workspace)
        (separatorSymbol ::
          List.replicate processed boundaryMark ++
            endSymbol :: bridgeRight width oldOutput) }
  let c7 : WorkConfiguration :=
    { state := 20
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate copied copiedRemainderMark ++
            coordinateMark ::
              List.replicate processed coordinateMark ++
                leftBoundary :: workspace)
        (List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput) }
  let c8 : WorkConfiguration :=
    { state := 20
      tape := rightPathTape routerLeft
        (endSymbol :: bridgeRight width oldOutput) }
  let c9 : WorkConfiguration :=
    { state := 21
      tape := rightPathTape (endSymbol :: routerLeft)
        (bridgeRight width oldOutput) }
  let c10 : WorkConfiguration :=
    { state := 21
      tape := rightPathTape
        (List.replicate width unitSymbol ++ endSymbol :: routerLeft)
        (separatorSymbol :: leftBoundary :: oldOutput) }
  let c11 : WorkConfiguration :=
    { state := 22
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: routerLeft)
        (leftBoundary :: oldOutput) }
  let c12 : WorkConfiguration :=
    { state := 23
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: routerLeft)
        oldOutput }
  let c13 : WorkConfiguration :=
    { state := 23
      tape := rightPathTape
        (List.replicate (copied + 1) unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate width unitSymbol ++ endSymbol :: routerLeft)
        [] }
  let c14 : WorkConfiguration :=
    { state := 24
      tape := leftPathTape [separatorSymbol]
        (List.replicate (copied + 1) unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate width unitSymbol ++ endSymbol :: routerLeft) }
  let c15 : WorkConfiguration :=
    { state := 24
      tape := leftPathTape
        (List.replicate (copied + 1) unitSymbol ++ [separatorSymbol])
        (leftBoundary :: separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: routerLeft) }
  let c16 : WorkConfiguration :=
    { state := 25
      tape := leftPathTape
        (leftBoundary ::
          List.replicate (copied + 1) unitSymbol ++ [separatorSymbol])
        (separatorSymbol ::
          List.replicate width unitSymbol ++ endSymbol :: routerLeft) }
  let c17 : WorkConfiguration :=
    { state := 26
      tape := leftPathTape
        (separatorSymbol :: leftBoundary ::
          List.replicate (copied + 1) unitSymbol ++ [separatorSymbol])
        (List.replicate width unitSymbol ++ endSymbol :: routerLeft) }
  let c18 : WorkConfiguration :=
    { state := 26
      tape := leftPathTape
        (List.replicate width unitSymbol ++
          separatorSymbol :: leftBoundary ::
            List.replicate (copied + 1) unitSymbol ++ [separatorSymbol])
        (endSymbol :: routerLeft) }
  let c19 := widthLoopConfiguration routerLeft (copied + 1) 0 width
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    cases processed <;>
      simp [c0, c1, copyLoopConfiguration, greaterCopiedRouterLeft,
        bridgeRight, oldOutput, copiedTail, coordinateTail, width,
        leftPathTape, List.replicate_succ] <;>
      rfl
  have h12 : workRunExact? machine processed c1 = some c2 := by
    exact scanLeft_replicate_exact 12 boundaryMark processed
      (endSymbol :: bridgeRight width oldOutput)
      (separatorSymbol :: copiedTail) (by intro left right; rfl)
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    cases copied <;>
      simp [c2, c3, copiedTail, coordinateTail, leftPathTape,
        List.replicate_succ] <;>
      rfl
  have h34 : workRunExact? machine copied c3 = some c4 := by
    have hScan := scanLeft_replicate_exact 12 copiedRemainderMark copied
      (separatorSymbol ::
        List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
      coordinateTail (by intro left right; rfl)
    simpa [c3, c4, copiedTail] using hScan
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    simp [c4, c5, coordinateTail, List.replicate_succ]
    rfl
  have h56 : workRunExact? machine copied c5 = some c6 := by
    have hScan := scanRight_replicate_exact 20 copiedRemainderMark copied
      (coordinateMark ::
        List.replicate processed coordinateMark ++ leftBoundary :: workspace)
      (separatorSymbol ::
        List.replicate processed boundaryMark ++
          endSymbol :: bridgeRight width oldOutput)
      (by intro left right; rfl)
    simpa [c5, c6] using hScan
  have h67 : workRunExact? machine 1 c6 = some c7 := by
    apply workRunExact_one
    cases processed <;>
      simp [c6, c7, rightPathTape, List.replicate_succ] <;>
      rfl
  have h78 : workRunExact? machine processed c7 = some c8 := by
    have hScan := scanRight_replicate_exact 20 boundaryMark processed
      (separatorSymbol ::
        List.replicate copied copiedRemainderMark ++
          coordinateMark ::
            List.replicate processed coordinateMark ++
              leftBoundary :: workspace)
      (endSymbol :: bridgeRight width oldOutput)
      (by intro left right; rfl)
    simpa [c7, c8, routerLeft, greaterCopiedRouterLeft,
      replicate_append_self_cons, List.replicate_succ] using hScan
  have h89 : workRunExact? machine 1 c8 = some c9 := by
    apply workRunExact_one
    rfl
  have h910 : workRunExact? machine width c9 = some c10 := by
    exact scanRight_replicate_exact 21 unitSymbol width
      (endSymbol :: routerLeft)
      (separatorSymbol :: leftBoundary :: oldOutput)
      (by intro left right; rfl)
  have h1011 : workRunExact? machine 1 c10 = some c11 := by
    apply workRunExact_one
    rfl
  have h1112 : workRunExact? machine 1 c11 = some c12 := by
    apply workRunExact_one
    simp [c11, c12, oldOutput, List.replicate_succ]
    rfl
  have h1213 : workRunExact? machine (copied + 1) c12 = some c13 := by
    have hScan := scanRight_replicate_exact 23 unitSymbol (copied + 1)
      (leftBoundary :: separatorSymbol ::
        List.replicate width unitSymbol ++ endSymbol :: routerLeft)
      [] (by intro left right; rfl)
    simpa [c12, c13, oldOutput] using hScan
  have h1314 : workRunExact? machine 1 c13 = some c14 := by
    apply workRunExact_one
    rfl
  have h1415 : workRunExact? machine (copied + 1) c14 = some c15 := by
    have hScan := scanLeft_replicate_exact 24 unitSymbol (copied + 1)
      [separatorSymbol]
      (leftBoundary :: separatorSymbol ::
        List.replicate width unitSymbol ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c14, c15] using hScan
  have h1516 : workRunExact? machine 1 c15 = some c16 := by
    apply workRunExact_one
    rfl
  have h1617 : workRunExact? machine 1 c16 = some c17 := by
    apply workRunExact_one
    simp [c16, c17, width, List.replicate_succ]
    rfl
  have h1718 : workRunExact? machine width c17 = some c18 := by
    have hScan := scanLeft_replicate_exact 26 unitSymbol width
      (separatorSymbol :: leftBoundary ::
        List.replicate (copied + 1) unitSymbol ++ [separatorSymbol])
      (endSymbol :: routerLeft) (by intro left right; rfl)
    simpa [c17, c18] using hScan
  have h1819 : workRunExact? machine 1 c18 = some c19 := by
    apply workRunExact_one
    simp [c18, c19, widthLoopConfiguration, width,
      List.replicate_succ]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 processed c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1) copied c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1) copied c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied) 1 c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1) processed
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed) 1
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1) width
    c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width) 1
    c0 c10 c11 h010 h1011
  have h012 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1) 1
    c0 c11 c12 h011 h1112
  have h013 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1)
    (copied + 1) c0 c12 c13 h012 h1213
  have h014 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1)) 1 c0 c13 c14 h013 h1314
  have h015 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1) (copied + 1) c0 c14 c15 h014 h1415
  have h016 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1)) 1 c0 c15 c16 h015 h1516
  have h017 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1) 1 c0 c16 c17 h016 h1617
  have h018 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1 + 1) width
    c0 c17 c18 h017 h1718
  have h019 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
      (copied + 1) + 1 + (copied + 1) + 1 + 1 + width) 1
    c0 c18 c19 h018 h1819
  have hCount :
      1 + processed + 1 + copied + 1 + copied + 1 + processed + 1 + width + 1 + 1 +
          (copied + 1) + 1 + (copied + 1) + 1 + 1 + width + 1 =
        copyCycleSteps processed copied width := by
    unfold copyCycleSteps
    omega
  rw [← hCount]
  simpa [c0, c19] using h019

private theorem copy_all_exact
    (processed copied widthTail : Nat) (workspace : List WorkSymbol) :
    ∀ remaining,
      workRunExact? machine
          (copyAllSteps processed copied (widthTail + 1) remaining)
          (copyLoopConfiguration processed copied remaining
            (widthTail + 1) workspace) =
        some (widthLoopConfiguration
          (greaterCopiedRouterLeft processed (copied + remaining) 0 workspace)
          (copied + remaining + 1) 0 (widthTail + 1)) := by
  intro remaining
  induction remaining generalizing copied with
  | zero =>
      simpa [copyAllSteps] using
        copy_finish_cycle_exact processed copied widthTail workspace
  | succ remaining ih =>
      have hCycle := copy_unit_cycle_exact processed copied remaining
        widthTail workspace
      have hTail := ih (copied + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (copyCycleSteps processed copied (widthTail + 1))
        (copyAllSteps processed (copied + 1) (widthTail + 1) remaining)
        (copyLoopConfiguration processed copied (remaining + 1)
          (widthTail + 1) workspace)
        (copyLoopConfiguration processed (copied + 1) remaining
          (widthTail + 1) workspace)
        (widthLoopConfiguration
          (greaterCopiedRouterLeft processed ((copied + 1) + remaining) 0
            workspace)
          ((copied + 1) + remaining + 1) 0 (widthTail + 1))
        hCycle hTail
      simpa [copyAllSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hAll

private theorem width_unit_cycle_exact
    (routerLeft : List WorkSymbol)
    (remainder copied remainingTail : Nat) :
    workRunExact? machine
        (widthCycleSteps remainder copied (remainingTail + 1))
        (widthLoopConfiguration routerLeft remainder copied
          (remainingTail + 1)) =
      some (widthLoopConfiguration routerLeft remainder (copied + 1)
        remainingTail) := by
  let output :=
    List.replicate remainder unitSymbol ++
      separatorSymbol :: List.replicate copied unitSymbol
  let c0 := widthLoopConfiguration routerLeft remainder copied
    (remainingTail + 1)
  let c1 : WorkConfiguration :=
    { state := 28
      tape := rightPathTape (endSymbol :: routerLeft)
        (List.replicate copied copiedWidthMark ++
          List.replicate (remainingTail + 1) unitSymbol ++
            separatorSymbol :: leftBoundary :: output) }
  let c2 : WorkConfiguration :=
    { state := 28
      tape := rightPathTape
        (List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (List.replicate (remainingTail + 1) unitSymbol ++
          separatorSymbol :: leftBoundary :: output) }
  let c3 : WorkConfiguration :=
    { state := 29
      tape := rightPathTape
        (copiedWidthMark ::
          List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (List.replicate remainingTail unitSymbol ++
          separatorSymbol :: leftBoundary :: output) }
  let c4 : WorkConfiguration :=
    { state := 29
      tape := rightPathTape
        (List.replicate remainingTail unitSymbol ++
          copiedWidthMark ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (separatorSymbol :: leftBoundary :: output) }
  let c5 : WorkConfiguration :=
    { state := 30
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate remainingTail unitSymbol ++
            copiedWidthMark ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (leftBoundary :: output) }
  let c6 : WorkConfiguration :=
    { state := 31
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate remainingTail unitSymbol ++
            copiedWidthMark ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        output }
  let c7 : WorkConfiguration :=
    { state := 31
      tape := rightPathTape
        (List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate remainingTail unitSymbol ++
              copiedWidthMark ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (separatorSymbol :: List.replicate copied unitSymbol) }
  let c8 : WorkConfiguration :=
    { state := 31
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate remainder unitSymbol ++
            leftBoundary :: separatorSymbol ::
              List.replicate remainingTail unitSymbol ++
                copiedWidthMark ::
                  List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (List.replicate copied unitSymbol) }
  let c9 : WorkConfiguration :=
    { state := 31
      tape := rightPathTape
        (List.replicate copied unitSymbol ++
          separatorSymbol ::
            List.replicate remainder unitSymbol ++
              leftBoundary :: separatorSymbol ::
                List.replicate remainingTail unitSymbol ++
                  copiedWidthMark ::
                    List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        [] }
  let c10 : WorkConfiguration :=
    { state := 32
      tape := leftPathTape [unitSymbol]
        (List.replicate copied unitSymbol ++
          separatorSymbol ::
            List.replicate remainder unitSymbol ++
              leftBoundary :: separatorSymbol ::
                List.replicate remainingTail unitSymbol ++
                  copiedWidthMark ::
                    List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c11 : WorkConfiguration :=
    { state := 32
      tape := leftPathTape
        (List.replicate copied unitSymbol ++ [unitSymbol])
        (separatorSymbol ::
          List.replicate remainder unitSymbol ++
            leftBoundary :: separatorSymbol ::
              List.replicate remainingTail unitSymbol ++
                copiedWidthMark ::
                  List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c12 : WorkConfiguration :=
    { state := 32
      tape := leftPathTape
        (separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
        (List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate remainingTail unitSymbol ++
              copiedWidthMark ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c13 : WorkConfiguration :=
    { state := 32
      tape := leftPathTape
        (List.replicate remainder unitSymbol ++
          separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
        (leftBoundary :: separatorSymbol ::
          List.replicate remainingTail unitSymbol ++
            copiedWidthMark ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c14 : WorkConfiguration :=
    { state := 33
      tape := leftPathTape
        (leftBoundary ::
          List.replicate remainder unitSymbol ++
            separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
        (separatorSymbol ::
          List.replicate remainingTail unitSymbol ++
            copiedWidthMark ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c15 : WorkConfiguration :=
    { state := 34
      tape := leftPathTape
        (separatorSymbol :: leftBoundary ::
          List.replicate remainder unitSymbol ++
            separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
        (List.replicate remainingTail unitSymbol ++
          copiedWidthMark ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c16 : WorkConfiguration :=
    { state := 34
      tape := leftPathTape
        (List.replicate remainingTail unitSymbol ++
          separatorSymbol :: leftBoundary ::
            List.replicate remainder unitSymbol ++
              separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
        (copiedWidthMark ::
          List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c17 : WorkConfiguration :=
    { state := 34
      tape := leftPathTape
        (List.replicate (copied + 1) copiedWidthMark ++
          List.replicate remainingTail unitSymbol ++
            separatorSymbol :: leftBoundary ::
              List.replicate remainder unitSymbol ++
                separatorSymbol ::
                  List.replicate copied unitSymbol ++ [unitSymbol])
        (endSymbol :: routerLeft) }
  let c18 := widthLoopConfiguration routerLeft remainder (copied + 1)
    remainingTail
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    cases copied <;>
      simp [c0, c1, widthLoopConfiguration, output, rightPathTape,
        List.replicate_succ] <;>
      rfl
  have h12 : workRunExact? machine copied c1 = some c2 := by
    have hScan := scanRight_replicate_exact 28 copiedWidthMark copied
      (endSymbol :: routerLeft)
      (List.replicate (remainingTail + 1) unitSymbol ++
        separatorSymbol :: leftBoundary :: output)
      (by intro left right; rfl)
    simpa [c1, c2] using hScan
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    simp [c2, c3, List.replicate_succ]
    rfl
  have h34 : workRunExact? machine remainingTail c3 = some c4 := by
    have hScan := scanRight_replicate_exact 29 unitSymbol remainingTail
      (copiedWidthMark ::
        List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (separatorSymbol :: leftBoundary :: output)
      (by intro left right; rfl)
    simpa [c3, c4] using hScan
  have h45 : workRunExact? machine 1 c4 = some c5 := by
    apply workRunExact_one
    rfl
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    cases remainder <;>
      simp [c5, c6, output, rightPathTape, List.replicate_succ] <;>
      rfl
  have h67 : workRunExact? machine remainder c6 = some c7 := by
    have hScan := scanRight_replicate_exact 31 unitSymbol remainder
      (leftBoundary :: separatorSymbol ::
        List.replicate remainingTail unitSymbol ++
          copiedWidthMark ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (separatorSymbol :: List.replicate copied unitSymbol)
      (by intro left right; rfl)
    simpa [c6, c7, output] using hScan
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    cases copied <;>
      simp [c7, c8, rightPathTape, List.replicate_succ] <;>
      rfl
  have h89 : workRunExact? machine copied c8 = some c9 := by
    have hScan := scanRight_replicate_exact 31 unitSymbol copied
      (separatorSymbol ::
        List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate remainingTail unitSymbol ++
              copiedWidthMark ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      [] (by intro left right; rfl)
    simpa [c8, c9] using hScan
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    cases copied <;>
      simp [c9, c10, leftPathTape, List.replicate_succ] <;>
      rfl
  have h1011 : workRunExact? machine copied c10 = some c11 := by
    have hScan := scanLeft_replicate_exact 32 unitSymbol copied
      [unitSymbol]
      (separatorSymbol ::
        List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate remainingTail unitSymbol ++
              copiedWidthMark ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c10, c11] using hScan
  have h1112 : workRunExact? machine 1 c11 = some c12 := by
    apply workRunExact_one
    cases remainder <;>
      simp [c11, c12, leftPathTape, List.replicate_succ] <;>
      rfl
  have h1213 : workRunExact? machine remainder c12 = some c13 := by
    have hScan := scanLeft_replicate_exact 32 unitSymbol remainder
      (separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
      (leftBoundary :: separatorSymbol ::
        List.replicate remainingTail unitSymbol ++
          copiedWidthMark ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c12, c13] using hScan
  have h1314 : workRunExact? machine 1 c13 = some c14 := by
    apply workRunExact_one
    rfl
  have h1415 : workRunExact? machine 1 c14 = some c15 := by
    apply workRunExact_one
    cases remainingTail <;>
      simp [c14, c15, leftPathTape, List.replicate_succ] <;>
      rfl
  have h1516 : workRunExact? machine remainingTail c15 = some c16 := by
    have hScan := scanLeft_replicate_exact 34 unitSymbol remainingTail
      (separatorSymbol :: leftBoundary ::
        List.replicate remainder unitSymbol ++
          separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
      (copiedWidthMark ::
        List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c15, c16] using hScan
  have h1617 : workRunExact? machine (copied + 1) c16 = some c17 := by
    have hScan := scanLeft_replicate_exact 34 copiedWidthMark (copied + 1)
      (List.replicate remainingTail unitSymbol ++
        separatorSymbol :: leftBoundary ::
          List.replicate remainder unitSymbol ++
            separatorSymbol :: List.replicate copied unitSymbol ++ [unitSymbol])
      (endSymbol :: routerLeft) (by intro left right; rfl)
    simpa [c16, c17, replicate_append_self_cons,
      List.replicate_succ] using hScan
  have h1718 : workRunExact? machine 1 c17 = some c18 := by
    apply workRunExact_one
    simp [c17, c18, widthLoopConfiguration, replicate_append_self_cons,
      List.replicate_succ]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 copied c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1) remainingTail c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail) 1 c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1) 1 c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1) remainder
    c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder) 1
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1) copied
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied) 1
    c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1)
    copied c0 c10 c11 h010 h1011
  have h012 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied)
    1 c0 c11 c12 h011 h1112
  have h013 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1)
    remainder c0 c12 c13 h012 h1213
  have h014 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
      remainder) 1 c0 c13 c14 h013 h1314
  have h015 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
      remainder + 1) 1 c0 c14 c15 h014 h1415
  have h016 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
      remainder + 1 + 1) remainingTail c0 c15 c16 h015 h1516
  have h017 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
      remainder + 1 + 1 + remainingTail) (copied + 1)
    c0 c16 c17 h016 h1617
  have h018 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
      remainder + 1 + 1 + remainingTail + (copied + 1)) 1
    c0 c17 c18 h017 h1718
  have hCount :
      1 + copied + 1 + remainingTail + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
          remainder + 1 + 1 + remainingTail + (copied + 1) + 1 =
        widthCycleSteps remainder copied (remainingTail + 1) := by
    unfold widthCycleSteps
    omega
  rw [← hCount]
  simpa [c0, c18] using h018

private theorem width_finish_exact (routerLeft : List WorkSymbol)
    (remainder copied : Nat) :
    workRunExact? machine (widthFinishSteps remainder copied)
        (widthLoopConfiguration routerLeft remainder copied 0) =
      some (bridgeFinalConfiguration routerLeft remainder copied) := by
  let output :=
    List.replicate remainder unitSymbol ++
      separatorSymbol :: List.replicate copied unitSymbol
  let c0 := widthLoopConfiguration routerLeft remainder copied 0
  let c1 : WorkConfiguration :=
    { state := 28
      tape := rightPathTape (endSymbol :: routerLeft)
        (List.replicate copied copiedWidthMark ++
          separatorSymbol :: leftBoundary :: output) }
  let c2 : WorkConfiguration :=
    { state := 28
      tape := rightPathTape
        (List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (separatorSymbol :: leftBoundary :: output) }
  let c3 : WorkConfiguration :=
    { state := 35
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (leftBoundary :: output) }
  let c4 : WorkConfiguration :=
    { state := 36
      tape := rightPathTape
        (leftBoundary :: separatorSymbol ::
          List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        output }
  let c5 : WorkConfiguration :=
    { state := 36
      tape := rightPathTape
        (List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (separatorSymbol :: List.replicate copied unitSymbol) }
  let c6 : WorkConfiguration :=
    { state := 36
      tape := rightPathTape
        (separatorSymbol ::
          List.replicate remainder unitSymbol ++
            leftBoundary :: separatorSymbol ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        (List.replicate copied unitSymbol) }
  let c7 : WorkConfiguration :=
    { state := 36
      tape := rightPathTape
        (List.replicate copied unitSymbol ++
          separatorSymbol ::
            List.replicate remainder unitSymbol ++
              leftBoundary :: separatorSymbol ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
        [] }
  let c8 : WorkConfiguration :=
    { state := 37
      tape := leftPathTape [endSymbol]
        (List.replicate copied unitSymbol ++
          separatorSymbol ::
            List.replicate remainder unitSymbol ++
              leftBoundary :: separatorSymbol ::
                List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c9 : WorkConfiguration :=
    { state := 37
      tape := leftPathTape
        (List.replicate copied unitSymbol ++ [endSymbol])
        (separatorSymbol ::
          List.replicate remainder unitSymbol ++
            leftBoundary :: separatorSymbol ::
              List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c10 : WorkConfiguration :=
    { state := 37
      tape := leftPathTape
        (separatorSymbol :: List.replicate copied unitSymbol ++ [endSymbol])
        (List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c11 : WorkConfiguration :=
    { state := 37
      tape := leftPathTape
        (List.replicate remainder unitSymbol ++
          separatorSymbol :: List.replicate copied unitSymbol ++ [endSymbol])
        (leftBoundary :: separatorSymbol ::
          List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft) }
  let c12 := bridgeFinalConfiguration routerLeft remainder copied
  have h01 : workRunExact? machine 1 c0 = some c1 := by
    apply workRunExact_one
    cases copied <;>
      simp [c0, c1, widthLoopConfiguration, output, rightPathTape,
        List.replicate_succ] <;>
      rfl
  have h12 : workRunExact? machine copied c1 = some c2 := by
    have hScan := scanRight_replicate_exact 28 copiedWidthMark copied
      (endSymbol :: routerLeft)
      (separatorSymbol :: leftBoundary :: output)
      (by intro left right; rfl)
    simpa [c1, c2] using hScan
  have h23 : workRunExact? machine 1 c2 = some c3 := by
    apply workRunExact_one
    rfl
  have h34 : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    cases remainder <;>
      simp [c3, c4, output, rightPathTape, List.replicate_succ] <;>
      rfl
  have h45 : workRunExact? machine remainder c4 = some c5 := by
    have hScan := scanRight_replicate_exact 36 unitSymbol remainder
      (leftBoundary :: separatorSymbol ::
        List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (separatorSymbol :: List.replicate copied unitSymbol)
      (by intro left right; rfl)
    simpa [c4, c5, output] using hScan
  have h56 : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    cases copied <;>
      simp [c5, c6, rightPathTape, List.replicate_succ] <;>
      rfl
  have h67 : workRunExact? machine copied c6 = some c7 := by
    have hScan := scanRight_replicate_exact 36 unitSymbol copied
      (separatorSymbol ::
        List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      [] (by intro left right; rfl)
    simpa [c6, c7] using hScan
  have h78 : workRunExact? machine 1 c7 = some c8 := by
    apply workRunExact_one
    cases copied <;>
      simp [c7, c8, leftPathTape, List.replicate_succ] <;>
      rfl
  have h89 : workRunExact? machine copied c8 = some c9 := by
    have hScan := scanLeft_replicate_exact 37 unitSymbol copied
      [endSymbol]
      (separatorSymbol ::
        List.replicate remainder unitSymbol ++
          leftBoundary :: separatorSymbol ::
            List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c8, c9] using hScan
  have h910 : workRunExact? machine 1 c9 = some c10 := by
    apply workRunExact_one
    cases remainder <;>
      simp [c9, c10, leftPathTape, List.replicate_succ] <;>
      rfl
  have h1011 : workRunExact? machine remainder c10 = some c11 := by
    have hScan := scanLeft_replicate_exact 37 unitSymbol remainder
      (separatorSymbol :: List.replicate copied unitSymbol ++ [endSymbol])
      (leftBoundary :: separatorSymbol ::
        List.replicate copied copiedWidthMark ++ endSymbol :: routerLeft)
      (by intro left right; rfl)
    simpa [c10, c11] using hScan
  have h1112 : workRunExact? machine 1 c11 = some c12 := by
    apply workRunExact_one
    simp [c11, c12, bridgeFinalConfiguration, shieldedDividerInputTape,
      dividerWord, rightPathTape]
    rfl
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine
    1 copied c0 c1 c2 h01 h12
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied) 1 c0 c2 c3 h02 h23
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1) 1 c0 c3 c4 h03 h34
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1) remainder c0 c4 c5 h04 h45
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder) 1 c0 c5 c6 h05 h56
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1) copied c0 c6 c7 h06 h67
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1 + copied) 1
    c0 c7 c8 h07 h78
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1 + copied + 1) copied
    c0 c8 c9 h08 h89
  have h010 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1 + copied + 1 + copied) 1
    c0 c9 c10 h09 h910
  have h011 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1 + copied + 1 + copied + 1)
    remainder c0 c10 c11 h010 h1011
  have h012 := PipelineMachineSimulation.workRunExact?_compose machine
    (1 + copied + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 + remainder)
    1 c0 c11 c12 h011 h1112
  have hCount :
      1 + copied + 1 + 1 + remainder + 1 + copied + 1 + copied + 1 +
          remainder + 1 =
        widthFinishSteps remainder copied := by
    unfold widthFinishSteps
    omega
  rw [← hCount]
  simpa [c0, c12] using h012

private theorem width_all_exact (routerLeft : List WorkSymbol)
    (remainder copied : Nat) :
    ∀ remaining,
      workRunExact? machine (widthAllSteps remainder copied remaining)
          (widthLoopConfiguration routerLeft remainder copied remaining) =
        some (bridgeFinalConfiguration routerLeft remainder
          (copied + remaining)) := by
  intro remaining
  induction remaining generalizing copied with
  | zero =>
      simpa [widthAllSteps] using
        width_finish_exact routerLeft remainder copied
  | succ remaining ih =>
      have hCycle := width_unit_cycle_exact routerLeft remainder copied remaining
      have hTail := ih (copied + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (widthCycleSteps remainder copied (remaining + 1))
        (widthAllSteps remainder (copied + 1) remaining)
        (widthLoopConfiguration routerLeft remainder copied (remaining + 1))
        (widthLoopConfiguration routerLeft remainder (copied + 1) remaining)
        (bridgeFinalConfiguration routerLeft remainder
          ((copied + 1) + remaining))
        hCycle hTail
      simpa [widthAllSteps, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hAll

def equalFinalConfiguration (processed width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := shieldedDividerInputTape 0 width
      (equalExterior processed width workspace) }

def greaterFinalConfiguration (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState
    tape := shieldedDividerInputTape (remainingCoordinate + 1) width
      (greaterExterior processed remainingCoordinate width workspace) }

theorem equalInputTape_is_exact_router_result (processed width : Nat)
    (workspace : List WorkSymbol) :
    equalInputTape processed width workspace =
      extendRouterResultTape
        (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
          (.equal processed)).tape width workspace := by
  rfl

theorem greaterInputTape_is_exact_router_result
    (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) :
    greaterInputTape processed remainingCoordinate width workspace =
      extendRouterResultTape
        (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
          (.greater processed remainingCoordinate)).tape width workspace := by
  rfl

/-- The equality branch derives the zero shifted remainder and constructs the
shielded divider input in one exact raw trace for every positive width. -/
theorem equal_workRunExact (processed width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    workRunExact? machine (equalWorkSteps width)
        (equalInputConfiguration processed width workspace) =
      some (equalFinalConfiguration processed width workspace) := by
  cases width with
  | zero => omega
  | succ widthTail =>
      have hPrefix := equal_prefix_exact processed widthTail workspace
      have hWidthRun := width_all_exact
        (equalRouterLeft processed workspace) 0 0 (widthTail + 1)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (prefixWorkSteps (widthTail + 1))
        (widthAllSteps 0 0 (widthTail + 1))
        (equalInputConfiguration processed (widthTail + 1) workspace)
        (widthLoopConfiguration (equalRouterLeft processed workspace)
          0 0 (widthTail + 1))
        (bridgeFinalConfiguration (equalRouterLeft processed workspace)
          0 (widthTail + 1))
        hPrefix (by simpa using hWidthRun)
      simpa [equalWorkSteps, equalFinalConfiguration,
        bridgeFinalConfiguration, equalExterior, equalRouterLeft]
        using hAll

/-- The strict branch derives and copies exactly the positive shifted
remainder exposed by M209 before constructing the shielded divider input. -/
theorem greater_workRunExact (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    workRunExact? machine
        (greaterWorkSteps processed remainingCoordinate width)
        (greaterInputConfiguration processed remainingCoordinate width
          workspace) =
      some (greaterFinalConfiguration processed remainingCoordinate width
        workspace) := by
  cases width with
  | zero => omega
  | succ widthTail =>
      have hPrefix := greater_prefix_exact processed remainingCoordinate
        widthTail workspace
      have hCopy := copy_all_exact processed 0 widthTail workspace
        remainingCoordinate
      have hWidthRun := width_all_exact
        (greaterCopiedRouterLeft processed remainingCoordinate 0 workspace)
        (remainingCoordinate + 1) 0 (widthTail + 1)
      have hPrefixCopy :=
        PipelineMachineSimulation.workRunExact?_compose machine
          (prefixWorkSteps (widthTail + 1))
          (copyAllSteps processed 0 (widthTail + 1) remainingCoordinate)
          (greaterInputConfiguration processed remainingCoordinate
            (widthTail + 1) workspace)
          (copyLoopConfiguration processed 0 remainingCoordinate
            (widthTail + 1) workspace)
          (widthLoopConfiguration
            (greaterCopiedRouterLeft processed remainingCoordinate 0 workspace)
            (remainingCoordinate + 1) 0 (widthTail + 1))
          hPrefix (by simpa using hCopy)
      have hAll := PipelineMachineSimulation.workRunExact?_compose machine
        (prefixWorkSteps (widthTail + 1) +
          copyAllSteps processed 0 (widthTail + 1) remainingCoordinate)
        (widthAllSteps (remainingCoordinate + 1) 0 (widthTail + 1))
        (greaterInputConfiguration processed remainingCoordinate
          (widthTail + 1) workspace)
        (widthLoopConfiguration
          (greaterCopiedRouterLeft processed remainingCoordinate 0 workspace)
          (remainingCoordinate + 1) 0 (widthTail + 1))
        (bridgeFinalConfiguration
          (greaterCopiedRouterLeft processed remainingCoordinate 0 workspace)
          (remainingCoordinate + 1) (widthTail + 1))
        hPrefixCopy (by simpa using hWidthRun)
      simpa [greaterWorkSteps, greaterFinalConfiguration,
        bridgeFinalConfiguration, greaterExterior,
        greaterCopiedRouterLeft] using hAll

/-- A missing unary width is fail-closed before any divider input is claimed. -/
theorem equal_zero_width_dead_state (processed : Nat)
    (workspace : List WorkSymbol) :
    (workRun machine 2
      (equalInputConfiguration processed 0 workspace)).state = 38 := by
  rfl

theorem greater_zero_width_dead_state
    (processed remainingCoordinate : Nat)
    (workspace : List WorkSymbol) :
    (workRun machine 2
      (greaterInputConfiguration processed remainingCoordinate 0
        workspace)).state = 38 := by
  rfl

theorem equalFinalConfiguration_isHalted (processed width : Nat)
    (workspace : List WorkSymbol) :
    machine.isHalted (equalFinalConfiguration processed width workspace) =
      true := by
  rfl

theorem greaterFinalConfiguration_isHalted
    (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) :
    machine.isHalted
        (greaterFinalConfiguration processed remainingCoordinate width
          workspace) = true := by
  rfl

/-- Every certified bridge work transition expands to exactly six concrete
three-symbol transitions. -/
theorem run_compile_equal_exact (processed width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    run (compileWorkMachine machine) (6 * equalWorkSteps width)
        (encodeWorkConfiguration
          (equalInputConfiguration processed width workspace)) =
      encodeWorkConfiguration
        (equalFinalConfiguration processed width workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (equalWorkSteps width)
    (equalInputConfiguration processed width workspace)
    (equalFinalConfiguration processed width workspace)
    (equal_workRunExact processed width workspace hWidth)

theorem run_compile_greater_exact
    (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    run (compileWorkMachine machine)
        (6 * greaterWorkSteps processed remainingCoordinate width)
        (encodeWorkConfiguration
          (greaterInputConfiguration processed remainingCoordinate width
            workspace)) =
      encodeWorkConfiguration
        (greaterFinalConfiguration processed remainingCoordinate width
          workspace) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (greaterWorkSteps processed remainingCoordinate width)
    (greaterInputConfiguration processed remainingCoordinate width workspace)
    (greaterFinalConfiguration processed remainingCoordinate width workspace)
    (greater_workRunExact processed remainingCoordinate width workspace hWidth)

/-! ## Shielded M211 transport -/

abbrev dividerMachine : WorkMachine := BuilderPostHeaderRawDivider.machine

def appendExteriorTape (tape : WorkTape)
    (exterior : List WorkSymbol) : WorkTape :=
  { left := tape.left ++ exterior
    head := tape.head
    right := tape.right }

def appendExteriorConfiguration (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := configuration.state
    tape := appendExteriorTape configuration.tape exterior }

/-- The canonical divider head has not crossed its left-boundary cell. -/
private def DividerBoundaryProtected (tape : WorkTape) : Prop :=
  (∃ leftPrefix, tape.left = leftPrefix ++ [leftBoundary]) ∨
    (tape.left = [] ∧ tape.head = leftBoundary)

private def dividerBoundaryRuleSafe (rule : WorkRule) : Bool :=
  if rule.readSymbol == leftBoundary then
    (rule.writeSymbol == leftBoundary) && !(rule.move == .left)
  else
    true

private theorem divider_rules_boundary_safe :
    BuilderPostHeaderRawDivider.rules.all dividerBoundaryRuleSafe = true := by
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

private theorem divider_rule_safe_at_boundary (rule : WorkRule)
    (hRule : rule ∈ BuilderPostHeaderRawDivider.rules)
    (hRead : rule.readSymbol = leftBoundary) :
    rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left := by
  have hSafe := (List.all_eq_true.mp divider_rules_boundary_safe) rule hRule
  simp [dividerBoundaryRuleSafe, hRead] at hSafe
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

private theorem dividerBoundaryProtected_head_of_left_nil
    (tape : WorkTape) (hProtected : DividerBoundaryProtected tape)
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

private theorem dividerBoundaryProtected_apply
    (configuration : WorkConfiguration) (rule : WorkRule)
    (hProtected : DividerBoundaryProtected configuration.tape)
    (hBoundary : configuration.tape.head = leftBoundary →
      rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left) :
    DividerBoundaryProtected (applyWorkRule rule configuration).tape := by
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

private theorem divider_step_transport
    (configuration next : WorkConfiguration)
    (exterior : List WorkSymbol)
    (hProtected : DividerBoundaryProtected configuration.tape)
    (hStep : workStep? dividerMachine configuration = some next) :
    DividerBoundaryProtected next.tape ∧
      workStep? dividerMachine
          (appendExteriorConfiguration configuration exterior) =
        some (appendExteriorConfiguration next exterior) := by
  rcases workStep?_some_exists dividerMachine configuration next hStep with
    ⟨rule, hHalted, hFind, hNext⟩
  have hRule := findWorkRule_some_mem hFind
  have hMatches := findWorkRule_some_matches hFind
  have hBoundary : configuration.tape.head = leftBoundary →
      rule.writeSymbol = leftBoundary ∧ rule.move ≠ .left := by
    intro hHead
    exact divider_rule_safe_at_boundary rule hRule (hMatches.2.trans hHead)
  have hNextProtected : DividerBoundaryProtected next.tape := by
    rw [hNext]
    exact dividerBoundaryProtected_apply configuration rule hProtected hBoundary
  have hLeftNonempty : rule.move = .left → configuration.tape.left ≠ [] := by
    intro hMove hLeft
    have hHead := dividerBoundaryProtected_head_of_left_nil
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
      dividerMachine.isHalted
          (appendExteriorConfiguration configuration exterior) = false := by
    simpa [WorkMachine.isHalted, appendExteriorConfiguration,
      appendExteriorTape] using hHalted
  have hFindExterior :
      findWorkRule dividerMachine.rules
          (appendExteriorConfiguration configuration exterior).state
          (appendExteriorConfiguration configuration exterior).tape.head =
        some rule := by
    simpa [appendExteriorConfiguration, appendExteriorTape] using hFind
  have hExteriorStep := workStep?_eq_apply_of_find dividerMachine
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

private theorem divider_workRunExact_transport :
    ∀ (steps : Nat) (initial final : WorkConfiguration)
      (exterior : List WorkSymbol),
      DividerBoundaryProtected initial.tape →
      workRunExact? dividerMachine steps initial = some final →
      workRunExact? dividerMachine steps
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
      cases hStep : workStep? dividerMachine initial with
      | none =>
          change
            (match workStep? dividerMachine initial with
             | none => none
             | some next => workRunExact? dividerMachine steps next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? dividerMachine steps next =
              some final := by
            change
              (match workStep? dividerMachine initial with
               | none => none
               | some result => workRunExact? dividerMachine steps result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          have hTransport := divider_step_transport initial next exterior
            hProtected hStep
          change
            (match workStep? dividerMachine
                (appendExteriorConfiguration initial exterior) with
             | none => none
             | some result => workRunExact? dividerMachine steps result) =
              some (appendExteriorConfiguration final exterior)
          rw [hTransport.2]
          exact ih next final exterior hTransport.1 hTail

def shieldedDividerStartConfiguration (dividend width : Nat)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := dividerMachine.startState
    tape := shieldedDividerInputTape dividend width exterior }

def shieldedDividerFinalConfiguration (dividend width : Nat)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  appendExteriorConfiguration
    (BuilderPostHeaderRawDivider.finalConfiguration dividend width) exterior

theorem shieldedDividerInputTape_eq_appendExterior
    (dividend width : Nat) (exterior : List WorkSymbol) :
    shieldedDividerInputTape dividend width exterior =
      appendExteriorTape
        (BuilderPostHeaderRawDivider.inputTape dividend width) exterior := by
  rw [BuilderPostHeaderRawDivider.inputTape_eq_inputWordTape]
  cases dividend <;>
    simp [shieldedDividerInputTape, dividerWord, appendExteriorTape,
      BuilderPostHeaderRawDivider.inputWordTape,
      BuilderPostHeaderRawDivider.phaseWord,
      BuilderPostHeaderRawDivider.leftBoundary, rightPathTape,
      List.replicate_succ]

private theorem divider_input_boundary_protected (dividend width : Nat) :
    DividerBoundaryProtected
      (BuilderPostHeaderRawDivider.inputTape dividend width) := by
  refine Or.inl ⟨[], ?_⟩
  rw [BuilderPostHeaderRawDivider.inputTape_eq_inputWordTape]
  cases dividend <;>
    simp [BuilderPostHeaderRawDivider.inputWordTape,
      BuilderPostHeaderRawDivider.phaseWord,
      BuilderPostHeaderRawDivider.leftBoundary, List.replicate_succ]

/-- M211's exact divider trace transports to the fresh shield without reading,
writing, or crossing any cell of the preserved exterior. -/
theorem shielded_divider_workRunExact (dividend width : Nat)
    (exterior : List WorkSymbol) (hWidth : 0 < width) :
    workRunExact? dividerMachine
        (BuilderPostHeaderRawDivider.workSteps dividend width)
        (shieldedDividerStartConfiguration dividend width exterior) =
      some (shieldedDividerFinalConfiguration dividend width exterior) := by
  have hCanonical := BuilderPostHeaderRawDivider.workRunExact dividend width
    hWidth
  have hTransport := divider_workRunExact_transport
    (BuilderPostHeaderRawDivider.workSteps dividend width)
    (workStartConfiguration dividerMachine
      (BuilderPostHeaderRawDivider.inputTape dividend width))
    (BuilderPostHeaderRawDivider.finalConfiguration dividend width)
    exterior (divider_input_boundary_protected dividend width) hCanonical
  simpa [shieldedDividerStartConfiguration,
    shieldedDividerFinalConfiguration, workStartConfiguration,
    shieldedDividerInputTape_eq_appendExterior,
    appendExteriorConfiguration] using hTransport

theorem shieldedDividerFinal_exterior_preserved
    (dividend width : Nat) (exterior : List WorkSymbol) :
    (shieldedDividerFinalConfiguration dividend width exterior).tape.left =
      (BuilderPostHeaderRawDivider.finalConfiguration dividend width).tape.left ++
        exterior := by
  rfl

theorem shieldedDividerFinal_head_preserved
    (dividend width : Nat) (exterior : List WorkSymbol) :
    (shieldedDividerFinalConfiguration dividend width exterior).tape.head =
      (BuilderPostHeaderRawDivider.finalConfiguration dividend width).tape.head := by
  rfl

theorem shieldedDividerFinal_right_preserved
    (dividend width : Nat) (exterior : List WorkSymbol) :
    (shieldedDividerFinalConfiguration dividend width exterior).tape.right =
      (BuilderPostHeaderRawDivider.finalConfiguration dividend width).tape.right := by
  rfl

def stripExteriorConfiguration (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) : WorkConfiguration :=
  { state := configuration.state
    tape :=
      { left := configuration.tape.left.take
          (configuration.tape.left.length - exterior.length)
        head := configuration.tape.head
        right := configuration.tape.right } }

theorem stripExterior_appendExterior (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) :
    stripExteriorConfiguration
        (appendExteriorConfiguration configuration exterior) exterior =
      configuration := by
  rcases configuration with ⟨state, ⟨left, head, right⟩⟩
  simp [stripExteriorConfiguration, appendExteriorConfiguration,
    appendExteriorTape, List.length_append]

/-- Decode only the shielded divider region, after removing the separately
tracked exterior suffix. -/
def shieldedTerminalQuotientRemainder (configuration : WorkConfiguration)
    (exterior : List WorkSymbol) : Nat × Nat :=
  BuilderPostHeaderRawDivider.terminalQuotientRemainder
    (stripExteriorConfiguration configuration exterior)

theorem shielded_final_quotient_remainder (dividend width : Nat)
    (exterior : List WorkSymbol) :
    shieldedTerminalQuotientRemainder
        (shieldedDividerFinalConfiguration dividend width exterior) exterior =
      (dividend / width, dividend % width) := by
  unfold shieldedTerminalQuotientRemainder
  rw [shieldedDividerFinalConfiguration, stripExterior_appendExterior]
  exact BuilderPostHeaderRawDivider.final_quotient_remainder dividend width

theorem run_compile_shielded_divider_exact (dividend width : Nat)
    (exterior : List WorkSymbol) (hWidth : 0 < width) :
    run (compileWorkMachine dividerMachine)
        (6 * BuilderPostHeaderRawDivider.workSteps dividend width)
        (encodeWorkConfiguration
          (shieldedDividerStartConfiguration dividend width exterior)) =
      encodeWorkConfiguration
        (shieldedDividerFinalConfiguration dividend width exterior) := by
  exact run_compileWorkMachine_mul_of_workRunExact dividerMachine
    (BuilderPostHeaderRawDivider.workSteps dividend width)
    (shieldedDividerStartConfiguration dividend width exterior)
    (shieldedDividerFinalConfiguration dividend width exterior)
    (shielded_divider_workRunExact dividend width exterior hWidth)

theorem equalFinal_tape_is_shieldedDivider_start
    (processed width : Nat) (workspace : List WorkSymbol) :
    (equalFinalConfiguration processed width workspace).tape =
      (shieldedDividerStartConfiguration 0 width
        (equalExterior processed width workspace)).tape := by
  rfl

theorem greaterFinal_tape_is_shieldedDivider_start
    (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) :
    (greaterFinalConfiguration processed remainingCoordinate width
        workspace).tape =
      (shieldedDividerStartConfiguration (remainingCoordinate + 1) width
        (greaterExterior processed remainingCoordinate width workspace)).tape := by
  rfl

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

theorem equal_one_step_short_not_halted (processed width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    machine.isHalted
        (workRun machine (equalWorkSteps width - 1)
          (equalInputConfiguration processed width workspace)) = false := by
  have hPositive : 0 < equalWorkSteps width := by
    unfold equalWorkSteps prefixWorkSteps
    omega
  exact one_step_short_not_halted_of_exact machine (equalWorkSteps width)
    (equalInputConfiguration processed width workspace)
    (equalFinalConfiguration processed width workspace) hPositive
    (equal_workRunExact processed width workspace hWidth)

theorem greater_one_step_short_not_halted
    (processed remainingCoordinate width : Nat)
    (workspace : List WorkSymbol) (hWidth : 0 < width) :
    machine.isHalted
        (workRun machine
          (greaterWorkSteps processed remainingCoordinate width - 1)
          (greaterInputConfiguration processed remainingCoordinate width
            workspace)) = false := by
  have hPositive :
      0 < greaterWorkSteps processed remainingCoordinate width := by
    unfold greaterWorkSteps prefixWorkSteps
    omega
  exact one_step_short_not_halted_of_exact machine
    (greaterWorkSteps processed remainingCoordinate width)
    (greaterInputConfiguration processed remainingCoordinate width workspace)
    (greaterFinalConfiguration processed remainingCoordinate width workspace)
    hPositive
    (greater_workRunExact processed remainingCoordinate width workspace hWidth)

private theorem shielded_divider_workSteps_positive
    (dividend width : Nat) (exterior : List WorkSymbol)
    (hWidth : 0 < width) :
    0 < BuilderPostHeaderRawDivider.workSteps dividend width := by
  cases hSteps : BuilderPostHeaderRawDivider.workSteps dividend width with
  | zero =>
      have hExact := shielded_divider_workRunExact dividend width exterior hWidth
      rw [hSteps] at hExact
      have hEqual :
          shieldedDividerStartConfiguration dividend width exterior =
            shieldedDividerFinalConfiguration dividend width exterior :=
        Option.some.inj hExact
      have hState := congrArg WorkConfiguration.state hEqual
      simp [shieldedDividerStartConfiguration,
        shieldedDividerFinalConfiguration, appendExteriorConfiguration,
        dividerMachine, BuilderPostHeaderRawDivider.machine,
        BuilderPostHeaderRawDivider.finalConfiguration,
        BuilderPostHeaderRawDivider.terminalConfiguration] at hState
  | succ steps => omega

theorem shielded_divider_one_step_short_not_halted
    (dividend width : Nat) (exterior : List WorkSymbol)
    (hWidth : 0 < width) :
    dividerMachine.isHalted
        (workRun dividerMachine
          (BuilderPostHeaderRawDivider.workSteps dividend width - 1)
          (shieldedDividerStartConfiguration dividend width exterior)) =
      false := by
  exact one_step_short_not_halted_of_exact dividerMachine
    (BuilderPostHeaderRawDivider.workSteps dividend width)
    (shieldedDividerStartConfiguration dividend width exterior)
    (shieldedDividerFinalConfiguration dividend width exterior)
    (shielded_divider_workSteps_positive dividend width exterior hWidth)
    (shielded_divider_workRunExact dividend width exterior hWidth)

/-! ## Uniform work bounds -/

private theorem copyAllSteps_le (processed copied width remaining : Nat) :
    copyAllSteps processed copied width remaining ≤
      (remaining + 1) *
        (2 * processed + 4 * (copied + remaining) + 2 * width + 13) := by
  induction remaining generalizing copied with
  | zero =>
      simp [copyAllSteps, copyCycleSteps]
  | succ remaining ih =>
      let bound :=
        2 * processed + 4 * (copied + (remaining + 1)) + 2 * width + 13
      have hCycle : copyCycleSteps processed copied width ≤ bound := by
        dsimp [bound]
        unfold copyCycleSteps
        omega
      have hTailBase := ih (copied + 1)
      have hTail :
          copyAllSteps processed (copied + 1) width remaining ≤
            (remaining + 1) * bound := by
        calc
          copyAllSteps processed (copied + 1) width remaining ≤
              (remaining + 1) *
                (2 * processed + 4 * ((copied + 1) + remaining) +
                  2 * width + 13) := hTailBase
          _ = (remaining + 1) * bound := by
            congr 1
            dsimp [bound]
            omega
      calc
        copyAllSteps processed copied width (remaining + 1) =
            copyCycleSteps processed copied width +
              copyAllSteps processed (copied + 1) width remaining := rfl
        _ ≤ bound + (remaining + 1) * bound :=
          Nat.add_le_add hCycle hTail
        _ = (remaining + 1 + 1) * bound := by
          calc
            bound + (remaining + 1) * bound =
                (remaining + 1) * bound + bound := Nat.add_comm _ _
            _ = (remaining + 1) * bound + 1 * bound := by simp
            _ = (remaining + 1 + 1) * bound :=
              (Nat.add_mul (remaining + 1) 1 bound).symm
        _ = (remaining + 1 + 1) *
            (2 * processed + 4 * (copied + (remaining + 1)) +
              2 * width + 13) := by rfl

private theorem widthAllSteps_le (remainder copied remaining : Nat) :
    widthAllSteps remainder copied remaining ≤
      (remaining + 1) *
        (4 * (copied + remaining) + 2 * remaining +
          2 * remainder + 9) := by
  induction remaining generalizing copied with
  | zero =>
      simp [widthAllSteps, widthFinishSteps]
      omega
  | succ remaining ih =>
      let bound :=
        4 * (copied + (remaining + 1)) + 2 * (remaining + 1) +
          2 * remainder + 9
      have hCycle :
          widthCycleSteps remainder copied (remaining + 1) ≤ bound := by
        dsimp [bound]
        unfold widthCycleSteps
        omega
      have hTailBase := ih (copied + 1)
      have hInner :
          4 * ((copied + 1) + remaining) + 2 * remaining +
              2 * remainder + 9 ≤
            bound := by
        dsimp [bound]
        omega
      have hTailScaled := Nat.mul_le_mul_left (remaining + 1) hInner
      have hTail :
          widthAllSteps remainder (copied + 1) remaining ≤
            (remaining + 1) * bound :=
        Nat.le_trans hTailBase hTailScaled
      calc
        widthAllSteps remainder copied (remaining + 1) =
            widthCycleSteps remainder copied (remaining + 1) +
              widthAllSteps remainder (copied + 1) remaining := rfl
        _ ≤ bound + (remaining + 1) * bound :=
          Nat.add_le_add hCycle hTail
        _ = (remaining + 1 + 1) * bound := by
          calc
            bound + (remaining + 1) * bound =
                (remaining + 1) * bound + bound := Nat.add_comm _ _
            _ = (remaining + 1) * bound + 1 * bound := by simp
            _ = (remaining + 1 + 1) * bound :=
              (Nat.add_mul (remaining + 1) 1 bound).symm
        _ = (remaining + 1 + 1) *
            (4 * (copied + (remaining + 1)) + 2 * (remaining + 1) +
              2 * remainder + 9) := by rfl

theorem equalWorkSteps_le_quadratic (width : Nat) :
    equalWorkSteps width ≤ 20 * (width + 1) * (width + 1) := by
  let size := width + 1
  have hWidth := widthAllSteps_le 0 0 width
  have hWidthInner :
      4 * (0 + width) + 2 * width + 2 * 0 + 9 ≤ 10 * size := by
    dsimp [size]
    omega
  have hWidthScaled := Nat.mul_le_mul_left (width + 1) hWidthInner
  have hWidthBound :
      widthAllSteps 0 0 width ≤ 10 * size * size := by
    calc
      widthAllSteps 0 0 width ≤
          (width + 1) *
            (4 * (0 + width) + 2 * width + 2 * 0 + 9) := hWidth
      _ ≤ (width + 1) * (10 * size) := hWidthScaled
      _ = 10 * size * size := by
        simp [size, Nat.mul_comm]
  have hPrefixLinear : prefixWorkSteps width ≤ 10 * size := by
    dsimp [size]
    unfold prefixWorkSteps
    omega
  have hSizeSelf : size ≤ size * size := by
    have hOne : 1 ≤ size := by
      dsimp [size]
      omega
    simpa using Nat.mul_le_mul_left size hOne
  have hPrefixBound : prefixWorkSteps width ≤ 10 * size * size := by
    exact Nat.le_trans hPrefixLinear (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 10 hSizeSelf)
  have hCoefficient : 10 * size + 10 * size ≤ 20 * size := by
    omega
  have hCombined := Nat.mul_le_mul_right size hCoefficient
  calc
    equalWorkSteps width =
        prefixWorkSteps width + widthAllSteps 0 0 width := rfl
    _ ≤ 10 * size * size + 10 * size * size :=
      Nat.add_le_add hPrefixBound hWidthBound
    _ ≤ 20 * size * size := by
      simpa [Nat.add_mul] using hCombined
    _ = 20 * (width + 1) * (width + 1) := by rfl

theorem greaterWorkSteps_le_quadratic
    (processed remainingCoordinate width : Nat) :
    greaterWorkSteps processed remainingCoordinate width ≤
      40 * (processed + remainingCoordinate + width + 1) *
        (processed + remainingCoordinate + width + 1) := by
  let size := processed + remainingCoordinate + width + 1
  have hSizePositive : 1 ≤ size := by
    dsimp [size]
    omega
  have hSizeSelf : size ≤ size * size := by
    simpa using Nat.mul_le_mul_left size hSizePositive
  have hPrefixLinear : prefixWorkSteps width ≤ 7 * size := by
    dsimp [size]
    unfold prefixWorkSteps
    omega
  have hPrefixBound : prefixWorkSteps width ≤ 7 * size * size :=
    Nat.le_trans hPrefixLinear (by
      simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 7 hSizeSelf)
  have hCopy := copyAllSteps_le processed 0 width remainingCoordinate
  have hCopyFactor : remainingCoordinate + 1 ≤ size := by
    dsimp [size]
    omega
  have hCopyInner :
      2 * processed + 4 * (0 + remainingCoordinate) + 2 * width + 13 ≤
        13 * size := by
    dsimp [size]
    omega
  have hCopyProduct := Nat.mul_le_mul hCopyFactor hCopyInner
  have hCopyBound :
      copyAllSteps processed 0 width remainingCoordinate ≤
        13 * size * size := by
    calc
      copyAllSteps processed 0 width remainingCoordinate ≤
          (remainingCoordinate + 1) *
            (2 * processed + 4 * (0 + remainingCoordinate) +
              2 * width + 13) := hCopy
      _ ≤ size * (13 * size) := hCopyProduct
      _ = 13 * size * size := by
        simp [Nat.mul_comm]
  have hWidth := widthAllSteps_le (remainingCoordinate + 1) 0 width
  have hWidthFactor : width + 1 ≤ size := by
    dsimp [size]
    omega
  have hWidthInner :
      4 * (0 + width) + 2 * width + 2 * (remainingCoordinate + 1) + 9 ≤
        11 * size := by
    dsimp [size]
    omega
  have hWidthProduct := Nat.mul_le_mul hWidthFactor hWidthInner
  have hWidthBound :
      widthAllSteps (remainingCoordinate + 1) 0 width ≤
        11 * size * size := by
    calc
      widthAllSteps (remainingCoordinate + 1) 0 width ≤
          (width + 1) *
            (4 * (0 + width) + 2 * width +
              2 * (remainingCoordinate + 1) + 9) := hWidth
      _ ≤ size * (11 * size) := hWidthProduct
      _ = 11 * size * size := by
        simp [Nat.mul_comm]
  have hCoefficient :
      7 * size + 13 * size + 11 * size ≤ 40 * size := by
    omega
  have hCombined := Nat.mul_le_mul_right size hCoefficient
  calc
    greaterWorkSteps processed remainingCoordinate width =
        prefixWorkSteps width +
          copyAllSteps processed 0 width remainingCoordinate +
            widthAllSteps (remainingCoordinate + 1) 0 width := rfl
    _ ≤ 7 * size * size + 13 * size * size + 11 * size * size :=
      Nat.add_le_add
        (Nat.add_le_add hPrefixBound hCopyBound) hWidthBound
    _ ≤ 40 * size * size := by
      simpa [Nat.add_mul] using hCombined
    _ = 40 * (processed + remainingCoordinate + width + 1) *
        (processed + remainingCoordinate + width + 1) := by rfl

def bridgeWorkStepsForResult
    (width : Nat) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult → Nat
  | .less _ _ => 0
  | .equal _ => equalWorkSteps width
  | .greater processed remainingCoordinate =>
      greaterWorkSteps processed remainingCoordinate width

private theorem scaled_square_mono (factor left right : Nat)
    (h : left ≤ right) :
    factor * left * left ≤ factor * right * right := by
  have hSquare := Nat.mul_le_mul h h
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left factor hSquare

theorem bridgeWorkSteps_compareResult_le
    (processed coordinate boundary width : Nat) :
    bridgeWorkStepsForResult width
        (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult
          processed coordinate boundary) ≤
      40 * (processed + coordinate + boundary + width + 1) *
        (processed + coordinate + boundary + width + 1) := by
  induction coordinate generalizing processed boundary with
  | zero =>
      cases boundary with
      | zero =>
          have hEqual := equalWorkSteps_le_quadratic width
          let small := width + 1
          let large := processed + 0 + 0 + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 20 small large hSize
          have hCoefficient : 20 * large * large ≤ 40 * large * large := by
            have hTwenty : 20 ≤ 40 := by omega
            exact Nat.mul_le_mul_right large
              (Nat.mul_le_mul_right large hTwenty)
          exact Nat.le_trans hEqual (Nat.le_trans hScaled hCoefficient)
      | succ boundary =>
          simp [bridgeWorkStepsForResult,
            BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult]
  | succ coordinate ih =>
      cases boundary with
      | zero =>
          have hGreater := greaterWorkSteps_le_quadratic
            processed coordinate width
          let small := processed + coordinate + width + 1
          let large := processed + (coordinate + 1) + 0 + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          exact Nat.le_trans hGreater
            (scaled_square_mono 40 small large hSize)
      | succ boundary =>
          have hTail := ih (processed + 1) boundary
          let small := processed + 1 + coordinate + boundary + width + 1
          let large :=
            processed + (coordinate + 1) + (boundary + 1) + width + 1
          have hSize : small ≤ large := by
            dsimp [small, large]
            omega
          have hScaled := scaled_square_mono 40 small large hSize
          exact Nat.le_trans hTail hScaled

/-! ## One source-size bound for router, bridge, and shielded divider -/

def stagedCompiledSteps {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat) : Nat :=
  BuilderPostHeaderRawLaunch.stagedCompiledSteps problem coordinate +
    6 * bridgeWorkStepsForResult problem.formulaTokensPerClause
      (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
        (BuilderFullScheduleCursorController.firstBodySlot problem))

def bridgeSizePolynomial {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add
    (.mul (.constant 2)
      (BuilderFullScheduleCursorController.terminalSlotPolynomial verifier))
    (.add (formulaClauseTokenPolynomial verifier) (.constant 1))

def rawTimeBound {language : Language}
    (verifier : PolynomialTimeVerifier language) : NatPolynomial :=
  .add (BuilderPostHeaderRawLaunch.rawTimeBound verifier)
    (.mul (.constant 240)
      (.mul (bridgeSizePolynomial verifier)
        (bridgeSizePolynomial verifier)))

theorem bridgeSizePolynomial_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (bridgeSizePolynomial problem.verifier).eval problem.input.length =
      2 * BuilderFullScheduleCursorController.terminalSlot problem +
        problem.formulaTokensPerClause + 1 := by
  rfl

theorem rawTimeBound_eval {language : Language}
    (problem : VerifierTableauProblem language) :
    (rawTimeBound problem.verifier).eval problem.input.length =
      (BuilderPostHeaderRawLaunch.rawTimeBound problem.verifier).eval
          problem.input.length +
        240 *
          ((2 * BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaTokensPerClause + 1) *
            (2 * BuilderFullScheduleCursorController.terminalSlot problem +
              problem.formulaTokensPerClause + 1)) := by
  rfl

theorem stagedCompiledSteps_le_rawTimeBound {language : Language}
    (problem : VerifierTableauProblem language) (coordinate : Nat)
    (hCoordinate :
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem) :
    stagedCompiledSteps problem coordinate ≤
      (rawTimeBound problem.verifier).eval problem.input.length := by
  have hBase := BuilderPostHeaderRawLaunch.stagedCompiledSteps_le_rawTimeBound
    problem coordinate hCoordinate
  have hFirstBody :
      BuilderFullScheduleCursorController.firstBodySlot problem ≤
        BuilderFullScheduleCursorController.terminalSlot problem := by
    rw [← BuilderFullScheduleCursorController.firstBodySlot_add_bodySlotCount
      problem]
    omega
  have hBridge := bridgeWorkSteps_compareResult_le 0 coordinate
    (BuilderFullScheduleCursorController.firstBodySlot problem)
    problem.formulaTokensPerClause
  let small :=
    0 + coordinate +
      BuilderFullScheduleCursorController.firstBodySlot problem +
        problem.formulaTokensPerClause + 1
  let large :=
    2 * BuilderFullScheduleCursorController.terminalSlot problem +
      problem.formulaTokensPerClause + 1
  have hSize : small ≤ large := by
    dsimp [small, large]
    omega
  have hBridgeLarge :
      bridgeWorkStepsForResult problem.formulaTokensPerClause
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
        40 * large * large :=
    Nat.le_trans hBridge (scaled_square_mono 40 small large hSize)
  have hBridgeCompiled := Nat.mul_le_mul_left 6 hBridgeLarge
  have hBridgeCompiled' :
      6 * bridgeWorkStepsForResult problem.formulaTokensPerClause
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
        240 * (large * large) := by
    calc
      6 * bridgeWorkStepsForResult problem.formulaTokensPerClause
          (BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0 coordinate
            (BuilderFullScheduleCursorController.firstBodySlot problem)) ≤
          6 * (40 * large * large) := hBridgeCompiled
      _ = 240 * (large * large) := by
        calc
          6 * (40 * large * large) = (6 * 40 * large) * large := by
            rw [← Nat.mul_assoc 6 (40 * large) large,
              ← Nat.mul_assoc 6 40 large]
          _ = 240 * large * large := by rfl
          _ = 240 * (large * large) := Nat.mul_assoc 240 large large
  unfold stagedCompiledSteps
  rw [rawTimeBound_eval]
  exact Nat.add_le_add hBase (by
    simpa [large] using hBridgeCompiled')

/-! ## Certificate-free public endpoint -/

/-- Exact bridge-and-divider obligations selected solely by the M209 result.
The header case deliberately performs no post-header work. -/
def ResultBridgeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol) :
    BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult → Prop
  | .less _ _ => True
  | .equal processed =>
      equalInputTape processed problem.formulaTokensPerClause workspace =
          extendRouterResultTape
            (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
              (.equal processed)).tape
            problem.formulaTokensPerClause workspace ∧
      workRunExact? machine
          (equalWorkSteps problem.formulaTokensPerClause)
          (equalInputConfiguration processed problem.formulaTokensPerClause
            workspace) =
        some (equalFinalConfiguration processed
          problem.formulaTokensPerClause workspace) ∧
      (equalFinalConfiguration processed problem.formulaTokensPerClause
          workspace).tape =
        (shieldedDividerStartConfiguration 0
          problem.formulaTokensPerClause
          (equalExterior processed problem.formulaTokensPerClause
            workspace)).tape ∧
      workRunExact? dividerMachine
          (BuilderPostHeaderRawDivider.workSteps 0
            problem.formulaTokensPerClause)
          (shieldedDividerStartConfiguration 0
            problem.formulaTokensPerClause
            (equalExterior processed problem.formulaTokensPerClause
              workspace)) =
        some (shieldedDividerFinalConfiguration 0
          problem.formulaTokensPerClause
          (equalExterior processed problem.formulaTokensPerClause
            workspace)) ∧
      shieldedTerminalQuotientRemainder
          (shieldedDividerFinalConfiguration 0
            problem.formulaTokensPerClause
            (equalExterior processed problem.formulaTokensPerClause
              workspace))
          (equalExterior processed problem.formulaTokensPerClause workspace) =
        (0, 0)
  | .greater processed remainingCoordinate =>
      greaterInputTape processed remainingCoordinate
          problem.formulaTokensPerClause workspace =
          extendRouterResultTape
            (BuilderArbitrarySlotHeaderRouter.RawRouter.resultConfiguration
              (.greater processed remainingCoordinate)).tape
            problem.formulaTokensPerClause workspace ∧
      workRunExact? machine
          (greaterWorkSteps processed remainingCoordinate
            problem.formulaTokensPerClause)
          (greaterInputConfiguration processed remainingCoordinate
            problem.formulaTokensPerClause workspace) =
        some (greaterFinalConfiguration processed remainingCoordinate
          problem.formulaTokensPerClause workspace) ∧
      (greaterFinalConfiguration processed remainingCoordinate
          problem.formulaTokensPerClause workspace).tape =
        (shieldedDividerStartConfiguration (remainingCoordinate + 1)
          problem.formulaTokensPerClause
          (greaterExterior processed remainingCoordinate
            problem.formulaTokensPerClause workspace)).tape ∧
      workRunExact? dividerMachine
          (BuilderPostHeaderRawDivider.workSteps (remainingCoordinate + 1)
            problem.formulaTokensPerClause)
          (shieldedDividerStartConfiguration (remainingCoordinate + 1)
            problem.formulaTokensPerClause
            (greaterExterior processed remainingCoordinate
              problem.formulaTokensPerClause workspace)) =
        some (shieldedDividerFinalConfiguration (remainingCoordinate + 1)
          problem.formulaTokensPerClause
          (greaterExterior processed remainingCoordinate
            problem.formulaTokensPerClause workspace)) ∧
      shieldedTerminalQuotientRemainder
          (shieldedDividerFinalConfiguration (remainingCoordinate + 1)
            problem.formulaTokensPerClause
            (greaterExterior processed remainingCoordinate
              problem.formulaTokensPerClause workspace))
          (greaterExterior processed remainingCoordinate
            problem.formulaTokensPerClause workspace) =
        ((remainingCoordinate + 1) / problem.formulaTokensPerClause,
          (remainingCoordinate + 1) % problem.formulaTokensPerClause)

theorem resultBridgeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (workspace : List WorkSymbol)
    (result :
      BuilderArbitrarySlotHeaderRouter.RawRouter.ComparisonResult) :
    ResultBridgeHolds problem workspace result := by
  have hWidth := BuilderPostHeaderRawLaunch.formulaTokensPerClause_pos problem
  cases result with
  | less processed remainingBoundary => trivial
  | equal processed =>
      exact ⟨equalInputTape_is_exact_router_result processed
          problem.formulaTokensPerClause workspace,
        equal_workRunExact processed problem.formulaTokensPerClause workspace
          hWidth,
        equalFinal_tape_is_shieldedDivider_start processed
          problem.formulaTokensPerClause workspace,
        shielded_divider_workRunExact 0 problem.formulaTokensPerClause
          (equalExterior processed problem.formulaTokensPerClause workspace)
          hWidth,
        (by simpa using
          (shielded_final_quotient_remainder 0
            problem.formulaTokensPerClause
            (equalExterior processed problem.formulaTokensPerClause
              workspace)))⟩
  | greater processed remainingCoordinate =>
      exact ⟨greaterInputTape_is_exact_router_result processed
          remainingCoordinate problem.formulaTokensPerClause workspace,
        greater_workRunExact processed remainingCoordinate
          problem.formulaTokensPerClause workspace hWidth,
        greaterFinal_tape_is_shieldedDivider_start processed
          remainingCoordinate problem.formulaTokensPerClause workspace,
        shielded_divider_workRunExact (remainingCoordinate + 1)
          problem.formulaTokensPerClause
          (greaterExterior processed remainingCoordinate
            problem.formulaTokensPerClause workspace) hWidth,
        shielded_final_quotient_remainder (remainingCoordinate + 1)
          problem.formulaTokensPerClause
          (greaterExterior processed remainingCoordinate
            problem.formulaTokensPerClause workspace)⟩

def InRangeRouteBridgeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) : Prop :=
  let result := BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
    coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)
  match outerRoute problem coordinate.val with
  | .header _ =>
      BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
        result = none
  | .postHeader remainder =>
      BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
          result = some remainder ∧
        ResultBridgeHolds problem workspace result ∧
        BuilderPostHeaderRawLaunch.RouteDecodeHolds problem remainder ∧
        postHeaderRoute problem remainder ≠ .outOfRange

theorem inRangeRouteBridgeHolds {language : Language}
    (problem : VerifierTableauProblem language)
    (coordinate :
      Fin (BuilderFullScheduleCursorController.terminalSlot problem))
    (workspace : List WorkSymbol) :
    InRangeRouteBridgeHolds problem coordinate workspace := by
  let result := BuilderArbitrarySlotHeaderRouter.RawRouter.compareResult 0
    coordinate.val
      (BuilderFullScheduleCursorController.firstBodySlot problem)
  have hRemainder :
      BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
          result =
        match outerRoute problem coordinate.val with
        | .header _ => none
        | .postHeader remainder => some remainder := by
    dsimp [result]
    rw [BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.compareResult_postHeaderRemainder?]
    unfold outerRoute
    split <;> rfl
  have hBridge := resultBridgeHolds problem workspace result
  cases hOuter : outerRoute problem coordinate.val with
  | header headerCoordinate =>
      simpa [InRangeRouteBridgeHolds, result, hOuter] using hRemainder
  | postHeader remainder =>
      have hDecode := BuilderPostHeaderRawLaunch.routeDecodeHolds problem
        remainder
      have hInRange := postHeaderRoute_in_range problem coordinate remainder
        hOuter
      have hRecovered :
          BuilderArbitrarySlotPostHeaderDecoder.RawRemainder.comparisonResultPostHeaderRemainder?
              result = some remainder := by
        simpa [hOuter] using hRemainder
      simpa [InRangeRouteBridgeHolds, result, hOuter] using
        And.intro hRecovered (And.intro hBridge (And.intro hDecode hInRange))

/-- M213 closes the literal M209-to-M211 physical tape handoff for every
coordinate and arbitrary exterior workspace. It does not emit a formula token,
iterate the full builder, or package the Cook-Levin reduction. -/
theorem cook_levin_builder_post_header_raw_tape_bridge_checked_complete
    {language : Language} (problem : VerifierTableauProblem language) :
    rules.length = 351 ∧
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) ∧
    (∀ (workspace : List WorkSymbol) result,
      ResultBridgeHolds problem workspace result) ∧
    (∀ (workspace : List WorkSymbol)
      (coordinate :
        Fin (BuilderFullScheduleCursorController.terminalSlot problem)),
      InRangeRouteBridgeHolds problem coordinate workspace) ∧
    (∀ coordinate,
      coordinate < BuilderFullScheduleCursorController.terminalSlot problem →
        stagedCompiledSteps problem coordinate ≤
          (rawTimeBound problem.verifier).eval problem.input.length) := by
  exact ⟨rules_length, rules_pairwise_query_distinct,
    resultBridgeHolds problem,
    (fun workspace coordinate =>
      inRangeRouteBridgeHolds problem coordinate workspace),
    stagedCompiledSteps_le_rawTimeBound problem⟩

end BuilderPostHeaderRawTapeBridge

end CookLevin

end PNP.Concrete
