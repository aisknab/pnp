/-
Copyright (c) 2026 PNP Labs.

Literal coordinate-preserving restoration of a mirrored divider endpoint.
Insert a real separator before the consumed segment, retaining quotient and
remainder as separate ordinary registers. Forty-one fixed rules shift and normalize
only the scratch prefix. Two outer blank cells are charged and consumed;
the original source workspace and the remaining outer tail are preserved.

The generic tape view is descriptive, not supplied correctness or generated
control. Source binding and general constraint selection are separate layers.
-/

import PNP.Concrete.CookLevinBuilderClauseDividerExecution

namespace PNP.Concrete.CookLevin.BuilderDividerCoordinateRegisters

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial

abbrev quotientMark : WorkSymbol := BuilderPostHeaderRawDivider.quotientMark
abbrev consumedMark : WorkSymbol := BuilderPostHeaderRawDivider.consumedDividend

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := write, move := move }

private inductive Carry where
  | unit | separator | endMark | quotient

private def Carry.state : Carry → Nat
  | .unit => 3
  | .separator => 4
  | .endMark => 5
  | .quotient => 6

private def Carry.symbol : Carry → WorkSymbol
  | .unit => unitSymbol
  | .separator => separatorSymbol
  | .endMark => scratchEndSymbol
  | .quotient => quotientMark

private def carryRules (carry : Carry) : List WorkRule :=
  [rule carry.state Carry.unit.state unitSymbol carry.symbol .left,
   rule carry.state Carry.separator.state separatorSymbol carry.symbol .left,
   rule carry.state Carry.endMark.state scratchEndSymbol carry.symbol .left,
   rule carry.state Carry.quotient.state quotientMark carry.symbol .left,
   rule carry.state 7 .blank carry.symbol .left]

def rules : List WorkRule :=
  [rule 0 1 scratchEndSymbol scratchEndSymbol .right,
   rule 1 1 unitSymbol unitSymbol .right,
   rule 1 2 separatorSymbol separatorSymbol .right,
   rule 2 2 unitSymbol unitSymbol .right,
   rule 2 4 consumedMark consumedMark .left,
   rule 2 4 leftMarker leftMarker .left] ++
  carryRules .unit ++ carryRules .separator ++
  carryRules .endMark ++ carryRules .quotient ++
  [rule 7 8 .blank scratchEndSymbol .right,
   rule 8 8 quotientMark unitSymbol .right,
   rule 8 9 scratchEndSymbol separatorSymbol .right,
   rule 9 9 unitSymbol unitSymbol .right,
   rule 9 10 separatorSymbol separatorSymbol .right,
   rule 10 10 unitSymbol unitSymbol .right,
   rule 10 11 separatorSymbol separatorSymbol .right,
   rule 11 11 consumedMark unitSymbol .right,
   rule 11 12 leftMarker separatorSymbol .right,
   rule 12 13 leftMarker separatorSymbol .right,
   rule 13 13 unitSymbol unitSymbol .right,
   rule 13 14 scratchEndSymbol separatorSymbol .left,
   rule 14 14 unitSymbol unitSymbol .left,
   rule 14 14 separatorSymbol separatorSymbol .left,
   rule 14 15 scratchEndSymbol scratchEndSymbol .stay]

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 15, rejectState := 16 }

private theorem startState_eq : machine.startState = 0 := rfl

theorem rules_length : rules.length = 41 := rfl

theorem rules_pairwise_query_distinct : rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro selected hMem
  change selected.sourceState ≠ 15
  change selected ∈ rules at hMem
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

/-- A view of existing cells, with no input-dependent machine control. -/
structure RestoreView where
  quotient : Nat
  width : Nat
  remainder : Nat
  consumed : Nat
  sidecarCount : Nat
  deriving DecidableEq, Repr

def restoredValues (view : RestoreView) : List Nat :=
  [view.sidecarCount, 0, view.consumed, view.remainder, view.width, view.quotient]

private def rightFocus (left word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

def inputTape (view : RestoreView) (workspace tail : List WorkSymbol) : WorkTape :=
  {
    left := List.replicate view.quotient quotientMark ++ tail
    head := scratchEndSymbol
    right := List.replicate view.width unitSymbol ++ separatorSymbol ::
      (List.replicate view.remainder unitSymbol ++
        List.replicate view.consumed consumedMark ++ leftMarker :: leftMarker ::
          (List.replicate view.sidecarCount unitSymbol ++ scratchEndSymbol :: workspace))
  }

def initialConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (inputTape view workspace tail)

def finalConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  { state := machine.acceptState,
    tape := BuilderDividerOperands.endTape (restoredValues view) workspace (tail.drop 2) }

def workSteps (view : RestoreView) : Nat :=
  3 * view.quotient + 4 * view.width + 4 * view.remainder +
    2 * view.consumed + 2 * view.sidecarCount + 19

private theorem carry_step (carry next : Carry) (left right : List WorkSymbol) :
    workStep? machine
      { state := carry.state, tape := { left := left, head := next.symbol, right := right } } =
      some {
        state := next.state
        tape := BuilderDividerLayout.leftFocus left (carry.symbol :: right)
      } := by
  cases carry <;> cases next <;> rfl

private theorem shift_left (word : List Carry) (carry : Carry)
    (tail right : List WorkSymbol) (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine (word.length + 1)
      { state := carry.state,
        tape := BuilderDividerLayout.leftFocus (word.map Carry.symbol ++ tail) right } =
      some {
        state := 7
        tape := BuilderDividerLayout.leftFocus (tail.drop 1)
          ((word.map Carry.symbol).reverse ++ carry.symbol :: right)
      } := by
  induction word generalizing carry right with
  | nil =>
    cases tail with
    | nil => cases carry <;> rfl
    | cons symbol rest =>
      change symbol = .blank at hBlank
      subst symbol
      cases carry <;> rfl
  | cons next rest ih =>
    simp only [List.length_cons, List.map_cons, List.cons_append,
      BuilderDividerLayout.leftFocus, workRunExact?]
    rw [carry_step]
    simpa only [List.map_cons, List.reverse_cons, List.append_assoc,
      List.cons_append, List.nil_append, workRunExact?, BuilderDividerLayout.leftFocus]
      using ih next (carry.symbol :: right)

private theorem create_end (tail right : List WorkSymbol)
    (hBlank : tail.headD .blank = .blank) :
    workRunExact? machine 1
      { state := 7, tape := BuilderDividerLayout.leftFocus tail right } =
      some {
        state := 8
        tape := rightFocus (scratchEndSymbol :: tail.drop 1) right
      } := by
  cases tail with
  | nil => rfl
  | cons symbol rest =>
    change symbol = .blank at hBlank
    subst symbol
    rfl

private def RightScanSymbol (state : Nat) (symbol : WorkSymbol) : Prop :=
  (state = 1 ∧ symbol = unitSymbol) ∨
  (state = 2 ∧ symbol = unitSymbol) ∨
  (state = 8 ∧ symbol = quotientMark) ∨
  (state = 9 ∧ symbol = unitSymbol) ∨
  (state = 10 ∧ symbol = unitSymbol) ∨
  (state = 11 ∧ symbol = consumedMark) ∨
  (state = 13 ∧ symbol = unitSymbol)

private theorem right_loop (state : Nat) (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : RightScanSymbol state symbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := rightFocus (unitSymbol :: left) right } := by
  rcases hSymbol with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

private theorem scan_right (state count : Nat) (symbol stop : WorkSymbol)
    (right left : List WorkSymbol) (hSymbol : RightScanSymbol state symbol) :
    workRunExact? machine count
      { state := state, tape := rightFocus left (List.replicate count symbol ++ stop :: right) } =
      some {
        state := state
        tape := { left := List.replicate count unitSymbol ++ left, head := stop, right := right }
      } := by
  induction count generalizing left with
  | zero => rfl
  | succ count ih =>
    simp only [List.replicate_succ, List.cons_append, rightFocus, workRunExact?]
    rw [right_loop state symbol left _ hSymbol]
    have hJoin : unitSymbol :: (List.replicate count unitSymbol ++ left) =
        List.replicate count unitSymbol ++ unitSymbol :: left := by
      calc
        _ = List.replicate (count + 1) unitSymbol ++ left := rfl
        _ = _ := by
          rw [List.replicate_succ']
          simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hJoin]
    exact ih (unitSymbol :: left)

private def RewindSafe (word : List WorkSymbol) : Prop :=
  ∀ symbol ∈ word, symbol = unitSymbol ∨ symbol = separatorSymbol

private theorem rewind_step (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : symbol = unitSymbol ∨ symbol = separatorSymbol) :
    workStep? machine { state := 14, tape := { left := left, head := symbol, right := right } } =
      some { state := 14, tape := BuilderDividerLayout.leftFocus left (symbol :: right) } := by
  rcases hSymbol with rfl | rfl <;> rfl

private theorem rewind (word tail right : List WorkSymbol) (hSafe : RewindSafe word) :
    workRunExact? machine word.length
      { state := 14, tape := BuilderDividerLayout.leftFocus (word ++ scratchEndSymbol :: tail) right } =
      some {
        state := 14
        tape := { left := tail, head := scratchEndSymbol, right := word.reverse ++ right }
      } := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hRest : RewindSafe rest := by
      intro next hMem
      exact hSafe next (List.mem_cons_of_mem symbol hMem)
    have hStep := rewind_step symbol (rest ++ scratchEndSymbol :: tail) right
      (hSafe symbol List.mem_cons_self)
    simp only [List.length_cons, List.cons_append, BuilderDividerLayout.leftFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
      List.nil_append] using ih (symbol :: right) hRest

private theorem safe_replicate (count : Nat) : RewindSafe (List.replicate count unitSymbol) := by
  intro symbol hMem
  exact Or.inl (List.eq_of_mem_replicate hMem)

private theorem safe_separator {word : List WorkSymbol} (hWord : RewindSafe word) :
    RewindSafe (separatorSymbol :: word) := by
  intro symbol hMem
  rcases List.mem_cons.mp hMem with hEqual | hRest
  · exact Or.inr hEqual
  · exact hWord symbol hRest

private theorem safe_append {left right : List WorkSymbol}
    (hLeft : RewindSafe left) (hRight : RewindSafe right) : RewindSafe (left ++ right) := by
  intro symbol hMem
  rcases List.mem_append.mp hMem with hMem | hMem
  · exact hLeft symbol hMem
  · exact hRight symbol hMem

/-- Execute the literal handoff, consuming only its two required outer blanks.
An empty tail supplies implicit blank cells; explicit padding is not erased
by an unproved tape-equality shortcut. -/
theorem workRunExact (view : RestoreView) (workspace tail : List WorkSymbol)
    (hFirst : tail.headD .blank = .blank)
    (hSecond : (tail.drop 1).headD .blank = .blank) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) := by
  let sideWord := List.replicate view.sidecarCount unitSymbol ++ scratchEndSymbol :: workspace
  let consumedWord := List.replicate view.consumed consumedMark ++ leftMarker :: leftMarker :: sideWord
  let remainderWord := List.replicate view.remainder unitSymbol ++ consumedWord
  let widthWord := List.replicate view.width unitSymbol ++ separatorSymbol :: remainderWord
  let initialLeft := List.replicate view.quotient quotientMark ++ tail
  let leftWidth := List.replicate view.width unitSymbol ++ scratchEndSymbol :: initialLeft
  let leftRemainder := List.replicate view.remainder unitSymbol ++ separatorSymbol :: leftWidth
  let widthStart : WorkConfiguration :=
    { state := 1, tape := rightFocus (scratchEndSymbol :: initialLeft) widthWord }
  let widthEnd : WorkConfiguration :=
    { state := 1, tape := { left := leftWidth, head := separatorSymbol, right := remainderWord } }
  let remainderStart : WorkConfiguration :=
    { state := 2, tape := rightFocus (separatorSymbol :: leftWidth) remainderWord }
  let remainderEnd : WorkConfiguration :=
    { state := 2, tape := rightFocus leftRemainder consumedWord }
  let shiftWord : List Carry :=
    List.replicate view.remainder .unit ++ Carry.separator ::
      (List.replicate view.width .unit ++ Carry.endMark ::
        List.replicate view.quotient .quotient)
  let shiftStart : WorkConfiguration :=
    { state := Carry.separator.state, tape := BuilderDividerLayout.leftFocus leftRemainder consumedWord }
  let mixedPrefix := List.replicate view.quotient quotientMark ++ scratchEndSymbol ::
    (List.replicate view.width unitSymbol ++ separatorSymbol ::
      (List.replicate view.remainder unitSymbol ++ separatorSymbol :: consumedWord))
  let shiftEnd : WorkConfiguration :=
    { state := 7, tape := BuilderDividerLayout.leftFocus (tail.drop 1) mixedPrefix }
  let left0 := scratchEndSymbol :: tail.drop 2
  let leftQ := List.replicate view.quotient unitSymbol ++ left0
  let leftW := List.replicate view.width unitSymbol ++ separatorSymbol :: leftQ
  let leftR := List.replicate view.remainder unitSymbol ++ separatorSymbol :: leftW
  let leftC := List.replicate view.consumed unitSymbol ++ separatorSymbol :: leftR
  let leftSide := List.replicate view.sidecarCount unitSymbol ++ separatorSymbol :: separatorSymbol :: leftC
  let afterQ := List.replicate view.width unitSymbol ++ separatorSymbol ::
    (List.replicate view.remainder unitSymbol ++ separatorSymbol :: consumedWord)
  let afterW := List.replicate view.remainder unitSymbol ++ separatorSymbol :: consumedWord
  let quotientStart : WorkConfiguration :=
    { state := 8, tape := rightFocus left0 mixedPrefix }
  let quotientEnd : WorkConfiguration :=
    { state := 8, tape := { left := leftQ, head := scratchEndSymbol, right := afterQ } }
  let normalWidthStart : WorkConfiguration :=
    { state := 9, tape := rightFocus (separatorSymbol :: leftQ) afterQ }
  let normalWidthEnd : WorkConfiguration :=
    { state := 9, tape := { left := leftW, head := separatorSymbol, right := afterW } }
  let normalRemainderStart : WorkConfiguration :=
    { state := 10, tape := rightFocus (separatorSymbol :: leftW) afterW }
  let normalRemainderEnd : WorkConfiguration :=
    { state := 10, tape := { left := leftR, head := separatorSymbol, right := consumedWord } }
  let consumedStart : WorkConfiguration :=
    { state := 11, tape := rightFocus (separatorSymbol :: leftR) consumedWord }
  let consumedEnd : WorkConfiguration :=
    { state := 11, tape := { left := leftC, head := leftMarker, right := leftMarker :: sideWord } }
  let sideStart : WorkConfiguration :=
    { state := 13, tape := rightFocus (separatorSymbol :: separatorSymbol :: leftC) sideWord }
  let sideEnd : WorkConfiguration :=
    { state := 13, tape := { left := leftSide, head := scratchEndSymbol, right := workspace } }
  let normalPrefix := List.replicate view.sidecarCount unitSymbol ++ separatorSymbol :: separatorSymbol ::
    (List.replicate view.consumed unitSymbol ++ separatorSymbol ::
      (List.replicate view.remainder unitSymbol ++ separatorSymbol ::
        (List.replicate view.width unitSymbol ++ separatorSymbol ::
          List.replicate view.quotient unitSymbol)))
  let rewindStart : WorkConfiguration :=
    {
      state := 14
      tape := BuilderDividerLayout.leftFocus
        (normalPrefix ++ scratchEndSymbol :: tail.drop 2) (separatorSymbol :: workspace)
    }
  let rewindEnd : WorkConfiguration :=
    {
      state := 14
      tape := {
        left := tail.drop 2
        head := scratchEndSymbol
        right := normalPrefix.reverse ++ separatorSymbol :: workspace
      }
    }
  have hLaunch : workRunExact? machine 1 (initialConfiguration view workspace tail) = some widthStart := by
    simp only [initialConfiguration, workStartConfiguration, startState_eq, inputTape,
      widthStart, initialLeft, widthWord, remainderWord, consumedWord, sideWord, List.append_assoc]
    rfl
  have hWidth : workRunExact? machine view.width widthStart = some widthEnd := by
    exact scan_right 1 view.width unitSymbol separatorSymbol remainderWord
      (scratchEndSymbol :: initialLeft) (Or.inl ⟨rfl, rfl⟩)
  have hToRemainder : workRunExact? machine 1 widthEnd = some remainderStart := by rfl
  have hRemainder : workRunExact? machine view.remainder remainderStart = some remainderEnd := by
    cases hConsumed : view.consumed with
    | zero =>
      have h := scan_right 2 view.remainder unitSymbol leftMarker
        (leftMarker :: sideWord) (separatorSymbol :: leftWidth)
        (Or.inr (Or.inl ⟨rfl, rfl⟩))
      simpa only [remainderStart, remainderEnd, remainderWord, consumedWord,
        leftRemainder, hConsumed, List.replicate_zero, List.nil_append, rightFocus] using h
    | succ consumed =>
      have h := scan_right 2 view.remainder unitSymbol consumedMark
        (List.replicate consumed consumedMark ++ leftMarker :: leftMarker :: sideWord)
        (separatorSymbol :: leftWidth) (Or.inr (Or.inl ⟨rfl, rfl⟩))
      simpa only [remainderStart, remainderEnd, remainderWord, consumedWord,
        leftRemainder, hConsumed, List.replicate_succ, List.cons_append, rightFocus] using h
  have hToShift : workRunExact? machine 1 remainderEnd = some shiftStart := by
    cases hConsumed : view.consumed with
    | zero =>
      simp only [remainderEnd, shiftStart, consumedWord, hConsumed,
        List.replicate_zero, List.nil_append, rightFocus]
      rfl
    | succ consumed =>
      simp only [remainderEnd, shiftStart, consumedWord, hConsumed,
        List.replicate_succ, List.cons_append, rightFocus]
      rfl
  have hShift : workRunExact? machine (shiftWord.length + 1) shiftStart = some shiftEnd := by
    have h := shift_left shiftWord .separator tail consumedWord hFirst
    simpa only [shiftStart, shiftEnd, shiftWord, leftRemainder, leftWidth, initialLeft,
      mixedPrefix, List.map_append, List.map_cons, List.map_replicate, List.map_nil,
      Carry.symbol, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using h
  have hEnd : workRunExact? machine 1 shiftEnd = some quotientStart := by
    have h := create_end (tail.drop 1) mixedPrefix hSecond
    simpa only [shiftEnd, quotientStart, left0, List.drop_drop] using h
  have hQuotient : workRunExact? machine view.quotient quotientStart = some quotientEnd := by
    have h := scan_right 8 view.quotient quotientMark scratchEndSymbol afterQ left0
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    exact h
  have hToWidth : workRunExact? machine 1 quotientEnd = some normalWidthStart := by rfl
  have hNormalWidth : workRunExact? machine view.width normalWidthStart = some normalWidthEnd := by
    exact scan_right 9 view.width unitSymbol separatorSymbol afterW (separatorSymbol :: leftQ)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))
  have hToLocal : workRunExact? machine 1 normalWidthEnd = some normalRemainderStart := by rfl
  have hLocal : workRunExact? machine view.remainder normalRemainderStart = some normalRemainderEnd := by
    exact scan_right 10 view.remainder unitSymbol separatorSymbol consumedWord (separatorSymbol :: leftW)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))))
  have hToConsumed : workRunExact? machine 1 normalRemainderEnd = some consumedStart := by rfl
  have hConsumed : workRunExact? machine view.consumed consumedStart = some consumedEnd := by
    exact scan_right 11 view.consumed consumedMark leftMarker (leftMarker :: sideWord)
      (separatorSymbol :: leftR)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))))))
  have hBoundaries : workRunExact? machine 2 consumedEnd = some sideStart := by rfl
  have hSide : workRunExact? machine view.sidecarCount sideStart = some sideEnd := by
    exact scan_right 13 view.sidecarCount unitSymbol scratchEndSymbol workspace
      (separatorSymbol :: separatorSymbol :: leftC)
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))))
  have hLeftSide : leftSide = normalPrefix ++ scratchEndSymbol :: tail.drop 2 := by
    simp only [leftSide, leftC, leftR, leftW, leftQ, left0, normalPrefix,
      List.append_assoc, List.cons_append]
  have hTurn : workRunExact? machine 1 sideEnd = some rewindStart := by
    have h : workRunExact? machine 1 sideEnd =
        some { state := 14, tape := BuilderDividerLayout.leftFocus leftSide (separatorSymbol :: workspace) } := by rfl
    simpa only [rewindStart, hLeftSide] using h
  have hSafe : RewindSafe normalPrefix :=
    safe_append (safe_replicate view.sidecarCount)
      (safe_separator (safe_separator (safe_append (safe_replicate view.consumed)
        (safe_separator (safe_append (safe_replicate view.remainder)
          (safe_separator (safe_append (safe_replicate view.width)
            (safe_separator (safe_replicate view.quotient)))))))))
  have hBack : workRunExact? machine normalPrefix.length rewindStart = some rewindEnd :=
    rewind normalPrefix (tail.drop 2) (separatorSymbol :: workspace) hSafe
  have hBytes : normalPrefix.reverse ++ separatorSymbol :: workspace =
      (registerWord (restoredValues view)).reverse ++ workspace := by
    simp only [normalPrefix, restoredValues, registerWord,
      List.replicate_zero, List.nil_append, List.append_nil, List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append]
  have hFinish : workRunExact? machine 1 rewindEnd = some (finalConfiguration view workspace tail) := by
    change workRunExact? machine 1 rewindEnd =
      some {
        state := 15
        tape := {
          left := tail.drop 2
          head := scratchEndSymbol
          right := (registerWord (restoredValues view)).reverse ++ workspace
        }
      }
    rw [← hBytes]
    rfl
  have hShiftLength : shiftWord.length = view.remainder + view.width + view.quotient + 2 := by
    simp only [shiftWord, List.length_append, List.length_cons, List.length_replicate]
    omega
  have hLength : normalPrefix.length = view.sidecarCount + view.consumed +
      view.remainder + view.width + view.quotient + 5 := by
    simp only [normalPrefix, List.length_append, List.length_cons, List.length_replicate]
    omega
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ hLaunch hWidth
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h01 hToRemainder
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h02 hRemainder
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h03 hToShift
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h04 hShift
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h05 hEnd
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h06 hQuotient
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h07 hToWidth
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h08 hNormalWidth
  have h10 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h09 hToLocal
  have h11 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h10 hLocal
  have h12 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h11 hToConsumed
  have h13 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h12 hConsumed
  have h14 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h13 hBoundaries
  have h15 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h14 hSide
  have h16 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h15 hTurn
  have h17 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h16 hBack
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h17 hFinish
  have hCost : 1 + view.width + 1 + view.remainder + 1 + (shiftWord.length + 1) + 1 +
      view.quotient + 1 + view.width + 1 + view.remainder + 1 + view.consumed + 2 +
      view.sidecarCount + 1 + normalPrefix.length + 1 = workSteps view := by
    unfold workSteps
    rw [hShiftLength, hLength]
    omega
  rw [hCost] at hAll
  exact hAll

theorem run_compile_exact (view : RestoreView) (workspace tail : List WorkSymbol)
    (hFirst : tail.headD .blank = .blank)
    (hSecond : (tail.drop 1).headD .blank = .blank) :
    run (compileWorkMachine machine) (6 * workSteps view)
        (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact view workspace tail hFirst hSecond)

theorem finalConfiguration_state (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).state = machine.acceptState := rfl

theorem final_tape_layout (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape =
      { left := tail.drop 2, head := scratchEndSymbol,
        right := (registerWord (restoredValues view)).reverse ++ workspace } := rfl

theorem restored_remainder (view : RestoreView) :
    (restoredValues view)[3]? = some view.remainder := rfl

theorem restored_quotient (view : RestoreView) :
    (restoredValues view)[5]? = some view.quotient := rfl

/-- Every scan, shift, inserted delimiter and rewind is charged. -/
theorem workSteps_le (view : RestoreView) (bound : Nat)
    (hQuotient : view.quotient ≤ bound) (hWidth : view.width ≤ bound)
    (hRemainder : view.remainder ≤ bound) (hConsumed : view.consumed ≤ bound)
    (hSidecar : view.sidecarCount ≤ bound) :
    workSteps view ≤ 15 * bound + 19 := by
  unfold workSteps
  omega

end PNP.Concrete.CookLevin.BuilderDividerCoordinateRegisters
