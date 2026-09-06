/-
Copyright (c) 2026 PNP Labs.

Literal restoration of the comparator/divider scratch prefix to ordinary unary
registers. Preserve the computed quotient, original workspace and arbitrary
outer tape. Nineteen fixed rules normalize markers and delimiters; input values
do not generate control. Every scan and transition is charged.

Binding the restored register word to the source-derived clause-width copy and
the second division is a later layer. This is not the complete formula builder.
-/

import PNP.Concrete.CookLevinBuilderSourceClassifier

namespace PNP.Concrete.CookLevin.BuilderClassifierRegisterRestore

open PipelineTape PipelineStateNamespace BuilderUnaryPolynomial

abbrev boundaryMark : WorkSymbol := BuilderArbitrarySlotHeaderRouter.RawRouter.boundaryMark
abbrev quotientMark : WorkSymbol := BuilderArbitrarySlotHeaderRouter.RawRouter.coordinateMark
abbrev consumedMark : WorkSymbol := BuilderPostHeaderRawDivider.consumedDividend

private def rule (source target : Nat) (read write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source, readSymbol := read, targetState := target,
    writeSymbol := write, move := move }

def rules : List WorkRule :=
  [rule 0 0 unitSymbol unitSymbol .left,
   rule 0 1 scratchEndSymbol scratchEndSymbol .right,
   rule 1 1 unitSymbol unitSymbol .right,
   rule 1 1 boundaryMark unitSymbol .right,
   rule 1 2 separatorSymbol separatorSymbol .right,
   rule 2 2 unitSymbol unitSymbol .right,
   rule 2 2 quotientMark unitSymbol .right,
   rule 2 3 leftMarker separatorSymbol .right,
   rule 3 3 unitSymbol unitSymbol .right,
   rule 3 4 separatorSymbol separatorSymbol .right,
   rule 4 4 unitSymbol unitSymbol .right,
   rule 4 4 consumedMark unitSymbol .right,
   rule 4 5 leftMarker separatorSymbol .right,
   rule 5 6 leftMarker separatorSymbol .right,
   rule 6 6 unitSymbol unitSymbol .right,
   rule 6 7 scratchEndSymbol separatorSymbol .left,
   rule 7 7 unitSymbol unitSymbol .left,
   rule 7 7 separatorSymbol separatorSymbol .left,
   rule 7 8 scratchEndSymbol scratchEndSymbol .stay]

def machine : WorkMachine :=
  { rules := rules, startState := 0, acceptState := 8, rejectState := 9 }

private theorem startState_eq : machine.startState = 0 := rfl

theorem rules_length : rules.length = 19 := rfl

theorem rules_pairwise_query_distinct : rules.Pairwise WorkMachineChain.QueryDistinct := by
  unfold WorkMachineChain.QueryDistinct
  decide

theorem noRuleAtAccept : WorkMachineChain.NoRuleAtAccept machine := by
  intro selected hMem
  change selected.sourceState ≠ 8
  change selected ∈ rules at hMem
  decide +revert

theorem acceptState_ne_rejectState : machine.acceptState ≠ machine.rejectState := by decide

/-- A view of the existing tape, not a correctness certificate or machine input parameter. -/
structure RestoreView where
  countRest : Nat
  countMarked : Nat
  quotientRest : Nat
  quotientMarked : Nat
  consumed : Nat
  remainder : Nat
  width : Nat
  sidecarCount : Nat
  deriving DecidableEq, Repr

def RestoreView.countTotal (view : RestoreView) : Nat := view.countRest + view.countMarked

def RestoreView.quotientTotal (view : RestoreView) : Nat := view.quotientRest + view.quotientMarked

def RestoreView.dividend (view : RestoreView) : Nat := view.remainder + view.consumed

def restoredValues (view : RestoreView) : List Nat :=
  [view.sidecarCount, 0, view.dividend, view.width, view.quotientTotal, view.countTotal]

private def rightFocus (left word : List WorkSymbol) : WorkTape :=
  match word with
  | [] => { left := left, head := .blank, right := [] }
  | symbol :: rest => { left := left, head := symbol, right := rest }

def inputTape (view : RestoreView) (workspace tail : List WorkSymbol) : WorkTape :=
  let side := List.replicate view.sidecarCount unitSymbol ++ scratchEndSymbol :: workspace
  let divider := List.replicate view.width unitSymbol ++ separatorSymbol ::
    ((List.replicate view.remainder unitSymbol ++ List.replicate view.consumed consumedMark) ++
      leftMarker :: leftMarker :: side)
  let quotient := List.replicate view.quotientRest unitSymbol ++ List.replicate view.quotientMarked quotientMark
  BuilderDividerLayout.leftFocus (List.replicate view.countRest unitSymbol ++ scratchEndSymbol :: tail)
    (List.replicate view.countMarked boundaryMark ++ separatorSymbol :: (quotient ++ leftMarker :: divider))

def initialConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  workStartConfiguration machine (inputTape view workspace tail)

def finalConfiguration (view : RestoreView) (workspace tail : List WorkSymbol) : WorkConfiguration :=
  {
    state := machine.acceptState
    tape := BuilderDividerOperands.endTape (restoredValues view) workspace tail
  }

def workSteps (view : RestoreView) : Nat :=
  view.countRest + 2 * (view.countTotal + view.quotientTotal + view.width +
    view.dividend + view.sidecarCount) + 13

private def RightScanSymbol (state : Nat) (symbol : WorkSymbol) : Prop :=
  (state = 1 ∧ (symbol = unitSymbol ∨ symbol = boundaryMark)) ∨
  (state = 2 ∧ (symbol = unitSymbol ∨ symbol = quotientMark)) ∨
  (state = 3 ∧ symbol = unitSymbol) ∨
  (state = 4 ∧ (symbol = unitSymbol ∨ symbol = consumedMark)) ∨
  (state = 6 ∧ symbol = unitSymbol)

private theorem right_loop (state : Nat) (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : RightScanSymbol state symbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := rightFocus (unitSymbol :: left) right } := by
  rcases hSymbol with ⟨rfl, hSymbol⟩ | ⟨rfl, hSymbol⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hSymbol⟩ | ⟨rfl, rfl⟩
  · rcases hSymbol with rfl | rfl <;> rfl
  · rcases hSymbol with rfl | rfl <;> rfl
  · rfl
  · rcases hSymbol with rfl | rfl <;> rfl
  · rfl

private theorem scan_right_units (state : Nat) (word : List WorkSymbol) (stop : WorkSymbol)
    (remainder left : List WorkSymbol) (hSymbols : ∀ symbol ∈ word, RightScanSymbol state symbol) :
    workRunExact? machine word.length
      { state := state, tape := rightFocus left (word ++ stop :: remainder) } =
      some {
        state := state
        tape := { left := List.replicate word.length unitSymbol ++ left, head := stop, right := remainder }
      } := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
    have hRest : ∀ item ∈ rest, RightScanSymbol state item := by
      intro item hMem
      exact hSymbols item (List.mem_cons_of_mem symbol hMem)
    have hStep := right_loop state symbol left (rest ++ stop :: remainder) (hSymbols symbol List.mem_cons_self)
    simp only [List.length_cons, List.cons_append, rightFocus, workRunExact?]
    rw [hStep]
    simpa only [List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append] using ih (unitSymbol :: left) hRest

private theorem scan_right_pair (state firstCount secondCount : Nat)
    (firstSymbol secondSymbol stop : WorkSymbol) (remainder left : List WorkSymbol)
    (hFirst : RightScanSymbol state firstSymbol) (hSecond : RightScanSymbol state secondSymbol) :
    workRunExact? machine (firstCount + secondCount)
      {
        state := state
        tape := rightFocus left
          ((List.replicate firstCount firstSymbol ++ List.replicate secondCount secondSymbol) ++
            stop :: remainder)
      } =
      some {
        state := state
        tape := {
          left := List.replicate (firstCount + secondCount) unitSymbol ++ left
          head := stop
          right := remainder
        }
      } := by
  have h := scan_right_units state
    (List.replicate firstCount firstSymbol ++ List.replicate secondCount secondSymbol) stop remainder left (by
      intro symbol hMem
      rcases List.mem_append.mp hMem with hMem | hMem
      · have hEqual := List.eq_of_mem_replicate hMem
        subst symbol
        exact hFirst
      · have hEqual := List.eq_of_mem_replicate hMem
        subst symbol
        exact hSecond)
  simpa only [List.length_append, List.length_replicate] using h

private theorem scan_right_replicate (state count : Nat) (symbol stop : WorkSymbol)
    (remainder left : List WorkSymbol) (hSymbol : RightScanSymbol state symbol) :
    workRunExact? machine count
      { state := state, tape := rightFocus left (List.replicate count symbol ++ stop :: remainder) } =
      some {
        state := state
        tape := { left := List.replicate count unitSymbol ++ left, head := stop, right := remainder }
      } := by
  have h := scan_right_units state (List.replicate count symbol) stop remainder left (by
    intro item hMem
    have hEqual := List.eq_of_mem_replicate hMem
    subst item
    exact hSymbol)
  simpa only [List.length_replicate] using h

private def LeftScanSymbol (state : Nat) (symbol : WorkSymbol) : Prop :=
  (state = 0 ∧ symbol = unitSymbol) ∨
    (state = 7 ∧ (symbol = unitSymbol ∨ symbol = separatorSymbol))

private theorem left_loop (state : Nat) (symbol : WorkSymbol) (left right : List WorkSymbol)
    (hSymbol : LeftScanSymbol state symbol) :
    workStep? machine { state := state, tape := { left := left, head := symbol, right := right } } =
      some { state := state, tape := BuilderDividerLayout.leftFocus left (symbol :: right) } := by
  rcases hSymbol with ⟨rfl, rfl⟩ | ⟨rfl, hSymbol⟩
  · rfl
  · rcases hSymbol with rfl | rfl <;> rfl

private theorem scan_left (state : Nat) (word tail right : List WorkSymbol)
    (hSymbols : ∀ symbol ∈ word, LeftScanSymbol state symbol) :
    workRunExact? machine word.length
      { state := state, tape := BuilderDividerLayout.leftFocus (word ++ scratchEndSymbol :: tail) right } =
      some {
        state := state
        tape := { left := tail, head := scratchEndSymbol, right := word.reverse ++ right }
      } := by
  induction word generalizing right with
  | nil => rfl
  | cons symbol rest ih =>
    have hRest : ∀ item ∈ rest, LeftScanSymbol state item := by
      intro item hMem
      exact hSymbols item (List.mem_cons_of_mem symbol hMem)
    have hStep := left_loop state symbol (rest ++ scratchEndSymbol :: tail) right
      (hSymbols symbol List.mem_cons_self)
    simp only [List.length_cons, List.cons_append, BuilderDividerLayout.leftFocus, workRunExact?]
    rw [hStep]
    simpa only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append] using
      ih (symbol :: right) hRest

private def RewindSafe (word : List WorkSymbol) : Prop :=
  ∀ symbol ∈ word, symbol = unitSymbol ∨ symbol = separatorSymbol

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

theorem workRunExact (view : RestoreView) (workspace tail : List WorkSymbol) :
    workRunExact? machine (workSteps view) (initialConfiguration view workspace tail) =
      some (finalConfiguration view workspace tail) := by
  let c := view.countTotal
  let q := view.quotientTotal
  let i := view.dividend
  let sideWord := List.replicate view.sidecarCount unitSymbol ++ scratchEndSymbol :: workspace
  let indexWord := List.replicate view.remainder unitSymbol ++ List.replicate view.consumed consumedMark
  let divisorWord := List.replicate view.width unitSymbol ++ separatorSymbol ::
    (indexWord ++ leftMarker :: leftMarker :: sideWord)
  let quotientWord := List.replicate view.quotientRest unitSymbol ++ List.replicate view.quotientMarked quotientMark
  let startRight := List.replicate view.countMarked boundaryMark ++ separatorSymbol ::
    (quotientWord ++ leftMarker :: divisorWord)
  let countWord := List.replicate view.countRest unitSymbol ++ List.replicate view.countMarked boundaryMark
  let left0 := scratchEndSymbol :: tail
  let leftC := List.replicate c unitSymbol ++ left0
  let leftQ := List.replicate q unitSymbol ++ separatorSymbol :: leftC
  let leftW := List.replicate view.width unitSymbol ++ separatorSymbol :: leftQ
  let leftI := List.replicate i unitSymbol ++ separatorSymbol :: leftW
  let leftSide := List.replicate view.sidecarCount unitSymbol ++ separatorSymbol :: separatorSymbol :: leftI
  let normalPrefix := List.replicate view.sidecarCount unitSymbol ++ separatorSymbol :: separatorSymbol ::
    (List.replicate i unitSymbol ++ separatorSymbol ::
      (List.replicate view.width unitSymbol ++ separatorSymbol ::
        (List.replicate q unitSymbol ++ separatorSymbol :: List.replicate c unitSymbol)))
  let zeroEnd : WorkConfiguration :=
    {
      state := 0
      tape := {
        left := tail
        head := scratchEndSymbol
        right := List.replicate view.countRest unitSymbol ++ startRight
      }
    }
  let countStart : WorkConfiguration :=
    { state := 1, tape := rightFocus left0 (countWord ++ separatorSymbol :: (quotientWord ++ leftMarker :: divisorWord)) }
  let countEnd : WorkConfiguration :=
    { state := 1, tape := { left := leftC, head := separatorSymbol, right := quotientWord ++ leftMarker :: divisorWord } }
  let quotientStart : WorkConfiguration :=
    { state := 2, tape := rightFocus (separatorSymbol :: leftC) (quotientWord ++ leftMarker :: divisorWord) }
  let quotientEnd : WorkConfiguration :=
    { state := 2, tape := { left := leftQ, head := leftMarker, right := divisorWord } }
  let widthStart : WorkConfiguration :=
    { state := 3, tape := rightFocus (separatorSymbol :: leftQ) divisorWord }
  let widthEnd : WorkConfiguration :=
    { state := 3, tape := { left := leftW, head := separatorSymbol, right := indexWord ++ leftMarker :: leftMarker :: sideWord } }
  let indexStart : WorkConfiguration :=
    { state := 4, tape := rightFocus (separatorSymbol :: leftW) (indexWord ++ leftMarker :: leftMarker :: sideWord) }
  let indexEnd : WorkConfiguration :=
    { state := 4, tape := { left := leftI, head := leftMarker, right := leftMarker :: sideWord } }
  let sideStart : WorkConfiguration :=
    { state := 6, tape := rightFocus (separatorSymbol :: separatorSymbol :: leftI) sideWord }
  let sideEnd : WorkConfiguration :=
    { state := 6, tape := { left := leftSide, head := scratchEndSymbol, right := workspace } }
  let rewindStart : WorkConfiguration :=
    { state := 7, tape := BuilderDividerLayout.leftFocus (normalPrefix ++ scratchEndSymbol :: tail) (separatorSymbol :: workspace) }
  let rewindEnd : WorkConfiguration :=
    { state := 7, tape := { left := tail, head := scratchEndSymbol, right := normalPrefix.reverse ++ separatorSymbol :: workspace } }
  have hStart : workRunExact? machine view.countRest (initialConfiguration view workspace tail) = some zeroEnd := by
    have h := scan_left 0 (List.replicate view.countRest unitSymbol) tail startRight (by
      intro symbol hMem
      exact Or.inl ⟨rfl, List.eq_of_mem_replicate hMem⟩)
    simpa only [initialConfiguration, workStartConfiguration, startState_eq, inputTape, zeroEnd, startRight,
      quotientWord, divisorWord, indexWord, sideWord, List.length_replicate, List.reverse_replicate] using h
  have hLaunch : workRunExact? machine 1 zeroEnd = some countStart := by
    simp only [zeroEnd, countStart, countWord, startRight, left0, List.append_assoc]
    rfl
  have hCount : workRunExact? machine c countStart = some countEnd := by
    have h := scan_right_pair 1 view.countRest view.countMarked unitSymbol boundaryMark separatorSymbol
      (quotientWord ++ leftMarker :: divisorWord) left0
      (Or.inl ⟨rfl, Or.inl rfl⟩) (Or.inl ⟨rfl, Or.inr rfl⟩)
    simpa only [c, RestoreView.countTotal, countStart, countEnd, countWord, leftC] using h
  have hToQuotient : workRunExact? machine 1 countEnd = some quotientStart := by rfl
  have hQuotient : workRunExact? machine q quotientStart = some quotientEnd := by
    have h := scan_right_pair 2 view.quotientRest view.quotientMarked unitSymbol quotientMark leftMarker
      divisorWord (separatorSymbol :: leftC)
      (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)) (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
    simpa only [q, RestoreView.quotientTotal, quotientStart, quotientEnd, quotientWord, leftQ] using h
  have hToWidth : workRunExact? machine 1 quotientEnd = some widthStart := by rfl
  have hWidth : workRunExact? machine view.width widthStart = some widthEnd := by
    have h := scan_right_replicate 3 view.width unitSymbol separatorSymbol
      (indexWord ++ leftMarker :: leftMarker :: sideWord) (separatorSymbol :: leftQ)
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
    simpa only [widthStart, widthEnd, divisorWord, leftW] using h
  have hToIndex : workRunExact? machine 1 widthEnd = some indexStart := by rfl
  have hIndex : workRunExact? machine i indexStart = some indexEnd := by
    have h := scan_right_pair 4 view.remainder view.consumed unitSymbol consumedMark leftMarker
      (leftMarker :: sideWord) (separatorSymbol :: leftW)
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))))
    simpa only [i, RestoreView.dividend, indexStart, indexEnd, indexWord, leftI] using h
  have hBoundaries : workRunExact? machine 2 indexEnd = some sideStart := by rfl
  have hSide : workRunExact? machine view.sidecarCount sideStart = some sideEnd := by
    have h := scan_right_replicate 6 view.sidecarCount unitSymbol scratchEndSymbol
      workspace (separatorSymbol :: separatorSymbol :: leftI)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))))
    simpa only [sideStart, sideEnd, sideWord, leftSide] using h
  have hLeftSide : leftSide = normalPrefix ++ scratchEndSymbol :: tail := by
    simp only [leftSide, leftI, leftW, leftQ, leftC, left0, normalPrefix,
      List.append_assoc, List.cons_append]
  have hTurn : workRunExact? machine 1 sideEnd = some rewindStart := by
    have h : workRunExact? machine 1 sideEnd =
        some { state := 7, tape := BuilderDividerLayout.leftFocus leftSide (separatorSymbol :: workspace) } := by rfl
    simpa only [rewindStart, hLeftSide] using h
  have hSafe : RewindSafe normalPrefix :=
    safe_append (safe_replicate view.sidecarCount)
      (safe_separator (safe_separator (safe_append (safe_replicate i)
        (safe_separator (safe_append (safe_replicate view.width)
          (safe_separator (safe_append (safe_replicate q)
            (safe_separator (safe_replicate c)))))))))
  have hBack : workRunExact? machine normalPrefix.length rewindStart = some rewindEnd := by
    exact scan_left 7 normalPrefix tail (separatorSymbol :: workspace)
      (fun symbol hMem => Or.inr ⟨rfl, hSafe symbol hMem⟩)
  have hBytes : normalPrefix.reverse ++ separatorSymbol :: workspace =
      (registerWord (restoredValues view)).reverse ++ workspace := by
    simp only [normalPrefix, restoredValues, c, q, i, registerWord,
      List.replicate_zero, List.nil_append, List.append_nil, List.reverse_append,
      List.reverse_cons, List.reverse_replicate, List.append_assoc, List.cons_append]
  have hFinish : workRunExact? machine 1 rewindEnd = some (finalConfiguration view workspace tail) := by
    change workRunExact? machine 1 rewindEnd =
      some {
        state := 8
        tape := {
          left := tail
          head := scratchEndSymbol
          right := (registerWord (restoredValues view)).reverse ++ workspace
        }
      }
    rw [← hBytes]
    rfl
  have hLength : normalPrefix.length = view.sidecarCount + i + view.width + q + c + 5 := by
    simp only [normalPrefix, List.length_append, List.length_cons, List.length_replicate]
    omega
  have h01 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ hStart hLaunch
  have h02 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h01 hCount
  have h03 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h02 hToQuotient
  have h04 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h03 hQuotient
  have h05 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h04 hToWidth
  have h06 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h05 hWidth
  have h07 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h06 hToIndex
  have h08 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h07 hIndex
  have h09 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h08 hBoundaries
  have h10 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h09 hSide
  have h11 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h10 hTurn
  have h12 := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h11 hBack
  have hAll := PipelineMachineSimulation.workRunExact?_compose machine _ _ _ _ _ h12 hFinish
  have hCost : view.countRest + 1 + c + 1 + q + 1 + view.width + 1 + i + 2 +
      view.sidecarCount + 1 + normalPrefix.length + 1 = workSteps view := by
    unfold workSteps
    rw [hLength]
    dsimp only [c, q, i]
    omega
  rw [hCost] at hAll
  exact hAll

theorem run_compile_exact (view : RestoreView) (workspace tail : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps view)
        (encodeWorkConfiguration (initialConfiguration view workspace tail)) =
      encodeWorkConfiguration (finalConfiguration view workspace tail) :=
  run_compileWorkMachine_mul_of_workRunExact _ _ _ _ (workRunExact view workspace tail)

theorem finalConfiguration_state (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).state = machine.acceptState := rfl

theorem final_tape_layout (view : RestoreView) (workspace tail : List WorkSymbol) :
    (finalConfiguration view workspace tail).tape =
      {
        left := tail
        head := scratchEndSymbol
        right := (registerWord (restoredValues view)).reverse ++ workspace
      } := rfl

/-- All scans are linear in the five reconstructed register magnitudes. -/
theorem workSteps_le (view : RestoreView) (bound : Nat)
    (hCount : view.countTotal ≤ bound) (hQuotient : view.quotientTotal ≤ bound)
    (hWidth : view.width ≤ bound) (hDividend : view.dividend ≤ bound)
    (hSidecar : view.sidecarCount ≤ bound) :
    workSteps view ≤ 11 * bound + 13 := by
  have hRest : view.countRest ≤ view.countTotal := by
    unfold RestoreView.countTotal
    omega
  unfold workSteps
  omega

end PNP.Concrete.CookLevin.BuilderClassifierRegisterRestore
