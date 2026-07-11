/-
Copyright (c) 2026 PNP Labs.

Universal operational correctness of the literal CNF work machine.  This
module keeps the proof at the finite rule-list interpreter boundary: phase
invariants describe concrete work tapes, exact traces are composed, and only
then is the generic six-raw-steps compiler theorem applied.
-/

import PNP.Concrete.CNFWorkFrameCorrectness
import PNP.Concrete.CNFVerifier

namespace PNP.Concrete

/-! ### Constructive tape and exact-run infrastructure -/

namespace WorkTape

/-- A tape with its nearest-left cells given first, matching `WorkTape.left`. -/
def focus (leftSide : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol) : WorkTape :=
  { left := leftSide, head := head, right := suffix }

theorem focus_moveRight (leftSide : List WorkSymbol) (head next : WorkSymbol)
    (suffix : List WorkSymbol) :
    (focus leftSide head (next :: suffix)).moveRight =
      focus (head :: leftSide) next suffix := rfl

theorem focus_moveRight_blank (leftSide : List WorkSymbol)
    (head : WorkSymbol) :
    (focus leftSide head []).moveRight =
      focus (head :: leftSide) WorkSymbol.blank [] := rfl

theorem focus_write (leftSide : List WorkSymbol) (head write : WorkSymbol)
    (suffix : List WorkSymbol) :
    (focus leftSide head suffix).write write = focus leftSide write suffix := rfl

/-- Focus the first symbol of a finite right word, or the implicit blank when
the word is empty. -/
def atWord (leftSide : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => focus leftSide WorkSymbol.blank []
  | head :: suffix => focus leftSide head suffix

/-- Focus the first symbol encountered while scanning left.  The tail is
stored directly as the nearest-first left stack. -/
def atLeftWord (rightSide : List WorkSymbol) : List WorkSymbol → WorkTape
  | [] => focus [] WorkSymbol.blank rightSide
  | head :: leftTail => focus leftTail head rightSide

end WorkTape

/-- Configuration focused at the first symbol of a finite right word. -/
def workConfigAtWord (state : Nat) (leftSide word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := WorkTape.atWord leftSide word }

/-- Configuration focused at the first symbol of a nearest-first left word. -/
def workConfigAtLeftWord (state : Nat) (leftWord rightSide : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := WorkTape.atLeftWord rightSide leftWord }

/-- Push an ordinary left-to-right scanned word onto a nearest-first left
stack. -/
def pushWorkLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], leftSide => leftSide
  | symbol :: rest, leftSide => pushWorkLeft rest (symbol :: leftSide)

theorem pushWorkLeft_cons (symbol : WorkSymbol) (rest leftSide : List WorkSymbol) :
    pushWorkLeft (symbol :: rest) leftSide =
      pushWorkLeft rest (symbol :: leftSide) := rfl

/-- Generic exact right scan.  The premise is a literal interpreter step for
every allowed focused symbol; the theorem performs no semantic shortcut. -/
theorem workRunExact?_scanRight (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine (workConfigAtWord state leftSide (head :: suffix)) =
        some (workConfigAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtWord state leftSide (word ++ suffix)) =
      some (workConfigAtWord state (pushWorkLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (workConfigAtWord state leftSide (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

/-- Generic exact left scan, dual to `workRunExact?_scanRight`. -/
theorem workRunExact?_scanLeft (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (workConfigAtLeftWord state (head :: leftTail) rightSide) =
        some (workConfigAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord state leftSuffix
        (pushWorkLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (workConfigAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

/-! ### Constructive scan-accumulator algebra -/

theorem pushScannedWorkSymbols_append_far (word left right : List WorkSymbol) :
    pushScannedWorkSymbols word (left ++ right) =
      pushScannedWorkSymbols word left ++ right := by
  induction word generalizing left with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: left)

theorem pushScannedWorkSymbols_append_word
    (first second farSide : List WorkSymbol) :
    pushScannedWorkSymbols (first ++ second) farSide =
      pushScannedWorkSymbols second
        (pushScannedWorkSymbols first farSide) := by
  induction first generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

theorem pushScannedWorkSymbols_cons_far (word : List WorkSymbol)
    (symbol : WorkSymbol) :
    pushScannedWorkSymbols word [symbol] =
      pushScannedWorkSymbols word [] ++ [symbol] := by
  change pushScannedWorkSymbols word ([] ++ [symbol]) = _
  exact pushScannedWorkSymbols_append_far word [] [symbol]

/-- Scanning a word right and then scanning the accumulated nearest-first
word left restores the original left-to-right order exactly. -/
theorem pushScannedWorkSymbols_cancel (word farSide : List WorkSymbol) :
    pushScannedWorkSymbols (pushScannedWorkSymbols word []) farSide =
      word ++ farSide := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      change pushScannedWorkSymbols
          (pushScannedWorkSymbols rest [symbol]) farSide =
        symbol :: (rest ++ farSide)
      rw [pushScannedWorkSymbols_cons_far]
      rw [pushScannedWorkSymbols_append_word]
      change symbol ::
          pushScannedWorkSymbols (pushScannedWorkSymbols rest []) farSide = _
      exact congrArg (List.cons symbol) ih

theorem pushScannedWorkSymbols_cancel_with_left
    (word left farSide : List WorkSymbol) :
    pushScannedWorkSymbols
        (pushScannedWorkSymbols word left) farSide =
      pushScannedWorkSymbols left (word ++ farSide) := by
  have hInner := pushScannedWorkSymbols_append_far word [] left
  change pushScannedWorkSymbols word left =
      pushScannedWorkSymbols word [] ++ left at hInner
  rw [hInner]
  rw [pushScannedWorkSymbols_append_word]
  rw [pushScannedWorkSymbols_cancel]

theorem pushWorkLeft_eq_pushScannedWorkSymbols
    (word farSide : List WorkSymbol) :
    pushWorkLeft word farSide = pushScannedWorkSymbols word farSide := by
  induction word generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

theorem pushWorkLeft_cancel (word farSide : List WorkSymbol) :
    pushWorkLeft (pushWorkLeft word []) farSide = word ++ farSide := by
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  rw [pushScannedWorkSymbols_cancel]

/-- Crossing a word to the right boundary and moving left produces exactly
the nearest-first tape shape consumed by a left scan. -/
theorem beforeRightScan_moveLeft_to_beforeLeftScan
    (word leftSuffix : List WorkSymbol)
    (leftDelimiter rightDelimiter : WorkSymbol)
    (suffix : List WorkSymbol) :
    (WorkTape.beforeRightScan
        (pushScannedWorkSymbols word (leftDelimiter :: leftSuffix)) []
        rightDelimiter suffix).moveLeft =
      WorkTape.beforeLeftScan leftSuffix
        (pushScannedWorkSymbols word []) leftDelimiter
        (rightDelimiter :: suffix) := by
  have hSplit :
      pushScannedWorkSymbols word (leftDelimiter :: leftSuffix) =
        pushScannedWorkSymbols word [] ++ leftDelimiter :: leftSuffix :=
    pushScannedWorkSymbols_append_far word []
      (leftDelimiter :: leftSuffix)
  rw [hSplit]
  cases pushScannedWorkSymbols word [] <;> rfl

/-- The left half of a completed round trip cancels the right-scan
accumulator and restores the original left-to-right word. -/
theorem beforeLeftScan_roundTrip
    (word leftSuffix : List WorkSymbol)
    (leftDelimiter rightDelimiter : WorkSymbol)
    (suffix : List WorkSymbol) :
    WorkTape.beforeLeftScan leftSuffix [] leftDelimiter
        (pushScannedWorkSymbols (pushScannedWorkSymbols word [])
          (rightDelimiter :: suffix)) =
      WorkTape.beforeLeftScan leftSuffix [] leftDelimiter
        (word ++ rightDelimiter :: suffix) := by
  rw [pushScannedWorkSymbols_cancel]

/-- A right scan, one delimiter-triggered move left, and the matching left
scan restore the crossed word exactly.  The theorem records the literal
transition count and never appeals to list extensionality. -/
theorem workRunExact?_scanRoundTrip_keep
    (machine : WorkMachine) (rightState leftState : Nat)
    (word leftSuffix : List WorkSymbol)
    (leftDelimiter rightDelimiter : WorkSymbol)
    (suffix : List WorkSymbol)
    (hRightHalted : ∀ tape : WorkTape,
      machine.isHalted
        ({ state := rightState, tape := tape } : WorkConfiguration) = false)
    (hRightFind : ∀ symbol, List.Mem symbol word →
      findWorkRule machine.rules rightState symbol =
        some (cnfKeepRule rightState symbol rightState .right))
    (hBoundaryFind : findWorkRule machine.rules rightState rightDelimiter =
      some (cnfKeepRule rightState rightDelimiter leftState .left))
    (hLeftHalted : ∀ tape : WorkTape,
      machine.isHalted
        ({ state := leftState, tape := tape } : WorkConfiguration) = false)
    (hLeftFind : ∀ symbol,
      List.Mem symbol (pushScannedWorkSymbols word []) →
      findWorkRule machine.rules leftState symbol =
        some (cnfKeepRule leftState symbol leftState .left)) :
    workRunExact? machine
        ((word.length + 1) +
          (pushScannedWorkSymbols word []).length)
        { state := rightState
          tape := WorkTape.beforeRightScan
            (leftDelimiter :: leftSuffix) word rightDelimiter suffix } =
      some
        { state := leftState
          tape := WorkTape.beforeLeftScan leftSuffix [] leftDelimiter
            (word ++ rightDelimiter :: suffix) } := by
  have hRight := workRunExact?_scanRight_keep machine rightState
    (leftDelimiter :: leftSuffix) word rightDelimiter suffix
    hRightHalted hRightFind
  have hBoundaryRaw := workRunExact?_one_of_find machine
    { state := rightState
      tape := WorkTape.beforeRightScan
        (pushScannedWorkSymbols word (leftDelimiter :: leftSuffix)) []
        rightDelimiter suffix }
    (cnfKeepRule rightState rightDelimiter leftState .left)
    (hRightHalted _) hBoundaryFind
  have hBoundary :
      workRunExact? machine 1
          { state := rightState
            tape := WorkTape.beforeRightScan
              (pushScannedWorkSymbols word (leftDelimiter :: leftSuffix)) []
              rightDelimiter suffix } =
        some
          { state := leftState
            tape := WorkTape.beforeLeftScan leftSuffix
              (pushScannedWorkSymbols word []) leftDelimiter
              (rightDelimiter :: suffix) } := by
    change workRunExact? machine 1 _ = some
      { state := leftState
        tape := (WorkTape.beforeRightScan
          (pushScannedWorkSymbols word (leftDelimiter :: leftSuffix)) []
          rightDelimiter suffix).moveLeft } at hBoundaryRaw
    rw [beforeRightScan_moveLeft_to_beforeLeftScan] at hBoundaryRaw
    exact hBoundaryRaw
  have hLeftRaw := workRunExact?_scanLeft_keep machine leftState
    leftSuffix (pushScannedWorkSymbols word []) leftDelimiter
    (rightDelimiter :: suffix) hLeftHalted hLeftFind
  have hLeft :
      workRunExact? machine (pushScannedWorkSymbols word []).length
          { state := leftState
            tape := WorkTape.beforeLeftScan leftSuffix
              (pushScannedWorkSymbols word []) leftDelimiter
              (rightDelimiter :: suffix) } =
        some
          { state := leftState
            tape := WorkTape.beforeLeftScan leftSuffix [] leftDelimiter
              (word ++ rightDelimiter :: suffix) } := by
    rw [beforeLeftScan_roundTrip] at hLeftRaw
    exact hLeftRaw
  have hRightBoundary := workRunExact?_add_of_exact machine word.length 1
    _ _ _ hRight hBoundary
  exact workRunExact?_add_of_exact machine (word.length + 1)
    (pushScannedWorkSymbols word []).length _ _ _ hRightBoundary hLeft

theorem workRunExact?_compose (machine : WorkMachine)
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

theorem workRunExact?_one_of_step (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

theorem workStep?_eq_none_of_halted (machine : WorkMachine)
    (config : WorkConfiguration) (hHalted : machine.isHalted config = true) :
    workStep? machine config = none := by
  unfold workStep?
  exact if_pos hHalted

theorem workRun_eq_self_of_step?_none (machine : WorkMachine)
    (fuel : Nat) (config : WorkConfiguration)
    (hStep : workStep? machine config = none) :
    workRun machine fuel config = config := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      change (match workStep? machine config with
        | none => config
        | some next => workRun machine fuel next) = config
      rw [hStep]

theorem workRun_eq_self_of_halted (machine : WorkMachine)
    (fuel : Nat) (config : WorkConfiguration)
    (hHalted : machine.isHalted config = true) :
    workRun machine fuel config = config :=
  workRun_eq_self_of_step?_none machine fuel config
    (workStep?_eq_none_of_halted machine config hHalted)

theorem workRun_of_exact (machine : WorkMachine) (steps : Nat)
    (start final : WorkConfiguration)
    (hExact : workRunExact? machine steps start = some final) :
    workRun machine steps start = final := by
  induction steps generalizing start with
  | zero =>
      change some start = some final at hExact
      exact Option.some.inj hExact
  | succ steps ih =>
      cases hStep : workStep? machine start with
      | none =>
          change
            (match workStep? machine start with
             | none => none
             | some next => workRunExact? machine steps next) =
              some final at hExact
          rw [hStep] at hExact
          contradiction
      | some next =>
          have hTail : workRunExact? machine steps next = some final := by
            change
              (match workStep? machine start with
               | none => none
               | some next => workRunExact? machine steps next) =
                some final at hExact
            rw [hStep] at hExact
            exact hExact
          change (match workStep? machine start with
            | none => start
            | some next => workRun machine steps next) = final
          rw [hStep]
          exact ih next hTail

private theorem exists_add_of_le_constructive {smaller larger : Nat}
    (h : smaller ≤ larger) : ∃ extra, larger = smaller + extra := by
  induction larger generalizing smaller with
  | zero =>
      cases smaller with
      | zero => exact ⟨0, rfl⟩
      | succ smaller => cases h
  | succ larger ih =>
      cases smaller with
      | zero => exact ⟨larger + 1, (Nat.zero_add (larger + 1)).symm⟩
      | succ smaller =>
          have hTail : smaller ≤ larger := Nat.le_of_succ_le_succ h
          rcases ih hTail with ⟨extra, hExtra⟩
          refine ⟨extra, ?_⟩
          rw [Nat.succ_add]
          exact congrArg Nat.succ hExtra

theorem workRun_pad_exact_halted (machine : WorkMachine)
    (steps fuel : Nat) (start final : WorkConfiguration)
    (hExact : workRunExact? machine steps start = some final)
    (hHalted : machine.isHalted final = true)
    (hBound : steps ≤ fuel) :
    workRun machine fuel start = final := by
  rcases exists_add_of_le_constructive hBound with ⟨extra, hFuel⟩
  rw [hFuel, workRun_add]
  rw [workRun_of_exact machine steps start final hExact]
  exact workRun_eq_self_of_halted machine extra final hHalted

/-! ### Symbol classes used by the phase invariants -/

inductive FormulaScanSymbol : WorkSymbol → Prop where
  | markTrue : FormulaScanSymbol cnfMarkTrue
  | f : FormulaScanSymbol cnfF
  | t : FormulaScanSymbol cnfT
  | sep : FormulaScanSymbol cnfSep
  | finish : FormulaScanSymbol cnfFinish

inductive AssignmentMarkSymbol : WorkSymbol → Prop where
  | markFalse : AssignmentMarkSymbol cnfMarkFalse
  | markTrue : AssignmentMarkSymbol cnfMarkTrue

inductive FormulaOrCounterSymbol : WorkSymbol → Prop where
  | markFalse : FormulaOrCounterSymbol cnfMarkFalse
  | markTrue : FormulaOrCounterSymbol cnfMarkTrue
  | f : FormulaOrCounterSymbol cnfF
  | t : FormulaOrCounterSymbol cnfT
  | sep : FormulaOrCounterSymbol cnfSep
  | finish : FormulaOrCounterSymbol cnfFinish

/-- Indexed classification of the complete nine-symbol work alphabet. -/
inductive CNFWorkSymbolCase : WorkSymbol → Prop where
  | blank : CNFWorkSymbolCase cnfBlank
  | markFalse : CNFWorkSymbolCase cnfMarkFalse
  | markTrue : CNFWorkSymbolCase cnfMarkTrue
  | rootGuard : CNFWorkSymbolCase cnfRootGuard
  | f : CNFWorkSymbolCase cnfF
  | sep : CNFWorkSymbolCase cnfSep
  | boundaryGuard : CNFWorkSymbolCase cnfBoundaryGuard
  | finish : CNFWorkSymbolCase cnfFinish
  | t : CNFWorkSymbolCase cnfT

theorem cnfWorkSymbolCase (symbol : WorkSymbol) :
    CNFWorkSymbolCase symbol := by
  cases symbol with
  | mk first second =>
      cases first <;> cases second
      · exact .blank
      · exact .markFalse
      · exact .markTrue
      · exact .rootGuard
      · exact .f
      · exact .sep
      · exact .boundaryGuard
      · exact .finish
      · exact .t

/- The following small indexed whitelists are the grammar contracts of the
states that make semantic choices.  Symbols outside a whitelist take the
explicit reject rule from that state's complete suffix. -/

inductive BootSymbol : WorkSymbol → Prop where
  | t : BootSymbol cnfT

inductive BlankSymbol : WorkSymbol → Prop where
  | blank : BlankSymbol cnfBlank

inductive RootGuardSymbol : WorkSymbol → Prop where
  | rootGuard : RootGuardSymbol cnfRootGuard

inductive WidthHeaderSymbol : WorkSymbol → Prop where
  | markTrue : WidthHeaderSymbol cnfMarkTrue
  | f : WidthHeaderSymbol cnfF
  | t : WidthHeaderSymbol cnfT

inductive WidthDoneAssignmentSymbol : WorkSymbol → Prop where
  | markFalse : WidthDoneAssignmentSymbol cnfMarkFalse
  | markTrue : WidthDoneAssignmentSymbol cnfMarkTrue
  | rootGuard : WidthDoneAssignmentSymbol cnfRootGuard

inductive WidthRestoreFormulaSymbol : WorkSymbol → Prop where
  | markTrue : WidthRestoreFormulaSymbol cnfMarkTrue
  | f : WidthRestoreFormulaSymbol cnfF

inductive ClauseStartSymbol : WorkSymbol → Prop where
  | sep : ClauseStartSymbol cnfSep
  | finish : ClauseStartSymbol cnfFinish

inductive LiteralSignSymbol : WorkSymbol → Prop where
  | f : LiteralSignSymbol cnfF
  | t : LiteralSignSymbol cnfT

inductive SatisfiedClauseSymbol : WorkSymbol → Prop where
  | f : SatisfiedClauseSymbol cnfF
  | finish : SatisfiedClauseSymbol cnfFinish
  | t : SatisfiedClauseSymbol cnfT

inductive BoundarySymbol : WorkSymbol → Prop where
  | boundaryGuard : BoundarySymbol cnfBoundaryGuard

inductive AssignmentSearchSymbol : WorkSymbol → Prop where
  | markFalse : AssignmentSearchSymbol cnfMarkFalse
  | markTrue : AssignmentSearchSymbol cnfMarkTrue
  | rootGuard : AssignmentSearchSymbol cnfRootGuard
  | f : AssignmentSearchSymbol cnfF
  | t : AssignmentSearchSymbol cnfT

inductive RestoreIndexSymbol : WorkSymbol → Prop where
  | markTrue : RestoreIndexSymbol cnfMarkTrue
  | f : RestoreIndexSymbol cnfF
  | t : RestoreIndexSymbol cnfT

inductive FrameOneCheckSymbol : WorkSymbol → Prop where
  | markFalse : FrameOneCheckSymbol cnfMarkFalse
  | markTrue : FrameOneCheckSymbol cnfMarkTrue
  | rootGuard : FrameOneCheckSymbol cnfRootGuard
  | sep : FrameOneCheckSymbol cnfSep
  | boundaryGuard : FrameOneCheckSymbol cnfBoundaryGuard

inductive FrameTwoCheckSymbol : WorkSymbol → Prop where
  | markFalse : FrameTwoCheckSymbol cnfMarkFalse
  | markTrue : FrameTwoCheckSymbol cnfMarkTrue
  | finish : FrameTwoCheckSymbol cnfFinish

/-- Once lookup has selected the complete-suffix reject rule, the exact
interpreter reaches the unchanged tape in the halted reject state in one
transition. -/
theorem cnfReject_run_one (state : Nat) (tape : WorkTape)
    (notHalted : cnfWorkMachine.isHalted
      ({ state := state, tape := tape } : WorkConfiguration) = false)
    (selected : findWorkRule cnfWorkRules state tape.head =
      some (cnfRejectRule state tape.head)) :
    workRunExact? cnfWorkMachine 1
        ({ state := state, tape := tape } : WorkConfiguration) =
      some
        ({ state := CNFWorkState.reject, tape := tape } :
          WorkConfiguration) := by
  have hSelected := workRunExact?_one_of_find cnfWorkMachine
    ({ state := state, tape := tape } : WorkConfiguration)
    (cnfRejectRule state tape.head) notHalted selected
  exact hSelected

/-! ### Exact malformed frame and width branches -/

set_option maxRecDepth 100000 in
theorem boot_reject_run (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ BootSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.boot
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.boot _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem bootLeft_reject_run (left right : List WorkSymbol)
    (symbol : WorkSymbol) (invalid : ¬ BlankSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.bootLeft
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.bootLeft _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => exact False.elim (invalid .blank)
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem frameOneCheckPayload_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ FrameOneCheckSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameOneCheckPayload
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.frameOneCheckPayload _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => exact False.elim (invalid .markFalse)
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => exact False.elim (invalid .rootGuard)
  | f => rfl
  | sep => exact False.elim (invalid .sep)
  | boundaryGuard => exact False.elim (invalid .boundaryGuard)
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem frameTwoCheckPayload_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ FrameTwoCheckSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameTwoCheckPayload
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.frameTwoCheckPayload _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => exact False.elim (invalid .markFalse)
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => rfl
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => exact False.elim (invalid .finish)
  | t => rfl

set_option maxRecDepth 100000 in
theorem frameTwoEnsureBlank_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ BlankSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameTwoEnsureBlank
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.frameTwoEnsureBlank _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => exact False.elim (invalid .blank)
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem frameTwoAtRightGuard_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ RootGuardSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameTwoAtRightGuard
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.frameTwoAtRightGuard _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => exact False.elim (invalid .rootGuard)
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem widthFindFormula_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ WidthHeaderSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthFindFormula
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.widthFindFormula _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => rfl
  | f => exact False.elim (invalid .f)
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem widthDoneCheckAssignment_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ WidthDoneAssignmentSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthDoneCheckAssignment
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.widthDoneCheckAssignment _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => exact False.elim (invalid .markFalse)
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => exact False.elim (invalid .rootGuard)
  | f => rfl
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem widthRestoreFormula_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ WidthRestoreFormulaSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthRestoreFormula
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.widthRestoreFormula _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => rfl
  | f => exact False.elim (invalid .f)
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => rfl

/-! ### Exact strict formula-grammar reject branches -/

set_option maxRecDepth 100000 in
theorem clauseStart_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ ClauseStartSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseStart
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.clauseStart _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => rfl
  | sep => exact False.elim (invalid .sep)
  | boundaryGuard => rfl
  | finish => exact False.elim (invalid .finish)
  | t => rfl

set_option maxRecDepth 100000 in
theorem clauseNeedLiteral_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ LiteralSignSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseNeedLiteral
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.clauseNeedLiteral _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => exact False.elim (invalid .f)
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem clauseContinueFalse_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ LiteralSignSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseContinue false
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one (CNFWorkState.clauseContinue false) _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => exact False.elim (invalid .f)
  | sep => rfl
  | boundaryGuard => rfl
  | finish => rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem clauseContinueTrue_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ SatisfiedClauseSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseContinue true
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one (CNFWorkState.clauseContinue true) _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => exact False.elim (invalid .f)
  | sep => rfl
  | boundaryGuard => rfl
  | finish => exact False.elim (invalid .finish)
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem finalCheck_reject_run
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ BoundarySymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.finalCheck
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one CNFWorkState.finalCheck _ (by rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => rfl
  | markFalse => rfl
  | markTrue => rfl
  | rootGuard => rfl
  | f => rfl
  | sep => rfl
  | boundaryGuard => exact False.elim (invalid .boundaryGuard)
  | finish => rfl
  | t => rfl

set_option maxRecDepth 100000 in
theorem literalIndex_reject_run (alreadySatisfied positive : Bool)
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ LiteralSignSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalIndex alreadySatisfied positive
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one
    (CNFWorkState.literalIndex alreadySatisfied positive) _
    (by cases alreadySatisfied <;> cases positive <;> rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => cases alreadySatisfied <;> cases positive <;> rfl
  | markFalse => cases alreadySatisfied <;> cases positive <;> rfl
  | markTrue => cases alreadySatisfied <;> cases positive <;> rfl
  | rootGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | f => exact False.elim (invalid .f)
  | sep => cases alreadySatisfied <;> cases positive <;> rfl
  | boundaryGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | finish => cases alreadySatisfied <;> cases positive <;> rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem literalMarkAssignment_reject_run
    (alreadySatisfied positive : Bool)
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ AssignmentSearchSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalMarkAssignment alreadySatisfied positive
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one
    (CNFWorkState.literalMarkAssignment alreadySatisfied positive) _
    (by cases alreadySatisfied <;> cases positive <;> rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => cases alreadySatisfied <;> cases positive <;> rfl
  | markFalse => exact False.elim (invalid .markFalse)
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => exact False.elim (invalid .rootGuard)
  | f => exact False.elim (invalid .f)
  | sep => cases alreadySatisfied <;> cases positive <;> rfl
  | boundaryGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | finish => cases alreadySatisfied <;> cases positive <;> rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem literalLookupAssignment_reject_run
    (alreadySatisfied positive : Bool)
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ AssignmentSearchSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalLookupAssignment
            alreadySatisfied positive
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one
    (CNFWorkState.literalLookupAssignment alreadySatisfied positive) _
    (by cases alreadySatisfied <;> cases positive <;> rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => cases alreadySatisfied <;> cases positive <;> rfl
  | markFalse => exact False.elim (invalid .markFalse)
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => exact False.elim (invalid .rootGuard)
  | f => exact False.elim (invalid .f)
  | sep => cases alreadySatisfied <;> cases positive <;> rfl
  | boundaryGuard => cases alreadySatisfied <;> cases positive <;> rfl
  | finish => cases alreadySatisfied <;> cases positive <;> rfl
  | t => exact False.elim (invalid .t)

set_option maxRecDepth 100000 in
theorem literalRestoreIndex_reject_run (result positive : Bool)
    (left right : List WorkSymbol) (symbol : WorkSymbol)
    (invalid : ¬ RestoreIndexSymbol symbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalRestoreIndex result positive
          tape := WorkTape.focus left symbol right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left symbol right } := by
  apply cnfReject_run_one
    (CNFWorkState.literalRestoreIndex result positive) _
    (by cases result <;> cases positive <;> rfl)
  cases cnfWorkSymbolCase symbol with
  | blank => cases result <;> cases positive <;> rfl
  | markFalse => cases result <;> cases positive <;> rfl
  | markTrue => exact False.elim (invalid .markTrue)
  | rootGuard => cases result <;> cases positive <;> rfl
  | f => exact False.elim (invalid .f)
  | sep => cases result <;> cases positive <;> rfl
  | boundaryGuard => cases result <;> cases positive <;> rfl
  | finish => cases result <;> cases positive <;> rfl
  | t => exact False.elim (invalid .t)

/- Named terminal corollaries make the strict decoder failure modes visible
without asking later semantic inductions to unfold a whitelist proof. -/

theorem frameOne_missingSeparator_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameOneCheckPayload
          tape := WorkTape.focus left cnfFinish right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfFinish right } :=
  frameOneCheckPayload_reject_run left right cnfFinish (by
    intro allowed
    cases allowed)

theorem frameTwo_falseTerminal_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameTwoCheckPayload
          tape := WorkTape.focus left cnfF right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfF right } :=
  frameTwoCheckPayload_reject_run left right cnfF (by
    intro allowed
    cases allowed)

theorem frameTwo_trueTerminal_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.frameTwoCheckPayload
          tape := WorkTape.focus left cnfT right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfT right } :=
  frameTwoCheckPayload_reject_run left right cnfT (by
    intro allowed
    cases allowed)

theorem width_missingHeaderTerminator_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthFindFormula
          tape := WorkTape.focus left cnfFinish right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfFinish right } :=
  widthFindFormula_reject_run left right cnfFinish (by
    intro allowed
    cases allowed)

theorem width_extraFalseAssignment_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthDoneCheckAssignment
          tape := WorkTape.focus left cnfF right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfF right } :=
  widthDoneCheckAssignment_reject_run left right cnfF (by
    intro allowed
    cases allowed)

theorem width_extraTrueAssignment_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.widthDoneCheckAssignment
          tape := WorkTape.focus left cnfT right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfT right } :=
  widthDoneCheckAssignment_reject_run left right cnfT (by
    intro allowed
    cases allowed)

theorem emptyClause_reject_run (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseNeedLiteral
          tape := WorkTape.focus left cnfFinish right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfFinish right } :=
  clauseNeedLiteral_reject_run left right cnfFinish (by
    intro allowed
    cases allowed)

theorem unsatisfiedClauseFinish_reject_run
    (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.clauseContinue false
          tape := WorkTape.focus left cnfFinish right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfFinish right } :=
  clauseContinueFalse_reject_run left right cnfFinish (by
    intro allowed
    cases allowed)

theorem literal_missingIndex_reject_run
    (alreadySatisfied positive : Bool) (left right : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        { state := CNFWorkState.literalIndex alreadySatisfied positive
          tape := WorkTape.focus left cnfFinish right } =
      some
        { state := CNFWorkState.reject
          tape := WorkTape.focus left cnfFinish right } :=
  literalIndex_reject_run alreadySatisfied positive left right cnfFinish (by
    intro allowed
    cases allowed)

theorem cnfTokenWorkSymbol_formulaScan (token : CNFToken) :
    FormulaScanSymbol token.workSymbol := by
  cases token with
  | f => exact .f
  | t => exact .t
  | sep => exact .sep
  | finish => exact .finish

theorem cnfTokenWorkSymbols_formulaScan (tokens : List CNFToken)
    (symbol : WorkSymbol) (found : List.Mem symbol (cnfTokenWorkSymbols tokens)) :
    FormulaScanSymbol symbol := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases found with
      | head => exact cnfTokenWorkSymbol_formulaScan token
      | tail _ tailFound => exact ih tailFound

/-- Marked assignment values preserve enough information for exact restore. -/
def markedAssignmentWorkSymbols : BitString → List WorkSymbol
  | [] => []
  | false :: rest => cnfMarkFalse :: markedAssignmentWorkSymbols rest
  | true :: rest => cnfMarkTrue :: markedAssignmentWorkSymbols rest

def assignmentWorkSymbols : BitString → List WorkSymbol
  | [] => []
  | false :: rest => cnfF :: assignmentWorkSymbols rest
  | true :: rest => cnfT :: assignmentWorkSymbols rest

theorem assignmentValueTokens_workSymbols (assignment : BitString) :
    cnfTokenWorkSymbols (assignmentValueTokens assignment) =
      assignmentWorkSymbols assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact congrArg (List.cons _) ih

theorem markedAssignmentWorkSymbols_allowed (assignment : BitString)
    (symbol : WorkSymbol)
    (found : List.Mem symbol (markedAssignmentWorkSymbols assignment)) :
    AssignmentMarkSymbol symbol := by
  induction assignment with
  | nil => contradiction
  | cons value rest ih =>
      cases value with
      | false =>
          cases found with
          | head => exact .markFalse
          | tail _ tailFound => exact ih tailFound
      | true =>
          cases found with
          | head => exact .markTrue
          | tail _ tailFound => exact ih tailFound

theorem assignmentWorkSymbols_length (assignment : BitString) :
    (assignmentWorkSymbols assignment).length = assignment.length := by
  induction assignment with
  | nil => rfl
  | cons value rest ih => cases value <;> exact congrArg Nat.succ ih

theorem markedAssignmentWorkSymbols_length (assignment : BitString) :
    (markedAssignmentWorkSymbols assignment).length = assignment.length := by
  induction assignment with
  | nil => rfl
  | cons value rest ih => cases value <;> exact congrArg Nat.succ ih

/-! ### Strict codec canonicality used by the all-pairs split -/

theorem encodeTokenPairs_of_decode (bits : BitString) (tokens : List CNFToken)
    (decoded : decodeTokenPairs bits = some tokens) :
    encodeTokenPairs tokens = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil => rfl
      | cons first tail =>
          cases tail with
          | nil => contradiction
          | cons second rest =>
              change (match decodeTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) = some []
                  at decoded
              cases hRest : decodeTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have impossible : CNFToken.ofBits first second :: suffix = [] :=
                    Option.some.inj decoded
                  cases impossible
  | cons token tokens ih =>
      cases bits with
      | nil =>
          change some [] = some (token :: tokens) at decoded
          have impossible : [] = token :: tokens := Option.some.inj decoded
          cases impossible
      | cons first tail =>
          cases tail with
          | nil => contradiction
          | cons second rest =>
              change (match decodeTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) =
                  some (token :: tokens) at decoded
              cases hRest : decodeTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have hCons : CNFToken.ofBits first second :: suffix =
                      token :: tokens := Option.some.inj decoded
                  have hToken : CNFToken.ofBits first second = token :=
                    List.cons.inj hCons |>.1
                  have hSuffix : suffix = tokens := List.cons.inj hCons |>.2
                  cases hSuffix
                  have hTail := ih rest hRest
                  cases first <;> cases second <;> cases hToken <;>
                    exact congrArg (List.cons _ ∘ List.cons _) hTail

theorem encodeFormulaTokenPairs_of_decode (bits : BitString)
    (tokens : List CNFToken)
    (decoded : decodeFormulaTokenPairs bits = some tokens) :
    encodeTokenPairs tokens ++ [false] = bits := by
  induction tokens generalizing bits with
  | nil =>
      cases bits with
      | nil => contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false => rfl
              | true => contradiction
          | cons second rest =>
              change (match decodeFormulaTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) = some []
                  at decoded
              cases hRest : decodeFormulaTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have impossible : CNFToken.ofBits first second :: suffix = [] :=
                    Option.some.inj decoded
                  cases impossible
  | cons token tokens ih =>
      cases bits with
      | nil => contradiction
      | cons first tail =>
          cases tail with
          | nil =>
              cases first with
              | false =>
                  change some [] = some (token :: tokens) at decoded
                  have impossible : [] = token :: tokens :=
                    Option.some.inj decoded
                  cases impossible
              | true => contradiction
          | cons second rest =>
              change (match decodeFormulaTokenPairs rest with
                | none => none
                | some suffix =>
                    some (CNFToken.ofBits first second :: suffix)) =
                  some (token :: tokens) at decoded
              cases hRest : decodeFormulaTokenPairs rest with
              | none => rw [hRest] at decoded; contradiction
              | some suffix =>
                  rw [hRest] at decoded
                  have hCons : CNFToken.ofBits first second :: suffix =
                      token :: tokens := Option.some.inj decoded
                  have hToken : CNFToken.ofBits first second = token :=
                    List.cons.inj hCons |>.1
                  have hSuffix : suffix = tokens := List.cons.inj hCons |>.2
                  cases hSuffix
                  have hTail := ih rest hRest
                  cases first <;> cases second <;> cases hToken <;>
                    exact congrArg (List.cons _ ∘ List.cons _) hTail

theorem encodeAssignmentCertificate_of_decode (certificate : BitString)
    (assignment : BitString)
    (decoded : decodeAssignmentCertificate certificate = some assignment) :
    encodeAssignmentCertificate assignment = certificate := by
  unfold decodeAssignmentCertificate at decoded
  cases hTokens : decodeTokenPairs certificate with
  | none => rw [hTokens] at decoded; contradiction
  | some tokens =>
      rw [hTokens] at decoded
      unfold encodeAssignmentCertificate
      rw [encodeAssignmentTokens_of_decode tokens assignment decoded]
      exact encodeTokenPairs_of_decode certificate tokens hTokens

theorem list_nil_or_snoc_constructive {alpha : Type} (items : List alpha) :
    items = [] ∨ ∃ front last, items = front ++ [last] := by
  induction items with
  | nil => exact Or.inl rfl
  | cons head tail ih =>
      cases ih with
      | inl empty =>
          cases empty
          exact Or.inr ⟨[], head, rfl⟩
      | inr snoc =>
          rcases snoc with ⟨front, last, shape⟩
          cases shape
          exact Or.inr ⟨head :: front, last, rfl⟩

private theorem listTwoStepInduction {alpha : Type}
    (Property : List alpha → Prop)
    (empty : Property [])
    (singleton : ∀ first, Property [first])
    (pair : ∀ first second rest,
      Property rest → Property (first :: second :: rest))
    (items : List alpha) : Property items := by
  have both : Property items ∧ ∀ first, Property (first :: items) := by
    induction items with
    | nil => exact ⟨empty, singleton⟩
    | cons head tail ih =>
        refine ⟨ih.2 head, ?_⟩
        intro first
        exact pair first head tail ih.1
  exact both.1

/-- A failed ordinary pair decoder has exactly one unpaired final bit. -/
theorem decodeTokenPairs_none_shape (bits : BitString)
    (decoded : decodeTokenPairs bits = none) :
    ∃ tokens last, bits = encodeTokenPairs tokens ++ [last] := by
  revert decoded
  apply listTwoStepInduction (Property := fun current =>
    decodeTokenPairs current = none →
      ∃ tokens last, current = encodeTokenPairs tokens ++ [last])
  · intro decoded
    contradiction
  · intro first decoded
    exact ⟨[], first, rfl⟩
  · intro first second rest ih decoded
    change (match decodeTokenPairs rest with
      | none => none
      | some suffix => some (CNFToken.ofBits first second :: suffix)) = none
      at decoded
    cases hRest : decodeTokenPairs rest with
    | some suffix =>
        rw [hRest] at decoded
        contradiction
    | none =>
        rcases ih hRest with ⟨tokens, last, shape⟩
        refine ⟨CNFToken.ofBits first second :: tokens, last, ?_⟩
        rw [shape]
        cases first <;> cases second <;> rfl

/-- A failed formula-pair decoder is either an even token stream with no pad
or a token stream followed by the wrong final pad bit. -/
theorem decodeFormulaTokenPairs_none_shape (bits : BitString)
    (decoded : decodeFormulaTokenPairs bits = none) :
    ∃ tokens,
      bits = encodeTokenPairs tokens ∨
      bits = encodeTokenPairs tokens ++ [true] := by
  revert decoded
  apply listTwoStepInduction (Property := fun current =>
    decodeFormulaTokenPairs current = none →
      ∃ tokens,
        current = encodeTokenPairs tokens ∨
        current = encodeTokenPairs tokens ++ [true])
  · intro decoded
    exact ⟨[], Or.inl rfl⟩
  · intro first decoded
    cases first with
    | false => contradiction
    | true => exact ⟨[], Or.inr rfl⟩
  · intro first second rest ih decoded
    change (match decodeFormulaTokenPairs rest with
      | none => none
      | some suffix => some (CNFToken.ofBits first second :: suffix)) = none
      at decoded
    cases hRest : decodeFormulaTokenPairs rest with
    | some suffix =>
        rw [hRest] at decoded
        contradiction
    | none =>
        rcases ih hRest with ⟨tokens, shape⟩
        refine ⟨CNFToken.ofBits first second :: tokens, ?_⟩
        cases shape with
        | inl evenShape =>
            left
            rw [evenShape]
            cases first <;> cases second <;> rfl
        | inr badPadShape =>
            right
            rw [badPadShape]
            cases first <;> cases second <;> rfl

/-- A failed whole-formula parse separates raw framing failure from strict
token-grammar failure. -/
theorem decodeEncodedCNF_none_cases (bits : BitString)
    (decoded : decodeEncodedCNF bits = none) :
    (∃ tokens,
      bits = encodeTokenPairs tokens ∨
      bits = encodeTokenPairs tokens ++ [true]) ∨
    ∃ tokens,
      decodeFormulaTokenPairs bits = some tokens ∧
      decodeCNFTokens tokens = none := by
  unfold decodeEncodedCNF at decoded
  cases hTokens : decodeFormulaTokenPairs bits with
  | none =>
      exact Or.inl (decodeFormulaTokenPairs_none_shape bits hTokens)
  | some tokens =>
      rw [hTokens] at decoded
      exact Or.inr ⟨tokens, rfl, decoded⟩

/-- A failed whole-certificate parse separates the dangling raw bit case
from failure of the strict assignment-token grammar. -/
theorem decodeAssignmentCertificate_none_cases (certificate : BitString)
    (decoded : decodeAssignmentCertificate certificate = none) :
    (∃ tokens last,
      certificate = encodeTokenPairs tokens ++ [last]) ∨
    ∃ tokens,
      decodeTokenPairs certificate = some tokens ∧
      decodeAssignmentTokens tokens = none := by
  unfold decodeAssignmentCertificate at decoded
  cases hTokens : decodeTokenPairs certificate with
  | none =>
      exact Or.inl (decodeTokenPairs_none_shape certificate hTokens)
  | some tokens =>
      rw [hTokens] at decoded
      exact Or.inr ⟨tokens, rfl, decoded⟩

/- The strict formula grammar is injective on every successful parse.  A
single structural induction carries the four parser states together because
each recursive call consumes the focused token. -/
private theorem decodeFormulaGrammar_inverse (tokens : List CNFToken) :
    (∀ start formula,
      decodeFormulaHeader start tokens = some formula →
      ∃ count,
        formula.variableCount = start + count ∧
        tokens = encodeUnaryTokens count ++
          (encodeClauseListTokens formula.clauses ++ [.finish])) ∧
    (∀ clauses,
      decodeFormulaClauses tokens = some clauses →
      tokens = encodeClauseListTokens clauses ++ [.finish]) ∧
    (∀ clause clauses,
      decodeFormulaClause tokens = some (clause, clauses) →
      tokens = encodeLiteralListTokens clause ++
        (.finish :: (encodeClauseListTokens clauses ++ [.finish]))) ∧
    (∀ positive start clause clauses,
      decodeFormulaLiteral positive start tokens = some (clause, clauses) →
      ∃ count tail,
        clause =
          ({ positive := positive, variableIndex := start + count } :
            CNFLiteral) :: tail ∧
        tokens = encodeUnaryTokens count ++
          (encodeLiteralListTokens tail ++
            (.finish :: (encodeClauseListTokens clauses ++ [.finish])))) := by
  induction tokens with
  | nil =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro start formula decoded
        contradiction
      · intro clauses decoded
        contradiction
      · intro clause clauses decoded
        contradiction
      · intro positive start clause clauses decoded
        contradiction
  | cons token rest ih =>
      rcases ih with ⟨headerIH, clausesIH, clauseIH, literalIH⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro start formula decoded
        cases token with
        | f =>
            change (match decodeFormulaClauses rest with
              | none => none
              | some clauses => some
                  ({ variableCount := start, clauses := clauses } : CNFFormula)) =
                some formula at decoded
            cases hRest : decodeFormulaClauses rest with
            | none =>
                rw [hRest] at decoded
                contradiction
            | some clauses =>
                rw [hRest] at decoded
                have hFormula :
                    ({ variableCount := start, clauses := clauses } : CNFFormula) =
                      formula := Option.some.inj decoded
                cases hFormula
                have hShape := clausesIH clauses hRest
                refine ⟨0, rfl, ?_⟩
                exact congrArg (List.cons CNFToken.f) hShape
        | t =>
            change decodeFormulaHeader (start + 1) rest = some formula at decoded
            rcases headerIH (start + 1) formula decoded with
              ⟨count, width, hShape⟩
            refine ⟨count + 1, ?_, ?_⟩
            · exact width.trans (nat_add_succ_shift start count)
            · exact congrArg (List.cons CNFToken.t) hShape
        | sep => contradiction
        | finish => contradiction
      · intro clauses decoded
        cases token with
        | f => contradiction
        | t => contradiction
        | sep =>
            change (match decodeFormulaClause rest with
              | none => none
              | some (clause, suffix) => some (clause :: suffix)) =
                some clauses at decoded
            cases hRest : decodeFormulaClause rest with
            | none =>
                rw [hRest] at decoded
                contradiction
            | some found =>
                rcases found with ⟨clause, suffix⟩
                rw [hRest] at decoded
                have hClauses : clause :: suffix = clauses :=
                  Option.some.inj decoded
                cases hClauses
                have hShape := clauseIH clause suffix hRest
                change CNFToken.sep :: rest =
                  (CNFToken.sep ::
                    (encodeLiteralListTokens clause ++ [.finish])) ++
                    encodeClauseListTokens suffix ++ [.finish]
                rw [hShape]
                exact congrArg (List.cons CNFToken.sep)
                  (calc
                    encodeLiteralListTokens clause ++
                        (CNFToken.finish ::
                          (encodeClauseListTokens suffix ++ [.finish])) =
                        (encodeLiteralListTokens clause ++ [.finish]) ++
                          (encodeClauseListTokens suffix ++ [.finish]) :=
                      (token_append_assoc_constructive
                        (encodeLiteralListTokens clause) [.finish]
                        (encodeClauseListTokens suffix ++ [.finish])).symm
                    _ = ((encodeLiteralListTokens clause ++ [.finish]) ++
                          encodeClauseListTokens suffix) ++ [.finish] :=
                      (token_append_assoc_constructive
                        (encodeLiteralListTokens clause ++ [.finish])
                        (encodeClauseListTokens suffix) [.finish]).symm)
        | finish =>
            cases rest with
            | nil =>
                change some [] = some clauses at decoded
                have hClauses : [] = clauses := Option.some.inj decoded
                cases hClauses
                rfl
            | cons next suffix => contradiction
      · intro clause clauses decoded
        cases token with
        | f =>
            change decodeFormulaLiteral false 0 rest =
              some (clause, clauses) at decoded
            rcases literalIH false 0 clause clauses decoded with
              ⟨count, tail, hClause, hShape⟩
            rw [Nat.zero_add] at hClause
            cases hClause
            change CNFToken.f :: rest =
              ((CNFToken.f :: encodeUnaryTokens count) ++
                encodeLiteralListTokens tail) ++
                (.finish :: (encodeClauseListTokens clauses ++ [.finish]))
            rw [hShape]
            rw [token_append_assoc_constructive]
            rfl
        | t =>
            change decodeFormulaLiteral true 0 rest =
              some (clause, clauses) at decoded
            rcases literalIH true 0 clause clauses decoded with
              ⟨count, tail, hClause, hShape⟩
            rw [Nat.zero_add] at hClause
            cases hClause
            change CNFToken.t :: rest =
              ((CNFToken.t :: encodeUnaryTokens count) ++
                encodeLiteralListTokens tail) ++
                (.finish :: (encodeClauseListTokens clauses ++ [.finish]))
            rw [hShape]
            rw [token_append_assoc_constructive]
            rfl
        | sep => contradiction
        | finish =>
            change (match decodeFormulaClauses rest with
              | none => none
              | some suffix => some ([], suffix)) =
                some (clause, clauses) at decoded
            cases hRest : decodeFormulaClauses rest with
            | none =>
                rw [hRest] at decoded
                contradiction
            | some suffix =>
                rw [hRest] at decoded
                have hPair : ([], suffix) = (clause, clauses) :=
                  Option.some.inj decoded
                have hClause : [] = clause := congrArg Prod.fst hPair
                have hClauses : suffix = clauses := congrArg Prod.snd hPair
                cases hClause
                cases hClauses
                have hShape := clausesIH clauses hRest
                exact congrArg (List.cons CNFToken.finish) hShape
      · intro positive start clause clauses decoded
        cases token with
        | f =>
            change (match decodeFormulaClause rest with
              | none => none
              | some (tail, suffix) => some
                  (({ positive := positive, variableIndex := start } :
                    CNFLiteral) :: tail, suffix)) =
                some (clause, clauses) at decoded
            cases hRest : decodeFormulaClause rest with
            | none =>
                rw [hRest] at decoded
                contradiction
            | some found =>
                rcases found with ⟨tail, suffix⟩
                rw [hRest] at decoded
                have hPair :
                    (({ positive := positive, variableIndex := start } :
                      CNFLiteral) :: tail, suffix) = (clause, clauses) :=
                  Option.some.inj decoded
                have hClause := congrArg Prod.fst hPair
                have hClauses := congrArg Prod.snd hPair
                cases hClause
                cases hClauses
                have hShape := clauseIH tail clauses hRest
                refine ⟨0, tail, ?_, ?_⟩
                · rfl
                · exact congrArg (List.cons CNFToken.f) hShape
        | t =>
            change decodeFormulaLiteral positive (start + 1) rest =
              some (clause, clauses) at decoded
            rcases literalIH positive (start + 1) clause clauses decoded with
              ⟨count, tail, hClause, hShape⟩
            refine ⟨count + 1, tail, ?_, ?_⟩
            · rw [hClause]
              exact congrArg
                (fun index =>
                  ({ positive := positive, variableIndex := index } :
                    CNFLiteral) :: tail)
                (nat_add_succ_shift start count)
            · exact congrArg (List.cons CNFToken.t) hShape
        | sep => contradiction
        | finish => contradiction

/-- Every accepted formula token stream is exactly the canonical encoding of
the formula returned by the strict decoder. -/
theorem encodeCNFTokens_of_decode (tokens : List CNFToken)
    (formula : CNFFormula) (decoded : decodeCNFTokens tokens = some formula) :
    encodeCNFTokens formula = tokens := by
  have inverse := decodeFormulaGrammar_inverse tokens
  rcases inverse.1 0 formula decoded with ⟨count, width, hShape⟩
  have countEq : formula.variableCount = count := by
    exact width.trans (Nat.zero_add count)
  rw [← countEq] at hShape
  unfold encodeCNFTokens
  exact (token_append_assoc_constructive
    (encodeUnaryTokens formula.variableCount)
    (encodeClauseListTokens formula.clauses) [.finish]).trans hShape.symm

/-- Every successfully decoded raw formula is byte-for-byte its canonical
formula encoding, including the unique final pad bit. -/
theorem encodeFormula_of_decode (bits : BitString) (formula : CNFFormula)
    (decoded : decodeEncodedCNF bits = some formula) :
    encodeFormula formula = bits := by
  unfold decodeEncodedCNF at decoded
  cases hTokens : decodeFormulaTokenPairs bits with
  | none =>
      rw [hTokens] at decoded
      contradiction
  | some tokens =>
      rw [hTokens] at decoded
      have hTokenShape := encodeCNFTokens_of_decode tokens formula decoded
      have hBitShape := encodeFormulaTokenPairs_of_decode bits tokens hTokens
      unfold encodeFormula encodeCNF
      exact (congrArg (fun stream => encodeTokenPairs stream ++ [false])
        hTokenShape).trans hBitShape

/-! ### Width-phase literal interpreter steps -/

theorem widthToBoundary_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthToBoundary
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthDoneToBoundary_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneToBoundary
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthPastCounter_step (leftSide : List WorkSymbol)
    (suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthPastCertificateCounter leftSide
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthPastCertificateCounter
        (cnfMarkFalse :: leftSide) suffix) := by
  rfl

theorem widthFindAssignment_mark_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindAssignment leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindAssignment
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthDoneCheckAssignment_step (leftSide : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDoneCheckAssignment leftSide
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
        (head :: leftSide) suffix) := by
  cases allowed <;> rfl

theorem widthBackAssignment_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackAssignment
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackAssignment
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

theorem widthBackCounter_step (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
          (cnfMarkFalse :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
        leftTail (cnfMarkFalse :: rightSide)) := by
  rfl

theorem widthBackFormula_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : FormulaOrCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackFormula
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackFormula
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

theorem widthRestoreBackFormula_step (head : WorkSymbol)
    (leftTail rightSide : List WorkSymbol)
    (allowed : FormulaOrCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

/-! ### Exact width scans and their first composed outward pass -/

theorem widthToBoundary_scan (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthToBoundary
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine CNFWorkState.widthToBoundary
    FormulaScanSymbol widthToBoundary_step word suffix leftSide allowed

theorem widthPastCounter_scan (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthPastCertificateCounter leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthPastCertificateCounter
        (pushWorkLeft word leftSide) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.widthPastCertificateCounter
    (fun symbol => symbol = cnfMarkFalse) _ word suffix leftSide allowed
  intro foundLeft found suffix foundEq
  cases foundEq
  exact widthPastCounter_step foundLeft suffix

theorem widthFindAssignment_scan (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthFindAssignment leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindAssignment
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine CNFWorkState.widthFindAssignment
    AssignmentMarkSymbol widthFindAssignment_mark_step word suffix leftSide
      allowed

theorem widthToBoundary_guard_step (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthPastCertificateCounter
        (cnfBoundaryGuard :: leftSide) suffix) := by
  rfl

theorem widthPastCounter_finish_step (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthPastCertificateCounter leftSide
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindAssignment
        (cnfFinish :: leftSide) suffix) := by
  rfl

/-- The first outward width pass crosses the formula tail, the certificate
counter, and the already marked assignment prefix with an exact additive
step count.  The focused `next` cell is deliberately left abstract: its
transition determines whether the next width unit exists. -/
theorem widthToAssignmentPrefix_run
    (formulaTail counter markedAssignment leftSide suffix : List WorkSymbol)
    (next : WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (((formulaTail.length + 1) + counter.length + 1) +
          markedAssignment.length)
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish :: (markedAssignment ++ next :: suffix)))))) =
      some (workConfigAtWord CNFWorkState.widthFindAssignment
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
        (next :: suffix)) := by
  have hFormula := widthToBoundary_scan formulaTail
    (cnfBoundaryGuard :: (counter ++
      (cnfFinish :: (markedAssignment ++ next :: suffix))))
    leftSide formulaAllowed
  have hGuard := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthToBoundary_guard_step (pushWorkLeft formulaTail leftSide)
      (counter ++ (cnfFinish :: (markedAssignment ++ next :: suffix))))
  have hCounter := widthPastCounter_scan counter
    (cnfFinish :: markedAssignment ++ next :: suffix)
    (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide) counterAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthPastCounter_finish_step
      (pushWorkLeft counter
        (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
      (markedAssignment ++ next :: suffix))
  have hAssignment := widthFindAssignment_scan markedAssignment
    (next :: suffix)
    (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
    assignmentAllowed
  have hFormulaGuard := workRunExact?_compose cnfWorkMachine
    formulaTail.length 1 _ _ _ hFormula hGuard
  have hThroughCounter := workRunExact?_compose cnfWorkMachine
    (formulaTail.length + 1) counter.length _ _ _ hFormulaGuard hCounter
  have hThroughFinish := workRunExact?_compose cnfWorkMachine
    ((formulaTail.length + 1) + counter.length) 1 _ _ _
      hThroughCounter hFinish
  exact workRunExact?_compose cnfWorkMachine
    (((formulaTail.length + 1) + counter.length) + 1)
    markedAssignment.length _ _ _ hThroughFinish hAssignment

/-! ### Exact literal outward scans -/

set_option maxRecDepth 4096 in
theorem literalIndexToBoundary_step (alreadySatisfied positive : Bool)
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol) (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
          leftSide (head :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
        (head :: leftSide) suffix) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

set_option maxRecDepth 4096 in
theorem literalIndexToBoundary_guard_step
    (alreadySatisfied positive : Bool) (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
          leftSide (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexPastCertificateCounter
          alreadySatisfied positive)
        (cnfBoundaryGuard :: leftSide) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

set_option maxRecDepth 4096 in
theorem literalIndexPastCounter_step
    (alreadySatisfied positive : Bool) (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndexPastCertificateCounter
            alreadySatisfied positive)
          leftSide (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexPastCertificateCounter
          alreadySatisfied positive)
        (cnfMarkFalse :: leftSide) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

set_option maxRecDepth 4096 in
theorem literalIndexPastCounter_finish_step
    (alreadySatisfied positive : Bool) (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndexPastCertificateCounter
            alreadySatisfied positive)
          leftSide (cnfFinish :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
        (cnfFinish :: leftSide) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

set_option maxRecDepth 4096 in
theorem literalMarkAssignment_step (alreadySatisfied positive : Bool)
    (leftSide : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol) (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
          leftSide (head :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
        (head :: leftSide) suffix) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

theorem literalIndexToBoundary_scan (alreadySatisfied positive : Bool)
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord
          (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
          leftSide (word ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
    FormulaScanSymbol (literalIndexToBoundary_step alreadySatisfied positive)
    word suffix leftSide allowed

theorem literalIndexPastCounter_scan (alreadySatisfied positive : Bool)
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord
          (CNFWorkState.literalIndexPastCertificateCounter
            alreadySatisfied positive)
          leftSide (word ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexPastCertificateCounter
          alreadySatisfied positive)
        (pushWorkLeft word leftSide) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalIndexPastCertificateCounter
      alreadySatisfied positive)
    (fun symbol => symbol = cnfMarkFalse) _ word suffix leftSide allowed
  intro foundLeft found foundSuffix foundEq
  cases foundEq
  exact literalIndexPastCounter_step alreadySatisfied positive
    foundLeft foundSuffix

theorem literalMarkAssignment_scan (alreadySatisfied positive : Bool)
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord
          (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
          leftSide (word ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
    AssignmentMarkSymbol
    (literalMarkAssignment_step alreadySatisfied positive)
    word suffix leftSide allowed

/-- A marked literal index performs the same finite outward traversal as the
width phase: formula tail, certificate counter, then the marked assignment
prefix.  The exact endpoint is the first unmarked value or the right guard. -/
theorem literalIndexToAssignmentPrefix_run
    (alreadySatisfied positive : Bool)
    (formulaTail counter markedAssignment leftSide suffix : List WorkSymbol)
    (next : WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (((formulaTail.length + 1) + counter.length + 1) +
          markedAssignment.length)
        (workConfigAtWord
          (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
          leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish :: (markedAssignment ++ next :: suffix)))))) =
      some (workConfigAtWord
        (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
        (next :: suffix)) := by
  have hFormula := literalIndexToBoundary_scan alreadySatisfied positive
    formulaTail
    (cnfBoundaryGuard :: (counter ++
      (cnfFinish :: (markedAssignment ++ next :: suffix))))
    leftSide formulaAllowed
  have hGuard := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndexToBoundary_guard_step alreadySatisfied positive
      (pushWorkLeft formulaTail leftSide)
      (counter ++ (cnfFinish :: (markedAssignment ++ next :: suffix))))
  have hCounter := literalIndexPastCounter_scan alreadySatisfied positive
    counter (cnfFinish :: markedAssignment ++ next :: suffix)
    (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide) counterAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndexPastCounter_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
      (markedAssignment ++ next :: suffix))
  have hAssignment := literalMarkAssignment_scan alreadySatisfied positive
    markedAssignment (next :: suffix)
    (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
    assignmentAllowed
  have hFormulaGuard := workRunExact?_compose cnfWorkMachine
    formulaTail.length 1 _ _ _ hFormula hGuard
  have hThroughCounter := workRunExact?_compose cnfWorkMachine
    (formulaTail.length + 1) counter.length _ _ _ hFormulaGuard hCounter
  have hThroughFinish := workRunExact?_compose cnfWorkMachine
    ((formulaTail.length + 1) + counter.length) 1 _ _ _
      hThroughCounter hFinish
  exact workRunExact?_compose cnfWorkMachine
    (((formulaTail.length + 1) + counter.length) + 1)
    markedAssignment.length _ _ _ hThroughFinish hAssignment

/-! ### Conservative cubic phase ledger -/

def cnfShiftedWorkSpan (n : Nat) : Nat := n + 2

def cnfWorkPhaseCube (n : Nat) : Nat :=
  cnfShiftedWorkSpan n * cnfShiftedWorkSpan n * cnfShiftedWorkSpan n

/-- Each of frame validation, width checking, and clause/literal evaluation
receives sixteen shifted-span cubes. -/
def cnfSinglePhaseBudget (n : Nat) : Nat := cnfWorkPhaseCube n * 16

/-- Eight fixed transitions plus three independent sixteen-cube phase
allocations. -/
def cnfConservativePhaseBudget (n : Nat) : Nat :=
  ((8 + cnfSinglePhaseBudget n) + cnfSinglePhaseBudget n) +
    cnfSinglePhaseBudget n

theorem cnfShiftedSquare_le_phaseCube (n : Nat) :
    cnfShiftedWorkSpan n * cnfShiftedWorkSpan n ≤
      cnfWorkPhaseCube n := by
  have positive : 1 ≤ n + 2 :=
    Nat.succ_le_succ (Nat.zero_le (n + 1))
  unfold cnfShiftedWorkSpan cnfWorkPhaseCube
  exact Nat.le_mul_of_pos_right ((n + 2) * (n + 2)) positive

theorem cnfShiftedSpan_le_square (n : Nat) :
    cnfShiftedWorkSpan n ≤
      cnfShiftedWorkSpan n * cnfShiftedWorkSpan n := by
  have positive : 1 ≤ n + 2 :=
    Nat.succ_le_succ (Nat.zero_le (n + 1))
  unfold cnfShiftedWorkSpan
  exact Nat.le_mul_of_pos_right (n + 2) positive

theorem cnfScaledQuadratic_le_singlePhaseBudget (n coefficient : Nat)
    (coefficientBound : coefficient ≤ 16) :
    (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * coefficient ≤
      cnfSinglePhaseBudget n := by
  have scaledCoefficient :
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * coefficient ≤
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 16 :=
    Nat.mul_le_mul_left
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) coefficientBound
  have scaledCube :
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 16 ≤
        cnfWorkPhaseCube n * 16 :=
    Nat.mul_le_mul_right 16 (cnfShiftedSquare_le_phaseCube n)
  exact Nat.le_trans scaledCoefficient scaledCube

theorem cnfScaledLinear_le_singlePhaseBudget (n coefficient : Nat)
    (coefficientBound : coefficient ≤ 16) :
    cnfShiftedWorkSpan n * coefficient ≤
      cnfSinglePhaseBudget n := by
  have scaledSquare : cnfShiftedWorkSpan n * coefficient ≤
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * coefficient :=
    Nat.mul_le_mul_right coefficient (cnfShiftedSpan_le_square n)
  exact Nat.le_trans scaledSquare
    (cnfScaledQuadratic_le_singlePhaseBudget n coefficient coefficientBound)

theorem cnfConservativePhaseBudget_normalized (n : Nat) :
    cnfConservativePhaseBudget n = 8 + cnfWorkPhaseCube n * 48 := by
  unfold cnfConservativePhaseBudget cnfSinglePhaseBudget
  rw [Nat.add_assoc 8]
  rw [Nat.add_assoc 8]
  rw [← Nat.mul_add]
  rw [← Nat.mul_add]

theorem cnfPhaseCoefficient_le_declared : 48 ≤ 64 := by
  change 48 ≤ 48 + 16
  exact Nat.le_add_right 48 16

theorem cnfConservativePhaseBudget_le_polynomial (n : Nat) :
    cnfConservativePhaseBudget n ≤ cnfWorkStepPolynomial.eval n := by
  rw [cnfConservativePhaseBudget_normalized]
  rw [cnfWorkStepPolynomial_eval]
  have scaled : cnfWorkPhaseCube n * 48 ≤
      cnfWorkPhaseCube n * 64 :=
    Nat.mul_le_mul_left (cnfWorkPhaseCube n)
      cnfPhaseCoefficient_le_declared
  have commute : cnfWorkPhaseCube n * 64 = 64 * cnfWorkPhaseCube n :=
    Nat.mul_comm (cnfWorkPhaseCube n) 64
  exact Nat.add_le_add (Nat.le_refl 8)
    (Nat.le_trans scaled (Nat.le_of_eq commute))

/-- Pointwise phase bounds add to the conservative cubic allocation. -/
theorem cnfPhaseSteps_le_polynomial (n fixedSteps frameSteps widthSteps
    grammarSteps : Nat)
    (fixedBound : fixedSteps ≤ 8)
    (frameBound : frameSteps ≤ cnfSinglePhaseBudget n)
    (widthBound : widthSteps ≤ cnfSinglePhaseBudget n)
    (grammarBound : grammarSteps ≤ cnfSinglePhaseBudget n) :
    ((fixedSteps + frameSteps) + widthSteps) + grammarSteps ≤
      cnfWorkStepPolynomial.eval n := by
  have fixedFrame : fixedSteps + frameSteps ≤
      8 + cnfSinglePhaseBudget n :=
    Nat.add_le_add fixedBound frameBound
  have throughWidth : (fixedSteps + frameSteps) + widthSteps ≤
      (8 + cnfSinglePhaseBudget n) + cnfSinglePhaseBudget n :=
    Nat.add_le_add fixedFrame widthBound
  have throughGrammar :
      ((fixedSteps + frameSteps) + widthSteps) + grammarSteps ≤
        cnfConservativePhaseBudget n :=
    Nat.add_le_add throughWidth grammarBound
  exact Nat.le_trans throughGrammar
    (cnfConservativePhaseBudget_le_polynomial n)

/-- Four exact phase traces compose into a halted exact execution within the
declared cubic fuel.  The theorem is deliberately conditional on the phase
traces; the remaining semantic inductions supply those traces. -/
theorem cnfWorkExact_phaseLedger
    (n fixedSteps frameSteps widthSteps grammarSteps : Nat)
    (start afterFixed afterFrame afterWidth final : WorkConfiguration)
    (fixedRun : workRunExact? cnfWorkMachine fixedSteps start =
      some afterFixed)
    (frameRun : workRunExact? cnfWorkMachine frameSteps afterFixed =
      some afterFrame)
    (widthRun : workRunExact? cnfWorkMachine widthSteps afterFrame =
      some afterWidth)
    (grammarRun : workRunExact? cnfWorkMachine grammarSteps afterWidth =
      some final)
    (fixedBound : fixedSteps ≤ 8)
    (frameBound : frameSteps ≤ cnfSinglePhaseBudget n)
    (widthBound : widthSteps ≤ cnfSinglePhaseBudget n)
    (grammarBound : grammarSteps ≤ cnfSinglePhaseBudget n)
    (halted : cnfWorkMachine.isHalted final = true) :
    ∃ steps,
      steps ≤ cnfWorkStepPolynomial.eval n ∧
      workRunExact? cnfWorkMachine steps start = some final ∧
      cnfWorkMachine.isHalted final = true ∧
      workRun cnfWorkMachine (cnfWorkStepPolynomial.eval n) start = final := by
  have fixedFrameRun := workRunExact?_compose cnfWorkMachine
    fixedSteps frameSteps start afterFixed afterFrame fixedRun frameRun
  have throughWidthRun := workRunExact?_compose cnfWorkMachine
    (fixedSteps + frameSteps) widthSteps start afterFrame afterWidth
    fixedFrameRun widthRun
  have completeRun := workRunExact?_compose cnfWorkMachine
    ((fixedSteps + frameSteps) + widthSteps) grammarSteps
    start afterWidth final throughWidthRun grammarRun
  have completeBound := cnfPhaseSteps_le_polynomial n fixedSteps
    frameSteps widthSteps grammarSteps fixedBound frameBound widthBound
    grammarBound
  refine ⟨((fixedSteps + frameSteps) + widthSteps) + grammarSteps,
    completeBound, completeRun, halted, ?_⟩
  exact workRun_pad_exact_halted cnfWorkMachine
    (((fixedSteps + frameSteps) + widthSteps) + grammarSteps)
    (cnfWorkStepPolynomial.eval n) start final completeRun halted completeBound

namespace FrameTraceDesign

set_option maxRecDepth 100000

theorem boot_nonempty_formula_exact
    (first : CNFToken) (formulaRest assignmentTokens : List CNFToken) :
    workRunExact? cnfWorkMachine 2
        (workStartConfiguration cnfWorkMachine
          (WorkTape.ofSymbols
            (pairedTokenLayout (first :: formulaRest) assignmentTokens))) =
      some
        { state := CNFWorkState.frameOneFindCounter
          tape := WorkTape.focus [cnfRootGuard] cnfT
            (List.replicate formulaRest.length cnfT ++
              cnfFinish ::
                (first.workSymbol ::
                  (cnfTokenWorkSymbols formulaRest ++
                    cnfSep ::
                      (List.replicate assignmentTokens.length cnfT ++
                        cnfFinish ::
                          (cnfTokenWorkSymbols assignmentTokens ++
                            [cnfFinish]))))) } := by
  rfl

def frameOneMarkedToken : CNFToken → WorkSymbol
  | .f => cnfMarkFalse
  | .t => cnfMarkTrue
  | .sep => cnfRootGuard
  | .finish => cnfBoundaryGuard

def frameOneMarkedTokens : List CNFToken → List WorkSymbol
  | [] => []
  | token :: rest => frameOneMarkedToken token :: frameOneMarkedTokens rest

def frameOneRestoreSymbol : WorkSymbol → WorkSymbol
  | ⟨.blank, .blank⟩ => cnfBlank
  | ⟨.blank, .zero⟩ => cnfF
  | ⟨.blank, .one⟩ => cnfT
  | ⟨.zero, .blank⟩ => cnfSep
  | ⟨.zero, .zero⟩ => cnfF
  | ⟨.zero, .one⟩ => cnfSep
  | ⟨.one, .blank⟩ => cnfFinish
  | ⟨.one, .zero⟩ => cnfFinish
  | ⟨.one, .one⟩ => cnfT

inductive FrameOneMarkedSymbol : WorkSymbol → Prop where
  | markFalse : FrameOneMarkedSymbol cnfMarkFalse
  | markTrue : FrameOneMarkedSymbol cnfMarkTrue
  | rootGuard : FrameOneMarkedSymbol cnfRootGuard
  | boundaryGuard : FrameOneMarkedSymbol cnfBoundaryGuard

inductive RawCNFTokenSymbol : WorkSymbol → Prop where
  | f : RawCNFTokenSymbol cnfF
  | t : RawCNFTokenSymbol cnfT
  | sep : RawCNFTokenSymbol cnfSep
  | finish : RawCNFTokenSymbol cnfFinish

inductive FrameOneBackCounterSymbol : WorkSymbol → Prop where
  | t : FrameOneBackCounterSymbol cnfT
  | markFalse : FrameOneBackCounterSymbol cnfMarkFalse

theorem mem_replicate_workSymbol_eq (count : Nat)
    (expected found : WorkSymbol)
    (member : List.Mem found (List.replicate count expected)) :
    found = expected := by
  induction count with
  | zero => contradiction
  | succ count ih =>
      cases member with
      | head => rfl
      | tail _ tailMember => exact ih tailMember

theorem length_replicate_workSymbol (count : Nat) (symbol : WorkSymbol) :
    (List.replicate count symbol).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih



theorem pushWorkLeft_append (first second farSide : List WorkSymbol) :
    pushWorkLeft (first ++ second) farSide =
      pushWorkLeft second (pushWorkLeft first farSide) := by
  induction first generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)





theorem pushWorkLeft_append_far (word left right : List WorkSymbol) :
    pushWorkLeft word (left ++ right) = pushWorkLeft word left ++ right := by
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  exact pushScannedWorkSymbols_append_far word left right

theorem pushWorkLeft_split_far (word farSide : List WorkSymbol) :
    pushWorkLeft word farSide = pushWorkLeft word [] ++ farSide := by
  change pushWorkLeft word ([] ++ farSide) = _
  exact pushWorkLeft_append_far word [] farSide

theorem map_pushWorkLeft (transform : WorkSymbol → WorkSymbol)
    (word farSide : List WorkSymbol) :
    List.map transform (pushWorkLeft word farSide) =
      pushWorkLeft (List.map transform word) (List.map transform farSide) := by
  induction word generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

theorem frameOneRestore_markedToken (token : CNFToken) :
    frameOneRestoreSymbol (frameOneMarkedToken token) = token.workSymbol := by
  cases token <;> rfl

theorem frameOneRestore_markedTokens (tokens : List CNFToken) :
    List.map frameOneRestoreSymbol (frameOneMarkedTokens tokens) =
      cnfTokenWorkSymbols tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      change frameOneRestoreSymbol (frameOneMarkedToken token) ::
          List.map frameOneRestoreSymbol (frameOneMarkedTokens rest) =
        token.workSymbol :: cnfTokenWorkSymbols rest
      rw [frameOneRestore_markedToken, ih]

theorem frameOneMarkedTokens_allowed (tokens : List CNFToken)
    (found : WorkSymbol)
    (member : List.Mem found (frameOneMarkedTokens tokens)) :
    FrameOneMarkedSymbol found := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases member with
      | head =>
          cases token with
          | f => exact .markFalse
          | t => exact .markTrue
          | sep => exact .rootGuard
          | finish => exact .boundaryGuard
      | tail _ tailMember => exact ih tailMember

theorem cnfTokenWorkSymbols_raw (tokens : List CNFToken)
    (found : WorkSymbol)
    (member : List.Mem found (cnfTokenWorkSymbols tokens)) :
    RawCNFTokenSymbol found := by
  induction tokens with
  | nil => contradiction
  | cons token rest ih =>
      cases member with
      | head =>
          cases token with
          | f => exact .f
          | t => exact .t
          | sep => exact .sep
          | finish => exact .finish
      | tail _ tailMember => exact ih tailMember

/-- Generic exact left scan whose selected rules rewrite each crossed cell. -/
theorem workRunExact?_scanLeft_write (machine : WorkMachine) (state : Nat)
    (transform : WorkSymbol → WorkSymbol) (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (workConfigAtLeftWord state (head :: leftTail) rightSide) =
        some (workConfigAtLeftWord state leftTail
          (transform head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord state leftSuffix
        (pushWorkLeft (List.map transform word) rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, List.Mem symbol rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (workConfigAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (transform head :: rightSide) hRest

theorem pushWorkLeft_members_allowed (Allowed : WorkSymbol → Prop)
    (word farSide : List WorkSymbol)
    (wordAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol)
    (farAllowed : ∀ symbol, List.Mem symbol farSide → Allowed symbol)
    (found : WorkSymbol) (member : List.Mem found
      (pushWorkLeft word farSide)) : Allowed found := by
  induction word generalizing farSide with
  | nil => exact farAllowed found member
  | cons head rest ih =>
      apply ih (head :: farSide)
      · intro symbol restMember
        exact wordAllowed symbol (List.Mem.tail head restMember)
      · intro symbol accumulatorMember
        cases accumulatorMember with
        | head => exact wordAllowed head (List.Mem.head rest)
        | tail _ tailMember => exact farAllowed symbol tailMember
      · exact member

theorem pushWorkLeft_length (word farSide : List WorkSymbol) :
    (pushWorkLeft word farSide).length = word.length + farSide.length := by
  induction word generalizing farSide with
  | nil => exact (Nat.zero_add farSide.length).symm
  | cons head rest ih =>
      change (pushWorkLeft rest (head :: farSide)).length =
        Nat.succ rest.length + farSide.length
      rw [ih]
      exact (Nat.add_succ rest.length farSide.length).trans
        (Nat.succ_add rest.length farSide.length).symm

theorem frameOneMarkedTokens_length (tokens : List CNFToken) :
    (frameOneMarkedTokens tokens).length = tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih => exact congrArg Nat.succ ih

theorem frameOne_restore_stack_allowed (tokens : List CNFToken)
    (found : WorkSymbol)
    (member : List.Mem found
      (pushWorkLeft (frameOneMarkedTokens tokens) [])) :
    FrameOneMarkedSymbol found := by
  apply pushWorkLeft_members_allowed FrameOneMarkedSymbol
    (frameOneMarkedTokens tokens) []
      (frameOneMarkedTokens_allowed tokens)
  · intro symbol impossible
    contradiction
  · exact member

theorem frameOne_findCounter_markFalse_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneFindCounter left
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindCounter
        (cnfMarkFalse :: left) suffix) := by
  rfl

theorem frameOne_findCounter_markFalse_scan
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine count
        (workConfigAtWord CNFWorkState.frameOneFindCounter left
          (List.replicate count cnfMarkFalse ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindCounter
        (pushWorkLeft (List.replicate count cnfMarkFalse) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneFindCounter
    (fun symbol => symbol = cnfMarkFalse)
    (fun stepLeft head stepSuffix equal => by
      cases equal
      exact frameOne_findCounter_markFalse_step stepLeft stepSuffix)
    (List.replicate count cnfMarkFalse) suffix left
    (mem_replicate_workSymbol_eq count cnfMarkFalse)
  rw [length_replicate_workSymbol count cnfMarkFalse] at scanned
  exact scanned

theorem frameOne_findCounter_finish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneFindCounter left
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneCheckPayload
        (cnfFinish :: left) suffix) := by
  rfl

theorem frameOne_checkPayload_marked_step
    (head : WorkSymbol) (left suffix : List WorkSymbol)
    (allowed : FrameOneMarkedSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneCheckPayload left
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneCheckPayload
        (head :: left) suffix) := by
  cases allowed <;> rfl

theorem frameOne_checkPayload_marked_scan
    (tokens : List CNFToken) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine tokens.length
        (workConfigAtWord CNFWorkState.frameOneCheckPayload left
          (frameOneMarkedTokens tokens ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneCheckPayload
        (pushWorkLeft (frameOneMarkedTokens tokens) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneCheckPayload FrameOneMarkedSymbol
    (fun leftSide head suffix allowed =>
      frameOne_checkPayload_marked_step head leftSide suffix allowed)
    (frameOneMarkedTokens tokens) suffix left
    (frameOneMarkedTokens_allowed tokens)
  rw [frameOneMarkedTokens_length tokens] at scanned
  exact scanned

theorem frameOne_checkPayload_sep_step
    (leftWord suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneCheckPayload leftWord
          (cnfSep :: suffix)) =
      some (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
        leftWord (cnfBoundaryGuard :: suffix)) := by
  cases leftWord <;> rfl

theorem frameOne_restorePayload_marked_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : FrameOneMarkedSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
        leftTail (frameOneRestoreSymbol head :: right)) := by
  cases allowed <;> rfl

theorem frameOne_restorePayload_tokens_scan
    (tokens : List CNFToken) (leftSuffix right : List WorkSymbol) :
    workRunExact? cnfWorkMachine tokens.length
        (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
          (pushWorkLeft (frameOneMarkedTokens tokens) leftSuffix) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
        leftSuffix (cnfTokenWorkSymbols tokens ++ right)) := by
  have scanned := workRunExact?_scanLeft_write cnfWorkMachine
    CNFWorkState.frameOneRestorePayload frameOneRestoreSymbol
    FrameOneMarkedSymbol frameOne_restorePayload_marked_step
    (pushWorkLeft (frameOneMarkedTokens tokens) []) leftSuffix right
    (frameOne_restore_stack_allowed tokens)
  rw [pushWorkLeft_length] at scanned
  rw [frameOneMarkedTokens_length tokens] at scanned
  rw [pushWorkLeft_split_far]
  rw [map_pushWorkLeft] at scanned
  rw [frameOneRestore_markedTokens] at scanned
  change workRunExact? cnfWorkMachine tokens.length
      (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
        (pushWorkLeft (frameOneMarkedTokens tokens) [] ++ leftSuffix) right) =
    some (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
      leftSuffix
      (pushWorkLeft (pushWorkLeft (cnfTokenWorkSymbols tokens) []) right))
    at scanned
  rw [pushWorkLeft_cancel] at scanned
  exact scanned

theorem frameOne_restorePayload_finish_step
    (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneRestorePayload
          (cnfFinish :: left) right) =
      some (workConfigAtWord CNFWorkState.frameOneGoBoundary
        (cnfFinish :: left) right) := by
  rfl

theorem frameOne_goBoundary_token_step
    (head : WorkSymbol) (left suffix : List WorkSymbol)
    (allowed : RawCNFTokenSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneGoBoundary left
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneGoBoundary
        (head :: left) suffix) := by
  cases allowed <;> rfl

theorem frameOne_goBoundary_tokens_scan
    (tokens : List CNFToken) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine tokens.length
        (workConfigAtWord CNFWorkState.frameOneGoBoundary left
          (cnfTokenWorkSymbols tokens ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneGoBoundary
        (pushWorkLeft (cnfTokenWorkSymbols tokens) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneGoBoundary RawCNFTokenSymbol
    (fun leftSide head stepSuffix allowed =>
      frameOne_goBoundary_token_step head leftSide stepSuffix allowed)
    (cnfTokenWorkSymbols tokens) suffix left
    (cnfTokenWorkSymbols_raw tokens)
  rw [cnfTokenWorkSymbols_length tokens] at scanned
  exact scanned

theorem frameOne_goBoundary_guard_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneGoBoundary left
          (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: left) suffix) := by
  rfl

/-- Once every frame-one counter and payload cell is marked, validation,
restoration, and transfer to frame two take exactly `4 * tokens.length + 4`
primitive transitions (spelled additively here for direct composition). -/
theorem frameOne_terminal_exact
    (tokens : List CNFToken) (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (((((((tokens.length + 1) + tokens.length) + 1) +
          tokens.length) + 1) + tokens.length) + 1)
        (workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
          (List.replicate tokens.length cnfMarkFalse ++
            cnfFinish ::
              (frameOneMarkedTokens tokens ++ cnfSep :: suffix))) =
      some
        (workConfigAtWord CNFWorkState.frameTwoFindCounter
          (cnfBoundaryGuard ::
            pushWorkLeft (cnfTokenWorkSymbols tokens)
              (cnfFinish ::
                pushWorkLeft
                  (List.replicate tokens.length cnfMarkFalse)
                  [cnfRootGuard]))
          suffix) := by
  have hCounter := frameOne_findCounter_markFalse_scan tokens.length
    [cnfRootGuard]
    (cnfFinish :: frameOneMarkedTokens tokens ++ cnfSep :: suffix)
  have hCounterFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_findCounter_finish_step
      (pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
      (frameOneMarkedTokens tokens ++ cnfSep :: suffix))
  have hPayload := frameOne_checkPayload_marked_scan tokens
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
    (cnfSep :: suffix)
  have hSeparator := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_checkPayload_sep_step
      (pushWorkLeft (frameOneMarkedTokens tokens)
        (cnfFinish ::
          pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
            [cnfRootGuard])) suffix)
  have hRestore := frameOne_restorePayload_tokens_scan tokens
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
    (cnfBoundaryGuard :: suffix)
  have hRestoreFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_restorePayload_finish_step
      (pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
      (cnfTokenWorkSymbols tokens ++ cnfBoundaryGuard :: suffix))
  have hGoBoundary := frameOne_goBoundary_tokens_scan tokens
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
    (cnfBoundaryGuard :: suffix)
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_goBoundary_guard_step
      (pushWorkLeft (cnfTokenWorkSymbols tokens)
        (cnfFinish ::
          pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
            [cnfRootGuard])) suffix)
  have hThroughCounter := workRunExact?_compose cnfWorkMachine
    tokens.length 1 _ _ _ hCounter hCounterFinish
  have hThroughPayload := workRunExact?_compose cnfWorkMachine
    (tokens.length + 1) tokens.length _ _ _ hThroughCounter hPayload
  have hThroughSeparator := workRunExact?_compose cnfWorkMachine
    ((tokens.length + 1) + tokens.length) 1 _ _ _
      hThroughPayload hSeparator
  have hThroughRestore := workRunExact?_compose cnfWorkMachine
    (((tokens.length + 1) + tokens.length) + 1) tokens.length _ _ _
      hThroughSeparator hRestore
  have hThroughRestoreFinish := workRunExact?_compose cnfWorkMachine
    ((((tokens.length + 1) + tokens.length) + 1) + tokens.length) 1 _ _ _
      hThroughRestore hRestoreFinish
  have hThroughGoBoundary := workRunExact?_compose cnfWorkMachine
    (((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1)
    tokens.length _ _ _ hThroughRestoreFinish hGoBoundary
  exact workRunExact?_compose cnfWorkMachine
    ((((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1) +
      tokens.length) 1 _ _ _ hThroughGoBoundary hBoundary

def assignmentValueWorkSymbol : Bool → WorkSymbol
  | false => cnfF
  | true => cnfT

def markedAssignmentValueWorkSymbol : Bool → WorkSymbol
  | false => cnfMarkFalse
  | true => cnfMarkTrue

def frameTwoRestoreSymbol : WorkSymbol → WorkSymbol
  | ⟨.blank, .blank⟩ => cnfBlank
  | ⟨.blank, .zero⟩ => cnfF
  | ⟨.blank, .one⟩ => cnfT
  | ⟨.zero, .blank⟩ => cnfRootGuard
  | ⟨.zero, .zero⟩ => cnfF
  | ⟨.zero, .one⟩ => cnfSep
  | ⟨.one, .blank⟩ => cnfBoundaryGuard
  | ⟨.one, .zero⟩ => cnfFinish
  | ⟨.one, .one⟩ => cnfT

theorem assignmentWorkSymbols_cons (value : Bool) (rest : BitString) :
    assignmentWorkSymbols (value :: rest) =
      assignmentValueWorkSymbol value :: assignmentWorkSymbols rest := by
  cases value <;> rfl

theorem markedAssignmentWorkSymbols_cons (value : Bool)
    (rest : BitString) :
    markedAssignmentWorkSymbols (value :: rest) =
      markedAssignmentValueWorkSymbol value ::
        markedAssignmentWorkSymbols rest := by
  cases value <;> rfl

theorem frameTwoRestore_markedValue (value : Bool) :
    frameTwoRestoreSymbol (markedAssignmentValueWorkSymbol value) =
      assignmentValueWorkSymbol value := by
  cases value <;> rfl

theorem frameTwoRestore_markedAssignment (assignment : BitString) :
    List.map frameTwoRestoreSymbol
        (markedAssignmentWorkSymbols assignment) =
      assignmentWorkSymbols assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      rw [markedAssignmentWorkSymbols_cons]
      rw [assignmentWorkSymbols_cons]
      change frameTwoRestoreSymbol (markedAssignmentValueWorkSymbol value) ::
          List.map frameTwoRestoreSymbol
            (markedAssignmentWorkSymbols rest) =
        assignmentValueWorkSymbol value :: assignmentWorkSymbols rest
      rw [frameTwoRestore_markedValue, ih]

theorem frameTwo_findCounter_t_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (cnfT :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoToHeader
        (cnfMarkFalse :: left) suffix) := by
  rfl

theorem frameTwo_toHeader_t_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoToHeader left
          (cnfT :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoToHeader
        (cnfT :: left) suffix) := by
  rfl

theorem frameTwo_toHeader_finish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoToHeader left
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindPayload
        (cnfFinish :: left) suffix) := by
  rfl

theorem frameTwo_findPayload_value_step
    (value : Bool) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoFindPayload left
          (assignmentValueWorkSymbol value :: suffix)) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload left
        (markedAssignmentValueWorkSymbol value :: suffix)) := by
  cases value <;> rfl

theorem frameTwo_backPayload_finish_step
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload
          (cnfFinish :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
        leftTail (cnfFinish :: right)) := by
  rfl

theorem frameTwo_backHeader_counter_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : FrameOneBackCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
        leftTail (head :: right)) := by
  cases allowed <;> rfl

theorem frameTwo_backHeader_boundary_step
    (leftBase right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
          (cnfBoundaryGuard :: leftBase) right) =
      some (workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase) right) := by
  rfl




theorem frameTwo_findCounter_markFalse_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfMarkFalse :: left) suffix) := by
  rfl

theorem frameTwo_findCounter_markFalse_scan
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine count
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (List.replicate count cnfMarkFalse ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindCounter
        (pushWorkLeft (List.replicate count cnfMarkFalse) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameTwoFindCounter
    (fun symbol => symbol = cnfMarkFalse)
    (fun stepLeft head stepSuffix equal => by
      cases equal
      exact frameTwo_findCounter_markFalse_step stepLeft stepSuffix)
    (List.replicate count cnfMarkFalse) suffix left
    (mem_replicate_workSymbol_eq count cnfMarkFalse)
  rw [length_replicate_workSymbol count cnfMarkFalse] at scanned
  exact scanned

theorem frameTwo_findCounter_finish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoCheckPayload
        (cnfFinish :: left) suffix) := by
  rfl

theorem frameTwo_checkPayload_marked_step
    (head : WorkSymbol) (left suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoCheckPayload left
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoCheckPayload
        (head :: left) suffix) := by
  cases allowed <;> rfl

theorem frameTwo_checkPayload_marked_scan
    (assignment : BitString) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtWord CNFWorkState.frameTwoCheckPayload left
          (markedAssignmentWorkSymbols assignment ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoCheckPayload
        (pushWorkLeft (markedAssignmentWorkSymbols assignment) left)
        suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameTwoCheckPayload AssignmentMarkSymbol
    (fun leftSide head stepSuffix allowed =>
      frameTwo_checkPayload_marked_step head leftSide stepSuffix allowed)
    (markedAssignmentWorkSymbols assignment) suffix left
    (markedAssignmentWorkSymbols_allowed assignment)
  rw [markedAssignmentWorkSymbols_length assignment] at scanned
  exact scanned

theorem frameTwo_checkPayload_finish_step
    (left : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoCheckPayload left
          [cnfFinish]) =
      some (workConfigAtWord CNFWorkState.frameTwoEnsureBlank
        (cnfRootGuard :: left) []) := by
  rfl

theorem frameTwo_ensureBlank_step
    (guardedLeft : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoEnsureBlank guardedLeft []) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoAtRightGuard
        guardedLeft [cnfBlank]) := by
  cases guardedLeft <;> rfl

theorem frameTwo_atRightGuard_step
    (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoAtRightGuard
          (cnfRootGuard :: left) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
        left (cnfRootGuard :: right)) := by
  rfl

theorem frameTwo_restorePayload_marked_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
        leftTail (frameTwoRestoreSymbol head :: right)) := by
  cases allowed <;> rfl

theorem frameTwo_restore_stack_allowed (assignment : BitString)
    (found : WorkSymbol)
    (member : List.Mem found
      (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])) :
    AssignmentMarkSymbol found := by
  apply pushWorkLeft_members_allowed AssignmentMarkSymbol
    (markedAssignmentWorkSymbols assignment) []
      (markedAssignmentWorkSymbols_allowed assignment)
  · intro symbol impossible
    contradiction
  · exact member

theorem frameTwo_restorePayload_assignment_scan
    (assignment : BitString) (leftSuffix right : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
          (pushWorkLeft (markedAssignmentWorkSymbols assignment) leftSuffix)
          right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
        leftSuffix (assignmentWorkSymbols assignment ++ right)) := by
  have scanned := workRunExact?_scanLeft_write cnfWorkMachine
    CNFWorkState.frameTwoRestorePayload frameTwoRestoreSymbol
    AssignmentMarkSymbol frameTwo_restorePayload_marked_step
    (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])
    leftSuffix right (frameTwo_restore_stack_allowed assignment)
  rw [pushWorkLeft_length] at scanned
  rw [markedAssignmentWorkSymbols_length assignment] at scanned
  rw [pushWorkLeft_split_far]
  rw [map_pushWorkLeft] at scanned
  rw [frameTwoRestore_markedAssignment] at scanned
  change workRunExact? cnfWorkMachine assignment.length
      (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
        (pushWorkLeft (markedAssignmentWorkSymbols assignment) [] ++
          leftSuffix) right) =
    some (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
      leftSuffix
      (pushWorkLeft (pushWorkLeft (assignmentWorkSymbols assignment) [])
        right)) at scanned
  rw [pushWorkLeft_cancel] at scanned
  exact scanned

theorem frameTwo_restorePayload_finish_step
    (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoRestorePayload
          (cnfFinish :: left) right) =
      some (workConfigAtLeftWord CNFWorkState.seekLeftRoot left
        (cnfFinish :: right)) := by
  cases left <;> rfl

/-- The all-marked second frame verifies its terminal blank, installs the
right root guard, restores the assignment, and enters the left-root seek. -/
theorem frameTwo_terminal_exact
    (assignment : BitString) (leftBase : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (((((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
          assignment.length) + 1)
        (workConfigAtWord CNFWorkState.frameTwoFindCounter
          (cnfBoundaryGuard :: leftBase)
          (List.replicate assignment.length cnfMarkFalse ++
            cnfFinish ::
              (markedAssignmentWorkSymbols assignment ++ [cnfFinish]))) =
      some
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft
            (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase))
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank]))) := by
  have hCounter := frameTwo_findCounter_markFalse_scan assignment.length
    (cnfBoundaryGuard :: leftBase)
    (cnfFinish :: markedAssignmentWorkSymbols assignment ++ [cnfFinish])
  have hCounterFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_findCounter_finish_step
      (pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase))
      (markedAssignmentWorkSymbols assignment ++ [cnfFinish]))
  have hPayload := frameTwo_checkPayload_marked_scan assignment
    (cnfFinish ::
      pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase)) [cnfFinish]
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_checkPayload_finish_step
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase))))
  have hBlank := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_ensureBlank_step
      (cnfRootGuard ::
        pushWorkLeft (markedAssignmentWorkSymbols assignment)
          (cnfFinish ::
            pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
              (cnfBoundaryGuard :: leftBase))))
  have hGuard := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_atRightGuard_step
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase))) [cnfBlank])
  have hRestore := frameTwo_restorePayload_assignment_scan assignment
    (cnfFinish ::
      pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase)) [cnfRootGuard, cnfBlank]
  have hRestoreFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_restorePayload_finish_step
      (pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase))
      (assignmentWorkSymbols assignment ++ [cnfRootGuard, cnfBlank]))
  have hThroughCounter := workRunExact?_compose cnfWorkMachine
    assignment.length 1 _ _ _ hCounter hCounterFinish
  have hThroughPayload := workRunExact?_compose cnfWorkMachine
    (assignment.length + 1) assignment.length _ _ _
      hThroughCounter hPayload
  have hThroughFinish := workRunExact?_compose cnfWorkMachine
    ((assignment.length + 1) + assignment.length) 1 _ _ _
      hThroughPayload hFinish
  have hThroughBlank := workRunExact?_compose cnfWorkMachine
    (((assignment.length + 1) + assignment.length) + 1) 1 _ _ _
      hThroughFinish hBlank
  have hThroughGuard := workRunExact?_compose cnfWorkMachine
    ((((assignment.length + 1) + assignment.length) + 1) + 1) 1 _ _ _
      hThroughBlank hGuard
  have hThroughRestore := workRunExact?_compose cnfWorkMachine
    (((((assignment.length + 1) + assignment.length) + 1) + 1) + 1)
      assignment.length _ _ _ hThroughGuard hRestore
  exact workRunExact?_compose cnfWorkMachine
    ((((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
      assignment.length) 1 _ _ _ hThroughRestore hRestoreFinish

theorem frameOne_findCounter_t_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneFindCounter left
          (cnfT :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneToHeader
        (cnfMarkFalse :: left) suffix) := by
  rfl

theorem frameOne_toHeader_t_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneToHeader left
          (cnfT :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneToHeader
        (cnfT :: left) suffix) := by
  rfl

theorem frameOne_toHeader_finish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneToHeader left
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindPayload
        (cnfFinish :: left) suffix) := by
  rfl

theorem frameOne_findPayload_token_step
    (token : CNFToken) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneFindPayload left
          (token.workSymbol :: suffix)) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackPayload left
        (frameOneMarkedToken token :: suffix)) := by
  cases token <;> rfl

theorem frameOne_backPayload_finish_step
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneBackPayload
          (cnfFinish :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
        leftTail (cnfFinish :: right)) := by
  rfl

theorem frameOne_backHeader_counter_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : FrameOneBackCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
        leftTail (head :: right)) := by
  cases allowed <;> rfl

theorem frameOne_backHeader_root_step
    (right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
          [cnfRootGuard] right) =
      some (workConfigAtWord CNFWorkState.frameOneFindCounter
        [cnfRootGuard] right) := by
  rfl



theorem workRunExact?_scanLeft_cancel
    (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (workConfigAtLeftWord state (head :: leftTail) rightSide) =
        some (workConfigAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtLeftWord state (pushWorkLeft word leftSuffix) rightSide) =
      some (workConfigAtLeftWord state leftSuffix (word ++ rightSide)) := by
  have reversedAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft word []) → Allowed symbol := by
    intro symbol member
    apply pushWorkLeft_members_allowed Allowed word [] hAllowed
    · intro found impossible
      contradiction
    · exact member
  have scanned := workRunExact?_scanLeft machine state Allowed hStep
    (pushWorkLeft word []) leftSuffix rightSide reversedAllowed
  rw [pushWorkLeft_length] at scanned
  rw [pushWorkLeft_split_far]
  change workRunExact? machine word.length
      (workConfigAtLeftWord state
        (pushWorkLeft word [] ++ leftSuffix) rightSide) =
    some (workConfigAtLeftWord state leftSuffix
      (pushWorkLeft (pushWorkLeft word []) rightSide)) at scanned
  rw [pushWorkLeft_cancel] at scanned
  exact scanned

theorem frameOne_findPayload_marked_step
    (head : WorkSymbol) (left suffix : List WorkSymbol)
    (allowed : FrameOneMarkedSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameOneFindPayload left
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindPayload
        (head :: left) suffix) := by
  cases allowed <;> rfl

theorem frameOne_backPayload_marked_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : FrameOneMarkedSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameOneBackPayload
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackPayload
        leftTail (head :: right)) := by
  cases allowed <;> rfl

theorem frameOne_findCounter_markFalse_word_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameOneFindCounter left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindCounter
        (pushWorkLeft word left) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneFindCounter (fun symbol => symbol = cnfMarkFalse)
    _ word suffix left allowed
  intro stepLeft head stepSuffix equal
  cases equal
  exact frameOne_findCounter_markFalse_step stepLeft stepSuffix

theorem frameOne_toHeader_t_word_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfT) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameOneToHeader left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneToHeader
        (pushWorkLeft word left) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneToHeader (fun symbol => symbol = cnfT)
    _ word suffix left allowed
  intro stepLeft head stepSuffix equal
  cases equal
  exact frameOne_toHeader_t_step stepLeft stepSuffix

theorem frameOne_findPayload_marked_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      FrameOneMarkedSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameOneFindPayload left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameOneFindPayload
        (pushWorkLeft word left) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameOneFindPayload FrameOneMarkedSymbol
    (fun leftSide head stepSuffix headAllowed =>
      frameOne_findPayload_marked_step head leftSide stepSuffix headAllowed)
    word suffix left allowed

theorem frameOne_backPayload_marked_cancel
    (word leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      FrameOneMarkedSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.frameOneBackPayload
          (pushWorkLeft word leftSuffix) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackPayload
        leftSuffix (word ++ right)) :=
  workRunExact?_scanLeft_cancel cnfWorkMachine
    CNFWorkState.frameOneBackPayload FrameOneMarkedSymbol
    frameOne_backPayload_marked_step word leftSuffix right allowed

theorem frameCounter_symbols_allowed
    (done rest : List WorkSymbol)
    (doneAllowed : ∀ symbol, List.Mem symbol done →
      symbol = cnfMarkFalse)
    (restAllowed : ∀ symbol, List.Mem symbol rest → symbol = cnfT)
    (found : WorkSymbol)
    (member : List.Mem found (done ++ cnfMarkFalse :: rest)) :
    FrameOneBackCounterSymbol found := by
  induction done with
  | nil =>
      cases member with
      | head => exact .markFalse
      | tail _ tailMember =>
          have equal := restAllowed found tailMember
          cases equal
          exact .t
  | cons first tail ih =>
      cases member with
      | head =>
          have equal := doneAllowed found (List.Mem.head tail)
          cases equal
          exact .markFalse
      | tail _ tailMember =>
          apply ih
          · intro symbol foundTail
            exact doneAllowed symbol (List.Mem.tail _ foundTail)
          · exact tailMember

theorem frameOne_backHeader_fullCounter_cancel
    (counter right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol counter →
      FrameOneBackCounterSymbol symbol) :
    workRunExact? cnfWorkMachine counter.length
        (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
          (pushWorkLeft counter [cnfRootGuard]) right) =
      some (workConfigAtLeftWord CNFWorkState.frameOneBackHeader
        [cnfRootGuard] (counter ++ right)) :=
  workRunExact?_scanLeft_cancel cnfWorkMachine
    CNFWorkState.frameOneBackHeader FrameOneBackCounterSymbol
    frameOne_backHeader_counter_step counter [cnfRootGuard] right allowed

def frameOneIterationSteps
    (doneCounter restCounter donePayload : List WorkSymbol) : Nat :=
  (((((((((doneCounter.length + 1) + restCounter.length) + 1) +
    donePayload.length) + 1) + donePayload.length) + 1) +
    (doneCounter ++ cnfMarkFalse :: restCounter).length) + 1)

/-- General frame-one induction step.  It scans the already marked counter
and payload prefixes, marks exactly one new payload token, and returns to the
left guard with both prefixes extended by one cell. -/
theorem frameOne_iteration_exact
    (doneCounter restCounter donePayload : List WorkSymbol)
    (token : CNFToken) (payloadTail : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (restCounterAllowed : ∀ symbol, List.Mem symbol restCounter →
      symbol = cnfT)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      FrameOneMarkedSymbol symbol) :
    workRunExact? cnfWorkMachine
        (frameOneIterationSteps doneCounter restCounter donePayload)
        (workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
          (doneCounter ++ cnfT ::
            (restCounter ++ cnfFinish ::
              (donePayload ++ token.workSymbol :: payloadTail)))) =
      some
        (workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
          (doneCounter ++ cnfMarkFalse :: restCounter ++
            (cnfFinish :: donePayload ++
              frameOneMarkedToken token :: payloadTail))) := by
  unfold frameOneIterationSteps
  have hDoneCounter := frameOne_findCounter_markFalse_word_scan
    doneCounter [cnfRootGuard]
    (cnfT :: restCounter ++ cnfFinish ::
      (donePayload ++ token.workSymbol :: payloadTail)) doneCounterAllowed
  have hMarkCounter := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_findCounter_t_step (pushWorkLeft doneCounter [cnfRootGuard])
      (restCounter ++ cnfFinish ::
        (donePayload ++ token.workSymbol :: payloadTail)))
  have hRestCounter := frameOne_toHeader_t_word_scan restCounter
    (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard])
    (cnfFinish :: donePayload ++ token.workSymbol :: payloadTail)
    restCounterAllowed
  have hHeader := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_toHeader_finish_step
      (pushWorkLeft restCounter
        (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard]))
      (donePayload ++ token.workSymbol :: payloadTail))
  have hDonePayload := frameOne_findPayload_marked_scan donePayload
    (cnfFinish ::
      pushWorkLeft restCounter
        (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard]))
    (token.workSymbol :: payloadTail) donePayloadAllowed
  have hMarkPayload := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_findPayload_token_step token
      (pushWorkLeft donePayload
        (cnfFinish ::
          pushWorkLeft restCounter
            (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard])))
      payloadTail)
  have hBackPayload := frameOne_backPayload_marked_cancel donePayload
    (cnfFinish ::
      pushWorkLeft restCounter
        (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard]))
    (frameOneMarkedToken token :: payloadTail) donePayloadAllowed
  have hBackFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_backPayload_finish_step
      (pushWorkLeft restCounter
        (cnfMarkFalse :: pushWorkLeft doneCounter [cnfRootGuard]))
      (donePayload ++ frameOneMarkedToken token :: payloadTail))
  let fullCounter := doneCounter ++ cnfMarkFalse :: restCounter
  have hFullAllowed : ∀ symbol, List.Mem symbol fullCounter →
      FrameOneBackCounterSymbol symbol := by
    intro symbol member
    exact frameCounter_symbols_allowed doneCounter restCounter
      doneCounterAllowed restCounterAllowed symbol member
  have hBackCounter := frameOne_backHeader_fullCounter_cancel fullCounter
    (cnfFinish :: donePayload ++ frameOneMarkedToken token :: payloadTail)
    hFullAllowed
  unfold fullCounter at hBackCounter
  rw [pushWorkLeft_append] at hBackCounter
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_backHeader_root_step
      (doneCounter ++ cnfMarkFalse :: restCounter ++
        (cnfFinish :: donePayload ++
          frameOneMarkedToken token :: payloadTail)))
  have hThroughMarkCounter := workRunExact?_compose cnfWorkMachine
    doneCounter.length 1 _ _ _ hDoneCounter hMarkCounter
  have hThroughRestCounter := workRunExact?_compose cnfWorkMachine
    (doneCounter.length + 1) restCounter.length _ _ _
      hThroughMarkCounter hRestCounter
  have hThroughHeader := workRunExact?_compose cnfWorkMachine
    ((doneCounter.length + 1) + restCounter.length) 1 _ _ _
      hThroughRestCounter hHeader
  have hThroughDonePayload := workRunExact?_compose cnfWorkMachine
    (((doneCounter.length + 1) + restCounter.length) + 1)
    donePayload.length _ _ _ hThroughHeader hDonePayload
  have hThroughMarkPayload := workRunExact?_compose cnfWorkMachine
    ((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) 1 _ _ _ hThroughDonePayload hMarkPayload
  have hThroughBackPayload := workRunExact?_compose cnfWorkMachine
    (((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) donePayload.length _ _ _
      hThroughMarkPayload hBackPayload
  have hThroughBackFinish := workRunExact?_compose cnfWorkMachine
    ((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) 1 _ _ _
      hThroughBackPayload hBackFinish
  have hThroughBackCounter := workRunExact?_compose cnfWorkMachine
    (((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) + 1)
    (doneCounter ++ cnfMarkFalse :: restCounter).length _ _ _
      hThroughBackFinish hBackCounter
  exact workRunExact?_compose cnfWorkMachine
    ((((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) + 1) +
      (doneCounter ++ cnfMarkFalse :: restCounter).length) 1 _ _ _
      hThroughBackCounter hRoot

/-! ### Induction-ready frame-two iteration -/

theorem frameTwo_findCounter_markFalse_word_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindCounter
        (pushWorkLeft word left) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameTwoFindCounter (fun symbol => symbol = cnfMarkFalse)
    _ word suffix left allowed
  intro stepLeft head stepSuffix equal
  cases equal
  exact frameTwo_findCounter_markFalse_step stepLeft stepSuffix

theorem frameTwo_toHeader_t_word_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfT) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameTwoToHeader left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoToHeader
        (pushWorkLeft word left) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameTwoToHeader (fun symbol => symbol = cnfT)
    _ word suffix left allowed
  intro stepLeft head stepSuffix equal
  cases equal
  exact frameTwo_toHeader_t_step stepLeft stepSuffix

theorem frameTwo_findPayload_marked_step
    (head : WorkSymbol) (left suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.frameTwoFindPayload left
          (head :: suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindPayload
        (head :: left) suffix) := by
  cases allowed <;> rfl

theorem frameTwo_findPayload_marked_scan
    (word left suffix : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.frameTwoFindPayload left
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.frameTwoFindPayload
        (pushWorkLeft word left) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.frameTwoFindPayload AssignmentMarkSymbol
    (fun leftSide head stepSuffix headAllowed =>
      frameTwo_findPayload_marked_step head leftSide stepSuffix headAllowed)
    word suffix left allowed

theorem frameTwo_backPayload_marked_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload
          (head :: leftTail) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload
        leftTail (head :: right)) := by
  cases allowed <;> rfl

theorem frameTwo_backPayload_marked_cancel
    (word leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload
          (pushWorkLeft word leftSuffix) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackPayload
        leftSuffix (word ++ right)) :=
  workRunExact?_scanLeft_cancel cnfWorkMachine
    CNFWorkState.frameTwoBackPayload AssignmentMarkSymbol
    frameTwo_backPayload_marked_step word leftSuffix right allowed

theorem frameTwo_backHeader_fullCounter_cancel
    (counter leftBase right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol counter →
      FrameOneBackCounterSymbol symbol) :
    workRunExact? cnfWorkMachine counter.length
        (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
          (pushWorkLeft counter (cnfBoundaryGuard :: leftBase)) right) =
      some (workConfigAtLeftWord CNFWorkState.frameTwoBackHeader
        (cnfBoundaryGuard :: leftBase) (counter ++ right)) :=
  workRunExact?_scanLeft_cancel cnfWorkMachine
    CNFWorkState.frameTwoBackHeader FrameOneBackCounterSymbol
    frameTwo_backHeader_counter_step counter
      (cnfBoundaryGuard :: leftBase) right allowed

theorem frameTwo_iteration_exact
    (doneCounter restCounter donePayload leftBase : List WorkSymbol)
    (value : Bool) (payloadTail : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (restCounterAllowed : ∀ symbol, List.Mem symbol restCounter →
      symbol = cnfT)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (frameOneIterationSteps doneCounter restCounter donePayload)
        (workConfigAtWord CNFWorkState.frameTwoFindCounter
          (cnfBoundaryGuard :: leftBase)
          (doneCounter ++ cnfT ::
            (restCounter ++ cnfFinish ::
              (donePayload ++ assignmentValueWorkSymbol value ::
                payloadTail)))) =
      some
        (workConfigAtWord CNFWorkState.frameTwoFindCounter
          (cnfBoundaryGuard :: leftBase)
          (doneCounter ++ cnfMarkFalse :: restCounter ++
            (cnfFinish :: donePayload ++
              markedAssignmentValueWorkSymbol value :: payloadTail))) := by
  unfold frameOneIterationSteps
  have hDoneCounter := frameTwo_findCounter_markFalse_word_scan
    doneCounter (cnfBoundaryGuard :: leftBase)
    (cnfT :: restCounter ++ cnfFinish ::
      (donePayload ++ assignmentValueWorkSymbol value :: payloadTail))
    doneCounterAllowed
  have hMarkCounter := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_findCounter_t_step
      (pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase))
      (restCounter ++ cnfFinish ::
        (donePayload ++ assignmentValueWorkSymbol value :: payloadTail)))
  have hRestCounter := frameTwo_toHeader_t_word_scan restCounter
    (cnfMarkFalse ::
      pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase))
    (cnfFinish :: donePayload ++
      assignmentValueWorkSymbol value :: payloadTail) restCounterAllowed
  have hHeader := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_toHeader_finish_step
      (pushWorkLeft restCounter
        (cnfMarkFalse ::
          pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase)))
      (donePayload ++ assignmentValueWorkSymbol value :: payloadTail))
  have hDonePayload := frameTwo_findPayload_marked_scan donePayload
    (cnfFinish ::
      pushWorkLeft restCounter
        (cnfMarkFalse ::
          pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase)))
    (assignmentValueWorkSymbol value :: payloadTail) donePayloadAllowed
  have hMarkPayload := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_findPayload_value_step value
      (pushWorkLeft donePayload
        (cnfFinish ::
          pushWorkLeft restCounter
            (cnfMarkFalse ::
              pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase))))
      payloadTail)
  have hBackPayload := frameTwo_backPayload_marked_cancel donePayload
    (cnfFinish ::
      pushWorkLeft restCounter
        (cnfMarkFalse ::
          pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase)))
    (markedAssignmentValueWorkSymbol value :: payloadTail)
    donePayloadAllowed
  have hBackFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_backPayload_finish_step
      (pushWorkLeft restCounter
        (cnfMarkFalse ::
          pushWorkLeft doneCounter (cnfBoundaryGuard :: leftBase)))
      (donePayload ++ markedAssignmentValueWorkSymbol value :: payloadTail))
  let fullCounter := doneCounter ++ cnfMarkFalse :: restCounter
  have hFullAllowed : ∀ symbol, List.Mem symbol fullCounter →
      FrameOneBackCounterSymbol symbol := by
    intro symbol member
    exact frameCounter_symbols_allowed doneCounter restCounter
      doneCounterAllowed restCounterAllowed symbol member
  have hBackCounter := frameTwo_backHeader_fullCounter_cancel fullCounter
    leftBase
    (cnfFinish :: donePayload ++
      markedAssignmentValueWorkSymbol value :: payloadTail) hFullAllowed
  unfold fullCounter at hBackCounter
  rw [pushWorkLeft_append] at hBackCounter
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_backHeader_boundary_step leftBase
      (doneCounter ++ cnfMarkFalse :: restCounter ++
        (cnfFinish :: donePayload ++
          markedAssignmentValueWorkSymbol value :: payloadTail)))
  have hThroughMarkCounter := workRunExact?_compose cnfWorkMachine
    doneCounter.length 1 _ _ _ hDoneCounter hMarkCounter
  have hThroughRestCounter := workRunExact?_compose cnfWorkMachine
    (doneCounter.length + 1) restCounter.length _ _ _
      hThroughMarkCounter hRestCounter
  have hThroughHeader := workRunExact?_compose cnfWorkMachine
    ((doneCounter.length + 1) + restCounter.length) 1 _ _ _
      hThroughRestCounter hHeader
  have hThroughDonePayload := workRunExact?_compose cnfWorkMachine
    (((doneCounter.length + 1) + restCounter.length) + 1)
    donePayload.length _ _ _ hThroughHeader hDonePayload
  have hThroughMarkPayload := workRunExact?_compose cnfWorkMachine
    ((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) 1 _ _ _ hThroughDonePayload hMarkPayload
  have hThroughBackPayload := workRunExact?_compose cnfWorkMachine
    (((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) donePayload.length _ _ _
      hThroughMarkPayload hBackPayload
  have hThroughBackFinish := workRunExact?_compose cnfWorkMachine
    ((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) 1 _ _ _
      hThroughBackPayload hBackFinish
  have hThroughBackCounter := workRunExact?_compose cnfWorkMachine
    (((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) + 1)
    (doneCounter ++ cnfMarkFalse :: restCounter).length _ _ _
      hThroughBackFinish hBackCounter
  exact workRunExact?_compose cnfWorkMachine
    ((((((((doneCounter.length + 1) + restCounter.length) + 1) +
      donePayload.length) + 1) + donePayload.length) + 1) +
      (doneCounter ++ cnfMarkFalse :: restCounter).length) 1 _ _ _
      hThroughBackCounter hBoundary

/-! ### Raw decoder split and canonical tape bridge -/

theorem rawCNFDecoder_split (input certificate : BitString) :
    (decodeEncodedCNF input = none) ∨
      (∃ formula,
        decodeEncodedCNF input = some formula ∧
          decodeAssignmentCertificate certificate = none) ∨
      (∃ formula assignment,
        decodeEncodedCNF input = some formula ∧
          decodeAssignmentCertificate certificate = some assignment) := by
  cases hFormula : decodeEncodedCNF input with
  | none => exact Or.inl rfl
  | some formula =>
      cases hAssignment : decodeAssignmentCertificate certificate with
      | none => exact Or.inr (Or.inl ⟨formula, rfl, rfl⟩)
      | some assignment =>
          exact Or.inr (Or.inr
            ⟨formula, assignment, rfl, rfl⟩)

theorem checkEncodedCertificate_false_of_decoder_failure
    (input certificate : BitString)
    (failure : decodeEncodedCNF input = none ∨
      decodeAssignmentCertificate certificate = none) :
    checkEncodedCertificate input certificate = false := by
  cases failure with
  | inl formulaFailure =>
      unfold checkEncodedCertificate
      rw [formulaFailure]
  | inr assignmentFailure =>
      unfold checkEncodedCertificate
      cases hFormula : decodeEncodedCNF input with
      | none => rfl
      | some formula => rw [assignmentFailure]

/-- Successful strict decoders identify the raw paired tape with the exact
canonical token layout used by the positive frame traces. -/
theorem pairedWorkTape_of_decoders_some
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    pairedWorkTape input certificate =
      WorkTape.ofSymbols
        (pairedTokenLayout (encodeFormulaTokens formula)
          (assignmentValueTokens assignment)) := by
  have formulaShape := encodeFormula_of_decode input formula formulaDecoded
  have assignmentShape := encodeAssignmentCertificate_of_decode
    certificate assignment assignmentDecoded
  rw [← formulaShape, ← assignmentShape]
  exact pairedWorkTape_encoded_cnf_assignment formula assignment

/-! ### Recursive successful frame composition -/

theorem frameWork_append_assoc
    (left middle right : List WorkSymbol) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

theorem frameAllowed_append_one (Allowed : WorkSymbol → Prop)
    (word : List WorkSymbol) (last : WorkSymbol)
    (wordAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol)
    (lastAllowed : Allowed last) :
    ∀ symbol, List.Mem symbol (word ++ [last]) → Allowed symbol := by
  induction word with
  | nil =>
      intro symbol member
      cases member with
      | head => exact lastAllowed
      | tail _ tailMember => contradiction
  | cons head tail ih =>
      intro symbol member
      cases member with
      | head => exact wordAllowed head (List.Mem.head tail)
      | tail _ tailMember =>
          exact ih
            (fun found foundMember =>
              wordAllowed found (List.Mem.tail head foundMember))
            symbol tailMember

theorem replicate_bit_cons_length (value : Bool) (rest : BitString)
    (symbol : WorkSymbol) :
    List.replicate (value :: rest).length symbol =
      symbol :: List.replicate rest.length symbol := by
  rfl

def frameOneFoldStart (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (suffix : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
    ((doneCounter ++ List.replicate tokens.length cnfT) ++
      cnfFinish ::
        ((donePayload ++ cnfTokenWorkSymbols tokens) ++ cnfSep :: suffix))

def frameOneFoldFinal (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (suffix : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
    ((doneCounter ++ List.replicate tokens.length cnfMarkFalse) ++
      cnfFinish ::
        ((donePayload ++ frameOneMarkedTokens tokens) ++ cnfSep :: suffix))

def frameOneFoldSteps :
    List WorkSymbol → List WorkSymbol → List CNFToken → Nat
  | _, _, [] => 0
  | doneCounter, donePayload, token :: rest =>
      frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT) donePayload +
        frameOneFoldSteps (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [frameOneMarkedToken token]) rest

theorem frameOneFoldStart_cons
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (suffix : List WorkSymbol) :
    frameOneFoldStart doneCounter donePayload (token :: rest) suffix =
      workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
        (doneCounter ++ cnfT ::
          (List.replicate rest.length cnfT ++ cnfFinish ::
            (donePayload ++ token.workSymbol ::
              (cnfTokenWorkSymbols rest ++ cnfSep :: suffix)))) := by
  unfold frameOneFoldStart
  change workConfigAtWord _ _
      ((doneCounter ++ cnfT :: List.replicate rest.length cnfT) ++
        cnfFinish ::
          ((donePayload ++ token.workSymbol :: cnfTokenWorkSymbols rest) ++
            cnfSep :: suffix)) = _
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOneFold_after_iteration
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (suffix : List WorkSymbol) :
    workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
        ((doneCounter ++ cnfMarkFalse ::
          List.replicate rest.length cnfT) ++
            (cnfFinish :: donePayload ++ frameOneMarkedToken token ::
              (cnfTokenWorkSymbols rest ++ cnfSep :: suffix))) =
      frameOneFoldStart (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token]) rest suffix := by
  unfold frameOneFoldStart
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOneFoldFinal_cons
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (suffix : List WorkSymbol) :
    frameOneFoldFinal (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token]) rest suffix =
      frameOneFoldFinal doneCounter donePayload (token :: rest) suffix := by
  unfold frameOneFoldFinal
  change workConfigAtWord _ _
      (((doneCounter ++ [cnfMarkFalse]) ++
          List.replicate rest.length cnfMarkFalse) ++
        cnfFinish ::
          (((donePayload ++ [frameOneMarkedToken token]) ++
              frameOneMarkedTokens rest) ++ cnfSep :: suffix)) =
    workConfigAtWord _ _
      ((doneCounter ++ cnfMarkFalse ::
          List.replicate rest.length cnfMarkFalse) ++
        cnfFinish ::
          ((donePayload ++ frameOneMarkedToken token ::
              frameOneMarkedTokens rest) ++ cnfSep :: suffix))
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOne_fold_exact
    (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (suffix : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      FrameOneMarkedSymbol symbol) :
    workRunExact? cnfWorkMachine
        (frameOneFoldSteps doneCounter donePayload tokens)
        (frameOneFoldStart doneCounter donePayload tokens suffix) =
      some (frameOneFoldFinal doneCounter donePayload tokens suffix) := by
  induction tokens generalizing doneCounter donePayload with
  | nil => rfl
  | cons token rest ih =>
      have restCounterAllowed : ∀ symbol,
          List.Mem symbol (List.replicate rest.length cnfT) →
            symbol = cnfT := by
        intro symbol member
        exact mem_replicate_workSymbol_eq rest.length cnfT symbol member
      have hIteration := frameOne_iteration_exact doneCounter
        (List.replicate rest.length cnfT) donePayload token
        (cnfTokenWorkSymbols rest ++ cnfSep :: suffix)
        doneCounterAllowed restCounterAllowed donePayloadAllowed
      rw [← frameOneFoldStart_cons] at hIteration
      have nextCounterAllowed : ∀ symbol,
          List.Mem symbol (doneCounter ++ [cnfMarkFalse]) →
            symbol = cnfMarkFalse := by
        exact frameAllowed_append_one
          (fun candidate => candidate = cnfMarkFalse)
          doneCounter cnfMarkFalse doneCounterAllowed rfl
      have nextPayloadAllowed : ∀ symbol,
          List.Mem symbol (donePayload ++ [frameOneMarkedToken token]) →
            FrameOneMarkedSymbol symbol := by
        exact frameAllowed_append_one FrameOneMarkedSymbol donePayload
          (frameOneMarkedToken token) donePayloadAllowed (by
            cases token <;> constructor)
      have hRest := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token])
        nextCounterAllowed nextPayloadAllowed
      rw [← frameOneFold_after_iteration] at hRest
      rw [frameOneFoldFinal_cons] at hRest
      exact workRunExact?_compose cnfWorkMachine
        (frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT) donePayload)
        (frameOneFoldSteps (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [frameOneMarkedToken token]) rest)
        _ _ _ hIteration hRest

def frameTwoFoldStart (doneCounter donePayload : List WorkSymbol)
    (assignment : BitString) (leftBase : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameTwoFindCounter
    (cnfBoundaryGuard :: leftBase)
    ((doneCounter ++ List.replicate assignment.length cnfT) ++
      cnfFinish ::
        ((donePayload ++ assignmentWorkSymbols assignment) ++ [cnfFinish]))

def frameTwoFoldFinal (doneCounter donePayload : List WorkSymbol)
    (assignment : BitString) (leftBase : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameTwoFindCounter
    (cnfBoundaryGuard :: leftBase)
    ((doneCounter ++ List.replicate assignment.length cnfMarkFalse) ++
      cnfFinish ::
        ((donePayload ++ markedAssignmentWorkSymbols assignment) ++
          [cnfFinish]))

def frameTwoFoldSteps :
    List WorkSymbol → List WorkSymbol → BitString → Nat
  | _, _, [] => 0
  | doneCounter, donePayload, value :: rest =>
      frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT) donePayload +
        frameTwoFoldSteps (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest

theorem frameTwoFoldStart_cons
    (doneCounter donePayload : List WorkSymbol)
    (value : Bool) (rest : BitString) (leftBase : List WorkSymbol) :
    frameTwoFoldStart doneCounter donePayload (value :: rest) leftBase =
      workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase)
        (doneCounter ++ cnfT ::
          (List.replicate rest.length cnfT ++ cnfFinish ::
            (donePayload ++ assignmentValueWorkSymbol value ::
              (assignmentWorkSymbols rest ++ [cnfFinish])))) := by
  unfold frameTwoFoldStart
  rw [replicate_bit_cons_length]
  rw [assignmentWorkSymbols_cons]
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameTwoFold_after_iteration
    (doneCounter donePayload : List WorkSymbol)
    (value : Bool) (rest : BitString) (leftBase : List WorkSymbol) :
    workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase)
        ((doneCounter ++ cnfMarkFalse ::
          List.replicate rest.length cnfT) ++
            (cnfFinish :: donePayload ++
              markedAssignmentValueWorkSymbol value ::
                (assignmentWorkSymbols rest ++ [cnfFinish]))) =
      frameTwoFoldStart (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest
        leftBase := by
  unfold frameTwoFoldStart
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameTwoFoldFinal_cons
    (doneCounter donePayload : List WorkSymbol)
    (value : Bool) (rest : BitString) (leftBase : List WorkSymbol) :
    frameTwoFoldFinal (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest
        leftBase =
      frameTwoFoldFinal doneCounter donePayload (value :: rest) leftBase := by
  unfold frameTwoFoldFinal
  rw [replicate_bit_cons_length]
  rw [markedAssignmentWorkSymbols_cons]
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameTwo_fold_exact
    (doneCounter donePayload : List WorkSymbol)
    (assignment : BitString) (leftBase : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (frameTwoFoldSteps doneCounter donePayload assignment)
        (frameTwoFoldStart doneCounter donePayload assignment leftBase) =
      some (frameTwoFoldFinal doneCounter donePayload assignment leftBase) := by
  induction assignment generalizing doneCounter donePayload with
  | nil => rfl
  | cons value rest ih =>
      have restCounterAllowed : ∀ symbol,
          List.Mem symbol (List.replicate rest.length cnfT) →
            symbol = cnfT := by
        intro symbol member
        exact mem_replicate_workSymbol_eq rest.length cnfT symbol member
      have hIteration := frameTwo_iteration_exact doneCounter
        (List.replicate rest.length cnfT) donePayload leftBase value
        (assignmentWorkSymbols rest ++ [cnfFinish])
        doneCounterAllowed restCounterAllowed donePayloadAllowed
      rw [← frameTwoFoldStart_cons] at hIteration
      have nextCounterAllowed : ∀ symbol,
          List.Mem symbol (doneCounter ++ [cnfMarkFalse]) →
            symbol = cnfMarkFalse :=
        frameAllowed_append_one
          (fun candidate => candidate = cnfMarkFalse)
          doneCounter cnfMarkFalse doneCounterAllowed rfl
      have nextPayloadAllowed : ∀ symbol,
          List.Mem symbol
            (donePayload ++ [markedAssignmentValueWorkSymbol value]) →
              AssignmentMarkSymbol symbol :=
        frameAllowed_append_one AssignmentMarkSymbol donePayload
          (markedAssignmentValueWorkSymbol value) donePayloadAllowed (by
            cases value <;> constructor)
      have hRest := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value])
        nextCounterAllowed nextPayloadAllowed
      rw [← frameTwoFold_after_iteration] at hRest
      rw [frameTwoFoldFinal_cons] at hRest
      exact workRunExact?_compose cnfWorkMachine
        (frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT) donePayload)
        (frameTwoFoldSteps (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest)
        _ _ _ hIteration hRest

def frameOneTerminalSteps (tokens : List CNFToken) : Nat :=
  (((((((tokens.length + 1) + tokens.length) + 1) +
    tokens.length) + 1) + tokens.length) + 1)

def frameTwoTerminalSteps (assignment : BitString) : Nat :=
  (((((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
    assignment.length) + 1)

theorem frameOne_complete_exact
    (tokens : List CNFToken) (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (frameOneFoldSteps [] [] tokens + frameOneTerminalSteps tokens)
        (frameOneFoldStart [] [] tokens suffix) =
      some
        (workConfigAtWord CNFWorkState.frameTwoFindCounter
          (cnfBoundaryGuard ::
            pushWorkLeft (cnfTokenWorkSymbols tokens)
              (cnfFinish ::
                pushWorkLeft
                  (List.replicate tokens.length cnfMarkFalse)
                  [cnfRootGuard]))
          suffix) := by
  have hFold := frameOne_fold_exact [] [] tokens suffix
    (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
  unfold frameOneFoldFinal at hFold
  have hTerminal := frameOne_terminal_exact tokens suffix
  unfold frameOneTerminalSteps
  exact workRunExact?_compose cnfWorkMachine
    (frameOneFoldSteps [] [] tokens)
    (((((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1) +
      tokens.length) + 1) _ _ _ hFold hTerminal

theorem frameTwo_complete_exact
    (assignment : BitString) (leftBase : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (frameTwoFoldSteps [] [] assignment +
          frameTwoTerminalSteps assignment)
        (frameTwoFoldStart [] [] assignment leftBase) =
      some
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft
            (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase))
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank]))) := by
  have hFold := frameTwo_fold_exact [] [] assignment leftBase
    (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
  unfold frameTwoFoldFinal at hFold
  have hTerminal := frameTwo_terminal_exact assignment leftBase
  unfold frameTwoTerminalSteps
  exact workRunExact?_compose cnfWorkMachine
    (frameTwoFoldSteps [] [] assignment)
    (((((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
      assignment.length) + 1) _ _ _ hFold hTerminal

def frameFormulaLeftBase (tokens : List CNFToken) : List WorkSymbol :=
  pushWorkLeft (cnfTokenWorkSymbols tokens)
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])

def frameAssignmentSuffix (assignment : BitString) : List WorkSymbol :=
  List.replicate assignment.length cnfT ++
    cnfFinish :: (assignmentWorkSymbols assignment ++ [cnfFinish])

def frameSuccessSteps (tokens : List CNFToken)
    (assignment : BitString) : Nat :=
  (2 + (frameOneFoldSteps [] [] tokens + frameOneTerminalSteps tokens)) +
    (frameTwoFoldSteps [] [] assignment + frameTwoTerminalSteps assignment)

theorem frameOneFoldStart_empty_cons
    (first : CNFToken) (rest : List CNFToken)
    (suffix : List WorkSymbol) :
    frameOneFoldStart [] [] (first :: rest) suffix =
      workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
        (cnfT ::
          (List.replicate rest.length cnfT ++
            cnfFinish :: first.workSymbol ::
              (cnfTokenWorkSymbols rest ++ cnfSep :: suffix))) := by
  rw [frameOneFoldStart_cons]
  rfl

theorem frameTwoFoldStart_empty
    (assignment : BitString) (leftBase : List WorkSymbol) :
    frameTwoFoldStart [] [] assignment leftBase =
      workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase) (frameAssignmentSuffix assignment) := by
  unfold frameTwoFoldStart frameAssignmentSuffix
  rfl

theorem frames_success_exact
    (first : CNFToken) (formulaRest : List CNFToken)
    (assignment : BitString) :
    workRunExact? cnfWorkMachine
        (frameSuccessSteps (first :: formulaRest) assignment)
        (workStartConfiguration cnfWorkMachine
          (WorkTape.ofSymbols
            (pairedTokenLayout (first :: formulaRest)
              (assignmentValueTokens assignment)))) =
      some
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft
            (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard ::
              frameFormulaLeftBase (first :: formulaRest)))
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank]))) := by
  have hBoot := boot_nonempty_formula_exact first formulaRest
    (assignmentValueTokens assignment)
  rw [assignmentValueTokens_length] at hBoot
  rw [assignmentValueTokens_workSymbols] at hBoot
  have hFrameOne := frameOne_complete_exact (first :: formulaRest)
    (List.replicate assignment.length cnfT ++
      cnfFinish :: (assignmentWorkSymbols assignment ++ [cnfFinish]))
  rw [frameOneFoldStart_empty_cons] at hFrameOne
  unfold frameFormulaLeftBase
  have hFrameTwo := frameTwo_complete_exact assignment
    (pushWorkLeft (cnfTokenWorkSymbols (first :: formulaRest))
      (cnfFinish ::
        pushWorkLeft
          (List.replicate (first :: formulaRest).length cnfMarkFalse)
          [cnfRootGuard]))
  rw [frameTwoFoldStart_empty] at hFrameTwo
  have hBootFrameOne := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest))
    _ _ _ hBoot hFrameOne
  unfold frameSuccessSteps
  exact workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: formulaRest) +
      frameOneTerminalSteps (first :: formulaRest)))
    (frameTwoFoldSteps [] [] assignment +
      frameTwoTerminalSteps assignment)
    _ _ _ hBootFrameOne hFrameTwo

theorem encodeFormulaTokens_cons (formula : CNFFormula) :
    ∃ first rest, encodeFormulaTokens formula = first :: rest := by
  unfold encodeFormulaTokens encodeCNFTokens
  cases formula.variableCount with
  | zero =>
      exact ⟨CNFToken.f,
        encodeClauseListTokens formula.clauses ++ [.finish], rfl⟩
  | succ count =>
      exact ⟨CNFToken.t,
        encodeUnaryTokens count ++
          encodeClauseListTokens formula.clauses ++ [.finish], rfl⟩

/-- Successful strict decoders drive both self-delimiting frame validators
to the exact restored semantic tape in `seekLeftRoot`. -/
theorem decoded_frames_success_exact
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    workRunExact? cnfWorkMachine
        (frameSuccessSteps (encodeFormulaTokens formula) assignment)
        (workStartConfiguration cnfWorkMachine
          (pairedWorkTape input certificate)) =
      some
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft
            (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard ::
              frameFormulaLeftBase (encodeFormulaTokens formula)))
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank]))) := by
  rw [pairedWorkTape_of_decoders_some input certificate formula assignment
    formulaDecoded assignmentDecoded]
  rcases encodeFormulaTokens_cons formula with ⟨first, rest, shape⟩
  rw [shape]
  exact frames_success_exact first rest assignment

theorem frame_length_append (left right : List WorkSymbol) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons symbol rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem frameIterationSteps_le_twelveSpan (n : Nat)
    (doneCounter restCounter donePayload : List WorkSymbol)
    (doneBound : doneCounter.length ≤ n)
    (restBound : restCounter.length ≤ n)
    (payloadBound : donePayload.length ≤ n) :
    frameOneIterationSteps doneCounter restCounter donePayload ≤
      cnfShiftedWorkSpan n * 12 := by
  let span := cnfShiftedWorkSpan n
  have nSpan : n ≤ span := by
    unfold span cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have oneSpan : 1 ≤ span := by
    unfold span cnfShiftedWorkSpan
    exact Nat.succ_le_succ (Nat.zero_le (n + 1))
  have doneSpan : doneCounter.length ≤ span :=
    Nat.le_trans doneBound nSpan
  have restSpan : restCounter.length ≤ span :=
    Nat.le_trans restBound nSpan
  have payloadSpan : donePayload.length ≤ span :=
    Nat.le_trans payloadBound nSpan
  have restOne : restCounter.length + 1 ≤ span + span :=
    Nat.add_le_add restSpan oneSpan
  have fullRaw : doneCounter.length + (restCounter.length + 1) ≤
      span + (span + span) := Nat.add_le_add doneSpan restOne
  have fullBound : (doneCounter ++ cnfMarkFalse :: restCounter).length ≤
      (span + span) + span := by
    rw [frame_length_append]
    exact Nat.le_trans fullRaw
      (Nat.le_of_eq (Nat.add_assoc span span span).symm)
  have h0 := Nat.add_le_add doneSpan oneSpan
  have h1 := Nat.add_le_add h0 restSpan
  have h2 := Nat.add_le_add h1 oneSpan
  have h3 := Nat.add_le_add h2 payloadSpan
  have h4 := Nat.add_le_add h3 oneSpan
  have h5 := Nat.add_le_add h4 payloadSpan
  have h6 := Nat.add_le_add h5 oneSpan
  have h7 := Nat.add_le_add h6 fullBound
  have h8 := Nat.add_le_add h7 oneSpan
  unfold frameOneIterationSteps
  unfold span at h8
  repeat' rw [← Nat.add_assoc] at h8
  have twelve :
      cnfShiftedWorkSpan n + cnfShiftedWorkSpan n +
                    cnfShiftedWorkSpan n + cnfShiftedWorkSpan n +
                  cnfShiftedWorkSpan n + cnfShiftedWorkSpan n +
                cnfShiftedWorkSpan n + cnfShiftedWorkSpan n +
              cnfShiftedWorkSpan n + cnfShiftedWorkSpan n +
            cnfShiftedWorkSpan n + cnfShiftedWorkSpan n =
        cnfShiftedWorkSpan n * 12 := by
    repeat' rw [Nat.mul_succ]
    rw [Nat.mul_zero, Nat.zero_add]
  exact Nat.le_trans h8 (Nat.le_of_eq twelve)

theorem frameOneFoldSteps_le (n : Nat)
    (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken)
    (counterPartition : doneCounter.length + tokens.length ≤ n)
    (payloadPartition : donePayload.length + tokens.length ≤ n) :
    frameOneFoldSteps doneCounter donePayload tokens ≤
      tokens.length * (cnfShiftedWorkSpan n * 12) := by
  induction tokens generalizing doneCounter donePayload with
  | nil => exact Nat.zero_le _
  | cons token rest ih =>
      have doneBound : doneCounter.length ≤ n :=
        Nat.le_trans (Nat.le_add_right doneCounter.length (token :: rest).length)
          counterPartition
      have payloadBound : donePayload.length ≤ n :=
        Nat.le_trans (Nat.le_add_right donePayload.length (token :: rest).length)
          payloadPartition
      have restBound : rest.length ≤ n := by
        have restToTokens : rest.length ≤ (token :: rest).length :=
          Nat.le_succ rest.length
        have tokensToCounter : (token :: rest).length ≤
            doneCounter.length + (token :: rest).length :=
          Nat.le_add_left (token :: rest).length doneCounter.length
        exact Nat.le_trans (Nat.le_trans restToTokens tokensToCounter)
          counterPartition
      have iterationBound := frameIterationSteps_le_twelveSpan n
        doneCounter (List.replicate rest.length cnfT) donePayload
        doneBound (by
          rw [length_replicate_workSymbol]
          exact restBound) payloadBound
      have nextCounterPartition :
          (doneCounter ++ [cnfMarkFalse]).length + rest.length ≤ n := by
        rw [frame_length_append]
        exact Nat.le_trans
          (Nat.le_of_eq (nat_add_succ_shift doneCounter.length rest.length))
          counterPartition
      have nextPayloadPartition :
          (donePayload ++ [frameOneMarkedToken token]).length +
              rest.length ≤ n := by
        rw [frame_length_append]
        exact Nat.le_trans
          (Nat.le_of_eq (nat_add_succ_shift donePayload.length rest.length))
          payloadPartition
      have restFold := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token])
        nextCounterPartition nextPayloadPartition
      have combined := Nat.add_le_add iterationBound restFold
      have normalized :
          cnfShiftedWorkSpan n * 12 +
              rest.length * (cnfShiftedWorkSpan n * 12) =
            (token :: rest).length * (cnfShiftedWorkSpan n * 12) := by
        rw [Nat.add_comm]
        exact (Nat.succ_mul rest.length
          (cnfShiftedWorkSpan n * 12)).symm
      exact Nat.le_trans combined (Nat.le_of_eq normalized)

theorem frameTwoFoldSteps_le (n : Nat)
    (doneCounter donePayload : List WorkSymbol)
    (assignment : BitString)
    (counterPartition : doneCounter.length + assignment.length ≤ n)
    (payloadPartition : donePayload.length + assignment.length ≤ n) :
    frameTwoFoldSteps doneCounter donePayload assignment ≤
      assignment.length * (cnfShiftedWorkSpan n * 12) := by
  induction assignment generalizing doneCounter donePayload with
  | nil => exact Nat.zero_le _
  | cons value rest ih =>
      have doneBound : doneCounter.length ≤ n :=
        Nat.le_trans
          (Nat.le_add_right doneCounter.length (value :: rest).length)
          counterPartition
      have payloadBound : donePayload.length ≤ n :=
        Nat.le_trans
          (Nat.le_add_right donePayload.length (value :: rest).length)
          payloadPartition
      have restBound : rest.length ≤ n := by
        have restToAssignment : rest.length ≤ (value :: rest).length :=
          Nat.le_succ rest.length
        have assignmentToCounter : (value :: rest).length ≤
            doneCounter.length + (value :: rest).length :=
          Nat.le_add_left (value :: rest).length doneCounter.length
        exact Nat.le_trans (Nat.le_trans restToAssignment assignmentToCounter)
          counterPartition
      have iterationBound := frameIterationSteps_le_twelveSpan n
        doneCounter (List.replicate rest.length cnfT) donePayload
        doneBound (by
          rw [length_replicate_workSymbol]
          exact restBound) payloadBound
      have nextCounterPartition :
          (doneCounter ++ [cnfMarkFalse]).length + rest.length ≤ n := by
        rw [frame_length_append]
        exact Nat.le_trans
          (Nat.le_of_eq (nat_add_succ_shift doneCounter.length rest.length))
          counterPartition
      have nextPayloadPartition :
          (donePayload ++ [markedAssignmentValueWorkSymbol value]).length +
              rest.length ≤ n := by
        rw [frame_length_append]
        exact Nat.le_trans
          (Nat.le_of_eq (nat_add_succ_shift donePayload.length rest.length))
          payloadPartition
      have restFold := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value])
        nextCounterPartition nextPayloadPartition
      have combined := Nat.add_le_add iterationBound restFold
      have normalized :
          cnfShiftedWorkSpan n * 12 +
              rest.length * (cnfShiftedWorkSpan n * 12) =
            (value :: rest).length * (cnfShiftedWorkSpan n * 12) := by
        rw [Nat.add_comm]
        exact (Nat.succ_mul rest.length
          (cnfShiftedWorkSpan n * 12)).symm
      exact Nat.le_trans combined (Nat.le_of_eq normalized)

theorem eight_span_normalize (span : Nat) :
    span + span + span + span + span + span + span + span =
      span * 8 := by
  repeat' rw [Nat.mul_succ]
  rw [Nat.mul_zero, Nat.zero_add]

theorem frameOneTerminalSteps_le (n : Nat) (tokens : List CNFToken)
    (tokenBound : tokens.length ≤ n) :
    frameOneTerminalSteps tokens ≤ cnfShiftedWorkSpan n * 8 := by
  have nSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have tokenSpan : tokens.length ≤ cnfShiftedWorkSpan n :=
    Nat.le_trans tokenBound nSpan
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.succ_le_succ (Nat.zero_le (n + 1))
  have h0 := Nat.add_le_add tokenSpan oneSpan
  have h1 := Nat.add_le_add h0 tokenSpan
  have h2 := Nat.add_le_add h1 oneSpan
  have h3 := Nat.add_le_add h2 tokenSpan
  have h4 := Nat.add_le_add h3 oneSpan
  have h5 := Nat.add_le_add h4 tokenSpan
  have h6 := Nat.add_le_add h5 oneSpan
  unfold frameOneTerminalSteps
  repeat' rw [← Nat.add_assoc] at h6
  exact Nat.le_trans h6
    (Nat.le_of_eq (eight_span_normalize (cnfShiftedWorkSpan n)))

theorem frameTwoTerminalSteps_le (n : Nat) (assignment : BitString)
    (assignmentBound : assignment.length ≤ n) :
    frameTwoTerminalSteps assignment ≤ cnfShiftedWorkSpan n * 8 := by
  have nSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have assignmentSpan : assignment.length ≤ cnfShiftedWorkSpan n :=
    Nat.le_trans assignmentBound nSpan
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.succ_le_succ (Nat.zero_le (n + 1))
  have h0 := Nat.add_le_add assignmentSpan oneSpan
  have h1 := Nat.add_le_add h0 assignmentSpan
  have h2 := Nat.add_le_add h1 oneSpan
  have h3 := Nat.add_le_add h2 oneSpan
  have h4 := Nat.add_le_add h3 oneSpan
  have h5 := Nat.add_le_add h4 assignmentSpan
  have h6 := Nat.add_le_add h5 oneSpan
  unfold frameTwoTerminalSteps
  repeat' rw [← Nat.add_assoc] at h6
  exact Nat.le_trans h6
    (Nat.le_of_eq (eight_span_normalize (cnfShiftedWorkSpan n)))

theorem frame_add_four_reorder (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d)]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [← Nat.add_assoc a c (b + d)]

theorem frame_cost_regroup (boot a b c d : Nat) :
    (boot + (a + b)) + (c + d) =
      (a + c) + ((b + d) + boot) := by
  calc
    (boot + (a + b)) + (c + d) =
        boot + ((a + b) + (c + d)) :=
      Nat.add_assoc boot (a + b) (c + d)
    _ = boot + ((a + c) + (b + d)) :=
      congrArg (Nat.add boot) (frame_add_four_reorder a b c d)
    _ = ((a + c) + (b + d)) + boot :=
      Nat.add_comm boot ((a + c) + (b + d))
    _ = (a + c) + ((b + d) + boot) :=
      Nat.add_assoc (a + c) (b + d) boot

theorem natMulAssocClean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a * b) * c + a * b = a * (b * c + b)
      rw [ih, Nat.mul_add]

theorem frameFolds_le_cubeTwelve (n : Nat)
    (tokens : List CNFToken) (assignment : BitString)
    (combinedBound : tokens.length + assignment.length ≤ n) :
    frameOneFoldSteps [] [] tokens + frameTwoFoldSteps [] [] assignment ≤
      cnfWorkPhaseCube n * 12 := by
  have tokenBound : tokens.length ≤ n :=
    Nat.le_trans (Nat.le_add_right tokens.length assignment.length)
      combinedBound
  have assignmentBound : assignment.length ≤ n :=
    Nat.le_trans (Nat.le_add_left assignment.length tokens.length)
      combinedBound
  have foldOne := frameOneFoldSteps_le n [] [] tokens
    (Nat.le_trans (Nat.le_of_eq (Nat.zero_add tokens.length)) tokenBound)
    (Nat.le_trans (Nat.le_of_eq (Nat.zero_add tokens.length)) tokenBound)
  have foldTwo := frameTwoFoldSteps_le n [] [] assignment
    (Nat.le_trans (Nat.le_of_eq (Nat.zero_add assignment.length))
      assignmentBound)
    (Nat.le_trans (Nat.le_of_eq (Nat.zero_add assignment.length))
      assignmentBound)
  have foldOneCommute : frameOneFoldSteps [] [] tokens ≤
      (cnfShiftedWorkSpan n * 12) * tokens.length :=
    Nat.le_trans foldOne
      (Nat.le_of_eq (Nat.mul_comm tokens.length
        (cnfShiftedWorkSpan n * 12)))
  have foldTwoCommute : frameTwoFoldSteps [] [] assignment ≤
      (cnfShiftedWorkSpan n * 12) * assignment.length :=
    Nat.le_trans foldTwo
      (Nat.le_of_eq (Nat.mul_comm assignment.length
        (cnfShiftedWorkSpan n * 12)))
  have foldsAdded := Nat.add_le_add foldOneCommute foldTwoCommute
  have foldsCombined :
      frameOneFoldSteps [] [] tokens + frameTwoFoldSteps [] [] assignment ≤
        (cnfShiftedWorkSpan n * 12) *
          (tokens.length + assignment.length) :=
    Nat.le_trans foldsAdded
      (Nat.le_of_eq (Nat.mul_add (cnfShiftedWorkSpan n * 12)
        tokens.length assignment.length).symm)
  have foldsToN := Nat.mul_le_mul_left
    (cnfShiftedWorkSpan n * 12) combinedBound
  have nSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have foldsToSpan := Nat.mul_le_mul_left
    (cnfShiftedWorkSpan n * 12) nSpan
  have foldNormalize :
      (cnfShiftedWorkSpan n * 12) * cnfShiftedWorkSpan n =
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 12 := by
    calc
      (cnfShiftedWorkSpan n * 12) * cnfShiftedWorkSpan n =
          cnfShiftedWorkSpan n * (12 * cnfShiftedWorkSpan n) :=
        natMulAssocClean (cnfShiftedWorkSpan n) 12
          (cnfShiftedWorkSpan n)
      _ = cnfShiftedWorkSpan n * (cnfShiftedWorkSpan n * 12) :=
        congrArg (Nat.mul (cnfShiftedWorkSpan n))
          (Nat.mul_comm 12 (cnfShiftedWorkSpan n))
      _ = (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 12 :=
        (natMulAssocClean (cnfShiftedWorkSpan n)
          (cnfShiftedWorkSpan n) 12).symm
  exact Nat.le_trans foldsCombined
    (Nat.le_trans foldsToN
      (Nat.le_trans foldsToSpan
        (Nat.le_trans (Nat.le_of_eq foldNormalize)
          (Nat.mul_le_mul_right 12 (cnfShiftedSquare_le_phaseCube n)))))

theorem frameTerminalsBoot_le_cubeFour (n : Nat)
    (tokens : List CNFToken) (assignment : BitString)
    (tokenBound : tokens.length ≤ n)
    (assignmentBound : assignment.length ≤ n)
    (fiveSpan : 5 ≤ cnfShiftedWorkSpan n) :
    (frameOneTerminalSteps tokens + frameTwoTerminalSteps assignment) + 2 ≤
      cnfWorkPhaseCube n * 4 := by
  have terminalOne := frameOneTerminalSteps_le n tokens tokenBound
  have terminalTwo := frameTwoTerminalSteps_le n assignment
    assignmentBound
  have terminalsAdded := Nat.add_le_add terminalOne terminalTwo
  have terminalNormalize :
      cnfShiftedWorkSpan n * 8 + cnfShiftedWorkSpan n * 8 =
        cnfShiftedWorkSpan n * 16 :=
    (Nat.mul_add (cnfShiftedWorkSpan n) 8 8).symm
  have terminalsSixteen := Nat.le_trans terminalsAdded
    (Nat.le_of_eq terminalNormalize)
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n :=
    Nat.le_trans (by
      change 1 ≤ 1 + 4
      exact Nat.le_add_right 1 4) fiveSpan
  have fourPlusOne : cnfShiftedWorkSpan n * 4 + 1 ≤
      cnfShiftedWorkSpan n * 4 + cnfShiftedWorkSpan n :=
    Nat.add_le_add_left oneSpan (cnfShiftedWorkSpan n * 4)
  have fourPlusSpan : cnfShiftedWorkSpan n * 4 + cnfShiftedWorkSpan n =
      cnfShiftedWorkSpan n * 5 :=
    (Nat.mul_succ (cnfShiftedWorkSpan n) 4).symm
  have fiveToSquare := Nat.mul_le_mul_left (cnfShiftedWorkSpan n) fiveSpan
  have augmentedToSquare : cnfShiftedWorkSpan n * 4 + 1 ≤
      cnfShiftedWorkSpan n * cnfShiftedWorkSpan n :=
    Nat.le_trans fourPlusOne
      (Nat.le_trans (Nat.le_of_eq fourPlusSpan) fiveToSquare)
  have augmentedScaled := Nat.mul_le_mul_right 4 augmentedToSquare
  have twoFour : 2 ≤ 4 := by
    change 2 ≤ 2 + 2
    exact Nat.le_add_right 2 2
  have raised := Nat.add_le_add_left twoFour
    ((cnfShiftedWorkSpan n * 4) * 4)
  have leftNormalize : (cnfShiftedWorkSpan n * 4) * 4 =
      cnfShiftedWorkSpan n * 16 := by
    rw [natMulAssocClean]
  have rightNormalize : (cnfShiftedWorkSpan n * 4 + 1) * 4 =
      (cnfShiftedWorkSpan n * 4) * 4 + 4 :=
    Nat.succ_mul (cnfShiftedWorkSpan n * 4) 4
  have terminalBootRaw : cnfShiftedWorkSpan n * 16 + 2 ≤
      (cnfShiftedWorkSpan n * 4 + 1) * 4 :=
    Nat.le_trans
      (Nat.le_of_eq (congrArg (fun value => value + 2) leftNormalize.symm))
      (Nat.le_trans raised (Nat.le_of_eq rightNormalize.symm))
  have toLinear := Nat.add_le_add_right terminalsSixteen 2
  exact Nat.le_trans toLinear
    (Nat.le_trans terminalBootRaw
      (Nat.le_trans augmentedScaled
        (Nat.mul_le_mul_right 4 (cnfShiftedSquare_le_phaseCube n))))

theorem frameSuccessSteps_le_singlePhase (n : Nat)
    (tokens : List CNFToken) (assignment : BitString)
    (combinedBound : tokens.length + assignment.length ≤ n)
    (fiveSpan : 5 ≤ cnfShiftedWorkSpan n) :
    frameSuccessSteps tokens assignment ≤ cnfSinglePhaseBudget n := by
  have tokenBound : tokens.length ≤ n :=
    Nat.le_trans (Nat.le_add_right tokens.length assignment.length)
      combinedBound
  have assignmentBound : assignment.length ≤ n :=
    Nat.le_trans (Nat.le_add_left assignment.length tokens.length)
      combinedBound
  have folds := frameFolds_le_cubeTwelve n tokens assignment
    combinedBound
  have terminals := frameTerminalsBoot_le_cubeFour n tokens assignment
    tokenBound assignmentBound fiveSpan
  have componentBounds := Nat.add_le_add folds terminals
  have totalNormalize :
      cnfWorkPhaseCube n * 12 + cnfWorkPhaseCube n * 4 =
        cnfWorkPhaseCube n * 16 :=
    (Nat.mul_add (cnfWorkPhaseCube n) 12 4).symm
  unfold frameSuccessSteps cnfSinglePhaseBudget
  rw [frame_cost_regroup]
  exact Nat.le_trans componentBounds (Nat.le_of_eq totalNormalize)

theorem decoded_frame_payload_length_le_pair_size
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    (encodeFormulaTokens formula).length + assignment.length ≤
      BitString.size (BitString.pair input certificate) := by
  have formulaShape := encodeFormula_of_decode input formula formulaDecoded
  have assignmentShape := encodeAssignmentCertificate_of_decode
    certificate assignment assignmentDecoded
  rw [← formulaShape, ← assignmentShape]
  rw [BitString.size_pair_normalized]
  unfold BitString.size
  rw [encodeFormula_eq_padded_tokens, paddedFormulaTokenBits_length]
  rw [encodeAssignmentCertificate_eq_token_bits]
  rw [assignmentCertificateTokenBits_length]
  rw [assignmentValueTokens_length]
  let tokenLength := (encodeFormulaTokens formula).length
  let assignmentLength := assignment.length
  have oneTwo : 0 < 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  have tokenToDouble : tokenLength ≤ 2 * tokenLength :=
    Nat.le_mul_of_pos_left tokenLength oneTwo
  have tokenToEncoded : tokenLength ≤ 2 * tokenLength + 1 :=
    Nat.le_trans tokenToDouble (Nat.le_add_right (2 * tokenLength) 1)
  have assignmentToDouble : assignmentLength ≤ 2 * assignmentLength :=
    Nat.le_mul_of_pos_left assignmentLength oneTwo
  have assignmentToEncoded : assignmentLength ≤
      2 * assignmentLength + 2 :=
    Nat.le_trans assignmentToDouble
      (Nat.le_add_right (2 * assignmentLength) 2)
  have payloadToRaw := Nat.add_le_add tokenToEncoded assignmentToEncoded
  have formulaRawToDouble : 2 * tokenLength + 1 ≤
      2 * (2 * tokenLength + 1) :=
    Nat.le_mul_of_pos_left (2 * tokenLength + 1) oneTwo
  have assignmentRawToDouble : 2 * assignmentLength + 2 ≤
      2 * (2 * assignmentLength + 2) :=
    Nat.le_mul_of_pos_left (2 * assignmentLength + 2) oneTwo
  have rawToDouble := Nat.add_le_add formulaRawToDouble
    assignmentRawToDouble
  have rawToPair := Nat.le_trans rawToDouble
    (Nat.le_add_right
      (2 * (2 * tokenLength + 1) +
        2 * (2 * assignmentLength + 2)) 2)
  exact Nat.le_trans payloadToRaw rawToPair

theorem decoded_frameSuccessSteps_le_pair_singlePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    frameSuccessSteps (encodeFormulaTokens formula) assignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  let pairSize := BitString.size (BitString.pair input certificate)
  have combinedBound := decoded_frame_payload_length_le_pair_size
    input certificate formula assignment formulaDecoded assignmentDecoded
  have fiveSpan : 5 ≤ cnfShiftedWorkSpan pairSize := by
    unfold pairSize cnfShiftedWorkSpan
    rw [BitString.size_pair_normalized]
    change 5 ≤ 2 * BitString.size input +
      2 * BitString.size certificate + 2 + 2
    have oneInput : 1 ≤ BitString.size input := by
      rw [← encodeFormula_of_decode input formula formulaDecoded]
      unfold BitString.size
      rw [encodeFormula_eq_padded_tokens, paddedFormulaTokenBits_length]
      exact Nat.le_add_left 1 (2 * (encodeFormulaTokens formula).length)
    have twoInput : 2 ≤ 2 * BitString.size input :=
      Nat.mul_le_mul_left 2 oneInput
    have base : 2 + 0 + 2 + 1 ≤
        2 * BitString.size input +
          2 * BitString.size certificate + 2 + 2 := by
      have certificateNonnegative : 0 ≤
          2 * BitString.size certificate := Nat.zero_le _
      have first := Nat.add_le_add twoInput certificateNonnegative
      have second := Nat.add_le_add_right first 2
      have oneTwo : 1 ≤ 2 := by
        change 1 ≤ 1 + 1
        exact Nat.le_add_right 1 1
      exact Nat.add_le_add second oneTwo
    exact base
  exact frameSuccessSteps_le_singlePhase pairSize
    (encodeFormulaTokens formula) assignment combinedBound fiveSpan

def leadingZeroWorkSymbol (bit : Bool) : WorkSymbol :=
  ⟨TapeSymbol.zero, TapeSymbol.ofBool bit⟩

def badFormulaBoundary (certificateNonempty : Bool) : WorkSymbol :=
  if certificateNonempty then cnfT else cnfFinish

theorem boot_t_exact (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 2
        (workStartConfiguration cnfWorkMachine
          (WorkTape.ofSymbols (cnfT :: suffix))) =
      some (workConfigAtWord CNFWorkState.frameOneFindCounter
        [cnfRootGuard] (cnfT :: suffix)) := by
  rfl

theorem frameOne_toHeader_leadingZero_reject
    (bit : Bool) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.frameOneToHeader left
          (leadingZeroWorkSymbol bit :: suffix)) =
      some (workConfigAtWord CNFWorkState.reject left
        (leadingZeroWorkSymbol bit :: suffix)) := by
  cases bit <;> rfl

theorem frameTwo_findCounter_leadingZero_reject
    (bit : Bool) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.frameTwoFindCounter left
          (leadingZeroWorkSymbol bit :: suffix)) =
      some (workConfigAtWord CNFWorkState.reject left
        (leadingZeroWorkSymbol bit :: suffix)) := by
  cases bit <;> rfl

theorem frameTwo_toHeader_leadingZero_reject
    (bit : Bool) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.frameTwoToHeader left
          (leadingZeroWorkSymbol bit :: suffix)) =
      some (workConfigAtWord CNFWorkState.reject left
        (leadingZeroWorkSymbol bit :: suffix)) := by
  cases bit <;> rfl

theorem frameOne_checkPayload_badBoundary_reject
    (certificateNonempty : Bool) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.frameOneCheckPayload left
          (badFormulaBoundary certificateNonempty :: suffix)) =
      some (workConfigAtWord CNFWorkState.reject left
        (badFormulaBoundary certificateNonempty :: suffix)) := by
  cases certificateNonempty <;> rfl

theorem formulaEvenHeader_reject
    (count : Nat) (bit : Bool) (suffix : List WorkSymbol) :
    ∃ steps left,
      steps ≤ count + 4 ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (WorkTape.ofSymbols
              (List.replicate count cnfT ++
                leadingZeroWorkSymbol bit :: suffix))) =
        some (workConfigAtWord CNFWorkState.reject left
          (leadingZeroWorkSymbol bit :: suffix)) := by
  cases count with
  | zero =>
      refine ⟨1, [], ?_, ?_⟩
      · change 1 ≤ 1 + 3
        exact Nat.le_add_right 1 3
      · cases bit <;> rfl
  | succ count =>
      have hBoot := boot_t_exact
        (List.replicate count cnfT ++
          leadingZeroWorkSymbol bit :: suffix)
      have hMark := workRunExact?_one_of_step cnfWorkMachine _ _
        (frameOne_findCounter_t_step [cnfRootGuard]
          (List.replicate count cnfT ++
            leadingZeroWorkSymbol bit :: suffix))
      have hScan := frameOne_toHeader_t_word_scan
        (List.replicate count cnfT)
        [cnfMarkFalse, cnfRootGuard]
        (leadingZeroWorkSymbol bit :: suffix)
        (mem_replicate_workSymbol_eq count cnfT)
      rw [length_replicate_workSymbol] at hScan
      have hReject := frameOne_toHeader_leadingZero_reject bit
        (pushWorkLeft (List.replicate count cnfT)
          [cnfMarkFalse, cnfRootGuard]) suffix
      have hBootMark := workRunExact?_compose cnfWorkMachine 2 1
        _ _ _ hBoot hMark
      have hThroughScan := workRunExact?_compose cnfWorkMachine
        (2 + 1) count _ _ _ hBootMark hScan
      have hComplete := workRunExact?_compose cnfWorkMachine
        ((2 + 1) + count) 1 _ _ _ hThroughScan hReject
      refine ⟨((2 + 1) + count) + 1,
        pushWorkLeft (List.replicate count cnfT)
          [cnfMarkFalse, cnfRootGuard], ?_, hComplete⟩
      calc
        ((2 + 1) + count) + 1 = count + 4 := by
          rw [Nat.add_comm (2 + 1) count]
        _ ≤ count + (1 + 4) :=
          Nat.add_le_add_left (Nat.le_add_left 4 1) count
        _ = (count + 1) + 4 := (Nat.add_assoc count 1 4).symm

theorem frameTwoMalformedHeader_reject
    (count : Nat) (bit : Bool) (leftBase suffix : List WorkSymbol) :
    ∃ left,
      workRunExact? cnfWorkMachine (count + 1)
          (workConfigAtWord CNFWorkState.frameTwoFindCounter leftBase
            (List.replicate count cnfT ++
              leadingZeroWorkSymbol bit :: suffix)) =
        some (workConfigAtWord CNFWorkState.reject left
          (leadingZeroWorkSymbol bit :: suffix)) := by
  cases count with
  | zero =>
      exact ⟨leftBase,
        frameTwo_findCounter_leadingZero_reject bit leftBase suffix⟩
  | succ count =>
      have hMark := workRunExact?_one_of_step cnfWorkMachine _ _
        (frameTwo_findCounter_t_step leftBase
          (List.replicate count cnfT ++
            leadingZeroWorkSymbol bit :: suffix))
      have hScan := frameTwo_toHeader_t_word_scan
        (List.replicate count cnfT) (cnfMarkFalse :: leftBase)
        (leadingZeroWorkSymbol bit :: suffix)
        (mem_replicate_workSymbol_eq count cnfT)
      rw [length_replicate_workSymbol] at hScan
      have hReject := frameTwo_toHeader_leadingZero_reject bit
        (pushWorkLeft (List.replicate count cnfT)
          (cnfMarkFalse :: leftBase)) suffix
      have hThroughScan := workRunExact?_compose cnfWorkMachine 1 count
        _ _ _ hMark hScan
      have hComplete := workRunExact?_compose cnfWorkMachine
        (1 + count) 1 _ _ _ hThroughScan hReject
      refine ⟨pushWorkLeft (List.replicate count cnfT)
        (cnfMarkFalse :: leftBase), ?_⟩
      rw [List.replicate_succ]
      rw [← Nat.add_comm 1 count]
      exact hComplete

def frameOneBoundaryFoldStart
    (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (boundary : WorkSymbol)
    (suffix : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
    ((doneCounter ++ List.replicate tokens.length cnfT) ++
      cnfFinish ::
        ((donePayload ++ cnfTokenWorkSymbols tokens) ++ boundary :: suffix))

def frameOneBoundaryFoldFinal
    (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (boundary : WorkSymbol)
    (suffix : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
    ((doneCounter ++ List.replicate tokens.length cnfMarkFalse) ++
      cnfFinish ::
        ((donePayload ++ frameOneMarkedTokens tokens) ++ boundary :: suffix))

theorem frameOneBoundaryFoldStart_cons
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (boundary : WorkSymbol) (suffix : List WorkSymbol) :
    frameOneBoundaryFoldStart doneCounter donePayload
        (token :: rest) boundary suffix =
      workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
        (doneCounter ++ cnfT ::
          (List.replicate rest.length cnfT ++ cnfFinish ::
            (donePayload ++ token.workSymbol ::
              (cnfTokenWorkSymbols rest ++ boundary :: suffix)))) := by
  unfold frameOneBoundaryFoldStart
  change workConfigAtWord _ _
      ((doneCounter ++ cnfT :: List.replicate rest.length cnfT) ++
        cnfFinish ::
          ((donePayload ++ token.workSymbol :: cnfTokenWorkSymbols rest) ++
            boundary :: suffix)) = _
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOneBoundaryFold_after_iteration
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (boundary : WorkSymbol) (suffix : List WorkSymbol) :
    workConfigAtWord CNFWorkState.frameOneFindCounter [cnfRootGuard]
        ((doneCounter ++ cnfMarkFalse ::
          List.replicate rest.length cnfT) ++
            (cnfFinish :: donePayload ++ frameOneMarkedToken token ::
              (cnfTokenWorkSymbols rest ++ boundary :: suffix))) =
      frameOneBoundaryFoldStart
        (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token]) rest boundary suffix := by
  unfold frameOneBoundaryFoldStart
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOneBoundaryFoldFinal_cons
    (doneCounter donePayload : List WorkSymbol)
    (token : CNFToken) (rest : List CNFToken)
    (boundary : WorkSymbol) (suffix : List WorkSymbol) :
    frameOneBoundaryFoldFinal
        (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token]) rest boundary suffix =
      frameOneBoundaryFoldFinal doneCounter donePayload
        (token :: rest) boundary suffix := by
  unfold frameOneBoundaryFoldFinal
  change workConfigAtWord _ _
      (((doneCounter ++ [cnfMarkFalse]) ++
          List.replicate rest.length cnfMarkFalse) ++
        cnfFinish ::
          (((donePayload ++ [frameOneMarkedToken token]) ++
              frameOneMarkedTokens rest) ++ boundary :: suffix)) =
    workConfigAtWord _ _
      ((doneCounter ++ cnfMarkFalse ::
          List.replicate rest.length cnfMarkFalse) ++
        cnfFinish ::
          ((donePayload ++ frameOneMarkedToken token ::
              frameOneMarkedTokens rest) ++ boundary :: suffix))
  repeat' rw [frameWork_append_assoc]
  rfl

theorem frameOne_boundary_fold_exact
    (doneCounter donePayload : List WorkSymbol)
    (tokens : List CNFToken) (boundary : WorkSymbol)
    (suffix : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      FrameOneMarkedSymbol symbol) :
    workRunExact? cnfWorkMachine
        (frameOneFoldSteps doneCounter donePayload tokens)
        (frameOneBoundaryFoldStart doneCounter donePayload
          tokens boundary suffix) =
      some (frameOneBoundaryFoldFinal doneCounter donePayload
        tokens boundary suffix) := by
  induction tokens generalizing doneCounter donePayload with
  | nil => rfl
  | cons token rest ih =>
      have restCounterAllowed : ∀ symbol,
          List.Mem symbol (List.replicate rest.length cnfT) →
            symbol = cnfT := by
        intro symbol member
        exact mem_replicate_workSymbol_eq rest.length cnfT symbol member
      have hIteration := frameOne_iteration_exact doneCounter
        (List.replicate rest.length cnfT) donePayload token
        (cnfTokenWorkSymbols rest ++ boundary :: suffix)
        doneCounterAllowed restCounterAllowed donePayloadAllowed
      rw [← frameOneBoundaryFoldStart_cons] at hIteration
      have nextCounterAllowed : ∀ symbol,
          List.Mem symbol (doneCounter ++ [cnfMarkFalse]) →
            symbol = cnfMarkFalse := by
        exact frameAllowed_append_one
          (fun candidate => candidate = cnfMarkFalse)
          doneCounter cnfMarkFalse doneCounterAllowed rfl
      have nextPayloadAllowed : ∀ symbol,
          List.Mem symbol (donePayload ++ [frameOneMarkedToken token]) →
            FrameOneMarkedSymbol symbol := by
        exact frameAllowed_append_one FrameOneMarkedSymbol donePayload
          (frameOneMarkedToken token) donePayloadAllowed (by
            cases token <;> constructor)
      have hRest := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [frameOneMarkedToken token])
        nextCounterAllowed nextPayloadAllowed
      rw [← frameOneBoundaryFold_after_iteration] at hRest
      rw [frameOneBoundaryFoldFinal_cons] at hRest
      exact workRunExact?_compose cnfWorkMachine
        (frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT) donePayload)
        (frameOneFoldSteps (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [frameOneMarkedToken token]) rest)
        _ _ _ hIteration hRest

def frameOneBadBoundarySteps (tokens : List CNFToken) : Nat :=
  ((tokens.length + 1) + tokens.length) + 1

theorem frameOne_badBoundary_terminal_exact
    (tokens : List CNFToken) (certificateNonempty : Bool)
    (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine (frameOneBadBoundarySteps tokens)
        (frameOneBoundaryFoldFinal [] [] tokens
          (badFormulaBoundary certificateNonempty) suffix) =
      some
        (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft (frameOneMarkedTokens tokens)
            (cnfFinish ::
              pushWorkLeft
                (List.replicate tokens.length cnfMarkFalse)
                [cnfRootGuard]))
          (badFormulaBoundary certificateNonempty :: suffix)) := by
  have hCounter := frameOne_findCounter_markFalse_scan tokens.length
    [cnfRootGuard]
    (cnfFinish :: frameOneMarkedTokens tokens ++
      badFormulaBoundary certificateNonempty :: suffix)
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_findCounter_finish_step
      (pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
      (frameOneMarkedTokens tokens ++
        badFormulaBoundary certificateNonempty :: suffix))
  have hPayload := frameOne_checkPayload_marked_scan tokens
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
    (badFormulaBoundary certificateNonempty :: suffix)
  have hReject := frameOne_checkPayload_badBoundary_reject
    certificateNonempty
    (pushWorkLeft (frameOneMarkedTokens tokens)
      (cnfFinish ::
        pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
          [cnfRootGuard])) suffix
  have hThroughFinish := workRunExact?_compose cnfWorkMachine
    tokens.length 1 _ _ _ hCounter hFinish
  have hThroughPayload := workRunExact?_compose cnfWorkMachine
    (tokens.length + 1) tokens.length _ _ _ hThroughFinish hPayload
  unfold frameOneBoundaryFoldFinal frameOneBadBoundarySteps
  exact workRunExact?_compose cnfWorkMachine
    ((tokens.length + 1) + tokens.length) 1 _ _ _
    hThroughPayload hReject

theorem frameOne_badBoundary_exact
    (tokens : List CNFToken) (certificateNonempty : Bool)
    (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (frameOneFoldSteps [] [] tokens +
          frameOneBadBoundarySteps tokens)
        (frameOneBoundaryFoldStart [] [] tokens
          (badFormulaBoundary certificateNonempty) suffix) =
      some
        (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft (frameOneMarkedTokens tokens)
            (cnfFinish ::
              pushWorkLeft
                (List.replicate tokens.length cnfMarkFalse)
                [cnfRootGuard]))
          (badFormulaBoundary certificateNonempty :: suffix)) := by
  have hFold := frameOne_boundary_fold_exact [] [] tokens
    (badFormulaBoundary certificateNonempty) suffix
    (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
  have hTerminal := frameOne_badBoundary_terminal_exact tokens
    certificateNonempty suffix
  exact workRunExact?_compose cnfWorkMachine
    (frameOneFoldSteps [] [] tokens)
    (frameOneBadBoundarySteps tokens) _ _ _ hFold hTerminal

theorem formulaBadPadLayout_reject
    (tokens : List CNFToken) (certificateNonempty : Bool)
    (suffix : List WorkSymbol) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (WorkTape.ofSymbols
              (List.replicate tokens.length cnfT ++ cnfFinish ::
                (cnfTokenWorkSymbols tokens ++
                  badFormulaBoundary certificateNonempty :: suffix)))) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  cases tokens with
  | nil =>
      refine ⟨1, (WorkTape.ofSymbols
        (cnfFinish :: badFormulaBoundary certificateNonempty :: suffix)), ?_⟩
      cases certificateNonempty <;> rfl
  | cons token rest =>
      have hBoot := boot_t_exact
        (List.replicate rest.length cnfT ++ cnfFinish ::
          (token.workSymbol ::
            (cnfTokenWorkSymbols rest ++
              badFormulaBoundary certificateNonempty :: suffix)))
      have hBad := frameOne_badBoundary_exact (token :: rest)
        certificateNonempty suffix
      rw [frameOneBoundaryFoldStart_cons] at hBad
      have hComplete := workRunExact?_compose cnfWorkMachine 2
        (frameOneFoldSteps [] [] (token :: rest) +
          frameOneBadBoundarySteps (token :: rest))
        _ _ _ hBoot hBad
      refine ⟨2 +
        (frameOneFoldSteps [] [] (token :: rest) +
          frameOneBadBoundarySteps (token :: rest)),
        (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft (frameOneMarkedTokens (token :: rest))
            (cnfFinish ::
              pushWorkLeft
                (List.replicate (token :: rest).length cnfMarkFalse)
                [cnfRootGuard]))
          (badFormulaBoundary certificateNonempty :: suffix)).tape, ?_⟩
      have startShape :
          List.replicate (token :: rest).length cnfT ++ cnfFinish ::
              (cnfTokenWorkSymbols (token :: rest) ++
                badFormulaBoundary certificateNonempty :: suffix) =
            cnfT ::
              (List.replicate rest.length cnfT ++ cnfFinish ::
                token.workSymbol ::
                  (cnfTokenWorkSymbols rest ++
                    badFormulaBoundary certificateNonempty :: suffix)) :=
        rfl
      rw [startShape]
      exact hComplete

theorem mapTapeOfBool_append (left right : BitString) :
    (left ++ right).map TapeSymbol.ofBool =
      left.map TapeSymbol.ofBool ++ right.map TapeSymbol.ofBool := by
  induction left with
  | nil => rfl
  | cons bit rest ih => exact congrArg (List.cons (TapeSymbol.ofBool bit)) ih

theorem listAppendAssoc {alpha : Type}
    (left middle right : List alpha) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons item rest ih => exact congrArg (List.cons item) ih

theorem mapTapeOfBool_replicate_true (count : Nat) :
    (List.replicate count true).map TapeSymbol.ofBool =
      List.replicate count TapeSymbol.one := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons TapeSymbol.one) ih

theorem replicate_succ_tail {alpha : Type}
    (count : Nat) (item : alpha) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        item :: (List.replicate count item ++ [item])
      exact congrArg (List.cons item) ih

theorem packWorkSymbols_even_ones (count : Nat)
    (suffix : List TapeSymbol) :
    packWorkSymbols
        (List.replicate (2 * count) TapeSymbol.one ++ suffix) =
      List.replicate count cnfT ++ packWorkSymbols suffix := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change cnfT ::
          packWorkSymbols
            (List.replicate (2 * count) TapeSymbol.one ++ suffix) =
        cnfT ::
          (List.replicate count cnfT ++ packWorkSymbols suffix)
      exact congrArg (List.cons cnfT) ih

theorem packWorkSymbols_encodeWorkRight_prefix
    (word : List WorkSymbol) (suffix : List TapeSymbol) :
    packWorkSymbols (encodeWorkRight word ++ suffix) =
      word ++ packWorkSymbols suffix := by
  induction word with
  | nil => rfl
  | cons symbol rest ih =>
      cases symbol with
      | mk first second =>
          change { first := first, second := second } ::
              packWorkSymbols (encodeWorkRight rest ++ suffix) =
            { first := first, second := second } ::
              (rest ++ packWorkSymbols suffix)
          exact congrArg (List.cons { first := first, second := second }) ih

theorem pairedWorkTape_formulaEven_shape
    (tokens : List CNFToken) (certificate : BitString) :
    ∃ bit suffix,
      pairedWorkTape (encodeTokenPairs tokens) certificate =
        WorkTape.ofSymbols
          (List.replicate tokens.length cnfT ++
            leadingZeroWorkSymbol bit :: suffix) := by
  unfold pairedWorkTape
  change ∃ bit suffix,
    WorkTape.ofSymbols
        (packWorkSymbols
          ((BitString.pair (encodeTokenPairs tokens) certificate).map
            TapeSymbol.ofBool)) =
      WorkTape.ofSymbols
        (List.replicate tokens.length cnfT ++
          leadingZeroWorkSymbol bit :: suffix)
  unfold BitString.pair BitString.frame
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_replicate_true]
  rw [encodeTokenPairs_length]
  rw [listAppendAssoc]
  rw [packWorkSymbols_even_ones]
  cases tokens with
  | nil =>
      cases certificate with
      | nil => exact ⟨false, [], rfl⟩
      | cons first rest =>
          refine ⟨true,
            packWorkSymbols
              ((List.replicate rest.length true ++
                false :: first :: rest).map TapeSymbol.ofBool), ?_⟩
          rfl
  | cons token rest =>
      cases token with
      | f =>
          refine ⟨false,
            packWorkSymbols
              (TapeSymbol.zero ::
                ((encodeTokenPairs rest).map TapeSymbol.ofBool ++
                  (List.replicate certificate.length true ++
                    false :: certificate).map TapeSymbol.ofBool)), ?_⟩
          rfl
      | t =>
          refine ⟨true,
            packWorkSymbols
              (TapeSymbol.one ::
                ((encodeTokenPairs rest).map TapeSymbol.ofBool ++
                  (List.replicate certificate.length true ++
                    false :: certificate).map TapeSymbol.ofBool)), ?_⟩
          rfl
      | sep =>
          refine ⟨false,
            packWorkSymbols
              (TapeSymbol.one ::
                ((encodeTokenPairs rest).map TapeSymbol.ofBool ++
                  (List.replicate certificate.length true ++
                    false :: certificate).map TapeSymbol.ofBool)), ?_⟩
          rfl
      | finish =>
          refine ⟨true,
            packWorkSymbols
              (TapeSymbol.zero ::
                ((encodeTokenPairs rest).map TapeSymbol.ofBool ++
                  (List.replicate certificate.length true ++
                    false :: certificate).map TapeSymbol.ofBool)), ?_⟩
          rfl

theorem pairedWorkTape_formulaBadPad_shape
    (tokens : List CNFToken) (certificate : BitString) :
    ∃ certificateNonempty suffix,
      pairedWorkTape (encodeTokenPairs tokens ++ [true]) certificate =
        WorkTape.ofSymbols
          (List.replicate tokens.length cnfT ++ cnfFinish ::
            (cnfTokenWorkSymbols tokens ++
              badFormulaBoundary certificateNonempty :: suffix)) := by
  unfold pairedWorkTape
  change ∃ certificateNonempty suffix,
    WorkTape.ofSymbols
        (packWorkSymbols
          ((BitString.pair (encodeTokenPairs tokens ++ [true]) certificate).map
            TapeSymbol.ofBool)) =
      WorkTape.ofSymbols
        (List.replicate tokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols tokens ++
            badFormulaBoundary certificateNonempty :: suffix))
  unfold BitString.pair BitString.frame
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_replicate_true]
  rw [BitString.length_append_constructive, encodeTokenPairs_length]
  rw [List.length_singleton]
  rw [listAppendAssoc]
  change ∃ certificateNonempty suffix,
    WorkTape.ofSymbols
        (packWorkSymbols
          (List.replicate (2 * tokens.length + 1) TapeSymbol.one ++
            TapeSymbol.zero ::
              ((encodeTokenPairs tokens ++ [true]).map TapeSymbol.ofBool ++
                ((List.replicate certificate.length true ++
                  false :: certificate).map TapeSymbol.ofBool)))) =
      WorkTape.ofSymbols
        (List.replicate tokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols tokens ++
            badFormulaBoundary certificateNonempty :: suffix))
  rw [replicate_succ_tail]
  rw [listAppendAssoc]
  rw [packWorkSymbols_even_ones]
  change ∃ certificateNonempty suffix,
    WorkTape.ofSymbols
      (List.replicate tokens.length cnfT ++ cnfFinish ::
        packWorkSymbols
          ((encodeTokenPairs tokens ++ [true]).map TapeSymbol.ofBool ++
            ((List.replicate certificate.length true ++
              false :: certificate).map TapeSymbol.ofBool))) =
      WorkTape.ofSymbols
        (List.replicate tokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols tokens ++
            badFormulaBoundary certificateNonempty :: suffix))
  rw [mapTapeOfBool_append]
  rw [← encodeWorkRight_cnfTokenWorkSymbols]
  rw [listAppendAssoc]
  rw [packWorkSymbols_encodeWorkRight_prefix]
  cases certificate with
  | nil => exact ⟨false, [], rfl⟩
  | cons first rest =>
      refine ⟨true,
        packWorkSymbols
          ((List.replicate rest.length true ++
            false :: first :: rest).map TapeSymbol.ofBool), ?_⟩
      rfl

theorem pairedWorkTape_assignmentOdd_shape
    (formulaTokens certificateTokens : List CNFToken) (last : Bool) :
    ∃ bit suffix,
      pairedWorkTape
          (encodeTokenPairs formulaTokens ++ [false])
          (encodeTokenPairs certificateTokens ++ [last]) =
        WorkTape.ofSymbols
          (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
            (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
              (List.replicate certificateTokens.length cnfT ++
                leadingZeroWorkSymbol bit :: suffix))) := by
  unfold pairedWorkTape
  change ∃ bit suffix,
    WorkTape.ofSymbols
        (packWorkSymbols
          ((BitString.pair (encodeTokenPairs formulaTokens ++ [false])
            (encodeTokenPairs certificateTokens ++ [last])).map
              TapeSymbol.ofBool)) =
      WorkTape.ofSymbols
        (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
            (List.replicate certificateTokens.length cnfT ++
              leadingZeroWorkSymbol bit :: suffix)))
  unfold BitString.pair BitString.frame
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_replicate_true]
  rw [BitString.length_append_constructive, encodeTokenPairs_length]
  rw [List.length_singleton]
  rw [listAppendAssoc]
  change ∃ bit suffix,
    WorkTape.ofSymbols
        (packWorkSymbols
          (List.replicate (2 * formulaTokens.length + 1) TapeSymbol.one ++
            TapeSymbol.zero ::
              ((encodeTokenPairs formulaTokens ++ [false]).map
                  TapeSymbol.ofBool ++
                ((List.replicate
                  (encodeTokenPairs certificateTokens ++ [last]).length true ++
                    false :: (encodeTokenPairs certificateTokens ++ [last])).map
                  TapeSymbol.ofBool)))) =
      WorkTape.ofSymbols
        (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
            (List.replicate certificateTokens.length cnfT ++
              leadingZeroWorkSymbol bit :: suffix)))
  rw [replicate_succ_tail]
  rw [listAppendAssoc]
  rw [packWorkSymbols_even_ones]
  rw [mapTapeOfBool_append]
  rw [← encodeWorkRight_cnfTokenWorkSymbols]
  change ∃ bit suffix,
    WorkTape.ofSymbols
      (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
        packWorkSymbols
          (encodeWorkRight (cnfTokenWorkSymbols formulaTokens) ++
            [TapeSymbol.zero] ++
              ((List.replicate
                (encodeTokenPairs certificateTokens ++ [last]).length true ++
                  false :: (encodeTokenPairs certificateTokens ++ [last])).map
                TapeSymbol.ofBool))) =
      WorkTape.ofSymbols
        (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
            (List.replicate certificateTokens.length cnfT ++
              leadingZeroWorkSymbol bit :: suffix)))
  rw [listAppendAssoc]
  rw [packWorkSymbols_encodeWorkRight_prefix]
  rw [BitString.length_append_constructive, encodeTokenPairs_length]
  rw [List.length_singleton]
  rw [mapTapeOfBool_append]
  rw [mapTapeOfBool_replicate_true]
  rw [List.replicate_succ]
  change ∃ bit suffix,
    WorkTape.ofSymbols
      (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
        (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
          packWorkSymbols
            (List.replicate (2 * certificateTokens.length) TapeSymbol.one ++
              TapeSymbol.zero ::
                ((encodeTokenPairs certificateTokens ++ [last]).map
                  TapeSymbol.ofBool)))) =
      WorkTape.ofSymbols
        (List.replicate formulaTokens.length cnfT ++ cnfFinish ::
          (cnfTokenWorkSymbols formulaTokens ++ cnfSep ::
            (List.replicate certificateTokens.length cnfT ++
              leadingZeroWorkSymbol bit :: suffix)))
  rw [packWorkSymbols_even_ones]
  cases certificateTokens with
  | nil => exact ⟨last, [], by cases last <;> rfl⟩
  | cons token rest =>
      cases token with
      | f =>
          exact ⟨false,
            packWorkSymbols
              (TapeSymbol.zero ::
                ((encodeTokenPairs rest ++ [last]).map TapeSymbol.ofBool)),
            rfl⟩
      | t =>
          exact ⟨true,
            packWorkSymbols
              (TapeSymbol.one ::
                ((encodeTokenPairs rest ++ [last]).map TapeSymbol.ofBool)),
            rfl⟩
      | sep =>
          exact ⟨false,
            packWorkSymbols
              (TapeSymbol.one ::
                ((encodeTokenPairs rest ++ [last]).map TapeSymbol.ofBool)),
            rfl⟩
      | finish =>
          exact ⟨true,
            packWorkSymbols
              (TapeSymbol.zero ::
                ((encodeTokenPairs rest ++ [last]).map TapeSymbol.ofBool)),
            rfl⟩

theorem formulaRawDecoder_none_rejects
    (input certificate : BitString)
    (decoded : decodeFormulaTokenPairs input = none) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  rcases decodeFormulaTokenPairs_none_shape input decoded with
    ⟨tokens, shape⟩
  cases shape with
  | inl evenShape =>
      cases evenShape
      rcases pairedWorkTape_formulaEven_shape tokens certificate with
        ⟨bit, suffix, tapeShape⟩
      rcases formulaEvenHeader_reject tokens.length bit suffix with
        ⟨steps, left, stepBound, run⟩
      refine ⟨steps,
        (workConfigAtWord CNFWorkState.reject left
          (leadingZeroWorkSymbol bit :: suffix)).tape, ?_⟩
      rw [tapeShape]
      exact run
  | inr badPadShape =>
      cases badPadShape
      rcases pairedWorkTape_formulaBadPad_shape tokens certificate with
        ⟨certificateNonempty, suffix, tapeShape⟩
      rcases formulaBadPadLayout_reject tokens certificateNonempty suffix
        with ⟨steps, tape, run⟩
      exact ⟨steps, tape, by rw [tapeShape]; exact run⟩

theorem assignmentRawDecoder_none_rejects
    (input certificate : BitString) (formula : CNFFormula)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (decoded : decodeTokenPairs certificate = none) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have inputShape := encodeFormula_of_decode input formula formulaDecoded
  rcases decodeTokenPairs_none_shape certificate decoded with
    ⟨certificateTokens, last, certificateShape⟩
  rw [← inputShape]
  rw [encodeFormula_eq_padded_tokens]
  unfold paddedFormulaTokenBits
  rw [certificateShape]
  rcases pairedWorkTape_assignmentOdd_shape
      (encodeFormulaTokens formula) certificateTokens last with
    ⟨bit, suffix, tapeShape⟩
  rcases encodeFormulaTokens_cons formula with
    ⟨first, rest, tokenShape⟩
  have hBoot := boot_t_exact
    (List.replicate rest.length cnfT ++ cnfFinish ::
      (first.workSymbol ::
        (cnfTokenWorkSymbols rest ++ cnfSep ::
          (List.replicate certificateTokens.length cnfT ++
            leadingZeroWorkSymbol bit :: suffix))))
  have hFrameOne := frameOne_complete_exact (first :: rest)
    (List.replicate certificateTokens.length cnfT ++
      leadingZeroWorkSymbol bit :: suffix)
  rw [frameOneFoldStart_empty_cons] at hFrameOne
  let leftBase :=
    pushWorkLeft (cnfTokenWorkSymbols (first :: rest))
      (cnfFinish ::
        pushWorkLeft
          (List.replicate (first :: rest).length cnfMarkFalse)
          [cnfRootGuard])
  rcases frameTwoMalformedHeader_reject certificateTokens.length bit
      (cnfBoundaryGuard :: leftBase) suffix with ⟨finalLeft, hReject⟩
  have hBootFrameOne := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest))
    _ _ _ hBoot hFrameOne
  have hComplete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest)))
    (certificateTokens.length + 1) _ _ _ hBootFrameOne hReject
  refine ⟨(2 + (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest))) +
      (certificateTokens.length + 1),
    (workConfigAtWord CNFWorkState.reject finalLeft
      (leadingZeroWorkSymbol bit :: suffix)).tape, ?_⟩
  rw [tapeShape]
  rw [tokenShape]
  exact hComplete

end FrameTraceDesign

end PNP.Concrete
