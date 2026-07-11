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

/-! ### Exact width-phase execution and phase ledger -/

theorem workSymbol_append_assoc
    (left middle right : List WorkSymbol) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons symbol rest ih => exact congrArg (List.cons symbol) ih

theorem workSymbol_length_append
    (left right : List WorkSymbol) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons symbol rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

theorem cnfTokenWorkSymbols_append
    (left right : List CNFToken) :
    cnfTokenWorkSymbols (left ++ right) =
      cnfTokenWorkSymbols left ++ cnfTokenWorkSymbols right := by
  induction left with
  | nil => rfl
  | cons token rest ih =>
      change token.workSymbol :: cnfTokenWorkSymbols (rest ++ right) =
        token.workSymbol ::
          (cnfTokenWorkSymbols rest ++ cnfTokenWorkSymbols right)
      exact congrArg (List.cons token.workSymbol) ih

theorem cnfTokenWorkSymbols_encodeUnaryTokens (count : Nat) :
    cnfTokenWorkSymbols (encodeUnaryTokens count) =
      List.replicate count cnfT ++ [cnfF] := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change cnfT :: cnfTokenWorkSymbols (encodeUnaryTokens count) =
        cnfT :: (List.replicate count cnfT ++ [cnfF])
      exact congrArg (List.cons cnfT) ih

theorem cnfTokenWorkSymbols_formula_header (formula : CNFFormula) :
    cnfTokenWorkSymbols (encodeFormulaTokens formula) =
      List.replicate formula.variableCount cnfT ++
        cnfF :: cnfTokenWorkSymbols
          (encodeClauseListTokens formula.clauses ++ [.finish]) := by
  unfold encodeFormulaTokens encodeCNFTokens
  rw [token_append_assoc_constructive]
  rw [cnfTokenWorkSymbols_append]
  rw [cnfTokenWorkSymbols_encodeUnaryTokens]
  change (List.replicate formula.variableCount cnfT ++ [cnfF]) ++ _ = _
  rw [workSymbol_append_assoc]
  rfl

def unmarkAssignmentWorkSymbol : WorkSymbol → WorkSymbol
  | ⟨.blank, .blank⟩ => ⟨.blank, .blank⟩
  | ⟨.blank, .zero⟩ => cnfF
  | ⟨.blank, .one⟩ => cnfT
  | ⟨.zero, .blank⟩ => ⟨.zero, .blank⟩
  | ⟨.zero, .zero⟩ => ⟨.zero, .zero⟩
  | ⟨.zero, .one⟩ => ⟨.zero, .one⟩
  | ⟨.one, .blank⟩ => ⟨.one, .blank⟩
  | ⟨.one, .zero⟩ => ⟨.one, .zero⟩
  | ⟨.one, .one⟩ => ⟨.one, .one⟩

theorem unmarkAssignmentWorkSymbol_false :
    unmarkAssignmentWorkSymbol cnfMarkFalse = cnfF := rfl

theorem unmarkAssignmentWorkSymbol_true :
    unmarkAssignmentWorkSymbol cnfMarkTrue = cnfT := rfl

theorem map_unmark_markedAssignment (assignment : BitString) :
    (markedAssignmentWorkSymbols assignment).map
        unmarkAssignmentWorkSymbol =
      assignmentWorkSymbols assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact congrArg (List.cons _) ih

theorem map_unmark_pushWorkLeft_marked
    (assignment : BitString) (left : List WorkSymbol) :
    (pushWorkLeft (markedAssignmentWorkSymbols assignment) left).map
        unmarkAssignmentWorkSymbol =
      pushWorkLeft (assignmentWorkSymbols assignment)
        (left.map unmarkAssignmentWorkSymbol) := by
  induction assignment generalizing left with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact ih (_ :: left)

theorem push_unmark_pushed_marked
    (assignment : BitString) (right : List WorkSymbol) :
    pushWorkLeft
        ((pushWorkLeft (markedAssignmentWorkSymbols assignment) []).map
          unmarkAssignmentWorkSymbol)
        right =
      assignmentWorkSymbols assignment ++ right := by
  rw [map_unmark_pushWorkLeft_marked]
  change pushWorkLeft (pushWorkLeft (assignmentWorkSymbols assignment) [])
      right = _
  exact pushWorkLeft_cancel (assignmentWorkSymbols assignment) right

theorem widthFindFormula_mark_step
    (leftSide formulaTail : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindFormula leftSide
          (cnfT :: formulaTail)) =
      some (workConfigAtWord CNFWorkState.widthToBoundary
        (cnfMarkTrue :: leftSide) formulaTail) := by
  rfl

theorem widthFindFormula_done_step
    (leftSide formulaTail : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindFormula leftSide
          (cnfF :: formulaTail)) =
      some (workConfigAtWord CNFWorkState.widthDoneToBoundary
        (cnfF :: leftSide) formulaTail) := by
  rfl

theorem widthFindAssignment_value_step
    (leftSide suffix : List WorkSymbol) (value : Bool) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindAssignment leftSide
          ((if value then cnfT else cnfF) :: suffix)) =
      some
        { state := CNFWorkState.widthBackAssignment
          tape := (WorkTape.focus leftSide
            (if value then cnfMarkTrue else cnfMarkFalse) suffix).moveLeft } := by
  cases value <;> rfl

set_option maxRecDepth 100000 in
theorem widthFindAssignment_short_step
    (leftSide suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.widthFindAssignment leftSide
          (cnfRootGuard :: suffix)) =
      some (workConfigAtWord CNFWorkState.reject leftSide
        (cnfRootGuard :: suffix)) := by
  exact cnfReject_run_one CNFWorkState.widthFindAssignment _ (by rfl) (by rfl)

theorem widthDonePastCounter_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDonePastCertificateCounter
          leftSide (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord
        CNFWorkState.widthDonePastCertificateCounter
        (cnfMarkFalse :: leftSide) suffix) := by
  rfl

theorem widthDonePastCounter_finish_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDonePastCertificateCounter
          leftSide (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
        (cnfFinish :: leftSide) suffix) := by
  rfl

theorem widthDoneToBoundary_guard_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord
        CNFWorkState.widthDonePastCertificateCounter
        (cnfBoundaryGuard :: leftSide) suffix) := by
  rfl

theorem widthRestoreAssignment_step
    (head : WorkSymbol) (leftTail rightSide : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
        leftTail (unmarkAssignmentWorkSymbol head :: rightSide)) := by
  cases allowed <;> rfl

theorem widthRestoreFormula_mark_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthRestoreFormula leftSide
          (cnfMarkTrue :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthRestoreFormula
        (cnfT :: leftSide) suffix) := by
  rfl

theorem widthRestoreFormula_done_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthRestoreFormula leftSide
          (cnfF :: suffix)) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfF :: leftSide) suffix) := by
  rfl

theorem pushWorkLeft_length (word left : List WorkSymbol) :
    (pushWorkLeft word left).length = word.length + left.length := by
  induction word generalizing left with
  | nil => exact (Nat.zero_add left.length).symm
  | cons symbol rest ih =>
      rw [pushWorkLeft_cons]
      rw [ih]
      change rest.length + Nat.succ left.length =
        Nat.succ rest.length + left.length
      rw [Nat.add_succ, Nat.succ_add]

theorem pushWorkLeft_allowed (Allowed : WorkSymbol → Prop)
    (word left : List WorkSymbol)
    (wordAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol)
    (leftAllowed : ∀ symbol, List.Mem symbol left → Allowed symbol)
    (symbol : WorkSymbol)
    (found : List.Mem symbol (pushWorkLeft word left)) : Allowed symbol := by
  induction word generalizing left with
  | nil => exact leftAllowed symbol found
  | cons head rest ih =>
      rw [pushWorkLeft_cons] at found
      apply ih (head :: left)
      · intro candidate inRest
        exact wordAllowed candidate (List.Mem.tail head inRest)
      · intro candidate inExtended
        cases inExtended with
        | head => exact wordAllowed head (List.Mem.head rest)
        | tail _ inLeft => exact leftAllowed candidate inLeft
      · exact found

/-- Constructive mapped left scan.  Unlike `workRunExact?_scanLeft`, each
crossed cell may be rewritten, so it directly models assignment restore. -/
theorem workRunExact?_scanLeftWrite (machine : WorkMachine)
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (write : WorkSymbol → WorkSymbol)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (workConfigAtLeftWord state (head :: leftTail) rightSide) =
        some (workConfigAtLeftWord state leftTail
          (write head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord state leftSuffix
        (pushWorkLeft (word.map write) rightSide)) := by
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
      exact ih (write head :: rightSide) hRest

theorem pushedMarkedAssignment_allowed (assignment : BitString)
    (symbol : WorkSymbol)
    (found : List.Mem symbol
      (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])) :
    AssignmentMarkSymbol symbol := by
  exact pushWorkLeft_allowed AssignmentMarkSymbol
    (markedAssignmentWorkSymbols assignment) []
    (markedAssignmentWorkSymbols_allowed assignment)
    (by intro candidate impossible; contradiction)
    symbol found

/-- The write-and-move-left assignment restoration is an exact inverse of
the outward marking pass, including value order. -/
theorem widthRestoreAssignment_scan (assignment : BitString)
    (leftSuffix rightSide : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
          (pushWorkLeft (markedAssignmentWorkSymbols assignment) [] ++
            leftSuffix)
          rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
        leftSuffix (assignmentWorkSymbols assignment ++ rightSide)) := by
  have hScan := workRunExact?_scanLeftWrite cnfWorkMachine
    CNFWorkState.widthRestoreAssignment AssignmentMarkSymbol
    unmarkAssignmentWorkSymbol widthRestoreAssignment_step
    (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])
    leftSuffix rightSide (pushedMarkedAssignment_allowed assignment)
  have hLength :
      (pushWorkLeft (markedAssignmentWorkSymbols assignment) []).length =
        assignment.length := by
    rw [pushWorkLeft_length]
    rw [markedAssignmentWorkSymbols_length]
    exact Nat.add_zero assignment.length
  rw [hLength] at hScan
  rw [push_unmark_pushed_marked] at hScan
  exact hScan

theorem replicate_markTrue_allowed (count : Nat)
    (symbol : WorkSymbol)
    (found : List.Mem symbol (List.replicate count cnfMarkTrue)) :
    symbol = cnfMarkTrue := by
  induction count with
  | zero => contradiction
  | succ count ih =>
      cases found with
      | head => rfl
      | tail _ tailFound => exact ih tailFound

/-- Constructive mapped right scan. -/
theorem workRunExact?_scanRightWrite (machine : WorkMachine)
    (state : Nat) (Allowed : WorkSymbol → Prop)
    (write : WorkSymbol → WorkSymbol)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine
          (workConfigAtWord state leftSide (head :: suffix)) =
        some (workConfigAtWord state (write head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtWord state leftSide (word ++ suffix)) =
      some (workConfigAtWord state
        (pushWorkLeft (word.map write) leftSide) suffix) := by
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
      exact ih (write head :: leftSide) hRest

theorem map_replicate_markTrue_to_true (count : Nat) :
    (List.replicate count cnfMarkTrue).map
        (fun _ => cnfT) =
      List.replicate count cnfT := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons cnfT) ih

theorem workSymbol_replicate_length (count : Nat)
    (symbol : WorkSymbol) :
    (List.replicate count symbol).length = count := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg Nat.succ ih

/-- Restoring the marked unary header writes exactly `T^count`, then crosses
the terminating `F` into clause evaluation. -/
theorem widthRestoreFormula_header (count : Nat)
    (leftSide formulaTail : List WorkSymbol) :
    workRunExact? cnfWorkMachine (count + 1)
        (workConfigAtWord CNFWorkState.widthRestoreFormula leftSide
          (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail)) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfF :: pushWorkLeft (List.replicate count cnfT) leftSide)
        formulaTail) := by
  have hMarks := workRunExact?_scanRightWrite cnfWorkMachine
    CNFWorkState.widthRestoreFormula
    (fun symbol => symbol = cnfMarkTrue)
    (fun _ => cnfT)
    (by
      intro foundLeft head suffix allowed
      cases allowed
      exact widthRestoreFormula_mark_step foundLeft suffix)
    (List.replicate count cnfMarkTrue) (cnfF :: formulaTail) leftSide
    (replicate_markTrue_allowed count)
  rw [map_replicate_markTrue_to_true] at hMarks
  rw [workSymbol_replicate_length] at hMarks
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthRestoreFormula_done_step
      (pushWorkLeft (List.replicate count cnfT) leftSide) formulaTail)
  exact workRunExact?_compose cnfWorkMachine count 1 _ _ _
    hMarks hFinish

/- Exact short/long comparison branches. -/

theorem widthDoneToBoundary_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneToBoundary
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.widthDoneToBoundary FormulaScanSymbol
    widthDoneToBoundary_step word suffix leftSide allowed

theorem widthDonePastCounter_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord
          CNFWorkState.widthDonePastCertificateCounter leftSide
          (word ++ suffix)) =
      some (workConfigAtWord
        CNFWorkState.widthDonePastCertificateCounter
        (pushWorkLeft word leftSide) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.widthDonePastCertificateCounter
    (fun symbol => symbol = cnfMarkFalse) _ word suffix leftSide allowed
  intro foundLeft head foundSuffix equal
  cases equal
  exact widthDonePastCounter_step foundLeft foundSuffix

theorem widthDoneCheckAssignment_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthDoneCheckAssignment leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
        (pushWorkLeft word leftSide) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.widthDoneCheckAssignment AssignmentMarkSymbol
    widthDoneCheckAssignment_step word suffix leftSide allowed

theorem widthDoneToAssignmentEnd_run
    (formulaTail counter markedAssignment leftSide suffix :
      List WorkSymbol)
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
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish :: (markedAssignment ++ next :: suffix)))))) =
      some (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
        (next :: suffix)) := by
  have hFormula := widthDoneToBoundary_scan formulaTail
    (cnfBoundaryGuard :: (counter ++
      (cnfFinish :: (markedAssignment ++ next :: suffix))))
    leftSide formulaAllowed
  have hGuard := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthDoneToBoundary_guard_step
      (pushWorkLeft formulaTail leftSide)
      (counter ++ (cnfFinish :: (markedAssignment ++ next :: suffix))))
  have hCounter := widthDonePastCounter_scan counter
    (cnfFinish :: markedAssignment ++ next :: suffix)
    (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide) counterAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthDonePastCounter_finish_step
      (pushWorkLeft counter
        (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
      (markedAssignment ++ next :: suffix))
  have hAssignment := widthDoneCheckAssignment_scan markedAssignment
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

set_option maxRecDepth 100000 in
theorem width_short_assignment_reject
    (formulaTail counter markedAssignment leftSide suffix :
      List WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        ((((formulaTail.length + 1) + counter.length + 1) +
          markedAssignment.length) + 1)
        (workConfigAtWord CNFWorkState.widthToBoundary leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish ::
              (markedAssignment ++ cnfRootGuard :: suffix)))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
        (cnfRootGuard :: suffix)) := by
  have hOut := widthToAssignmentPrefix_run formulaTail counter
    markedAssignment leftSide suffix cnfRootGuard formulaAllowed
    counterAllowed assignmentAllowed
  have hReject := widthFindAssignment_short_step
    (pushWorkLeft markedAssignment
      (cnfFinish :: pushWorkLeft counter
        (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))) suffix
  exact workRunExact?_compose cnfWorkMachine
    (((formulaTail.length + 1) + counter.length + 1) +
      markedAssignment.length)
    1 _ _ _ hOut hReject

set_option maxRecDepth 100000 in
theorem width_long_assignment_reject
    (formulaTail counter markedAssignment leftSide suffix :
      List WorkSymbol)
    (extra : Bool)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        ((((formulaTail.length + 1) + counter.length + 1) +
          markedAssignment.length) + 1)
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish :: (markedAssignment ++
              (if extra then cnfT else cnfF) :: suffix)))))) =
      some (workConfigAtWord CNFWorkState.reject
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
        ((if extra then cnfT else cnfF) :: suffix)) := by
  have hOut := widthDoneToAssignmentEnd_run formulaTail counter
    markedAssignment leftSide suffix (if extra then cnfT else cnfF)
    formulaAllowed counterAllowed assignmentAllowed
  have hReject :
      workRunExact? cnfWorkMachine 1
          (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
            (pushWorkLeft markedAssignment
              (cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
            ((if extra then cnfT else cnfF) :: suffix)) =
        some (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft markedAssignment
            (cnfFinish :: pushWorkLeft counter
              (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
          ((if extra then cnfT else cnfF) :: suffix)) := by
    cases extra
    · exact width_extraFalseAssignment_reject_run _ _
    · exact width_extraTrueAssignment_reject_run _ _
  exact workRunExact?_compose cnfWorkMachine
    (((formulaTail.length + 1) + counter.length + 1) +
      markedAssignment.length)
    1 _ _ _ hOut hReject

theorem pushWorkLeft_append_far (word farSide : List WorkSymbol) :
    pushWorkLeft word farSide = pushWorkLeft word [] ++ farSide := by
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  rw [pushWorkLeft_eq_pushScannedWorkSymbols]
  exact pushScannedWorkSymbols_append_far word [] farSide

theorem focus_pushed_moveLeft (word leftSuffix rightSide :
    List WorkSymbol) (delimiter head : WorkSymbol) :
    (WorkTape.focus (pushWorkLeft word (delimiter :: leftSuffix)) head
      rightSide).moveLeft =
      WorkTape.atLeftWord (head :: rightSide)
        (pushWorkLeft word [] ++ delimiter :: leftSuffix) := by
  rw [pushWorkLeft_append_far]
  cases pushed : pushWorkLeft word [] <;> rfl

theorem widthDoneCheckAssignment_root_step
    (markedAssignment counter formulaTail leftSide suffix :
      List WorkSymbol) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
          (pushWorkLeft markedAssignment
            (cnfFinish :: pushWorkLeft counter
              (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
          (cnfRootGuard :: suffix)) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
        (pushWorkLeft markedAssignment [] ++
          cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
        (cnfRootGuard :: suffix)) := by
  have hStep :
      workStep? cnfWorkMachine
          (workConfigAtWord CNFWorkState.widthDoneCheckAssignment
            (pushWorkLeft markedAssignment
              (cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
            (cnfRootGuard :: suffix)) =
        some
          { state := CNFWorkState.widthRestoreAssignment
            tape := (WorkTape.focus
              (pushWorkLeft markedAssignment
                (cnfFinish :: pushWorkLeft counter
                  (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide)))
              cnfRootGuard suffix).moveLeft } := by
    rfl
  have hOne := workRunExact?_one_of_step cnfWorkMachine _ _ hStep
  rw [focus_pushed_moveLeft] at hOne
  exact hOne

/-- Equal-width endpoint plus exact assignment restoration. -/
theorem width_equal_assignment_restored
    (formulaTail counter leftSide suffix : List WorkSymbol)
    (assignment : BitString)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine
        (((((formulaTail.length + 1) + counter.length + 1) +
          assignment.length) + 1) + assignment.length)
        (workConfigAtWord CNFWorkState.widthDoneToBoundary leftSide
          (formulaTail ++ (cnfBoundaryGuard :: (counter ++
            (cnfFinish :: (markedAssignmentWorkSymbols assignment ++
              cnfRootGuard :: suffix)))))) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
        (cnfFinish :: pushWorkLeft counter
          (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
        (assignmentWorkSymbols assignment ++ cnfRootGuard :: suffix)) := by
  have hOut := widthDoneToAssignmentEnd_run formulaTail counter
    (markedAssignmentWorkSymbols assignment) leftSide suffix cnfRootGuard
    formulaAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignment)
  rw [markedAssignmentWorkSymbols_length] at hOut
  have hRoot := widthDoneCheckAssignment_root_step
    (markedAssignmentWorkSymbols assignment) counter formulaTail leftSide suffix
  have hRestore := widthRestoreAssignment_scan assignment
    (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: pushWorkLeft formulaTail leftSide))
    (cnfRootGuard :: suffix)
  have hOutRoot := workRunExact?_compose cnfWorkMachine
    (((formulaTail.length + 1) + counter.length + 1) + assignment.length)
    1 _ _ _ hOut hRoot
  exact workRunExact?_compose cnfWorkMachine
    ((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1)
    assignment.length _ _ _ hOutRoot hRestore

/- Return leg of one successful width unit.  These are deliberately small
exact traces so the semantic induction can compose them without unfolding
the finite rule table. -/

theorem widthBackAssignment_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.widthBackAssignment
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackAssignment
        leftSuffix (pushWorkLeft word rightSide)) :=
  workRunExact?_scanLeft cnfWorkMachine CNFWorkState.widthBackAssignment
    AssignmentMarkSymbol widthBackAssignment_step word leftSuffix rightSide
    allowed

theorem widthBackAssignment_finish_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackAssignment
          (cnfFinish :: leftTail) rightSide) =
      some (workConfigAtLeftWord
        CNFWorkState.widthBackCertificateCounter leftTail
        (cnfFinish :: rightSide)) := by
  rfl

theorem widthBackCounter_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
        leftSuffix (pushWorkLeft word rightSide)) := by
  apply workRunExact?_scanLeft cnfWorkMachine
    CNFWorkState.widthBackCertificateCounter
    (fun symbol => symbol = cnfMarkFalse) _ word leftSuffix rightSide allowed
  intro head leftTail foundRight equal
  cases equal
  exact widthBackCounter_step leftTail foundRight

theorem widthBackCounter_boundary_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackCertificateCounter
          (cnfBoundaryGuard :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackFormula leftTail
        (cnfBoundaryGuard :: rightSide)) := by
  rfl


theorem widthBackFormula_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      FormulaOrCounterSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.widthBackFormula
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthBackFormula
        leftSuffix (pushWorkLeft word rightSide)) :=
  workRunExact?_scanLeft cnfWorkMachine CNFWorkState.widthBackFormula
    FormulaOrCounterSymbol widthBackFormula_step word leftSuffix rightSide
    allowed

theorem widthBackFormula_root_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthBackFormula
          (cnfRootGuard :: leftTail) rightSide) =
      some (workConfigAtWord CNFWorkState.seekFormulaStart
        (cnfRootGuard :: leftTail) rightSide) := by
  cases rightSide <;> rfl

theorem seekFormulaStart_counter_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.seekFormulaStart leftSide
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.seekFormulaStart
        (cnfMarkFalse :: leftSide) suffix) := by
  rfl

theorem seekFormulaStart_counter_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.seekFormulaStart leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.seekFormulaStart
        (pushWorkLeft word leftSide) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine CNFWorkState.seekFormulaStart
    (fun symbol => symbol = cnfMarkFalse) _ word suffix leftSide allowed
  intro foundLeft head foundSuffix equal
  cases equal
  exact seekFormulaStart_counter_step foundLeft foundSuffix

theorem seekFormulaStart_finish_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.seekFormulaStart leftSide
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (cnfFinish :: leftSide) suffix) := by
  rfl

theorem widthFindFormula_marked_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthFindFormula leftSide
          (cnfMarkTrue :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (cnfMarkTrue :: leftSide) suffix) := by
  rfl

theorem widthFindFormula_marked_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → symbol = cnfMarkTrue) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthFindFormula leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (pushWorkLeft word leftSide) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine CNFWorkState.widthFindFormula
    (fun symbol => symbol = cnfMarkTrue) _ word suffix leftSide allowed
  intro foundLeft head foundSuffix equal
  cases equal
  exact widthFindFormula_marked_step foundLeft foundSuffix

def widthMarkedFormulaPhysical
    (outerCounter headerPrefix formulaTail : List WorkSymbol) :
    List WorkSymbol :=
  outerCounter ++ cnfFinish ::
    (headerPrefix ++ cnfMarkTrue :: formulaTail)

def widthReturnSteps
    (outerCounter headerPrefix formulaTail counter markedAssignment :
      List WorkSymbol) : Nat :=
  ((((((((markedAssignment.length + 1) + counter.length) + 1) +
    (widthMarkedFormulaPhysical outerCounter headerPrefix
      formulaTail).length) + 1) + outerCounter.length) + 1) +
      (headerPrefix.length + 1))

theorem formulaScan_to_formulaOrCounter (symbol : WorkSymbol)
    (allowed : FormulaScanSymbol symbol) : FormulaOrCounterSymbol symbol := by
  cases allowed with
  | markTrue => exact .markTrue
  | f => exact .f
  | t => exact .t
  | sep => exact .sep
  | finish => exact .finish

theorem allowed_append (Allowed : WorkSymbol → Prop)
    (left right : List WorkSymbol)
    (leftAllowed : ∀ symbol, List.Mem symbol left → Allowed symbol)
    (rightAllowed : ∀ symbol, List.Mem symbol right → Allowed symbol)
    (symbol : WorkSymbol) (found : List.Mem symbol (left ++ right)) :
    Allowed symbol := by
  induction left generalizing symbol with
  | nil => exact rightAllowed symbol found
  | cons first rest ih =>
      cases found with
      | head => exact leftAllowed first (List.Mem.head rest)
      | tail _ inAppend =>
          exact ih
            (fun candidate inRest =>
              leftAllowed candidate (List.Mem.tail first inRest))
            symbol inAppend

theorem widthMarkedFormulaPhysical_allowed
    (outerCounter headerPrefix formulaTail : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (headerAllowed : ∀ symbol, List.Mem symbol headerPrefix →
      symbol = cnfMarkTrue)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (symbol : WorkSymbol)
    (found : List.Mem symbol
      (widthMarkedFormulaPhysical outerCounter headerPrefix
        formulaTail)) : FormulaOrCounterSymbol symbol := by
  unfold widthMarkedFormulaPhysical at found
  apply allowed_append FormulaOrCounterSymbol outerCounter
    (cnfFinish :: (headerPrefix ++ cnfMarkTrue :: formulaTail))
  · intro candidate inOuter
    have equal := outerAllowed candidate inOuter
    cases equal
    exact .markFalse
  · intro candidate inRest
    cases inRest with
    | head => exact .finish
    | tail _ inHeaderAndTail =>
        apply allowed_append FormulaOrCounterSymbol headerPrefix
          (cnfMarkTrue :: formulaTail)
        · intro headerSymbol inHeader
          have equal := headerAllowed headerSymbol inHeader
          cases equal
          exact .markTrue
        · intro tailSymbol inMarkedAndFormula
          cases inMarkedAndFormula with
          | head => exact .markTrue
          | tail _ inFormula =>
              exact formulaScan_to_formulaOrCounter tailSymbol
                (formulaAllowed tailSymbol inFormula)
        · exact inHeaderAndTail
  · exact found

theorem append_markTrue_allowed (headerPrefix : List WorkSymbol)
    (headerAllowed : ∀ symbol, List.Mem symbol headerPrefix →
      symbol = cnfMarkTrue)
    (symbol : WorkSymbol)
    (found : List.Mem symbol (headerPrefix ++ [cnfMarkTrue])) :
    symbol = cnfMarkTrue := by
  exact allowed_append (fun candidate => candidate = cnfMarkTrue)
    headerPrefix [cnfMarkTrue] headerAllowed
    (by
      intro candidate inSingleton
      cases inSingleton with
      | head => rfl
      | tail _ impossible => contradiction)
    symbol found

/-- Exact return leg after one header `T` has consumed one assignment value.
The input is the normalized nearest-first stack produced by the outward pass;
the output is precisely the next width-loop invariant. -/
theorem widthOneUnit_return
    (outerCounter headerPrefix formulaTail counter markedAssignment
      assignmentSuffix : List WorkSymbol)
    (markedValue : WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (headerAllowed : ∀ symbol, List.Mem symbol headerPrefix →
      symbol = cnfMarkTrue)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (widthReturnSteps outerCounter headerPrefix formulaTail
          counter markedAssignment)
        (workConfigAtLeftWord CNFWorkState.widthBackAssignment
          (pushWorkLeft markedAssignment [] ++
            cnfFinish ::
              (pushWorkLeft counter [] ++
                cnfBoundaryGuard ::
                  (pushWorkLeft
                    (widthMarkedFormulaPhysical outerCounter
                      headerPrefix formulaTail) [] ++ [cnfRootGuard])))
          (markedValue :: assignmentSuffix)) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (pushWorkLeft (headerPrefix ++ [cnfMarkTrue])
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
        (formulaTail ++
          (cnfBoundaryGuard :: (counter ++
            (cnfFinish ::
              (markedAssignment ++ markedValue :: assignmentSuffix)))))) := by
  let physical := widthMarkedFormulaPhysical outerCounter
    headerPrefix formulaTail
  let afterMarked := cnfFinish ::
    (pushWorkLeft counter [] ++
      cnfBoundaryGuard :: (pushWorkLeft physical [] ++ [cnfRootGuard]))
  have reversedMarkedAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft markedAssignment []) →
        AssignmentMarkSymbol symbol := by
    intro symbol found
    exact pushWorkLeft_allowed AssignmentMarkSymbol
      markedAssignment [] assignmentAllowed
      (by intro candidate impossible; contradiction) symbol found
  have hMarked := widthBackAssignment_scan
    (pushWorkLeft markedAssignment []) afterMarked
    (markedValue :: assignmentSuffix) reversedMarkedAllowed
  have markedLength : (pushWorkLeft markedAssignment []).length =
      markedAssignment.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero markedAssignment.length
  rw [markedLength] at hMarked
  rw [pushWorkLeft_cancel] at hMarked
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthBackAssignment_finish_step
      (pushWorkLeft counter [] ++
        cnfBoundaryGuard :: (pushWorkLeft physical [] ++ [cnfRootGuard]))
      (markedAssignment ++ markedValue :: assignmentSuffix))
  have reversedCounterAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft counter []) → symbol = cnfMarkFalse := by
    intro symbol found
    exact pushWorkLeft_allowed
      (fun candidate => candidate = cnfMarkFalse)
      counter [] counterAllowed
      (by intro candidate impossible; contradiction) symbol found
  have hCounter := widthBackCounter_scan
    (pushWorkLeft counter [])
    (cnfBoundaryGuard :: (pushWorkLeft physical [] ++ [cnfRootGuard]))
    (cnfFinish :: markedAssignment ++ markedValue :: assignmentSuffix)
    reversedCounterAllowed
  have counterLength : (pushWorkLeft counter []).length = counter.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero counter.length
  rw [counterLength] at hCounter
  rw [pushWorkLeft_cancel] at hCounter
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthBackCounter_boundary_step
      (pushWorkLeft physical [] ++ [cnfRootGuard])
      (counter ++ cnfFinish ::
        (markedAssignment ++ markedValue :: assignmentSuffix)))
  have physicalAllowed : ∀ symbol, List.Mem symbol physical →
      FormulaOrCounterSymbol symbol := by
    exact widthMarkedFormulaPhysical_allowed outerCounter
      headerPrefix formulaTail outerAllowed headerAllowed formulaAllowed
  have reversedPhysicalAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft physical []) →
        FormulaOrCounterSymbol symbol := by
    intro symbol found
    exact pushWorkLeft_allowed FormulaOrCounterSymbol physical []
      physicalAllowed (by intro candidate impossible; contradiction)
      symbol found
  have hPhysical := widthBackFormula_scan
    (pushWorkLeft physical []) [cnfRootGuard]
    (cnfBoundaryGuard :: counter ++ cnfFinish ::
      (markedAssignment ++ markedValue :: assignmentSuffix))
    reversedPhysicalAllowed
  have physicalLength : (pushWorkLeft physical []).length = physical.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero physical.length
  rw [physicalLength] at hPhysical
  rw [pushWorkLeft_cancel] at hPhysical
  let returnTail := cnfBoundaryGuard :: (counter ++
    (cnfFinish :: (markedAssignment ++ markedValue :: assignmentSuffix)))
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthBackFormula_root_step []
      (physical ++ returnTail))
  have physicalSplit :
      physical ++ returnTail =
        outerCounter ++
          ((cnfFinish ::
            (headerPrefix ++ cnfMarkTrue :: formulaTail)) ++ returnTail) := by
    unfold physical widthMarkedFormulaPhysical
    exact workSymbol_append_assoc outerCounter
      (cnfFinish :: (headerPrefix ++ cnfMarkTrue :: formulaTail))
      returnTail
  have hOuter := seekFormulaStart_counter_scan outerCounter
    ((cnfFinish ::
      (headerPrefix ++ cnfMarkTrue :: formulaTail)) ++ returnTail)
    [cnfRootGuard] outerAllowed
  have hOuterFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (seekFormulaStart_finish_step
      (pushWorkLeft outerCounter [cnfRootGuard])
      ((headerPrefix ++ cnfMarkTrue :: formulaTail) ++ returnTail))
  have formulaSplit :
      (headerPrefix ++ cnfMarkTrue :: formulaTail) ++ returnTail =
        (headerPrefix ++ [cnfMarkTrue]) ++
          (formulaTail ++ returnTail) := by
    calc
      (headerPrefix ++ cnfMarkTrue :: formulaTail) ++ returnTail =
          headerPrefix ++
            ((cnfMarkTrue :: formulaTail) ++ returnTail) :=
        workSymbol_append_assoc headerPrefix
          (cnfMarkTrue :: formulaTail)
          returnTail
      _ = headerPrefix ++
          (cnfMarkTrue :: (formulaTail ++ returnTail)) := rfl
      _ = headerPrefix ++
          ([cnfMarkTrue] ++ (formulaTail ++ returnTail)) := rfl
      _ = (headerPrefix ++ [cnfMarkTrue]) ++
          (formulaTail ++ returnTail) :=
        (workSymbol_append_assoc headerPrefix [cnfMarkTrue]
          (formulaTail ++ returnTail)).symm
  have hHeader := widthFindFormula_marked_scan
    (headerPrefix ++ [cnfMarkTrue])
    (formulaTail ++ returnTail)
    (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
    (append_markTrue_allowed headerPrefix headerAllowed)
  have headerLength : (headerPrefix ++ [cnfMarkTrue]).length =
      headerPrefix.length + 1 := by
    rw [workSymbol_length_append]
    rfl
  rw [headerLength] at hHeader
  have h1 := workRunExact?_compose cnfWorkMachine
    markedAssignment.length 1 _ _ _ hMarked hFinish
  have h2 := workRunExact?_compose cnfWorkMachine
    (markedAssignment.length + 1) counter.length _ _ _ h1 hCounter
  have h3 := workRunExact?_compose cnfWorkMachine
    ((markedAssignment.length + 1) + counter.length) 1 _ _ _ h2 hBoundary
  have h4 := workRunExact?_compose cnfWorkMachine
    (((markedAssignment.length + 1) + counter.length) + 1)
    physical.length _ _ _ h3 hPhysical
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((markedAssignment.length + 1) + counter.length) + 1) +
      physical.length) 1 _ _ _ h4 hRoot
  rw [physicalSplit] at h5
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((markedAssignment.length + 1) + counter.length) + 1) +
      physical.length) + 1) outerCounter.length _ _ _ h5 hOuter
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((markedAssignment.length + 1) + counter.length) + 1) +
      physical.length) + 1) + outerCounter.length) 1 _ _ _ h6 hOuterFinish
  rw [formulaSplit] at h7
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((markedAssignment.length + 1) + counter.length) + 1) +
      physical.length) + 1) + outerCounter.length) + 1)
    (headerPrefix.length + 1) _ _ _ h7 hHeader
  unfold widthReturnSteps
  unfold returnTail at h8
  exact h8

theorem pushWorkLeft_append_word
    (first second farSide : List WorkSymbol) :
    pushWorkLeft (first ++ second) farSide =
      pushWorkLeft second (pushWorkLeft first farSide) := by
  induction first generalizing farSide with
  | nil => rfl
  | cons symbol rest ih => exact ih (symbol :: farSide)

theorem widthMarkedFormulaPhysical_push
    (outerCounter headerPrefix formulaTail : List WorkSymbol) :
    pushWorkLeft formulaTail
        (cnfMarkTrue :: pushWorkLeft headerPrefix
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) =
      pushWorkLeft
          (widthMarkedFormulaPhysical outerCounter headerPrefix
            formulaTail) [] ++ [cnfRootGuard] := by
  calc
    pushWorkLeft formulaTail
        (cnfMarkTrue :: pushWorkLeft headerPrefix
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) =
      pushWorkLeft (cnfMarkTrue :: formulaTail)
        (pushWorkLeft headerPrefix
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) := rfl
    _ = pushWorkLeft (headerPrefix ++ cnfMarkTrue :: formulaTail)
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]) :=
      (pushWorkLeft_append_word headerPrefix
        (cnfMarkTrue :: formulaTail)
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])).symm
    _ = pushWorkLeft
        (cnfFinish :: (headerPrefix ++ cnfMarkTrue :: formulaTail))
        (pushWorkLeft outerCounter [cnfRootGuard]) := rfl
    _ = pushWorkLeft
        (outerCounter ++
          cnfFinish :: (headerPrefix ++ cnfMarkTrue :: formulaTail))
        [cnfRootGuard] :=
      (pushWorkLeft_append_word outerCounter
        (cnfFinish :: (headerPrefix ++ cnfMarkTrue :: formulaTail))
        [cnfRootGuard]).symm
    _ = pushWorkLeft
          (widthMarkedFormulaPhysical outerCounter headerPrefix
            formulaTail) [cnfRootGuard] := rfl
    _ = pushWorkLeft
          (widthMarkedFormulaPhysical outerCounter headerPrefix
            formulaTail) [] ++ [cnfRootGuard] :=
      pushWorkLeft_append_far
        (widthMarkedFormulaPhysical outerCounter headerPrefix
          formulaTail) [cnfRootGuard]

def widthOutwardSteps
    (formulaTail counter markedAssignment : List WorkSymbol) : Nat :=
  ((formulaTail.length + 1) + counter.length + 1) +
    markedAssignment.length

def widthOneUnitSteps
    (outerCounter headerPrefix formulaTail counter markedAssignment :
      List WorkSymbol) : Nat :=
  ((1 + widthOutwardSteps formulaTail counter markedAssignment) + 1) +
    widthReturnSteps outerCounter headerPrefix formulaTail counter
      markedAssignment

theorem widthFindAssignment_value_normalized
    (outerCounter headerPrefix formulaTail counter markedAssignment
      assignmentSuffix : List WorkSymbol)
    (value : Bool) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.widthFindAssignment
          (pushWorkLeft markedAssignment
            (cnfFinish :: pushWorkLeft counter
              (cnfBoundaryGuard ::
                pushWorkLeft formulaTail
                  (cnfMarkTrue :: pushWorkLeft headerPrefix
                    (cnfFinish ::
                      pushWorkLeft outerCounter [cnfRootGuard])))))
          ((if value then cnfT else cnfF) :: assignmentSuffix)) =
      some (workConfigAtLeftWord CNFWorkState.widthBackAssignment
        (pushWorkLeft markedAssignment [] ++
          cnfFinish ::
            (pushWorkLeft counter [] ++
              cnfBoundaryGuard ::
                (pushWorkLeft
                  (widthMarkedFormulaPhysical outerCounter
                    headerPrefix formulaTail) [] ++ [cnfRootGuard])))
        ((if value then cnfMarkTrue else cnfMarkFalse) ::
          assignmentSuffix)) := by
  have hStep := widthFindAssignment_value_step
    (pushWorkLeft markedAssignment
      (cnfFinish :: pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail
            (cnfMarkTrue :: pushWorkLeft headerPrefix
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])))))
    assignmentSuffix value
  have hOne := workRunExact?_one_of_step cnfWorkMachine _ _ hStep
  have hTape :
      (WorkTape.focus
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail
                (cnfMarkTrue :: pushWorkLeft headerPrefix
                  (cnfFinish ::
                    pushWorkLeft outerCounter [cnfRootGuard])))))
        (if value then cnfMarkTrue else cnfMarkFalse)
        assignmentSuffix).moveLeft =
        WorkTape.atLeftWord
          ((if value then cnfMarkTrue else cnfMarkFalse) :: assignmentSuffix)
          (pushWorkLeft markedAssignment [] ++
            cnfFinish ::
              (pushWorkLeft counter [] ++
                cnfBoundaryGuard ::
                  (pushWorkLeft
                    (widthMarkedFormulaPhysical outerCounter
                      headerPrefix formulaTail) [] ++ [cnfRootGuard]))) := by
    calc
      (WorkTape.focus
        (pushWorkLeft markedAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail
                (cnfMarkTrue :: pushWorkLeft headerPrefix
                  (cnfFinish ::
                    pushWorkLeft outerCounter [cnfRootGuard])))))
        (if value then cnfMarkTrue else cnfMarkFalse)
        assignmentSuffix).moveLeft =
          WorkTape.atLeftWord
            ((if value then cnfMarkTrue else cnfMarkFalse) :: assignmentSuffix)
            (pushWorkLeft markedAssignment [] ++
              cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard ::
                  pushWorkLeft formulaTail
                    (cnfMarkTrue :: pushWorkLeft headerPrefix
                      (cnfFinish ::
                        pushWorkLeft outerCounter [cnfRootGuard])))) :=
        focus_pushed_moveLeft markedAssignment
          (pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail
                (cnfMarkTrue :: pushWorkLeft headerPrefix
                  (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))))
          assignmentSuffix cnfFinish
          (if value then cnfMarkTrue else cnfMarkFalse)
      _ = WorkTape.atLeftWord
          ((if value then cnfMarkTrue else cnfMarkFalse) :: assignmentSuffix)
          (pushWorkLeft markedAssignment [] ++
            cnfFinish ::
              (pushWorkLeft counter [] ++
                cnfBoundaryGuard ::
                  (pushWorkLeft
                    (widthMarkedFormulaPhysical outerCounter
                      headerPrefix formulaTail) [] ++ [cnfRootGuard]))) := by
        rw [pushWorkLeft_append_far counter]
        rw [widthMarkedFormulaPhysical_push]
  rw [hTape] at hOne
  exact hOne

/-- One exact successful width iteration: mark one header `T`, consume one
assignment value, return to the next formula-header cell, and preserve every
other cell.  This is the induction step for the `Nat`/assignment case split. -/
theorem widthOneUnit_run
    (outerCounter headerPrefix formulaTail counter markedAssignment
      assignmentSuffix : List WorkSymbol)
    (value : Bool)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (headerAllowed : ∀ symbol, List.Mem symbol headerPrefix →
      symbol = cnfMarkTrue)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (assignmentAllowed : ∀ symbol, List.Mem symbol markedAssignment →
      AssignmentMarkSymbol symbol) :
    workRunExact? cnfWorkMachine
        (widthOneUnitSteps outerCounter headerPrefix formulaTail
          counter markedAssignment)
        (workConfigAtWord CNFWorkState.widthFindFormula
          (pushWorkLeft headerPrefix
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
          (cnfT :: (formulaTail ++
            (cnfBoundaryGuard :: (counter ++
              (cnfFinish :: (markedAssignment ++
                (if value then cnfT else cnfF) :: assignmentSuffix))))))) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (pushWorkLeft (headerPrefix ++ [cnfMarkTrue])
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
      (formulaTail ++
          (cnfBoundaryGuard :: (counter ++
            (cnfFinish ::
              (markedAssignment ++
                (if value then cnfMarkTrue else cnfMarkFalse) ::
                  assignmentSuffix)))))) := by
  let outwardSuffix := cnfBoundaryGuard :: (counter ++
    (cnfFinish :: (markedAssignment ++
      (if value then cnfT else cnfF) :: assignmentSuffix)))
  have hMark := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthFindFormula_mark_step
      (pushWorkLeft headerPrefix
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
      (formulaTail ++ outwardSuffix))
  have hOut := widthToAssignmentPrefix_run formulaTail counter
    markedAssignment
    (cnfMarkTrue :: pushWorkLeft headerPrefix
      (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
    assignmentSuffix (if value then cnfT else cnfF)
    formulaAllowed counterAllowed assignmentAllowed
  have hValue := widthFindAssignment_value_normalized outerCounter
    headerPrefix formulaTail counter markedAssignment assignmentSuffix value
  have hReturn := widthOneUnit_return outerCounter headerPrefix
    formulaTail counter markedAssignment assignmentSuffix
    (if value then cnfMarkTrue else cnfMarkFalse)
    outerAllowed headerAllowed formulaAllowed counterAllowed assignmentAllowed
  have hMarkOut := workRunExact?_compose cnfWorkMachine 1
    (widthOutwardSteps formulaTail counter markedAssignment)
    _ _ _ hMark (by
      unfold widthOutwardSteps
      exact hOut)
  have hThroughValue := workRunExact?_compose cnfWorkMachine
    (1 + widthOutwardSteps formulaTail counter markedAssignment) 1
    _ _ _ hMarkOut hValue
  have hComplete := workRunExact?_compose cnfWorkMachine
    ((1 + widthOutwardSteps formulaTail counter markedAssignment) + 1)
    (widthReturnSteps outerCounter headerPrefix formulaTail counter
      markedAssignment)
    _ _ _ hThroughValue hReturn
  unfold widthOneUnitSteps
  unfold outwardSuffix at hComplete
  exact hComplete

/- Phase-cost wrappers. -/

def widthInductionLedger (n rounds : Nat) : Nat :=
  (rounds * cnfShiftedWorkSpan n) * 8 + cnfShiftedWorkSpan n * 8

theorem widthInductionLedger_le_singlePhase (n rounds : Nat)
    (roundsBound : rounds ≤ n) :
    widthInductionLedger n rounds ≤ cnfSinglePhaseBudget n := by
  have nToSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have roundsToSpan : rounds ≤ cnfShiftedWorkSpan n :=
    Nat.le_trans roundsBound nToSpan
  have roundsProduct :
      rounds * cnfShiftedWorkSpan n ≤
        cnfShiftedWorkSpan n * cnfShiftedWorkSpan n :=
    Nat.mul_le_mul_right (cnfShiftedWorkSpan n) roundsToSpan
  have roundsScaled :
      (rounds * cnfShiftedWorkSpan n) * 8 ≤
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 8 :=
    Nat.mul_le_mul_right 8 roundsProduct
  have finalToSquare : cnfShiftedWorkSpan n ≤
      cnfShiftedWorkSpan n * cnfShiftedWorkSpan n :=
    by
      have positive : 1 ≤ n + 2 :=
        Nat.succ_le_succ (Nat.zero_le (n + 1))
      unfold cnfShiftedWorkSpan
      exact Nat.le_mul_of_pos_right (n + 2) positive
  have finalScaled : cnfShiftedWorkSpan n * 8 ≤
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 8 :=
    Nat.mul_le_mul_right 8 finalToSquare
  have combined := Nat.add_le_add roundsScaled finalScaled
  have normalized :
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 8 +
          (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 8 =
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 16 := by
    rw [← Nat.mul_add]
  rw [normalized] at combined
  unfold widthInductionLedger
  have squareToCube := cnfShiftedSquare_le_phaseCube n
  have scaledToCube :
      (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 16 ≤
        cnfWorkPhaseCube n * 16 :=
    Nat.mul_le_mul_right 16 squareToCube
  unfold cnfSinglePhaseBudget
  exact Nat.le_trans combined scaledToCube

/-- Attach the cubic phase certificate to any exact width trace whose
semantic induction has discharged the eight-plus-eight ledger. -/
theorem widthExact_run_within_singlePhase
    (n rounds steps : Nat) (start final : WorkConfiguration)
    (exactRun : workRunExact? cnfWorkMachine steps start = some final)
    (roundsBound : rounds ≤ n)
    (stepsBound : steps ≤ widthInductionLedger n rounds) :
    steps ≤ cnfSinglePhaseBudget n ∧
      workRunExact? cnfWorkMachine steps start = some final := by
  exact ⟨Nat.le_trans stepsBound
    (widthInductionLedger_le_singlePhase n rounds roundsBound), exactRun⟩

private inductive WidthCostAtom where
  | unit
  | formula
  | counter
  | marked
  | outer
  | header

private def widthCostAtomRank : WidthCostAtom → Nat
  | .marked => 0
  | .counter => 1
  | .header => 2
  | .formula => 3
  | .outer => 4
  | .unit => 5

private def widthCostAtomValue
    (unit formula counter marked outer header : Nat) :
    WidthCostAtom → Nat
  | .unit => unit
  | .formula => formula
  | .counter => counter
  | .marked => marked
  | .outer => outer
  | .header => header

private def widthCostAtomSum
    (unit formula counter marked outer header : Nat) :
    List WidthCostAtom → Nat
  | [] => 0
  | atom :: rest =>
      widthCostAtomValue unit formula counter marked outer header atom +
        widthCostAtomSum unit formula counter marked outer header rest

private def widthCostAtomInsert
    (atom : WidthCostAtom) : List WidthCostAtom → List WidthCostAtom
  | [] => [atom]
  | head :: rest =>
      if widthCostAtomRank atom ≤ widthCostAtomRank head then
        atom :: head :: rest
      else
        head :: widthCostAtomInsert atom rest

private def widthCostAtomSort :
    List WidthCostAtom → List WidthCostAtom
  | [] => []
  | atom :: rest => widthCostAtomInsert atom (widthCostAtomSort rest)

private theorem widthCostAtomSum_insert
    (unit formula counter marked outer header : Nat)
    (atom : WidthCostAtom) (items : List WidthCostAtom) :
    widthCostAtomSum unit formula counter marked outer header
        (widthCostAtomInsert atom items) =
      widthCostAtomValue unit formula counter marked outer header atom +
        widthCostAtomSum unit formula counter marked outer header items := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      cases atom <;> cases head <;> try rfl
      all_goals
        change _ + widthCostAtomSum unit formula counter marked outer header
            (widthCostAtomInsert _ rest) = _
        rw [ih]
        exact Nat.add_left_comm _ _ _

private theorem widthCostAtomSum_sort
    (unit formula counter marked outer header : Nat)
    (items : List WidthCostAtom) :
    widthCostAtomSum unit formula counter marked outer header
        (widthCostAtomSort items) =
      widthCostAtomSum unit formula counter marked outer header items := by
  induction items with
  | nil => rfl
  | cons atom rest ih =>
      change widthCostAtomSum unit formula counter marked outer header
          (widthCostAtomInsert atom (widthCostAtomSort rest)) = _
      rw [widthCostAtomSum_insert]
      rw [ih]
      rfl

private inductive WidthCostExpr where
  | atom : WidthCostAtom → WidthCostExpr
  | add : WidthCostExpr → WidthCostExpr → WidthCostExpr

private def widthCostExprValue
    (unit formula counter marked outer header : Nat) :
    WidthCostExpr → Nat
  | .atom atom =>
      widthCostAtomValue unit formula counter marked outer header atom
  | .add left right =>
      widthCostExprValue unit formula counter marked outer header left +
        widthCostExprValue unit formula counter marked outer header right

private def widthCostExprAtoms : WidthCostExpr → List WidthCostAtom
  | .atom atom => [atom]
  | .add left right => widthCostExprAtoms left ++ widthCostExprAtoms right

private theorem widthCostAtomSum_append
    (unit formula counter marked outer header : Nat)
    (left right : List WidthCostAtom) :
    widthCostAtomSum unit formula counter marked outer header
        (left ++ right) =
      widthCostAtomSum unit formula counter marked outer header left +
        widthCostAtomSum unit formula counter marked outer header right := by
  induction left with
  | nil => exact (Nat.zero_add _).symm
  | cons atom rest ih =>
      change _ + widthCostAtomSum unit formula counter marked outer header
          (rest ++ right) =
        (_ + widthCostAtomSum unit formula counter marked outer header rest) +
          widthCostAtomSum unit formula counter marked outer header right
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

private theorem widthCostExprValue_atoms
    (unit formula counter marked outer header : Nat)
    (expression : WidthCostExpr) :
    widthCostExprValue unit formula counter marked outer header expression =
      widthCostAtomSum unit formula counter marked outer header
        (widthCostExprAtoms expression) := by
  induction expression with
  | atom atom => exact (Nat.add_zero _).symm
  | add left right leftIH rightIH =>
      rw [widthCostExprAtoms, widthCostAtomSum_append]
      change widthCostExprValue unit formula counter marked outer header left +
          widthCostExprValue unit formula counter marked outer header right = _
      rw [leftIH, rightIH]

private def widthRawCostExpr : WidthCostExpr :=
  let u := WidthCostExpr.atom .unit
  let f := WidthCostExpr.atom .formula
  let c := WidthCostExpr.atom .counter
  let m := WidthCostExpr.atom .marked
  let o := WidthCostExpr.atom .outer
  let h := WidthCostExpr.atom .header
  let first := .add (.add (.add (.add f u) c) u) m
  let nested := .add o (.add (.add h (.add f u)) u)
  let second := .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add m u) c) u) nested) u) o) u)
    (.add h u)
  .add (.add (.add u first) u) second

private def widthTargetUnitsExpr : WidthCostExpr :=
  let u := WidthCostExpr.atom .unit
  .add
    (.add
      (.add
        (.add
          (.add
            (.add
              (.add
                (.add
                  (.add
                    (.add u u) u) u) u) u) u) u) u) u)
    u

private def widthTargetCostExpr : WidthCostExpr :=
  let f := WidthCostExpr.atom .formula
  let c := WidthCostExpr.atom .counter
  let m := WidthCostExpr.atom .marked
  let o := WidthCostExpr.atom .outer
  let h := WidthCostExpr.atom .header
  .add
    (.add
      (.add (.add m c) (.add m c))
      (.add (.add (.add h f) (.add h f)) (.add o o)))
    widthTargetUnitsExpr

private theorem width_cost_regroup_clean
    (unit formula counter marked outer header : Nat) :
    unit + (formula + unit + counter + unit + marked) + unit +
        (marked + unit + counter + unit +
              (outer + (header + (formula + unit) + unit)) +
            unit + outer + unit + (header + unit)) =
      (((marked + counter) + (marked + counter)) +
          (((header + formula) + (header + formula)) + (outer + outer))) +
        ((((((((((unit + unit) + unit) + unit) + unit) + unit) + unit) +
          unit) + unit) + unit) + unit) := by
  have rawValue :
      widthCostExprValue unit formula counter marked outer header
          widthRawCostExpr =
        unit + (formula + unit + counter + unit + marked) + unit +
          (marked + unit + counter + unit +
                (outer + (header + (formula + unit) + unit)) +
              unit + outer + unit + (header + unit)) := rfl
  have targetValue :
      widthCostExprValue unit formula counter marked outer header
          widthTargetCostExpr =
        (((marked + counter) + (marked + counter)) +
            (((header + formula) + (header + formula)) + (outer + outer))) +
          ((((((((((unit + unit) + unit) + unit) + unit) + unit) + unit) +
            unit) + unit) + unit) + unit) := rfl
  have sortedAtoms :
      widthCostAtomSort (widthCostExprAtoms widthRawCostExpr) =
        widthCostAtomSort (widthCostExprAtoms widthTargetCostExpr) := rfl
  calc
    unit + (formula + unit + counter + unit + marked) + unit +
        (marked + unit + counter + unit +
              (outer + (header + (formula + unit) + unit)) +
            unit + outer + unit + (header + unit)) =
      widthCostExprValue unit formula counter marked outer header
        widthRawCostExpr := rawValue.symm
    _ = widthCostAtomSum unit formula counter marked outer header
          (widthCostExprAtoms widthRawCostExpr) :=
      widthCostExprValue_atoms unit formula counter marked outer header
        widthRawCostExpr
    _ = widthCostAtomSum unit formula counter marked outer header
          (widthCostAtomSort (widthCostExprAtoms widthRawCostExpr)) :=
      (widthCostAtomSum_sort unit formula counter marked outer header
        (widthCostExprAtoms widthRawCostExpr)).symm
    _ = widthCostAtomSum unit formula counter marked outer header
          (widthCostAtomSort (widthCostExprAtoms widthTargetCostExpr)) :=
      congrArg
        (widthCostAtomSum unit formula counter marked outer header)
        sortedAtoms
    _ = widthCostAtomSum unit formula counter marked outer header
          (widthCostExprAtoms widthTargetCostExpr) :=
      widthCostAtomSum_sort unit formula counter marked outer header
        (widthCostExprAtoms widthTargetCostExpr)
    _ = widthCostExprValue unit formula counter marked outer header
          widthTargetCostExpr :=
      (widthCostExprValue_atoms unit formula counter marked outer header
        widthTargetCostExpr).symm
    _ = (((marked + counter) + (marked + counter)) +
          (((header + formula) + (header + formula)) + (outer + outer))) +
        ((((((((((unit + unit) + unit) + unit) + unit) + unit) + unit) +
          unit) + unit) + unit) + unit) := targetValue

private theorem eleven_le_sixteen_clean : 11 ≤ 16 := by
  change 11 ≤ 11 + 5
  exact Nat.le_add_right 11 5

private theorem widthNatMulAssocClean (a b c : Nat) :
    (a * b) * c = a * (b * c) := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a * b) * c + a * b = a * (b * c + b)
      rw [ih, Nat.mul_add]

private theorem widthNatAddFourReorder (a b c d : Nat) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [Nat.add_assoc a b (c + d)]
  rw [← Nat.add_assoc b c d]
  rw [Nat.add_comm b c]
  rw [Nat.add_assoc c b d]
  rw [← Nat.add_assoc a c (b + d)]

private theorem eight_doubles_normalize (n : Nat) :
    ((n + n) + (n + n)) + ((n + n) + (n + n)) = n * 8 := by
  calc
    ((n + n) + (n + n)) + ((n + n) + (n + n)) =
        2 * ((n + n) + (n + n)) := (Nat.two_mul _).symm
    _ = 2 * (2 * (n + n)) :=
      congrArg (Nat.mul 2) (Nat.two_mul (n + n)).symm
    _ = 2 * (2 * (2 * n)) :=
      congrArg (Nat.mul 2)
        (congrArg (Nat.mul 2) (Nat.two_mul n).symm)
    _ = (2 * 2) * (2 * n) :=
      (widthNatMulAssocClean 2 2 (2 * n)).symm
    _ = ((2 * 2) * 2) * n :=
      (widthNatMulAssocClean (2 * 2) 2 n).symm
    _ = n * 8 := Nat.mul_comm 8 n

private theorem natAddMulClean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      rw [ih]
      exact widthNatAddFourReorder (a * c) (b * c) a b

private theorem target_normalization_clean (n : Nat) :
    (((n + n) + (n + n)) + ((n + n) + (n + n))) + 16 =
      (n + 2) * 8 := by
  rw [eight_doubles_normalize]
  change n * 8 + 2 * 8 = (n + 2) * 8
  exact (natAddMulClean n 2 8).symm

private theorem width_marked_physical_length_clean
    (outer header tail : List WorkSymbol) :
    (widthMarkedFormulaPhysical outer header tail).length =
      outer.length + (header.length + (tail.length + 1) + 1) := by
  unfold widthMarkedFormulaPhysical
  rw [workSymbol_length_append]
  change outer.length + Nat.succ (header ++ cnfMarkTrue :: tail).length = _
  rw [workSymbol_length_append]
  rfl

theorem widthOneUnitSteps_le_eightSpan (n : Nat)
    (outerCounter headerPrefix formulaTail counter markedAssignment :
      List WorkSymbol)
    (formulaPartition :
      headerPrefix.length + 1 + formulaTail.length ≤ outerCounter.length)
    (assignmentPrefix : markedAssignment.length ≤ counter.length)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthOneUnitSteps outerCounter headerPrefix formulaTail counter
        markedAssignment ≤
      cnfShiftedWorkSpan n * 8 := by
  have headerFormulaBound :
      headerPrefix.length + formulaTail.length ≤ outerCounter.length := by
    exact Nat.le_trans
      (Nat.add_le_add_right
        (Nat.le_add_right headerPrefix.length 1) formulaTail.length)
      formulaPartition
  have assignmentCounterBound :
      markedAssignment.length + counter.length ≤ n + n := by
    exact Nat.add_le_add
      (Nat.le_trans assignmentPrefix counterBound) counterBound
  have assignmentCounterTwice :
      (markedAssignment.length + counter.length) +
          (markedAssignment.length + counter.length) ≤
        (n + n) + (n + n) := by
    exact Nat.add_le_add assignmentCounterBound assignmentCounterBound
  have headerFormulaToN :
      headerPrefix.length + formulaTail.length ≤ n :=
    Nat.le_trans headerFormulaBound outerBound
  have headerFormulaTwice :
      (headerPrefix.length + formulaTail.length) +
          (headerPrefix.length + formulaTail.length) ≤
        n + n := by
    exact Nat.add_le_add headerFormulaToN headerFormulaToN
  have outerTwice : outerCounter.length + outerCounter.length ≤ n + n := by
    exact Nat.add_le_add outerBound outerBound
  have formulaAndOuterTwice :
      ((headerPrefix.length + formulaTail.length) +
          (headerPrefix.length + formulaTail.length)) +
          (outerCounter.length + outerCounter.length) ≤
        (n + n) + (n + n) := by
    exact Nat.add_le_add headerFormulaTwice outerTwice
  have allVariableOccurrences :
      ((markedAssignment.length + counter.length) +
          (markedAssignment.length + counter.length)) +
          (((headerPrefix.length + formulaTail.length) +
            (headerPrefix.length + formulaTail.length)) +
            (outerCounter.length + outerCounter.length)) ≤
        ((n + n) + (n + n)) + ((n + n) + (n + n)) := by
    exact Nat.add_le_add assignmentCounterTwice formulaAndOuterTwice
  have variablesAndConstant :
      (((markedAssignment.length + counter.length) +
          (markedAssignment.length + counter.length)) +
          (((headerPrefix.length + formulaTail.length) +
            (headerPrefix.length + formulaTail.length)) +
            (outerCounter.length + outerCounter.length))) + 11 ≤
        (((n + n) + (n + n)) + ((n + n) + (n + n))) + 16 := by
    exact Nat.add_le_add allVariableOccurrences eleven_le_sixteen_clean
  have targetNormalization :
      (((n + n) + (n + n)) + ((n + n) + (n + n))) + 16 =
        (n + 2) * 8 := by
    exact target_normalization_clean n
  unfold widthOneUnitSteps widthOutwardSteps
    widthReturnSteps cnfShiftedWorkSpan
  rw [width_marked_physical_length_clean]
  rw [width_cost_regroup_clean]
  exact Nat.le_trans variablesAndConstant (Nat.le_of_eq targetNormalization)

theorem formulaVariableCount_le_encodedTokens (formula : CNFFormula) :
    formula.variableCount ≤ (encodeFormulaTokens formula).length := by
  have shape := cnfTokenWorkSymbols_formula_header formula
  have lengths := congrArg List.length shape
  rw [cnfTokenWorkSymbols_length] at lengths
  rw [workSymbol_length_append] at lengths
  rw [workSymbol_replicate_length] at lengths
  exact Nat.le_trans
    (Nat.le_add_right formula.variableCount
      (cnfF :: cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish])).length)
    (Nat.le_of_eq lengths.symm)


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

theorem decoded_formulaVariableCount_le_pair_size
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    formula.variableCount ≤
      BitString.size (BitString.pair input certificate) := by
  have variableToTokens := formulaVariableCount_le_encodedTokens formula
  have tokensToCombined : (encodeFormulaTokens formula).length ≤
      (encodeFormulaTokens formula).length + assignment.length :=
    Nat.le_add_right (encodeFormulaTokens formula).length assignment.length
  have combinedToPair :=
    FrameTraceDesign.decoded_frame_payload_length_le_pair_size
      input certificate formula assignment formulaDecoded assignmentDecoded
  exact Nat.le_trans variableToTokens
    (Nat.le_trans tokensToCombined combinedToPair)

theorem widthExact_run_withinPairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (rounds steps : Nat)
    (start final : WorkConfiguration)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (exactRun : workRunExact? cnfWorkMachine steps start = some final)
    (roundsBound : rounds ≤ formula.variableCount)
    (stepsBound : steps ≤
      widthInductionLedger
        (BitString.size (BitString.pair input certificate)) rounds) :
    steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps start = some final := by
  have roundsToPair := Nat.le_trans roundsBound
    (decoded_formulaVariableCount_le_pair_size input certificate formula
      assignment formulaDecoded assignmentDecoded)
  exact widthExact_run_within_singlePhase
    (BitString.size (BitString.pair input certificate)) rounds steps
    start final exactRun roundsToPair stepsBound

namespace ClauseLiteralDesign

set_option maxRecDepth 100000

def restoreAssignmentSymbol : WorkSymbol → WorkSymbol
  | ⟨.blank, .blank⟩ => cnfBlank
  | ⟨.blank, .zero⟩ => cnfF
  | ⟨.blank, .one⟩ => cnfT
  | ⟨.zero, .blank⟩ => cnfRootGuard
  | ⟨.zero, .zero⟩ => cnfF
  | ⟨.zero, .one⟩ => cnfSep
  | ⟨.one, .blank⟩ => cnfBoundaryGuard
  | ⟨.one, .zero⟩ => cnfFinish
  | ⟨.one, .one⟩ => cnfT

theorem restoreAssignmentSymbol_markedValue (value : Bool) :
    restoreAssignmentSymbol
        (FrameTraceDesign.markedAssignmentValueWorkSymbol value) =
      FrameTraceDesign.assignmentValueWorkSymbol value := by
  cases value <;> rfl

theorem restoreAssignmentSymbol_markedAssignment (assignment : BitString) :
    List.map restoreAssignmentSymbol
        (markedAssignmentWorkSymbols assignment) =
      assignmentWorkSymbols assignment := by
  induction assignment with
  | nil => rfl
  | cons value rest ih =>
      rw [FrameTraceDesign.markedAssignmentWorkSymbols_cons]
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      change restoreAssignmentSymbol
          (FrameTraceDesign.markedAssignmentValueWorkSymbol value) ::
            List.map restoreAssignmentSymbol
              (markedAssignmentWorkSymbols rest) =
        FrameTraceDesign.assignmentValueWorkSymbol value ::
          assignmentWorkSymbols rest
      rw [restoreAssignmentSymbol_markedValue, ih]

theorem literalRestoreAssignment_marked_step (result positive : Bool)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (head :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment result positive)
        leftTail (restoreAssignmentSymbol head :: right)) := by
  cases result <;> cases positive <;> cases allowed <;> rfl

theorem literalRestoreAssignment_stack_allowed (assignment : BitString)
    (found : WorkSymbol)
    (member : List.Mem found
      (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])) :
    AssignmentMarkSymbol found := by
  apply FrameTraceDesign.pushWorkLeft_members_allowed AssignmentMarkSymbol
    (markedAssignmentWorkSymbols assignment) []
      (markedAssignmentWorkSymbols_allowed assignment)
  · intro symbol impossible
    contradiction
  · exact member

theorem literalRestoreAssignment_scan (result positive : Bool)
    (assignment : BitString) (leftSuffix right : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (pushWorkLeft (markedAssignmentWorkSymbols assignment) leftSuffix)
          right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment result positive)
        leftSuffix (assignmentWorkSymbols assignment ++ right)) := by
  have scanned := FrameTraceDesign.workRunExact?_scanLeft_write
    cnfWorkMachine
    (CNFWorkState.literalRestoreAssignment result positive)
    restoreAssignmentSymbol AssignmentMarkSymbol
    (literalRestoreAssignment_marked_step result positive)
    (pushWorkLeft (markedAssignmentWorkSymbols assignment) [])
    leftSuffix right (literalRestoreAssignment_stack_allowed assignment)
  rw [FrameTraceDesign.pushWorkLeft_length] at scanned
  rw [markedAssignmentWorkSymbols_length assignment] at scanned
  rw [FrameTraceDesign.pushWorkLeft_split_far]
  rw [FrameTraceDesign.map_pushWorkLeft] at scanned
  rw [restoreAssignmentSymbol_markedAssignment] at scanned
  change workRunExact? cnfWorkMachine assignment.length
      (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment result positive)
        (pushWorkLeft (markedAssignmentWorkSymbols assignment) [] ++
          leftSuffix) right) =
    some (workConfigAtLeftWord
      (CNFWorkState.literalRestoreAssignment result positive)
      leftSuffix
      (pushWorkLeft (pushWorkLeft (assignmentWorkSymbols assignment) [])
        right)) at scanned
  rw [pushWorkLeft_cancel] at scanned
  exact scanned

theorem literalRestoreAssignment_finish_step (result positive : Bool)
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (cnfFinish :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreCertificateCounter result positive)
        leftTail (cnfFinish :: right)) := by
  cases result <;> cases positive <;> rfl

theorem literalRestoreCounter_markFalse_step (result positive : Bool)
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreCertificateCounter result positive)
          (cnfMarkFalse :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreCertificateCounter result positive)
        leftTail (cnfMarkFalse :: right)) := by
  cases result <;> cases positive <;> rfl

theorem literalRestoreCounter_scan (result positive : Bool)
    (counter leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine counter.length
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreCertificateCounter result positive)
          (pushWorkLeft counter leftSuffix) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreCertificateCounter result positive)
        leftSuffix (counter ++ right)) := by
  apply FrameTraceDesign.workRunExact?_scanLeft_cancel cnfWorkMachine
    (CNFWorkState.literalRestoreCertificateCounter result positive)
    (fun symbol => symbol = cnfMarkFalse) _ counter leftSuffix right allowed
  intro head leftTail stepRight equal
  cases equal
  exact literalRestoreCounter_markFalse_step result positive leftTail stepRight

theorem literalRestoreCounter_boundary_step (result positive : Bool)
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreCertificateCounter result positive)
          (cnfBoundaryGuard :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreSeekSign result positive)
        leftTail (cnfBoundaryGuard :: right)) := by
  cases result <;> cases positive <;> rfl

inductive RestoreSignScanSymbol : WorkSymbol → Prop where
  | markTrue : RestoreSignScanSymbol cnfMarkTrue
  | f : RestoreSignScanSymbol cnfF
  | t : RestoreSignScanSymbol cnfT
  | sep : RestoreSignScanSymbol cnfSep
  | finish : RestoreSignScanSymbol cnfFinish

theorem literalRestoreSign_keep_step (result positive : Bool)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (allowed : RestoreSignScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreSeekSign result positive)
          (head :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreSeekSign result positive)
        leftTail (head :: right)) := by
  cases result <;> cases positive <;> cases allowed <;> rfl

theorem literalRestoreSign_scan (result positive : Bool)
    (word leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      RestoreSignScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreSeekSign result positive)
          (pushWorkLeft word leftSuffix) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreSeekSign result positive)
        leftSuffix (word ++ right)) :=
  FrameTraceDesign.workRunExact?_scanLeft_cancel cnfWorkMachine
    (CNFWorkState.literalRestoreSeekSign result positive)
    RestoreSignScanSymbol (literalRestoreSign_keep_step result positive)
    word leftSuffix right allowed

theorem literalRestoreSign_boundary_step (result positive : Bool)
    (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreSeekSign result positive)
          (cnfBoundaryGuard :: leftTail) right) =
      some (workConfigAtWord
        (CNFWorkState.literalRestoreIndex result positive)
        ((if positive then cnfT else cnfF) :: leftTail) right) := by
  cases result <;> cases positive <;> rfl

def restoreIndexSymbol : WorkSymbol → WorkSymbol
  | ⟨.blank, .blank⟩ => cnfBlank
  | ⟨.blank, .zero⟩ => cnfMarkFalse
  | ⟨.blank, .one⟩ => cnfT
  | ⟨.zero, .blank⟩ => cnfRootGuard
  | ⟨.zero, .zero⟩ => cnfF
  | ⟨.zero, .one⟩ => cnfSep
  | ⟨.one, .blank⟩ => cnfBoundaryGuard
  | ⟨.one, .zero⟩ => cnfFinish
  | ⟨.one, .one⟩ => cnfT

theorem map_restoreIndex_replicate (count : Nat) :
    List.map restoreIndexSymbol (List.replicate count cnfMarkTrue) =
      List.replicate count cnfT := by
  induction count with
  | zero => rfl
  | succ count ih => exact congrArg (List.cons cnfT) ih

theorem workRunExact?_scanRight_write (machine : WorkMachine) (state : Nat)
    (transform : WorkSymbol → WorkSymbol) (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine
          (workConfigAtWord state leftSide (head :: suffix)) =
        some (workConfigAtWord state
          (transform head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, List.Mem symbol word → Allowed symbol) :
    workRunExact? machine word.length
        (workConfigAtWord state leftSide (word ++ suffix)) =
      some (workConfigAtWord state
        (pushWorkLeft (List.map transform word) leftSide) suffix) := by
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
      exact ih (transform head :: leftSide) hRest

theorem literalRestoreIndex_marked_step (result positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalRestoreIndex result positive)
          left (cnfMarkTrue :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalRestoreIndex result positive)
        (cnfT :: left) suffix) := by
  cases result <;> cases positive <;> rfl

theorem literalRestoreIndex_t_step (result positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalRestoreIndex result positive)
          left (cnfT :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalRestoreIndex result positive)
        (cnfT :: left) suffix) := by
  cases result <;> cases positive <;> rfl

theorem literalRestoreIndex_f_step (result positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalRestoreIndex result positive)
          left (cnfF :: suffix)) =
      some (workConfigAtWord (CNFWorkState.clauseContinue result)
        (cnfF :: left) suffix) := by
  cases result <;> cases positive <;> rfl

theorem literalRestoreIndex_marked_scan (result positive : Bool)
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine count
        (workConfigAtWord
          (CNFWorkState.literalRestoreIndex result positive)
          left (List.replicate count cnfMarkTrue ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalRestoreIndex result positive)
        (pushWorkLeft (List.replicate count cnfT) left) suffix) := by
  have scanned := workRunExact?_scanRight_write cnfWorkMachine
    (CNFWorkState.literalRestoreIndex result positive)
    restoreIndexSymbol (fun symbol => symbol = cnfMarkTrue)
    (fun stepLeft head stepSuffix equal => by
      cases equal
      exact literalRestoreIndex_marked_step result positive
        stepLeft stepSuffix)
    (List.replicate count cnfMarkTrue) suffix left
    (FrameTraceDesign.mem_replicate_workSymbol_eq count cnfMarkTrue)
  rw [FrameTraceDesign.length_replicate_workSymbol] at scanned
  rw [map_restoreIndex_replicate] at scanned
  exact scanned

theorem literalRestoreIndex_t_scan (result positive : Bool)
    (count : Nat) (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine count
        (workConfigAtWord
          (CNFWorkState.literalRestoreIndex result positive)
          left (List.replicate count cnfT ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalRestoreIndex result positive)
        (pushWorkLeft (List.replicate count cnfT) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalRestoreIndex result positive)
    (fun symbol => symbol = cnfT)
    (fun stepLeft head stepSuffix equal => by
      cases equal
      exact literalRestoreIndex_t_step result positive stepLeft stepSuffix)
    (List.replicate count cnfT) suffix left
    (FrameTraceDesign.mem_replicate_workSymbol_eq count cnfT)
  rw [FrameTraceDesign.length_replicate_workSymbol] at scanned
  exact scanned

def literalRestoreSteps (assignmentLength counterLength formulaSuffixLength
    markedIndexLength rawIndexTailLength : Nat) : Nat :=
  (((((((((((assignmentLength + 1) + counterLength) + 1) +
    formulaSuffixLength) + 1) + rawIndexTailLength) +
    markedIndexLength) + 1) + markedIndexLength) +
    rawIndexTailLength) + 1)

theorem formulaScan_restoreSign (symbol : WorkSymbol)
    (allowed : FormulaScanSymbol symbol) : RestoreSignScanSymbol symbol := by
  cases allowed with
  | markTrue => exact .markTrue
  | f => exact .f
  | t => exact .t
  | sep => exact .sep
  | finish => exact .finish

def literalRestoreLeft (assignment : BitString)
    (counter formulaSuffix leftBase : List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat) : List WorkSymbol :=
  let markedLeft := pushWorkLeft
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let rawLeft := pushWorkLeft
    (List.replicate rawIndexTailLength cnfT) markedLeft
  let suffixLeft := pushWorkLeft formulaSuffix (cnfF :: rawLeft)
  let counterLeft := pushWorkLeft counter
    (cnfBoundaryGuard :: suffixLeft)
  pushWorkLeft (markedAssignmentWorkSymbols assignment)
    (cnfFinish :: counterLeft)

theorem literalRestore_exact (result positive : Bool)
    (assignment : BitString) (counter formulaSuffix leftBase right :
      List WorkSymbol)
    (markedIndexLength rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalRestoreSteps assignment.length counter.length
          formulaSuffix.length markedIndexLength rawIndexTailLength)
        (workConfigAtLeftWord
          (CNFWorkState.literalRestoreAssignment result positive)
          (literalRestoreLeft assignment counter formulaSuffix leftBase
            markedIndexLength rawIndexTailLength)
          right) =
      some (workConfigAtWord (CNFWorkState.clauseContinue result)
        (cnfF ::
          pushWorkLeft (List.replicate rawIndexTailLength cnfT)
            (pushWorkLeft (List.replicate markedIndexLength cnfT)
              ((if positive then cnfT else cnfF) :: leftBase)))
        (formulaSuffix ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++ right)))))) := by
  unfold literalRestoreSteps literalRestoreLeft
  let formulaLeft :=
    pushWorkLeft formulaSuffix
      (cnfF ::
        pushWorkLeft (List.replicate rawIndexTailLength cnfT)
          (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase)))
  let assignmentTail := assignmentWorkSymbols assignment ++ right
  let counterTail := cnfFinish :: assignmentTail
  let formulaTail := cnfBoundaryGuard :: (counter ++ counterTail)
  let restoredFormulaTail := formulaSuffix ++ formulaTail
  let indexFinishTail := cnfF :: restoredFormulaTail
  let rawIndexTail :=
    List.replicate rawIndexTailLength cnfT ++ indexFinishTail
  let markedIndexTail :=
    List.replicate markedIndexLength cnfMarkTrue ++ rawIndexTail
  have hAssignment := literalRestoreAssignment_scan result positive
    assignment (cnfFinish :: pushWorkLeft counter
      (cnfBoundaryGuard :: formulaLeft)) right
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreAssignment_finish_step result positive
      (pushWorkLeft counter (cnfBoundaryGuard :: formulaLeft))
      assignmentTail)
  have hCounter := literalRestoreCounter_scan result positive counter
    (cnfBoundaryGuard :: formulaLeft)
    counterTail counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreCounter_boundary_step result positive formulaLeft
      (counter ++ counterTail))
  have suffixAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    exact formulaScan_restoreSign symbol (formulaAllowed symbol member)
  have hFormulaSuffix := literalRestoreSign_scan result positive
    formulaSuffix
    (cnfF ::
      pushWorkLeft (List.replicate rawIndexTailLength cnfT)
        (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase)))
    formulaTail
    suffixAllowed
  have hFormulaFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreSign_keep_step result positive cnfF
      (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
        (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase)))
      restoredFormulaTail
      RestoreSignScanSymbol.f)
  have rawAllowed : ∀ symbol,
      List.Mem symbol (List.replicate rawIndexTailLength cnfT) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := FrameTraceDesign.mem_replicate_workSymbol_eq
      rawIndexTailLength cnfT symbol member
    cases equal
    exact .t
  have hRawTail := literalRestoreSign_scan result positive
    (List.replicate rawIndexTailLength cnfT)
    (pushWorkLeft (List.replicate markedIndexLength cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    indexFinishTail
    rawAllowed
  rw [FrameTraceDesign.length_replicate_workSymbol] at hRawTail
  have markedAllowed : ∀ symbol,
      List.Mem symbol (List.replicate markedIndexLength cnfMarkTrue) →
        RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := FrameTraceDesign.mem_replicate_workSymbol_eq
      markedIndexLength cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hMarked := literalRestoreSign_scan result positive
    (List.replicate markedIndexLength cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
    rawIndexTail
    markedAllowed
  rw [FrameTraceDesign.length_replicate_workSymbol] at hMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreSign_boundary_step result positive leftBase
      markedIndexTail)
  have hRestoreMarked := literalRestoreIndex_marked_scan result positive
    markedIndexLength
    ((if positive then cnfT else cnfF) :: leftBase)
    rawIndexTail
  have hKeepRaw := literalRestoreIndex_t_scan result positive
    rawIndexTailLength
    (pushWorkLeft (List.replicate markedIndexLength cnfT)
      ((if positive then cnfT else cnfF) :: leftBase))
    indexFinishTail
  have hIndexFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalRestoreIndex_f_step result positive
      (pushWorkLeft (List.replicate rawIndexTailLength cnfT)
        (pushWorkLeft (List.replicate markedIndexLength cnfT)
          ((if positive then cnfT else cnfF) :: leftBase)))
      restoredFormulaTail)
  have h1 := workRunExact?_compose cnfWorkMachine assignment.length 1
    _ _ _ hAssignment hAssignmentFinish
  have h2 := workRunExact?_compose cnfWorkMachine
    (assignment.length + 1) counter.length _ _ _ h1 hCounter
  have h3 := workRunExact?_compose cnfWorkMachine
    ((assignment.length + 1) + counter.length) 1 _ _ _ h2 hCounterBoundary
  have h4 := workRunExact?_compose cnfWorkMachine
    (((assignment.length + 1) + counter.length) + 1)
    formulaSuffix.length _ _ _ h3 hFormulaSuffix
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) 1 _ _ _ h4 hFormulaFinish
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) rawIndexTailLength _ _ _ h5 hRawTail
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength)
    markedIndexLength _ _ _ h6 hMarked
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) 1 _ _ _ h7 hSign
  have h9 := workRunExact?_compose cnfWorkMachine
    ((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) markedIndexLength _ _ _ h8 hRestoreMarked
  have h10 := workRunExact?_compose cnfWorkMachine
    (((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) + markedIndexLength)
    rawIndexTailLength _ _ _ h9 hKeepRaw
  exact workRunExact?_compose cnfWorkMachine
    ((((((((((assignment.length + 1) + counter.length) + 1) +
      formulaSuffix.length) + 1) + rawIndexTailLength) +
      markedIndexLength) + 1) + markedIndexLength) +
      rawIndexTailLength) 1 _ _ _ h10 hIndexFinish

theorem literalIndex_f_lookup_step (alreadySatisfied positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          left (cnfF :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
        (cnfF :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalLookupBoundary_keep_step (alreadySatisfied positive : Bool)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol) (allowed : FormulaScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
          left (head :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
        (head :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

theorem literalLookupBoundary_scan (alreadySatisfied positive : Bool)
    (word suffix left : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word → FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord
          (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
          left (word ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
        (pushWorkLeft word left) suffix) :=
  workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
    FormulaScanSymbol
    (literalLookupBoundary_keep_step alreadySatisfied positive)
    word suffix left allowed

theorem literalLookupBoundary_guard_step (alreadySatisfied positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupToBoundary alreadySatisfied positive)
          left (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupPastCertificateCounter
          alreadySatisfied positive)
        (cnfBoundaryGuard :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalLookupCounter_markFalse_step
    (alreadySatisfied positive : Bool) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupPastCertificateCounter
            alreadySatisfied positive)
          left (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupPastCertificateCounter
          alreadySatisfied positive)
        (cnfMarkFalse :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalLookupCounter_scan (alreadySatisfied positive : Bool)
    (counter suffix left : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine counter.length
        (workConfigAtWord
          (CNFWorkState.literalLookupPastCertificateCounter
            alreadySatisfied positive)
          left (counter ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupPastCertificateCounter
          alreadySatisfied positive)
        (pushWorkLeft counter left) suffix) := by
  apply workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalLookupPastCertificateCounter
      alreadySatisfied positive)
    (fun symbol => symbol = cnfMarkFalse) _ counter suffix left allowed
  intro stepLeft head stepSuffix equal
  cases equal
  exact literalLookupCounter_markFalse_step alreadySatisfied positive
    stepLeft stepSuffix

theorem literalLookupCounter_finish_step
    (alreadySatisfied positive : Bool) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupPastCertificateCounter
            alreadySatisfied positive)
          left (cnfFinish :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
        (cnfFinish :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalLookupAssignment_marked_step
    (alreadySatisfied positive : Bool) (left : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
          left (head :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
        (head :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

theorem literalLookupAssignment_marked_scan
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (suffix left : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtWord
          (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
          left (markedAssignmentWorkSymbols assignment ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
        (pushWorkLeft (markedAssignmentWorkSymbols assignment) left)
        suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
    AssignmentMarkSymbol
    (literalLookupAssignment_marked_step alreadySatisfied positive)
    (markedAssignmentWorkSymbols assignment) suffix left
    (markedAssignmentWorkSymbols_allowed assignment)
  rw [markedAssignmentWorkSymbols_length assignment] at scanned
  exact scanned

theorem literalLookupAssignment_value_step
    (alreadySatisfied positive value : Bool)
    (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
          left
          (FrameTraceDesign.assignmentValueWorkSymbol value :: right)) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment
          (alreadySatisfied || boolEqual value positive) positive)
        left
        (FrameTraceDesign.assignmentValueWorkSymbol value :: right)) := by
  cases alreadySatisfied <;> cases positive <;> cases value <;> rfl

def literalLookupSteps (assignmentPrefixLength counterLength
    formulaSuffixLength : Nat) : Nat :=
  ((((((1 + formulaSuffixLength) + 1) + counterLength) + 1) +
    assignmentPrefixLength) + 1) +
      literalRestoreSteps assignmentPrefixLength counterLength
        formulaSuffixLength assignmentPrefixLength 0

theorem literalLookup_inRange_exact
    (alreadySatisfied positive value : Bool)
    (assignmentPrefix assignmentSuffix : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalLookupSteps assignmentPrefix.length counter.length
          formulaSuffix.length)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfF ::
            formulaSuffix ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols assignmentPrefix ++
                      (FrameTraceDesign.assignmentValueWorkSymbol value ::
                        (assignmentWorkSymbols assignmentSuffix ++ right)))))))) =
      some (workConfigAtWord
        (CNFWorkState.clauseContinue
          (alreadySatisfied || boolEqual value positive))
        (cnfF ::
          pushWorkLeft (List.replicate assignmentPrefix.length cnfT)
            ((if positive then cnfT else cnfF) :: leftBase))
        (formulaSuffix ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignmentPrefix ++
                  (FrameTraceDesign.assignmentValueWorkSymbol value ::
                    (assignmentWorkSymbols assignmentSuffix ++ right)))))))) := by
  unfold literalLookupSteps
  let signLeft :=
    pushWorkLeft (List.replicate assignmentPrefix.length cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase)
  let assignmentRight :=
    FrameTraceDesign.assignmentValueWorkSymbol value ::
      (assignmentWorkSymbols assignmentSuffix ++ right)
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++ assignmentRight
  let certificateTail :=
    cnfBoundaryGuard ::
      (counter ++ (cnfFinish :: markedAssignmentTail))
  have hIndexFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_f_lookup_step alreadySatisfied positive signLeft
      (formulaSuffix ++ certificateTail))
  have hFormula := literalLookupBoundary_scan alreadySatisfied positive
    formulaSuffix certificateTail (cnfF :: signLeft) formulaAllowed
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupBoundary_guard_step alreadySatisfied positive
      (pushWorkLeft formulaSuffix (cnfF :: signLeft))
      (counter ++ cnfFinish :: markedAssignmentTail))
  have hCounter := literalLookupCounter_scan alreadySatisfied positive
    counter (cnfFinish :: markedAssignmentTail)
    (cnfBoundaryGuard :: pushWorkLeft formulaSuffix (cnfF :: signLeft))
    counterAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupCounter_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaSuffix (cnfF :: signLeft)))
      markedAssignmentTail)
  have hMarked := literalLookupAssignment_marked_scan
    alreadySatisfied positive assignmentPrefix assignmentRight
    (cnfFinish ::
      pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaSuffix (cnfF :: signLeft)))
  have hValue := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupAssignment_value_step alreadySatisfied positive value
      (pushWorkLeft (markedAssignmentWorkSymbols assignmentPrefix)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaSuffix (cnfF :: signLeft))))
      (assignmentWorkSymbols assignmentSuffix ++ right))
  have hRestore := literalRestore_exact
    (alreadySatisfied || boolEqual value positive) positive assignmentPrefix
    counter formulaSuffix leftBase assignmentRight
    assignmentPrefix.length 0 counterAllowed formulaAllowed
  have h1 := workRunExact?_compose cnfWorkMachine 1 formulaSuffix.length
    _ _ _ hIndexFinish hFormula
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + formulaSuffix.length) 1 _ _ _ h1 hBoundary

  have h3 := workRunExact?_compose cnfWorkMachine
    ((1 + formulaSuffix.length) + 1) counter.length _ _ _ h2 hCounter
  have h4 := workRunExact?_compose cnfWorkMachine
    (((1 + formulaSuffix.length) + 1) + counter.length) 1
    _ _ _ h3 hFinish
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((1 + formulaSuffix.length) + 1) + counter.length) + 1)
    assignmentPrefix.length _ _ _ h4 hMarked
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((1 + formulaSuffix.length) + 1) + counter.length) + 1) +
      assignmentPrefix.length) 1 _ _ _ h5 hValue
  exact workRunExact?_compose cnfWorkMachine
    ((((((1 + formulaSuffix.length) + 1) + counter.length) + 1) +
      assignmentPrefix.length) + 1)
    (literalRestoreSteps assignmentPrefix.length counter.length
      formulaSuffix.length assignmentPrefix.length 0)
    _ _ _ h6 hRestore

theorem literalLookupAssignment_root_step
    (alreadySatisfied positive : Bool) (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalLookupAssignment alreadySatisfied positive)
          left (cnfRootGuard :: right)) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment alreadySatisfied positive)
        left (cnfRootGuard :: right)) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalLookup_oob_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalLookupSteps assignment.length counter.length
          formulaSuffix.length)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfF ::
            formulaSuffix ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) =
      some (workConfigAtWord
        (CNFWorkState.clauseContinue alreadySatisfied)
        (cnfF ::
          pushWorkLeft (List.replicate assignment.length cnfT)
            ((if positive then cnfT else cnfF) :: leftBase))
        (formulaSuffix ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))))) := by
  unfold literalLookupSteps
  let signLeft := pushWorkLeft
    (List.replicate assignment.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let assignmentRight := cnfRootGuard :: right
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignment ++ assignmentRight
  let certificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have hIndexFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_f_lookup_step alreadySatisfied positive signLeft
      (formulaSuffix ++ certificateTail))
  have hFormula := literalLookupBoundary_scan alreadySatisfied positive
    formulaSuffix certificateTail (cnfF :: signLeft) formulaAllowed
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupBoundary_guard_step alreadySatisfied positive
      (pushWorkLeft formulaSuffix (cnfF :: signLeft))
      (counter ++ cnfFinish :: markedAssignmentTail))
  have hCounter := literalLookupCounter_scan alreadySatisfied positive
    counter (cnfFinish :: markedAssignmentTail)
    (cnfBoundaryGuard :: pushWorkLeft formulaSuffix (cnfF :: signLeft))
    counterAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupCounter_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaSuffix (cnfF :: signLeft)))
      markedAssignmentTail)
  have hMarked := literalLookupAssignment_marked_scan
    alreadySatisfied positive assignment assignmentRight
    (cnfFinish ::
      pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaSuffix (cnfF :: signLeft)))
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalLookupAssignment_root_step alreadySatisfied positive
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaSuffix (cnfF :: signLeft)))) right)
  have hRestore := literalRestore_exact alreadySatisfied positive assignment
    counter formulaSuffix leftBase assignmentRight assignment.length 0
    counterAllowed formulaAllowed
  have h1 := workRunExact?_compose cnfWorkMachine 1 formulaSuffix.length
    _ _ _ hIndexFinish hFormula
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + formulaSuffix.length) 1 _ _ _ h1 hBoundary
  have h3 := workRunExact?_compose cnfWorkMachine
    ((1 + formulaSuffix.length) + 1) counter.length _ _ _ h2 hCounter
  have h4 := workRunExact?_compose cnfWorkMachine
    (((1 + formulaSuffix.length) + 1) + counter.length) 1
    _ _ _ h3 hFinish
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((1 + formulaSuffix.length) + 1) + counter.length) + 1)
    assignment.length _ _ _ h4 hMarked
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((1 + formulaSuffix.length) + 1) + counter.length) + 1) +
      assignment.length) 1 _ _ _ h5 hRoot
  exact workRunExact?_compose cnfWorkMachine
    ((((((1 + formulaSuffix.length) + 1) + counter.length) + 1) +
      assignment.length) + 1)
    (literalRestoreSteps assignment.length counter.length
      formulaSuffix.length assignment.length 0)
    _ _ _ h6 hRestore

theorem literalIndex_t_mark_step (alreadySatisfied positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          left (cnfT :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndexToBoundary alreadySatisfied positive)
        (cnfMarkTrue :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalMarkAssignment_root_step
    (alreadySatisfied positive : Bool) (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
          left (cnfRootGuard :: right)) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalRestoreAssignment alreadySatisfied positive)
        left (cnfRootGuard :: right)) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem pushWorkLeft_replicate_cons (count : Nat) (symbol : WorkSymbol)
    (farSide : List WorkSymbol) :
    pushWorkLeft (List.replicate count symbol) (symbol :: farSide) =
      symbol :: pushWorkLeft (List.replicate count symbol) farSide := by
  induction count generalizing farSide with
  | zero => rfl
  | succ count ih => exact ih (symbol :: farSide)

theorem natAddRightUnitExchange (first second : Nat) :
    first + (second + 1) = (first + 1) + second := by
  induction second with
  | zero => rfl
  | succ second ih => exact congrArg Nat.succ ih

theorem pushWorkLeft_replicate_markTrue_succ (count : Nat)
    (farSide : List WorkSymbol) :
    pushWorkLeft (List.replicate (Nat.succ count) cnfMarkTrue) farSide =
      cnfMarkTrue ::
        pushWorkLeft (List.replicate count cnfMarkTrue) farSide := by
  change pushWorkLeft (List.replicate count cnfMarkTrue)
      (cnfMarkTrue :: farSide) =
    cnfMarkTrue :: pushWorkLeft (List.replicate count cnfMarkTrue) farSide
  exact pushWorkLeft_replicate_cons count cnfMarkTrue farSide

theorem oobFormulaTail_allowed (rawIndexTailLength : Nat)
    (formulaSuffix : List WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol)
    (symbol : WorkSymbol)
    (member : List.Mem symbol
      (List.replicate rawIndexTailLength cnfT ++ cnfF :: formulaSuffix)) :
    FormulaScanSymbol symbol := by
  induction rawIndexTailLength with
  | zero =>
      cases member with
      | head => exact .f
      | tail _ tailMember => exact formulaAllowed symbol tailMember
  | succ count ih =>
      cases member with
      | head => exact .t
      | tail _ tailMember => exact ih tailMember

def literalMarkOOBSteps (assignmentLength counterLength
    formulaSuffixLength rawIndexTailLength : Nat) : Nat :=
  let formulaTailLength := rawIndexTailLength + 1 + formulaSuffixLength
  ((1 + ((((formulaTailLength + 1) + counterLength) + 1) +
    assignmentLength)) + 1) +
      literalRestoreSteps assignmentLength counterLength
        formulaSuffixLength (Nat.succ assignmentLength) rawIndexTailLength

theorem literalMark_oob_rawTail_exact
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (rawIndexTailLength : Nat)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkOOBSteps assignment.length counter.length
          formulaSuffix.length rawIndexTailLength)
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft (List.replicate assignment.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (List.replicate rawIndexTailLength cnfT ++
              (cnfF ::
                (formulaSuffix ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (markedAssignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right)))))))))) =
      some (workConfigAtWord
        (CNFWorkState.clauseContinue alreadySatisfied)
        (cnfF ::
          pushWorkLeft (List.replicate rawIndexTailLength cnfT)
            (pushWorkLeft
              (List.replicate (Nat.succ assignment.length) cnfT)
              ((if positive then cnfT else cnfF) :: leftBase)))
        (formulaSuffix ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  (cnfRootGuard :: right))))))) := by
  unfold literalMarkOOBSteps
  let signLeft := pushWorkLeft
    (List.replicate assignment.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail :=
    List.replicate rawIndexTailLength cnfT ++ cnfF :: formulaSuffix
  let assignmentRight := cnfRootGuard :: right
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignment ++ assignmentRight
  let certificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    exact oobFormulaTail_allowed rawIndexTailLength formulaSuffix
      formulaAllowed symbol member
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ certificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignment)
    (cnfMarkTrue :: signLeft) right cnfRootGuard tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignment)
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_root_step alreadySatisfied positive
      (pushWorkLeft (markedAssignmentWorkSymbols assignment)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))) right)
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft := by
    exact pushWorkLeft_replicate_markTrue_succ assignment.length
      (cnfBoundaryGuard :: leftBase)
  have hFormulaShape :
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft) =
        pushWorkLeft formulaSuffix
          (cnfF ::
            pushWorkLeft (List.replicate rawIndexTailLength cnfT)
              (pushWorkLeft
                (List.replicate (Nat.succ assignment.length) cnfMarkTrue)
                (cnfBoundaryGuard :: leftBase))) := by
    unfold formulaTail
    rw [FrameTraceDesign.pushWorkLeft_append]
    rw [hMarkedShape]
    rfl
  rw [hFormulaShape] at hRoot
  have hRestore := literalRestore_exact alreadySatisfied positive assignment
    counter formulaSuffix leftBase assignmentRight
    (Nat.succ assignment.length) rawIndexTailLength
    counterAllowed formulaAllowed
  unfold literalRestoreLeft at hRestore
  have formulaTailLength : formulaTail.length =
      rawIndexTailLength + 1 + formulaSuffix.length := by
    unfold formulaTail
    rw [FrameTraceDesign.frame_length_append]
    rw [FrameTraceDesign.length_replicate_workSymbol]
    rw [List.length_cons]
    exact natAddRightUnitExchange rawIndexTailLength formulaSuffix.length
  rw [formulaTailLength] at hOut
  rw [markedAssignmentWorkSymbols_length assignment] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)
    _ _ _ hMarkIndex hOut
  rw [hFormulaShape] at h1
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)) 1 _ _ _ h1 hRoot
  unfold signLeft formulaTail certificateTail markedAssignmentTail at h2
  unfold assignmentRight at h2
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at h2
  unfold assignmentRight at hRestore
  exact workRunExact?_compose cnfWorkMachine
    ((1 + ((((rawIndexTailLength + 1 + formulaSuffix.length) + 1) +
      counter.length + 1) + assignment.length)) + 1)
    (literalRestoreSteps assignment.length counter.length
      formulaSuffix.length (Nat.succ assignment.length) rawIndexTailLength)
    _ _ _ h2 hRestore

theorem assignmentWorkSymbols_append (first second : BitString) :
    assignmentWorkSymbols (first ++ second) =
      assignmentWorkSymbols first ++ assignmentWorkSymbols second := by
  induction first with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact congrArg (List.cons _) ih

theorem markedAssignmentWorkSymbols_append (first second : BitString) :
    markedAssignmentWorkSymbols (first ++ second) =
      markedAssignmentWorkSymbols first ++
        markedAssignmentWorkSymbols second := by
  induction first with
  | nil => rfl
  | cons value rest ih =>
      cases value <;> exact congrArg (List.cons _) ih

theorem literalMarkAssignment_value_step
    (alreadySatisfied positive value : Bool)
    (left right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalMarkAssignment alreadySatisfied positive)
          left
          (FrameTraceDesign.assignmentValueWorkSymbol value :: right)) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
        left
        (FrameTraceDesign.markedAssignmentValueWorkSymbol value :: right)) := by
  cases alreadySatisfied <;> cases positive <;> cases value <;> rfl

theorem literalReturnAssignment_marked_step
    (alreadySatisfied positive : Bool) (head : WorkSymbol)
    (leftTail right : List WorkSymbol)
    (allowed : AssignmentMarkSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
          (head :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
        leftTail (head :: right)) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

theorem literalReturnAssignment_scan
    (alreadySatisfied positive : Bool) (assignment : BitString)
    (leftSuffix right : List WorkSymbol) :
    workRunExact? cnfWorkMachine assignment.length
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
          (pushWorkLeft (markedAssignmentWorkSymbols assignment) leftSuffix)
          right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
        leftSuffix (markedAssignmentWorkSymbols assignment ++ right)) := by
  have scanned := FrameTraceDesign.workRunExact?_scanLeft_cancel
    cnfWorkMachine
    (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
    AssignmentMarkSymbol
    (literalReturnAssignment_marked_step alreadySatisfied positive)
    (markedAssignmentWorkSymbols assignment) leftSuffix right
    (markedAssignmentWorkSymbols_allowed assignment)
  rw [markedAssignmentWorkSymbols_length assignment] at scanned
  exact scanned

theorem literalReturnAssignment_finish_step
    (alreadySatisfied positive : Bool) (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnAssignment alreadySatisfied positive)
          (cnfFinish :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnCertificateCounter
          alreadySatisfied positive)
        leftTail (cnfFinish :: right)) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalReturnCounter_markFalse_step
    (alreadySatisfied positive : Bool) (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnCertificateCounter
            alreadySatisfied positive)
          (cnfMarkFalse :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnCertificateCounter
          alreadySatisfied positive)
        leftTail (cnfMarkFalse :: right)) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalReturnCounter_scan
    (alreadySatisfied positive : Bool) (counter leftSuffix right :
      List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine counter.length
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnCertificateCounter
            alreadySatisfied positive)
          (pushWorkLeft counter leftSuffix) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnCertificateCounter
          alreadySatisfied positive)
        leftSuffix (counter ++ right)) := by
  apply FrameTraceDesign.workRunExact?_scanLeft_cancel cnfWorkMachine
    (CNFWorkState.literalReturnCertificateCounter
      alreadySatisfied positive)
    (fun symbol => symbol = cnfMarkFalse) _ counter leftSuffix right allowed
  intro head leftTail stepRight equal
  cases equal
  exact literalReturnCounter_markFalse_step alreadySatisfied positive
    leftTail stepRight

theorem literalReturnCounter_boundary_step
    (alreadySatisfied positive : Bool) (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnCertificateCounter
            alreadySatisfied positive)
          (cnfBoundaryGuard :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
        leftTail (cnfBoundaryGuard :: right)) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalReturnSign_keep_step
    (alreadySatisfied positive : Bool) (head : WorkSymbol)
    (leftTail right : List WorkSymbol)
    (allowed : RestoreSignScanSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
          (head :: leftTail) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
        leftTail (head :: right)) := by
  cases alreadySatisfied <;> cases positive <;> cases allowed <;> rfl

theorem literalReturnSign_scan
    (alreadySatisfied positive : Bool) (word leftSuffix right :
      List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      RestoreSignScanSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
          (pushWorkLeft word leftSuffix) right) =
      some (workConfigAtLeftWord
        (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
        leftSuffix (word ++ right)) :=
  FrameTraceDesign.workRunExact?_scanLeft_cancel cnfWorkMachine
    (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
    RestoreSignScanSymbol (literalReturnSign_keep_step alreadySatisfied positive)
    word leftSuffix right allowed

theorem literalReturnSign_boundary_step
    (alreadySatisfied positive : Bool) (leftTail right : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord
          (CNFWorkState.literalReturnSeekSign alreadySatisfied positive)
          (cnfBoundaryGuard :: leftTail) right) =
      some (workConfigAtWord
        (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
        (cnfBoundaryGuard :: leftTail) right) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalReturnIndex_marked_step
    (alreadySatisfied positive : Bool) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
          left (cnfMarkTrue :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
        (cnfMarkTrue :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem literalReturnIndex_marked_scan
    (alreadySatisfied positive : Bool) (count : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine count
        (workConfigAtWord
          (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
          left (List.replicate count cnfMarkTrue ++ suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
        (pushWorkLeft (List.replicate count cnfMarkTrue) left) suffix) := by
  have scanned := workRunExact?_scanRight cnfWorkMachine
    (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
    (fun symbol => symbol = cnfMarkTrue)
    (fun stepLeft head stepSuffix equal => by
      cases equal
      exact literalReturnIndex_marked_step alreadySatisfied positive
        stepLeft stepSuffix)
    (List.replicate count cnfMarkTrue) suffix left
    (FrameTraceDesign.mem_replicate_workSymbol_eq count cnfMarkTrue)
  rw [FrameTraceDesign.length_replicate_workSymbol] at scanned
  exact scanned

theorem literalReturnIndex_next_step
    (alreadySatisfied positive next : Bool) (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord
          (CNFWorkState.literalReturnSeekIndex alreadySatisfied positive)
          left
          (FrameTraceDesign.assignmentValueWorkSymbol next :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndex alreadySatisfied positive)
        left
        (FrameTraceDesign.assignmentValueWorkSymbol next :: suffix)) := by
  cases alreadySatisfied <;> cases positive <;> cases next <;> rfl

def literalMarkIterationSteps (assignmentPrefixLength counterLength
    formulaTailLength : Nat) : Nat :=
  let outward := (((formulaTailLength + 1) + counterLength) + 1) +
    assignmentPrefixLength
  (((((((((((1 + outward) + 1) + assignmentPrefixLength) + 1) +
    counterLength) + 1) + formulaTailLength) +
    Nat.succ assignmentPrefixLength) + 1) +
    Nat.succ assignmentPrefixLength) + 1)

theorem literalMark_inRange_iteration_exact
    (alreadySatisfied positive value next : Bool)
    (assignmentPrefix : BitString)
    (counter formulaRest leftBase assignmentRight : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length
          (Nat.succ formulaRest.length))
        (workConfigAtWord
          (CNFWorkState.literalIndex alreadySatisfied positive)
          (pushWorkLeft
            (List.replicate assignmentPrefix.length cnfMarkTrue)
            (cnfBoundaryGuard :: leftBase))
          (cnfT ::
            (FrameTraceDesign.assignmentValueWorkSymbol next ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols assignmentPrefix ++
                        (FrameTraceDesign.assignmentValueWorkSymbol value ::
                          assignmentRight))))))))) =
      some (workConfigAtWord
        (CNFWorkState.literalIndex alreadySatisfied positive)
        (pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase))
        (FrameTraceDesign.assignmentValueWorkSymbol next ::
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols assignmentPrefix ++
                    (FrameTraceDesign.markedAssignmentValueWorkSymbol value ::
                      assignmentRight)))))))) := by
  unfold literalMarkIterationSteps
  let signLeft := pushWorkLeft
    (List.replicate assignmentPrefix.length cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
  let formulaTail :=
    FrameTraceDesign.assignmentValueWorkSymbol next :: formulaRest
  let initialAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (FrameTraceDesign.assignmentValueWorkSymbol value :: assignmentRight)
  let markedAssignmentTail :=
    markedAssignmentWorkSymbols assignmentPrefix ++
      (FrameTraceDesign.markedAssignmentValueWorkSymbol value ::
        assignmentRight)
  let initialCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: initialAssignmentTail))
  let markedCertificateTail := cnfBoundaryGuard ::
    (counter ++ (cnfFinish :: markedAssignmentTail))
  have tailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol := by
    intro symbol member
    unfold formulaTail at member
    cases next with
    | false =>
        cases member with
        | head => exact .f
        | tail _ tailMember => exact formulaAllowed symbol tailMember
    | true =>
        cases member with
        | head => exact .t
        | tail _ tailMember => exact formulaAllowed symbol tailMember
  have returnTailAllowed : ∀ symbol, List.Mem symbol formulaTail →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    exact formulaScan_restoreSign symbol (tailAllowed symbol member)
  have hMarkIndex := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalIndex_t_mark_step alreadySatisfied positive signLeft
      (formulaTail ++ initialCertificateTail))
  have hOut := literalIndexToAssignmentPrefix_run alreadySatisfied positive
    formulaTail counter (markedAssignmentWorkSymbols assignmentPrefix)
    (cnfMarkTrue :: signLeft) assignmentRight
    (FrameTraceDesign.assignmentValueWorkSymbol value)
    tailAllowed counterAllowed
    (markedAssignmentWorkSymbols_allowed assignmentPrefix)
  have hValue := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalMarkAssignment_value_step alreadySatisfied positive value
      (pushWorkLeft (markedAssignmentWorkSymbols assignmentPrefix)
        (cnfFinish ::
          pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))))
      assignmentRight)
  have hBackAssignment := literalReturnAssignment_scan
    alreadySatisfied positive assignmentPrefix
    (cnfFinish ::
      pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
    (FrameTraceDesign.markedAssignmentValueWorkSymbol value ::
      assignmentRight)
  have hAssignmentFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnAssignment_finish_step alreadySatisfied positive
      (pushWorkLeft counter
        (cnfBoundaryGuard ::
          pushWorkLeft formulaTail (cnfMarkTrue :: signLeft)))
      markedAssignmentTail)
  have hBackCounter := literalReturnCounter_scan alreadySatisfied positive
    counter
    (cnfBoundaryGuard ::
      pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
    (cnfFinish :: markedAssignmentTail) counterAllowed
  have hCounterBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnCounter_boundary_step alreadySatisfied positive
      (pushWorkLeft formulaTail (cnfMarkTrue :: signLeft))
      (counter ++ cnfFinish :: markedAssignmentTail))
  have hMarkedShape :
      pushWorkLeft
          (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
          (cnfBoundaryGuard :: leftBase) =
        cnfMarkTrue :: signLeft :=
    pushWorkLeft_replicate_markTrue_succ assignmentPrefix.length
      (cnfBoundaryGuard :: leftBase)
  rw [← hMarkedShape] at hCounterBoundary
  have hBackFormula := literalReturnSign_scan alreadySatisfied positive
    formulaTail
    (pushWorkLeft
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    markedCertificateTail returnTailAllowed
  have markedAllowed : ∀ symbol,
      List.Mem symbol
        (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue) →
      RestoreSignScanSymbol symbol := by
    intro symbol member
    have equal := FrameTraceDesign.mem_replicate_workSymbol_eq
      (Nat.succ assignmentPrefix.length) cnfMarkTrue symbol member
    cases equal
    exact .markTrue
  have hBackMarked := literalReturnSign_scan alreadySatisfied positive
    (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail) markedAllowed
  rw [FrameTraceDesign.length_replicate_workSymbol] at hBackMarked
  have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnSign_boundary_step alreadySatisfied positive leftBase
      (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue ++
        formulaTail ++ markedCertificateTail))
  have hForwardMarked := literalReturnIndex_marked_scan
    alreadySatisfied positive (Nat.succ assignmentPrefix.length)
    (cnfBoundaryGuard :: leftBase)
    (formulaTail ++ markedCertificateTail)
  have hNext := workRunExact?_one_of_step cnfWorkMachine _ _
    (literalReturnIndex_next_step alreadySatisfied positive next
      (pushWorkLeft
        (List.replicate (Nat.succ assignmentPrefix.length) cnfMarkTrue)
        (cnfBoundaryGuard :: leftBase))
      (formulaRest ++ markedCertificateTail))
  have formulaTailLength : formulaTail.length = Nat.succ formulaRest.length :=
    rfl
  rw [formulaTailLength] at hOut
  rw [formulaTailLength] at hBackFormula
  rw [markedAssignmentWorkSymbols_length assignmentPrefix] at hOut
  have h1 := workRunExact?_compose cnfWorkMachine 1
    ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length) _ _ _ hMarkIndex hOut
  have h2 := workRunExact?_compose cnfWorkMachine
    (1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) 1 _ _ _ h1 hValue
  have h3 := workRunExact?_compose cnfWorkMachine
    ((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) assignmentPrefix.length
    _ _ _ h2 hBackAssignment
  have h4 := workRunExact?_compose cnfWorkMachine
    (((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) 1
    _ _ _ h3 hAssignmentFinish
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1)
    counter.length _ _ _ h4 hBackCounter
  rw [← hMarkedShape] at h5
  have h6 := workRunExact?_compose cnfWorkMachine
    (((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) 1 _ _ _ h5 hCounterBoundary
  have h7 := workRunExact?_compose cnfWorkMachine
    ((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) (Nat.succ formulaRest.length)
    _ _ _ h6 hBackFormula
  have h8 := workRunExact?_compose cnfWorkMachine
    (((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length)
    (Nat.succ assignmentPrefix.length) _ _ _ h7 hBackMarked
  rw [FrameTraceDesign.frameWork_append_assoc] at hSign
  have h9 := workRunExact?_compose cnfWorkMachine
    ((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) 1 _ _ _ h8 hSign
  have h10 := workRunExact?_compose cnfWorkMachine
    (((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) + 1)
    (Nat.succ assignmentPrefix.length) _ _ _ h9 hForwardMarked
  exact workRunExact?_compose cnfWorkMachine
    ((((((((((1 + ((((Nat.succ formulaRest.length + 1) + counter.length) + 1) +
      assignmentPrefix.length)) + 1) + assignmentPrefix.length) + 1) +
      counter.length) + 1) + Nat.succ formulaRest.length) +
      Nat.succ assignmentPrefix.length) + 1) +
      Nat.succ assignmentPrefix.length) 1 _ _ _ h10 hNext


theorem markedAssignment_append_value_tail (front : BitString)
    (value : Bool) (tail : List WorkSymbol) :
    markedAssignmentWorkSymbols (front ++ [value]) ++ tail =
      markedAssignmentWorkSymbols front ++
        (FrameTraceDesign.markedAssignmentValueWorkSymbol value :: tail) := by
  induction front with
  | nil => cases value <;> rfl
  | cons first rest ih =>
      cases first <;> exact congrArg (List.cons _) ih

theorem assignment_append_value_tail (front : BitString)
    (value : Bool) (rest : BitString) :
    front ++ value :: rest = (front ++ [value]) ++ rest := by
  induction front with
  | nil => rfl
  | cons first tail ih => exact congrArg (List.cons first) ih

theorem length_append_value (front : BitString) (value : Bool) :
    (front ++ [value]).length = Nat.succ front.length := by
  induction front with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

theorem pushWorkLeft_replicate_t_succ (count : Nat)
    (farSide : List WorkSymbol) :
    pushWorkLeft (List.replicate (Nat.succ count) cnfT) farSide =
      cnfT :: pushWorkLeft (List.replicate count cnfT) farSide := by
  change pushWorkLeft (List.replicate count cnfT) (cnfT :: farSide) =
    cnfT :: pushWorkLeft (List.replicate count cnfT) farSide
  exact pushWorkLeft_replicate_cons count cnfT farSide

theorem pushWorkLeft_replicate_t_add (first second : Nat)
    (farSide : List WorkSymbol) :
    pushWorkLeft (List.replicate second cnfT)
        (pushWorkLeft (List.replicate first cnfT) farSide) =
      pushWorkLeft (List.replicate (first + second) cnfT) farSide := by
  induction second with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ second ih =>
      rw [pushWorkLeft_replicate_t_succ]
      rw [ih]
      rw [Nat.add_succ]
      rw [pushWorkLeft_replicate_t_succ]

theorem checkLiteral_zero_cons (positive value : Bool) (rest : BitString) :
    checkLiteral
        ({ positive := positive, variableIndex := 0 } : CNFLiteral)
        (value :: rest) =
      boolEqual value positive := rfl

theorem checkLiteral_succ_cons (positive value : Bool) (index : Nat)
    (rest : BitString) :
    checkLiteral
        ({ positive := positive, variableIndex := Nat.succ index } :
          CNFLiteral)
        (value :: rest) =
      checkLiteral
        ({ positive := positive, variableIndex := index } : CNFLiteral)
        rest := rfl

theorem checkLiteral_empty (positive : Bool) (index : Nat) :
    checkLiteral
        ({ positive := positive, variableIndex := index } : CNFLiteral)
        [] = false := by
  cases index <;> rfl

def literalSemanticStart (alreadySatisfied positive : Bool)
    (assignmentPrefix : BitString) (index : Nat)
    (remainingAssignment : BitString)
    (counter formulaSuffix leftBase endTail : List WorkSymbol) :
    WorkConfiguration :=
  workConfigAtWord (CNFWorkState.literalIndex alreadySatisfied positive)
    (pushWorkLeft
      (List.replicate assignmentPrefix.length cnfMarkTrue)
      (cnfBoundaryGuard :: leftBase))
    (List.replicate index cnfT ++
      (cnfF ::
        (formulaSuffix ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (markedAssignmentWorkSymbols assignmentPrefix ++
                  (assignmentWorkSymbols remainingAssignment ++
                    endTail))))))))

def literalSemanticFinal (result positive : Bool) (fullIndex : Nat)
    (fullAssignment : BitString)
    (counter formulaSuffix leftBase endTail : List WorkSymbol) :
    WorkConfiguration :=
  workConfigAtWord (CNFWorkState.clauseContinue result)
    (cnfF ::
      pushWorkLeft (List.replicate fullIndex cnfT)
        ((if positive then cnfT else cnfF) :: leftBase))
    (formulaSuffix ++
      (cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols fullAssignment ++ endTail)))))

theorem literalMark_unary_iteration_exists
    (alreadySatisfied positive value : Bool) (assignmentPrefix : BitString)
    (index : Nat) (remainingAssignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    ∃ steps,
      workRunExact? cnfWorkMachine steps
          (literalSemanticStart alreadySatisfied positive assignmentPrefix
            (Nat.succ index) (value :: remainingAssignment)
            counter formulaSuffix leftBase (cnfRootGuard :: right)) =
        some
          (literalSemanticStart alreadySatisfied positive
            (assignmentPrefix ++ [value]) index remainingAssignment
            counter formulaSuffix leftBase (cnfRootGuard :: right)) := by
  cases index with
  | zero =>
      have h := literalMark_inRange_iteration_exact
        alreadySatisfied positive value false assignmentPrefix counter
        formulaSuffix leftBase
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)
        counterAllowed formulaAllowed
      rw [← length_append_value assignmentPrefix value] at h
      rw [← markedAssignment_append_value_tail assignmentPrefix value
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)]
        at h
      refine ⟨literalMarkIterationSteps assignmentPrefix.length counter.length
        (Nat.succ formulaSuffix.length), ?_⟩
      unfold literalSemanticStart
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      rw [List.replicate_succ]
      cases value <;> exact h
  | succ index =>
      let formulaRest :=
        List.replicate index cnfT ++ cnfF :: formulaSuffix
      have formulaRestAllowed : ∀ symbol, List.Mem symbol formulaRest →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact oobFormulaTail_allowed index formulaSuffix formulaAllowed
          symbol member
      have h := literalMark_inRange_iteration_exact
        alreadySatisfied positive value true assignmentPrefix counter
        formulaRest leftBase
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)
        counterAllowed formulaRestAllowed
      rw [← length_append_value assignmentPrefix value] at h
      rw [← markedAssignment_append_value_tail assignmentPrefix value
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)]
        at h
      refine ⟨literalMarkIterationSteps assignmentPrefix.length counter.length
        (Nat.succ formulaRest.length), ?_⟩
      unfold literalSemanticStart
      unfold formulaRest
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      rw [List.replicate_succ]
      unfold formulaRest at h
      rw [List.replicate_succ]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at h
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      cases value <;> exact h

theorem succ_add_exchange (first second : Nat) :
    Nat.succ first + second = first + Nat.succ second := by
  exact (Nat.succ_add first second).trans (Nat.add_succ first second).symm

theorem literalIndex_semantic_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment fullAssignment : BitString)
    (index fullIndex : Nat)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (fullIndexShape : fullIndex = assignmentPrefix.length + index)
    (fullAssignmentShape :
      fullAssignment = assignmentPrefix ++ remainingAssignment)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    ∃ steps,
      workRunExact? cnfWorkMachine steps
          (literalSemanticStart alreadySatisfied positive assignmentPrefix
            index remainingAssignment counter formulaSuffix leftBase
            (cnfRootGuard :: right)) =
        some
          (literalSemanticFinal
            (alreadySatisfied ||
              checkLiteral
                ({ positive := positive, variableIndex := index } :
                  CNFLiteral)
                remainingAssignment)
            positive fullIndex fullAssignment counter formulaSuffix
            leftBase (cnfRootGuard :: right)) := by
  induction index generalizing assignmentPrefix remainingAssignment with
  | zero =>
      cases remainingAssignment with
      | nil =>
          have h := literalLookup_oob_exact alreadySatisfied positive
            assignmentPrefix counter formulaSuffix leftBase right
            counterAllowed formulaAllowed
          refine ⟨literalLookupSteps assignmentPrefix.length counter.length
            formulaSuffix.length, ?_⟩
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [Nat.add_zero]
          rw [BitString.append_nil_constructive]
          rw [checkLiteral_empty]
          rw [Bool.or_false]
          exact h
      | cons value rest =>
          have h := literalLookup_inRange_exact alreadySatisfied positive
            value assignmentPrefix rest counter formulaSuffix leftBase
            (cnfRootGuard :: right) counterAllowed formulaAllowed
          refine ⟨literalLookupSteps assignmentPrefix.length counter.length
            formulaSuffix.length, ?_⟩
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [Nat.add_zero]
          rw [checkLiteral_zero_cons]
          rw [assignmentWorkSymbols_append]
          rw [FrameTraceDesign.assignmentWorkSymbols_cons]
          repeat' rw [FrameTraceDesign.frameWork_append_assoc]
          cases value <;> exact h
  | succ index ih =>
      cases remainingAssignment with
      | nil =>
          have h := literalMark_oob_rawTail_exact alreadySatisfied positive
            assignmentPrefix counter formulaSuffix leftBase right index
            counterAllowed formulaAllowed
          rw [pushWorkLeft_replicate_t_add] at h
          rw [succ_add_exchange] at h
          refine ⟨literalMarkOOBSteps assignmentPrefix.length counter.length
            formulaSuffix.length index, ?_⟩
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [BitString.append_nil_constructive]
          rw [List.replicate_succ]
          rw [checkLiteral_empty]
          rw [Bool.or_false]
          exact h
      | cons value rest =>
          rcases literalMark_unary_iteration_exists alreadySatisfied positive
            value assignmentPrefix index rest counter formulaSuffix leftBase
            right counterAllowed formulaAllowed with
            ⟨iterationSteps, iterationRun⟩
          let extendedPrefix := assignmentPrefix ++ [value]
          have extendedIndexShape :
              fullIndex = extendedPrefix.length + index := by
            unfold extendedPrefix
            rw [length_append_value]
            rw [succ_add_exchange]
            exact fullIndexShape
          have extendedAssignmentShape :
              fullAssignment = extendedPrefix ++ rest := by
            unfold extendedPrefix
            exact fullAssignmentShape.trans
              (assignment_append_value_tail assignmentPrefix value rest)
          rcases ih extendedPrefix rest extendedIndexShape
            extendedAssignmentShape with ⟨remainingSteps, remainingRun⟩
          have composed := workRunExact?_compose cnfWorkMachine
            iterationSteps remainingSteps _ _ _ iterationRun remainingRun
          refine ⟨iterationSteps + remainingSteps, ?_⟩
          rw [checkLiteral_succ_cons]
          exact composed

theorem literalIndex_full_exact
    (alreadySatisfied positive : Bool) (index : Nat)
    (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    ∃ steps,
      workRunExact? cnfWorkMachine steps
          (literalSemanticStart alreadySatisfied positive [] index assignment
            counter formulaSuffix leftBase (cnfRootGuard :: right)) =
        some
          (literalSemanticFinal
            (alreadySatisfied ||
              checkLiteral
                ({ positive := positive, variableIndex := index } :
                  CNFLiteral)
                assignment)
            positive index assignment counter formulaSuffix leftBase
            (cnfRootGuard :: right)) := by
  exact literalIndex_semantic_exact alreadySatisfied positive [] assignment
    assignment index index counter formulaSuffix leftBase right
    (Nat.zero_add index).symm rfl
    counterAllowed formulaAllowed

def literalWorkSymbols (literal : CNFLiteral) : List WorkSymbol :=
  FrameTraceDesign.assignmentValueWorkSymbol literal.positive ::
    (List.replicate literal.variableIndex cnfT ++ [cnfF])

def literalListWorkSymbols : List CNFLiteral → List WorkSymbol
  | [] => []
  | literal :: rest => literalWorkSymbols literal ++
      literalListWorkSymbols rest

theorem assignmentValueWorkSymbol_eq_if (value : Bool) :
    FrameTraceDesign.assignmentValueWorkSymbol value =
      if value then cnfT else cnfF := by
  cases value <;> rfl

theorem literalWorkSymbols_push (literal : CNFLiteral)
    (left : List WorkSymbol) :
    pushWorkLeft (literalWorkSymbols literal) left =
      cnfF ::
        pushWorkLeft (List.replicate literal.variableIndex cnfT)
          (FrameTraceDesign.assignmentValueWorkSymbol literal.positive ::
            left) := by
  unfold literalWorkSymbols
  change pushWorkLeft
      (List.replicate literal.variableIndex cnfT ++ [cnfF])
      (FrameTraceDesign.assignmentValueWorkSymbol literal.positive :: left) = _
  rw [FrameTraceDesign.pushWorkLeft_append]
  rfl

theorem literalWorkSymbols_append (literal : CNFLiteral)
    (tail : List WorkSymbol) :
    literalWorkSymbols literal ++ tail =
      FrameTraceDesign.assignmentValueWorkSymbol literal.positive ::
        (List.replicate literal.variableIndex cnfT ++ (cnfF :: tail)) := by
  unfold literalWorkSymbols
  change FrameTraceDesign.assignmentValueWorkSymbol literal.positive ::
      ((List.replicate literal.variableIndex cnfT ++ [cnfF]) ++ tail) = _
  rw [FrameTraceDesign.frameWork_append_assoc]
  rfl

theorem unaryLiteralWorkSymbols_allowed (index : Nat)
    (symbol : WorkSymbol)
    (member : List.Mem symbol
      (List.replicate index cnfT ++ [cnfF])) :
    FormulaScanSymbol symbol := by
  induction index with
  | zero =>
      cases member with
      | head => exact .f
      | tail _ impossible => contradiction
  | succ index ih =>
      cases member with
      | head => exact .t
      | tail _ tailMember => exact ih tailMember

theorem literalWorkSymbols_allowed (literal : CNFLiteral)
    (symbol : WorkSymbol) (member : List.Mem symbol
      (literalWorkSymbols literal)) : FormulaScanSymbol symbol := by
  unfold literalWorkSymbols at member
  cases member with
  | head =>
      cases literal.positive
      · exact .f
      · exact .t
  | tail _ tailMember =>
      exact unaryLiteralWorkSymbols_allowed literal.variableIndex
        symbol tailMember

theorem workSymbol_mem_append_cases (first second : List WorkSymbol)
    (symbol : WorkSymbol) (member : List.Mem symbol (first ++ second)) :
    List.Mem symbol first ∨ List.Mem symbol second := by
  induction first with
  | nil => exact Or.inr member
  | cons head rest ih =>
      cases member with
      | head => exact Or.inl (List.Mem.head rest)
      | tail _ tailMember =>
          cases ih tailMember with
          | inl restMember =>
              exact Or.inl (List.Mem.tail head restMember)
          | inr secondMember => exact Or.inr secondMember

theorem literalListWorkSymbols_allowed (literals : List CNFLiteral)
    (symbol : WorkSymbol) (member : List.Mem symbol
      (literalListWorkSymbols literals)) : FormulaScanSymbol symbol := by
  induction literals with
  | nil => contradiction
  | cons literal rest ih =>
      unfold literalListWorkSymbols at member
      have split := workSymbol_mem_append_cases
        (literalWorkSymbols literal) (literalListWorkSymbols rest)
        symbol member
      cases split with
      | inl literalMember =>
          exact literalWorkSymbols_allowed literal symbol literalMember
      | inr restMember => exact ih restMember

theorem literalListWorkSymbols_cons (literal : CNFLiteral)
    (rest : List CNFLiteral) :
    literalListWorkSymbols (literal :: rest) =
      literalWorkSymbols literal ++ literalListWorkSymbols rest := rfl

theorem clauseContinue_literal_step (alreadySatisfied positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord (CNFWorkState.clauseContinue alreadySatisfied)
          left
          (FrameTraceDesign.assignmentValueWorkSymbol positive :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndex alreadySatisfied positive)
        (cnfBoundaryGuard :: left) suffix) := by
  cases alreadySatisfied <;> cases positive <;> rfl

theorem clauseContinue_true_finish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord (CNFWorkState.clauseContinue true)
          left (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfFinish :: left) suffix) := by
  rfl

def clauseSemanticFinal (result : Bool)
    (left formulaRest : List WorkSymbol) : WorkConfiguration :=
  if result then
    workConfigAtWord CNFWorkState.clauseStart
      (cnfFinish :: left) formulaRest
  else
    workConfigAtWord CNFWorkState.reject left (cnfFinish :: formulaRest)

theorem clauseFormulaSuffix_allowed (literals : List CNFLiteral)
    (formulaRest : List WorkSymbol)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol)
    (symbol : WorkSymbol)
    (member : List.Mem symbol
      (literalListWorkSymbols literals ++ cnfFinish :: formulaRest)) :
    FormulaScanSymbol symbol := by
  have split := workSymbol_mem_append_cases
    (literalListWorkSymbols literals) (cnfFinish :: formulaRest)
    symbol member
  cases split with
  | inl literalMember =>
      exact literalListWorkSymbols_allowed literals symbol literalMember
  | inr tailMember =>
      cases tailMember with
      | head => exact .finish
      | tail _ restMember => exact formulaAllowed symbol restMember

theorem clauseContinue_semantic_exact (alreadySatisfied : Bool)
    (literals : List CNFLiteral) (assignment : BitString)
    (counter formulaRest left right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    ∃ steps,
      workRunExact? cnfWorkMachine steps
          (workConfigAtWord (CNFWorkState.clauseContinue alreadySatisfied)
            left
            (literalListWorkSymbols literals ++
              (cnfFinish ::
                (formulaRest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right))))))))) =
        some
          (clauseSemanticFinal
            (alreadySatisfied || checkClause literals assignment)
            (pushWorkLeft (literalListWorkSymbols literals) left)
            (formulaRest ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) := by
  induction literals generalizing alreadySatisfied left with
  | nil =>
      cases alreadySatisfied with
      | false =>
          let clauseTail := formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))
          have h := unsatisfiedClauseFinish_reject_run left clauseTail
          refine ⟨1, ?_⟩
          unfold literalListWorkSymbols clauseSemanticFinal checkClause
          change workRunExact? cnfWorkMachine 1
              (workConfigAtWord (CNFWorkState.clauseContinue false) left
                (cnfFinish :: clauseTail)) =
            some (workConfigAtWord CNFWorkState.reject left
              (cnfFinish :: clauseTail))
          exact h
      | true =>
          let clauseTail := formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))
          have h := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_true_finish_step left clauseTail)
          refine ⟨1, ?_⟩
          unfold literalListWorkSymbols clauseSemanticFinal checkClause
          change workRunExact? cnfWorkMachine 1
              (workConfigAtWord (CNFWorkState.clauseContinue true) left
                (cnfFinish :: clauseTail)) =
            some (workConfigAtWord CNFWorkState.clauseStart
              (cnfFinish :: left) clauseTail)
          exact h
  | cons literal rest ih =>
      let literalSuffix :=
        literalListWorkSymbols rest ++ cnfFinish :: formulaRest
      let certificateTail := cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))
      have suffixAllowed : ∀ symbol, List.Mem symbol literalSuffix →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact clauseFormulaSuffix_allowed rest formulaRest formulaAllowed
          symbol member
      have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseContinue_literal_step alreadySatisfied literal.positive left
          (List.replicate literal.variableIndex cnfT ++
            (cnfF :: (literalSuffix ++ certificateTail))))
      rcases literalIndex_full_exact alreadySatisfied literal.positive
        literal.variableIndex assignment counter literalSuffix left right
        counterAllowed suffixAllowed with ⟨literalSteps, literalRun⟩
      unfold literalSemanticStart literalSemanticFinal at literalRun
      have signLiteralRun := workRunExact?_compose cnfWorkMachine 1
        literalSteps _ _ _ hSign literalRun
      rw [← assignmentValueWorkSymbol_eq_if literal.positive]
        at signLiteralRun
      rw [← literalWorkSymbols_push literal left] at signLiteralRun
      rw [FrameTraceDesign.frameWork_append_assoc] at signLiteralRun
      rcases ih
        (alreadySatisfied || checkLiteral literal assignment)
        (pushWorkLeft (literalWorkSymbols literal) left) with
        ⟨restSteps, restRun⟩
      have complete := workRunExact?_compose cnfWorkMachine
        (1 + literalSteps) restSteps _ _ _ signLiteralRun restRun
      rw [Bool.or_assoc] at complete
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at complete
      refine ⟨(1 + literalSteps) + restSteps, ?_⟩
      unfold literalListWorkSymbols checkClause
      rw [FrameTraceDesign.pushWorkLeft_append]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      rw [literalWorkSymbols_append]
      exact complete

theorem clauseNeedLiteral_step (positive : Bool)
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.clauseNeedLiteral left
          (FrameTraceDesign.assignmentValueWorkSymbol positive :: suffix)) =
      some (workConfigAtWord
        (CNFWorkState.literalIndex false positive)
        (cnfBoundaryGuard :: left) suffix) := by
  cases positive <;> rfl

theorem clause_semantic_exact (clause : List CNFLiteral)
    (assignment : BitString)
    (counter formulaRest left right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    ∃ steps,
      workRunExact? cnfWorkMachine steps
          (workConfigAtWord CNFWorkState.clauseNeedLiteral left
            (literalListWorkSymbols clause ++
              (cnfFinish ::
                (formulaRest ++
                  (cnfBoundaryGuard ::
                    (counter ++
                      (cnfFinish ::
                        (assignmentWorkSymbols assignment ++
                          (cnfRootGuard :: right))))))))) =
        some
          (clauseSemanticFinal (checkClause clause assignment)
            (pushWorkLeft (literalListWorkSymbols clause) left)
            (formulaRest ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) := by
  cases clause with
  | nil =>
      let clauseTail := formulaRest ++
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (assignmentWorkSymbols assignment ++
                (cnfRootGuard :: right)))))
      have h := emptyClause_reject_run left clauseTail
      refine ⟨1, ?_⟩
      unfold literalListWorkSymbols clauseSemanticFinal checkClause
      change workRunExact? cnfWorkMachine 1
          (workConfigAtWord CNFWorkState.clauseNeedLiteral left
            (cnfFinish :: clauseTail)) =
        some (workConfigAtWord CNFWorkState.reject left
          (cnfFinish :: clauseTail))
      exact h
  | cons literal rest =>
      let literalSuffix :=
        literalListWorkSymbols rest ++ cnfFinish :: formulaRest
      let certificateTail := cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))
      have suffixAllowed : ∀ symbol, List.Mem symbol literalSuffix →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact clauseFormulaSuffix_allowed rest formulaRest formulaAllowed
          symbol member
      have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseNeedLiteral_step literal.positive left
          (List.replicate literal.variableIndex cnfT ++
            (cnfF :: (literalSuffix ++ certificateTail))))
      rcases literalIndex_full_exact false literal.positive
        literal.variableIndex assignment counter literalSuffix left right
        counterAllowed suffixAllowed with ⟨literalSteps, literalRun⟩
      unfold literalSemanticStart literalSemanticFinal at literalRun
      have signLiteralRun := workRunExact?_compose cnfWorkMachine 1
        literalSteps _ _ _ hSign literalRun
      rw [← assignmentValueWorkSymbol_eq_if literal.positive]
        at signLiteralRun
      rw [← literalWorkSymbols_push literal left] at signLiteralRun
      rw [FrameTraceDesign.frameWork_append_assoc] at signLiteralRun
      rw [Bool.false_or] at signLiteralRun
      rcases clauseContinue_semantic_exact
        (checkLiteral literal assignment) rest assignment counter formulaRest
        (pushWorkLeft (literalWorkSymbols literal) left) right
        counterAllowed formulaAllowed with ⟨restSteps, restRun⟩
      have complete := workRunExact?_compose cnfWorkMachine
        (1 + literalSteps) restSteps _ _ _ signLiteralRun restRun
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at complete
      refine ⟨(1 + literalSteps) + restSteps, ?_⟩
      unfold literalListWorkSymbols checkClause
      rw [FrameTraceDesign.pushWorkLeft_append]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      rw [literalWorkSymbols_append]
      exact complete

/-- Conditional accumulated ledger for the operational clause induction.
Each unary-index or clause-control unit is charged at most twelve full tape
spans; no more than one shifted span of such units fits on the raw tape. -/
theorem clauseLiteral_accumulated_le_singlePhaseBudget
    (n outerUnits unitCharge steps : Nat)
    (outerBound : outerUnits ≤ cnfShiftedWorkSpan n)
    (unitChargeBound : unitCharge ≤ cnfShiftedWorkSpan n * 12)
    (accumulated : steps ≤ outerUnits * unitCharge) :
    steps ≤ cnfSinglePhaseBudget n := by
  have productBound : outerUnits * unitCharge ≤
      cnfShiftedWorkSpan n * (cnfShiftedWorkSpan n * 12) :=
    Nat.mul_le_mul outerBound unitChargeBound
  have normalized :
      cnfShiftedWorkSpan n * (cnfShiftedWorkSpan n * 12) =
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 12 :=
    (FrameTraceDesign.natMulAssocClean (cnfShiftedWorkSpan n)
      (cnfShiftedWorkSpan n) 12).symm
  have coefficientBound : 12 ≤ 16 := by
    change 12 ≤ 12 + 4
    exact Nat.le_add_right 12 4
  have phaseBound :=
    cnfScaledQuadratic_le_singlePhaseBudget n 12 coefficientBound
  rw [normalized] at productBound
  exact Nat.le_trans accumulated (Nat.le_trans productBound phaseBound)
end ClauseLiteralDesign

namespace ClauseLiteralCostDesign

open ClauseLiteralDesign

/-! ### Deterministic clause/literal execution counts -/

set_option maxRecDepth 100000

/-- The exact interpreter count selected by the recursive literal proof. -/
def literalSemanticStepCount (counter formulaSuffix : List WorkSymbol) :
    BitString → BitString → Nat → Nat
  | assignmentPrefix, _, 0 =>
      literalLookupSteps assignmentPrefix.length counter.length
        formulaSuffix.length
  | assignmentPrefix, [], Nat.succ index =>
      literalMarkOOBSteps assignmentPrefix.length counter.length
        formulaSuffix.length index
  | assignmentPrefix, value :: rest, Nat.succ index =>
      literalMarkIterationSteps assignmentPrefix.length counter.length
          (List.replicate index cnfT ++ cnfF :: formulaSuffix).length +
        literalSemanticStepCount counter formulaSuffix
          (assignmentPrefix ++ [value]) rest index

theorem literalMark_unary_iteration_count_exact
    (alreadySatisfied positive value : Bool) (assignmentPrefix : BitString)
    (index : Nat) (remainingAssignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalMarkIterationSteps assignmentPrefix.length counter.length
          (List.replicate index cnfT ++ cnfF :: formulaSuffix).length)
        (literalSemanticStart alreadySatisfied positive assignmentPrefix
          (Nat.succ index) (value :: remainingAssignment)
          counter formulaSuffix leftBase (cnfRootGuard :: right)) =
      some
        (literalSemanticStart alreadySatisfied positive
          (assignmentPrefix ++ [value]) index remainingAssignment
          counter formulaSuffix leftBase (cnfRootGuard :: right)) := by
  cases index with
  | zero =>
      have h := literalMark_inRange_iteration_exact
        alreadySatisfied positive value false assignmentPrefix counter
        formulaSuffix leftBase
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)
        counterAllowed formulaAllowed
      rw [← length_append_value assignmentPrefix value] at h
      rw [← markedAssignment_append_value_tail assignmentPrefix value
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)]
        at h
      unfold literalSemanticStart
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      rw [List.replicate_succ]
      cases value <;> exact h
  | succ index =>
      let formulaRest :=
        List.replicate index cnfT ++ cnfF :: formulaSuffix
      have formulaRestAllowed : ∀ symbol, List.Mem symbol formulaRest →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact oobFormulaTail_allowed index formulaSuffix formulaAllowed
          symbol member
      have h := literalMark_inRange_iteration_exact
        alreadySatisfied positive value true assignmentPrefix counter
        formulaRest leftBase
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)
        counterAllowed formulaRestAllowed
      rw [← length_append_value assignmentPrefix value] at h
      rw [← markedAssignment_append_value_tail assignmentPrefix value
        (assignmentWorkSymbols remainingAssignment ++ cnfRootGuard :: right)]
        at h
      unfold literalSemanticStart
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      rw [List.replicate_succ]
      unfold formulaRest at h
      rw [List.replicate_succ]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at h
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      cases value <;> exact h

theorem literalIndex_semantic_count_exact
    (alreadySatisfied positive : Bool)
    (assignmentPrefix remainingAssignment fullAssignment : BitString)
    (index fullIndex : Nat)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (fullIndexShape : fullIndex = assignmentPrefix.length + index)
    (fullAssignmentShape :
      fullAssignment = assignmentPrefix ++ remainingAssignment)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalSemanticStepCount counter formulaSuffix assignmentPrefix
          remainingAssignment index)
        (literalSemanticStart alreadySatisfied positive assignmentPrefix
          index remainingAssignment counter formulaSuffix leftBase
          (cnfRootGuard :: right)) =
      some
        (literalSemanticFinal
          (alreadySatisfied ||
            checkLiteral
              ({ positive := positive, variableIndex := index } : CNFLiteral)
              remainingAssignment)
          positive fullIndex fullAssignment counter formulaSuffix leftBase
          (cnfRootGuard :: right)) := by
  induction index generalizing assignmentPrefix remainingAssignment with
  | zero =>
      cases remainingAssignment with
      | nil =>
          have h := literalLookup_oob_exact alreadySatisfied positive
            assignmentPrefix counter formulaSuffix leftBase right
            counterAllowed formulaAllowed
          unfold literalSemanticStepCount
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [Nat.add_zero]
          rw [BitString.append_nil_constructive]
          rw [checkLiteral_empty]
          rw [Bool.or_false]
          exact h
      | cons value rest =>
          have h := literalLookup_inRange_exact alreadySatisfied positive
            value assignmentPrefix rest counter formulaSuffix leftBase
            (cnfRootGuard :: right) counterAllowed formulaAllowed
          unfold literalSemanticStepCount
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [Nat.add_zero]
          rw [checkLiteral_zero_cons]
          rw [assignmentWorkSymbols_append]
          rw [FrameTraceDesign.assignmentWorkSymbols_cons]
          repeat' rw [FrameTraceDesign.frameWork_append_assoc]
          cases value <;> exact h
  | succ index ih =>
      cases remainingAssignment with
      | nil =>
          have h := literalMark_oob_rawTail_exact alreadySatisfied positive
            assignmentPrefix counter formulaSuffix leftBase right index
            counterAllowed formulaAllowed
          rw [pushWorkLeft_replicate_t_add] at h
          rw [succ_add_exchange] at h
          unfold literalSemanticStepCount
          unfold literalSemanticStart literalSemanticFinal
          rw [fullIndexShape]
          rw [fullAssignmentShape]
          rw [BitString.append_nil_constructive]
          rw [List.replicate_succ]
          rw [checkLiteral_empty]
          rw [Bool.or_false]
          exact h
      | cons value rest =>
          have iterationRun := literalMark_unary_iteration_count_exact
            alreadySatisfied positive value assignmentPrefix index rest
            counter formulaSuffix leftBase right counterAllowed formulaAllowed
          let extendedPrefix := assignmentPrefix ++ [value]
          have extendedIndexShape :
              fullIndex = extendedPrefix.length + index := by
            unfold extendedPrefix
            rw [length_append_value]
            rw [succ_add_exchange]
            exact fullIndexShape
          have extendedAssignmentShape :
              fullAssignment = extendedPrefix ++ rest := by
            unfold extendedPrefix
            exact fullAssignmentShape.trans
              (assignment_append_value_tail assignmentPrefix value rest)
          have remainingRun := ih extendedPrefix rest extendedIndexShape
            extendedAssignmentShape
          have complete := workRunExact?_compose cnfWorkMachine
            (literalMarkIterationSteps assignmentPrefix.length counter.length
              (List.replicate index cnfT ++ cnfF :: formulaSuffix).length)
            (literalSemanticStepCount counter formulaSuffix extendedPrefix
              rest index)
            _ _ _ iterationRun remainingRun
          unfold literalSemanticStepCount
          rw [checkLiteral_succ_cons]
          exact complete

theorem literalIndex_full_count_exact
    (alreadySatisfied positive : Bool) (index : Nat)
    (assignment : BitString)
    (counter formulaSuffix leftBase right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaSuffix →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (literalSemanticStepCount counter formulaSuffix [] assignment index)
        (literalSemanticStart alreadySatisfied positive [] index assignment
          counter formulaSuffix leftBase (cnfRootGuard :: right)) =
      some
        (literalSemanticFinal
          (alreadySatisfied ||
            checkLiteral
              ({ positive := positive, variableIndex := index } : CNFLiteral)
              assignment)
          positive index assignment counter formulaSuffix leftBase
          (cnfRootGuard :: right)) := by
  exact literalIndex_semantic_count_exact alreadySatisfied positive []
    assignment assignment index index counter formulaSuffix leftBase right
    (Nat.zero_add index).symm rfl counterAllowed formulaAllowed

/-- Exact clause-control count: one sign transition, the literal count, and
the recursively remaining clause, with one final finish transition. -/
def clauseSemanticStepCount (assignment : BitString)
    (counter formulaRest : List WorkSymbol) : List CNFLiteral → Nat
  | [] => 1
  | literal :: rest =>
      (1 + literalSemanticStepCount counter
        (literalListWorkSymbols rest ++ cnfFinish :: formulaRest)
        [] assignment literal.variableIndex) +
      clauseSemanticStepCount assignment counter formulaRest rest

theorem clauseContinue_semantic_count_exact (alreadySatisfied : Bool)
    (literals : List CNFLiteral) (assignment : BitString)
    (counter formulaRest left right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (clauseSemanticStepCount assignment counter formulaRest literals)
        (workConfigAtWord (CNFWorkState.clauseContinue alreadySatisfied)
          left
          (literalListWorkSymbols literals ++
            (cnfFinish ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (assignmentWorkSymbols assignment ++
                        (cnfRootGuard :: right))))))))) =
      some
        (clauseSemanticFinal
          (alreadySatisfied || checkClause literals assignment)
          (pushWorkLeft (literalListWorkSymbols literals) left)
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right))))))) := by
  induction literals generalizing alreadySatisfied left with
  | nil =>
      cases alreadySatisfied with
      | false =>
          let clauseTail := formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))
          have h := unsatisfiedClauseFinish_reject_run left clauseTail
          unfold clauseSemanticStepCount literalListWorkSymbols
            clauseSemanticFinal checkClause
          change workRunExact? cnfWorkMachine 1
              (workConfigAtWord (CNFWorkState.clauseContinue false) left
                (cnfFinish :: clauseTail)) =
            some (workConfigAtWord CNFWorkState.reject left
              (cnfFinish :: clauseTail))
          exact h
      | true =>
          let clauseTail := formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right)))))
          have h := workRunExact?_one_of_step cnfWorkMachine _ _
            (clauseContinue_true_finish_step left clauseTail)
          unfold clauseSemanticStepCount literalListWorkSymbols
            clauseSemanticFinal checkClause
          change workRunExact? cnfWorkMachine 1
              (workConfigAtWord (CNFWorkState.clauseContinue true) left
                (cnfFinish :: clauseTail)) =
            some (workConfigAtWord CNFWorkState.clauseStart
              (cnfFinish :: left) clauseTail)
          exact h
  | cons literal rest ih =>
      let literalSuffix :=
        literalListWorkSymbols rest ++ cnfFinish :: formulaRest
      let certificateTail := cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))
      have suffixAllowed : ∀ symbol, List.Mem symbol literalSuffix →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact clauseFormulaSuffix_allowed rest formulaRest formulaAllowed
          symbol member
      have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseContinue_literal_step alreadySatisfied literal.positive left
          (List.replicate literal.variableIndex cnfT ++
            (cnfF :: (literalSuffix ++ certificateTail))))
      have literalRun := literalIndex_full_count_exact alreadySatisfied
        literal.positive literal.variableIndex assignment counter literalSuffix
        left right counterAllowed suffixAllowed
      unfold literalSemanticStart literalSemanticFinal at literalRun
      have signLiteralRun := workRunExact?_compose cnfWorkMachine 1
        (literalSemanticStepCount counter literalSuffix [] assignment
          literal.variableIndex) _ _ _ hSign literalRun
      rw [← assignmentValueWorkSymbol_eq_if literal.positive]
        at signLiteralRun
      rw [← literalWorkSymbols_push literal left] at signLiteralRun
      rw [FrameTraceDesign.frameWork_append_assoc] at signLiteralRun
      have restRun := ih
        (alreadySatisfied || checkLiteral literal assignment)
        (pushWorkLeft (literalWorkSymbols literal) left)
      have complete := workRunExact?_compose cnfWorkMachine
        (1 + literalSemanticStepCount counter literalSuffix [] assignment
          literal.variableIndex)
        (clauseSemanticStepCount assignment counter formulaRest rest)
        _ _ _ signLiteralRun restRun
      rw [Bool.or_assoc] at complete
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at complete
      unfold literalSuffix at complete
      unfold clauseSemanticStepCount
      rw [literalListWorkSymbols_cons]
      unfold checkClause
      rw [FrameTraceDesign.pushWorkLeft_append]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      rw [literalWorkSymbols_append]
      exact complete

theorem clause_semantic_count_exact (clause : List CNFLiteral)
    (assignment : BitString)
    (counter formulaRest left right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaRest →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (clauseSemanticStepCount assignment counter formulaRest clause)
        (workConfigAtWord CNFWorkState.clauseNeedLiteral left
          (literalListWorkSymbols clause ++
            (cnfFinish ::
              (formulaRest ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (assignmentWorkSymbols assignment ++
                        (cnfRootGuard :: right))))))))) =
      some
        (clauseSemanticFinal (checkClause clause assignment)
          (pushWorkLeft (literalListWorkSymbols clause) left)
          (formulaRest ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (assignmentWorkSymbols assignment ++
                    (cnfRootGuard :: right))))))) := by
  cases clause with
  | nil =>
      let clauseTail := formulaRest ++
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (assignmentWorkSymbols assignment ++
                (cnfRootGuard :: right)))))
      have h := emptyClause_reject_run left clauseTail
      unfold clauseSemanticStepCount literalListWorkSymbols
        clauseSemanticFinal checkClause
      change workRunExact? cnfWorkMachine 1
          (workConfigAtWord CNFWorkState.clauseNeedLiteral left
            (cnfFinish :: clauseTail)) =
        some (workConfigAtWord CNFWorkState.reject left
          (cnfFinish :: clauseTail))
      exact h
  | cons literal rest =>
      let literalSuffix :=
        literalListWorkSymbols rest ++ cnfFinish :: formulaRest
      let certificateTail := cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))
      have suffixAllowed : ∀ symbol, List.Mem symbol literalSuffix →
          FormulaScanSymbol symbol := by
        intro symbol member
        exact clauseFormulaSuffix_allowed rest formulaRest formulaAllowed
          symbol member
      have hSign := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseNeedLiteral_step literal.positive left
          (List.replicate literal.variableIndex cnfT ++
            (cnfF :: (literalSuffix ++ certificateTail))))
      have literalRun := literalIndex_full_count_exact false literal.positive
        literal.variableIndex assignment counter literalSuffix left right
        counterAllowed suffixAllowed
      unfold literalSemanticStart literalSemanticFinal at literalRun
      have signLiteralRun := workRunExact?_compose cnfWorkMachine 1
        (literalSemanticStepCount counter literalSuffix [] assignment
          literal.variableIndex) _ _ _ hSign literalRun
      rw [← assignmentValueWorkSymbol_eq_if literal.positive]
        at signLiteralRun
      rw [← literalWorkSymbols_push literal left] at signLiteralRun
      rw [FrameTraceDesign.frameWork_append_assoc] at signLiteralRun
      rw [Bool.false_or] at signLiteralRun
      have restRun := clauseContinue_semantic_count_exact
        (checkLiteral literal assignment) rest assignment counter formulaRest
        (pushWorkLeft (literalWorkSymbols literal) left) right
        counterAllowed formulaAllowed
      have complete := workRunExact?_compose cnfWorkMachine
        (1 + literalSemanticStepCount counter literalSuffix [] assignment
          literal.variableIndex)
        (clauseSemanticStepCount assignment counter formulaRest rest)
        _ _ _ signLiteralRun restRun
      repeat' rw [FrameTraceDesign.frameWork_append_assoc] at complete
      unfold literalSuffix at complete
      unfold clauseSemanticStepCount
      rw [literalListWorkSymbols_cons]
      unfold checkClause
      rw [FrameTraceDesign.pushWorkLeft_append]
      repeat' rw [FrameTraceDesign.frameWork_append_assoc]
      rw [literalWorkSymbols_append]
      exact complete

/-! ### Constructive primitive charge normalization and bounds -/

private inductive ChargeCostAtom where
  | unit
  | formula
  | counter
  | marked
  | outer
  | header

private def chargeCostAtomRank : ChargeCostAtom → Nat
  | .marked => 0
  | .counter => 1
  | .header => 2
  | .formula => 3
  | .outer => 4
  | .unit => 5

private def chargeCostAtomValue
    (unit formula counter marked outer header : Nat) :
    ChargeCostAtom → Nat
  | .unit => unit
  | .formula => formula
  | .counter => counter
  | .marked => marked
  | .outer => outer
  | .header => header

private def chargeCostAtomSum
    (unit formula counter marked outer header : Nat) :
    List ChargeCostAtom → Nat
  | [] => 0
  | atom :: rest =>
      chargeCostAtomValue unit formula counter marked outer header atom +
        chargeCostAtomSum unit formula counter marked outer header rest

private def chargeCostAtomInsert
    (atom : ChargeCostAtom) : List ChargeCostAtom → List ChargeCostAtom
  | [] => [atom]
  | head :: rest =>
      if chargeCostAtomRank atom ≤ chargeCostAtomRank head then
        atom :: head :: rest
      else
        head :: chargeCostAtomInsert atom rest

private def chargeCostAtomSort :
    List ChargeCostAtom → List ChargeCostAtom
  | [] => []
  | atom :: rest => chargeCostAtomInsert atom (chargeCostAtomSort rest)

private theorem chargeCostAtomSum_insert
    (unit formula counter marked outer header : Nat)
    (atom : ChargeCostAtom) (items : List ChargeCostAtom) :
    chargeCostAtomSum unit formula counter marked outer header
        (chargeCostAtomInsert atom items) =
      chargeCostAtomValue unit formula counter marked outer header atom +
        chargeCostAtomSum unit formula counter marked outer header items := by
  induction items with
  | nil => rfl
  | cons head rest ih =>
      cases atom <;> cases head <;> try rfl
      all_goals
        change _ + chargeCostAtomSum unit formula counter marked outer header
            (chargeCostAtomInsert _ rest) = _
        rw [ih]
        exact Nat.add_left_comm _ _ _

private theorem chargeCostAtomSum_sort
    (unit formula counter marked outer header : Nat)
    (items : List ChargeCostAtom) :
    chargeCostAtomSum unit formula counter marked outer header
        (chargeCostAtomSort items) =
      chargeCostAtomSum unit formula counter marked outer header items := by
  induction items with
  | nil => rfl
  | cons atom rest ih =>
      change chargeCostAtomSum unit formula counter marked outer header
          (chargeCostAtomInsert atom (chargeCostAtomSort rest)) = _
      rw [chargeCostAtomSum_insert]
      rw [ih]
      rfl

private inductive ChargeCostExpr where
  | atom : ChargeCostAtom → ChargeCostExpr
  | add : ChargeCostExpr → ChargeCostExpr → ChargeCostExpr

private def chargeCostExprValue
    (unit formula counter marked outer header : Nat) :
    ChargeCostExpr → Nat
  | .atom atom =>
      chargeCostAtomValue unit formula counter marked outer header atom
  | .add left right =>
      chargeCostExprValue unit formula counter marked outer header left +
        chargeCostExprValue unit formula counter marked outer header right

private def chargeCostExprAtoms : ChargeCostExpr → List ChargeCostAtom
  | .atom atom => [atom]
  | .add left right => chargeCostExprAtoms left ++ chargeCostExprAtoms right

private theorem chargeCostAtomSum_append
    (unit formula counter marked outer header : Nat)
    (left right : List ChargeCostAtom) :
    chargeCostAtomSum unit formula counter marked outer header
        (left ++ right) =
      chargeCostAtomSum unit formula counter marked outer header left +
        chargeCostAtomSum unit formula counter marked outer header right := by
  induction left with
  | nil => exact (Nat.zero_add _).symm
  | cons atom rest ih =>
      change _ + chargeCostAtomSum unit formula counter marked outer header
          (rest ++ right) =
        (_ + chargeCostAtomSum unit formula counter marked outer header rest) +
          chargeCostAtomSum unit formula counter marked outer header right
      rw [ih]
      exact (Nat.add_assoc _ _ _).symm

private theorem chargeCostExprValue_atoms
    (unit formula counter marked outer header : Nat)
    (expression : ChargeCostExpr) :
    chargeCostExprValue unit formula counter marked outer header expression =
      chargeCostAtomSum unit formula counter marked outer header
        (chargeCostExprAtoms expression) := by
  induction expression with
  | atom atom => exact (Nat.add_zero _).symm
  | add left right leftIH rightIH =>
      rw [chargeCostExprAtoms, chargeCostAtomSum_append]
      change chargeCostExprValue unit formula counter marked outer header left +
          chargeCostExprValue unit formula counter marked outer header right = _
      rw [leftIH, rightIH]

private theorem chargeCostExpr_equal_of_sorted
    (unit formula counter marked outer header : Nat)
    (left right : ChargeCostExpr)
    (sorted : chargeCostAtomSort (chargeCostExprAtoms left) =
      chargeCostAtomSort (chargeCostExprAtoms right)) :
    chargeCostExprValue unit formula counter marked outer header left =
      chargeCostExprValue unit formula counter marked outer header right := by
  calc
    chargeCostExprValue unit formula counter marked outer header left =
        chargeCostAtomSum unit formula counter marked outer header
          (chargeCostExprAtoms left) :=
      chargeCostExprValue_atoms unit formula counter marked outer header left
    _ = chargeCostAtomSum unit formula counter marked outer header
          (chargeCostAtomSort (chargeCostExprAtoms left)) :=
      (chargeCostAtomSum_sort unit formula counter marked outer header
        (chargeCostExprAtoms left)).symm
    _ = chargeCostAtomSum unit formula counter marked outer header
          (chargeCostAtomSort (chargeCostExprAtoms right)) :=
      congrArg (chargeCostAtomSum unit formula counter marked outer header)
        sorted
    _ = chargeCostAtomSum unit formula counter marked outer header
          (chargeCostExprAtoms right) :=
      chargeCostAtomSum_sort unit formula counter marked outer header
        (chargeCostExprAtoms right)
    _ = chargeCostExprValue unit formula counter marked outer header right :=
      (chargeCostExprValue_atoms unit formula counter marked outer header
        right).symm

private def chargeExprAddTail :
    ChargeCostExpr → List ChargeCostExpr → ChargeCostExpr
  | expression, [] => expression
  | expression, next :: rest =>
      chargeExprAddTail (.add expression next) rest

private def chargeAtomExpr (atom : ChargeCostAtom) : ChargeCostExpr :=
  .atom atom

private def chargeExprFromAtoms
    (first : ChargeCostAtom) (rest : List ChargeCostAtom) : ChargeCostExpr :=
  chargeExprAddTail (.atom first) (rest.map ChargeCostExpr.atom)

private def literalRestoreRawExpr : ChargeCostExpr :=
  let u := chargeAtomExpr .unit
  let f := chargeAtomExpr .formula
  let c := chargeAtomExpr .counter
  let m := chargeAtomExpr .marked
  let a := chargeAtomExpr .outer
  let r := chargeAtomExpr .header
  chargeExprAddTail a [u, c, u, f, u, r, m, u, m, r, u]

private def literalRestoreTargetExpr : ChargeCostExpr :=
  chargeExprFromAtoms .outer
    [.counter, .formula, .header, .header, .marked, .marked,
      .unit, .unit, .unit, .unit, .unit]

private def literalLookupRawExpr : ChargeCostExpr :=
  let u := chargeAtomExpr .unit
  let f := chargeAtomExpr .formula
  let c := chargeAtomExpr .counter
  let a := chargeAtomExpr .outer
  let outer := chargeExprAddTail u [f, u, c, u, a, u]
  let restore := chargeExprAddTail a [u, c, u, f, u, a, u, a, u]
  .add outer restore

private def literalLookupTargetExpr : ChargeCostExpr :=
  chargeExprFromAtoms .outer
    [.outer, .outer, .outer, .counter, .counter,
      .formula, .formula,
      .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit, .unit]

private def literalMarkIterationRawExpr : ChargeCostExpr :=
  let u := chargeAtomExpr .unit
  let f := chargeAtomExpr .formula
  let c := chargeAtomExpr .counter
  let a := chargeAtomExpr .outer
  let outward := chargeExprAddTail f [u, c, u, a]
  let successor := .add a u
  chargeExprAddTail (.add u outward)
    [u, a, u, c, u, f, successor, u, successor, u]

private def literalMarkIterationTargetExpr : ChargeCostExpr :=
  chargeExprFromAtoms .outer
    [.outer, .outer, .outer, .counter, .counter,
      .formula, .formula,
      .unit, .unit, .unit, .unit, .unit,
      .unit, .unit, .unit, .unit, .unit]

private def literalMarkOOBRawExpr : ChargeCostExpr :=
  let u := chargeAtomExpr .unit
  let f := chargeAtomExpr .formula
  let c := chargeAtomExpr .counter
  let a := chargeAtomExpr .outer
  let r := chargeAtomExpr .header
  let successor := .add a u
  let formulaTail := chargeExprAddTail r [u, f]
  let outward := chargeExprAddTail formulaTail [u, c, u, a]
  let restore :=
    chargeExprAddTail a [u, c, u, f, u, r, successor, u,
      successor, r, u]
  .add (.add (.add u outward) u) restore

private def literalMarkOOBTargetExpr : ChargeCostExpr :=
  chargeExprFromAtoms .outer
    [.outer, .outer, .outer, .counter, .counter,
      .formula, .formula, .header, .header, .header,
      .unit, .unit, .unit, .unit, .unit, .unit,
      .unit, .unit, .unit, .unit, .unit, .unit]

theorem literalRestoreSteps_closed
    (assignmentLength counterLength formulaSuffixLength
      markedIndexLength rawIndexTailLength : Nat) :
    literalRestoreSteps assignmentLength counterLength formulaSuffixLength
        markedIndexLength rawIndexTailLength =
      assignmentLength + counterLength + formulaSuffixLength +
        rawIndexTailLength + rawIndexTailLength + markedIndexLength +
        markedIndexLength + 5 := by
  unfold literalRestoreSteps
  change chargeCostExprValue 1 formulaSuffixLength counterLength
      markedIndexLength assignmentLength rawIndexTailLength
      literalRestoreRawExpr =
    chargeCostExprValue 1 formulaSuffixLength counterLength
      markedIndexLength assignmentLength rawIndexTailLength
      literalRestoreTargetExpr
  apply chargeCostExpr_equal_of_sorted
  rfl

theorem literalLookupSteps_closed
    (assignmentPrefixLength counterLength formulaSuffixLength : Nat) :
    literalLookupSteps assignmentPrefixLength counterLength
        formulaSuffixLength =
      assignmentPrefixLength + assignmentPrefixLength +
        assignmentPrefixLength + assignmentPrefixLength +
        counterLength + counterLength +
        formulaSuffixLength + formulaSuffixLength + 9 := by
  unfold literalLookupSteps literalRestoreSteps
  change chargeCostExprValue 1 formulaSuffixLength counterLength
      0 assignmentPrefixLength 0 literalLookupRawExpr =
    chargeCostExprValue 1 formulaSuffixLength counterLength
      0 assignmentPrefixLength 0 literalLookupTargetExpr
  apply chargeCostExpr_equal_of_sorted
  rfl

theorem literalMarkIterationSteps_closed
    (assignmentPrefixLength counterLength formulaTailLength : Nat) :
    literalMarkIterationSteps assignmentPrefixLength counterLength
        formulaTailLength =
      assignmentPrefixLength + assignmentPrefixLength +
        assignmentPrefixLength + assignmentPrefixLength +
        counterLength + counterLength +
        formulaTailLength + formulaTailLength + 10 := by
  unfold literalMarkIterationSteps
  change chargeCostExprValue 1 formulaTailLength counterLength
      0 assignmentPrefixLength 0 literalMarkIterationRawExpr =
    chargeCostExprValue 1 formulaTailLength counterLength
      0 assignmentPrefixLength 0 literalMarkIterationTargetExpr
  apply chargeCostExpr_equal_of_sorted
  rfl

theorem literalMarkOOBSteps_closed
    (assignmentLength counterLength formulaSuffixLength
      rawIndexTailLength : Nat) :
    literalMarkOOBSteps assignmentLength counterLength formulaSuffixLength
        rawIndexTailLength =
      assignmentLength + assignmentLength + assignmentLength +
        assignmentLength + counterLength + counterLength +
        formulaSuffixLength + formulaSuffixLength +
        rawIndexTailLength + rawIndexTailLength + rawIndexTailLength + 12 := by
  unfold literalMarkOOBSteps literalRestoreSteps
  change chargeCostExprValue 1 formulaSuffixLength counterLength
      0 assignmentLength rawIndexTailLength literalMarkOOBRawExpr =
    chargeCostExprValue 1 formulaSuffixLength counterLength
      0 assignmentLength rawIndexTailLength literalMarkOOBTargetExpr
  apply chargeCostExpr_equal_of_sorted
  rfl

private theorem chargeNatAddMulClean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      rw [ih]
      exact FrameTraceDesign.frame_add_four_reorder
        (a * c) (b * c) a b

private theorem eightCopies_normalize (n : Nat) :
    (((((((n + n) + n) + n) + n) + n) + n) + n) = n * 8 := by
  repeat' rw [Nat.mul_succ]
  rw [Nat.mul_zero, Nat.zero_add]

private theorem elevenCopies_normalize (n : Nat) :
    ((((((((((n + n) + n) + n) + n) + n) + n) + n) + n) + n) + n) =
      n * 11 := by
  repeat' rw [Nat.mul_succ]
  rw [Nat.mul_zero, Nat.zero_add]

private theorem eightTerms_plus_constant_le_twelveSpan
    (n constant a b c d e f g h : Nat)
    (aBound : a ≤ n) (bBound : b ≤ n)
    (cBound : c ≤ n) (dBound : d ≤ n)
    (eBound : e ≤ n) (fBound : f ≤ n)
    (gBound : g ≤ n) (hBound : h ≤ n)
    (constantBound : constant ≤ 24) :
    (((((((a + b) + c) + d) + e) + f) + g) + h) + constant ≤
      cnfShiftedWorkSpan n * 12 := by
  have h0 := Nat.add_le_add aBound bBound
  have h1 := Nat.add_le_add h0 cBound
  have h2 := Nat.add_le_add h1 dBound
  have h3 := Nat.add_le_add h2 eBound
  have h4 := Nat.add_le_add h3 fBound
  have h5 := Nat.add_le_add h4 gBound
  have h6 := Nat.add_le_add h5 hBound
  have eightTwelve : 8 ≤ 12 := by
    change 8 ≤ 8 + 4
    exact Nat.le_add_right 8 4
  have scaled := Nat.mul_le_mul_left n eightTwelve
  have variables :
      (((((((a + b) + c) + d) + e) + f) + g) + h) ≤ n * 12 := by
    exact Nat.le_trans h6
      (Nat.le_trans (Nat.le_of_eq (eightCopies_normalize n)) scaled)
  have combined := Nat.add_le_add variables constantBound
  have normalize : n * 12 + 24 = (n + 2) * 12 := by
    exact (chargeNatAddMulClean n 2 12).symm
  unfold cnfShiftedWorkSpan
  exact Nat.le_trans combined (Nat.le_of_eq normalize)

private theorem elevenTerms_plus_constant_le_twelveSpan
    (n constant a b c d e f g h i j k : Nat)
    (aBound : a ≤ n) (bBound : b ≤ n)
    (cBound : c ≤ n) (dBound : d ≤ n)
    (eBound : e ≤ n) (fBound : f ≤ n)
    (gBound : g ≤ n) (hBound : h ≤ n)
    (iBound : i ≤ n) (jBound : j ≤ n)
    (kBound : k ≤ n)
    (constantBound : constant ≤ 24) :
    ((((((((((a + b) + c) + d) + e) + f) + g) + h) + i) + j) + k) +
        constant ≤ cnfShiftedWorkSpan n * 12 := by
  have h0 := Nat.add_le_add aBound bBound
  have h1 := Nat.add_le_add h0 cBound
  have h2 := Nat.add_le_add h1 dBound
  have h3 := Nat.add_le_add h2 eBound
  have h4 := Nat.add_le_add h3 fBound
  have h5 := Nat.add_le_add h4 gBound
  have h6 := Nat.add_le_add h5 hBound
  have h7 := Nat.add_le_add h6 iBound
  have h8 := Nat.add_le_add h7 jBound
  have h9 := Nat.add_le_add h8 kBound
  have elevenTwelve : 11 ≤ 12 := by
    change 11 ≤ 11 + 1
    exact Nat.le_add_right 11 1
  have scaled := Nat.mul_le_mul_left n elevenTwelve
  have variables :
      ((((((((((a + b) + c) + d) + e) + f) + g) + h) + i) + j) + k) ≤
        n * 12 := by
    exact Nat.le_trans h9
      (Nat.le_trans (Nat.le_of_eq (elevenCopies_normalize n)) scaled)
  have combined := Nat.add_le_add variables constantBound
  have normalize : n * 12 + 24 = (n + 2) * 12 := by
    exact (chargeNatAddMulClean n 2 12).symm
  unfold cnfShiftedWorkSpan
  exact Nat.le_trans combined (Nat.le_of_eq normalize)

theorem literalLookupSteps_le_unitCharge (n assignmentPrefixLength
    counterLength formulaSuffixLength : Nat)
    (assignmentBound : assignmentPrefixLength ≤ n)
    (counterBound : counterLength ≤ n)
    (formulaBound : formulaSuffixLength ≤ n) :
    literalLookupSteps assignmentPrefixLength counterLength
        formulaSuffixLength ≤ cnfShiftedWorkSpan n * 12 := by
  rw [literalLookupSteps_closed]
  apply eightTerms_plus_constant_le_twelveSpan n 9
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact counterBound
  · exact counterBound
  · exact formulaBound
  · exact formulaBound
  · change 9 ≤ 9 + 15
    exact Nat.le_add_right 9 15

theorem literalMarkIterationSteps_le_unitCharge (n assignmentPrefixLength
    counterLength formulaTailLength : Nat)
    (assignmentBound : assignmentPrefixLength ≤ n)
    (counterBound : counterLength ≤ n)
    (formulaBound : formulaTailLength ≤ n) :
    literalMarkIterationSteps assignmentPrefixLength counterLength
        formulaTailLength ≤ cnfShiftedWorkSpan n * 12 := by
  rw [literalMarkIterationSteps_closed]
  apply eightTerms_plus_constant_le_twelveSpan n 10
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact counterBound
  · exact counterBound
  · exact formulaBound
  · exact formulaBound
  · change 10 ≤ 10 + 14
    exact Nat.le_add_right 10 14

theorem literalMarkOOBSteps_le_unitCharge (n assignmentLength counterLength
    formulaSuffixLength rawIndexTailLength : Nat)
    (assignmentBound : assignmentLength ≤ n)
    (counterBound : counterLength ≤ n)
    (formulaBound : formulaSuffixLength ≤ n)
    (rawIndexBound : rawIndexTailLength ≤ n) :
    literalMarkOOBSteps assignmentLength counterLength formulaSuffixLength
        rawIndexTailLength ≤ cnfShiftedWorkSpan n * 12 := by
  rw [literalMarkOOBSteps_closed]
  apply elevenTerms_plus_constant_le_twelveSpan n 12
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact assignmentBound
  · exact counterBound
  · exact counterBound
  · exact formulaBound
  · exact formulaBound
  · exact rawIndexBound
  · exact rawIndexBound
  · exact rawIndexBound
  · change 12 ≤ 12 + 12
    exact Nat.le_add_right 12 12

/-! ### Literal and clause recursive runtime bounds -/

private theorem charge_plus_successor_mul (index charge : Nat) :
    charge + (index + 1) * charge = (Nat.succ index + 1) * charge := by
  change charge + Nat.succ index * charge =
    Nat.succ (Nat.succ index) * charge
  calc
    charge + Nat.succ index * charge =
        charge + (index * charge + charge) :=
      congrArg (Nat.add charge) (Nat.succ_mul index charge)
    _ = (index * charge + charge) + charge := by
      rw [← Nat.add_assoc]
      rw [Nat.add_comm charge (index * charge)]
    _ = Nat.succ index * charge + charge :=
      congrArg (fun x => x + charge) (Nat.succ_mul index charge).symm
    _ = Nat.succ (Nat.succ index) * charge :=
      (Nat.succ_mul (Nat.succ index) charge).symm

theorem literalSemanticStepCount_le_indexCharge
    (n : Nat) (counter formulaSuffix : List WorkSymbol)
    (assignmentPrefix remainingAssignment : BitString) (index : Nat)
    (assignmentBound :
      assignmentPrefix.length + remainingAssignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaBound : index + formulaSuffix.length ≤ n) :
    literalSemanticStepCount counter formulaSuffix assignmentPrefix
        remainingAssignment index ≤
      (index + 1) * (cnfShiftedWorkSpan n * 12) := by
  induction index generalizing assignmentPrefix remainingAssignment with
  | zero =>
      unfold literalSemanticStepCount
      have lookupBound := literalLookupSteps_le_unitCharge n
        assignmentPrefix.length counter.length formulaSuffix.length
        (Nat.le_trans
          (Nat.le_add_right assignmentPrefix.length
            remainingAssignment.length)
          assignmentBound)
        counterBound
        (Nat.le_trans
          (Nat.le_add_left formulaSuffix.length 0)
          formulaBound)
      exact Nat.le_trans lookupBound
        (Nat.le_of_eq (Nat.one_mul (cnfShiftedWorkSpan n * 12)).symm)
  | succ index ih =>
      cases remainingAssignment with
      | nil =>
          unfold literalSemanticStepCount
          apply Nat.le_trans
            (literalMarkOOBSteps_le_unitCharge n assignmentPrefix.length
              counter.length formulaSuffix.length index
              (Nat.le_trans
                (Nat.le_add_right assignmentPrefix.length 0)
                assignmentBound)
              counterBound
              (Nat.le_trans
                (Nat.le_add_left formulaSuffix.length (Nat.succ index))
                formulaBound)
              (Nat.le_trans (Nat.le_succ index)
                (Nat.le_of_add_right_le formulaBound)))
          exact Nat.le_mul_of_pos_left (cnfShiftedWorkSpan n * 12)
            (Nat.zero_lt_succ (Nat.succ index))
      | cons value rest =>
          have extendedAssignmentBound :
              (assignmentPrefix ++ [value]).length + rest.length ≤ n := by
            change assignmentPrefix.length + Nat.succ rest.length ≤ n at assignmentBound
            rw [Nat.add_succ] at assignmentBound
            rw [length_append_value, Nat.succ_add]
            exact assignmentBound
          have recursiveFormulaBound :
              index + formulaSuffix.length ≤ n :=
            Nat.le_trans
              (Nat.add_le_add_right (Nat.le_succ index)
                formulaSuffix.length)
              formulaBound
          have formulaTailBound :
              (List.replicate index cnfT ++ cnfF :: formulaSuffix).length ≤
                n := by
            rw [workSymbol_length_append, workSymbol_replicate_length,
              List.length_cons]
            rw [Nat.add_succ]
            rw [Nat.succ_add] at formulaBound
            exact formulaBound
          have iterationBound :=
            literalMarkIterationSteps_le_unitCharge n
              assignmentPrefix.length counter.length
              (List.replicate index cnfT ++ cnfF :: formulaSuffix).length
              (Nat.le_trans
                (Nat.le_add_right assignmentPrefix.length
                  (value :: rest).length)
                assignmentBound)
              counterBound formulaTailBound
          have recursiveBound := ih
            (assignmentPrefix ++ [value]) rest extendedAssignmentBound
            recursiveFormulaBound
          unfold literalSemanticStepCount
          exact Nat.le_trans (Nat.add_le_add iterationBound recursiveBound)
            (Nat.le_of_eq
              (charge_plus_successor_mul index
                (cnfShiftedWorkSpan n * 12)))

private theorem clauseNatAddMulClean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      rw [ih]
      exact FrameTraceDesign.frame_add_four_reorder
        (a * c) (b * c) a b

private theorem one_le_clauseUnitCharge (n : Nat) :
    1 ≤ cnfShiftedWorkSpan n * 12 := by
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
    exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))
  have twelvePositive : 0 < 12 := Nat.zero_lt_succ 11
  exact Nat.le_trans oneSpan
    (Nat.le_mul_of_pos_right (cnfShiftedWorkSpan n) twelvePositive)

private theorem clauseCharge_plus_successor_mul (index charge : Nat) :
    charge + (index + 1) * charge = (Nat.succ index + 1) * charge := by
  change charge + Nat.succ index * charge =
    Nat.succ (Nat.succ index) * charge
  calc
    charge + Nat.succ index * charge =
        charge + (index * charge + charge) :=
      congrArg (Nat.add charge) (Nat.succ_mul index charge)
    _ = (index * charge + charge) + charge := by
      rw [← Nat.add_assoc]
      rw [Nat.add_comm charge (index * charge)]
    _ = Nat.succ index * charge + charge :=
      congrArg (fun x => x + charge) (Nat.succ_mul index charge).symm
    _ = Nat.succ (Nat.succ index) * charge :=
      (Nat.succ_mul (Nat.succ index) charge).symm

theorem literalWorkSymbols_length (literal : CNFLiteral) :
    (literalWorkSymbols literal).length = literal.variableIndex + 2 := by
  unfold literalWorkSymbols
  change Nat.succ
      (List.replicate literal.variableIndex cnfT ++ [cnfF]).length =
    literal.variableIndex + 2
  rw [workSymbol_length_append, workSymbol_replicate_length]
  change Nat.succ (literal.variableIndex + 1) =
    literal.variableIndex + 2
  rfl

private theorem literalIndex_suffix_le_segment
    (index restLength formulaLength n : Nat)
    (segmentBound :
      ((index + 2) + restLength) + 1 + formulaLength ≤ n) :
    index + (restLength + Nat.succ formulaLength) ≤ n := by
  have indexToEncoded : index ≤ index + 2 :=
    Nat.le_add_right index 2
  have enlarged := Nat.add_le_add_right indexToEncoded
    (restLength + Nat.succ formulaLength)
  have normalize :
      (index + 2) + (restLength + Nat.succ formulaLength) =
        ((index + 2) + restLength) + 1 + formulaLength := by
    change (index + 2) + (restLength + (formulaLength + 1)) =
      ((index + 2) + restLength) + 1 + formulaLength
    calc
      (index + 2) + (restLength + (formulaLength + 1)) =
          ((index + 2) + restLength) + (formulaLength + 1) :=
        (Nat.add_assoc (index + 2) restLength
          (formulaLength + 1)).symm
      _ = ((index + 2) + restLength) + (1 + formulaLength) :=
        congrArg (Nat.add ((index + 2) + restLength))
          (Nat.add_comm formulaLength 1)
      _ = ((index + 2) + restLength) + 1 + formulaLength :=
        (Nat.add_assoc ((index + 2) + restLength) 1 formulaLength).symm
  exact Nat.le_trans enlarged
    (Nat.le_trans (Nat.le_of_eq normalize) segmentBound)

theorem clauseSemanticStepCount_le_encodedCharge
    (n : Nat) (assignment : BitString)
    (counter formulaRest : List WorkSymbol) (literals : List CNFLiteral)
    (assignmentBound : assignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaSegmentBound :
      (literalListWorkSymbols literals).length + 1 +
        formulaRest.length ≤ n) :
    clauseSemanticStepCount assignment counter formulaRest literals ≤
      ((literalListWorkSymbols literals).length + 1) *
        (cnfShiftedWorkSpan n * 12) := by
  induction literals with
  | nil =>
      unfold clauseSemanticStepCount literalListWorkSymbols
      exact Nat.le_trans (one_le_clauseUnitCharge n)
        (Nat.le_of_eq
          (Nat.one_mul (cnfShiftedWorkSpan n * 12)).symm)
  | cons literal rest ih =>
      have normalizedSegmentBound :
          ((literal.variableIndex + 2) +
              (literalListWorkSymbols rest).length) + 1 +
            formulaRest.length ≤ n := by
        rw [literalListWorkSymbols_cons, workSymbol_length_append,
          literalWorkSymbols_length] at formulaSegmentBound
        exact formulaSegmentBound
      have restSegmentBound :
          (literalListWorkSymbols rest).length + 1 +
            formulaRest.length ≤ n := by
        have restToWhole := Nat.le_add_left
          (literalListWorkSymbols rest).length
          (literal.variableIndex + 2)
        have withFinish := Nat.add_le_add_right restToWhole 1
        have withFormula := Nat.add_le_add_right withFinish formulaRest.length
        exact Nat.le_trans withFormula normalizedSegmentBound
      have suffixLength :
          (literalListWorkSymbols rest ++ cnfFinish :: formulaRest).length =
            (literalListWorkSymbols rest).length +
              Nat.succ formulaRest.length := by
        rw [workSymbol_length_append]
        rfl
      have literalFormulaBound :
          literal.variableIndex +
              (literalListWorkSymbols rest ++
                cnfFinish :: formulaRest).length ≤ n := by
        rw [suffixLength]
        exact literalIndex_suffix_le_segment literal.variableIndex
          (literalListWorkSymbols rest).length formulaRest.length n
          normalizedSegmentBound
      have literalBound := literalSemanticStepCount_le_indexCharge n counter
        (literalListWorkSymbols rest ++ cnfFinish :: formulaRest)
        [] assignment literal.variableIndex
        (by
          change 0 + assignment.length ≤ n
          rw [Nat.zero_add]
          exact assignmentBound)
        counterBound literalFormulaBound
      have signLiteralBound :
          1 + literalSemanticStepCount counter
              (literalListWorkSymbols rest ++ cnfFinish :: formulaRest)
              [] assignment literal.variableIndex ≤
            (literal.variableIndex + 2) *
              (cnfShiftedWorkSpan n * 12) := by
        have combined := Nat.add_le_add (one_le_clauseUnitCharge n)
          literalBound
        exact Nat.le_trans combined
          (Nat.le_of_eq
            (clauseCharge_plus_successor_mul literal.variableIndex
              (cnfShiftedWorkSpan n * 12)))
      have restBound := ih restSegmentBound
      unfold clauseSemanticStepCount
      rw [literalListWorkSymbols_cons, workSymbol_length_append,
        literalWorkSymbols_length]
      have combined := Nat.add_le_add signLiteralBound restBound
      apply Nat.le_trans combined
      have distributed := clauseNatAddMulClean
        (literal.variableIndex + 2)
        ((literalListWorkSymbols rest).length + 1)
        (cnfShiftedWorkSpan n * 12)
      have coefficient :
          (literal.variableIndex + 2) +
              ((literalListWorkSymbols rest).length + 1) =
            (literal.variableIndex + 2 +
              (literalListWorkSymbols rest).length) + 1 :=
        (Nat.add_assoc (literal.variableIndex + 2)
          (literalListWorkSymbols rest).length 1).symm
      exact Nat.le_of_eq
        (distributed.symm.trans
          (congrArg (fun count =>
            count * (cnfShiftedWorkSpan n * 12)) coefficient))

theorem clauseSemanticStepCount_le_singlePhase
    (n : Nat) (assignment : BitString)
    (counter formulaRest : List WorkSymbol) (literals : List CNFLiteral)
    (assignmentBound : assignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaSegmentBound :
      (literalListWorkSymbols literals).length + 1 +
        formulaRest.length ≤ n) :
    clauseSemanticStepCount assignment counter formulaRest literals ≤
      cnfSinglePhaseBudget n := by
  have accumulated := clauseSemanticStepCount_le_encodedCharge n assignment
    counter formulaRest literals assignmentBound counterBound
    formulaSegmentBound
  have outerToN : (literalListWorkSymbols literals).length + 1 ≤ n :=
    Nat.le_of_add_right_le formulaSegmentBound
  have nToSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have outerBound : (literalListWorkSymbols literals).length + 1 ≤
      cnfShiftedWorkSpan n := Nat.le_trans outerToN nToSpan
  exact ClauseLiteralDesign.clauseLiteral_accumulated_le_singlePhaseBudget
    n ((literalListWorkSymbols literals).length + 1)
    (cnfShiftedWorkSpan n * 12)
    (clauseSemanticStepCount assignment counter formulaRest literals)
    outerBound (Nat.le_refl (cnfShiftedWorkSpan n * 12)) accumulated

theorem decodedClauseSemanticStepCount_le_pairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (literals : List CNFLiteral)
    (formulaRest : List WorkSymbol)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (segmentWithinFormula :
      (literalListWorkSymbols literals).length + 1 +
          formulaRest.length ≤
        (encodeFormulaTokens formula).length) :
    clauseSemanticStepCount assignment
        (List.replicate assignment.length cnfMarkFalse)
        formulaRest literals ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  have combinedBound :=
    FrameTraceDesign.decoded_frame_payload_length_le_pair_size
      input certificate formula assignment formulaDecoded assignmentDecoded
  have formulaToCombined : (encodeFormulaTokens formula).length ≤
      (encodeFormulaTokens formula).length + assignment.length :=
    Nat.le_add_right (encodeFormulaTokens formula).length assignment.length
  have assignmentToCombined : assignment.length ≤
      (encodeFormulaTokens formula).length + assignment.length :=
    Nat.le_add_left assignment.length (encodeFormulaTokens formula).length
  have formulaBound := Nat.le_trans formulaToCombined combinedBound
  have assignmentBound := Nat.le_trans assignmentToCombined combinedBound
  have counterBound :
      (List.replicate assignment.length cnfMarkFalse).length ≤
        BitString.size (BitString.pair input certificate) := by
    rw [workSymbol_replicate_length]
    exact assignmentBound
  have segmentBound := Nat.le_trans segmentWithinFormula formulaBound
  exact clauseSemanticStepCount_le_singlePhase
    (BitString.size (BitString.pair input certificate)) assignment
    (List.replicate assignment.length cnfMarkFalse) formulaRest literals
    assignmentBound counterBound segmentBound

/-! ### Formula-wide canonical semantics and runtime composition -/

set_option maxRecDepth 100000

/-- Canonical clause-list work symbols, including the final formula finish. -/
def formulaClauseWorkSymbols :
    List (List CNFLiteral) → List WorkSymbol
  | [] => [cnfFinish]
  | clause :: rest =>
      cnfSep ::
        (literalListWorkSymbols clause ++
          cnfFinish :: formulaClauseWorkSymbols rest)

theorem formulaClauseWorkSymbols_cons_append
    (clause : List CNFLiteral) (rest : List (List CNFLiteral))
    (tail : List WorkSymbol) :
    formulaClauseWorkSymbols (clause :: rest) ++ tail =
      cnfSep ::
        (literalListWorkSymbols clause ++
          cnfFinish :: (formulaClauseWorkSymbols rest ++ tail)) := by
  calc
    formulaClauseWorkSymbols (clause :: rest) ++ tail =
        (cnfSep ::
          (literalListWorkSymbols clause ++
            cnfFinish :: formulaClauseWorkSymbols rest)) ++ tail := rfl
    _ = cnfSep ::
        ((literalListWorkSymbols clause ++
          cnfFinish :: formulaClauseWorkSymbols rest) ++ tail) := rfl
    _ = cnfSep ::
        (literalListWorkSymbols clause ++
          ((cnfFinish :: formulaClauseWorkSymbols rest) ++ tail)) :=
      congrArg (List.cons cnfSep)
        (FrameTraceDesign.frameWork_append_assoc
          (literalListWorkSymbols clause)
          (cnfFinish :: formulaClauseWorkSymbols rest) tail)
    _ = cnfSep ::
        (literalListWorkSymbols clause ++
          cnfFinish :: (formulaClauseWorkSymbols rest ++ tail)) := rfl

theorem formulaClauseWorkSymbols_allowed
    (clauses : List (List CNFLiteral))
    (symbol : WorkSymbol)
    (member : List.Mem symbol (formulaClauseWorkSymbols clauses)) :
    FormulaScanSymbol symbol := by
  induction clauses with
  | nil =>
      cases member with
      | head => exact .finish
      | tail _ impossible => contradiction
  | cons clause rest ih =>
      unfold formulaClauseWorkSymbols at member
      cases member with
      | head => exact .sep
      | tail _ tailMember =>
          have split := workSymbol_mem_append_cases
            (literalListWorkSymbols clause)
            (cnfFinish :: formulaClauseWorkSymbols rest)
            symbol tailMember
          cases split with
          | inl literalMember =>
              exact literalListWorkSymbols_allowed clause symbol literalMember
          | inr suffixMember =>
              cases suffixMember with
              | head => exact .finish
              | tail _ restMember => exact ih restMember

theorem cnfTokenWorkSymbols_encodeLiteralTokens
    (literal : CNFLiteral) :
    cnfTokenWorkSymbols (encodeLiteralTokens literal) =
      literalWorkSymbols literal := by
  unfold encodeLiteralTokens literalWorkSymbols
  cases literal.positive
  · change cnfF ::
        cnfTokenWorkSymbols (encodeUnaryTokens literal.variableIndex) = _
    rw [cnfTokenWorkSymbols_encodeUnaryTokens]
    unfold FrameTraceDesign.assignmentValueWorkSymbol
    rfl
  · change cnfT ::
        cnfTokenWorkSymbols (encodeUnaryTokens literal.variableIndex) = _
    rw [cnfTokenWorkSymbols_encodeUnaryTokens]
    unfold FrameTraceDesign.assignmentValueWorkSymbol
    rfl

theorem cnfTokenWorkSymbols_encodeLiteralListTokens
    (literals : List CNFLiteral) :
    cnfTokenWorkSymbols (encodeLiteralListTokens literals) =
      literalListWorkSymbols literals := by
  induction literals with
  | nil => rfl
  | cons literal rest ih =>
      unfold encodeLiteralListTokens literalListWorkSymbols
      rw [cnfTokenWorkSymbols_append]
      rw [cnfTokenWorkSymbols_encodeLiteralTokens]
      rw [ih]

theorem cnfTokenWorkSymbols_encodeClauseTokens
    (clause : List CNFLiteral) :
    cnfTokenWorkSymbols (encodeClauseTokens clause) =
      cnfSep :: (literalListWorkSymbols clause ++ [cnfFinish]) := by
  unfold encodeClauseTokens
  change cnfSep ::
      cnfTokenWorkSymbols (encodeLiteralListTokens clause ++ [.finish]) = _
  rw [cnfTokenWorkSymbols_append]
  rw [cnfTokenWorkSymbols_encodeLiteralListTokens]
  rfl

theorem cnfTokenWorkSymbols_encodeFormulaClauses
    (clauses : List (List CNFLiteral)) :
    cnfTokenWorkSymbols (encodeClauseListTokens clauses ++ [.finish]) =
      formulaClauseWorkSymbols clauses := by
  induction clauses with
  | nil => rfl
  | cons clause rest ih =>
      unfold encodeClauseListTokens
      rw [token_append_assoc_constructive]
      rw [cnfTokenWorkSymbols_append]
      rw [cnfTokenWorkSymbols_encodeClauseTokens]
      rw [ih]
      calc
        (cnfSep ::
            (literalListWorkSymbols clause ++ [cnfFinish])) ++
            formulaClauseWorkSymbols rest =
          cnfSep ::
            ((literalListWorkSymbols clause ++ [cnfFinish]) ++
              formulaClauseWorkSymbols rest) := rfl
        _ = cnfSep ::
            (literalListWorkSymbols clause ++
              ([cnfFinish] ++ formulaClauseWorkSymbols rest)) :=
          congrArg (List.cons cnfSep)
            (FrameTraceDesign.frameWork_append_assoc
              (literalListWorkSymbols clause) [cnfFinish]
              (formulaClauseWorkSymbols rest))
        _ = cnfSep ::
            (literalListWorkSymbols clause ++
              cnfFinish :: formulaClauseWorkSymbols rest) := rfl
        _ = formulaClauseWorkSymbols (clause :: rest) := rfl

theorem checkCNF_eq_checkClauses_of_width
    (formula : CNFFormula) (assignment : BitString)
    (width : assignment.length = formula.variableCount) :
    checkCNF formula assignment =
      checkClauses formula.clauses assignment := by
  have widthCheck :=
    (natEqual_eq_true_iff assignment.length formula.variableCount).mpr width
  unfold checkCNF
  rw [widthCheck]
  rfl

theorem clauseStart_separator_step (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.clauseStart left
          (cnfSep :: suffix)) =
      some (workConfigAtWord CNFWorkState.clauseNeedLiteral
        (cnfSep :: left) suffix) := by
  rfl

theorem clauseStart_formulaFinish_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.clauseStart left
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.finalCheck
        (cnfFinish :: left) suffix) := by
  rfl

theorem finalCheck_boundary_step
    (left suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.finalCheck left
          (cnfBoundaryGuard :: suffix)) =
      some (workConfigAtWord CNFWorkState.accept left
        (cnfBoundaryGuard :: suffix)) := by
  rfl

/-- The exact number of transitions taken by canonical formula evaluation.
Evaluation stops at the first false clause, as the machine does. -/
def formulaSemanticStepCount (assignment : BitString)
    (counter : List WorkSymbol) : List (List CNFLiteral) → Nat
  | [] => 2
  | clause :: rest =>
      let clauseSteps := clauseSemanticStepCount assignment counter
        (formulaClauseWorkSymbols rest) clause
      if checkClause clause assignment then
        (1 + clauseSteps) +
          formulaSemanticStepCount assignment counter rest
      else
        1 + clauseSteps

theorem formula_semantic_count_exact
    (clauses : List (List CNFLiteral)) (assignment : BitString)
    (counter left right : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    ∃ final,
      workRunExact? cnfWorkMachine
          (formulaSemanticStepCount assignment counter clauses)
          (workConfigAtWord CNFWorkState.clauseStart left
            (formulaClauseWorkSymbols clauses ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) =
        some final ∧
      final.state =
        if checkClauses clauses assignment then
          CNFWorkState.accept
        else
          CNFWorkState.reject := by
  induction clauses generalizing left with
  | nil =>
      let suffix := counter ++
        (cnfFinish ::
          (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right)))
      have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseStart_formulaFinish_step left
          (cnfBoundaryGuard :: suffix))
      have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
        (finalCheck_boundary_step (cnfFinish :: left) suffix)
      have complete := workRunExact?_compose cnfWorkMachine 1 1
        _ _ _ hFinish hBoundary
      refine ⟨workConfigAtWord CNFWorkState.accept (cnfFinish :: left)
          (cnfBoundaryGuard :: suffix), ?_, ?_⟩
      · unfold formulaSemanticStepCount formulaClauseWorkSymbols
        unfold suffix at complete
        exact complete
      · rfl
  | cons clause rest ih =>
      let certificateTail := cnfBoundaryGuard ::
        (counter ++
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++ (cnfRootGuard :: right))))
      have separatorRun := workRunExact?_one_of_step cnfWorkMachine _ _
        (clauseStart_separator_step left
          (literalListWorkSymbols clause ++
            cnfFinish ::
              (formulaClauseWorkSymbols rest ++ certificateTail)))
      have clauseRun := clause_semantic_count_exact clause assignment counter
        (formulaClauseWorkSymbols rest) (cnfSep :: left) right
        counterAllowed (formulaClauseWorkSymbols_allowed rest)
      have throughClause := workRunExact?_compose cnfWorkMachine 1
        (clauseSemanticStepCount assignment counter
          (formulaClauseWorkSymbols rest) clause)
        _ _ _ separatorRun clauseRun
      cases clauseCheck : checkClause clause assignment with
      | false =>
          refine ⟨clauseSemanticFinal false
              (pushWorkLeft (literalListWorkSymbols clause)
                (cnfSep :: left))
              (formulaClauseWorkSymbols rest ++ certificateTail), ?_, ?_⟩
          · unfold formulaSemanticStepCount
            rw [clauseCheck]
            rw [clauseCheck] at throughClause
            unfold certificateTail
            rw [formulaClauseWorkSymbols_cons_append]
            exact throughClause
          · unfold clauseSemanticFinal
            unfold checkClauses
            rw [clauseCheck]
            rfl
      | true =>
          let extendedLeft := cnfFinish ::
            pushWorkLeft (literalListWorkSymbols clause) (cnfSep :: left)
          rcases ih extendedLeft with ⟨final, remainingRun, finalState⟩
          rw [clauseCheck] at throughClause
          unfold clauseSemanticFinal at throughClause
          have complete := workRunExact?_compose cnfWorkMachine
            (1 + clauseSemanticStepCount assignment counter
              (formulaClauseWorkSymbols rest) clause)
            (formulaSemanticStepCount assignment counter rest)
            _ _ _ throughClause remainingRun
          refine ⟨final, ?_, ?_⟩
          · unfold formulaSemanticStepCount
            rw [clauseCheck]
            unfold extendedLeft at complete
            unfold certificateTail at complete
            rw [formulaClauseWorkSymbols_cons_append]
            exact complete
          · unfold checkClauses
            rw [clauseCheck]
            exact finalState

theorem canonical_formula_semantic_count_exact
    (formula : CNFFormula) (assignment : BitString)
    (counter left right : List WorkSymbol)
    (width : assignment.length = formula.variableCount)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    ∃ final,
      workRunExact? cnfWorkMachine
          (formulaSemanticStepCount assignment counter formula.clauses)
          (workConfigAtWord CNFWorkState.clauseStart left
            (cnfTokenWorkSymbols
                (encodeClauseListTokens formula.clauses ++ [.finish]) ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) =
        some final ∧
      final.state =
        if checkCNF formula assignment then
          CNFWorkState.accept
        else
          CNFWorkState.reject := by
  rw [cnfTokenWorkSymbols_encodeFormulaClauses]
  rcases formula_semantic_count_exact formula.clauses assignment counter
    left right counterAllowed with ⟨final, exactRun, finalState⟩
  refine ⟨final, exactRun, ?_⟩
  rw [checkCNF_eq_checkClauses_of_width formula assignment width]
  exact finalState

theorem formulaClauseWorkSymbols_length_cons
    (clause : List CNFLiteral) (rest : List (List CNFLiteral)) :
    (formulaClauseWorkSymbols (clause :: rest)).length =
      ((literalListWorkSymbols clause).length + 2) +
        (formulaClauseWorkSymbols rest).length := by
  calc
    (formulaClauseWorkSymbols (clause :: rest)).length =
        Nat.succ
          (literalListWorkSymbols clause ++
            cnfFinish :: formulaClauseWorkSymbols rest).length := rfl
    _ = Nat.succ
        ((literalListWorkSymbols clause).length +
          (cnfFinish :: formulaClauseWorkSymbols rest).length) :=
      congrArg Nat.succ
        (workSymbol_length_append (literalListWorkSymbols clause)
          (cnfFinish :: formulaClauseWorkSymbols rest))
    _ = Nat.succ
        ((literalListWorkSymbols clause).length +
          Nat.succ (formulaClauseWorkSymbols rest).length) := rfl
    _ = ((literalListWorkSymbols clause).length + 2) +
        (formulaClauseWorkSymbols rest).length := by
      rw [Nat.add_succ]
      rw [Nat.succ_add, Nat.succ_add]

private theorem formulaNatAddMulClean (a b c : Nat) :
    (a + b) * c = a * c + b * c := by
  induction c with
  | zero => rfl
  | succ c ih =>
      change (a + b) * c + (a + b) =
        (a * c + a) + (b * c + b)
      rw [ih]
      exact FrameTraceDesign.frame_add_four_reorder
        (a * c) (b * c) a b

private theorem one_le_formulaUnitCharge (n : Nat) :
    1 ≤ cnfShiftedWorkSpan n * 12 := by
  have oneSpan : 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
    exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))
  have twelvePositive : 0 < 12 := Nat.zero_lt_succ 11
  exact Nat.le_trans oneSpan
    (Nat.le_mul_of_pos_right (cnfShiftedWorkSpan n) twelvePositive)

private theorem formulaCharge_plus_successor_mul
    (index charge : Nat) :
    charge + (index + 1) * charge =
      (Nat.succ index + 1) * charge := by
  change charge + Nat.succ index * charge =
    Nat.succ (Nat.succ index) * charge
  calc
    charge + Nat.succ index * charge =
        charge + (index * charge + charge) :=
      congrArg (Nat.add charge) (Nat.succ_mul index charge)
    _ = (index * charge + charge) + charge := by
      rw [← Nat.add_assoc]
      rw [Nat.add_comm charge (index * charge)]
    _ = Nat.succ index * charge + charge :=
      congrArg (fun value => value + charge)
        (Nat.succ_mul index charge).symm
    _ = Nat.succ (Nat.succ index) * charge :=
      (Nat.succ_mul (Nat.succ index) charge).symm

private theorem formulaTwo_le_twoCharges (charge : Nat)
    (oneCharge : 1 ≤ charge) :
    2 ≤ 2 * charge := by
  have pair := Nat.add_le_add oneCharge oneCharge
  have normalize : charge + charge = 2 * charge := by
    calc
      charge + charge = 1 * charge + charge :=
        congrArg (fun value => value + charge) (Nat.one_mul charge).symm
      _ = 2 * charge := (Nat.succ_mul 1 charge).symm
  exact Nat.le_trans pair (Nat.le_of_eq normalize)

theorem formulaSemanticStepCount_le_encodedCharge
    (n : Nat) (assignment : BitString) (counter : List WorkSymbol)
    (clauses : List (List CNFLiteral))
    (assignmentBound : assignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaBound : (formulaClauseWorkSymbols clauses).length ≤ n) :
    formulaSemanticStepCount assignment counter clauses ≤
      ((formulaClauseWorkSymbols clauses).length + 1) *
        (cnfShiftedWorkSpan n * 12) := by
  induction clauses with
  | nil =>
      unfold formulaSemanticStepCount formulaClauseWorkSymbols
      exact formulaTwo_le_twoCharges (cnfShiftedWorkSpan n * 12)
        (one_le_formulaUnitCharge n)
  | cons clause rest ih =>
      have normalizedFormulaBound :
          ((literalListWorkSymbols clause).length + 2) +
              (formulaClauseWorkSymbols rest).length ≤ n := by
        rw [formulaClauseWorkSymbols_length_cons] at formulaBound
        exact formulaBound
      have clauseSegmentBound :
          (literalListWorkSymbols clause).length + 1 +
              (formulaClauseWorkSymbols rest).length ≤ n := by
        have oneTwo : 1 ≤ 2 := Nat.le_succ 1
        have literalToEncoded := Nat.add_le_add_left oneTwo
          (literalListWorkSymbols clause).length
        have withRest := Nat.add_le_add_right literalToEncoded
          (formulaClauseWorkSymbols rest).length
        exact Nat.le_trans withRest normalizedFormulaBound
      have restFormulaBound :
          (formulaClauseWorkSymbols rest).length ≤ n :=
        Nat.le_trans
          (Nat.le_add_left (formulaClauseWorkSymbols rest).length
            ((literalListWorkSymbols clause).length + 2))
          normalizedFormulaBound
      have clauseBound := clauseSemanticStepCount_le_encodedCharge n
        assignment counter (formulaClauseWorkSymbols rest) clause
        assignmentBound counterBound clauseSegmentBound
      have prefixBound :
          1 + clauseSemanticStepCount assignment counter
              (formulaClauseWorkSymbols rest) clause ≤
            ((literalListWorkSymbols clause).length + 2) *
              (cnfShiftedWorkSpan n * 12) := by
        have combined := Nat.add_le_add (one_le_formulaUnitCharge n)
          clauseBound
        exact Nat.le_trans combined
          (Nat.le_of_eq
            (formulaCharge_plus_successor_mul
              (literalListWorkSymbols clause).length
              (cnfShiftedWorkSpan n * 12)))
      have restBound := ih restFormulaBound
      have distributed := formulaNatAddMulClean
        ((literalListWorkSymbols clause).length + 2)
        ((formulaClauseWorkSymbols rest).length + 1)
        (cnfShiftedWorkSpan n * 12)
      have coefficient :
          ((literalListWorkSymbols clause).length + 2) +
              ((formulaClauseWorkSymbols rest).length + 1) =
            (((literalListWorkSymbols clause).length + 2) +
              (formulaClauseWorkSymbols rest).length) + 1 :=
        (Nat.add_assoc ((literalListWorkSymbols clause).length + 2)
          (formulaClauseWorkSymbols rest).length 1).symm
      have normalize :
          ((literalListWorkSymbols clause).length + 2) *
                (cnfShiftedWorkSpan n * 12) +
              ((formulaClauseWorkSymbols rest).length + 1) *
                (cnfShiftedWorkSpan n * 12) =
            ((((literalListWorkSymbols clause).length + 2) +
              (formulaClauseWorkSymbols rest).length) + 1) *
                (cnfShiftedWorkSpan n * 12) :=
        distributed.symm.trans
          (congrArg (fun count =>
            count * (cnfShiftedWorkSpan n * 12)) coefficient)
      cases clauseCheck : checkClause clause assignment with
      | false =>
          unfold formulaSemanticStepCount
          rw [clauseCheck]
          rw [formulaClauseWorkSymbols_length_cons]
          exact Nat.le_trans prefixBound
            (Nat.le_trans
              (Nat.le_add_right
                (((literalListWorkSymbols clause).length + 2) *
                  (cnfShiftedWorkSpan n * 12))
                (((formulaClauseWorkSymbols rest).length + 1) *
                  (cnfShiftedWorkSpan n * 12)))
              (Nat.le_of_eq normalize))
      | true =>
          unfold formulaSemanticStepCount
          rw [clauseCheck]
          rw [formulaClauseWorkSymbols_length_cons]
          exact Nat.le_trans (Nat.add_le_add prefixBound restBound)
            (Nat.le_of_eq normalize)

theorem formulaSemanticStepCount_le_singlePhase
    (n : Nat) (assignment : BitString) (counter : List WorkSymbol)
    (clauses : List (List CNFLiteral))
    (assignmentBound : assignment.length ≤ n)
    (counterBound : counter.length ≤ n)
    (formulaBound : (formulaClauseWorkSymbols clauses).length ≤ n) :
    formulaSemanticStepCount assignment counter clauses ≤
      cnfSinglePhaseBudget n := by
  have accumulated := formulaSemanticStepCount_le_encodedCharge n
    assignment counter clauses assignmentBound counterBound formulaBound
  have outerToSuccessor := Nat.add_le_add_right formulaBound 1
  have successorToSpan : n + 1 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.add_le_add_left (Nat.le_succ 1) n
  have outerBound : (formulaClauseWorkSymbols clauses).length + 1 ≤
      cnfShiftedWorkSpan n :=
    Nat.le_trans outerToSuccessor successorToSpan
  exact ClauseLiteralDesign.clauseLiteral_accumulated_le_singlePhaseBudget
    n ((formulaClauseWorkSymbols clauses).length + 1)
    (cnfShiftedWorkSpan n * 12)
    (formulaSemanticStepCount assignment counter clauses)
    outerBound (Nat.le_refl (cnfShiftedWorkSpan n * 12)) accumulated

theorem formulaClauseWorkSymbols_length_le_encodeFormulaTokens
    (formula : CNFFormula) :
    (formulaClauseWorkSymbols formula.clauses).length ≤
      (encodeFormulaTokens formula).length := by
  rw [← cnfTokenWorkSymbols_encodeFormulaClauses]
  rw [cnfTokenWorkSymbols_length]
  have formulaShape : encodeFormulaTokens formula =
      encodeUnaryTokens formula.variableCount ++
        (encodeClauseListTokens formula.clauses ++ [CNFToken.finish]) := by
    unfold encodeFormulaTokens encodeCNFTokens
    exact token_append_assoc_constructive
      (encodeUnaryTokens formula.variableCount)
      (encodeClauseListTokens formula.clauses) [CNFToken.finish]
  rw [formulaShape]
  exact Nat.le_trans
    (Nat.le_add_left
      (encodeClauseListTokens formula.clauses ++ [CNFToken.finish]).length
      (encodeUnaryTokens formula.variableCount).length)
    (Nat.le_of_eq
      (token_length_append_constructive
        (encodeUnaryTokens formula.variableCount)
        (encodeClauseListTokens formula.clauses ++
          [CNFToken.finish])).symm)

theorem decodedFormulaSemanticStepCount_le_pairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    formulaSemanticStepCount assignment
        (List.replicate assignment.length cnfMarkFalse) formula.clauses ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  have combinedBound :=
    FrameTraceDesign.decoded_frame_payload_length_le_pair_size
      input certificate formula assignment formulaDecoded assignmentDecoded
  have formulaTokenBound : (encodeFormulaTokens formula).length ≤
      BitString.size (BitString.pair input certificate) :=
    Nat.le_trans
      (Nat.le_add_right (encodeFormulaTokens formula).length
        assignment.length)
      combinedBound
  have assignmentBound : assignment.length ≤
      BitString.size (BitString.pair input certificate) :=
    Nat.le_trans
      (Nat.le_add_left assignment.length
        (encodeFormulaTokens formula).length)
      combinedBound
  have formulaBound : (formulaClauseWorkSymbols formula.clauses).length ≤
      BitString.size (BitString.pair input certificate) :=
    Nat.le_trans
      (formulaClauseWorkSymbols_length_le_encodeFormulaTokens formula)
      formulaTokenBound
  have counterBound :
      (List.replicate assignment.length cnfMarkFalse).length ≤
        BitString.size (BitString.pair input certificate) := by
    rw [workSymbol_replicate_length]
    exact assignmentBound
  exact formulaSemanticStepCount_le_singlePhase
    (BitString.size (BitString.pair input certificate)) assignment
    (List.replicate assignment.length cnfMarkFalse) formula.clauses
    assignmentBound counterBound formulaBound

theorem canonical_formula_semantic_withinPairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (left right : List WorkSymbol)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (width : assignment.length = formula.variableCount) :
    ∃ final,
      formulaSemanticStepCount assignment
          (List.replicate assignment.length cnfMarkFalse) formula.clauses ≤
        cnfSinglePhaseBudget
          (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine
          (formulaSemanticStepCount assignment
            (List.replicate assignment.length cnfMarkFalse) formula.clauses)
          (workConfigAtWord CNFWorkState.clauseStart left
            (cnfTokenWorkSymbols
                (encodeClauseListTokens formula.clauses ++ [.finish]) ++
              (cnfBoundaryGuard ::
                (List.replicate assignment.length cnfMarkFalse ++
                  (cnfFinish ::
                    (assignmentWorkSymbols assignment ++
                      (cnfRootGuard :: right))))))) =
        some final ∧
      final.state =
        if checkCNF formula assignment then
          CNFWorkState.accept
        else
          CNFWorkState.reject := by
  have phaseBound := decodedFormulaSemanticStepCount_le_pairSinglePhase
    input certificate formula assignment formulaDecoded assignmentDecoded
  have counterAllowed : ∀ symbol,
      List.Mem symbol (List.replicate assignment.length cnfMarkFalse) →
        symbol = cnfMarkFalse := by
    intro symbol member
    exact FrameTraceDesign.mem_replicate_workSymbol_eq
      assignment.length cnfMarkFalse symbol member
  rcases canonical_formula_semantic_count_exact formula assignment
    (List.replicate assignment.length cnfMarkFalse) left right width
    counterAllowed with ⟨final, exactRun, finalState⟩
  exact ⟨final, phaseBound, exactRun, finalState⟩

end ClauseLiteralCostDesign

end PNP.Concrete

namespace PNP.Concrete

namespace MalformedFuelDesign

open FrameTraceDesign

set_option maxRecDepth 100000

theorem bitStringSize_le_pairSize_left
    (input certificate : BitString) :
    BitString.size input ≤
      BitString.size (BitString.pair input certificate) := by
  rw [BitString.size_pair_normalized]
  have oneTwo : 1 ≤ 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  have toDouble : BitString.size input ≤ 2 * BitString.size input :=
    Nat.le_mul_of_pos_left (BitString.size input) oneTwo
  have toCertificate : 2 * BitString.size input ≤
      2 * BitString.size input + 2 * BitString.size certificate :=
    Nat.le_add_right _ _
  have toBoundary :
      2 * BitString.size input + 2 * BitString.size certificate ≤
        2 * BitString.size input + 2 * BitString.size certificate + 2 :=
    Nat.le_add_right _ 2
  exact Nat.le_trans toDouble (Nat.le_trans toCertificate toBoundary)

theorem bitStringSize_le_pairSize_right
    (input certificate : BitString) :
    BitString.size certificate ≤
      BitString.size (BitString.pair input certificate) := by
  rw [BitString.size_pair_normalized]
  have oneTwo : 1 ≤ 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  have toDouble : BitString.size certificate ≤
      2 * BitString.size certificate :=
    Nat.le_mul_of_pos_left (BitString.size certificate) oneTwo
  have toFormula : 2 * BitString.size certificate ≤
      2 * BitString.size input + 2 * BitString.size certificate :=
    Nat.le_add_left _ _
  have toBoundary :
      2 * BitString.size input + 2 * BitString.size certificate ≤
        2 * BitString.size input + 2 * BitString.size certificate + 2 :=
    Nat.le_add_right _ 2
  exact Nat.le_trans toDouble (Nat.le_trans toFormula toBoundary)

theorem componentSizes_le_pairSize (input certificate : BitString) :
    BitString.size input + BitString.size certificate ≤
      BitString.size (BitString.pair input certificate) := by
  rw [BitString.size_pair_normalized]
  have oneTwo : 1 ≤ 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  have inputDouble : BitString.size input ≤ 2 * BitString.size input :=
    Nat.le_mul_of_pos_left (BitString.size input) oneTwo
  have certificateDouble : BitString.size certificate ≤
      2 * BitString.size certificate :=
    Nat.le_mul_of_pos_left (BitString.size certificate) oneTwo
  have doubled := Nat.add_le_add inputDouble certificateDouble
  exact Nat.le_trans doubled (Nat.le_add_right _ 2)

theorem tokenLength_le_encodedPairsSize (tokens : List CNFToken) :
    tokens.length ≤ BitString.size (encodeTokenPairs tokens) := by
  unfold BitString.size
  rw [encodeTokenPairs_length]
  have oneTwo : 1 ≤ 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  exact Nat.le_mul_of_pos_left tokens.length oneTwo

theorem tokenLength_le_encodedPairsBitSize
    (tokens : List CNFToken) (last : Bool) :
    tokens.length ≤
      BitString.size (encodeTokenPairs tokens ++ [last]) := by
  unfold BitString.size
  rw [BitString.length_append_constructive]
  rw [encodeTokenPairs_length]
  rw [List.length_singleton]
  have oneTwo : 1 ≤ 2 := by
    change 1 ≤ 1 + 1
    exact Nat.le_add_right 1 1
  exact Nat.le_trans (Nat.le_mul_of_pos_left tokens.length oneTwo)
    (Nat.le_add_right _ 1)

theorem frameOneBadBoundarySteps_le_terminal
    (tokens : List CNFToken) :
    frameOneBadBoundarySteps tokens ≤ frameOneTerminalSteps tokens := by
  unfold frameOneBadBoundarySteps frameOneTerminalSteps
  have h0 : tokens.length + 1 ≤
      (tokens.length + 1) + tokens.length :=
    Nat.le_add_right _ _
  have h1 : tokens.length + 1 ≤
      ((tokens.length + 1) + tokens.length) + 1 :=
    Nat.le_trans h0 (Nat.le_add_right _ 1)
  have h2 : ((tokens.length + 1) + tokens.length) + 1 ≤
      (((tokens.length + 1) + tokens.length) + 1) + tokens.length :=
    Nat.le_add_right _ _
  have h3 : ((tokens.length + 1) + tokens.length) + 1 ≤
      ((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1 :=
    Nat.le_trans h2 (Nat.le_add_right _ 1)
  have h4 :
      ((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1 ≤
        (((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1) +
          tokens.length :=
    Nat.le_add_right _ _
  have h5 : ((tokens.length + 1) + tokens.length) + 1 ≤
      ((((((tokens.length + 1) + tokens.length) + 1) + tokens.length) + 1) +
        tokens.length) + 1 :=
    Nat.le_trans h3 (Nat.le_trans h4 (Nat.le_add_right _ 1))
  exact h5

theorem frameTwoMalformedCounterSteps_le_terminal
    (assignment : BitString) :
    assignment.length + 1 ≤ frameTwoTerminalSteps assignment := by
  unfold frameTwoTerminalSteps
  have h0 : assignment.length + 1 ≤
      (assignment.length + 1) + assignment.length :=
    Nat.le_add_right _ _
  have h1 : assignment.length + 1 ≤
      ((assignment.length + 1) + assignment.length) + 1 :=
    Nat.le_trans h0 (Nat.le_add_right _ 1)
  have h2 : assignment.length + 1 ≤
      (((assignment.length + 1) + assignment.length) + 1) + 1 :=
    Nat.le_trans h1 (Nat.le_add_right _ 1)
  have h3 : assignment.length + 1 ≤
      ((((assignment.length + 1) + assignment.length) + 1) + 1) + 1 :=
    Nat.le_trans h2 (Nat.le_add_right _ 1)
  have h4 : assignment.length + 1 ≤
      (((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
        assignment.length :=
    Nat.le_trans h3 (Nat.le_add_right _ _)
  exact Nat.le_trans h4 (Nat.le_add_right _ 1)

theorem formulaBadPadLayout_reject_with_successCost
    (tokens : List CNFToken) (certificateNonempty : Bool)
    (suffix : List WorkSymbol) :
    ∃ steps tape,
      steps ≤ frameSuccessSteps tokens [] ∧
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
        (cnfFinish :: badFormulaBoundary certificateNonempty :: suffix)),
        ?_, ?_⟩
      · unfold frameSuccessSteps frameOneFoldSteps frameOneTerminalSteps
          frameTwoFoldSteps frameTwoTerminalSteps
        change 1 ≤ 2 + 4 + 5
        exact Nat.le_add_right 1 10
      · cases certificateNonempty <;> rfl
  | cons token rest =>
      let allTokens := token :: rest
      have hBoot := boot_t_exact
        (List.replicate rest.length cnfT ++ cnfFinish ::
          (token.workSymbol ::
            (cnfTokenWorkSymbols rest ++
              badFormulaBoundary certificateNonempty :: suffix)))
      have hBad := frameOne_badBoundary_exact allTokens
        certificateNonempty suffix
      rw [frameOneBoundaryFoldStart_cons] at hBad
      have hComplete := workRunExact?_compose cnfWorkMachine 2
        (frameOneFoldSteps [] [] allTokens +
          frameOneBadBoundarySteps allTokens)
        _ _ _ hBoot hBad
      let steps := 2 +
        (frameOneFoldSteps [] [] allTokens +
          frameOneBadBoundarySteps allTokens)
      let final := workConfigAtWord CNFWorkState.reject
        (pushWorkLeft (frameOneMarkedTokens allTokens)
          (cnfFinish ::
            pushWorkLeft
              (List.replicate allTokens.length cnfMarkFalse)
              [cnfRootGuard]))
        (badFormulaBoundary certificateNonempty :: suffix)
      refine ⟨steps, final.tape, ?_, ?_⟩
      · have terminalBound := frameOneBadBoundarySteps_le_terminal allTokens
        have firstBound : steps ≤
            2 + (frameOneFoldSteps [] [] allTokens +
              frameOneTerminalSteps allTokens) :=
          Nat.add_le_add_left
            (Nat.add_le_add_left terminalBound
              (frameOneFoldSteps [] [] allTokens)) 2
        have secondBound :
            2 + (frameOneFoldSteps [] [] allTokens +
                frameOneTerminalSteps allTokens) ≤
              (2 + (frameOneFoldSteps [] [] allTokens +
                frameOneTerminalSteps allTokens)) +
                  (frameTwoFoldSteps [] [] [] + frameTwoTerminalSteps []) :=
          Nat.le_add_right _ _
        unfold frameSuccessSteps
        exact Nat.le_trans firstBound secondBound
      · have startShape :
            List.replicate allTokens.length cnfT ++ cnfFinish ::
                (cnfTokenWorkSymbols allTokens ++
                  badFormulaBoundary certificateNonempty :: suffix) =
              cnfT ::
                (List.replicate rest.length cnfT ++ cnfFinish ::
                  token.workSymbol ::
                    (cnfTokenWorkSymbols rest ++
                      badFormulaBoundary certificateNonempty :: suffix)) :=
          rfl
        unfold steps final allTokens
        rw [startShape]
        exact hComplete

theorem formulaEvenHeaderSteps_le_singlePhase
    (n count steps : Nat) (countBound : count ≤ n)
    (stepsBound : steps ≤ count + 4) :
    steps ≤ cnfSinglePhaseBudget n := by
  have countFour : count + 4 ≤ n + 4 :=
    Nat.add_le_add_right countBound 4
  have nToSpan : n ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2
  have twoToSpan : 2 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_left 2 n
  have fourToTwiceSpan : 4 ≤
      cnfShiftedWorkSpan n + cnfShiftedWorkSpan n := by
    change 2 + 2 ≤ cnfShiftedWorkSpan n + cnfShiftedWorkSpan n
    exact Nat.add_le_add twoToSpan twoToSpan
  have raw : n + 4 ≤
      cnfShiftedWorkSpan n +
        (cnfShiftedWorkSpan n + cnfShiftedWorkSpan n) :=
    Nat.add_le_add nToSpan fourToTwiceSpan
  have normalized :
      cnfShiftedWorkSpan n +
          (cnfShiftedWorkSpan n + cnfShiftedWorkSpan n) =
        cnfShiftedWorkSpan n * 3 := by
    calc
      cnfShiftedWorkSpan n +
          (cnfShiftedWorkSpan n + cnfShiftedWorkSpan n) =
          (cnfShiftedWorkSpan n + cnfShiftedWorkSpan n) +
            cnfShiftedWorkSpan n :=
        (Nat.add_assoc (cnfShiftedWorkSpan n)
          (cnfShiftedWorkSpan n) (cnfShiftedWorkSpan n)).symm
      _ = cnfShiftedWorkSpan n * 3 := by
        rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_one]
  have coefficientBound : 3 ≤ 16 := by
    change 3 ≤ 3 + 13
    exact Nat.le_add_right 3 13
  exact Nat.le_trans stepsBound
    (Nat.le_trans countFour
      (Nat.le_trans raw
        (Nat.le_trans (Nat.le_of_eq normalized)
          (cnfScaledLinear_le_singlePhaseBudget n 3 coefficientBound))))

theorem one_le_encodedPairsBitSize
    (tokens : List CNFToken) (last : Bool) :
    1 ≤ BitString.size (encodeTokenPairs tokens ++ [last]) := by
  unfold BitString.size
  rw [BitString.length_append_constructive]
  rw [List.length_singleton]
  exact Nat.le_add_left 1 (encodeTokenPairs tokens).length

theorem five_le_shiftedPairSpan_of_inputPos
    (input certificate : BitString)
    (inputPos : 1 ≤ BitString.size input) :
    5 ≤ cnfShiftedWorkSpan
      (BitString.size (BitString.pair input certificate)) := by
  unfold cnfShiftedWorkSpan
  rw [BitString.size_pair_normalized]
  have twiceInput : 2 ≤ 2 * BitString.size input :=
    Nat.mul_le_mul_left 2 inputPos
  have certificateNonnegative : 0 ≤ 2 * BitString.size certificate :=
    Nat.zero_le _
  have first := Nat.add_le_add twiceInput certificateNonnegative
  have second := Nat.add_le_add_right first 2
  have threeFour : 3 ≤ 4 := by
    change 3 ≤ 3 + 1
    exact Nat.le_add_right 3 1
  have pairAtLeastThree : 3 ≤
      2 * BitString.size input + 2 * BitString.size certificate + 2 :=
    Nat.le_trans threeFour second
  have shifted := Nat.add_le_add_right pairAtLeastThree 2
  exact shifted

theorem formulaRawDecoder_none_rejects_withinPairSinglePhase
    (input certificate : BitString)
    (decoded : decodeFormulaTokenPairs input = none) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
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
      rcases pairedWorkTape_formulaEven_shape tokens certificate with
        ⟨bit, suffix, tapeShape⟩
      rcases formulaEvenHeader_reject tokens.length bit suffix with
        ⟨steps, left, stepBound, run⟩
      have tokenToInput : tokens.length ≤ BitString.size input := by
        rw [evenShape]
        exact tokenLength_le_encodedPairsSize tokens
      have tokenToPair : tokens.length ≤
          BitString.size (BitString.pair input certificate) :=
        Nat.le_trans tokenToInput
          (bitStringSize_le_pairSize_left input certificate)
      have phaseBound := formulaEvenHeaderSteps_le_singlePhase
        (BitString.size (BitString.pair input certificate))
        tokens.length steps tokenToPair stepBound
      refine ⟨steps,
        (workConfigAtWord CNFWorkState.reject left
          (leadingZeroWorkSymbol bit :: suffix)).tape,
        phaseBound, ?_⟩
      rw [evenShape, tapeShape]
      exact run
  | inr badPadShape =>
      rcases pairedWorkTape_formulaBadPad_shape tokens certificate with
        ⟨certificateNonempty, suffix, tapeShape⟩
      rcases formulaBadPadLayout_reject_with_successCost tokens
        certificateNonempty suffix with ⟨steps, tape, costBound, run⟩
      have tokenToInput : tokens.length ≤ BitString.size input := by
        rw [badPadShape]
        exact tokenLength_le_encodedPairsBitSize tokens true
      have tokenToPair : tokens.length ≤
          BitString.size (BitString.pair input certificate) :=
        Nat.le_trans tokenToInput
          (bitStringSize_le_pairSize_left input certificate)
      have combinedBound : tokens.length + ([] : BitString).length ≤
          BitString.size (BitString.pair input certificate) := by
        exact tokenToPair
      have inputPos : 1 ≤ BitString.size input := by
        rw [badPadShape]
        exact one_le_encodedPairsBitSize tokens true
      have fiveSpan := five_le_shiftedPairSpan_of_inputPos input certificate
        inputPos
      have successBound := frameSuccessSteps_le_singlePhase
        (BitString.size (BitString.pair input certificate)) tokens []
        combinedBound fiveSpan
      refine ⟨steps, tape, Nat.le_trans costBound successBound, ?_⟩
      rw [badPadShape, tapeShape]
      exact run

theorem assignmentRawDecoder_none_rejects_withinPairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (decoded : decodeTokenPairs certificate = none) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have inputShape := encodeFormula_of_decode input formula formulaDecoded
  rcases decodeTokenPairs_none_shape certificate decoded with
    ⟨certificateTokens, last, certificateShape⟩
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
  let steps :=
    (2 + (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest))) +
      (certificateTokens.length + 1)
  let dummyAssignment : BitString :=
    List.replicate certificateTokens.length false
  have dummyLength : dummyAssignment.length = certificateTokens.length := by
    unfold dummyAssignment
    exact BitString.length_replicate_constructive
      certificateTokens.length false
  have malformedCounterToTerminal : certificateTokens.length + 1 ≤
      frameTwoTerminalSteps dummyAssignment := by
    have bound := frameTwoMalformedCounterSteps_le_terminal dummyAssignment
    rw [dummyLength] at bound
    exact bound
  have malformedCounterToFrameTwo : certificateTokens.length + 1 ≤
      frameTwoFoldSteps [] [] dummyAssignment +
        frameTwoTerminalSteps dummyAssignment :=
    Nat.le_trans malformedCounterToTerminal
      (Nat.le_add_left (frameTwoTerminalSteps dummyAssignment)
        (frameTwoFoldSteps [] [] dummyAssignment))
  have costToSuccess : steps ≤
      frameSuccessSteps (first :: rest) dummyAssignment := by
    unfold steps frameSuccessSteps
    exact Nat.add_le_add_left malformedCounterToFrameTwo
      (2 + (frameOneFoldSteps [] [] (first :: rest) +
        frameOneTerminalSteps (first :: rest)))
  have formulaTokenToInput : (encodeFormulaTokens formula).length ≤
      BitString.size input := by
    rw [← inputShape]
    unfold encodeFormula encodeCNF
    exact tokenLength_le_encodedPairsBitSize
      (encodeCNFTokens formula) false
  have certificateTokenToCertificate : certificateTokens.length ≤
      BitString.size certificate := by
    rw [certificateShape]
    exact tokenLength_le_encodedPairsBitSize certificateTokens last
  have dummyToCertificate : dummyAssignment.length ≤
      BitString.size certificate := by
    rw [dummyLength]
    exact certificateTokenToCertificate
  have combinedToComponents :
      (encodeFormulaTokens formula).length + dummyAssignment.length ≤
        BitString.size input + BitString.size certificate :=
    Nat.add_le_add formulaTokenToInput dummyToCertificate
  have combinedBound :
      (encodeFormulaTokens formula).length + dummyAssignment.length ≤
        BitString.size (BitString.pair input certificate) :=
    Nat.le_trans combinedToComponents
      (componentSizes_le_pairSize input certificate)
  have inputPos : 1 ≤ BitString.size input := by
    rw [← inputShape]
    unfold encodeFormula encodeCNF
    exact one_le_encodedPairsBitSize (encodeCNFTokens formula) false
  have fiveSpan := five_le_shiftedPairSpan_of_inputPos input certificate
    inputPos
  have successBound := frameSuccessSteps_le_singlePhase
    (BitString.size (BitString.pair input certificate))
    (encodeFormulaTokens formula) dummyAssignment combinedBound fiveSpan
  have tokenCostShape :
      frameSuccessSteps (first :: rest) dummyAssignment =
        frameSuccessSteps (encodeFormulaTokens formula) dummyAssignment :=
    congrArg (fun tokens => frameSuccessSteps tokens dummyAssignment)
      tokenShape.symm
  have phaseBound : steps ≤ cnfSinglePhaseBudget
      (BitString.size (BitString.pair input certificate)) := by
    rw [tokenCostShape] at costToSuccess
    exact Nat.le_trans costToSuccess successBound
  refine ⟨steps,
    (workConfigAtWord CNFWorkState.reject finalLeft
      (leadingZeroWorkSymbol bit :: suffix)).tape,
    phaseBound, ?_⟩
  rw [← inputShape]
  rw [encodeFormula_eq_padded_tokens]
  unfold paddedFormulaTokenBits
  rw [certificateShape]
  rw [tapeShape]
  rw [tokenShape]
  unfold steps
  exact hComplete

end MalformedFuelDesign

end PNP.Concrete


namespace PNP.Concrete
namespace WidthSuccessDesign

open FrameTraceDesign
open ClauseLiteralCostDesign
open ClauseLiteralDesign

set_option maxRecDepth 100000

theorem widthRestoreAssignment_finish_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
          (cnfFinish :: leftTail) rightSide) =
      some (workConfigAtLeftWord
        CNFWorkState.widthRestoreCertificateCounter leftTail
        (cnfFinish :: rightSide)) := by
  rfl

theorem widthRestoreCounter_markFalse_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreCertificateCounter
          (cnfMarkFalse :: leftTail) rightSide) =
      some (workConfigAtLeftWord
        CNFWorkState.widthRestoreCertificateCounter leftTail
        (cnfMarkFalse :: rightSide)) := by
  rfl

theorem widthRestoreCounter_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.widthRestoreCertificateCounter
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord
        CNFWorkState.widthRestoreCertificateCounter leftSuffix
        (pushWorkLeft word rightSide)) := by
  apply workRunExact?_scanLeft cnfWorkMachine
    CNFWorkState.widthRestoreCertificateCounter
    (fun symbol => symbol = cnfMarkFalse)
  · intro head leftTail foundRight equal
    cases equal
    exact widthRestoreCounter_markFalse_step leftTail foundRight
  · exact allowed

theorem widthRestoreCounter_boundary_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreCertificateCounter
          (cnfBoundaryGuard :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
        leftTail (cnfBoundaryGuard :: rightSide)) := by
  rfl

theorem widthRestoreCounter_run
    (counter leftBase rightSide : List WorkSymbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine ((1 + counter.length) + 1)
        (workConfigAtLeftWord CNFWorkState.widthRestoreAssignment
          (cnfFinish :: pushWorkLeft counter
            (cnfBoundaryGuard :: leftBase)) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
        leftBase
        (cnfBoundaryGuard :: (counter ++ cnfFinish :: rightSide))) := by
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthRestoreAssignment_finish_step
      (pushWorkLeft counter (cnfBoundaryGuard :: leftBase)) rightSide)
  have reversedAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft counter []) →
        symbol = cnfMarkFalse := by
    intro symbol member
    exact pushWorkLeft_allowed (fun candidate => candidate = cnfMarkFalse)
      counter [] counterAllowed
      (by intro candidate impossible; contradiction) symbol member
  have hCounter := widthRestoreCounter_scan
    (pushWorkLeft counter []) (cnfBoundaryGuard :: leftBase)
    (cnfFinish :: rightSide) reversedAllowed
  have counterLength : (pushWorkLeft counter []).length = counter.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero counter.length
  rw [counterLength] at hCounter
  rw [pushWorkLeft_append_far] at hFinish
  have throughCounter := workRunExact?_compose cnfWorkMachine 1
    counter.length _ _ _ hFinish hCounter
  rw [pushWorkLeft_cancel] at throughCounter
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthRestoreCounter_boundary_step leftBase
      (counter ++ cnfFinish :: rightSide))
  have complete := workRunExact?_compose cnfWorkMachine
    (1 + counter.length) 1 _ _ _ throughCounter hBoundary
  rw [← pushWorkLeft_append_far counter
    (cnfBoundaryGuard :: leftBase)] at complete
  exact complete

theorem widthRestoreBackFormula_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      FormulaOrCounterSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
        leftSuffix (pushWorkLeft word rightSide)) := by
  exact workRunExact?_scanLeft cnfWorkMachine
    CNFWorkState.widthRestoreBackFormula FormulaOrCounterSymbol
    widthRestoreBackFormula_step word leftSuffix rightSide allowed

theorem widthRestoreBackFormula_root_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
          (cnfRootGuard :: leftTail) rightSide) =
      some (workConfigAtWord CNFWorkState.widthRestoreSeekFormula
        (cnfRootGuard :: leftTail) rightSide) := by
  cases rightSide <;> rfl

theorem widthRestorePhysical_run
    (physical rightSide : List WorkSymbol)
    (physicalAllowed : ∀ symbol, List.Mem symbol physical →
      FormulaOrCounterSymbol symbol) :
    workRunExact? cnfWorkMachine (physical.length + 1)
        (workConfigAtLeftWord CNFWorkState.widthRestoreBackFormula
          (pushWorkLeft physical [] ++ [cnfRootGuard]) rightSide) =
      some (workConfigAtWord CNFWorkState.widthRestoreSeekFormula
        [cnfRootGuard] (physical ++ rightSide)) := by
  have reversedAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft physical []) →
        FormulaOrCounterSymbol symbol := by
    intro symbol member
    exact pushWorkLeft_allowed FormulaOrCounterSymbol physical []
      physicalAllowed (by intro candidate impossible; contradiction)
      symbol member
  have hPhysical := widthRestoreBackFormula_scan
    (pushWorkLeft physical []) [cnfRootGuard] rightSide reversedAllowed
  have physicalLength :
      (pushWorkLeft physical []).length = physical.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero physical.length
  rw [physicalLength] at hPhysical
  rw [pushWorkLeft_cancel] at hPhysical
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthRestoreBackFormula_root_step [] (physical ++ rightSide))
  exact workRunExact?_compose cnfWorkMachine physical.length 1
    _ _ _ hPhysical hRoot

theorem widthRestoreSeekFormula_counter_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthRestoreSeekFormula leftSide
          (cnfMarkFalse :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthRestoreSeekFormula
        (cnfMarkFalse :: leftSide) suffix) := by
  rfl

theorem widthRestoreSeekFormula_counter_scan
    (word suffix leftSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtWord CNFWorkState.widthRestoreSeekFormula leftSide
          (word ++ suffix)) =
      some (workConfigAtWord CNFWorkState.widthRestoreSeekFormula
        (pushWorkLeft word leftSide) suffix) := by
  exact workRunExact?_scanRight cnfWorkMachine
    CNFWorkState.widthRestoreSeekFormula
    (fun symbol => symbol = cnfMarkFalse)
    (by
      intro foundLeft head foundSuffix equal
      cases equal
      exact widthRestoreSeekFormula_counter_step foundLeft foundSuffix)
    word suffix leftSide allowed

theorem widthRestoreSeekFormula_finish_step
    (leftSide suffix : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtWord CNFWorkState.widthRestoreSeekFormula leftSide
          (cnfFinish :: suffix)) =
      some (workConfigAtWord CNFWorkState.widthRestoreFormula
        (cnfFinish :: leftSide) suffix) := by
  rfl

theorem widthRestoreSeekCounter_run
    (outerCounter headerTail : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine (outerCounter.length + 1)
        (workConfigAtWord CNFWorkState.widthRestoreSeekFormula
          [cnfRootGuard]
          (outerCounter ++ cnfFinish :: headerTail)) =
      some (workConfigAtWord CNFWorkState.widthRestoreFormula
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
        headerTail) := by
  have hCounter := widthRestoreSeekFormula_counter_scan outerCounter
    (cnfFinish :: headerTail) [cnfRootGuard] outerAllowed
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthRestoreSeekFormula_finish_step
      (pushWorkLeft outerCounter [cnfRootGuard]) headerTail)
  exact workRunExact?_compose cnfWorkMachine outerCounter.length 1
    _ _ _ hCounter hFinish

def widthTerminalPhysical (outerCounter : List WorkSymbol)
    (count : Nat) (formulaTail : List WorkSymbol) : List WorkSymbol :=
  outerCounter ++
    cnfFinish ::
      (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail)

theorem widthTerminalPhysical_push (outerCounter : List WorkSymbol)
    (count : Nat) (formulaTail : List WorkSymbol) :
    pushWorkLeft formulaTail
        (cnfF ::
          pushWorkLeft (List.replicate count cnfMarkTrue)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) =
      pushWorkLeft (widthTerminalPhysical outerCounter count formulaTail) [] ++
        [cnfRootGuard] := by
  calc
    pushWorkLeft formulaTail
        (cnfF ::
          pushWorkLeft (List.replicate count cnfMarkTrue)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) =
      pushWorkLeft (cnfF :: formulaTail)
        (pushWorkLeft (List.replicate count cnfMarkTrue)
          (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])) := rfl
    _ = pushWorkLeft
        (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail)
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]) :=
      (pushWorkLeft_append_word (List.replicate count cnfMarkTrue)
        (cnfF :: formulaTail)
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])).symm
    _ = pushWorkLeft
        (cnfFinish ::
          (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail))
        (pushWorkLeft outerCounter [cnfRootGuard]) := rfl
    _ = pushWorkLeft
        (outerCounter ++
          cnfFinish ::
            (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail))
        [cnfRootGuard] :=
      (pushWorkLeft_append_word outerCounter
        (cnfFinish ::
          (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail))
        [cnfRootGuard]).symm
    _ = pushWorkLeft
        (widthTerminalPhysical outerCounter count formulaTail) [] ++
          [cnfRootGuard] := by
      unfold widthTerminalPhysical
      rw [pushWorkLeft_append_far]

theorem widthTerminalPhysical_allowed
    (outerCounter : List WorkSymbol) (count : Nat)
    (formulaTail : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (symbol : WorkSymbol)
    (member : List.Mem symbol
      (widthTerminalPhysical outerCounter count formulaTail)) :
    FormulaOrCounterSymbol symbol := by
  unfold widthTerminalPhysical at member
  apply allowed_append FormulaOrCounterSymbol outerCounter
    (cnfFinish ::
      (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail))
  · intro candidate inOuter
    have equal := outerAllowed candidate inOuter
    cases equal
    exact .markFalse
  · intro candidate inTail
    cases inTail with
    | head => exact .finish
    | tail _ inHeaderFormula =>
        apply allowed_append FormulaOrCounterSymbol
          (List.replicate count cnfMarkTrue) (cnfF :: formulaTail)
        · intro headerSymbol headerMember
          have equal := FrameTraceDesign.mem_replicate_workSymbol_eq
            count cnfMarkTrue headerSymbol headerMember
          cases equal
          exact .markTrue
        · intro tailSymbol tailMember
          cases tailMember with
          | head => exact .f
          | tail _ inFormula =>
              exact formulaScan_to_formulaOrCounter tailSymbol
                (formulaAllowed tailSymbol inFormula)
        · exact inHeaderFormula
  · exact member

def widthTerminalSteps (outerCounter counter : List WorkSymbol)
    (count : Nat) (formulaTail : List WorkSymbol)
    (assignment : BitString) : Nat :=
  let doneSteps :=
    (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)
  let restoreCounterSteps := (1 + counter.length) + 1
  let physicalSteps :=
    (widthTerminalPhysical outerCounter count formulaTail).length + 1
  let seekSteps := outerCounter.length + 1
  ((((1 + doneSteps) + restoreCounterSteps) + physicalSteps) + seekSteps) +
    (count + 1)

theorem widthTerminal_success_exact
    (outerCounter counter formulaTail : List WorkSymbol)
    (count : Nat) (assignment : BitString) (suffix : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (widthTerminalSteps outerCounter counter count formulaTail assignment)
        (workConfigAtWord CNFWorkState.widthFindFormula
          (pushWorkLeft (List.replicate count cnfMarkTrue)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
          (cnfF ::
            (formulaTail ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols assignment ++
                      cnfRootGuard :: suffix))))))) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfF ::
          pushWorkLeft (List.replicate count cnfT)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
        (formulaTail ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  cnfRootGuard :: suffix)))))) := by
  let returnTail := cnfBoundaryGuard ::
    (counter ++
      (cnfFinish ::
        (assignmentWorkSymbols assignment ++ cnfRootGuard :: suffix)))
  let leftBase :=
    pushWorkLeft (List.replicate count cnfMarkTrue)
      (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
  have hDone := workRunExact?_one_of_step cnfWorkMachine _ _
    (widthFindFormula_done_step leftBase
      (formulaTail ++
        (cnfBoundaryGuard ::
          (counter ++
            (cnfFinish ::
              (markedAssignmentWorkSymbols assignment ++
                cnfRootGuard :: suffix))))))
  have hEqual := width_equal_assignment_restored formulaTail counter
    (cnfF :: leftBase) suffix assignment formulaAllowed counterAllowed
  have throughEqual := workRunExact?_compose cnfWorkMachine 1
    (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)
    _ _ _ hDone hEqual
  have hCounter := widthRestoreCounter_run counter
    (pushWorkLeft formulaTail (cnfF :: leftBase))
    (assignmentWorkSymbols assignment ++ cnfRootGuard :: suffix)
    counterAllowed
  have throughCounter := workRunExact?_compose cnfWorkMachine
    (1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length))
    ((1 + counter.length) + 1) _ _ _ throughEqual hCounter
  rw [widthTerminalPhysical_push] at throughCounter
  have physicalAllowed := widthTerminalPhysical_allowed outerCounter count
    formulaTail outerAllowed formulaAllowed
  have hPhysical := widthRestorePhysical_run
    (widthTerminalPhysical outerCounter count formulaTail) returnTail
    physicalAllowed
  have throughPhysical := workRunExact?_compose cnfWorkMachine
    ((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1))
    ((widthTerminalPhysical outerCounter count formulaTail).length + 1)
    _ _ _ throughCounter hPhysical
  have physicalSplit :
      widthTerminalPhysical outerCounter count formulaTail ++ returnTail =
        outerCounter ++
          (cnfFinish ::
            ((List.replicate count cnfMarkTrue ++ cnfF :: formulaTail) ++
              returnTail)) := by
    unfold widthTerminalPhysical
    exact workSymbol_append_assoc outerCounter
      (cnfFinish ::
        (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail))
      returnTail
  rw [physicalSplit] at throughPhysical
  have hSeek := widthRestoreSeekCounter_run outerCounter
    ((List.replicate count cnfMarkTrue ++ cnfF :: formulaTail) ++ returnTail)
    outerAllowed
  have throughSeek := workRunExact?_compose cnfWorkMachine
    (((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1)) +
      ((widthTerminalPhysical outerCounter count formulaTail).length + 1))
    (outerCounter.length + 1) _ _ _ throughPhysical hSeek
  have headerSplit :
      (List.replicate count cnfMarkTrue ++ cnfF :: formulaTail) ++
          returnTail =
        List.replicate count cnfMarkTrue ++
          cnfF :: (formulaTail ++ returnTail) := by
    exact workSymbol_append_assoc (List.replicate count cnfMarkTrue)
      (cnfF :: formulaTail) returnTail
  rw [headerSplit] at throughSeek
  have hHeader := widthRestoreFormula_header count
    (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
    (formulaTail ++ returnTail)
  have complete := workRunExact?_compose cnfWorkMachine
    ((((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1)) +
      ((widthTerminalPhysical outerCounter count formulaTail).length + 1)) +
      (outerCounter.length + 1))
    (count + 1) _ _ _ throughSeek hHeader
  unfold widthTerminalSteps
  unfold leftBase at complete
  unfold returnTail at complete
  exact complete

def widthLoopStepCount (outerCounter counter formulaTail : List WorkSymbol) :
    BitString → BitString → Nat
  | processed, [] =>
      widthTerminalSteps outerCounter counter processed.length formulaTail
        processed
  | processed, _value :: rest =>
      widthOneUnitSteps outerCounter
          (List.replicate processed.length cnfMarkTrue)
          (List.replicate rest.length cnfT ++ cnfF :: formulaTail)
          counter (markedAssignmentWorkSymbols processed) +
        widthLoopStepCount outerCounter counter formulaTail
          (processed ++ [_value]) rest

theorem widthLoop_success_exact
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (suffix : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol) :
    workRunExact? cnfWorkMachine
        (widthLoopStepCount outerCounter counter formulaTail
          processed remaining)
        (workConfigAtWord CNFWorkState.widthFindFormula
          (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
          ((List.replicate remaining.length cnfT ++
              cnfF :: formulaTail) ++
            (cnfBoundaryGuard ::
              (counter ++
                (cnfFinish ::
                  (markedAssignmentWorkSymbols processed ++
                    (assignmentWorkSymbols remaining ++
                      cnfRootGuard :: suffix))))))) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfF ::
          pushWorkLeft
            (List.replicate (processed.length + remaining.length) cnfT)
            (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
        (formulaTail ++
          (cnfBoundaryGuard ::
            (counter ++
              (cnfFinish ::
                (assignmentWorkSymbols (processed ++ remaining) ++
                  cnfRootGuard :: suffix)))))) := by
  induction remaining generalizing processed with
  | nil =>
      unfold widthLoopStepCount
      rw [BitString.append_nil_constructive]
      change workRunExact? cnfWorkMachine
          (widthTerminalSteps outerCounter counter processed.length
            formulaTail processed)
          (workConfigAtWord CNFWorkState.widthFindFormula
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            (cnfF ::
              (formulaTail ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols processed ++
                        cnfRootGuard :: suffix))))))) = _
      exact widthTerminal_success_exact outerCounter counter formulaTail
        processed.length processed suffix outerAllowed counterAllowed
        formulaAllowed
  | cons value rest ih =>
      let nextFormulaTail :=
        List.replicate rest.length cnfT ++ cnfF :: formulaTail
      have nextFormulaAllowed : ∀ symbol,
          List.Mem symbol nextFormulaTail → FormulaScanSymbol symbol := by
        intro symbol member
        exact oobFormulaTail_allowed rest.length formulaTail formulaAllowed
          symbol member
      have headerAllowed : ∀ symbol,
          List.Mem symbol (List.replicate processed.length cnfMarkTrue) →
            symbol = cnfMarkTrue := by
        intro symbol member
        exact FrameTraceDesign.mem_replicate_workSymbol_eq
          processed.length cnfMarkTrue symbol member
      have hUnit := widthOneUnit_run outerCounter
        (List.replicate processed.length cnfMarkTrue) nextFormulaTail
        counter (markedAssignmentWorkSymbols processed)
        (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix) value
        outerAllowed headerAllowed
        nextFormulaAllowed counterAllowed
        (markedAssignmentWorkSymbols_allowed processed)
      have hRest := ih (processed ++ [value])
      rw [length_append_value] at hRest
      rw [FrameTraceDesign.replicate_succ_tail] at hRest
      rw [markedAssignment_append_value_tail processed value
        (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix)] at hRest
      have markedValueShape :
          FrameTraceDesign.markedAssignmentValueWorkSymbol value =
            if value then cnfMarkTrue else cnfMarkFalse := by
        cases value <;> rfl
      rw [markedValueShape] at hRest
      have complete := workRunExact?_compose cnfWorkMachine
        (widthOneUnitSteps outerCounter
          (List.replicate processed.length cnfMarkTrue) nextFormulaTail
          counter (markedAssignmentWorkSymbols processed))
        (widthLoopStepCount outerCounter counter formulaTail
          (processed ++ [value]) rest)
        _ _ _ hUnit hRest
      unfold widthLoopStepCount
      unfold nextFormulaTail at complete
      rw [FrameTraceDesign.replicate_bit_cons_length]
      rw [FrameTraceDesign.assignmentWorkSymbols_cons]
      rw [assignmentValueWorkSymbol_eq_if]
      rw [assignment_append_value_tail processed value rest]
      rw [List.length_cons]
      rw [Nat.add_succ]
      rw [Nat.succ_add] at complete
      exact complete

theorem seekLeftRoot_formulaOrCounter_step
    (head : WorkSymbol) (leftTail rightSide : List WorkSymbol)
    (allowed : FormulaOrCounterSymbol head) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (head :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.seekLeftRoot
        leftTail (head :: rightSide)) := by
  cases allowed <;> rfl

theorem seekLeftRoot_scan
    (word leftSuffix rightSide : List WorkSymbol)
    (allowed : ∀ symbol, List.Mem symbol word →
      FormulaOrCounterSymbol symbol) :
    workRunExact? cnfWorkMachine word.length
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (word ++ leftSuffix) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.seekLeftRoot
        leftSuffix (pushWorkLeft word rightSide)) := by
  exact workRunExact?_scanLeft cnfWorkMachine CNFWorkState.seekLeftRoot
    FormulaOrCounterSymbol seekLeftRoot_formulaOrCounter_step
    word leftSuffix rightSide allowed

theorem seekLeftRoot_boundary_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (cnfBoundaryGuard :: leftTail) rightSide) =
      some (workConfigAtLeftWord CNFWorkState.seekLeftRoot
        leftTail (cnfBoundaryGuard :: rightSide)) := by
  rfl

theorem seekLeftRoot_root_step
    (leftTail rightSide : List WorkSymbol) :
    workStep? cnfWorkMachine
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (cnfRootGuard :: leftTail) rightSide) =
      some (workConfigAtWord CNFWorkState.seekFormulaStart
        (cnfRootGuard :: leftTail) rightSide) := by
  cases rightSide <;> rfl

def widthSeekPreludeSteps (outerCounter formulaWord counter :
    List WorkSymbol) : Nat :=
  ((((((counter.length + 1) + formulaWord.length) + 1) +
    outerCounter.length) + 1) + outerCounter.length) + 1

theorem widthSeekPrelude_exact
    (outerCounter formulaWord counter rightSide : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaWord →
      FormulaScanSymbol symbol)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse) :
    workRunExact? cnfWorkMachine
        (widthSeekPreludeSteps outerCounter formulaWord counter)
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft counter
            (cnfBoundaryGuard ::
              pushWorkLeft formulaWord
                (cnfFinish ::
                  pushWorkLeft outerCounter [cnfRootGuard])))
          rightSide) =
      some (workConfigAtWord CNFWorkState.widthFindFormula
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
        (formulaWord ++
          (cnfBoundaryGuard :: (counter ++ rightSide)))) := by
  have reversedCounterAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft counter []) →
        FormulaOrCounterSymbol symbol := by
    intro symbol member
    have equal := pushWorkLeft_allowed
      (fun candidate => candidate = cnfMarkFalse) counter []
      counterAllowed (by intro candidate impossible; contradiction)
      symbol member
    cases equal
    exact .markFalse
  have hCounter := seekLeftRoot_scan (pushWorkLeft counter [])
    (cnfBoundaryGuard ::
      pushWorkLeft formulaWord
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
    rightSide reversedCounterAllowed
  have counterLength : (pushWorkLeft counter []).length = counter.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero counter.length
  rw [counterLength] at hCounter
  rw [pushWorkLeft_cancel] at hCounter
  have hBoundary := workRunExact?_one_of_step cnfWorkMachine _ _
    (seekLeftRoot_boundary_step
      (pushWorkLeft formulaWord
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
      (counter ++ rightSide))
  have throughBoundary := workRunExact?_compose cnfWorkMachine
    counter.length 1 _ _ _ hCounter hBoundary
  have reversedFormulaAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft formulaWord []) →
        FormulaOrCounterSymbol symbol := by
    intro symbol member
    have allowed := pushWorkLeft_allowed FormulaScanSymbol formulaWord []
      formulaAllowed (by intro candidate impossible; contradiction)
      symbol member
    exact formulaScan_to_formulaOrCounter symbol allowed
  have hFormula := seekLeftRoot_scan (pushWorkLeft formulaWord [])
    (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
    (cnfBoundaryGuard :: counter ++ rightSide) reversedFormulaAllowed
  have formulaLength :
      (pushWorkLeft formulaWord []).length = formulaWord.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero formulaWord.length
  rw [formulaLength] at hFormula
  rw [pushWorkLeft_append_far formulaWord
    (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])]
    at throughBoundary
  have throughFormula := workRunExact?_compose cnfWorkMachine
    (counter.length + 1) formulaWord.length _ _ _
    throughBoundary hFormula
  rw [pushWorkLeft_cancel] at throughFormula
  have hFinish := workRunExact?_one_of_step cnfWorkMachine _ _
    (seekLeftRoot_formulaOrCounter_step cnfFinish
      (pushWorkLeft outerCounter [cnfRootGuard])
      (formulaWord ++ (cnfBoundaryGuard :: (counter ++ rightSide)))
      .finish)
  have throughFinish := workRunExact?_compose cnfWorkMachine
    ((counter.length + 1) + formulaWord.length) 1
    _ _ _ throughFormula hFinish
  have reversedOuterAllowed : ∀ symbol,
      List.Mem symbol (pushWorkLeft outerCounter []) →
        FormulaOrCounterSymbol symbol := by
    intro symbol member
    have equal := pushWorkLeft_allowed
      (fun candidate => candidate = cnfMarkFalse) outerCounter []
      outerAllowed (by intro candidate impossible; contradiction)
      symbol member
    cases equal
    exact .markFalse
  have hOuterLeft := seekLeftRoot_scan (pushWorkLeft outerCounter [])
    [cnfRootGuard]
    (cnfFinish ::
      (formulaWord ++ (cnfBoundaryGuard :: (counter ++ rightSide))))
    reversedOuterAllowed
  have outerLength :
      (pushWorkLeft outerCounter []).length = outerCounter.length := by
    rw [pushWorkLeft_length]
    exact Nat.add_zero outerCounter.length
  rw [outerLength] at hOuterLeft
  rw [pushWorkLeft_append_far outerCounter [cnfRootGuard]] at throughFinish
  have throughOuterLeft := workRunExact?_compose cnfWorkMachine
    (((counter.length + 1) + formulaWord.length) + 1)
    outerCounter.length _ _ _ throughFinish hOuterLeft
  rw [pushWorkLeft_cancel] at throughOuterLeft
  have hRoot := workRunExact?_one_of_step cnfWorkMachine _ _
    (seekLeftRoot_root_step []
      (outerCounter ++
        (cnfFinish ::
          (formulaWord ++
            (cnfBoundaryGuard :: (counter ++ rightSide))))))
  have throughRoot := workRunExact?_compose cnfWorkMachine
    ((((counter.length + 1) + formulaWord.length) + 1) +
      outerCounter.length) 1 _ _ _ throughOuterLeft hRoot
  have hOuterRight := seekFormulaStart_counter_scan outerCounter
    (cnfFinish ::
      (formulaWord ++ (cnfBoundaryGuard :: (counter ++ rightSide))))
    [cnfRootGuard] outerAllowed
  have throughOuterRight := workRunExact?_compose cnfWorkMachine
    (((((counter.length + 1) + formulaWord.length) + 1) +
      outerCounter.length) + 1) outerCounter.length
    _ _ _ throughRoot hOuterRight
  have hStart := workRunExact?_one_of_step cnfWorkMachine _ _
    (seekFormulaStart_finish_step
      (pushWorkLeft outerCounter [cnfRootGuard])
      (formulaWord ++ (cnfBoundaryGuard :: (counter ++ rightSide))))
  have complete := workRunExact?_compose cnfWorkMachine
    ((((((counter.length + 1) + formulaWord.length) + 1) +
      outerCounter.length) + 1) + outerCounter.length) 1
    _ _ _ throughOuterRight hStart
  unfold widthSeekPreludeSteps
  rw [← pushWorkLeft_append_far outerCounter [cnfRootGuard]] at complete
  rw [← pushWorkLeft_append_far formulaWord
    (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])] at complete
  rw [← pushWorkLeft_append_far counter
    (cnfBoundaryGuard ::
      pushWorkLeft formulaWord
        (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))] at complete
  exact complete

theorem widthCost_add_scaled (span left right leftUnits rightUnits : Nat)
    (leftBound : left ≤ span * leftUnits)
    (rightBound : right ≤ span * rightUnits) :
    left + right ≤ span * (leftUnits + rightUnits) := by
  have combined := Nat.add_le_add leftBound rightBound
  exact Nat.le_trans combined
    (Nat.le_of_eq (Nat.mul_add span leftUnits rightUnits).symm)

theorem widthCost_promote_scaled (span value small large : Nat)
    (valueBound : value ≤ span * small) (coefficientBound : small ≤ large) :
    value ≤ span * large := by
  exact Nat.le_trans valueBound
    (Nat.mul_le_mul_left span coefficientBound)

theorem widthOne_le_shiftedSpan (n : Nat) :
    1 ≤ cnfShiftedWorkSpan n := by
  unfold cnfShiftedWorkSpan
  change Nat.succ 0 ≤ Nat.succ (Nat.succ n)
  exact Nat.succ_le_succ (Nat.zero_le (Nat.succ n))

theorem widthLength_le_shiftedSpan (n length : Nat)
    (lengthBound : length ≤ n) :
    length ≤ cnfShiftedWorkSpan n := by
  exact Nat.le_trans lengthBound (by
    unfold cnfShiftedWorkSpan
    exact Nat.le_add_right n 2)

theorem widthLengthSucc_le_shiftedSpan (n length : Nat)
    (lengthBound : length ≤ n) :
    length + 1 ≤ cnfShiftedWorkSpan n := by
  unfold cnfShiftedWorkSpan
  exact Nat.add_le_add lengthBound (Nat.le_succ 1)

theorem widthDoneEndpointSteps_le_fourSpan (n formulaLength counterLength
    assignmentLength : Nat)
    (formulaBound : formulaLength ≤ n)
    (counterBound : counterLength ≤ n)
    (assignmentBound : assignmentLength ≤ n) :
    (((((formulaLength + 1) + counterLength + 1) +
      assignmentLength) + 1) + assignmentLength) ≤
      cnfShiftedWorkSpan n * 4 := by
  have formulaPiece := widthLengthSucc_le_shiftedSpan n formulaLength
    formulaBound
  have counterPiece := widthLengthSucc_le_shiftedSpan n counterLength
    counterBound
  have assignmentPiece := widthLengthSucc_le_shiftedSpan n assignmentLength
    assignmentBound
  have assignmentPlain := widthLength_le_shiftedSpan n assignmentLength
    assignmentBound
  have firstPair := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (formulaLength + 1) (counterLength + 1) 1 1
    (by rw [Nat.mul_one]; exact formulaPiece)
    (by rw [Nat.mul_one]; exact counterPiece)
  have firstThree := widthCost_add_scaled (cnfShiftedWorkSpan n)
    ((formulaLength + 1) + (counterLength + 1))
    (assignmentLength + 1) (1 + 1) 1 firstPair
    (by rw [Nat.mul_one]; exact assignmentPiece)
  have allFour := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (((formulaLength + 1) + (counterLength + 1)) +
      (assignmentLength + 1)) assignmentLength
    ((1 + 1) + 1) 1 firstThree
    (by rw [Nat.mul_one]; exact assignmentPlain)
  rw [Nat.add_assoc (formulaLength + 1) counterLength 1]
  rw [Nat.add_assoc
    ((formulaLength + 1) + (counterLength + 1)) assignmentLength 1]
  exact allFour

theorem widthRestoreCounterSteps_le_span (n counterLength : Nat)
    (counterBound : counterLength ≤ n) :
    (1 + counterLength) + 1 ≤ cnfShiftedWorkSpan n := by
  have first := Nat.add_le_add (Nat.le_refl 1) counterBound
  have complete := Nat.add_le_add first (Nat.le_refl 1)
  unfold cnfShiftedWorkSpan
  rw [Nat.add_comm 1 n] at complete
  exact complete

theorem width_add_three_succ_reorder (a b c : Nat) :
    a + ((b + (c + 1)) + 1) + 1 =
      ((a + 1) + (b + 1)) + (c + 1) := by
  calc
    a + ((b + (c + 1)) + 1) + 1 =
        (a + b) + ((c + 1) + (1 + 1)) := by
      rw [Nat.add_assoc b (c + 1) 1]
      rw [← Nat.add_assoc a b ((c + 1) + 1)]
      rw [Nat.add_assoc (a + b) ((c + 1) + 1) 1]
    _ = ((a + 1) + (b + 1)) + (c + 1) := by
      rw [FrameTraceDesign.frame_add_four_reorder a 1 b 1]
      rw [Nat.add_assoc (a + b) (1 + 1) (c + 1)]
      rw [Nat.add_comm (1 + 1) (c + 1)]

theorem widthTerminalPhysicalSteps_le_threeSpan (n count : Nat)
    (outerCounter formulaTail : List WorkSymbol)
    (outerBound : outerCounter.length ≤ n)
    (countBound : count ≤ n)
    (formulaBound : formulaTail.length ≤ n) :
    (widthTerminalPhysical outerCounter count formulaTail).length + 1 ≤
      cnfShiftedWorkSpan n * 3 := by
  have outerPiece := widthLengthSucc_le_shiftedSpan n outerCounter.length
    outerBound
  have countPiece := widthLengthSucc_le_shiftedSpan n count countBound
  have formulaPiece := widthLengthSucc_le_shiftedSpan n formulaTail.length
    formulaBound
  have firstPair := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (outerCounter.length + 1) (count + 1) 1 1
    (by rw [Nat.mul_one]; exact outerPiece)
    (by rw [Nat.mul_one]; exact countPiece)
  have allThree := widthCost_add_scaled (cnfShiftedWorkSpan n)
    ((outerCounter.length + 1) + (count + 1))
    (formulaTail.length + 1) (1 + 1) 1 firstPair
    (by rw [Nat.mul_one]; exact formulaPiece)
  unfold widthTerminalPhysical
  rw [workSymbol_length_append]
  change outerCounter.length +
      ((List.replicate count cnfMarkTrue ++
        cnfF :: formulaTail).length + 1) + 1 ≤ _
  rw [workSymbol_length_append]
  rw [workSymbol_replicate_length]
  change outerCounter.length +
      ((count + (formulaTail.length + 1)) + 1) + 1 ≤ _
  rw [width_add_three_succ_reorder]
  exact allThree

theorem widthSeekPreludeSteps_le_fourSpan (n : Nat)
    (outerCounter formulaWord counter : List WorkSymbol)
    (outerBound : outerCounter.length ≤ n)
    (formulaBound : formulaWord.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthSeekPreludeSteps outerCounter formulaWord counter ≤
      cnfShiftedWorkSpan n * 4 := by
  have counterPiece := widthLengthSucc_le_shiftedSpan n counter.length
    counterBound
  have formulaPiece := widthLengthSucc_le_shiftedSpan n formulaWord.length
    formulaBound
  have outerPiece := widthLengthSucc_le_shiftedSpan n outerCounter.length
    outerBound
  have firstPair := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (counter.length + 1) (formulaWord.length + 1) 1 1
    (by rw [Nat.mul_one]; exact counterPiece)
    (by rw [Nat.mul_one]; exact formulaPiece)
  have firstThree := widthCost_add_scaled (cnfShiftedWorkSpan n)
    ((counter.length + 1) + (formulaWord.length + 1))
    (outerCounter.length + 1) (1 + 1) 1 firstPair
    (by rw [Nat.mul_one]; exact outerPiece)
  have allFour := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (((counter.length + 1) + (formulaWord.length + 1)) +
      (outerCounter.length + 1))
    (outerCounter.length + 1) ((1 + 1) + 1) 1 firstThree
    (by rw [Nat.mul_one]; exact outerPiece)
  unfold widthSeekPreludeSteps
  rw [Nat.add_assoc (counter.length + 1) formulaWord.length 1]
  rw [Nat.add_assoc
    ((counter.length + 1) + (formulaWord.length + 1))
    outerCounter.length 1]
  rw [Nat.add_assoc
    (((counter.length + 1) + (formulaWord.length + 1)) +
      (outerCounter.length + 1)) outerCounter.length 1]
  exact allFour

theorem widthTerminalSteps_le_twelveSpan (n count : Nat)
    (outerCounter counter formulaTail : List WorkSymbol)
    (assignment : BitString)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n)
    (countBound : count ≤ n)
    (formulaBound : formulaTail.length ≤ n)
    (assignmentBound : assignment.length ≤ n) :
    widthTerminalSteps outerCounter counter count formulaTail assignment ≤
      cnfShiftedWorkSpan n * 12 := by
  let span := cnfShiftedWorkSpan n
  have onePiece : 1 ≤ span * 1 := by
    rw [Nat.mul_one]
    exact widthOne_le_shiftedSpan n
  have donePiece :
      (((((formulaTail.length + 1) + counter.length + 1) +
        assignment.length) + 1) + assignment.length) ≤ span * 4 :=
    widthDoneEndpointSteps_le_fourSpan n formulaTail.length counter.length
      assignment.length formulaBound counterBound assignmentBound
  have restoreRaw := widthRestoreCounterSteps_le_span n counter.length
    counterBound
  have restorePiece : (1 + counter.length) + 1 ≤ span * 1 := by
    rw [Nat.mul_one]
    exact restoreRaw
  have physicalPiece := widthTerminalPhysicalSteps_le_threeSpan n count
    outerCounter formulaTail outerBound countBound formulaBound
  have seekRaw := widthLengthSucc_le_shiftedSpan n outerCounter.length
    outerBound
  have seekPiece : outerCounter.length + 1 ≤ span * 1 := by
    rw [Nat.mul_one]
    exact seekRaw
  have countRaw := widthLengthSucc_le_shiftedSpan n count countBound
  have countPiece : count + 1 ≤ span * 1 := by
    rw [Nat.mul_one]
    exact countRaw
  have throughDone := widthCost_add_scaled span 1
    (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)
    1 4 onePiece donePiece
  have throughRestore := widthCost_add_scaled span
    (1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length))
    ((1 + counter.length) + 1) (1 + 4) 1 throughDone restorePiece
  have throughPhysical := widthCost_add_scaled span
    ((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1))
    ((widthTerminalPhysical outerCounter count formulaTail).length + 1)
    ((1 + 4) + 1) 3 throughRestore physicalPiece
  have throughSeek := widthCost_add_scaled span
    (((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1)) +
      ((widthTerminalPhysical outerCounter count formulaTail).length + 1))
    (outerCounter.length + 1) (((1 + 4) + 1) + 3) 1
    throughPhysical seekPiece
  have complete := widthCost_add_scaled span
    ((((1 + (((((formulaTail.length + 1) + counter.length + 1) +
      assignment.length) + 1) + assignment.length)) +
      ((1 + counter.length) + 1)) +
      ((widthTerminalPhysical outerCounter count formulaTail).length + 1)) +
      (outerCounter.length + 1))
    (count + 1) ((((1 + 4) + 1) + 3) + 1) 1
    throughSeek countPiece
  apply widthCost_promote_scaled span
    (widthTerminalSteps outerCounter counter count formulaTail assignment)
    (((((1 + 4) + 1) + 3) + 1) + 1) 12
  · unfold widthTerminalSteps
    exact complete
  · change 11 ≤ 11 + 1
    exact Nat.le_add_right 11 1

theorem widthOneUnitSteps_le_twelveSpan (n : Nat)
    (outerCounter headerPrefix formulaTail counter markedAssignment :
      List WorkSymbol)
    (formulaPartition :
      headerPrefix.length + 1 + formulaTail.length ≤ outerCounter.length)
    (assignmentPrefix : markedAssignment.length ≤ counter.length)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthOneUnitSteps outerCounter headerPrefix formulaTail counter
        markedAssignment ≤ cnfShiftedWorkSpan n * 12 := by
  have eightBound := widthOneUnitSteps_le_eightSpan n outerCounter
    headerPrefix formulaTail counter markedAssignment formulaPartition
    assignmentPrefix outerBound counterBound
  apply widthCost_promote_scaled (cnfShiftedWorkSpan n)
    (widthOneUnitSteps outerCounter headerPrefix formulaTail counter
      markedAssignment) 8 12 eightBound
  change 8 ≤ 8 + 4
  exact Nat.le_add_right 8 4

theorem width_add_succ_swap (left right : Nat) :
    left + (right + 1) = (left + 1) + right := by
  calc
    left + (right + 1) = left + (1 + right) :=
      congrArg (Nat.add left) (Nat.add_comm right 1)
    _ = (left + 1) + right := (Nat.add_assoc left 1 right).symm

theorem width_formula_cons_reorder (processed rest tail : Nat) :
    (processed + (rest + 1) + 1) + tail =
      (processed + 1) + (rest + (tail + 1)) := by
  rw [width_add_succ_swap processed rest]
  rw [Nat.add_assoc (processed + 1) rest 1]
  rw [Nat.add_assoc (processed + 1) (rest + 1) tail]
  rw [Nat.add_assoc rest 1 tail]
  rw [Nat.add_comm 1 tail]

theorem widthCharge_plus_successor_mul (index charge : Nat) :
    charge + (index + 1) * charge =
      (Nat.succ index + 1) * charge := by
  change charge + Nat.succ index * charge =
    Nat.succ (Nat.succ index) * charge
  calc
    charge + Nat.succ index * charge =
        charge + (index * charge + charge) :=
      congrArg (Nat.add charge) (Nat.succ_mul index charge)
    _ = (index * charge + charge) + charge := by
      rw [← Nat.add_assoc]
      rw [Nat.add_comm charge (index * charge)]
    _ = Nat.succ index * charge + charge :=
      congrArg (fun value => value + charge)
        (Nat.succ_mul index charge).symm
    _ = Nat.succ (Nat.succ index) * charge :=
      (Nat.succ_mul (Nat.succ index) charge).symm

theorem widthLoopStepCount_le_charges (n : Nat)
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString)
    (formulaPartition :
      (processed.length + remaining.length + 1) + formulaTail.length ≤
        outerCounter.length)
    (assignmentPartition :
      processed.length + remaining.length ≤ counter.length)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthLoopStepCount outerCounter counter formulaTail processed remaining ≤
      (remaining.length + 1) * (cnfShiftedWorkSpan n * 12) := by
  induction remaining generalizing processed with
  | nil =>
      have processedToCounter : processed.length ≤ counter.length := by
        change processed.length + 0 ≤ counter.length at assignmentPartition
        exact assignmentPartition
      have processedBound := Nat.le_trans processedToCounter counterBound
      have formulaToOuter : formulaTail.length ≤ outerCounter.length :=
        Nat.le_trans
          (Nat.le_add_left formulaTail.length
            (processed.length + [].length + 1))
          formulaPartition
      have formulaBound := Nat.le_trans formulaToOuter outerBound
      have terminalBound := widthTerminalSteps_le_twelveSpan n
        processed.length outerCounter counter formulaTail processed outerBound
        counterBound processedBound formulaBound processedBound
      unfold widthLoopStepCount
      exact Nat.le_trans terminalBound
        (Nat.le_of_eq (Nat.one_mul (cnfShiftedWorkSpan n * 12)).symm)
  | cons value rest ih =>
      let nextFormulaTail :=
        List.replicate rest.length cnfT ++ cnfF :: formulaTail
      have unitFormulaPartition :
          (List.replicate processed.length cnfMarkTrue).length + 1 +
              nextFormulaTail.length ≤ outerCounter.length := by
        unfold nextFormulaTail
        rw [workSymbol_replicate_length]
        rw [workSymbol_length_append]
        rw [workSymbol_replicate_length]
        change (processed.length + 1) +
            (rest.length + (formulaTail.length + 1)) ≤ outerCounter.length
        rw [← width_formula_cons_reorder]
        exact formulaPartition
      have processedToCounter : processed.length ≤ counter.length :=
        Nat.le_trans
          (Nat.le_add_right processed.length (value :: rest).length)
          assignmentPartition
      have markedToCounter :
          (markedAssignmentWorkSymbols processed).length ≤ counter.length := by
        rw [markedAssignmentWorkSymbols_length]
        exact processedToCounter
      have unitBound := widthOneUnitSteps_le_twelveSpan n outerCounter
        (List.replicate processed.length cnfMarkTrue) nextFormulaTail
        counter (markedAssignmentWorkSymbols processed)
        unitFormulaPartition markedToCounter outerBound counterBound
      have nextFormulaPartition :
          ((processed ++ [value]).length + rest.length + 1) +
              formulaTail.length ≤ outerCounter.length := by
        rw [length_append_value]
        change (((processed.length + 1) + rest.length) + 1) +
            formulaTail.length ≤ outerCounter.length
        rw [← width_add_succ_swap processed.length rest.length]
        exact formulaPartition
      have nextAssignmentPartition :
          (processed ++ [value]).length + rest.length ≤ counter.length := by
        rw [length_append_value]
        change (processed.length + 1) + rest.length ≤ counter.length
        rw [← width_add_succ_swap processed.length rest.length]
        exact assignmentPartition
      have restBound := ih (processed ++ [value]) nextFormulaPartition
        nextAssignmentPartition
      have combined := Nat.add_le_add unitBound restBound
      unfold widthLoopStepCount
      unfold nextFormulaTail at combined
      exact Nat.le_trans combined
        (Nat.le_of_eq
          (widthCharge_plus_successor_mul rest.length
            (cnfShiftedWorkSpan n * 12)))

def widthTerminalRejectSteps
    (formulaTail counter markedAssignment : List WorkSymbol) : Nat :=
  (((formulaTail.length + 1) + counter.length + 1) +
    markedAssignment.length) + 1

def widthMismatchStepCount
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed : BitString) : Nat → BitString → Nat
  | 0, [] => 0
  | 0, _extra :: _rest =>
      1 + widthTerminalRejectSteps formulaTail counter
        (markedAssignmentWorkSymbols processed)
  | Nat.succ count, [] =>
      1 + widthTerminalRejectSteps
        (List.replicate count cnfT ++ cnfF :: formulaTail) counter
        (markedAssignmentWorkSymbols processed)
  | Nat.succ count, value :: rest =>
      widthOneUnitSteps outerCounter
          (List.replicate processed.length cnfMarkTrue)
          (List.replicate count cnfT ++ cnfF :: formulaTail)
          counter (markedAssignmentWorkSymbols processed) +
        widthMismatchStepCount outerCounter counter formulaTail
          (processed ++ [value]) count rest

theorem widthTerminalRejectSteps_le_fourSpan (n : Nat)
    (formulaTail counter markedAssignment : List WorkSymbol)
    (formulaBound : formulaTail.length ≤ n)
    (counterBound : counter.length ≤ n)
    (assignmentBound : markedAssignment.length ≤ n) :
    1 + widthTerminalRejectSteps formulaTail counter markedAssignment ≤
      cnfShiftedWorkSpan n * 4 := by
  have formulaRaw := widthLengthSucc_le_shiftedSpan n formulaTail.length
    formulaBound
  have formulaPiece : formulaTail.length + 1 ≤
      cnfShiftedWorkSpan n * 1 := by
    rw [Nat.mul_one]
    exact formulaRaw
  have counterRaw := widthLengthSucc_le_shiftedSpan n counter.length
    counterBound
  have counterPiece : counter.length + 1 ≤
      cnfShiftedWorkSpan n * 1 := by
    rw [Nat.mul_one]
    exact counterRaw
  have assignmentRaw := widthLengthSucc_le_shiftedSpan n
    markedAssignment.length assignmentBound
  have assignmentPiece : markedAssignment.length + 1 ≤
      cnfShiftedWorkSpan n * 1 := by
    rw [Nat.mul_one]
    exact assignmentRaw
  have onePiece : 1 ≤ cnfShiftedWorkSpan n * 1 := by
    rw [Nat.mul_one]
    exact widthOne_le_shiftedSpan n
  have firstPair := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (formulaTail.length + 1) (counter.length + 1) 1 1
    formulaPiece counterPiece
  have firstThree := widthCost_add_scaled (cnfShiftedWorkSpan n)
    ((formulaTail.length + 1) + (counter.length + 1))
    (markedAssignment.length + 1) (1 + 1) 1 firstPair assignmentPiece
  have allFour := widthCost_add_scaled (cnfShiftedWorkSpan n)
    (((formulaTail.length + 1) + (counter.length + 1)) +
      (markedAssignment.length + 1)) 1 ((1 + 1) + 1) 1
    firstThree onePiece
  unfold widthTerminalRejectSteps
  rw [Nat.add_comm 1
    (((((formulaTail.length + 1) + counter.length + 1) +
      markedAssignment.length) + 1))]
  rw [Nat.add_assoc (formulaTail.length + 1) counter.length 1]
  rw [Nat.add_assoc
    ((formulaTail.length + 1) + (counter.length + 1))
    markedAssignment.length 1]
  exact allFour

theorem widthMismatchStepCount_le_charges (n : Nat)
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (headerCount : Nat)
    (formulaPartition :
      (processed.length + headerCount + 1) + formulaTail.length ≤
        outerCounter.length)
    (assignmentPartition :
      processed.length + remaining.length ≤ counter.length)
    (outerBound : outerCounter.length ≤ n)
    (counterBound : counter.length ≤ n) :
    widthMismatchStepCount outerCounter counter formulaTail processed
        headerCount remaining ≤
      (headerCount + 1) * (cnfShiftedWorkSpan n * 12) := by
  induction headerCount generalizing processed remaining with
  | zero =>
      cases remaining with
      | nil =>
          unfold widthMismatchStepCount
          exact Nat.zero_le (1 * (cnfShiftedWorkSpan n * 12))
      | cons extra rest =>
          have formulaToOuter : formulaTail.length ≤ outerCounter.length :=
            Nat.le_trans
              (Nat.le_add_left formulaTail.length
                (processed.length + 0 + 1))
              formulaPartition
          have formulaBound := Nat.le_trans formulaToOuter outerBound
          have processedToCounter : processed.length ≤ counter.length :=
            Nat.le_trans
              (Nat.le_add_right processed.length (extra :: rest).length)
              assignmentPartition
          have markedBound :
              (markedAssignmentWorkSymbols processed).length ≤ n := by
            rw [markedAssignmentWorkSymbols_length]
            exact Nat.le_trans processedToCounter counterBound
          have rejectBound := widthTerminalRejectSteps_le_fourSpan n
            formulaTail counter (markedAssignmentWorkSymbols processed)
            formulaBound counterBound markedBound
          have rejectCharge := widthCost_promote_scaled
            (cnfShiftedWorkSpan n)
            (1 + widthTerminalRejectSteps formulaTail counter
              (markedAssignmentWorkSymbols processed))
            4 12 rejectBound (by
              change 4 ≤ 4 + 8
              exact Nat.le_add_right 4 8)
          unfold widthMismatchStepCount
          exact Nat.le_trans rejectCharge
            (Nat.le_of_eq (Nat.one_mul
              (cnfShiftedWorkSpan n * 12)).symm)
  | succ count ih =>
      cases remaining with
      | nil =>
          let shortFormulaTail :=
            List.replicate count cnfT ++ cnfF :: formulaTail
          have shortToOuter : shortFormulaTail.length ≤
              outerCounter.length := by
            have withPrefix :
                (processed.length + 1) + shortFormulaTail.length ≤
                  outerCounter.length := by
              unfold shortFormulaTail
              rw [workSymbol_length_append]
              rw [workSymbol_replicate_length]
              change (processed.length + 1) +
                  (count + (formulaTail.length + 1)) ≤
                outerCounter.length
              rw [← width_formula_cons_reorder]
              exact formulaPartition
            exact Nat.le_trans
              (Nat.le_add_left shortFormulaTail.length
                (processed.length + 1)) withPrefix
          have shortBound := Nat.le_trans shortToOuter outerBound
          have processedToCounter : processed.length ≤ counter.length := by
            change processed.length + 0 ≤ counter.length at assignmentPartition
            exact assignmentPartition
          have markedBound :
              (markedAssignmentWorkSymbols processed).length ≤ n := by
            rw [markedAssignmentWorkSymbols_length]
            exact Nat.le_trans processedToCounter counterBound
          have rejectBound := widthTerminalRejectSteps_le_fourSpan n
            shortFormulaTail counter (markedAssignmentWorkSymbols processed)
            shortBound counterBound markedBound
          have rejectCharge := widthCost_promote_scaled
            (cnfShiftedWorkSpan n)
            (1 + widthTerminalRejectSteps shortFormulaTail counter
              (markedAssignmentWorkSymbols processed))
            4 12 rejectBound (by
              change 4 ≤ 4 + 8
              exact Nat.le_add_right 4 8)
          unfold widthMismatchStepCount
          unfold shortFormulaTail at rejectCharge
          exact Nat.le_trans rejectCharge
            (Nat.le_mul_of_pos_left (cnfShiftedWorkSpan n * 12)
              (Nat.zero_lt_succ (Nat.succ count)))
      | cons value rest =>
          let nextFormulaTail :=
            List.replicate count cnfT ++ cnfF :: formulaTail
          have unitFormulaPartition :
              (List.replicate processed.length cnfMarkTrue).length + 1 +
                  nextFormulaTail.length ≤ outerCounter.length := by
            unfold nextFormulaTail
            rw [workSymbol_replicate_length]
            rw [workSymbol_length_append]
            rw [workSymbol_replicate_length]
            change (processed.length + 1) +
                (count + (formulaTail.length + 1)) ≤ outerCounter.length
            rw [← width_formula_cons_reorder]
            exact formulaPartition
          have processedToCounter : processed.length ≤ counter.length :=
            Nat.le_trans
              (Nat.le_add_right processed.length (value :: rest).length)
              assignmentPartition
          have markedToCounter :
              (markedAssignmentWorkSymbols processed).length ≤
                counter.length := by
            rw [markedAssignmentWorkSymbols_length]
            exact processedToCounter
          have unitBound := widthOneUnitSteps_le_twelveSpan n outerCounter
            (List.replicate processed.length cnfMarkTrue) nextFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            unitFormulaPartition markedToCounter outerBound counterBound
          have nextFormulaPartition :
              ((processed ++ [value]).length + count + 1) +
                  formulaTail.length ≤ outerCounter.length := by
            rw [length_append_value]
            change (((processed.length + 1) + count) + 1) +
                formulaTail.length ≤ outerCounter.length
            rw [← width_add_succ_swap processed.length count]
            exact formulaPartition
          have nextAssignmentPartition :
              (processed ++ [value]).length + rest.length ≤
                counter.length := by
            rw [length_append_value]
            change (processed.length + 1) + rest.length ≤ counter.length
            rw [← width_add_succ_swap processed.length rest.length]
            exact assignmentPartition
          have restBound := ih (processed ++ [value]) rest
            nextFormulaPartition nextAssignmentPartition
          have combined := Nat.add_le_add unitBound restBound
          unfold widthMismatchStepCount
          unfold nextFormulaTail at combined
          exact Nat.le_trans combined
            (Nat.le_of_eq
              (widthCharge_plus_successor_mul count
                (cnfShiftedWorkSpan n * 12)))

theorem widthMismatch_exact
    (outerCounter counter formulaTail : List WorkSymbol)
    (processed remaining : BitString) (headerCount : Nat)
    (suffix : List WorkSymbol)
    (outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse)
    (counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse)
    (formulaAllowed : ∀ symbol, List.Mem symbol formulaTail →
      FormulaScanSymbol symbol)
    (different : headerCount ≠ remaining.length) :
    ∃ final,
      workRunExact? cnfWorkMachine
          (widthMismatchStepCount outerCounter counter formulaTail
            processed headerCount remaining)
          (workConfigAtWord CNFWorkState.widthFindFormula
            (pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard]))
            ((List.replicate headerCount cnfT ++ cnfF :: formulaTail) ++
              (cnfBoundaryGuard ::
                (counter ++
                  (cnfFinish ::
                    (markedAssignmentWorkSymbols processed ++
                      (assignmentWorkSymbols remaining ++
                        cnfRootGuard :: suffix))))))) =
        some final ∧
      final.state = CNFWorkState.reject := by
  induction headerCount generalizing processed remaining with
  | zero =>
      cases remaining with
      | nil =>
          exact False.elim (different rfl)
      | cons extra rest =>
          let leftBase :=
            pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
          have hDone := workRunExact?_one_of_step cnfWorkMachine _ _
            (widthFindFormula_done_step leftBase
              (formulaTail ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols processed ++
                        (assignmentWorkSymbols (extra :: rest) ++
                          cnfRootGuard :: suffix)))))))
          have hLong := width_long_assignment_reject formulaTail counter
            (markedAssignmentWorkSymbols processed) (cnfF :: leftBase)
            (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix) extra
            formulaAllowed counterAllowed
            (markedAssignmentWorkSymbols_allowed processed)
          rw [FrameTraceDesign.assignmentWorkSymbols_cons,
            assignmentValueWorkSymbol_eq_if] at hDone
          have complete := workRunExact?_compose cnfWorkMachine 1
            (widthTerminalRejectSteps formulaTail counter
              (markedAssignmentWorkSymbols processed))
            _ _ _ hDone hLong
          refine ⟨workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (markedAssignmentWorkSymbols processed)
              (cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard ::
                  pushWorkLeft formulaTail (cnfF :: leftBase))))
            ((if extra then cnfT else cnfF) ::
              (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix)), ?_, rfl⟩
          unfold widthMismatchStepCount
          unfold widthTerminalRejectSteps at complete ⊢
          unfold leftBase at complete ⊢
          rw [FrameTraceDesign.assignmentWorkSymbols_cons,
            assignmentValueWorkSymbol_eq_if]
          exact complete
  | succ count ih =>
      cases remaining with
      | nil =>
          let leftBase :=
            pushWorkLeft (List.replicate processed.length cnfMarkTrue)
              (cnfFinish :: pushWorkLeft outerCounter [cnfRootGuard])
          let shortFormulaTail :=
            List.replicate count cnfT ++ cnfF :: formulaTail
          have shortFormulaAllowed : ∀ symbol,
              List.Mem symbol shortFormulaTail → FormulaScanSymbol symbol := by
            intro symbol member
            exact oobFormulaTail_allowed count formulaTail formulaAllowed
              symbol member
          have hMark := workRunExact?_one_of_step cnfWorkMachine _ _
            (widthFindFormula_mark_step leftBase
              (shortFormulaTail ++
                (cnfBoundaryGuard ::
                  (counter ++
                    (cnfFinish ::
                      (markedAssignmentWorkSymbols processed ++
                        cnfRootGuard :: suffix))))))
          have hShort := width_short_assignment_reject shortFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            (cnfMarkTrue :: leftBase) suffix shortFormulaAllowed
            counterAllowed (markedAssignmentWorkSymbols_allowed processed)
          have complete := workRunExact?_compose cnfWorkMachine 1
            (widthTerminalRejectSteps shortFormulaTail counter
              (markedAssignmentWorkSymbols processed))
            _ _ _ hMark hShort
          refine ⟨workConfigAtWord CNFWorkState.reject
            (pushWorkLeft (markedAssignmentWorkSymbols processed)
              (cnfFinish :: pushWorkLeft counter
                (cnfBoundaryGuard ::
                  pushWorkLeft shortFormulaTail
                    (cnfMarkTrue :: leftBase))))
            (cnfRootGuard :: suffix), ?_, rfl⟩
          unfold widthMismatchStepCount
          unfold widthTerminalRejectSteps at complete ⊢
          unfold shortFormulaTail leftBase at complete ⊢
          exact complete
      | cons value rest =>
          have restDifferent : count ≠ rest.length := by
            intro equal
            apply different
            rw [List.length_cons, equal]
          let nextFormulaTail :=
            List.replicate count cnfT ++ cnfF :: formulaTail
          have nextFormulaAllowed : ∀ symbol,
              List.Mem symbol nextFormulaTail → FormulaScanSymbol symbol := by
            intro symbol member
            exact oobFormulaTail_allowed count formulaTail formulaAllowed
              symbol member
          have headerAllowed : ∀ symbol,
              List.Mem symbol (List.replicate processed.length cnfMarkTrue) →
                symbol = cnfMarkTrue := by
            intro symbol member
            exact FrameTraceDesign.mem_replicate_workSymbol_eq
              processed.length cnfMarkTrue symbol member
          have hUnit := widthOneUnit_run outerCounter
            (List.replicate processed.length cnfMarkTrue) nextFormulaTail
            counter (markedAssignmentWorkSymbols processed)
            (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix) value
            outerAllowed headerAllowed nextFormulaAllowed counterAllowed
            (markedAssignmentWorkSymbols_allowed processed)
          obtain ⟨final, hRest, finalReject⟩ :=
            ih (processed ++ [value]) rest restDifferent
          rw [length_append_value] at hRest
          rw [FrameTraceDesign.replicate_succ_tail] at hRest
          rw [markedAssignment_append_value_tail processed value
            (assignmentWorkSymbols rest ++ cnfRootGuard :: suffix)] at hRest
          have markedValueShape :
              FrameTraceDesign.markedAssignmentValueWorkSymbol value =
                if value then cnfMarkTrue else cnfMarkFalse := by
            cases value <;> rfl
          rw [markedValueShape] at hRest
          have complete := workRunExact?_compose cnfWorkMachine
            (widthOneUnitSteps outerCounter
              (List.replicate processed.length cnfMarkTrue) nextFormulaTail
              counter (markedAssignmentWorkSymbols processed))
            (widthMismatchStepCount outerCounter counter formulaTail
              (processed ++ [value]) count rest)
            _ _ _ hUnit hRest
          refine ⟨final, ?_, finalReject⟩
          unfold widthMismatchStepCount
          unfold nextFormulaTail at complete
          rw [FrameTraceDesign.assignmentWorkSymbols_cons]
          rw [assignmentValueWorkSymbol_eq_if]
          exact complete

def decodedWidthMismatchSteps (formula : CNFFormula)
    (assignment : BitString) : Nat :=
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter +
    widthMismatchStepCount outerCounter counter
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish]))
      [] formula.variableCount assignment

theorem decodedWidth_unequal_exact
    (formula : CNFFormula) (assignment : BitString)
    (width : formula.variableCount ≠ assignment.length) :
    ∃ final,
      workRunExact? cnfWorkMachine
          (decodedWidthMismatchSteps formula assignment)
          (workConfigAtLeftWord CNFWorkState.seekLeftRoot
            (pushWorkLeft
              (List.replicate assignment.length cnfMarkFalse)
              (cnfBoundaryGuard ::
                frameFormulaLeftBase (encodeFormulaTokens formula)))
            (cnfFinish ::
              (assignmentWorkSymbols assignment ++
                [cnfRootGuard, cnfBlank]))) =
        some final ∧
      final.state = CNFWorkState.reject := by
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  have outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse := by
    intro symbol member
    exact FrameTraceDesign.mem_replicate_workSymbol_eq tokens.length
      cnfMarkFalse symbol member
  have counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse := by
    intro symbol member
    exact FrameTraceDesign.mem_replicate_workSymbol_eq assignment.length
      cnfMarkFalse symbol member
  have formulaAllowed : ∀ symbol,
      List.Mem symbol (cnfTokenWorkSymbols tokens) →
        FormulaScanSymbol symbol := by
    intro symbol member
    exact cnfTokenWorkSymbols_formulaScan tokens symbol member
  have hPrelude := widthSeekPrelude_exact outerCounter
    (cnfTokenWorkSymbols tokens) counter
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++ [cnfRootGuard, cnfBlank]))
    outerAllowed formulaAllowed counterAllowed
  have clauseTailAllowed : ∀ symbol,
      List.Mem symbol
          (cnfTokenWorkSymbols
            (encodeClauseListTokens formula.clauses ++ [.finish])) →
        FormulaScanSymbol symbol := by
    intro symbol member
    exact cnfTokenWorkSymbols_formulaScan
      (encodeClauseListTokens formula.clauses ++ [.finish]) symbol member
  obtain ⟨final, hMismatch, finalReject⟩ :=
    widthMismatch_exact outerCounter counter
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish]))
      [] assignment formula.variableCount [cnfBlank] outerAllowed
      counterAllowed clauseTailAllowed width
  rw [← cnfTokenWorkSymbols_formula_header] at hMismatch
  have emptyLength : ([] : BitString).length = 0 := rfl
  rw [emptyLength] at hMismatch
  have complete := workRunExact?_compose cnfWorkMachine
    (widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter)
    (widthMismatchStepCount outerCounter counter
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish]))
      [] formula.variableCount assignment)
    _ _ _ hPrelude hMismatch
  refine ⟨final, ?_, finalReject⟩
  unfold decodedWidthMismatchSteps
  unfold tokens outerCounter counter at complete
  unfold tokens at complete
  unfold frameFormulaLeftBase
  exact complete

def decodedWidthSuccessSteps (formula : CNFFormula)
    (assignment : BitString) : Nat :=
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter +
    widthLoopStepCount outerCounter counter
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish])) [] assignment

theorem decodedWidth_equal_exact
    (formula : CNFFormula) (assignment : BitString)
    (width : assignment.length = formula.variableCount) :
    workRunExact? cnfWorkMachine
        (decodedWidthSuccessSteps formula assignment)
        (workConfigAtLeftWord CNFWorkState.seekLeftRoot
          (pushWorkLeft
            (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard ::
              frameFormulaLeftBase (encodeFormulaTokens formula)))
          (cnfFinish ::
            (assignmentWorkSymbols assignment ++
              [cnfRootGuard, cnfBlank]))) =
      some (workConfigAtWord CNFWorkState.clauseStart
        (cnfF ::
          pushWorkLeft
            (List.replicate assignment.length cnfT)
            (cnfFinish ::
              pushWorkLeft
                (List.replicate (encodeFormulaTokens formula).length
                  cnfMarkFalse)
                [cnfRootGuard]))
        (cnfTokenWorkSymbols
            (encodeClauseListTokens formula.clauses ++ [.finish]) ++
          (cnfBoundaryGuard ::
            (List.replicate assignment.length cnfMarkFalse ++
              (cnfFinish ::
                (assignmentWorkSymbols assignment ++
                  [cnfRootGuard, cnfBlank])))))) := by
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  have outerAllowed : ∀ symbol, List.Mem symbol outerCounter →
      symbol = cnfMarkFalse := by
    intro symbol member
    exact FrameTraceDesign.mem_replicate_workSymbol_eq tokens.length
      cnfMarkFalse symbol member
  have counterAllowed : ∀ symbol, List.Mem symbol counter →
      symbol = cnfMarkFalse := by
    intro symbol member
    exact FrameTraceDesign.mem_replicate_workSymbol_eq assignment.length
      cnfMarkFalse symbol member
  have formulaAllowed : ∀ symbol,
      List.Mem symbol (cnfTokenWorkSymbols tokens) →
        FormulaScanSymbol symbol := by
    intro symbol member
    exact cnfTokenWorkSymbols_formulaScan tokens symbol member
  have hPrelude := widthSeekPrelude_exact outerCounter
    (cnfTokenWorkSymbols tokens) counter
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++ [cnfRootGuard, cnfBlank]))
    outerAllowed formulaAllowed counterAllowed
  have clauseTailAllowed : ∀ symbol,
      List.Mem symbol
          (cnfTokenWorkSymbols
            (encodeClauseListTokens formula.clauses ++ [.finish])) →
        FormulaScanSymbol symbol := by
    intro symbol member
    exact cnfTokenWorkSymbols_formulaScan
      (encodeClauseListTokens formula.clauses ++ [.finish]) symbol member
  have hLoop := widthLoop_success_exact outerCounter counter
    (cnfTokenWorkSymbols
      (encodeClauseListTokens formula.clauses ++ [.finish]))
    [] assignment [cnfBlank] outerAllowed counterAllowed clauseTailAllowed
  rw [width] at hLoop
  rw [← cnfTokenWorkSymbols_formula_header] at hLoop
  rw [← width] at hLoop
  have emptyLength : ([] : BitString).length = 0 := rfl
  rw [emptyLength] at hLoop
  rw [Nat.zero_add] at hLoop
  have complete := workRunExact?_compose cnfWorkMachine
    (widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter)
    (widthLoopStepCount outerCounter counter
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish])) [] assignment)
    _ _ _ hPrelude hLoop
  unfold decodedWidthSuccessSteps
  unfold tokens outerCounter counter at complete
  unfold tokens at complete
  unfold frameFormulaLeftBase
  exact complete

theorem encodedFormulaHeader_length (formula : CNFFormula) :
    (encodeFormulaTokens formula).length =
      (formula.variableCount + 1) +
        (cnfTokenWorkSymbols
          (encodeClauseListTokens formula.clauses ++ [.finish])).length := by
  have shape := cnfTokenWorkSymbols_formula_header formula
  have lengths := congrArg List.length shape
  rw [cnfTokenWorkSymbols_length] at lengths
  rw [workSymbol_length_append] at lengths
  rw [workSymbol_replicate_length] at lengths
  exact Eq.trans lengths
    (width_add_succ_swap formula.variableCount
      (cnfTokenWorkSymbols
        (encodeClauseListTokens formula.clauses ++ [.finish])).length)

def widthExpandedLedger (n rounds : Nat) : Nat :=
  (rounds + 2) * (cnfShiftedWorkSpan n * 12)

theorem widthExpandedLedger_le_singlePhase (n rounds : Nat)
    (roundsBound : rounds ≤ n) :
    widthExpandedLedger n rounds ≤ cnfSinglePhaseBudget n := by
  have chunksToSpan : rounds + 2 ≤ cnfShiftedWorkSpan n := by
    unfold cnfShiftedWorkSpan
    exact Nat.add_le_add roundsBound (Nat.le_refl 2)
  have scaled := Nat.mul_le_mul_right
    (cnfShiftedWorkSpan n * 12) chunksToSpan
  have normalized :
      cnfShiftedWorkSpan n * (cnfShiftedWorkSpan n * 12) =
        (cnfShiftedWorkSpan n * cnfShiftedWorkSpan n) * 12 :=
    (FrameTraceDesign.natMulAssocClean
      (cnfShiftedWorkSpan n) (cnfShiftedWorkSpan n) 12).symm
  rw [normalized] at scaled
  unfold widthExpandedLedger
  exact Nat.le_trans scaled
    (cnfScaledQuadratic_le_singlePhaseBudget n 12 (by
      change 12 ≤ 12 + 4
      exact Nat.le_add_right 12 4))

theorem decodedWidthSuccessSteps_le_pairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment)
    (width : assignment.length = formula.variableCount) :
    decodedWidthSuccessSteps formula assignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  let pairSize := BitString.size (BitString.pair input certificate)
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  let formulaTail := cnfTokenWorkSymbols
    (encodeClauseListTokens formula.clauses ++ [.finish])
  have combinedBound : tokens.length + assignment.length ≤ pairSize := by
    unfold tokens pairSize
    exact FrameTraceDesign.decoded_frame_payload_length_le_pair_size
      input certificate formula assignment formulaDecoded assignmentDecoded
  have tokenBound : tokens.length ≤ pairSize :=
    Nat.le_trans (Nat.le_add_right tokens.length assignment.length)
      combinedBound
  have assignmentBound : assignment.length ≤ pairSize :=
    Nat.le_trans (Nat.le_add_left assignment.length tokens.length)
      combinedBound
  have outerBound : outerCounter.length ≤ pairSize := by
    unfold outerCounter
    rw [workSymbol_replicate_length]
    exact tokenBound
  have counterBound : counter.length ≤ pairSize := by
    unfold counter
    rw [workSymbol_replicate_length]
    exact assignmentBound
  have headerLength := encodedFormulaHeader_length formula
  have formulaPartition :
      (([] : BitString).length + assignment.length + 1) +
          formulaTail.length ≤ outerCounter.length := by
    unfold outerCounter formulaTail tokens
    rw [workSymbol_replicate_length]
    have emptyLength : ([] : BitString).length = 0 := rfl
    rw [emptyLength, Nat.zero_add]
    change (assignment.length + 1) +
        (cnfTokenWorkSymbols
          (encodeClauseListTokens formula.clauses ++ [.finish])).length ≤
      (encodeFormulaTokens formula).length
    rw [width]
    exact Nat.le_of_eq headerLength.symm
  have assignmentPartition :
      ([] : BitString).length + assignment.length ≤ counter.length := by
    unfold counter
    rw [workSymbol_replicate_length]
    have emptyLength : ([] : BitString).length = 0 := rfl
    rw [emptyLength, Nat.zero_add]
    exact Nat.le_refl assignment.length
  have loopBound := widthLoopStepCount_le_charges pairSize outerCounter
    counter formulaTail [] assignment formulaPartition assignmentPartition
    outerBound counterBound
  have formulaWordBound : (cnfTokenWorkSymbols tokens).length ≤ pairSize := by
    rw [cnfTokenWorkSymbols_length]
    exact tokenBound
  have preludeFour := widthSeekPreludeSteps_le_fourSpan pairSize
    outerCounter (cnfTokenWorkSymbols tokens) counter outerBound
    formulaWordBound counterBound
  have preludeBound := widthCost_promote_scaled
    (cnfShiftedWorkSpan pairSize)
    (widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter)
    4 12 preludeFour (by
      change 4 ≤ 4 + 8
      exact Nat.le_add_right 4 8)
  have combined := Nat.add_le_add preludeBound loopBound
  have ledgerBound :
      widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter +
          widthLoopStepCount outerCounter counter formulaTail [] assignment ≤
        widthExpandedLedger pairSize assignment.length := by
    unfold widthExpandedLedger
    exact Nat.le_trans combined
      (Nat.le_of_eq
        (widthCharge_plus_successor_mul assignment.length
          (cnfShiftedWorkSpan pairSize * 12)))
  apply Nat.le_trans (by
    unfold decodedWidthSuccessSteps
    unfold tokens outerCounter counter formulaTail at ledgerBound
    exact ledgerBound)
  exact widthExpandedLedger_le_singlePhase pairSize assignment.length
    assignmentBound

theorem decodedWidthMismatchSteps_le_pairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (assignmentDecoded :
      decodeAssignmentCertificate certificate = some assignment) :
    decodedWidthMismatchSteps formula assignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  let pairSize := BitString.size (BitString.pair input certificate)
  let tokens := encodeFormulaTokens formula
  let outerCounter := List.replicate tokens.length cnfMarkFalse
  let counter := List.replicate assignment.length cnfMarkFalse
  let formulaTail := cnfTokenWorkSymbols
    (encodeClauseListTokens formula.clauses ++ [.finish])
  have combinedBound : tokens.length + assignment.length ≤ pairSize := by
    unfold tokens pairSize
    exact FrameTraceDesign.decoded_frame_payload_length_le_pair_size
      input certificate formula assignment formulaDecoded assignmentDecoded
  have tokenBound : tokens.length ≤ pairSize :=
    Nat.le_trans (Nat.le_add_right tokens.length assignment.length)
      combinedBound
  have assignmentBound : assignment.length ≤ pairSize :=
    Nat.le_trans (Nat.le_add_left assignment.length tokens.length)
      combinedBound
  have outerBound : outerCounter.length ≤ pairSize := by
    unfold outerCounter
    rw [workSymbol_replicate_length]
    exact tokenBound
  have counterBound : counter.length ≤ pairSize := by
    unfold counter
    rw [workSymbol_replicate_length]
    exact assignmentBound
  have headerLength := encodedFormulaHeader_length formula
  have formulaPartition :
      (([] : BitString).length + formula.variableCount + 1) +
          formulaTail.length ≤ outerCounter.length := by
    unfold outerCounter formulaTail tokens
    rw [workSymbol_replicate_length]
    have emptyLength : ([] : BitString).length = 0 := rfl
    rw [emptyLength, Nat.zero_add]
    change (formula.variableCount + 1) +
        (cnfTokenWorkSymbols
          (encodeClauseListTokens formula.clauses ++ [.finish])).length ≤
      (encodeFormulaTokens formula).length
    exact Nat.le_of_eq headerLength.symm
  have assignmentPartition :
      ([] : BitString).length + assignment.length ≤ counter.length := by
    unfold counter
    rw [workSymbol_replicate_length]
    have emptyLength : ([] : BitString).length = 0 := rfl
    rw [emptyLength, Nat.zero_add]
    exact Nat.le_refl assignment.length
  have mismatchBound := widthMismatchStepCount_le_charges pairSize
    outerCounter counter formulaTail [] assignment formula.variableCount
    formulaPartition assignmentPartition outerBound counterBound
  have formulaWordBound : (cnfTokenWorkSymbols tokens).length ≤ pairSize := by
    rw [cnfTokenWorkSymbols_length]
    exact tokenBound
  have preludeFour := widthSeekPreludeSteps_le_fourSpan pairSize
    outerCounter (cnfTokenWorkSymbols tokens) counter outerBound
    formulaWordBound counterBound
  have preludeBound := widthCost_promote_scaled
    (cnfShiftedWorkSpan pairSize)
    (widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter)
    4 12 preludeFour (by
      change 4 ≤ 4 + 8
      exact Nat.le_add_right 4 8)
  have combined := Nat.add_le_add preludeBound mismatchBound
  have ledgerBound :
      widthSeekPreludeSteps outerCounter (cnfTokenWorkSymbols tokens) counter +
          widthMismatchStepCount outerCounter counter formulaTail []
            formula.variableCount assignment ≤
        widthExpandedLedger pairSize formula.variableCount := by
    unfold widthExpandedLedger
    exact Nat.le_trans combined
      (Nat.le_of_eq
        (widthCharge_plus_successor_mul formula.variableCount
          (cnfShiftedWorkSpan pairSize * 12)))
  have variableBound := decoded_formulaVariableCount_le_pair_size
    input certificate formula assignment formulaDecoded assignmentDecoded
  apply Nat.le_trans (by
    unfold decodedWidthMismatchSteps
    unfold tokens outerCounter counter formulaTail at ledgerBound
    exact ledgerBound)
  exact widthExpandedLedger_le_singlePhase pairSize formula.variableCount
    variableBound

end WidthSuccessDesign
end PNP.Concrete


namespace PNP.Concrete
namespace AssignmentGrammarFailureDesign

open FrameTraceDesign

set_option maxRecDepth 100000

/-- A paired token layout whose final assignment token is explicit rather
than fixed to `Finish`. -/
def pairedTokenLayoutTerminal (formulaTokens assignmentPrefix :
    List CNFToken) (terminal : CNFToken) : List WorkSymbol :=
  List.replicate formulaTokens.length cnfT ++
    cnfFinish ::
      (cnfTokenWorkSymbols formulaTokens ++
        cnfSep ::
          (List.replicate assignmentPrefix.length cnfT ++
            cnfFinish ::
              (cnfTokenWorkSymbols assignmentPrefix ++
                [terminal.workSymbol])))

private theorem assignmentTape_append_assoc {α : Type}
    (left middle right : List α) :
    (left ++ middle) ++ right = left ++ (middle ++ right) := by
  induction left with
  | nil => rfl
  | cons item rest ih => exact congrArg (List.cons item) ih

private theorem assignmentTape_cons_append {α : Type}
    (item : α) (left right : List α) :
    (item :: left) ++ right = item :: (left ++ right) := rfl

private theorem assignmentTape_nil_append {α : Type}
    (right : List α) : ([] : List α) ++ right = right := rfl

private theorem assignmentAppendConsAsSingleton {α : Type}
    (front suffix : List α) (item : α) :
    front ++ item :: suffix = (front ++ [item]) ++ suffix := by
  induction front with
  | nil => rfl
  | cons head rest ih => exact congrArg (List.cons head) ih

private theorem assignmentPrefixLayout {α : Type}
    (done scan rest payload assignment tail : List α)
    (mark finish marked : α) :
    (done ++ mark :: (scan ++ rest)) ++
        ((finish :: payload) ++ marked :: (assignment ++ tail)) =
      ((done ++ [mark]) ++ (scan ++ rest)) ++
        finish :: (((payload ++ [marked]) ++ assignment) ++ tail) := by
  induction done with
  | nil =>
      change mark ::
          ((scan ++ rest) ++
            finish :: (payload ++ marked :: (assignment ++ tail))) =
        mark ::
          ((scan ++ rest) ++
            finish :: (((payload ++ [marked]) ++ assignment) ++ tail))
      rw [assignmentAppendConsAsSingleton payload (assignment ++ tail) marked]
      rw [assignmentTape_append_assoc (payload ++ [marked]) assignment tail]
  | cons head suffix ih => exact congrArg (List.cons head) ih

private theorem assignmentMapOfBool_append (left right : BitString) :
    (left ++ right).map TapeSymbol.ofBool =
      left.map TapeSymbol.ofBool ++ right.map TapeSymbol.ofBool := by
  induction left with
  | nil => rfl
  | cons bit rest ih =>
      exact congrArg (List.cons (TapeSymbol.ofBool bit)) ih

private theorem assignmentMapOfBool_false_cons (bits : BitString) :
    (false :: bits).map TapeSymbol.ofBool =
      TapeSymbol.zero :: bits.map TapeSymbol.ofBool := rfl

private theorem assignmentMapOfBool_false_singleton :
    [false].map TapeSymbol.ofBool = [TapeSymbol.zero] := rfl

private theorem assignmentEncodeTokenPairs_singleton (token : CNFToken) :
    encodeTokenPairs [token] = token.bits := by
  cases token <;> rfl

private theorem assignmentMapOfBool_replicate_true (n : Nat) :
    (List.replicate n true).map TapeSymbol.ofBool =
      List.replicate n TapeSymbol.one := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (List.cons TapeSymbol.one) ih

private theorem assignmentReplicate_one_succ_tail (n : Nat) :
    List.replicate (n + 1) TapeSymbol.one =
      List.replicate n TapeSymbol.one ++ [TapeSymbol.one] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change TapeSymbol.one :: List.replicate (n + 1) TapeSymbol.one =
        TapeSymbol.one ::
          (List.replicate n TapeSymbol.one ++ [TapeSymbol.one])
      exact congrArg (List.cons TapeSymbol.one) ih

private theorem assignmentReplicate_one_add_two (n : Nat) :
    List.replicate (n + 2) TapeSymbol.one =
      TapeSymbol.one ::
        (List.replicate n TapeSymbol.one ++ [TapeSymbol.one]) := by
  change TapeSymbol.one :: List.replicate (n + 1) TapeSymbol.one =
    TapeSymbol.one ::
      (List.replicate n TapeSymbol.one ++ [TapeSymbol.one])
  exact congrArg (List.cons TapeSymbol.one)
    (assignmentReplicate_one_succ_tail n)

private theorem assignmentEncodeWorkRight_replicate_true (n : Nat) :
    encodeWorkRight (List.replicate n cnfT) =
      List.replicate (2 * n) TapeSymbol.one := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ]
      change TapeSymbol.one :: TapeSymbol.one ::
          encodeWorkRight (List.replicate n cnfT) =
        List.replicate (2 * (n + 1)) TapeSymbol.one
      rw [ih, Nat.mul_add]
      rfl

private theorem assignmentPairedRawShape
    (outer formula counter assignment terminal : List TapeSymbol) :
    outer ++ TapeSymbol.one :: TapeSymbol.zero ::
        (formula ++ TapeSymbol.zero :: TapeSymbol.one ::
          (counter ++ TapeSymbol.one :: TapeSymbol.zero ::
            (assignment ++ terminal))) =
      (outer ++ [TapeSymbol.one]) ++
        (TapeSymbol.zero :: (formula ++ [TapeSymbol.zero])) ++
          ((TapeSymbol.one :: (counter ++ [TapeSymbol.one])) ++
            (TapeSymbol.zero :: (assignment ++ terminal))) := by
  rw [assignmentAppendConsAsSingleton outer _ TapeSymbol.one]
  rw [assignmentAppendConsAsSingleton formula _ TapeSymbol.zero]
  rw [assignmentAppendConsAsSingleton counter _ TapeSymbol.one]
  repeat' rw [assignmentTape_append_assoc]
  repeat' rw [assignmentTape_cons_append]
  repeat' rw [assignmentTape_nil_append]
  repeat' rw [assignmentTape_append_assoc]
  repeat' rw [assignmentTape_cons_append]
  repeat' rw [assignmentTape_nil_append]

theorem encodeWorkRight_pairedTokenLayoutTerminal
    (formulaTokens assignmentPrefix : List CNFToken)
    (terminal : CNFToken) :
    encodeWorkRight
        (pairedTokenLayoutTerminal formulaTokens assignmentPrefix terminal) =
      (BitString.pair
        (paddedFormulaTokenBits formulaTokens)
        (encodeTokenPairs assignmentPrefix ++ terminal.bits)).map
          TapeSymbol.ofBool := by
  unfold pairedTokenLayoutTerminal
  rw [encodeWorkRight_append]
  rw [assignmentEncodeWorkRight_replicate_true]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        encodeWorkRight
          (cnfTokenWorkSymbols formulaTokens ++
            cnfSep ::
              (List.replicate assignmentPrefix.length cnfT ++
                cnfFinish ::
                  (cnfTokenWorkSymbols assignmentPrefix ++
                    [terminal.workSymbol]))) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_cnfTokenWorkSymbols]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
          TapeSymbol.zero :: TapeSymbol.one ::
            encodeWorkRight
              (List.replicate assignmentPrefix.length cnfT ++
                cnfFinish ::
                  (cnfTokenWorkSymbols assignmentPrefix ++
                    [terminal.workSymbol]))) = _
  rw [encodeWorkRight_append]
  rw [assignmentEncodeWorkRight_replicate_true]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
          TapeSymbol.zero :: TapeSymbol.one ::
            (List.replicate (2 * assignmentPrefix.length) TapeSymbol.one ++
              TapeSymbol.one :: TapeSymbol.zero ::
                encodeWorkRight
                  (cnfTokenWorkSymbols assignmentPrefix ++
                    [terminal.workSymbol]))) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_cnfTokenWorkSymbols]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        ((encodeTokenPairs formulaTokens).map TapeSymbol.ofBool ++
          TapeSymbol.zero :: TapeSymbol.one ::
            (List.replicate (2 * assignmentPrefix.length) TapeSymbol.one ++
              TapeSymbol.one :: TapeSymbol.zero ::
                ((encodeTokenPairs assignmentPrefix).map TapeSymbol.ofBool ++
                  encodeWorkRight [terminal.workSymbol]))) = _
  have terminalEncoded :
      encodeWorkRight [terminal.workSymbol] =
        terminal.bits.map TapeSymbol.ofBool := by
    exact CNFToken.workSymbol_first_second terminal
  rw [terminalEncoded]
  unfold BitString.pair BitString.frame
  rw [assignmentMapOfBool_append]
  rw [assignmentMapOfBool_append, assignmentMapOfBool_append]
  rw [assignmentMapOfBool_replicate_true,
    assignmentMapOfBool_replicate_true]
  rw [paddedFormulaTokenBits_length]
  rw [BitString.length_append_constructive]
  rw [encodeTokenPairs_length]
  rw [token_bits_length]
  unfold paddedFormulaTokenBits
  rw [assignmentMapOfBool_false_cons,
    assignmentMapOfBool_false_cons]
  rw [assignmentMapOfBool_append (encodeTokenPairs formulaTokens) [false]]
  rw [assignmentMapOfBool_append (encodeTokenPairs assignmentPrefix)
    terminal.bits]
  rw [assignmentMapOfBool_false_singleton]
  rw [assignmentReplicate_one_succ_tail]
  rw [assignmentReplicate_one_add_two]
  exact assignmentPairedRawShape _ _ _ _ _

theorem packWorkSymbols_pairedTokenLayoutTerminal
    (formulaTokens assignmentPrefix : List CNFToken)
    (terminal : CNFToken) :
    packWorkSymbols
        ((BitString.pair
          (paddedFormulaTokenBits formulaTokens)
          (encodeTokenPairs assignmentPrefix ++ terminal.bits)).map
            TapeSymbol.ofBool) =
      pairedTokenLayoutTerminal formulaTokens assignmentPrefix terminal := by
  have encoded := encodeWorkRight_pairedTokenLayoutTerminal
    formulaTokens assignmentPrefix terminal
  have packed := congrArg packWorkSymbols encoded
  rw [packWorkSymbols_encodeWorkRight] at packed
  exact packed.symm

theorem pairedWorkTape_terminal_shape
    (input certificate : BitString) (formula : CNFFormula)
    (assignmentPrefix : List CNFToken) (terminal : CNFToken)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (certificateShape : certificate =
      encodeTokenPairs assignmentPrefix ++ terminal.bits) :
    pairedWorkTape input certificate =
      WorkTape.ofSymbols
        (pairedTokenLayoutTerminal (encodeFormulaTokens formula)
          assignmentPrefix terminal) := by
  have formulaShape := encodeFormula_of_decode input formula formulaDecoded
  rw [← formulaShape, certificateShape]
  rw [encodeFormula_eq_padded_tokens]
  unfold pairedWorkTape
  change WorkTape.ofSymbols
      (packWorkSymbols
        ((BitString.pair
          (paddedFormulaTokenBits (encodeFormulaTokens formula))
          (encodeTokenPairs assignmentPrefix ++ terminal.bits)).map
            TapeSymbol.ofBool)) = _
  rw [packWorkSymbols_pairedTokenLayoutTerminal]

inductive AssignmentGrammarFailure : List CNFToken → Prop where
  | empty : AssignmentGrammarFailure []
  | valueFalse {rest : List CNFToken}
      (tail : AssignmentGrammarFailure rest) :
      AssignmentGrammarFailure (.f :: rest)
  | valueTrue {rest : List CNFToken}
      (tail : AssignmentGrammarFailure rest) :
      AssignmentGrammarFailure (.t :: rest)
  | separator (rest : List CNFToken) :
      AssignmentGrammarFailure (.sep :: rest)
  | finishTrailing (next : CNFToken) (rest : List CNFToken) :
      AssignmentGrammarFailure (.finish :: next :: rest)

theorem assignmentGrammarFailure_of_decode_none
    (tokens : List CNFToken)
    (decoded : decodeAssignmentTokens tokens = none) :
    AssignmentGrammarFailure tokens := by
  induction tokens with
  | nil => exact .empty
  | cons token rest ih =>
      cases token with
      | f =>
          change (match decodeAssignmentTokens rest with
            | none => none
            | some assignment => some (false :: assignment)) = none at decoded
          cases tailCase : decodeAssignmentTokens rest with
          | none =>
              exact .valueFalse (ih tailCase)
          | some assignment =>
              rw [tailCase] at decoded
              contradiction
      | t =>
          change (match decodeAssignmentTokens rest with
            | none => none
            | some assignment => some (true :: assignment)) = none at decoded
          cases tailCase : decodeAssignmentTokens rest with
          | none =>
              exact .valueTrue (ih tailCase)
          | some assignment =>
              rw [tailCase] at decoded
              contradiction
      | sep => exact .separator rest
      | finish =>
          cases rest with
          | nil => contradiction
          | cons next suffix => exact .finishTrailing next suffix

inductive AssignmentFailureNormal : List CNFToken → Prop where
  | empty : AssignmentFailureNormal []
  | terminalF (values : BitString) :
      AssignmentFailureNormal (assignmentValueTokens values ++ [.f])
  | terminalT (values : BitString) :
      AssignmentFailureNormal (assignmentValueTokens values ++ [.t])
  | terminalSep (values : BitString) :
      AssignmentFailureNormal (assignmentValueTokens values ++ [.sep])
  | interiorSep (values : BitString) (next : CNFToken)
      (rest : List CNFToken) :
      AssignmentFailureNormal
        (assignmentValueTokens values ++ .sep :: next :: rest)
  | interiorFinish (values : BitString) (next : CNFToken)
      (rest : List CNFToken) :
      AssignmentFailureNormal
        (assignmentValueTokens values ++ .finish :: next :: rest)

theorem assignmentGrammarFailure_normal
    {tokens : List CNFToken} (failure : AssignmentGrammarFailure tokens) :
    AssignmentFailureNormal tokens := by
  induction failure with
  | empty => exact .empty
  | valueFalse tail ih =>
      cases ih with
      | empty => exact .terminalF []
      | terminalF values => exact .terminalF (false :: values)
      | terminalT values => exact .terminalT (false :: values)
      | terminalSep values => exact .terminalSep (false :: values)
      | interiorSep values next rest =>
          exact .interiorSep (false :: values) next rest
      | interiorFinish values next rest =>
          exact .interiorFinish (false :: values) next rest
  | valueTrue tail ih =>
      cases ih with
      | empty => exact .terminalT []
      | terminalF values => exact .terminalF (true :: values)
      | terminalT values => exact .terminalT (true :: values)
      | terminalSep values => exact .terminalSep (true :: values)
      | interiorSep values next rest =>
          exact .interiorSep (true :: values) next rest
      | interiorFinish values next rest =>
          exact .interiorFinish (true :: values) next rest
  | separator rest =>
      cases rest with
      | nil => exact .terminalSep []
      | cons next suffix => exact .interiorSep [] next suffix
  | finishTrailing next rest => exact .interiorFinish [] next rest

def frameTwoPrefixStart (doneCounter donePayload restCounter :
    List WorkSymbol) (assignment : BitString)
    (payloadTail leftBase : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameTwoFindCounter
    (cnfBoundaryGuard :: leftBase)
    ((doneCounter ++
        (List.replicate assignment.length cnfT ++ restCounter)) ++
      cnfFinish ::
        ((donePayload ++ assignmentWorkSymbols assignment) ++ payloadTail))

def frameTwoPrefixFinal (doneCounter donePayload restCounter :
    List WorkSymbol) (assignment : BitString)
    (payloadTail leftBase : List WorkSymbol) : WorkConfiguration :=
  workConfigAtWord CNFWorkState.frameTwoFindCounter
    (cnfBoundaryGuard :: leftBase)
    ((doneCounter ++
        (List.replicate assignment.length cnfMarkFalse ++ restCounter)) ++
      cnfFinish ::
        ((donePayload ++ markedAssignmentWorkSymbols assignment) ++
          payloadTail))

def frameTwoPrefixSteps (restCounter : List WorkSymbol) :
    List WorkSymbol → List WorkSymbol → BitString → Nat
  | _, _, [] => 0
  | doneCounter, donePayload, value :: rest =>
      frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT ++ restCounter) donePayload +
        frameTwoPrefixSteps restCounter
          (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest

private theorem frameTwoPrefixStart_cons
    (doneCounter donePayload restCounter : List WorkSymbol)
    (value : Bool) (rest : BitString)
    (payloadTail leftBase : List WorkSymbol) :
    frameTwoPrefixStart doneCounter donePayload restCounter
        (value :: rest) payloadTail leftBase =
      workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase)
        (doneCounter ++ cnfT ::
          ((List.replicate rest.length cnfT ++ restCounter) ++
            cnfFinish ::
              (donePayload ++ assignmentValueWorkSymbol value ::
                (assignmentWorkSymbols rest ++ payloadTail)))) := by
  unfold frameTwoPrefixStart
  rw [replicate_bit_cons_length]
  rw [assignmentWorkSymbols_cons]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  rfl

private theorem frameTwoPrefix_after_iteration
    (doneCounter donePayload restCounter : List WorkSymbol)
    (value : Bool) (rest : BitString)
    (payloadTail leftBase : List WorkSymbol) :
    workConfigAtWord CNFWorkState.frameTwoFindCounter
        (cnfBoundaryGuard :: leftBase)
        ((doneCounter ++ cnfMarkFalse ::
          (List.replicate rest.length cnfT ++ restCounter)) ++
            (cnfFinish :: donePayload ++
              markedAssignmentValueWorkSymbol value ::
                (assignmentWorkSymbols rest ++ payloadTail))) =
      frameTwoPrefixStart (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value])
        restCounter rest payloadTail leftBase := by
  unfold frameTwoPrefixStart
  exact congrArg
    (fun word => workConfigAtWord CNFWorkState.frameTwoFindCounter
      (cnfBoundaryGuard :: leftBase) word)
    (assignmentPrefixLayout doneCounter
      (List.replicate rest.length cnfT) restCounter donePayload
      (assignmentWorkSymbols rest) payloadTail cnfMarkFalse cnfFinish
      (markedAssignmentValueWorkSymbol value))

private theorem frameTwoPrefixFinal_cons
    (doneCounter donePayload restCounter : List WorkSymbol)
    (value : Bool) (rest : BitString)
    (payloadTail leftBase : List WorkSymbol) :
    frameTwoPrefixFinal (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value])
        restCounter rest payloadTail leftBase =
      frameTwoPrefixFinal doneCounter donePayload restCounter
        (value :: rest) payloadTail leftBase := by
  unfold frameTwoPrefixFinal
  rw [replicate_bit_cons_length]
  rw [markedAssignmentWorkSymbols_cons]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  rfl

private theorem frameTwoPrefixSteps_value
    (restCounter doneCounter donePayload : List WorkSymbol)
    (value : Bool) (rest : BitString) :
    frameTwoPrefixSteps restCounter doneCounter donePayload (value :: rest) =
      frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT ++ restCounter) donePayload +
        frameTwoPrefixSteps restCounter
          (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest := by
  rfl

theorem frameTwo_prefix_exact
    (doneCounter donePayload restCounter : List WorkSymbol)
    (assignment : BitString) (payloadTail leftBase : List WorkSymbol)
    (doneCounterAllowed : ∀ symbol, List.Mem symbol doneCounter →
      symbol = cnfMarkFalse)
    (donePayloadAllowed : ∀ symbol, List.Mem symbol donePayload →
      AssignmentMarkSymbol symbol)
    (restCounterAllowed : ∀ symbol, List.Mem symbol restCounter →
      symbol = cnfT) :
    workRunExact? cnfWorkMachine
        (frameTwoPrefixSteps restCounter doneCounter donePayload assignment)
        (frameTwoPrefixStart doneCounter donePayload restCounter assignment
          payloadTail leftBase) =
      some (frameTwoPrefixFinal doneCounter donePayload restCounter assignment
        payloadTail leftBase) := by
  induction assignment generalizing doneCounter donePayload with
  | nil => rfl
  | cons value rest ih =>
      have scanCounterAllowed : ∀ symbol,
          List.Mem symbol
            (List.replicate rest.length cnfT ++ restCounter) →
            symbol = cnfT := by
        intro symbol member
        have split := ClauseLiteralDesign.workSymbol_mem_append_cases
          (List.replicate rest.length cnfT) restCounter symbol member
        cases split with
        | inl inReplicate =>
            exact mem_replicate_workSymbol_eq rest.length cnfT symbol
              inReplicate
        | inr inRest => exact restCounterAllowed symbol inRest
      have iteration := frameTwo_iteration_exact doneCounter
        (List.replicate rest.length cnfT ++ restCounter) donePayload
        leftBase value (assignmentWorkSymbols rest ++ payloadTail)
        doneCounterAllowed scanCounterAllowed donePayloadAllowed
      rw [← frameTwoPrefixStart_cons] at iteration
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
      have remaining := ih (doneCounter ++ [cnfMarkFalse])
        (donePayload ++ [markedAssignmentValueWorkSymbol value])
        nextCounterAllowed nextPayloadAllowed
      rw [← frameTwoPrefix_after_iteration] at remaining
      rw [frameTwoPrefixFinal_cons] at remaining
      rw [frameTwoPrefixSteps_value]
      exact workRunExact?_compose cnfWorkMachine
        (frameOneIterationSteps doneCounter
          (List.replicate rest.length cnfT ++ restCounter) donePayload)
        (frameTwoPrefixSteps restCounter
          (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest)
        _ _ _ iteration remaining

def frameTwoTerminalBadSteps (assignment : BitString) : Nat :=
  (((frameTwoPrefixSteps [] [] [] assignment + assignment.length) + 1) +
    assignment.length) + 1

theorem frameTwo_terminal_bad_exact
    (assignment : BitString) (leftBase : List WorkSymbol)
    (bad : WorkSymbol) (invalid : ¬ FrameTwoCheckSymbol bad) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (frameTwoTerminalBadSteps assignment)
          (frameTwoPrefixStart [] [] [] assignment [bad] leftBase) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have prefixRun := frameTwo_prefix_exact [] [] [] assignment [bad]
    leftBase (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
  unfold frameTwoPrefixFinal at prefixRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at prefixRun
  have counterRun := frameTwo_findCounter_markFalse_scan assignment.length
    (cnfBoundaryGuard :: leftBase)
    (cnfFinish :: markedAssignmentWorkSymbols assignment ++ [bad])
  have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_findCounter_finish_step
      (pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase))
      (markedAssignmentWorkSymbols assignment ++ [bad]))
  have payloadRun := frameTwo_checkPayload_marked_scan assignment
    (cnfFinish ::
      pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase)) [bad]
  have rejectRun := frameTwoCheckPayload_reject_run
    (pushWorkLeft (markedAssignmentWorkSymbols assignment)
      (cnfFinish ::
        pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
          (cnfBoundaryGuard :: leftBase))) [] bad invalid
  have throughCounter := workRunExact?_compose cnfWorkMachine
    (frameTwoPrefixSteps [] [] [] assignment) assignment.length
    _ _ _ prefixRun counterRun
  have throughFinish := workRunExact?_compose cnfWorkMachine
    (frameTwoPrefixSteps [] [] [] assignment + assignment.length) 1
    _ _ _ throughCounter finishRun
  have throughPayload := workRunExact?_compose cnfWorkMachine
    ((frameTwoPrefixSteps [] [] [] assignment + assignment.length) + 1)
    assignment.length _ _ _ throughFinish payloadRun
  have complete := workRunExact?_compose cnfWorkMachine
    (((frameTwoPrefixSteps [] [] [] assignment + assignment.length) + 1) +
      assignment.length) 1 _ _ _ throughPayload rejectRun
  refine ⟨(workConfigAtWord CNFWorkState.reject
    (pushWorkLeft (markedAssignmentWorkSymbols assignment)
      (cnfFinish ::
        pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
          (cnfBoundaryGuard :: leftBase))) [bad]).tape, ?_⟩
  unfold frameTwoTerminalBadSteps
  exact complete

theorem frameTwoFindPayload_reject_run
    (left right : List WorkSymbol) (bad : WorkSymbol)
    (badCase : bad = cnfSep ∨ bad = cnfFinish) :
    workRunExact? cnfWorkMachine 1
        (workConfigAtWord CNFWorkState.frameTwoFindPayload left
          (bad :: right)) =
      some (workConfigAtWord CNFWorkState.reject left (bad :: right)) := by
  cases badCase with
  | inl equal =>
      cases equal
      apply cnfReject_run_one CNFWorkState.frameTwoFindPayload _ (by rfl)
      rfl
  | inr equal =>
      cases equal
      apply cnfReject_run_one CNFWorkState.frameTwoFindPayload _ (by rfl)
      rfl

def frameTwoInteriorBadSteps
    (assignment : BitString) (suffixPrefixLength : Nat) : Nat :=
  (((((frameTwoPrefixSteps
    (List.replicate (Nat.succ suffixPrefixLength) cnfT)
    [] [] assignment + assignment.length) + 1) + suffixPrefixLength) + 1) +
    assignment.length) + 1

theorem frameTwo_interior_bad_exact
    (assignment : BitString) (suffixPrefix : List CNFToken)
    (terminal : CNFToken) (leftBase : List WorkSymbol)
    (bad : WorkSymbol) (badCase : bad = cnfSep ∨ bad = cnfFinish) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (frameTwoInteriorBadSteps assignment suffixPrefix.length)
          (frameTwoPrefixStart [] []
            (List.replicate (Nat.succ suffixPrefix.length) cnfT)
            assignment
            (bad :: (cnfTokenWorkSymbols suffixPrefix ++
              [terminal.workSymbol])) leftBase) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  let restCounter :=
    List.replicate (Nat.succ suffixPrefix.length) cnfT
  let payloadTail := bad ::
    (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol])
  have prefixRun := frameTwo_prefix_exact [] [] restCounter assignment
    payloadTail leftBase (by intro symbol member; contradiction)
    (by intro symbol member; contradiction) (by
      intro symbol member
      exact mem_replicate_workSymbol_eq (Nat.succ suffixPrefix.length)
        cnfT symbol member)
  unfold frameTwoPrefixFinal at prefixRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at prefixRun
  have doneCounterRun := frameTwo_findCounter_markFalse_scan
    assignment.length (cnfBoundaryGuard :: leftBase)
    (restCounter ++ cnfFinish ::
      (markedAssignmentWorkSymbols assignment ++ payloadTail))
  have markCounterRun := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_findCounter_t_step
      (pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase))
      (List.replicate suffixPrefix.length cnfT ++
        cnfFinish ::
          (markedAssignmentWorkSymbols assignment ++ payloadTail)))
  have restCounterRun := frameTwo_toHeader_t_word_scan
    (List.replicate suffixPrefix.length cnfT)
    (cnfMarkFalse ::
      pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
        (cnfBoundaryGuard :: leftBase))
    (cnfFinish ::
      (markedAssignmentWorkSymbols assignment ++ payloadTail)) (by
        intro symbol member
        exact mem_replicate_workSymbol_eq suffixPrefix.length cnfT symbol
          member)
  rw [length_replicate_workSymbol] at restCounterRun
  have headerRun := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameTwo_toHeader_finish_step
      (pushWorkLeft (List.replicate suffixPrefix.length cnfT)
        (cnfMarkFalse ::
          pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase)))
      (markedAssignmentWorkSymbols assignment ++ payloadTail))
  have payloadRun := frameTwo_findPayload_marked_scan
    (markedAssignmentWorkSymbols assignment)
    (cnfFinish ::
      pushWorkLeft (List.replicate suffixPrefix.length cnfT)
        (cnfMarkFalse ::
          pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
            (cnfBoundaryGuard :: leftBase)))
    payloadTail (markedAssignmentWorkSymbols_allowed assignment)
  rw [markedAssignmentWorkSymbols_length] at payloadRun
  have rejectRun := frameTwoFindPayload_reject_run
    (pushWorkLeft (markedAssignmentWorkSymbols assignment)
      (cnfFinish ::
        pushWorkLeft (List.replicate suffixPrefix.length cnfT)
          (cnfMarkFalse ::
            pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
              (cnfBoundaryGuard :: leftBase))))
    (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol]) bad badCase
  have h1 := workRunExact?_compose cnfWorkMachine
    (frameTwoPrefixSteps restCounter [] [] assignment) assignment.length
    _ _ _ prefixRun doneCounterRun
  have h2 := workRunExact?_compose cnfWorkMachine
    (frameTwoPrefixSteps restCounter [] [] assignment + assignment.length)
    1 _ _ _ h1 markCounterRun
  have h3 := workRunExact?_compose cnfWorkMachine
    ((frameTwoPrefixSteps restCounter [] [] assignment + assignment.length) +
      1) suffixPrefix.length _ _ _ h2 restCounterRun
  have h4 := workRunExact?_compose cnfWorkMachine
    (((frameTwoPrefixSteps restCounter [] [] assignment +
      assignment.length) + 1) + suffixPrefix.length) 1
    _ _ _ h3 headerRun
  have h5 := workRunExact?_compose cnfWorkMachine
    ((((frameTwoPrefixSteps restCounter [] [] assignment +
      assignment.length) + 1) + suffixPrefix.length) + 1)
    assignment.length _ _ _ h4 payloadRun
  have complete := workRunExact?_compose cnfWorkMachine
    (((((frameTwoPrefixSteps restCounter [] [] assignment +
      assignment.length) + 1) + suffixPrefix.length) + 1) +
        assignment.length) 1 _ _ _ h5 rejectRun
  refine ⟨(workConfigAtWord CNFWorkState.reject
    (pushWorkLeft (markedAssignmentWorkSymbols assignment)
      (cnfFinish ::
        pushWorkLeft (List.replicate suffixPrefix.length cnfT)
          (cnfMarkFalse ::
            pushWorkLeft (List.replicate assignment.length cnfMarkFalse)
              (cnfBoundaryGuard :: leftBase))))
    (bad :: (cnfTokenWorkSymbols suffixPrefix ++
      [terminal.workSymbol]))).tape, ?_⟩
  unfold frameTwoInteriorBadSteps
  exact complete

def assignmentTerminalRejectSteps (formulaTokens : List CNFToken)
    (assignment : BitString) : Nat :=
  (2 + (frameOneFoldSteps [] [] formulaTokens +
    frameOneTerminalSteps formulaTokens)) +
      frameTwoTerminalBadSteps assignment

theorem assignment_terminal_full_exact
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (bad : CNFToken)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (certificateShape : certificate =
      encodeTokenPairs (assignmentValueTokens assignment) ++ bad.bits)
    (badCase : bad = .f ∨ bad = .t ∨ bad = .sep) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (assignmentTerminalRejectSteps
            (encodeFormulaTokens formula) assignment)
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have tapeShape := pairedWorkTape_terminal_shape input certificate formula
    (assignmentValueTokens assignment) bad formulaDecoded certificateShape
  rcases encodeFormulaTokens_cons formula with ⟨first, rest, tokenShape⟩
  let assignmentSuffix :=
    List.replicate assignment.length cnfT ++
      cnfFinish :: (assignmentWorkSymbols assignment ++ [bad.workSymbol])
  have bootRun := boot_t_exact
    (List.replicate rest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols rest ++ cnfSep :: assignmentSuffix)))
  have frameOneRun := frameOne_complete_exact (first :: rest)
    assignmentSuffix
  rw [frameOneFoldStart_empty_cons] at frameOneRun
  let leftBase := frameFormulaLeftBase (first :: rest)
  have invalid : ¬ FrameTwoCheckSymbol bad.workSymbol := by
    intro allowed
    cases badCase with
    | inl equal =>
        cases equal
        cases allowed
    | inr remaining =>
        cases remaining with
        | inl equal =>
            cases equal
            cases allowed
        | inr equal =>
            cases equal
            cases allowed
  rcases frameTwo_terminal_bad_exact assignment leftBase bad.workSymbol
      invalid with ⟨tape, badRun⟩
  unfold frameTwoPrefixStart at badRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun
  have throughFrame := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest))
    _ _ _ bootRun frameOneRun
  have complete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest)))
    (frameTwoTerminalBadSteps assignment)
    _ _ _ throughFrame badRun
  refine ⟨tape, ?_⟩
  rw [tapeShape, tokenShape]
  unfold pairedTokenLayoutTerminal
  rw [assignmentValueTokens_length]
  rw [assignmentValueTokens_workSymbols]
  unfold assignmentTerminalRejectSteps
  exact complete

private theorem assignmentReplicate_add {α : Type}
    (first second : Nat) (item : α) :
    List.replicate (first + second) item =
      List.replicate first item ++ List.replicate second item := by
  induction first with
  | zero =>
      rw [Nat.zero_add]
      rfl
  | succ first ih =>
      rw [Nat.succ_add]
      change item :: List.replicate (first + second) item =
        item ::
          (List.replicate first item ++ List.replicate second item)
      exact congrArg (List.cons item) ih

private theorem assignmentReplicate_cons_length {α β : Type}
    (head : α) (tail : List α) (item : β) :
    List.replicate (head :: tail).length item =
      item :: List.replicate tail.length item := rfl

private theorem assignmentTokenWorkSymbols_cons
    (head : CNFToken) (tail : List CNFToken) :
    cnfTokenWorkSymbols (head :: tail) =
      head.workSymbol :: cnfTokenWorkSymbols tail := rfl

def assignmentInteriorRejectSteps (formulaTokens : List CNFToken)
    (assignment : BitString) (suffixPrefixLength : Nat) : Nat :=
  (2 + (frameOneFoldSteps [] [] formulaTokens +
    frameOneTerminalSteps formulaTokens)) +
      frameTwoInteriorBadSteps assignment suffixPrefixLength

theorem assignment_interior_full_exact
    (input certificate : BitString) (formula : CNFFormula)
    (assignment : BitString) (bad : CNFToken)
    (suffixPrefix : List CNFToken) (terminal : CNFToken)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (certificateShape : certificate =
      encodeTokenPairs
          (assignmentValueTokens assignment ++ bad :: suffixPrefix) ++
        terminal.bits)
    (badCase : bad = .sep ∨ bad = .finish) :
    ∃ tape,
      workRunExact? cnfWorkMachine
          (assignmentInteriorRejectSteps
            (encodeFormulaTokens formula) assignment suffixPrefix.length)
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  let assignmentPrefix :=
    assignmentValueTokens assignment ++ bad :: suffixPrefix
  have tapeShape := pairedWorkTape_terminal_shape input certificate formula
    assignmentPrefix terminal formulaDecoded certificateShape
  rcases encodeFormulaTokens_cons formula with ⟨first, rest, tokenShape⟩
  let restCounter :=
    List.replicate (Nat.succ suffixPrefix.length) cnfT
  let payloadTail := bad.workSymbol ::
    (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol])
  let assignmentSuffix :=
    (List.replicate assignment.length cnfT ++ restCounter) ++
      cnfFinish ::
        ((assignmentWorkSymbols assignment ++ payloadTail))
  have bootRun := boot_t_exact
    (List.replicate rest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols rest ++ cnfSep :: assignmentSuffix)))
  have frameOneRun := frameOne_complete_exact (first :: rest)
    assignmentSuffix
  rw [frameOneFoldStart_empty_cons] at frameOneRun
  let leftBase := frameFormulaLeftBase (first :: rest)
  have badWorkCase : bad.workSymbol = cnfSep ∨
      bad.workSymbol = cnfFinish := by
    cases badCase with
    | inl equal =>
        cases equal
        exact Or.inl rfl
    | inr equal =>
        cases equal
        exact Or.inr rfl
  rcases frameTwo_interior_bad_exact assignment suffixPrefix terminal
      leftBase bad.workSymbol badWorkCase with ⟨tape, badRun⟩
  unfold frameTwoPrefixStart at badRun
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun
  have throughFrame := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest))
    _ _ _ bootRun frameOneRun
  unfold leftBase frameFormulaLeftBase at badRun
  unfold assignmentSuffix restCounter payloadTail at throughFrame
  repeat' rw [FrameTraceDesign.frameWork_append_assoc] at badRun throughFrame
  have badStartShape :
      ([] ++
        (List.replicate assignment.length cnfT ++
          (List.replicate (Nat.succ suffixPrefix.length) cnfT ++
            cnfFinish ::
              ([] ++
                (assignmentWorkSymbols assignment ++
                  bad.workSymbol ::
                    (cnfTokenWorkSymbols suffixPrefix ++
                      [terminal.workSymbol])))))) =
        (List.replicate assignment.length cnfT ++
          List.replicate (Nat.succ suffixPrefix.length) cnfT) ++
            cnfFinish ::
              (assignmentWorkSymbols assignment ++
                bad.workSymbol ::
                  (cnfTokenWorkSymbols suffixPrefix ++
                    [terminal.workSymbol])) := by
    exact (FrameTraceDesign.frameWork_append_assoc
      (List.replicate assignment.length cnfT)
      (List.replicate (Nat.succ suffixPrefix.length) cnfT)
      (cnfFinish ::
        (assignmentWorkSymbols assignment ++
          bad.workSymbol ::
            (cnfTokenWorkSymbols suffixPrefix ++
              [terminal.workSymbol])))).symm
  rw [badStartShape] at badRun
  have complete := workRunExact?_compose cnfWorkMachine
    (2 + (frameOneFoldSteps [] [] (first :: rest) +
      frameOneTerminalSteps (first :: rest)))
    (frameTwoInteriorBadSteps assignment suffixPrefix.length)
    _ _ _ throughFrame badRun
  refine ⟨tape, ?_⟩
  rw [tapeShape, tokenShape]
  unfold pairedTokenLayoutTerminal
  rw [token_length_append_constructive]
  rw [assignmentValueTokens_length]
  rw [assignmentReplicate_add]
  rw [cnfTokenWorkSymbols_append]
  rw [assignmentValueTokens_workSymbols]
  unfold assignmentInteriorRejectSteps
  rw [assignmentReplicate_cons_length first rest cnfT]
  rw [assignmentTokenWorkSymbols_cons first rest]
  rw [assignmentTokenWorkSymbols_cons bad suffixPrefix]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  repeat' rw [assignmentTape_cons_append]
  repeat' rw [FrameTraceDesign.frameWork_append_assoc]
  have badLength : (bad :: suffixPrefix).length =
      Nat.succ suffixPrefix.length := rfl
  rw [badLength]
  rw [FrameTraceDesign.frameWork_append_assoc
    (List.replicate assignment.length cnfT)
    (List.replicate (Nat.succ suffixPrefix.length) cnfT)
    (cnfFinish ::
      (assignmentWorkSymbols assignment ++
        bad.workSymbol ::
          (cnfTokenWorkSymbols suffixPrefix ++ [terminal.workSymbol])))]
    at complete
  exact complete

theorem tokenList_snoc (first : CNFToken) (rest : List CNFToken) :
    ∃ front terminal, first :: rest = front ++ [terminal] := by
  induction rest generalizing first with
  | nil => exact ⟨[], first, rfl⟩
  | cons next suffix ih =>
      rcases ih next with ⟨front, terminal, shape⟩
      exact ⟨first :: front, terminal, congrArg (List.cons first) shape⟩

private theorem assignmentList_length_append {α : Type}
    (left right : List α) :
    (left ++ right).length = left.length + right.length := by
  induction left with
  | nil => exact (Nat.zero_add right.length).symm
  | cons item rest ih =>
      change Nat.succ (rest ++ right).length =
        Nat.succ rest.length + right.length
      rw [Nat.succ_add]
      exact congrArg Nat.succ ih

private theorem assignmentList_append_nil {α : Type}
    (items : List α) : items ++ [] = items := by
  induction items with
  | nil => rfl
  | cons item rest ih => exact congrArg (List.cons item) ih

private theorem frameOneIterationSteps_congr_lengths
    (doneCounter₁ restCounter₁ donePayload₁ : List WorkSymbol)
    (doneCounter₂ restCounter₂ donePayload₂ : List WorkSymbol)
    (doneCounterLength : doneCounter₁.length = doneCounter₂.length)
    (restCounterLength : restCounter₁.length = restCounter₂.length)
    (donePayloadLength : donePayload₁.length = donePayload₂.length) :
    frameOneIterationSteps doneCounter₁ restCounter₁ donePayload₁ =
      frameOneIterationSteps doneCounter₂ restCounter₂ donePayload₂ := by
  unfold frameOneIterationSteps
  rw [assignmentList_length_append, assignmentList_length_append]
  rw [doneCounterLength, restCounterLength, donePayloadLength]
  rw [show (cnfMarkFalse :: restCounter₁).length =
      (cnfMarkFalse :: restCounter₂).length from
    congrArg Nat.succ restCounterLength]

/-- The malformed-frame prefix is literally no more expensive than the
corresponding prefix of a successful frame whose assignment is extended by
an arbitrary tail of the same length as the still-unprocessed counter. -/
theorem frameTwoPrefixSteps_le_fold_append
    (restCounter : List WorkSymbol) (tail : BitString)
    (sameLength : restCounter.length = tail.length)
    (doneCounter donePayload : List WorkSymbol)
    (assignment : BitString) :
    frameTwoPrefixSteps restCounter doneCounter donePayload assignment ≤
      frameTwoFoldSteps doneCounter donePayload (assignment ++ tail) := by
  induction assignment generalizing doneCounter donePayload with
  | nil =>
      change 0 ≤ frameTwoFoldSteps doneCounter donePayload tail
      exact Nat.zero_le _
  | cons value rest ih =>
      have restLength :
          (List.replicate rest.length cnfT ++ restCounter).length =
            (List.replicate (rest ++ tail).length cnfT).length := by
        rw [assignmentList_length_append]
        rw [length_replicate_workSymbol, length_replicate_workSymbol]
        rw [assignmentList_length_append, sameLength]
      have iterationShape := frameOneIterationSteps_congr_lengths
        doneCounter
        (List.replicate rest.length cnfT ++ restCounter)
        donePayload doneCounter
        (List.replicate (rest ++ tail).length cnfT)
        donePayload rfl restLength rfl
      change
        frameOneIterationSteps doneCounter
            (List.replicate rest.length cnfT ++ restCounter) donePayload +
          frameTwoPrefixSteps restCounter
            (doneCounter ++ [cnfMarkFalse])
            (donePayload ++ [markedAssignmentValueWorkSymbol value]) rest ≤
        frameOneIterationSteps doneCounter
            (List.replicate (rest ++ tail).length cnfT) donePayload +
          frameTwoFoldSteps (doneCounter ++ [cnfMarkFalse])
            (donePayload ++ [markedAssignmentValueWorkSymbol value])
            (rest ++ tail)
      rw [iterationShape]
      exact Nat.add_le_add_left
        (ih (doneCounter ++ [cnfMarkFalse])
          (donePayload ++ [markedAssignmentValueWorkSymbol value])) _

theorem frameTwoTerminalBadSteps_le_success
    (assignment : BitString) :
    frameTwoTerminalBadSteps assignment ≤
      frameTwoFoldSteps [] [] assignment +
        frameTwoTerminalSteps assignment := by
  have prefixBound := frameTwoPrefixSteps_le_fold_append
    ([] : List WorkSymbol) ([] : BitString) rfl [] [] assignment
  have terminalCore :
      (((assignment.length + 1) + assignment.length) + 1) ≤
        frameTwoTerminalSteps assignment := by
    unfold frameTwoTerminalSteps
    have first := Nat.le_add_right
      (((assignment.length + 1) + assignment.length) + 1) 1
    have second := Nat.le_trans first
      (Nat.le_add_right
        ((((assignment.length + 1) + assignment.length) + 1) + 1) 1)
    have third := Nat.le_trans second
      (Nat.le_add_right
        (((((assignment.length + 1) + assignment.length) + 1) + 1) + 1)
        assignment.length)
    exact Nat.le_trans third
      (Nat.le_add_right
        ((((((assignment.length + 1) + assignment.length) + 1) + 1) + 1) +
          assignment.length) 1)
  have combined := Nat.add_le_add prefixBound terminalCore
  unfold frameTwoTerminalBadSteps at combined
  rw [assignmentList_append_nil] at combined
  repeat' rw [Nat.add_assoc] at combined
  unfold frameTwoTerminalBadSteps
  repeat' rw [Nat.add_assoc]
  exact combined

def assignmentInteriorDummy
    (assignment : BitString) (suffixPrefixLength : Nat) : BitString :=
  assignment ++ List.replicate (Nat.succ suffixPrefixLength) false

theorem assignmentInteriorDummy_length
    (assignment : BitString) (suffixPrefixLength : Nat) :
    (assignmentInteriorDummy assignment suffixPrefixLength).length =
      assignment.length + Nat.succ suffixPrefixLength := by
  unfold assignmentInteriorDummy
  rw [assignmentList_length_append]
  rw [BitString.length_replicate_constructive]

theorem frameTwoInteriorBadSteps_le_success
    (assignment : BitString) (suffixPrefixLength : Nat) :
    frameTwoInteriorBadSteps assignment suffixPrefixLength ≤
      frameTwoFoldSteps [] []
          (assignmentInteriorDummy assignment suffixPrefixLength) +
        frameTwoTerminalSteps
          (assignmentInteriorDummy assignment suffixPrefixLength) := by
  let restCounter :=
    List.replicate (Nat.succ suffixPrefixLength) cnfT
  let tail : BitString :=
    List.replicate (Nat.succ suffixPrefixLength) false
  have restCounterLength : restCounter.length = tail.length := by
    unfold restCounter tail
    rw [length_replicate_workSymbol]
    rw [BitString.length_replicate_constructive]
  have prefixBound := frameTwoPrefixSteps_le_fold_append restCounter tail
    restCounterLength [] [] assignment
  have dummyShape : assignmentInteriorDummy assignment suffixPrefixLength =
      assignment ++ tail := by rfl
  rw [← dummyShape] at prefixBound
  let d := assignment.length + Nat.succ suffixPrefixLength
  have assignmentToD : assignment.length ≤ d := by
    unfold d
    exact Nat.le_add_right assignment.length
      (Nat.succ suffixPrefixLength)
  have assignmentOneToDOne : assignment.length + 1 ≤ d + 1 :=
    Nat.add_le_add_right assignmentToD 1
  have doubledBound :
      (assignment.length + 1) + (d + 1) ≤
        (d + 1) + (d + 1) :=
    Nat.add_le_add_right assignmentOneToDOne (d + 1)
  have remainderShape :
      (((((assignment.length + 1) + suffixPrefixLength) + 1) +
          assignment.length) + 1) =
        (assignment.length + 1) + (d + 1) := by
    unfold d
    rw [Nat.add_assoc (assignment.length + 1) suffixPrefixLength 1]
    rw [Nat.add_assoc (assignment.length + 1)
      (suffixPrefixLength + 1) assignment.length]
    rw [Nat.add_assoc (assignment.length + 1)
      ((suffixPrefixLength + 1) + assignment.length) 1]
    rw [Nat.add_comm (suffixPrefixLength + 1) assignment.length]
  have terminalCoreShape :
      (((d + 1) + d) + 1) = (d + 1) + (d + 1) := by
    exact Nat.add_assoc (d + 1) d 1
  have remainderToCore :
      (((((assignment.length + 1) + suffixPrefixLength) + 1) +
          assignment.length) + 1) ≤
        (((d + 1) + d) + 1) := by
    rw [remainderShape, terminalCoreShape]
    exact doubledBound
  have first := Nat.le_trans remainderToCore
    (Nat.le_add_right (((d + 1) + d) + 1) 1)
  have second := Nat.le_trans first
    (Nat.le_add_right ((((d + 1) + d) + 1) + 1) 1)
  have third := Nat.le_trans second
    (Nat.le_add_right (((((d + 1) + d) + 1) + 1) + 1) d)
  have fullD := Nat.le_trans third
    (Nat.le_add_right ((((((d + 1) + d) + 1) + 1) + 1) + d) 1)
  have dummyLength :
      (assignmentInteriorDummy assignment suffixPrefixLength).length = d := by
    unfold d
    exact assignmentInteriorDummy_length assignment suffixPrefixLength
  have remainderBound :
      (((((assignment.length + 1) + suffixPrefixLength) + 1) +
          assignment.length) + 1) ≤
        frameTwoTerminalSteps
          (assignmentInteriorDummy assignment suffixPrefixLength) := by
    unfold frameTwoTerminalSteps
    rw [dummyLength]
    exact fullD
  have combined := Nat.add_le_add prefixBound remainderBound
  unfold restCounter at combined
  repeat' rw [Nat.add_assoc] at combined
  unfold frameTwoInteriorBadSteps
  repeat' rw [Nat.add_assoc]
  exact combined

theorem assignmentTerminalRejectSteps_le_success
    (formulaTokens : List CNFToken) (assignment : BitString) :
    assignmentTerminalRejectSteps formulaTokens assignment ≤
      frameSuccessSteps formulaTokens assignment := by
  unfold assignmentTerminalRejectSteps frameSuccessSteps
  exact Nat.add_le_add_left
    (frameTwoTerminalBadSteps_le_success assignment)
    (2 + (frameOneFoldSteps [] [] formulaTokens +
      frameOneTerminalSteps formulaTokens))

theorem assignmentInteriorRejectSteps_le_success
    (formulaTokens : List CNFToken) (assignment : BitString)
    (suffixPrefixLength : Nat) :
    assignmentInteriorRejectSteps formulaTokens assignment
        suffixPrefixLength ≤
      frameSuccessSteps formulaTokens
        (assignmentInteriorDummy assignment suffixPrefixLength) := by
  unfold assignmentInteriorRejectSteps frameSuccessSteps
  exact Nat.add_le_add_left
    (frameTwoInteriorBadSteps_le_success assignment suffixPrefixLength)
    (2 + (frameOneFoldSteps [] [] formulaTokens +
      frameOneTerminalSteps formulaTokens))

theorem frameSuccessSteps_withinPair_of_decoded_components
    (input certificate : BitString) (formula : CNFFormula)
    (tokens : List CNFToken) (dummyAssignment : BitString)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (tokensDecoded : decodeTokenPairs certificate = some tokens)
    (dummyToTokens : dummyAssignment.length ≤ tokens.length) :
    frameSuccessSteps (encodeFormulaTokens formula) dummyAssignment ≤
      cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) := by
  have inputShape := encodeFormula_of_decode input formula formulaDecoded
  have certificateShape := encodeTokenPairs_of_decode certificate tokens
    tokensDecoded
  have formulaTokenToInput : (encodeFormulaTokens formula).length ≤
      BitString.size input := by
    rw [← inputShape]
    unfold encodeFormula encodeCNF
    exact MalformedFuelDesign.tokenLength_le_encodedPairsBitSize
      (encodeCNFTokens formula) false
  have certificateTokenToCertificate : tokens.length ≤
      BitString.size certificate := by
    rw [← certificateShape]
    exact MalformedFuelDesign.tokenLength_le_encodedPairsSize tokens
  have dummyToCertificate : dummyAssignment.length ≤
      BitString.size certificate :=
    Nat.le_trans dummyToTokens certificateTokenToCertificate
  have combinedToComponents :
      (encodeFormulaTokens formula).length + dummyAssignment.length ≤
        BitString.size input + BitString.size certificate :=
    Nat.add_le_add formulaTokenToInput dummyToCertificate
  have combinedBound :
      (encodeFormulaTokens formula).length + dummyAssignment.length ≤
        BitString.size (BitString.pair input certificate) :=
    Nat.le_trans combinedToComponents
      (MalformedFuelDesign.componentSizes_le_pairSize input certificate)
  have inputPos : 1 ≤ BitString.size input := by
    rw [← inputShape]
    unfold encodeFormula encodeCNF
    exact MalformedFuelDesign.one_le_encodedPairsBitSize
      (encodeCNFTokens formula) false
  have fiveSpan :=
    MalformedFuelDesign.five_le_shiftedPairSpan_of_inputPos
      input certificate inputPos
  exact frameSuccessSteps_le_singlePhase
    (BitString.size (BitString.pair input certificate))
    (encodeFormulaTokens formula) dummyAssignment combinedBound fiveSpan

def pairedEmptyCertificateLayout
    (formulaTokens : List CNFToken) : List WorkSymbol :=
  List.replicate formulaTokens.length cnfT ++
    cnfFinish :: (cnfTokenWorkSymbols formulaTokens ++ [cnfF])

theorem encodeWorkRight_pairedEmptyCertificateLayout
    (formulaTokens : List CNFToken) :
    encodeWorkRight (pairedEmptyCertificateLayout formulaTokens) =
      (BitString.pair (paddedFormulaTokenBits formulaTokens) []).map
        TapeSymbol.ofBool := by
  unfold pairedEmptyCertificateLayout
  rw [encodeWorkRight_append]
  rw [assignmentEncodeWorkRight_replicate_true]
  change List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
      TapeSymbol.one :: TapeSymbol.zero ::
        encodeWorkRight (cnfTokenWorkSymbols formulaTokens ++ [cnfF]) = _
  rw [encodeWorkRight_append]
  rw [encodeWorkRight_cnfTokenWorkSymbols]
  unfold BitString.pair BitString.frame paddedFormulaTokenBits
  rw [assignmentMapOfBool_append]
  rw [assignmentMapOfBool_append]
  rw [assignmentMapOfBool_replicate_true]
  rw [BitString.length_append_constructive]
  rw [encodeTokenPairs_length]
  rw [List.length_singleton]
  rw [assignmentReplicate_one_succ_tail]
  rw [assignmentMapOfBool_false_cons]
  rw [assignmentMapOfBool_append (encodeTokenPairs formulaTokens) [false]]
  rw [assignmentMapOfBool_false_singleton]
  have cnfFEncoded : encodeWorkRight [cnfF] =
      [TapeSymbol.zero, TapeSymbol.zero] := rfl
  rw [cnfFEncoded]
  have emptyFrameMapped :
      (List.replicate ([] : BitString).length true ++ [false]).map
          TapeSymbol.ofBool =
        [TapeSymbol.zero] := rfl
  rw [emptyFrameMapped]
  repeat' rw [assignmentTape_cons_append]
  repeat' rw [assignmentTape_append_assoc]
  have tailShape :
      List.map TapeSymbol.ofBool (encodeTokenPairs formulaTokens) ++
          [TapeSymbol.zero, TapeSymbol.zero] =
        (List.map TapeSymbol.ofBool (encodeTokenPairs formulaTokens) ++
          [TapeSymbol.zero]) ++ [TapeSymbol.zero] := by
    exact (assignmentTape_append_assoc
      (List.map TapeSymbol.ofBool (encodeTokenPairs formulaTokens))
      [TapeSymbol.zero] [TapeSymbol.zero]).symm
  exact congrArg
    (fun tail =>
      List.replicate (2 * formulaTokens.length) TapeSymbol.one ++
        TapeSymbol.one :: TapeSymbol.zero :: tail)
    tailShape

theorem packWorkSymbols_pairedEmptyCertificateLayout
    (formulaTokens : List CNFToken) :
    packWorkSymbols
        ((BitString.pair (paddedFormulaTokenBits formulaTokens) []).map
          TapeSymbol.ofBool) =
      pairedEmptyCertificateLayout formulaTokens := by
  have encoded := encodeWorkRight_pairedEmptyCertificateLayout formulaTokens
  have packed := congrArg packWorkSymbols encoded
  rw [packWorkSymbols_encodeWorkRight] at packed
  exact packed.symm

theorem pairedWorkTape_empty_certificate_shape
    (input : BitString) (formula : CNFFormula)
    (formulaDecoded : decodeEncodedCNF input = some formula) :
    pairedWorkTape input [] =
      WorkTape.ofSymbols
        (pairedEmptyCertificateLayout (encodeFormulaTokens formula)) := by
  have formulaShape := encodeFormula_of_decode input formula formulaDecoded
  rw [← formulaShape]
  rw [encodeFormula_eq_padded_tokens]
  unfold pairedWorkTape
  change WorkTape.ofSymbols
      (packWorkSymbols
        ((BitString.pair
          (paddedFormulaTokenBits (encodeFormulaTokens formula)) []).map
            TapeSymbol.ofBool)) = _
  rw [packWorkSymbols_pairedEmptyCertificateLayout]

theorem frameOne_fBoundary_terminal_exact
    (tokens : List CNFToken) (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine (frameOneBadBoundarySteps tokens)
        (frameOneBoundaryFoldFinal [] [] tokens cnfF suffix) =
      some
        (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft (frameOneMarkedTokens tokens)
            (cnfFinish ::
              pushWorkLeft
                (List.replicate tokens.length cnfMarkFalse)
                [cnfRootGuard]))
          (cnfF :: suffix)) := by
  have counterRun := frameOne_findCounter_markFalse_scan tokens.length
    [cnfRootGuard]
    (cnfFinish :: frameOneMarkedTokens tokens ++ cnfF :: suffix)
  have finishRun := workRunExact?_one_of_step cnfWorkMachine _ _
    (frameOne_findCounter_finish_step
      (pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard])
      (frameOneMarkedTokens tokens ++ cnfF :: suffix))
  have payloadRun := frameOne_checkPayload_marked_scan tokens
    (cnfFinish ::
      pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
        [cnfRootGuard]) (cnfF :: suffix)
  have rejectRun := frameOneCheckPayload_reject_run
    (pushWorkLeft (frameOneMarkedTokens tokens)
      (cnfFinish ::
        pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
          [cnfRootGuard])) suffix cnfF (by
            intro allowed
            cases allowed)
  have throughFinish := workRunExact?_compose cnfWorkMachine
    tokens.length 1 _ _ _ counterRun finishRun
  have throughPayload := workRunExact?_compose cnfWorkMachine
    (tokens.length + 1) tokens.length _ _ _ throughFinish payloadRun
  unfold frameOneBoundaryFoldFinal frameOneBadBoundarySteps
  exact workRunExact?_compose cnfWorkMachine
    ((tokens.length + 1) + tokens.length) 1 _ _ _
    throughPayload rejectRun

theorem frameOne_fBoundary_exact
    (tokens : List CNFToken) (suffix : List WorkSymbol) :
    workRunExact? cnfWorkMachine
        (frameOneFoldSteps [] [] tokens + frameOneBadBoundarySteps tokens)
        (frameOneBoundaryFoldStart [] [] tokens cnfF suffix) =
      some
        (workConfigAtWord CNFWorkState.reject
          (pushWorkLeft (frameOneMarkedTokens tokens)
            (cnfFinish ::
              pushWorkLeft
                (List.replicate tokens.length cnfMarkFalse)
                [cnfRootGuard]))
          (cnfF :: suffix)) := by
  have foldRun := frameOne_boundary_fold_exact [] [] tokens cnfF suffix
    (by intro symbol member; contradiction)
    (by intro symbol member; contradiction)
  have terminalRun := frameOne_fBoundary_terminal_exact tokens suffix
  exact workRunExact?_compose cnfWorkMachine
    (frameOneFoldSteps [] [] tokens) (frameOneBadBoundarySteps tokens)
    _ _ _ foldRun terminalRun

theorem assignment_empty_full_exact
    (input : BitString) (formula : CNFFormula)
    (formulaDecoded : decodeEncodedCNF input = some formula) :
    ∃ steps tape,
      steps ≤ frameSuccessSteps (encodeFormulaTokens formula) [] ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input [])) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have tapeShape := pairedWorkTape_empty_certificate_shape input formula
    formulaDecoded
  rcases encodeFormulaTokens_cons formula with ⟨first, rest, tokenShape⟩
  let tokens := first :: rest
  have bootRun := boot_t_exact
    (List.replicate rest.length cnfT ++
      cnfFinish ::
        (first.workSymbol ::
          (cnfTokenWorkSymbols rest ++ [cnfF])))
  have rejectRun := frameOne_fBoundary_exact tokens []
  rw [frameOneBoundaryFoldStart_cons] at rejectRun
  have complete := workRunExact?_compose cnfWorkMachine 2
    (frameOneFoldSteps [] [] tokens + frameOneBadBoundarySteps tokens)
    _ _ _ bootRun rejectRun
  let steps := 2 +
    (frameOneFoldSteps [] [] tokens + frameOneBadBoundarySteps tokens)
  have terminalBound :=
    MalformedFuelDesign.frameOneBadBoundarySteps_le_terminal tokens
  have firstBound : steps ≤
      2 + (frameOneFoldSteps [] [] tokens +
        frameOneTerminalSteps tokens) :=
    Nat.add_le_add_left
      (Nat.add_le_add_left terminalBound
        (frameOneFoldSteps [] [] tokens)) 2
  have secondBound :
      2 + (frameOneFoldSteps [] [] tokens + frameOneTerminalSteps tokens) ≤
        frameSuccessSteps tokens [] := by
    unfold frameSuccessSteps
    exact Nat.le_add_right _
      (frameTwoFoldSteps [] [] [] + frameTwoTerminalSteps [])
  have secondBoundFormula :
      2 + (frameOneFoldSteps [] [] tokens + frameOneTerminalSteps tokens) ≤
        frameSuccessSteps (encodeFormulaTokens formula) [] := by
    rw [tokenShape]
    exact secondBound
  refine ⟨steps,
    (workConfigAtWord CNFWorkState.reject
      (pushWorkLeft (frameOneMarkedTokens tokens)
        (cnfFinish ::
          pushWorkLeft (List.replicate tokens.length cnfMarkFalse)
            [cnfRootGuard])) [cnfF]).tape,
    Nat.le_trans firstBound secondBoundFormula, ?_⟩
  rw [tapeShape]
  rw [tokenShape]
  unfold pairedEmptyCertificateLayout tokens steps
  exact complete

/-- Every successfully pair-decoded but assignment-grammar-invalid
certificate has an exact rejecting run.  The three normal forms correspond
to an empty certificate, a bad terminal token, or an interior separator or
finish token. -/
theorem assignmentGrammarFailure_full_exact
    (input certificate : BitString) (formula : CNFFormula)
    (tokens : List CNFToken)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (tokensDecoded : decodeTokenPairs certificate = some tokens)
    (grammarFailed : decodeAssignmentTokens tokens = none) :
    ∃ steps tape,
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have bitsShape := encodeTokenPairs_of_decode certificate tokens
    tokensDecoded
  have failure := assignmentGrammarFailure_of_decode_none tokens
    grammarFailed
  have normal := assignmentGrammarFailure_normal failure
  cases normal with
  | empty =>
      have certificateEmpty : certificate = [] := bitsShape.symm
      rw [certificateEmpty]
      rcases assignment_empty_full_exact input formula formulaDecoded with
        ⟨steps, tape, stepBound, exactRun⟩
      exact ⟨steps, tape, exactRun⟩
  | terminalF values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.f.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .f formulaDecoded certificateShape (Or.inl rfl) with
        ⟨tape, exactRun⟩
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, exactRun⟩
  | terminalT values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.t.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .t formulaDecoded certificateShape (Or.inr (Or.inl rfl)) with
        ⟨tape, exactRun⟩
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, exactRun⟩
  | terminalSep values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.sep.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .sep formulaDecoded certificateShape (Or.inr (Or.inr rfl)) with
        ⟨tape, exactRun⟩
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, exactRun⟩
  | interiorSep values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .sep :: next :: rest =
            (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (assignmentTape_append_assoc
          (assignmentValueTokens values) (.sep :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [assignmentEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases assignment_interior_full_exact input certificate formula values
          .sep suffixPrefix terminal formulaDecoded certificateShape
          (Or.inl rfl) with
        ⟨tape, exactRun⟩
      exact ⟨assignmentInteriorRejectSteps
        (encodeFormulaTokens formula) values suffixPrefix.length,
        tape, exactRun⟩
  | interiorFinish values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .finish :: next :: rest =
            (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (assignmentTape_append_assoc
          (assignmentValueTokens values) (.finish :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [assignmentEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases assignment_interior_full_exact input certificate formula values
          .finish suffixPrefix terminal formulaDecoded certificateShape
          (Or.inr rfl) with
        ⟨tape, exactRun⟩
      exact ⟨assignmentInteriorRejectSteps
        (encodeFormulaTokens formula) values suffixPrefix.length,
        tape, exactRun⟩

/-- The complete assignment-grammar failure contract used by universal
composition: exact rejection within one pair-sized phase. -/
theorem assignmentGrammarFailure_rejects_withinPairSinglePhase
    (input certificate : BitString) (formula : CNFFormula)
    (tokens : List CNFToken)
    (formulaDecoded : decodeEncodedCNF input = some formula)
    (tokensDecoded : decodeTokenPairs certificate = some tokens)
    (grammarFailed : decodeAssignmentTokens tokens = none) :
    ∃ steps tape,
      steps ≤ cnfSinglePhaseBudget
        (BitString.size (BitString.pair input certificate)) ∧
      workRunExact? cnfWorkMachine steps
          (workStartConfiguration cnfWorkMachine
            (pairedWorkTape input certificate)) =
        some
          ({ state := CNFWorkState.reject, tape := tape } :
            WorkConfiguration) := by
  have bitsShape := encodeTokenPairs_of_decode certificate tokens
    tokensDecoded
  have failure := assignmentGrammarFailure_of_decode_none tokens
    grammarFailed
  have normal := assignmentGrammarFailure_normal failure
  cases normal with
  | empty =>
      have certificateEmpty : certificate = [] := bitsShape.symm
      have emptyTokensDecoded : decodeTokenPairs [] =
          some ([] : List CNFToken) := by
        rw [← certificateEmpty]
        exact tokensDecoded
      rw [certificateEmpty]
      rcases assignment_empty_full_exact input formula formulaDecoded with
        ⟨steps, tape, successCost, exactRun⟩
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components
          input [] formula [] [] formulaDecoded emptyTokensDecoded
          (Nat.zero_le _)
      exact ⟨steps, tape, Nat.le_trans successCost successBound, exactRun⟩
  | terminalF values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.f.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .f formulaDecoded certificateShape (Or.inl rfl) with
        ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.f]).length := by
        rw [assignmentList_length_append]
        rw [assignmentValueTokens_length]
        change values.length ≤ values.length + 1
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components input certificate
          formula (assignmentValueTokens values ++ [CNFToken.f]) values
          formulaDecoded tokensDecoded dummyToTokens
      have stepBound := Nat.le_trans
        (assignmentTerminalRejectSteps_le_success
          (encodeFormulaTokens formula) values) successBound
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, stepBound, exactRun⟩
  | terminalT values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.t.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .t formulaDecoded certificateShape (Or.inr (Or.inl rfl)) with
        ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.t]).length := by
        rw [assignmentList_length_append]
        rw [assignmentValueTokens_length]
        change values.length ≤ values.length + 1
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components input certificate
          formula (assignmentValueTokens values ++ [CNFToken.t]) values
          formulaDecoded tokensDecoded dummyToTokens
      have stepBound := Nat.le_trans
        (assignmentTerminalRejectSteps_le_success
          (encodeFormulaTokens formula) values) successBound
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, stepBound, exactRun⟩
  | terminalSep values =>
      have certificateShape : certificate =
          encodeTokenPairs (assignmentValueTokens values) ++
            CNFToken.sep.bits := by
        rw [encodeTokenPairs_append] at bitsShape
        exact bitsShape.symm
      rcases assignment_terminal_full_exact input certificate formula values
          .sep formulaDecoded certificateShape (Or.inr (Or.inr rfl)) with
        ⟨tape, exactRun⟩
      have dummyToTokens : values.length ≤
          (assignmentValueTokens values ++ [CNFToken.sep]).length := by
        rw [assignmentList_length_append]
        rw [assignmentValueTokens_length]
        change values.length ≤ values.length + 1
        exact Nat.le_add_right values.length 1
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components input certificate
          formula (assignmentValueTokens values ++ [CNFToken.sep]) values
          formulaDecoded tokensDecoded dummyToTokens
      have stepBound := Nat.le_trans
        (assignmentTerminalRejectSteps_le_success
          (encodeFormulaTokens formula) values) successBound
      exact ⟨assignmentTerminalRejectSteps
        (encodeFormulaTokens formula) values, tape, stepBound, exactRun⟩
  | interiorSep values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .sep :: next :: rest =
            (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (assignmentTape_append_assoc
          (assignmentValueTokens values) (.sep :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [assignmentEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .sep :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases assignment_interior_full_exact input certificate formula values
          .sep suffixPrefix terminal formulaDecoded certificateShape
          (Or.inl rfl) with
        ⟨tape, exactRun⟩
      have dummyToTokens :
          (assignmentInteriorDummy values suffixPrefix.length).length ≤
            (assignmentValueTokens values ++ .sep :: next :: rest).length := by
        rw [tokenShape]
        rw [assignmentInteriorDummy_length]
        rw [assignmentList_length_append, assignmentList_length_append]
        rw [assignmentValueTokens_length]
        change values.length + Nat.succ suffixPrefix.length ≤
          (values.length + Nat.succ suffixPrefix.length) + 1
        exact Nat.le_add_right _ 1
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components input certificate
          formula (assignmentValueTokens values ++ .sep :: next :: rest)
          (assignmentInteriorDummy values suffixPrefix.length)
          formulaDecoded tokensDecoded dummyToTokens
      have stepBound := Nat.le_trans
        (assignmentInteriorRejectSteps_le_success
          (encodeFormulaTokens formula) values suffixPrefix.length)
        successBound
      exact ⟨assignmentInteriorRejectSteps
        (encodeFormulaTokens formula) values suffixPrefix.length,
        tape, stepBound, exactRun⟩
  | interiorFinish values next rest =>
      rcases tokenList_snoc next rest with
        ⟨suffixPrefix, terminal, tailShape⟩
      have tokenShape :
          assignmentValueTokens values ++ .finish :: next :: rest =
            (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
              [terminal] := by
        rw [tailShape]
        exact (assignmentTape_append_assoc
          (assignmentValueTokens values) (.finish :: suffixPrefix)
          [terminal]).symm
      have encodedShape := bitsShape
      rw [tokenShape, encodeTokenPairs_append] at encodedShape
      rw [assignmentEncodeTokenPairs_singleton] at encodedShape
      have certificateShape : certificate =
          encodeTokenPairs
              (assignmentValueTokens values ++ .finish :: suffixPrefix) ++
            terminal.bits := encodedShape.symm
      rcases assignment_interior_full_exact input certificate formula values
          .finish suffixPrefix terminal formulaDecoded certificateShape
          (Or.inr rfl) with
        ⟨tape, exactRun⟩
      have dummyToTokens :
          (assignmentInteriorDummy values suffixPrefix.length).length ≤
            (assignmentValueTokens values ++ .finish :: next :: rest).length := by
        rw [tokenShape]
        rw [assignmentInteriorDummy_length]
        rw [assignmentList_length_append, assignmentList_length_append]
        rw [assignmentValueTokens_length]
        change values.length + Nat.succ suffixPrefix.length ≤
          (values.length + Nat.succ suffixPrefix.length) + 1
        exact Nat.le_add_right _ 1
      have successBound :=
        frameSuccessSteps_withinPair_of_decoded_components input certificate
          formula (assignmentValueTokens values ++ .finish :: next :: rest)
          (assignmentInteriorDummy values suffixPrefix.length)
          formulaDecoded tokensDecoded dummyToTokens
      have stepBound := Nat.le_trans
        (assignmentInteriorRejectSteps_le_success
          (encodeFormulaTokens formula) values suffixPrefix.length)
        successBound
      exact ⟨assignmentInteriorRejectSteps
        (encodeFormulaTokens formula) values suffixPrefix.length,
        tape, stepBound, exactRun⟩

end AssignmentGrammarFailureDesign
end PNP.Concrete
