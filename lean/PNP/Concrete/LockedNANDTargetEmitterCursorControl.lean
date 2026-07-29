/-
Copyright (c) 2026 PNP Labs.

Literal cursor installation and restoration for the grammar-only locked-NAND
target emitter.

The retained source is immutable except while the controller is paused at one
packed source cell.  At that point this finite machine replaces the cell by a
dedicated contextual cursor marker, rewinds to the source-left boundary, and
halts on the first source cell.  After a cursor-aware token append, the second
entry scans back to the marker, restores the statically selected packed cell,
and advances once.  No source coordinate or target word is supplied by the
caller.
-/

import PNP.Concrete.LockedNANDTargetEmitterMachine

namespace PNP.Concrete.LockedNAND.TargetEmitterCursorControl

open TargetEmitter

def cursorMark : WorkSymbol := WorkSymbol.oneBlank

def installState : Nat := 0
def rewindState : Nat := 1
def restoreState : Nat := 2
def installedState : Nat := 3
def restoredState : Nat := 4
def rejectState : Nat := 5
def deadState : Nat := 6

def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

def rules (original : WorkSymbol) : List WorkRule :=
  [ literalRule installState original
      rewindState cursorMark .left
  , literalRule rewindState WorkSymbol.zeroZero
      rewindState WorkSymbol.zeroZero .left
  , literalRule rewindState WorkSymbol.zeroOne
      rewindState WorkSymbol.zeroOne .left
  , literalRule rewindState WorkSymbol.oneZero
      rewindState WorkSymbol.oneZero .left
  , literalRule rewindState WorkSymbol.oneOne
      rewindState WorkSymbol.oneOne .left
  , literalRule rewindState sourceLeftBoundary
      installedState sourceLeftBoundary .right
  , literalRule restoreState WorkSymbol.zeroZero
      restoreState WorkSymbol.zeroZero .right
  , literalRule restoreState WorkSymbol.zeroOne
      restoreState WorkSymbol.zeroOne .right
  , literalRule restoreState WorkSymbol.oneZero
      restoreState WorkSymbol.oneZero .right
  , literalRule restoreState WorkSymbol.oneOne
      restoreState WorkSymbol.oneOne .right
  , literalRule restoreState cursorMark
      restoredState original .right
  ]

def installMachine (original : WorkSymbol) : WorkMachine :=
  { rules := rules original
    startState := installState
    acceptState := installedState
    rejectState := rejectState }

def restoreMachine (original : WorkSymbol) : WorkMachine :=
  { rules := rules original
    startState := restoreState
    acceptState := restoredState
    rejectState := rejectState }

theorem rules_length (original : WorkSymbol) :
    (rules original).length = 11 := by
  rfl

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_pairwise (original : WorkSymbol) :
    (rules original).Pairwise QueryDistinct := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;>
    simp [rules, literalRule, QueryDistinct,
      sourceLeftBoundary, cursorMark, installState, rewindState,
      restoreState, WorkSymbol.blankZero, WorkSymbol.oneBlank,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne]

theorem install_start_ne_accept (original : WorkSymbol) :
    (installMachine original).startState ≠
      (installMachine original).acceptState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem install_start_ne_reject (original : WorkSymbol) :
    (installMachine original).startState ≠
      (installMachine original).rejectState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem install_accept_ne_reject (original : WorkSymbol) :
    (installMachine original).acceptState ≠
      (installMachine original).rejectState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem restore_start_ne_accept (original : WorkSymbol) :
    (restoreMachine original).startState ≠
      (restoreMachine original).acceptState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem restore_start_ne_reject (original : WorkSymbol) :
    (restoreMachine original).startState ≠
      (restoreMachine original).rejectState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem restore_accept_ne_reject (original : WorkSymbol) :
    (restoreMachine original).acceptState ≠
      (restoreMachine original).rejectState := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_installed (original symbol : WorkSymbol) :
    findWorkRule (rules original) installedState symbol = none := by
  rcases original with ⟨originalFirst, originalSecond⟩
  rcases symbol with ⟨first, second⟩
  cases originalFirst <;> cases originalSecond <;>
    cases first <;> cases second <;> decide

theorem no_rule_at_restored (original symbol : WorkSymbol) :
    findWorkRule (rules original) restoredState symbol = none := by
  rcases original with ⟨originalFirst, originalSecond⟩
  rcases symbol with ⟨first, second⟩
  cases originalFirst <;> cases originalSecond <;>
    cases first <;> cases second <;> decide

theorem no_rule_at_reject (original symbol : WorkSymbol) :
    findWorkRule (rules original) rejectState symbol = none := by
  rcases original with ⟨originalFirst, originalSecond⟩
  rcases symbol with ⟨first, second⟩
  cases originalFirst <;> cases originalSecond <;>
    cases first <;> cases second <;> decide

def tapeAtWord (left : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] =>
      { left := left
        head := WorkSymbol.blank
        right := [] }
  | head :: rest =>
      { left := left
        head := head
        right := rest }

def configAtWord (state : Nat) (left word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state
    tape := tapeAtWord left word }

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  match leftWord with
  | [] =>
      { state := state
        tape :=
          { left := []
            head := WorkSymbol.blank
            right := right } }
  | head :: left =>
      { state := state
        tape :=
          { left := left
            head := head
            right := right } }

private def pushLeft : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], far => far
  | head :: rest, far => pushLeft rest (head :: far)

private theorem pushLeft_eq_reverse_append
    (word far : List WorkSymbol) :
    pushLeft word far = word.reverse ++ far := by
  induction word generalizing far with
  | nil =>
      rfl
  | cons head rest ih =>
      simp only [pushLeft, ih, List.reverse_cons,
        List.append_assoc]
      rfl

private theorem exactRun_add (machine : WorkMachine)
    (first second : Nat) (initial middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first initial = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final := by
  induction first generalizing initial with
  | zero =>
      change some initial = some middle at hFirst
      have initialEq : initial = middle := Option.some.inj hFirst
      rw [Nat.zero_add, initialEq]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have tail :
              workRunExact? machine first next = some middle := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine initial with
             | none => none
             | some next =>
                 workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next tail

private theorem exactRun_one (machine : WorkMachine)
    (initial final : WorkConfiguration)
    (step : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change
    (match workStep? machine initial with
     | none => none
     | some next => some next) = some final
  rw [step]

private theorem find_install (original : WorkSymbol)
    (ordinary : PackedSymbol original) :
    findWorkRule (rules original) installState original =
      some
        (literalRule installState original
          rewindState cursorMark .left) := by
  cases ordinary <;> rfl

private theorem find_rewind_packed (original symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    findWorkRule (rules original) rewindState symbol =
      some
        (literalRule rewindState symbol
          rewindState symbol .left) := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> cases ordinary <;> rfl

private theorem find_rewind_boundary (original : WorkSymbol) :
    findWorkRule (rules original) rewindState sourceLeftBoundary =
      some
        (literalRule rewindState sourceLeftBoundary
          installedState sourceLeftBoundary .right) := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> rfl

private theorem find_restore_packed (original symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    findWorkRule (rules original) restoreState symbol =
      some
        (literalRule restoreState symbol
          restoreState symbol .right) := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> cases ordinary <;> rfl

private theorem find_restore_marker (original : WorkSymbol) :
    findWorkRule (rules original) restoreState cursorMark =
      some
        (literalRule restoreState cursorMark
          restoredState original .right) := by
  rcases original with ⟨first, second⟩
  cases first <;> cases second <;> rfl

private theorem rewind_packed_step (original symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol)
    (leftWord right : List WorkSymbol) :
    workStep? (installMachine original)
        (configAtLeftWord rewindState
          (symbol :: leftWord) right) =
      some
        (configAtLeftWord rewindState leftWord
          (symbol :: right)) := by
  have notHalted :
      (installMachine original).isHalted
        (configAtLeftWord rewindState
          (symbol :: leftWord) right) = false := by
    rfl
  calc
    workStep? (installMachine original)
        (configAtLeftWord rewindState
          (symbol :: leftWord) right) =
      some
        (applyWorkRule
          (literalRule rewindState symbol
            rewindState symbol .left)
          (configAtLeftWord rewindState
            (symbol :: leftWord) right)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_packed original symbol ordinary)
    _ = some
        (configAtLeftWord rewindState leftWord
          (symbol :: right)) := by
      cases leftWord <;> rfl

private theorem scanLeft_exact (original : WorkSymbol)
    (word leftSuffix right : List WorkSymbol)
    (packed : ∀ symbol, symbol ∈ word → PackedSymbol symbol) :
    workRunExact? (installMachine original) word.length
        (configAtLeftWord rewindState
          (word ++ leftSuffix) right) =
      some
        (configAtLeftWord rewindState leftSuffix
          (pushLeft word right)) := by
  induction word generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headPacked : PackedSymbol head :=
        packed head (List.Mem.head rest)
      have restPacked :
          ∀ symbol, symbol ∈ rest → PackedSymbol symbol := by
        intro symbol member
        exact packed symbol (List.Mem.tail head member)
      have step :
          workRunExact? (installMachine original) 1
              (configAtLeftWord rewindState
                (head :: rest ++ leftSuffix) right) =
            some
              (configAtLeftWord rewindState
                (rest ++ leftSuffix) (head :: right)) := by
        exact exactRun_one _ _ _
          (rewind_packed_step original head headPacked
            (rest ++ leftSuffix) right)
      have tail := ih (head :: right) restPacked
      have combined :=
        exactRun_add (installMachine original) 1 rest.length
          _ _ _ step tail
      simpa [pushLeft, Nat.add_comm] using combined

private theorem install_one (original : WorkSymbol)
    (left suffix : List WorkSymbol)
    (ordinary : PackedSymbol original)
    (leftNonempty : left ≠ []) :
    workRunExact? (installMachine original) 1
        (configAtWord installState left
          (original :: suffix)) =
      some
        (configAtLeftWord rewindState left
          (cursorMark :: suffix)) := by
  cases left with
  | nil =>
      contradiction
  | cons head rest =>
      apply exactRun_one
      have notHalted :
          (installMachine original).isHalted
            (configAtWord installState (head :: rest)
              (original :: suffix)) = false := by
        rfl
      calc
        workStep? (installMachine original)
            (configAtWord installState (head :: rest)
              (original :: suffix)) =
          some
            (applyWorkRule
              (literalRule installState original
                rewindState cursorMark .left)
              (configAtWord installState (head :: rest)
                (original :: suffix))) :=
          workStep?_eq_apply_of_find _ _ _ notHalted
            (find_install original ordinary)
        _ = some
            (configAtLeftWord rewindState (head :: rest)
              (cursorMark :: suffix)) := by
          rfl

private theorem rewind_boundary_step (original : WorkSymbol)
    (outsideLeft suffix : List WorkSymbol) :
    workRunExact? (installMachine original) 1
        (configAtLeftWord rewindState
          (sourceLeftBoundary :: outsideLeft) suffix) =
      some
        (configAtWord installedState
          (sourceLeftBoundary :: outsideLeft)
          (suffix)) := by
  apply exactRun_one
  have notHalted :
      (installMachine original).isHalted
        (configAtLeftWord rewindState
          (sourceLeftBoundary :: outsideLeft) suffix) = false := by
    rfl
  calc
    workStep? (installMachine original)
        (configAtLeftWord rewindState
          (sourceLeftBoundary :: outsideLeft) suffix) =
      some
        (applyWorkRule
          (literalRule rewindState sourceLeftBoundary
            installedState sourceLeftBoundary .right)
          (configAtLeftWord rewindState
            (sourceLeftBoundary :: outsideLeft) suffix)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_boundary original)
    _ = some
        (configAtWord installedState
          (sourceLeftBoundary :: outsideLeft) suffix) := by
      cases suffix <;> rfl

/-- Replace the selected packed source cell by the contextual cursor, rewind
over the exact packed prefix, and halt on the first retained source cell. -/
theorem install_exact (original : WorkSymbol)
    (before after outsideLeft suffix : List WorkSymbol)
    (ordinary : PackedSymbol original)
    (prefixPacked :
      ∀ symbol, symbol ∈ before → PackedSymbol symbol) :
    workRunExact? (installMachine original) (before.length + 2)
        (configAtWord installState
          (before.reverse ++ sourceLeftBoundary :: outsideLeft)
          (original :: after ++ suffix)) =
      some
        (configAtWord installedState
          (sourceLeftBoundary :: outsideLeft)
          (before ++ cursorMark :: after ++ suffix)) := by
  let marked :=
    configAtLeftWord rewindState
      (before.reverse ++ sourceLeftBoundary :: outsideLeft)
      (cursorMark :: after ++ suffix)
  have first :
      workRunExact? (installMachine original) 1
          (configAtWord installState
            (before.reverse ++ sourceLeftBoundary :: outsideLeft)
            (original :: after ++ suffix)) =
        some marked := by
    apply install_one original
      (before.reverse ++ sourceLeftBoundary :: outsideLeft)
      (after ++ suffix) ordinary
    intro impossible
    have lengthEqual := congrArg List.length impossible
    simp at lengthEqual
  let boundary :=
    configAtLeftWord rewindState
      (sourceLeftBoundary :: outsideLeft)
      (before ++ cursorMark :: after ++ suffix)
  have throughPrefix :
      workRunExact? (installMachine original) before.length marked =
        some boundary := by
    simpa [marked, boundary, List.append_assoc,
      pushLeft_eq_reverse_append] using
      scanLeft_exact original before.reverse
        (sourceLeftBoundary :: outsideLeft)
        (cursorMark :: after ++ suffix)
        (by
          intro symbol member
          exact prefixPacked symbol
            (by simpa using List.mem_reverse.mp member))
  have last :
      workRunExact? (installMachine original) 1 boundary =
        some
          (configAtWord installedState
            (sourceLeftBoundary :: outsideLeft)
            (before ++ cursorMark :: after ++ suffix)) := by
    simpa [boundary, List.append_assoc] using
      rewind_boundary_step original outsideLeft
        (before ++ cursorMark :: after ++ suffix)
  have firstTwo :=
    exactRun_add (installMachine original) 1 before.length
      _ marked boundary first throughPrefix
  have all :=
    exactRun_add (installMachine original) (1 + before.length) 1
      _ boundary _ firstTwo last
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using all

private theorem restore_scan_exact (original : WorkSymbol)
    (before : List WorkSymbol)
    (packed : ∀ symbol, symbol ∈ before → PackedSymbol symbol)
    (left suffix : List WorkSymbol) :
    workRunExact? (restoreMachine original) before.length
        (configAtWord restoreState left
          (before ++ cursorMark :: suffix)) =
      some
        (configAtWord restoreState
          (before.reverse ++ left)
          (cursorMark :: suffix)) := by
  induction before generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headPacked : PackedSymbol head :=
        packed head (List.Mem.head rest)
      have restPacked :
          ∀ symbol, symbol ∈ rest → PackedSymbol symbol := by
        intro symbol member
        exact packed symbol (List.Mem.tail head member)
      have step :
          workRunExact? (restoreMachine original) 1
              (configAtWord restoreState left
                (head :: rest ++ cursorMark :: suffix)) =
            some
              (configAtWord restoreState (head :: left)
                (rest ++ cursorMark :: suffix)) := by
        apply exactRun_one
        have notHalted :
            (restoreMachine original).isHalted
              (configAtWord restoreState left
                (head :: rest ++ cursorMark :: suffix)) = false := by
          rfl
        calc
          workStep? (restoreMachine original)
              (configAtWord restoreState left
                (head :: rest ++ cursorMark :: suffix)) =
            some
              (applyWorkRule
                (literalRule restoreState head
                  restoreState head .right)
                (configAtWord restoreState left
                  (head :: rest ++ cursorMark :: suffix))) :=
            workStep?_eq_apply_of_find _ _ _ notHalted
              (find_restore_packed original head headPacked)
          _ = some
              (configAtWord restoreState (head :: left)
                (rest ++ cursorMark :: suffix)) := by
            cases rest <;> rfl
      have tail :=
        ih restPacked (head :: left)
      have combined :=
        exactRun_add (restoreMachine original) 1 rest.length
          _ _ _ step tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem restore_marker_step (original : WorkSymbol)
    (left suffix : List WorkSymbol) :
    workRunExact? (restoreMachine original) 1
        (configAtWord restoreState left
          (cursorMark :: suffix)) =
      some
        (configAtWord restoredState
          (original :: left) suffix) := by
  apply exactRun_one
  have notHalted :
      (restoreMachine original).isHalted
        (configAtWord restoreState left
          (cursorMark :: suffix)) = false := by
    rfl
  calc
    workStep? (restoreMachine original)
        (configAtWord restoreState left
          (cursorMark :: suffix)) =
      some
        (applyWorkRule
          (literalRule restoreState cursorMark
            restoredState original .right)
          (configAtWord restoreState left
            (cursorMark :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_restore_marker original)
    _ = some
        (configAtWord restoredState
          (original :: left) suffix) := by
      cases suffix <;> rfl

/-- Starting at the first source cell, find the contextual cursor, restore its
statically known packed value, and advance to the following source cell. -/
theorem restore_exact (original : WorkSymbol)
    (before after outsideLeft : List WorkSymbol)
    (prefixPacked :
      ∀ symbol, symbol ∈ before → PackedSymbol symbol) :
    workRunExact? (restoreMachine original) (before.length + 1)
        (configAtWord restoreState
          (sourceLeftBoundary :: outsideLeft)
          (before ++ cursorMark :: after)) =
      some
        (configAtWord restoredState
          (original :: before.reverse ++
            sourceLeftBoundary :: outsideLeft)
          after) := by
  let atMarker :=
    configAtWord restoreState
      (before.reverse ++ sourceLeftBoundary :: outsideLeft)
      (cursorMark :: after)
  have scan :
      workRunExact? (restoreMachine original) before.length
          (configAtWord restoreState
            (sourceLeftBoundary :: outsideLeft)
            (before ++ cursorMark :: after)) =
        some atMarker := by
    simpa [atMarker] using
      restore_scan_exact original before prefixPacked
        (sourceLeftBoundary :: outsideLeft) after
  have final :
      workRunExact? (restoreMachine original) 1 atMarker =
        some
          (configAtWord restoredState
            (original :: before.reverse ++
              sourceLeftBoundary :: outsideLeft) after) := by
    simpa [atMarker, List.append_assoc] using
      restore_marker_step original
        (before.reverse ++ sourceLeftBoundary :: outsideLeft) after
  have all :=
    exactRun_add (restoreMachine original) before.length 1
      _ atMarker _ scan final
  exact all

theorem installed_halted (original : WorkSymbol)
    (tape : WorkTape) :
    (installMachine original).isHalted
      { state := installedState, tape := tape } = true := by
  rfl

theorem restored_halted (original : WorkSymbol)
    (tape : WorkTape) :
    (restoreMachine original).isHalted
      { state := restoredState, tape := tape } = true := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterCursorControl
