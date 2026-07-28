/-
Copyright (c) 2026 PNP Labs.

Total-trace infrastructure for the strict-v0 locked-NAND source parser.

This module isolates the two operational facts shared by every malformed
branch.  Once control enters cleanup, the machine first finds the installed
left guard, then erases the complete guarded finite word, and finally enters
the rejecting halt.  The exact transition count is retained.

The final section records the accepting predecessor and the semantic
invariant required by the all-input proof.  It deliberately does not claim
that the invariant has already been established for every parser state; that
exhaustive grammar argument is the remaining integration obligation.
-/

import PNP.Concrete.LockedNANDSourceParserMachine
import PNP.Concrete.LockedNANDSourceParserSemantics
import PNP.Concrete.LockedNANDSourceParserValidTrace

namespace PNP.Concrete.LockedNAND.SourceParser

/-! ### The two cleanup transition programs -/

/-- The cleanup seek state always has a transition.  At the installed guard
it erases the guard and turns right; at every other work symbol it keeps the
symbol and moves left. -/
theorem cleanupSeekGuard_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupSeekGuard, tape := tape } :
          WorkConfiguration) =
      if tape.head == leftGuard then
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right }
      else
        some
          { state := State.cleanupSeekGuard
            tape := tape.move .left } := by
  set_option maxRecDepth 100000 in
    rcases tape with ⟨left, ⟨first, second⟩, right⟩
    cases first <;> cases second <;> rfl

/-- The cleanup erase state always has a transition.  A blank delimiter
enters the reject halt; every other symbol is erased while moving right. -/
theorem cleanupRight_workStep (tape : WorkTape) :
    workStep? machine
        ({ state := State.cleanupRight, tape := tape } :
          WorkConfiguration) =
      if tape.head == cellBlank then
        some
          { state := State.reject
            tape := tape }
      else
        some
          { state := State.cleanupRight
            tape := (tape.write cellBlank).move .right } := by
  set_option maxRecDepth 100000 in
    rcases tape with ⟨left, ⟨first, second⟩, right⟩
    cases first <;> cases second <;> rfl

private theorem workSymbol_beq_false_of_ne
    (first second : WorkSymbol) (different : first ≠ second) :
    (first == second) = false := by
  rcases first with ⟨firstLeft, firstRight⟩
  rcases second with ⟨secondLeft, secondRight⟩
  cases firstLeft <;> cases firstRight <;>
    cases secondLeft <;> cases secondRight <;>
    first | rfl | exact False.elim (different rfl)

private theorem exactRun_add (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first initial = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final := by
  induction first generalizing initial with
  | zero =>
      have initialEq : initial = middle := Option.some.inj hFirst
      cases initialEq
      simpa using hSecond
  | succ first ih =>
      cases stepEq : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine first next) =
              some middle at hFirst
          rw [stepEq] at hFirst
          contradiction
      | some next =>
          have tailRun :
              workRunExact? machine first next = some middle := by
            change
              (match workStep? machine initial with
               | none => none
               | some next => workRunExact? machine first next) =
                some middle at hFirst
            rw [stepEq] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine initial with
             | none => none
             | some next =>
                 workRunExact? machine (first + second) next) =
              some final
          rw [stepEq]
          exact ih next tailRun

/-! ### Exact leftward seek -/

/-- Push a nearest-first left scan onto the right side of a work tape.  This
is definitionally aligned with repeated `moveLeft` transitions. -/
def pushCleanupScan : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], right => right
  | symbol :: rest, right =>
      pushCleanupScan rest (symbol :: right)

/-- A cleanup-seek configuration whose finite `scan` begins at the current
head and ends immediately before the distinguished left guard. -/
def cleanupSeekConfiguration (outsideLeft scan right : List WorkSymbol) :
    WorkConfiguration :=
  match scan with
  | [] =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := outsideLeft
            head := leftGuard
            right := right } }
  | symbol :: rest =>
      { state := State.cleanupSeekGuard
        tape :=
          { left := rest ++ leftGuard :: outsideLeft
            head := symbol
            right := right } }

private theorem cleanupSeekConfiguration_step
    (outsideLeft : List WorkSymbol) (symbol : WorkSymbol)
    (rest right : List WorkSymbol)
    (notGuard : symbol ≠ leftGuard) :
    workStep? machine
        (cleanupSeekConfiguration outsideLeft
          (symbol :: rest) right) =
      some
        (cleanupSeekConfiguration outsideLeft rest
          (symbol :: right)) := by
  unfold cleanupSeekConfiguration
  have compared :
      (symbol == leftGuard) = false :=
    workSymbol_beq_false_of_ne symbol leftGuard notGuard
  rw [cleanupSeekGuard_workStep]
  change
    (if symbol == leftGuard then _ else _) =
      some
        (cleanupSeekConfiguration outsideLeft rest
          (symbol :: right))
  rw [compared]
  cases rest <;> rfl

/-- The seek state reaches the distinguished guard in exactly the number of
cells between the current cursor and that guard.  Symbols are retained and
appear on the right in physical left-to-right order. -/
theorem cleanupSeekGuard_exact
    (outsideLeft scan right : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ scan → symbol ≠ leftGuard) :
    workRunExact? machine scan.length
        (cleanupSeekConfiguration outsideLeft scan right) =
      some
        (cleanupSeekConfiguration outsideLeft []
          (pushCleanupScan scan right)) := by
  induction scan generalizing right with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotGuard :
          symbol ≠ leftGuard :=
        noInnerGuard symbol (List.Mem.head rest)
      have restNoGuard :
          ∀ found, found ∈ rest → found ≠ leftGuard := by
        intro found member
        exact noInnerGuard found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupSeekConfiguration outsideLeft
              (symbol :: rest) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupSeekConfiguration outsideLeft []
              (pushCleanupScan (symbol :: rest) right))
      rw [cleanupSeekConfiguration_step outsideLeft symbol rest right
        headNotGuard]
      exact ih (symbol :: right) restNoGuard

theorem pushCleanupScan_append
    (scan first second : List WorkSymbol) :
    pushCleanupScan scan (first ++ second) =
      pushCleanupScan scan first ++ second := by
  induction scan generalizing first with
  | nil =>
      rfl
  | cons symbol rest ih =>
      change
        pushCleanupScan rest (symbol :: (first ++ second)) =
          pushCleanupScan rest (symbol :: first) ++ second
      exact ih (symbol :: first)

/-- Seeking left preserves every scanned cell, so the materialized forward
word has exactly the combined scan/right length. -/
theorem pushCleanupScan_length
    (scan right : List WorkSymbol) :
    (pushCleanupScan scan right).length =
      scan.length + right.length := by
  induction scan generalizing right with
  | nil =>
      simp [pushCleanupScan]
  | cons symbol rest ih =>
      change
        (pushCleanupScan rest (symbol :: right)).length =
          (symbol :: rest).length + right.length
      rw [ih]
      simp only [List.length_cons]
      omega

/-! ### Exact rightward erasure -/

/-- Materialize one blank on the left for every erased work symbol.  Only the
length of the word matters, but this accumulator form matches `moveRight`
definitionally. -/
def pushCleanupBlanks : List WorkSymbol → List WorkSymbol →
    List WorkSymbol
  | [], left => left
  | _ :: rest, left =>
      pushCleanupBlanks rest (cellBlank :: left)

/-- A cleanup-right configuration focused at the beginning of `word`, with
an explicit blank delimiter followed by an arbitrary exterior suffix. -/
def cleanupRightConfiguration (left word suffix : List WorkSymbol) :
    WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := suffix } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest ++ cellBlank :: suffix } }

private theorem cleanupRightConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest suffix : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightConfiguration left
          (symbol :: rest) suffix) =
      some
        (cleanupRightConfiguration (cellBlank :: left)
          rest suffix) := by
  unfold cleanupRightConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  rw [cleanupRight_workStep]
  change
    (if symbol == cellBlank then _ else _) =
      some
        (cleanupRightConfiguration (cellBlank :: left)
          rest suffix)
  rw [compared]
  cases rest <;> rfl

/-- The erase state blanks a finite word in exactly its length, stopping on
the explicit blank delimiter without consuming it. -/
theorem cleanupRight_erase_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightConfiguration left word suffix) =
      some
        (cleanupRightConfiguration
          (pushCleanupBlanks word left) [] suffix) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightConfiguration left
              (symbol :: rest) suffix) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightConfiguration
              (pushCleanupBlanks (symbol :: rest) left)
              [] suffix)
      rw [cleanupRightConfiguration_step left symbol rest suffix
        headNotBlank]
      exact ih (cellBlank :: left) restNonblank

/-- On the delimiter, cleanup enters the designated reject halt in exactly
one transition. -/
theorem cleanupRight_reject_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (cleanupRightConfiguration left [] suffix) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } } := by
  unfold cleanupRightConfiguration
  change
    (match workStep? machine
        ({ state := State.cleanupRight
           tape :=
             { left := left
               head := cellBlank
               right := suffix } } : WorkConfiguration) with
     | none => none
     | some next => some next) =
      some
        { state := State.reject
          tape :=
            { left := left
              head := cellBlank
              right := suffix } }
  rw [cleanupRight_workStep]
  rfl

/-- Erase a finite nonblank word and reject, retaining an exact transition
count of `word.length + 1`. -/
theorem cleanupRight_exact
    (left word suffix : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightConfiguration left word suffix) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := suffix } } := by
  exact exactRun_add word.length 1
    (cleanupRightConfiguration left word suffix)
    (cleanupRightConfiguration
      (pushCleanupBlanks word left) [] suffix)
    { state := State.reject
      tape :=
        { left := pushCleanupBlanks word left
          head := cellBlank
          right := suffix } }
    (cleanupRight_erase_exact left word suffix nonblank)
    (cleanupRight_reject_exact
      (pushCleanupBlanks word left) suffix)

/-! ### Finite-list cleanup with an implicit exterior blank -/

/-- A cleanup-right configuration whose delimiter is the implicit blank
beyond a finite list.  This is the exact representation produced from a raw
input tape, which does not materialize a trailing blank until the final
rightward move. -/
def cleanupRightFiniteConfiguration
    (left word : List WorkSymbol) : WorkConfiguration :=
  match word with
  | [] =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := cellBlank
            right := [] } }
  | symbol :: rest =>
      { state := State.cleanupRight
        tape :=
          { left := left
            head := symbol
            right := rest } }

private theorem cleanupRightFiniteConfiguration_step
    (left : List WorkSymbol) (symbol : WorkSymbol)
    (rest : List WorkSymbol)
    (notBlank : symbol ≠ cellBlank) :
    workStep? machine
        (cleanupRightFiniteConfiguration left
          (symbol :: rest)) =
      some
        (cleanupRightFiniteConfiguration
          (cellBlank :: left) rest) := by
  unfold cleanupRightFiniteConfiguration
  have compared :
      (symbol == cellBlank) = false :=
    workSymbol_beq_false_of_ne symbol cellBlank notBlank
  rw [cleanupRight_workStep]
  change
    (if symbol == cellBlank then _ else _) =
      some
        (cleanupRightFiniteConfiguration
          (cellBlank :: left) rest)
  rw [compared]
  cases rest <;> rfl

/-- A finite nonblank word is erased exactly, leaving the implicit exterior
blank focused. -/
theorem cleanupRightFinite_erase_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine word.length
        (cleanupRightFiniteConfiguration left word) =
      some
        (cleanupRightFiniteConfiguration
          (pushCleanupBlanks word left) []) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      have headNotBlank :
          symbol ≠ cellBlank :=
        nonblank symbol (List.Mem.head rest)
      have restNonblank :
          ∀ found, found ∈ rest → found ≠ cellBlank := by
        intro found member
        exact nonblank found (List.Mem.tail symbol member)
      change
        (match workStep? machine
            (cleanupRightFiniteConfiguration left
              (symbol :: rest)) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (cleanupRightFiniteConfiguration
              (pushCleanupBlanks (symbol :: rest) left) [])
      rw [cleanupRightFiniteConfiguration_step
        left symbol rest headNotBlank]
      exact ih (cellBlank :: left) restNonblank

/-- Erase a finite nonblank word up to the implicit exterior blank and enter
the reject halt. -/
theorem cleanupRightFinite_exact
    (left word : List WorkSymbol)
    (nonblank :
      ∀ symbol, symbol ∈ word → symbol ≠ cellBlank) :
    workRunExact? machine (word.length + 1)
        (cleanupRightFiniteConfiguration left word) =
      some
        { state := State.reject
          tape :=
            { left := pushCleanupBlanks word left
              head := cellBlank
              right := [] } } := by
  exact exactRun_add word.length 1
    (cleanupRightFiniteConfiguration left word)
    (cleanupRightFiniteConfiguration
      (pushCleanupBlanks word left) [])
    { state := State.reject
      tape :=
        { left := pushCleanupBlanks word left
          head := cellBlank
          right := [] } }
    (cleanupRightFinite_erase_exact left word nonblank)
    (by
      change
        workRunExact? machine 1
            (cleanupRightConfiguration
              (pushCleanupBlanks word left) [] []) =
          some
            { state := State.reject
              tape :=
                { left := pushCleanupBlanks word left
                  head := cellBlank
                  right := [] } }
      exact cleanupRight_reject_exact
        (pushCleanupBlanks word left) [])

/-! ### The complete guarded cleanup trace -/

/-- Exact cleanup cost from an arbitrary cursor position inside a finite
guarded word. -/
def guardedCleanupSteps (leftScan rightWord : List WorkSymbol) : Nat :=
  leftScan.length + 1 +
    (pushCleanupScan leftScan rightWord).length + 1

/-- Closed arithmetic form of the guarded cleanup schedule. -/
theorem guardedCleanupSteps_eq
    (leftScan rightWord : List WorkSymbol) :
    guardedCleanupSteps leftScan rightWord =
      2 * leftScan.length + rightWord.length + 2 := by
  unfold guardedCleanupSteps
  rw [pushCleanupScan_length]
  omega

/-- Exact terminal configuration after guarded cleanup.  `outsideLeft` and
`suffix` lie outside the guarded region and are intentionally retained. -/
def cleanupRejectConfiguration
    (outsideLeft leftScan rightWord suffix : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks
            (pushCleanupScan leftScan rightWord)
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := suffix } }

/-- From any cursor position in a guarded finite workspace, cleanup erases
every guarded cell and reaches reject.  The first hypothesis identifies the
distinguished left guard; the second says that the guarded source region has
no earlier blank delimiter. -/
theorem guardedCleanup_exact
    (outsideLeft leftScan rightWord suffix : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan leftScan rightWord →
          symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupSteps leftScan rightWord)
        (cleanupSeekConfiguration outsideLeft leftScan
          (rightWord ++ cellBlank :: suffix)) =
      some
        (cleanupRejectConfiguration
          outsideLeft leftScan rightWord suffix) := by
  let forwardWord := pushCleanupScan leftScan rightWord
  let atGuard :=
    cleanupSeekConfiguration outsideLeft []
      (forwardWord ++ cellBlank :: suffix)
  let atErase :=
    cleanupRightConfiguration
      (cellBlank :: outsideLeft) forwardWord suffix
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration outsideLeft leftScan
            (rightWord ++ cellBlank :: suffix)) =
        some atGuard := by
    have run := cleanupSeekGuard_exact outsideLeft leftScan
      (rightWord ++ cellBlank :: suffix) noInnerGuard
    rw [pushCleanupScan_append] at run
    exact run
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase, forwardWord]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   pushCleanupScan leftScan rightWord ++
                     cellBlank :: suffix } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightConfiguration
            (cellBlank :: outsideLeft)
            (pushCleanupScan leftScan rightWord) suffix)
    rw [cleanupSeekGuard_workStep]
    cases wordEq : pushCleanupScan leftScan rightWord <;> rfl
  have erase :
      workRunExact? machine (forwardWord.length + 1)
          atErase =
        some
          (cleanupRejectConfiguration
            outsideLeft leftScan rightWord suffix) := by
    dsimp [atErase, forwardWord]
    exact cleanupRight_exact
      (cellBlank :: outsideLeft)
      (pushCleanupScan leftScan rightWord) suffix nonblank
  have throughGuard := exactRun_add leftScan.length 1
    (cleanupSeekConfiguration outsideLeft leftScan
      (rightWord ++ cellBlank :: suffix))
    atGuard atErase seek crossGuard
  have complete := exactRun_add (leftScan.length + 1)
    (forwardWord.length + 1)
    (cleanupSeekConfiguration outsideLeft leftScan
      (rightWord ++ cellBlank :: suffix))
    atErase
    (cleanupRejectConfiguration
      outsideLeft leftScan rightWord suffix)
    throughGuard erase
  simpa [guardedCleanupSteps, forwardWord, Nat.add_assoc] using complete

/-- Exact cleanup from the finite raw-input representation, where the first
blank after the guarded word is implicit rather than present in `right`. -/
theorem guardedCleanupFinite_exact
    (outsideLeft leftScan rightWord : List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (nonblank :
      ∀ symbol,
        symbol ∈ pushCleanupScan leftScan rightWord →
          symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupSteps leftScan rightWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan rightWord) =
      some
        (cleanupRejectConfiguration
          outsideLeft leftScan rightWord []) := by
  let forwardWord := pushCleanupScan leftScan rightWord
  let atGuard :=
    cleanupSeekConfiguration outsideLeft [] forwardWord
  let atErase :=
    cleanupRightFiniteConfiguration
      (cellBlank :: outsideLeft) forwardWord
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan rightWord) =
        some atGuard := by
    exact cleanupSeekGuard_exact
      outsideLeft leftScan rightWord noInnerGuard
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase, forwardWord]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   pushCleanupScan leftScan rightWord } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightFiniteConfiguration
            (cellBlank :: outsideLeft)
            (pushCleanupScan leftScan rightWord))
    rw [cleanupSeekGuard_workStep]
    cases wordEq : pushCleanupScan leftScan rightWord <;> rfl
  have erase :
      workRunExact? machine (forwardWord.length + 1)
          atErase =
        some
          (cleanupRejectConfiguration
            outsideLeft leftScan rightWord []) := by
    dsimp [atErase, forwardWord]
    exact cleanupRightFinite_exact
      (cellBlank :: outsideLeft)
      (pushCleanupScan leftScan rightWord) nonblank
  have throughGuard := exactRun_add leftScan.length 1
    (cleanupSeekConfiguration outsideLeft leftScan rightWord)
    atGuard atErase seek crossGuard
  have complete := exactRun_add (leftScan.length + 1)
    (forwardWord.length + 1)
    (cleanupSeekConfiguration outsideLeft leftScan rightWord)
    atErase
    (cleanupRejectConfiguration
      outsideLeft leftScan rightWord [])
    throughGuard erase
  simpa [guardedCleanupSteps, forwardWord,
    Nat.add_assoc] using complete

/-- Cleanup cost when a materialized blank already occurs inside the finite
representation reached after the leftward seek. -/
def guardedCleanupExplicitSteps
    (leftScan eraseWord : List WorkSymbol) : Nat :=
  leftScan.length + 1 + eraseWord.length + 1

/-- Closed arithmetic form of cleanup at an already materialized blank. -/
theorem guardedCleanupExplicitSteps_eq
    (leftScan eraseWord : List WorkSymbol) :
    guardedCleanupExplicitSteps leftScan eraseWord =
      leftScan.length + eraseWord.length + 2 := by
  unfold guardedCleanupExplicitSteps
  omega

/-- Rejecting endpoint for cleanup whose first materialized blank is followed
by an arbitrary finite suffix. -/
def cleanupExplicitRejectConfiguration
    (outsideLeft eraseWord suffix : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.reject
    tape :=
      { left :=
          pushCleanupBlanks eraseWord
            (cellBlank :: outsideLeft)
        head := cellBlank
        right := suffix } }

/-- General materialized-delimiter cleanup.  The equality states where the
first relevant blank appears after the seek has put the scanned cells back
into physical order. -/
theorem guardedCleanupExplicit_exact
    (outsideLeft leftScan right eraseWord suffix :
      List WorkSymbol)
    (noInnerGuard :
      ∀ symbol, symbol ∈ leftScan → symbol ≠ leftGuard)
    (forwardShape :
      pushCleanupScan leftScan right =
        eraseWord ++ cellBlank :: suffix)
    (nonblank :
      ∀ symbol, symbol ∈ eraseWord →
        symbol ≠ cellBlank) :
    workRunExact? machine
        (guardedCleanupExplicitSteps leftScan eraseWord)
        (cleanupSeekConfiguration
          outsideLeft leftScan right) =
      some
        (cleanupExplicitRejectConfiguration
          outsideLeft eraseWord suffix) := by
  let atGuard :=
    cleanupSeekConfiguration outsideLeft []
      (eraseWord ++ cellBlank :: suffix)
  let atErase :=
    cleanupRightConfiguration
      (cellBlank :: outsideLeft) eraseWord suffix
  have seek :
      workRunExact? machine leftScan.length
          (cleanupSeekConfiguration
            outsideLeft leftScan right) =
        some atGuard := by
    have run := cleanupSeekGuard_exact
      outsideLeft leftScan right noInnerGuard
    rw [forwardShape] at run
    exact run
  have crossGuard :
      workRunExact? machine 1 atGuard = some atErase := by
    dsimp [atGuard, atErase]
    change
      (match workStep? machine
          ({ state := State.cleanupSeekGuard
             tape :=
               { left := outsideLeft
                 head := leftGuard
                 right :=
                   eraseWord ++ cellBlank :: suffix } } :
            WorkConfiguration) with
       | none => none
       | some next => some next) =
        some
          (cleanupRightConfiguration
            (cellBlank :: outsideLeft) eraseWord suffix)
    rw [cleanupSeekGuard_workStep]
    cases eraseWord <;> rfl
  have erase :
      workRunExact? machine (eraseWord.length + 1)
          atErase =
        some
          (cleanupExplicitRejectConfiguration
            outsideLeft eraseWord suffix) := by
    dsimp [atErase]
    exact cleanupRight_exact
      (cellBlank :: outsideLeft)
      eraseWord suffix nonblank
  have throughGuard := exactRun_add leftScan.length 1
    (cleanupSeekConfiguration outsideLeft leftScan right)
    atGuard atErase seek crossGuard
  have complete := exactRun_add (leftScan.length + 1)
    (eraseWord.length + 1)
    (cleanupSeekConfiguration outsideLeft leftScan right)
    atErase
    (cleanupExplicitRejectConfiguration
      outsideLeft eraseWord suffix)
    throughGuard erase
  simpa [guardedCleanupExplicitSteps,
    Nat.add_assoc] using complete

/-- If no exterior suffix follows the guarded source region, the rejecting
configuration exposes the empty raw output word. -/
theorem cleanupRejectConfiguration_output_empty
    (outsideLeft leftScan rightWord : List WorkSymbol) :
    (encodeWorkTape
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord []).tape).outputBits = [] := by
  rfl

/-- The guarded-cleanup endpoint is genuinely halted, so any larger work or
compiled fuel budget remains at rejection. -/
theorem cleanupRejectConfiguration_isHalted
    (outsideLeft leftScan rightWord suffix : List WorkSymbol) :
    machine.isHalted
      (cleanupRejectConfiguration
        outsideLeft leftScan rightWord suffix) = true := by
  rfl

/-! ### Accepting predecessor and semantic invariant -/

/-- The canonical pre-accept boundary: all temporary gate marks have been
restored, the installed guard is focused, and the original source word lies
unchanged to its right. -/
def restoredBoundaryConfiguration (raw : RawCircuit) :
    WorkConfiguration :=
  { state := State.successRestoreLeft
    tape :=
      { left := []
        head := leftGuard
        right := circuitCells raw ++ [cellBlank] } }

/-- The final guard-erasure transition turns a restored canonical boundary
into the exact accepting endpoint. -/
theorem restoredBoundary_workStep (raw : RawCircuit) :
    workStep? machine (restoredBoundaryConfiguration raw) =
      some (validFinalConfiguration raw) := by
  cases cellsEq : circuitCells raw with
  | nil =>
      exact False.elim (circuitCells_ne_empty raw cellsEq)
  | cons first rest =>
      unfold restoredBoundaryConfiguration validFinalConfiguration
        acceptedTape
      rw [cellsEq]
      set_option maxRecDepth 100000 in
        rfl

theorem restoredBoundary_exact (raw : RawCircuit) :
    workRunExact? machine 1 (restoredBoundaryConfiguration raw) =
      some (validFinalConfiguration raw) := by
  change
    (match workStep? machine (restoredBoundaryConfiguration raw) with
     | none => none
     | some next => some next) =
      some (validFinalConfiguration raw)
  rw [restoredBoundary_workStep]

private theorem findWorkRule_some_mem {rules : List WorkRule}
    {state : Nat} {symbol : WorkSymbol} {selected : WorkRule}
    (selectedEq :
      findWorkRule rules state symbol = some selected) :
    selected ∈ rules := by
  induction rules with
  | nil =>
      contradiction
  | cons first rest ih =>
      by_cases queryMatches :
          first.sourceState = state ∧
            first.readSymbol = symbol
      · have firstEq :=
          findWorkRule_cons_of_matches first rest
            state symbol queryMatches
        have selectedIsFirst :
            first = selected :=
          Option.some.inj (firstEq.symm.trans selectedEq)
        subst selected
        exact List.Mem.head rest
      · have tailEq :=
          findWorkRule_cons_of_not_matches first rest
            state symbol queryMatches
        exact List.Mem.tail first
          (ih (tailEq.symm.trans selectedEq))

private def AcceptingRuleShape (rule : WorkRule) : Prop :=
  rule.targetState = State.accept →
    rule.sourceState = State.successRestoreLeft ∧
      rule.readSymbol = leftGuard ∧
      rule.writeSymbol = cellBlank ∧
      rule.move = .right

private instance acceptingRuleShapeDecidable (rule : WorkRule) :
    Decidable (AcceptingRuleShape rule) := by
  unfold AcceptingRuleShape
  infer_instance

private theorem list_all_member_true
    {α : Type} (predicate : α → Bool) :
    ∀ (items : List α) (item : α),
      items.all predicate = true →
      item ∈ items →
      predicate item = true := by
  intro items
  induction items with
  | nil =>
      intro item _ member
      contradiction
  | cons first rest ih =>
      intro item allTrue member
      have bothTrue :
          predicate first = true ∧
            rest.all predicate = true := by
        simpa [Bool.and_eq_true] using allTrue
      have memberCases :
          item = first ∨ item ∈ rest := by
        simpa using member
      rcases memberCases with itemEq | inRest
      · subst item
        exact bothTrue.1
      · exact ih item bothTrue.2 inRest

set_option maxRecDepth 100000 in
private theorem all_rules_accepting_shape :
    rules.all
      (fun rule =>
        @decide (AcceptingRuleShape rule)
          (acceptingRuleShapeDecidable rule)) = true := by
  decide

private theorem accepting_rule_shape_of_mem
    (rule : WorkRule) (member : rule ∈ rules) :
    AcceptingRuleShape rule := by
  have decided :
      @decide (AcceptingRuleShape rule)
          (acceptingRuleShapeDecidable rule) = true :=
    list_all_member_true
      (fun found =>
        @decide (AcceptingRuleShape found)
          (acceptingRuleShapeDecidable found))
      rules rule all_rules_accepting_shape member
  exact
    (decide_true_iff_constructive
      (AcceptingRuleShape rule)
      (acceptingRuleShapeDecidable rule)).mp
        decided

/-- There is only one incoming transition to acceptance: it comes from the
restore-left state while focused on the installed guard, writes a blank, and
moves right.  This finite reverse-edge audit ranges over the literal rule
list. -/
theorem workStep_to_accept_predecessor
    (config final : WorkConfiguration)
    (step : workStep? machine config = some final)
    (accepts : final.state = machine.acceptState) :
    config.state = State.successRestoreLeft ∧
      config.tape.head = leftGuard ∧
      final.tape =
        (config.tape.write cellBlank).move .right := by
  rcases workStep?_some_exists machine config final step with
    ⟨rule, _notHalted, selected, finalEq⟩
  have member :
      rule ∈ rules := by
    exact findWorkRule_some_mem selected
  have targetAccept :
      rule.targetState = State.accept := by
    rw [finalEq] at accepts
    exact accepts
  have shape :=
    accepting_rule_shape_of_mem rule member targetAccept
  have query := findWorkRule_some_matches selected
  constructor
  · exact query.1.symm.trans shape.1
  constructor
  · exact query.2.symm.trans shape.2.1
  · rw [finalEq]
    change
      (config.tape.write rule.writeSymbol).move rule.move =
        (config.tape.write cellBlank).move .right
    rw [shape.2.2.1, shape.2.2.2]

/-- The semantic fact that must hold whenever a run reaches the unique
pre-accept restore state.  Keeping this obligation named prevents a later
all-input theorem from silently assuming successful parsing. -/
private def SuccessRestoreInvariant (bits : BitString) : Prop :=
  ∀ steps config,
    workRunExact? machine steps
        (workStartConfiguration machine
          (rawInputWorkTape bits)) =
      some config →
    config.state = State.successRestoreLeft →
    config.tape.head = leftGuard →
      ∃ raw,
        bits = encodeCircuit raw ∧
          raw.wellFormed = true ∧
          config = restoredBoundaryConfiguration raw

private theorem workRunExact_succ_split_last :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? machine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? machine steps initial = some before ∧
          workStep? machine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final run
      cases stepEq : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => some next) =
              some final at run
          rw [stepEq] at run
          contradiction
      | some next =>
          have nextEq : next = final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => some result) =
                some final at run
            rw [stepEq] at run
            exact Option.some.inj run
          subst final
          exact ⟨initial, rfl, stepEq⟩
  | succ steps ih =>
      intro initial final run
      cases stepEq : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next =>
                 workRunExact? machine (steps + 1) next) =
              some final at run
          rw [stepEq] at run
          contradiction
      | some next =>
          have tailRun :
              workRunExact? machine (steps + 1) next =
                some final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result =>
                   workRunExact? machine (steps + 1) result) =
                some final at run
            rw [stepEq] at run
            exact run
          rcases ih next final tailRun with
            ⟨before, prefixRun, last⟩
          refine ⟨before, ?_, last⟩
          change
            (match workStep? machine initial with
             | none => none
             | some result =>
                 workRunExact? machine steps result) =
              some before
          rw [stepEq]
          exact prefixRun

/-- Assuming the named restore invariant, every exact run that enters accept
has a canonical well-formed raw source, the exact restored endpoint, and a
successful elaborated decode.  The theorem is the acceptance-soundness half
of the later exhaustive all-input split. -/
private theorem accepting_exactRun_restored_sound
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (invariant : SuccessRestoreInvariant bits)
    (run :
      workRunExact? machine (steps + 1)
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (accepts : final.state = machine.acceptState) :
    ∃ raw packed,
      bits = encodeCircuit raw ∧
        raw.wellFormed = true ∧
        final = validFinalConfiguration raw ∧
        decodeElaboratedCircuit bits = some packed := by
  rcases workRunExact_succ_split_last steps
      (workStartConfiguration machine
        (rawInputWorkTape bits))
      final run with
    ⟨before, prefixRun, last⟩
  have predecessor :=
    workStep_to_accept_predecessor before final last accepts
  rcases invariant steps before prefixRun
      predecessor.1 predecessor.2.1 with
    ⟨raw, bitsEq, wellFormed, beforeEq⟩
  have canonicalStep :
      workStep? machine before =
        some (validFinalConfiguration raw) := by
    rw [beforeEq]
    exact restoredBoundary_workStep raw
  have finalEq :
      final = validFinalConfiguration raw :=
    Option.some.inj (last.symm.trans canonicalStep)
  have decodeExists :
      ∃ packed,
        decodeElaboratedCircuit (encodeCircuit raw) =
          some packed :=
    (decodeElaboratedCircuit_exists_iff
      (encodeCircuit raw)).mpr
        ⟨raw, decodeCircuit_encodeCircuit raw, wellFormed⟩
  rcases decodeExists with ⟨packed, decoded⟩
  refine ⟨raw, packed, bitsEq, wellFormed, finalEq, ?_⟩
  rw [bitsEq]
  exact decoded

/-- Acceptance soundness in the public source-language predicate, separated
cleanly from the still-pending proof of `SuccessRestoreInvariant`. -/
private theorem accepting_exactRun_valid_of_successRestoreInvariant
    (bits : BitString) (steps : Nat)
    (final : WorkConfiguration)
    (invariant : SuccessRestoreInvariant bits)
    (run :
      workRunExact? machine (steps + 1)
          (workStartConfiguration machine
            (rawInputWorkTape bits)) =
        some final)
    (accepts : final.state = machine.acceptState) :
    ValidEncodedCircuit bits := by
  rcases accepting_exactRun_restored_sound
      bits steps final invariant run accepts with
    ⟨_raw, packed, _bitsEq, _wellFormed,
      _finalEq, decoded⟩
  exact valid_of_decoded decoded

end PNP.Concrete.LockedNAND.SourceParser
