/-
Copyright (c) 2026 PNP Labs.

Literal terminal cleanup for the cursor-bearing strict-v0 locked-NAND target
emitter.

The source-driven controller deliberately keeps one contextual cursor marker
in the retained packed source while it emits the final output section.  This
six-rule machine erases the four ordinary packed symbols, that cursor marker,
and the source/target boundary.  It then halts with the first target cell under
the head.  No transition reads a decoded circuit or a precomputed target.
-/

import PNP.Concrete.LockedNANDTargetEmitterCursorAppender
import PNP.Concrete.LockedNANDTargetEmitterFinalizer

namespace PNP.Concrete.LockedNAND.TargetEmitterCursorFinalizer

open TargetEmitter

def cursorMarker : WorkSymbol :=
  TargetEmitterCursorAppender.cursorMarker

def eraseState : Nat := 0
def acceptState : Nat := 1
def rejectState : Nat := 2

def eraseRule (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := eraseState
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

/-- Four packed-source erasers, the contextual cursor eraser, and the
source/target-boundary eraser.  Every other symbol is ruleless. -/
def rules : List WorkRule :=
  [ eraseRule WorkSymbol.zeroZero eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.zeroOne eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.oneZero eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.oneOne eraseState WorkSymbol.blank .right
  , eraseRule cursorMarker eraseState WorkSymbol.blank .right
  , eraseRule sourceTargetBoundary acceptState WorkSymbol.blank .right
  ]

def machine : WorkMachine :=
  { rules := rules
    startState := eraseState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachine : Machine :=
  compileWorkMachine machine

theorem rules_length : rules.length = 6 := by
  rfl

theorem rules_pairwise :
    rules.Pairwise fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol) := by
  decide

theorem start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
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

def configurationAtWord (state : Nat) (left word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state
    tape := tapeAtWord left word }

def inputConfiguration (source target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  configurationAtWord eraseState
    (sourceLeftBoundary :: outsideLeft)
    (source ++ sourceTargetBoundary :: target ++
      WorkSymbol.blank :: outsideRight)

def finalTape (source target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  tapeAtWord
    (WorkSymbol.blank ::
      List.replicate source.length WorkSymbol.blank ++
        sourceLeftBoundary :: outsideLeft)
    (target ++ WorkSymbol.blank :: outsideRight)

def finalConfiguration (source target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) : WorkConfiguration :=
  { state := acceptState
    tape := finalTape source target outsideLeft outsideRight }

def workSteps (source : List WorkSymbol) : Nat :=
  source.length + 1

/-- Source cells accepted by terminal cleanup.  Exactly-one-cursor invariants
are established by the controller; cleanup itself only needs this local
symbol-level condition and fails closed on every other work symbol. -/
def SourceSymbol (symbol : WorkSymbol) : Prop :=
  PackedSymbol symbol ∨ symbol = cursorMarker

private theorem source_step (symbol : WorkSymbol)
    (allowed : SourceSymbol symbol)
    (left suffix : List WorkSymbol) :
    workStep? machine
        (configurationAtWord eraseState left (symbol :: suffix)) =
      some
        (configurationAtWord eraseState
          (WorkSymbol.blank :: left) suffix) := by
  rcases allowed with ordinary | marker
  · cases ordinary <;> rfl
  · subst symbol
    rfl

private theorem boundary_step
    (left suffix : List WorkSymbol) :
    workStep? machine
        (configurationAtWord eraseState left
          (sourceTargetBoundary :: suffix)) =
      some
        (configurationAtWord acceptState
          (WorkSymbol.blank :: left) suffix) := by
  rfl

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      change item :: List.replicate (count + 1) item =
        (item :: List.replicate count item) ++ [item]
      rw [ih]
      simp only [List.cons_append]

private theorem erase_exact
    (source suffix left : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ source → SourceSymbol symbol) :
    workRunExact? machine source.length
        (configurationAtWord eraseState left (source ++ suffix)) =
      some
        (configurationAtWord eraseState
          (List.replicate source.length WorkSymbol.blank ++ left)
          suffix) := by
  induction source generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed : SourceSymbol head :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → SourceSymbol symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configurationAtWord eraseState left
              (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [source_step head headAllowed left (rest ++ suffix)]
      change
        workRunExact? machine rest.length
            (configurationAtWord eraseState
              (WorkSymbol.blank :: left) (rest ++ suffix)) = _
      rw [ih (WorkSymbol.blank :: left) restAllowed]
      simp [replicate_succ_append, List.append_assoc]

private theorem exactRun_add (first second : Nat)
    (initial middle final : WorkConfiguration)
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
          have hTail :
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
          exact ih next hTail

/-- Any retained source consisting only of packed cells and the contextual
cursor is erased in exactly `source.length + 1` steps. -/
theorem finalize_exact
    (source target outsideLeft outsideRight : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ source → SourceSymbol symbol) :
    workRunExact? machine (workSteps source)
        (inputConfiguration source target outsideLeft outsideRight) =
      some
        (finalConfiguration source target outsideLeft outsideRight) := by
  let middle :=
    configurationAtWord eraseState
      (List.replicate source.length WorkSymbol.blank ++
        sourceLeftBoundary :: outsideLeft)
      (sourceTargetBoundary :: target ++
        WorkSymbol.blank :: outsideRight)
  have sourceRun :
      workRunExact? machine source.length
          (inputConfiguration source target outsideLeft outsideRight) =
        some middle := by
    simpa [inputConfiguration, middle, configurationAtWord,
      List.append_assoc] using
        erase_exact source
          (sourceTargetBoundary :: target ++
            WorkSymbol.blank :: outsideRight)
          (sourceLeftBoundary :: outsideLeft) allowed
  have last :
      workRunExact? machine 1 middle =
        some (finalConfiguration source target
          outsideLeft outsideRight) := by
    change
      (match workStep? machine middle with
       | none => none
       | some next => some next) = _
    rw [show workStep? machine middle =
      some
        (configurationAtWord acceptState
          (WorkSymbol.blank ::
            List.replicate source.length WorkSymbol.blank ++
              sourceLeftBoundary :: outsideLeft)
          (target ++ WorkSymbol.blank :: outsideRight)) by
        simpa [middle] using
          boundary_step
            (List.replicate source.length WorkSymbol.blank ++
              sourceLeftBoundary :: outsideLeft)
            (target ++ WorkSymbol.blank :: outsideRight)]
    simp [finalConfiguration, finalTape, configurationAtWord]
  exact exactRun_add source.length 1 _ middle _ sourceRun last

/-- The observable final output is exactly the encoded token word; the erased
source, cursor, and outer workspace cannot contribute output bits. -/
theorem final_output_eq (source : List WorkSymbol)
    (tokens : List Token) (outsideLeft outsideRight : List WorkSymbol) :
    (encodeWorkTape
      (finalTape source (SourceParser.packedTokenCells tokens)
        outsideLeft outsideRight)).outputBits =
      encodeTokens tokens := by
  change
    (encodeWorkTape
      (TargetEmitterFinalizer.finalTape source
        (SourceParser.packedTokenCells tokens)
        outsideLeft outsideRight)).outputBits =
      encodeTokens tokens
  exact TargetEmitterFinalizer.final_output_eq
    source tokens outsideLeft outsideRight

theorem final_isHalted
    (source target outsideLeft outsideRight : List WorkSymbol) :
    machine.isHalted
      (finalConfiguration source target outsideLeft outsideRight) = true := by
  rfl

/-- Any nonpacked, noncursor source symbol is rejected by absence of a rule. -/
theorem malformed_source_stuck
    (left right : List WorkSymbol) :
    workStep? machine
        (configurationAtWord eraseState left
          (WorkSymbol.zeroBlank :: right)) = none := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterCursorFinalizer
