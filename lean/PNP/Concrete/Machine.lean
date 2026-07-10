/-
Copyright (c) 2026 PNP Labs.

A small deterministic machine and transition-cost kernel.

Machine programs are finite lists of transition rules.  In particular, the
`Machine` syntax does not contain a Lean function standing in for executable
code.  The interpreter below gives the syntax its deterministic semantics by
using the first matching rule.
-/

import PNP.Concrete.BitString

namespace PNP.Concrete

/-- Symbols on the machine tape.  Blank cells beyond the represented tape are
implicit. -/
inductive TapeSymbol where
  | blank
  | zero
  | one
deriving BEq, DecidableEq, Repr

namespace TapeSymbol

/-- Embed an input bit as a tape symbol. -/
def ofBool : Bool → TapeSymbol
  | false => .zero
  | true => .one

end TapeSymbol

/-- A single-tape head movement. -/
inductive HeadMove where
  | left
  | stay
  | right
deriving BEq, DecidableEq, Repr

/-- One rule in a finite deterministic machine program. -/
structure Rule where
  sourceState : Nat
  readSymbol : TapeSymbol
  targetState : Nat
  writeSymbol : TapeSymbol
  move : HeadMove
deriving BEq, DecidableEq, Repr

/-- A tape focused at its current head position.

`left` stores cells nearest to the head first, while `right` stores them in
their ordinary left-to-right order. -/
structure Tape where
  left : List TapeSymbol
  head : TapeSymbol
  right : List TapeSymbol
deriving BEq, DecidableEq, Repr

namespace Tape

/-- The all-blank tape. -/
def blank : Tape :=
  { left := [], head := .blank, right := [] }

/-- Put a bitstring on an otherwise blank tape with the head at its first bit.
The empty input starts on a blank cell. -/
def ofInput : BitString → Tape
  | [] => blank
  | bit :: rest =>
      { left := []
        head := TapeSymbol.ofBool bit
        right := rest.map TapeSymbol.ofBool }

/-- Overwrite the focused cell. -/
def write (tape : Tape) (symbol : TapeSymbol) : Tape :=
  { tape with head := symbol }

/-- Move the focus one cell to the left, materializing an implicit blank cell
when necessary. -/
def moveLeft (tape : Tape) : Tape :=
  match tape.left with
  | [] =>
      { left := []
        head := .blank
        right := tape.head :: tape.right }
  | symbol :: rest =>
      { left := rest
        head := symbol
        right := tape.head :: tape.right }

/-- Move the focus one cell to the right, materializing an implicit blank cell
when necessary. -/
def moveRight (tape : Tape) : Tape :=
  match tape.right with
  | [] =>
      { left := tape.head :: tape.left
        head := .blank
        right := [] }
  | symbol :: rest =>
      { left := tape.head :: tape.left
        head := symbol
        right := rest }

/-- Apply a head movement to a tape. -/
def move (tape : Tape) : HeadMove → Tape
  | .left => tape.moveLeft
  | .stay => tape
  | .right => tape.moveRight

end Tape

/-- A machine configuration consists of a control state and focused tape. -/
structure Configuration where
  state : Nat
  tape : Tape
deriving BEq, DecidableEq, Repr

/-- Concrete syntax for a deterministic single-tape machine.

The first matching element of `rules` is selected, so the semantics remains
deterministic even when a rule list contains duplicate left-hand sides. -/
structure Machine where
  rules : List Rule
  startState : Nat
  acceptState : Nat
  rejectState : Nat
deriving BEq, DecidableEq, Repr

/-- Find the first rule matching the current state and tape symbol. -/
def findRule : List Rule → Nat → TapeSymbol → Option Rule
  | [], _, _ => none
  | rule :: rest, state, symbol =>
      if rule.sourceState == state && rule.readSymbol == symbol then
        some rule
      else
        findRule rest state symbol

/-- Whether a configuration is in either designated halting state. -/
def Machine.isHalted (machine : Machine) (config : Configuration) : Bool :=
  config.state == machine.acceptState || config.state == machine.rejectState

/-- Apply a selected transition rule. -/
def applyRule (rule : Rule) (config : Configuration) : Configuration :=
  { state := rule.targetState
    tape := (config.tape.write rule.writeSymbol).move rule.move }

/-- Execute one transition.  Halting configurations and configurations with no
matching rule have no successor. -/
def step? (machine : Machine) (config : Configuration) : Option Configuration :=
  if machine.isHalted config then
    none
  else
    match findRule machine.rules config.state config.tape.head with
    | none => none
    | some rule => some (applyRule rule config)

/-- Execute at most `fuel` transitions.  No recursive call is made after fuel
reaches zero, so a rule cannot be taken outside the stated transition budget. -/
def run (machine : Machine) : Nat → Configuration → Configuration
  | 0, config => config
  | fuel + 1, config =>
      match step? machine config with
      | none => config
      | some next => run machine fuel next

/-- A zero transition budget leaves the initial configuration untouched. -/
@[simp] theorem run_zero (machine : Machine) (config : Configuration) :
    run machine 0 config = config := rfl

/-- A positive transition budget performs at most one transition before using
the remaining budget. -/
theorem run_succ (machine : Machine) (fuel : Nat) (config : Configuration) :
    run machine (fuel + 1) config =
      match step? machine config with
      | none => config
      | some next => run machine fuel next := rfl

/-- Initial configuration for a bitstring input. -/
def startConfig (machine : Machine) (input : BitString) : Configuration :=
  { state := machine.startState, tape := Tape.ofInput input }

/-- Observable outcome of a bounded deterministic run. -/
inductive Verdict where
  | accept
  | reject
  | timeout
deriving BEq, DecidableEq, Repr

/-- Run a concrete machine for at most `fuel` transitions and inspect the final
state.  A stuck nonhalting configuration is reported as `timeout`. -/
def boundedDecide (machine : Machine) (fuel : Nat) (input : BitString) : Verdict :=
  let final := run machine fuel (startConfig machine input)
  if final.state == machine.acceptState then
    .accept
  else if final.state == machine.rejectState then
    .reject
  else
    .timeout

/-- A proof-bearing polynomial-time machine for a bitstring predicate.

The time bound is concrete `NatPolynomial` syntax.  Both proof fields refer to
the interpreter above at exactly the evaluated input-size bound, tying the
finite rule-list program to its stated language semantics. -/
structure PolynomialTimeMachine (language : BitString → Prop) where
  machine : Machine
  timeBound : NatPolynomial
  haltsWithin : ∀ input,
    boundedDecide machine (timeBound.eval (BitString.size input)) input ≠ .timeout
  accepts_iff : ∀ input,
    boundedDecide machine (timeBound.eval (BitString.size input)) input = .accept ↔
      language input

namespace PolynomialTimeMachine

/-- The bounded verdict supplied by a polynomial-time machine witness. -/
def verdict {language : BitString → Prop}
    (witness : PolynomialTimeMachine language) (input : BitString) : Verdict :=
  boundedDecide witness.machine
    (witness.timeBound.eval (BitString.size input)) input

/-- A polynomial-time machine witness never times out at its stated bound. -/
theorem verdict_ne_timeout {language : BitString → Prop}
    (witness : PolynomialTimeMachine language) (input : BitString) :
    witness.verdict input ≠ .timeout := by
  simpa [verdict] using witness.haltsWithin input

/-- Acceptance by the witness at its stated bound is exactly membership in its
language semantics. -/
theorem verdict_accepts_iff {language : BitString → Prop}
    (witness : PolynomialTimeMachine language) (input : BitString) :
    witness.verdict input = .accept ↔ language input := by
  simpa [verdict] using witness.accepts_iff input

end PolynomialTimeMachine

/-! ### Small executable regression machines -/

/-- A zero-transition machine that accepts every input. -/
def immediateAcceptMachine : Machine :=
  { rules := []
    startState := 0
    acceptState := 0
    rejectState := 1 }

/-- A zero-transition machine that rejects every input. -/
def immediateRejectMachine : Machine :=
  { rules := []
    startState := 0
    acceptState := 1
    rejectState := 0 }

/-- A stuck nonhalting machine, used to exercise the timeout verdict. -/
def stuckMachine : Machine :=
  { rules := []
    startState := 0
    acceptState := 1
    rejectState := 2 }

/-- A machine that accepts a leading zero after exactly one transition. -/
def acceptLeadingZeroMachine : Machine :=
  { rules :=
      [{ sourceState := 0
         readSymbol := .zero
         targetState := 1
         writeSymbol := .zero
         move := .stay }]
    startState := 0
    acceptState := 1
    rejectState := 2 }

/-- The universal language has a concrete zero-step polynomial-time machine. -/
def acceptAllPolynomialTime : PolynomialTimeMachine (fun _ => True) :=
  { machine := immediateAcceptMachine
    timeBound := .constant 0
    haltsWithin := by
      intro input
      exact Verdict.noConfusion
    accepts_iff := by
      intro input
      constructor
      · intro _
        exact True.intro
      · intro _
        rfl }

/-- The empty language has a concrete zero-step polynomial-time machine. -/
def rejectAllPolynomialTime : PolynomialTimeMachine (fun _ => False) :=
  { machine := immediateRejectMachine
    timeBound := .constant 0
    haltsWithin := by
      intro input
      exact Verdict.noConfusion
    accepts_iff := by
      intro input
      constructor
      · intro impossible
        exact Verdict.noConfusion impossible
      · intro impossible
        exact False.elim impossible }

/-- The immediate-accept regression machine accepts with a zero-step budget. -/
theorem immediateAcceptMachine_accepts :
    boundedDecide immediateAcceptMachine 0 [] = .accept := rfl

/-- The immediate-reject regression machine rejects with a zero-step budget. -/
theorem immediateRejectMachine_rejects :
    boundedDecide immediateRejectMachine 0 [true] = .reject := rfl

/-- A stuck nonhalting regression machine reports timeout. -/
theorem stuckMachine_times_out :
    boundedDecide stuckMachine 100 [false, true] = .timeout := rfl

/-- Zero fuel cannot take the leading-zero transition. -/
theorem acceptLeadingZeroMachine_zero_fuel_times_out :
    boundedDecide acceptLeadingZeroMachine 0 [false] = .timeout := rfl

/-- One unit of fuel takes exactly the leading-zero transition. -/
theorem acceptLeadingZeroMachine_one_fuel_accepts :
    boundedDecide acceptLeadingZeroMachine 1 [false] = .accept := rfl

end PNP.Concrete
