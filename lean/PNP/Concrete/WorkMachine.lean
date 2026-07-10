/-
Copyright (c) 2026 PNP Labs.

A finite nine-symbol work machine and a literal compiler to the concrete
three-symbol single-tape machine.  A work symbol is exactly a pair of raw
tape symbols.  The compiler implements one work transition by six raw
transitions; neither the source machine nor the compiled machine contains a
Lean function as executable program data.
-/

import PNP.Concrete.Machine

namespace PNP.Concrete

instance : ReflBEq TapeSymbol where
  rfl := by
    intro symbol
    cases symbol <;> rfl

instance : LawfulBEq TapeSymbol where
  eq_of_beq := by
    intro left right h
    cases left <;> cases right <;> first | rfl | contradiction

/-- The nine-symbol alphabet used by the readable work-machine layer. -/
structure WorkSymbol where
  first : TapeSymbol
  second : TapeSymbol
deriving BEq, DecidableEq, Repr

instance : ReflBEq WorkSymbol where
  rfl := by
    rintro ⟨first, second⟩
    cases first <;> cases second <;> rfl

instance : LawfulBEq WorkSymbol where
  eq_of_beq := by
    rintro ⟨leftFirst, leftSecond⟩ ⟨rightFirst, rightSecond⟩ h
    cases leftFirst <;> cases leftSecond <;>
      cases rightFirst <;> cases rightSecond <;>
      first | rfl | contradiction

namespace WorkSymbol

def blank : WorkSymbol := ⟨.blank, .blank⟩
def blankZero : WorkSymbol := ⟨.blank, .zero⟩
def blankOne : WorkSymbol := ⟨.blank, .one⟩
def zeroBlank : WorkSymbol := ⟨.zero, .blank⟩
def zeroZero : WorkSymbol := ⟨.zero, .zero⟩
def zeroOne : WorkSymbol := ⟨.zero, .one⟩
def oneBlank : WorkSymbol := ⟨.one, .blank⟩
def oneZero : WorkSymbol := ⟨.one, .zero⟩
def oneOne : WorkSymbol := ⟨.one, .one⟩

end WorkSymbol

/-- One transition in a finite work-machine program. -/
structure WorkRule where
  sourceState : Nat
  readSymbol : WorkSymbol
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove
deriving BEq, DecidableEq, Repr

/-- A work tape focused at one two-cell work symbol. -/
structure WorkTape where
  left : List WorkSymbol
  head : WorkSymbol
  right : List WorkSymbol
deriving BEq, DecidableEq, Repr

namespace WorkTape

def blank : WorkTape :=
  { left := [], head := WorkSymbol.blank, right := [] }

def write (tape : WorkTape) (symbol : WorkSymbol) : WorkTape :=
  { tape with head := symbol }

def moveLeft (tape : WorkTape) : WorkTape :=
  match tape.left with
  | [] =>
      { left := []
        head := WorkSymbol.blank
        right := tape.head :: tape.right }
  | symbol :: rest =>
      { left := rest
        head := symbol
        right := tape.head :: tape.right }

def moveRight (tape : WorkTape) : WorkTape :=
  match tape.right with
  | [] =>
      { left := tape.head :: tape.left
        head := WorkSymbol.blank
        right := [] }
  | symbol :: rest =>
      { left := tape.head :: tape.left
        head := symbol
        right := rest }

def move (tape : WorkTape) : HeadMove → WorkTape
  | .left => tape.moveLeft
  | .stay => tape
  | .right => tape.moveRight

end WorkTape

structure WorkConfiguration where
  state : Nat
  tape : WorkTape
deriving BEq, DecidableEq, Repr

/-- Finite syntax for a deterministic work machine. -/
structure WorkMachine where
  rules : List WorkRule
  startState : Nat
  acceptState : Nat
  rejectState : Nat
deriving BEq, DecidableEq, Repr

/-- First matching work rule, paired with its zero-based list index. -/
private inductive WorkRuleMatch (rule : WorkRule) (state : Nat)
    (symbol : WorkSymbol) where
  | no
  | yes (source_eq : rule.sourceState = state)
      (symbol_eq : rule.readSymbol = symbol)

private def inspectWorkRule (rule : WorkRule) (state : Nat)
    (symbol : WorkSymbol) : WorkRuleMatch rule state symbol :=
  if hSource : rule.sourceState = state then
    if hSymbol : rule.readSymbol = symbol then
      .yes hSource hSymbol
    else
      .no
  else
    .no

def findIndexedWorkRuleFrom :
    List WorkRule → Nat → WorkSymbol → Nat → Option (Nat × WorkRule)
  | [], _, _, _ => none
  | rule :: rest, state, symbol, index =>
      match inspectWorkRule rule state symbol with
      | .yes _ _ => some (index, rule)
      | .no => findIndexedWorkRuleFrom rest state symbol (index + 1)

def findIndexedWorkRule (rules : List WorkRule) (state : Nat)
    (symbol : WorkSymbol) : Option (Nat × WorkRule) :=
  findIndexedWorkRuleFrom rules state symbol 0

def findWorkRule (rules : List WorkRule) (state : Nat)
    (symbol : WorkSymbol) : Option WorkRule :=
  match findIndexedWorkRule rules state symbol with
  | none => none
  | some (_, rule) => some rule

theorem findIndexedWorkRuleFrom_some_matches
    {rules : List WorkRule} {state : Nat} {symbol : WorkSymbol}
    {index foundIndex : Nat} {rule : WorkRule}
    (h : findIndexedWorkRuleFrom rules state symbol index =
      some (foundIndex, rule)) :
    rule.sourceState = state ∧ rule.readSymbol = symbol := by
  induction rules generalizing index with
  | nil => contradiction
  | cons first rest ih =>
      unfold findIndexedWorkRuleFrom at h
      cases hMatch : inspectWorkRule first state symbol with
      | no =>
          rw [hMatch] at h
          exact ih h
      | yes hFirstSource hFirstSymbol =>
          rw [hMatch] at h
          have hPair : (index, first) = (foundIndex, rule) :=
            Option.some.inj h
          have hRule : first = rule := congrArg Prod.snd hPair
          exact
            ⟨(congrArg WorkRule.sourceState hRule).symm.trans hFirstSource,
             (congrArg WorkRule.readSymbol hRule).symm.trans hFirstSymbol⟩

def WorkMachine.isHalted (machine : WorkMachine)
    (config : WorkConfiguration) : Bool :=
  config.state == machine.acceptState || config.state == machine.rejectState

def workStartConfiguration (machine : WorkMachine) (tape : WorkTape) :
    WorkConfiguration :=
  { state := machine.startState, tape := tape }

def applyWorkRule (rule : WorkRule) (config : WorkConfiguration) :
    WorkConfiguration :=
  { state := rule.targetState
    tape := (config.tape.write rule.writeSymbol).move rule.move }

def workStep? (machine : WorkMachine) (config : WorkConfiguration) :
    Option WorkConfiguration :=
  if machine.isHalted config then
    none
  else
    match findWorkRule machine.rules config.state config.tape.head with
    | none => none
    | some rule => some (applyWorkRule rule config)

def workRun (machine : WorkMachine) : Nat → WorkConfiguration → WorkConfiguration
  | 0, config => config
  | fuel + 1, config =>
      match workStep? machine config with
      | none => config
      | some next => workRun machine fuel next

/-- Execute exactly `steps` transitions, failing when execution stops early. -/
def workRunExact? (machine : WorkMachine) :
    Nat → WorkConfiguration → Option WorkConfiguration
  | 0, config => some config
  | steps + 1, config =>
      match workStep? machine config with
      | none => none
      | some next => workRunExact? machine steps next

inductive WorkVerdict where
  | accept
  | reject
  | timeout
deriving BEq, DecidableEq, Repr

def workBoundedDecide (machine : WorkMachine) (fuel : Nat)
    (initialTape : WorkTape) : WorkVerdict :=
  let final := workRun machine fuel (workStartConfiguration machine initialTape)
  if final.state == machine.acceptState then
    .accept
  else if final.state == machine.rejectState then
    .reject
  else
    .timeout

/-! ### Literal two-cell encoding -/

/-- Raw cells strictly to the left of a work focus, nearest first. -/
def encodeWorkLeft : List WorkSymbol → List TapeSymbol
  | [] => []
  | symbol :: rest => symbol.second :: symbol.first :: encodeWorkLeft rest

/-- Raw cells strictly to the right of a work focus, ordinary left-to-right. -/
def encodeWorkRight : List WorkSymbol → List TapeSymbol
  | [] => []
  | symbol :: rest => symbol.first :: symbol.second :: encodeWorkRight rest

/-- Encode a focused work tape with the raw head on the first component. -/
def encodeWorkTape (tape : WorkTape) : Tape :=
  { left := encodeWorkLeft tape.left
    head := tape.head.first
    right := tape.head.second :: encodeWorkRight tape.right }

/-! ### Compiler state and finite rule syntax -/

private def rawSymbolCode : TapeSymbol → Nat
  | .blank => 0
  | .zero => 1
  | .one => 2

private def boundaryState (state : Nat) : Nat := 8 * state

private def dispatchState (state : Nat) (first : TapeSymbol) : Nat :=
  8 * (3 * state + rawSymbolCode first) + 1

private def workSymbolCode (symbol : WorkSymbol) : Nat :=
  3 * rawSymbolCode symbol.first + rawSymbolCode symbol.second

private def selectedState (state : Nat) (symbol : WorkSymbol)
    (stage : Nat) : Nat :=
  8 * (9 * state + workSymbolCode symbol) + stage

private def rawSymbols : List TapeSymbol := [.blank, .zero, .one]

private def preserveRules (source target : Nat) (movement : HeadMove) :
    List Rule :=
  rawSymbols.map (fun symbol =>
    { sourceState := source
      readSymbol := symbol
      targetState := target
      writeSymbol := symbol
      move := movement })

private def compileWorkRule (_index : Nat) (rule : WorkRule) : List Rule :=
  [ { sourceState := boundaryState rule.sourceState
      readSymbol := rule.readSymbol.first
      targetState := dispatchState rule.sourceState rule.readSymbol.first
      writeSymbol := rule.readSymbol.first
      move := .right }
  , { sourceState := dispatchState rule.sourceState rule.readSymbol.first
      readSymbol := rule.readSymbol.second
      targetState := selectedState rule.sourceState rule.readSymbol 2
      writeSymbol := rule.writeSymbol.second
      move := .left }
  , { sourceState := selectedState rule.sourceState rule.readSymbol 2
      readSymbol := rule.readSymbol.first
      targetState := selectedState rule.sourceState rule.readSymbol 3
      writeSymbol := rule.writeSymbol.first
      move := .stay }
  , { sourceState := selectedState rule.sourceState rule.readSymbol 3
      readSymbol := rule.writeSymbol.first
      targetState := selectedState rule.sourceState rule.readSymbol 4
      writeSymbol := rule.writeSymbol.first
      move := rule.move }
  ] ++ preserveRules
      (selectedState rule.sourceState rule.readSymbol 4)
      (selectedState rule.sourceState rule.readSymbol 5) rule.move ++
    preserveRules
      (selectedState rule.sourceState rule.readSymbol 5)
      (boundaryState rule.targetState) .stay

private def compileWorkRulesFrom : Nat → List WorkRule → List Rule
  | _, [] => []
  | index, rule :: rest =>
      compileWorkRule index rule ++ compileWorkRulesFrom (index + 1) rest

/-- Compile a finite work-machine rule list to a finite raw rule list. -/
def compileWorkMachine (machine : WorkMachine) : Machine :=
  { rules := compileWorkRulesFrom 0 machine.rules
    startState := boundaryState machine.startState
    acceptState := boundaryState machine.acceptState
    rejectState := boundaryState machine.rejectState }

/-- Encode a macro-boundary work configuration as a raw configuration. -/
def encodeWorkConfiguration (config : WorkConfiguration) : Configuration :=
  { state := boundaryState config.state
    tape := encodeWorkTape config.tape }

end PNP.Concrete
