/-
Copyright (c) 2026 PNP Labs.

Literal finite-control substrate for the strict-v0 locked-NAND target emitter.

This file deliberately starts below the semantic builder layer.  Its executable
rule table knows only the nine work symbols, the twelve fixed strict-v0 token
tags, and two context-local boundary symbols.  In particular, no transition
rule calls `decodeCircuit`, `targetBytes`, `rawLockedInstance`, or any other
host-side source-to-target function.

The true source-to-target machine must enter on `rawInputWorkTape bits`: a
grammar-decodable circuit with out-of-range references still has a direct raw
target and therefore must not be routed through the stricter well-formedness
parser.  `restoredSourceEntryConfiguration` below is an exact canonical-source
endpoint for later non-destructive grammar-controller proofs; it is not a
composition claim about the existing well-formedness parser.

The finite table in this module is the target-token append primitive used by
that controller.  It scans the retained packed source, scans the already
emitted target, appends exactly the requested strict-v0 token, and returns to
the first source cell.  A request is represented only by one of twelve literal
control-state blocks.  Target bytes are never preloaded into its workspace.
-/

import PNP.Concrete.LockedNANDRawBuilder
import PNP.Concrete.LockedNANDSourceParserValidTrace

namespace PNP.Concrete.LockedNAND.TargetEmitter

open PNP.Concrete

/-! ### Literal alphabet and context-local workspace markers -/

def allWorkSymbols : List WorkSymbol :=
  [WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
   WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

/-- Packed source and packed target cells use exactly these four symbols. -/
def packedSymbols : List WorkSymbol :=
  [WorkSymbol.zeroZero, WorkSymbol.zeroOne,
   WorkSymbol.oneZero, WorkSymbol.oneOne]

/-- Left boundary of the retained packed source.  Its meaning is contextual. -/
def sourceLeftBoundary : WorkSymbol := WorkSymbol.blankZero

/-- Boundary between the retained source and the growing target. -/
def sourceTargetBoundary : WorkSymbol := WorkSymbol.blankOne

/-- One unary unit in a controller register or check-stack record. -/
def unaryUnit : WorkSymbol := WorkSymbol.zeroBlank

/-- Separator between adjacent unary controller records. -/
def unarySeparator : WorkSymbol := WorkSymbol.oneBlank

inductive PackedSymbol : WorkSymbol → Prop where
  | zeroZero : PackedSymbol WorkSymbol.zeroZero
  | zeroOne : PackedSymbol WorkSymbol.zeroOne
  | oneZero : PackedSymbol WorkSymbol.oneZero
  | oneOne : PackedSymbol WorkSymbol.oneOne

theorem packedSymbol_mem {symbol : WorkSymbol}
    (ordinary : PackedSymbol symbol) :
    symbol ∈ packedSymbols := by
  cases ordinary <;> simp [packedSymbols]

/-! ### Unary controller registers and the pending-source check stack -/

/-- Logical unary registers needed by the fixed-template raw construction.
The physical word is nearest-first on the left side of the work head. -/
structure UnaryRegisters where
  inputCount : Nat
  normalizedGateCount : Nat
  carrierWidth : Nat
  baseline : Nat
  currentGate : Nat
  outputIndex : Nat
deriving BEq, DecidableEq, Repr

def zeroRegisters : UnaryRegisters :=
  { inputCount := 0
    normalizedGateCount := 0
    carrierWidth := 0
    baseline := 0
    currentGate := 0
    outputIndex := 0 }

def unaryWord (value : Nat) : List WorkSymbol :=
  List.replicate value unaryUnit

def unaryRecord (value : Nat) : List WorkSymbol :=
  unaryWord value ++ [unarySeparator]

/-- Physical register bank, in the order in which a returning controller sees
it after crossing the source-left boundary. -/
def registerBank (registers : UnaryRegisters) : List WorkSymbol :=
  unaryRecord registers.inputCount ++
  unaryRecord registers.normalizedGateCount ++
  unaryRecord registers.carrierWidth ++
  unaryRecord registers.baseline ++
  unaryRecord registers.currentGate ++
  unaryRecord registers.outputIndex

/-- One pending source coordinate.  The newest record is placed first. -/
def checkRecord (coordinate : Nat) : List WorkSymbol :=
  unaryWord coordinate ++ [unarySeparator]

def checkStack (coordinates : List Nat) : List WorkSymbol :=
  coordinates.reverse.flatMap checkRecord

/-- Everything to the left of the retained source.  `outsideLeft` is explicit
so later composition can preserve unrelated caller workspace. -/
def controllerLeftWorkspace (registers : UnaryRegisters)
    (coordinates : List Nat) (outsideLeft : List WorkSymbol) :
    List WorkSymbol :=
  sourceLeftBoundary ::
    (registerBank registers ++ checkStack coordinates ++ outsideLeft)

theorem unaryWord_length (value : Nat) :
    (unaryWord value).length = value := by
  simp [unaryWord]

theorem unaryRecord_length (value : Nat) :
    (unaryRecord value).length = value + 1 := by
  simp [unaryRecord, unaryWord]

theorem checkRecord_length (coordinate : Nat) :
    (checkRecord coordinate).length = coordinate + 1 := by
  simp [checkRecord, unaryWord]

/-! ### Strict-v0 token requests as literal finite control -/

def allTokens : List Token :=
  [.version0, .unit, .natEnd, .input,
   .constantFalse, .constantTrue, .gate, .gateEnd,
   .programEnd, .outputsEnd, .threshold, .instanceEnd]

def tokenCode : Token → Nat
  | .version0 => 0
  | .unit => 1
  | .natEnd => 2
  | .input => 3
  | .constantFalse => 4
  | .constantTrue => 5
  | .gate => 6
  | .gateEnd => 7
  | .programEnd => 8
  | .outputsEnd => 9
  | .threshold => 10
  | .instanceEnd => 11

/-- First packed two-bit cell of each literal four-bit token tag. -/
def tokenFirstSymbol : Token → WorkSymbol
  | .version0 => WorkSymbol.zeroZero
  | .unit => WorkSymbol.zeroZero
  | .natEnd => WorkSymbol.zeroZero
  | .input => WorkSymbol.zeroZero
  | .constantFalse => WorkSymbol.zeroOne
  | .constantTrue => WorkSymbol.zeroOne
  | .gate => WorkSymbol.zeroOne
  | .gateEnd => WorkSymbol.zeroOne
  | .programEnd => WorkSymbol.oneZero
  | .outputsEnd => WorkSymbol.oneZero
  | .threshold => WorkSymbol.oneZero
  | .instanceEnd => WorkSymbol.oneZero

/-- Second packed two-bit cell of each literal four-bit token tag. -/
def tokenSecondSymbol : Token → WorkSymbol
  | .version0 => WorkSymbol.zeroZero
  | .unit => WorkSymbol.zeroOne
  | .natEnd => WorkSymbol.oneZero
  | .input => WorkSymbol.oneOne
  | .constantFalse => WorkSymbol.zeroZero
  | .constantTrue => WorkSymbol.zeroOne
  | .gate => WorkSymbol.oneZero
  | .gateEnd => WorkSymbol.oneOne
  | .programEnd => WorkSymbol.zeroZero
  | .outputsEnd => WorkSymbol.zeroOne
  | .threshold => WorkSymbol.oneZero
  | .instanceEnd => WorkSymbol.oneOne

def tokenSymbols (token : Token) : List WorkSymbol :=
  [tokenFirstSymbol token, tokenSecondSymbol token]

theorem tokenSymbols_eq_parser_cells (token : Token) :
    tokenSymbols token = SourceParser.tokenCells token := by
  cases token <;> rfl

def acceptState : Nat := 0
def rejectState : Nat := 1
def deadState : Nat := 2

def seekSourceState (token : Token) : Nat :=
  3 + 5 * tokenCode token

def seekTargetState (token : Token) : Nat :=
  seekSourceState token + 1

def writeSecondState (token : Token) : Nat :=
  seekSourceState token + 2

def rewindTargetState (token : Token) : Nat :=
  seekSourceState token + 3

def rewindSourceState (token : Token) : Nat :=
  seekSourceState token + 4

/-- The two source-driven framing states occupy the first states after the
twelve five-state token blocks. -/
def frameSeekEndState : Nat := 63
def frameReturnState : Nat := 64

/-- A total action row for one active control state.  Unexpected symbols enter
the non-halting, ruleless dead state and therefore fail closed. -/
structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def seekSourceAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (seekSourceState token, symbol, .right)
  else if symbol = sourceTargetBoundary then
    (seekTargetState token, symbol, .right)
  else
    deadAction symbol

def seekTargetAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (seekTargetState token, symbol, .right)
  else if symbol = WorkSymbol.blank then
    (writeSecondState token, tokenFirstSymbol token, .right)
  else
    deadAction symbol

def writeSecondAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (rewindTargetState token, tokenSecondSymbol token, .left)
  else
    deadAction symbol

def rewindTargetAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (rewindTargetState token, symbol, .left)
  else if symbol = sourceTargetBoundary then
    (rewindSourceState token, symbol, .left)
  else
    deadAction symbol

def rewindSourceAction (token : Token) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (rewindSourceState token, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

/-- Scan a raw packed input to its first blank and materialize the
source/target boundary there. -/
def frameSeekEndAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (frameSeekEndState, symbol, .right)
  else if symbol = WorkSymbol.blank then
    (frameReturnState, sourceTargetBoundary, .left)
  else
    deadAction symbol

/-- Return over the untouched packed input, install its left boundary, and
launch the first literal target-token request (`version0`). -/
def frameReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.zeroZero ∨ symbol = WorkSymbol.zeroOne ∨
      symbol = WorkSymbol.oneZero ∨ symbol = WorkSymbol.oneOne then
    (frameReturnState, symbol, .left)
  else if symbol = WorkSymbol.blank then
    (seekSourceState .version0, sourceLeftBoundary, .right)
  else
    deadAction symbol

def tokenPrograms (token : Token) : List StateProgram :=
  [{ state := seekSourceState token, action := seekSourceAction token },
   { state := seekTargetState token, action := seekTargetAction token },
   { state := writeSecondState token, action := writeSecondAction token },
   { state := rewindTargetState token, action := rewindTargetAction token },
   { state := rewindSourceState token, action := rewindSourceAction token }]

def framePrograms : List StateProgram :=
  [{ state := frameSeekEndState, action := frameSeekEndAction },
   { state := frameReturnState, action := frameReturnAction }]

def statePrograms : List StateProgram :=
  framePrograms ++ allTokens.flatMap tokenPrograms

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

/-- The executable 558-rule table.  It is closed finite data after reduction. -/
def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

theorem allWorkSymbols_length :
    allWorkSymbols.length = 9 := by
  rfl

theorem allTokens_length :
    allTokens.length = 12 := by
  rfl

theorem tokenPrograms_length (token : Token) :
    (tokenPrograms token).length = 5 := by
  rfl

theorem statePrograms_length :
    statePrograms.length = 62 := by
  rfl

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  simp [rulesAt, allWorkSymbols_length]

theorem rules_length :
    rules.length = 558 := by
  change (statePrograms.flatMap rulesAt).length = 558
  have materializedLength :
      ∀ programs : List StateProgram,
        (programs.flatMap rulesAt).length = 9 * programs.length := by
    intro programs
    induction programs with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.flatMap_cons, List.length_append,
          rulesAt_length, ih, List.length_cons, Nat.mul_succ]
        omega
  rw [materializedLength, statePrograms_length]

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

private theorem rulesAt_pairwise_query_distinct
    (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols
  simp [QueryDistinct, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source_eq {program : StateProgram}
    {rule : WorkRule} (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with ⟨symbol, _symbolMember, hRule⟩
  rw [← hRule]

private theorem materializedPrograms_pairwise_query_distinct
    (programs : List StateProgram)
    (stateDistinct : programs.Pairwise fun left right =>
      left.state ≠ right.state) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil => exact List.Pairwise.nil
  | cons first rest ih =>
      cases stateDistinct with
      | cons firstDistinct restDistinct =>
          change
            (rulesAt first ++ rest.flatMap rulesAt).Pairwise
              QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨rulesAt_pairwise_query_distinct first,
             ih restDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember, rightRuleMember⟩
          have sourceNe :=
            firstDistinct rightProgram rightProgramMember
          have leftSource := rulesAt_source_eq leftMember
          have rightSource := rulesAt_source_eq rightRuleMember
          have sourceEq := congrArg Prod.fst queryEq
          exact sourceNe
            (leftSource.symm.trans (sourceEq.trans rightSource))

private theorem statePrograms_pairwise_state_distinct :
    statePrograms.Pairwise fun left right => left.state ≠ right.state := by
  set_option maxRecDepth 100000 in
    decide

/-- Deterministic rule queries are pairwise distinct across the whole table. -/
theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  exact materializedPrograms_pairwise_query_distinct statePrograms
    statePrograms_pairwise_state_distinct

theorem accept_ne_reject :
    acceptState ≠ rejectState := by
  decide

/-- The same literal table can be entered at any of the twelve token-request
blocks. -/
def machineFor (token : Token) : WorkMachine :=
  { rules := rules
    startState := seekSourceState token
    acceptState := acceptState
    rejectState := rejectState }

def machine : WorkMachine :=
  { rules := rules
    startState := frameSeekEndState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachineFor (token : Token) : Machine :=
  compileWorkMachine (machineFor token)

def compiledMachine : Machine :=
  compileWorkMachine machine

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem accept_configuration_halted (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := acceptState, tape := tape } = true := by
  rfl

theorem reject_configuration_halted (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := rejectState, tape := tape } = true := by
  rfl

theorem dead_configuration_not_halted (token : Token) (tape : WorkTape) :
    (machineFor token).isHalted
      { state := deadState, tape := tape } = false := by
  rfl

/-! ### Exact mechanics of one source-driven token append -/

def configAtWord (state : Nat) (leftSide word : List WorkSymbol) :
    WorkConfiguration :=
  match word with
  | [] =>
      { state := state
        tape := { left := leftSide, head := WorkSymbol.blank, right := [] } }
  | head :: rightSide =>
      { state := state
        tape := { left := leftSide, head := head, right := rightSide } }

def configAtLeftWord (state : Nat)
    (leftWord rightSide : List WorkSymbol) : WorkConfiguration :=
  match leftWord with
  | [] =>
      { state := state
        tape := { left := [], head := WorkSymbol.blank, right := rightSide } }
  | head :: leftSide =>
      { state := state
        tape := { left := leftSide, head := head, right := rightSide } }

/-- Move a left-to-right word across the focus onto the nearest-first left
side. -/
private def pushLeft : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], farSide => farSide
  | head :: rest, farSide => pushLeft rest (head :: farSide)

private theorem pushLeft_eq_reverse_append
    (word farSide : List WorkSymbol) :
    pushLeft word farSide = word.reverse ++ farSide := by
  induction word generalizing farSide with
  | nil => rfl
  | cons head rest ih =>
      simp only [pushLeft, ih, List.reverse_cons, List.append_assoc]
      rfl

private theorem workRunExact_compose (machine : WorkMachine)
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

private theorem workRunExact_one (machine : WorkMachine)
    (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change (match workStep? machine start with
    | none => none
    | some result => some result) = some next
  rw [hStep]

private theorem scanRightExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtWord state leftSide (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) hHead]
      exact ih (head :: leftSide) hRest

private theorem scanLeftExact (machine : WorkMachine) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil => rfl
  | cons head rest ih =>
      have hHead : Allowed head := hAllowed head (List.Mem.head rest)
      have hRest : ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? machine
          (configAtLeftWord state (head :: (rest ++ leftSuffix))
            rightSide) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide hHead]
      exact ih (head :: rightSide) hRest

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

set_option maxRecDepth 200000 in
private theorem find_seekSource_packed (token : Token)
    (symbol : WorkSymbol) (ordinary : PackedSymbol symbol) :
    findWorkRule rules (seekSourceState token) symbol =
      some (literalRule (seekSourceState token) symbol
        (seekSourceState token) symbol .right) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekSource_boundary (token : Token) :
    findWorkRule rules (seekSourceState token) sourceTargetBoundary =
      some (literalRule (seekSourceState token) sourceTargetBoundary
        (seekTargetState token) sourceTargetBoundary .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekTarget_packed (token : Token)
    (symbol : WorkSymbol) (ordinary : PackedSymbol symbol) :
    findWorkRule rules (seekTargetState token) symbol =
      some (literalRule (seekTargetState token) symbol
        (seekTargetState token) symbol .right) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekTarget_blank (token : Token) :
    findWorkRule rules (seekTargetState token) WorkSymbol.blank =
      some (literalRule (seekTargetState token) WorkSymbol.blank
        (writeSecondState token) (tokenFirstSymbol token) .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_writeSecond_blank (token : Token) :
    findWorkRule rules (writeSecondState token) WorkSymbol.blank =
      some (literalRule (writeSecondState token) WorkSymbol.blank
        (rewindTargetState token) (tokenSecondSymbol token) .left) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindTarget_packed (token : Token)
    (symbol : WorkSymbol) (ordinary : PackedSymbol symbol) :
    findWorkRule rules (rewindTargetState token) symbol =
      some (literalRule (rewindTargetState token) symbol
        (rewindTargetState token) symbol .left) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindTarget_boundary (token : Token) :
    findWorkRule rules (rewindTargetState token) sourceTargetBoundary =
      some (literalRule (rewindTargetState token) sourceTargetBoundary
        (rewindSourceState token) sourceTargetBoundary .left) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindSource_packed (token : Token)
    (symbol : WorkSymbol) (ordinary : PackedSymbol symbol) :
    findWorkRule rules (rewindSourceState token) symbol =
      some (literalRule (rewindSourceState token) symbol
        (rewindSourceState token) symbol .left) := by
  cases ordinary <;> cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_rewindSource_boundary (token : Token) :
    findWorkRule rules (rewindSourceState token) sourceLeftBoundary =
      some (literalRule (rewindSourceState token) sourceLeftBoundary
        acceptState sourceLeftBoundary .right) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem seekSource_packed_step (token : Token)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (symbol :: suffix)) =
      some (configAtWord (seekSourceState token)
        (symbol :: leftSide) suffix) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekSourceState token) leftSide
          (symbol :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (symbol :: suffix)) =
      some (applyWorkRule
        (literalRule (seekSourceState token) symbol
          (seekSourceState token) symbol .right)
        (configAtWord (seekSourceState token) leftSide
          (symbol :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekSource_packed token symbol ordinary)
    _ = some (configAtWord (seekSourceState token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem seekSource_boundary_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) =
      some (configAtWord (seekTargetState token)
        (sourceTargetBoundary :: leftSide) suffix) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix)) =
      some (applyWorkRule
        (literalRule (seekSourceState token) sourceTargetBoundary
          (seekTargetState token) sourceTargetBoundary .right)
        (configAtWord (seekSourceState token) leftSide
          (sourceTargetBoundary :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekSource_boundary token)
    _ = some (configAtWord (seekTargetState token)
        (sourceTargetBoundary :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem seekTarget_packed_step (token : Token)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (symbol :: suffix)) =
      some (configAtWord (seekTargetState token)
        (symbol :: leftSide) suffix) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekTargetState token) leftSide
          (symbol :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (symbol :: suffix)) =
      some (applyWorkRule
        (literalRule (seekTargetState token) symbol
          (seekTargetState token) symbol .right)
        (configAtWord (seekTargetState token) leftSide
          (symbol :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekTarget_packed token symbol ordinary)
    _ = some (configAtWord (seekTargetState token)
        (symbol :: leftSide) suffix) := by
      cases suffix <;> rfl

set_option maxRecDepth 200000 in
private theorem writeFirst_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) =
      some (configAtWord (writeSecondState token)
        (tokenFirstSymbol token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix)) =
      some (applyWorkRule
        (literalRule (seekTargetState token) WorkSymbol.blank
          (writeSecondState token) (tokenFirstSymbol token) .right)
        (configAtWord (seekTargetState token) leftSide
          (WorkSymbol.blank :: WorkSymbol.blank :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekTarget_blank token)
    _ = some (configAtWord (writeSecondState token)
        (tokenFirstSymbol token :: leftSide)
        (WorkSymbol.blank :: suffix)) := by
      rfl

set_option maxRecDepth 200000 in
private theorem writeSecond_step (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtWord (writeSecondState token)
          (tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) =
      some (configAtLeftWord (rewindTargetState token)
        (tokenFirstSymbol token :: leftSide)
        (tokenSecondSymbol token :: suffix)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (writeSecondState token)
          (tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (writeSecondState token)
          (tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix)) =
      some (applyWorkRule
        (literalRule (writeSecondState token) WorkSymbol.blank
          (rewindTargetState token) (tokenSecondSymbol token) .left)
        (configAtWord (writeSecondState token)
          (tokenFirstSymbol token :: leftSide)
          (WorkSymbol.blank :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_writeSecond_blank token)
    _ = some (configAtLeftWord (rewindTargetState token)
        (tokenFirstSymbol token :: leftSide)
        (tokenSecondSymbol token :: suffix)) := by
      rfl

set_option maxRecDepth 200000 in
private theorem rewindTarget_packed_step (token : Token)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    workStep? (machineFor token)
        (configAtLeftWord (rewindTargetState token)
          (symbol :: leftTail) rightSide) =
      some (configAtLeftWord (rewindTargetState token)
        leftTail (symbol :: rightSide)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtLeftWord (rewindTargetState token)
          (symbol :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtLeftWord (rewindTargetState token)
          (symbol :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (rewindTargetState token) symbol
          (rewindTargetState token) symbol .left)
        (configAtLeftWord (rewindTargetState token)
          (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_rewindTarget_packed token symbol ordinary)
    _ = some (configAtLeftWord (rewindTargetState token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindTarget_boundary_step (token : Token)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtLeftWord (rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) =
      some (configAtLeftWord (rewindSourceState token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtLeftWord (rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtLeftWord (rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (rewindTargetState token) sourceTargetBoundary
          (rewindSourceState token) sourceTargetBoundary .left)
        (configAtLeftWord (rewindTargetState token)
          (sourceTargetBoundary :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_rewindTarget_boundary token)
    _ = some (configAtLeftWord (rewindSourceState token)
        leftTail (sourceTargetBoundary :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindSource_packed_step (token : Token)
    (leftTail rightSide : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    workStep? (machineFor token)
        (configAtLeftWord (rewindSourceState token)
          (symbol :: leftTail) rightSide) =
      some (configAtLeftWord (rewindSourceState token)
        leftTail (symbol :: rightSide)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtLeftWord (rewindSourceState token)
          (symbol :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtLeftWord (rewindSourceState token)
          (symbol :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (rewindSourceState token) symbol
          (rewindSourceState token) symbol .left)
        (configAtLeftWord (rewindSourceState token)
          (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_rewindSource_packed token symbol ordinary)
    _ = some (configAtLeftWord (rewindSourceState token)
        leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

set_option maxRecDepth 200000 in
private theorem rewindSource_boundary_step (token : Token)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtLeftWord (rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) =
      some (configAtWord acceptState
        (sourceLeftBoundary :: leftTail) rightSide) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtLeftWord (rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtLeftWord (rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide) =
      some (applyWorkRule
        (literalRule (rewindSourceState token) sourceLeftBoundary
          acceptState sourceLeftBoundary .right)
        (configAtLeftWord (rewindSourceState token)
          (sourceLeftBoundary :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_rewindSource_boundary token)
    _ = some (configAtWord acceptState
        (sourceLeftBoundary :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem tokenFirst_packed (token : Token) :
    PackedSymbol (tokenFirstSymbol token) := by
  cases token <;> constructor

private theorem tokenSecond_packed (token : Token) :
    PackedSymbol (tokenSecondSymbol token) := by
  cases token <;> constructor

theorem packedTokenCells_packed (tokens : List Token) :
    ∀ symbol, symbol ∈ SourceParser.packedTokenCells tokens →
      PackedSymbol symbol := by
  induction tokens with
  | nil =>
      intro symbol found
      contradiction
  | cons token rest ih =>
      intro symbol found
      simp only [SourceParser.packedTokenCells, List.mem_append] at found
      cases found with
      | inl tokenMember =>
          rw [← tokenSymbols_eq_parser_cells] at tokenMember
          have pairMembership :
              symbol = tokenFirstSymbol token ∨
                symbol = tokenSecondSymbol token := by
            simpa [tokenSymbols] using tokenMember
          rcases pairMembership with first | second
          · subst symbol
            exact tokenFirst_packed token
          · subst symbol
            exact tokenSecond_packed token
      | inr restMember =>
          exact ih symbol restMember

theorem circuitCells_packed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ SourceParser.circuitCells raw →
      PackedSymbol symbol := by
  intro symbol found
  rw [← SourceParser.packedTokenCells_encodeCircuitTokens raw] at found
  exact packedTokenCells_packed (encodeCircuitTokens raw) symbol found

def appendPackedEntry (token : Token)
    (source target controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord (seekSourceState token)
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight))))

def appendPackedFinal (source target : List WorkSymbol)
    (token : Token) (controllerOutside outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary :: controllerOutside)
    (source ++
      (sourceTargetBoundary ::
        (target ++ tokenSymbols token ++
          (WorkSymbol.blank :: outsideRight))))

def packedAppendWorkSteps (source target : List WorkSymbol) : Nat :=
  2 * source.length + 2 * target.length + 6

/-- Exact operational correctness of one literal token request.  The source
and existing target are arbitrary packed words; both remain byte-for-byte
unchanged, the requested token is appended, and arbitrary workspace outside
the reserved three blank cells is preserved. -/
theorem appendPacked_exact (token : Token)
    (source target controllerOutside outsideRight : List WorkSymbol)
    (sourcePacked : ∀ symbol, symbol ∈ source → PackedSymbol symbol)
    (targetPacked : ∀ symbol, symbol ∈ target → PackedSymbol symbol) :
    workRunExact? (machineFor token)
        (packedAppendWorkSteps source target)
        (appendPackedEntry token source target
          controllerOutside outsideRight) =
      some (appendPackedFinal source target token
        controllerOutside outsideRight) := by
  let baseLeft := sourceLeftBoundary :: controllerOutside
  let afterSourceLeft := pushLeft source baseLeft
  let afterBoundaryLeft := sourceTargetBoundary :: afterSourceLeft
  let afterTargetLeft := pushLeft target afterBoundaryLeft
  let targetAndTokenRight :=
    target ++ tokenSymbols token ++ (WorkSymbol.blank :: outsideRight)
  have hSource :
      workRunExact? (machineFor token) source.length
          (configAtWord (seekSourceState token) baseLeft
            (source ++
              (sourceTargetBoundary ::
                (target ++
                  (WorkSymbol.blank :: WorkSymbol.blank ::
                    WorkSymbol.blank :: outsideRight))))) =
        some (configAtWord (seekSourceState token) afterSourceLeft
          (sourceTargetBoundary ::
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight)))) := by
    exact scanRightExact (machineFor token) (seekSourceState token)
      PackedSymbol
      (fun left head suffix ordinary =>
        seekSource_packed_step token left suffix head ordinary)
      source
      (sourceTargetBoundary ::
        (target ++
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)))
      baseLeft sourcePacked
  have hSourceBoundary :
      workRunExact? (machineFor token) 1
          (configAtWord (seekSourceState token) afterSourceLeft
            (sourceTargetBoundary ::
              (target ++
                (WorkSymbol.blank :: WorkSymbol.blank ::
                  WorkSymbol.blank :: outsideRight)))) =
        some (configAtWord (seekTargetState token) afterBoundaryLeft
          (target ++
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight))) := by
    apply workRunExact_one
    exact seekSource_boundary_step token afterSourceLeft
      (target ++
        (WorkSymbol.blank :: WorkSymbol.blank ::
          WorkSymbol.blank :: outsideRight))
  have hTarget :
      workRunExact? (machineFor token) target.length
          (configAtWord (seekTargetState token) afterBoundaryLeft
            (target ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight))) =
        some (configAtWord (seekTargetState token) afterTargetLeft
          (WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight)) := by
    exact scanRightExact (machineFor token) (seekTargetState token)
      PackedSymbol
      (fun left head suffix ordinary =>
        seekTarget_packed_step token left suffix head ordinary)
      target
      (WorkSymbol.blank :: WorkSymbol.blank ::
        WorkSymbol.blank :: outsideRight)
      afterBoundaryLeft targetPacked
  have hFirst :
      workRunExact? (machineFor token) 1
          (configAtWord (seekTargetState token) afterTargetLeft
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight)) =
        some (configAtWord (writeSecondState token)
          (tokenFirstSymbol token :: afterTargetLeft)
          (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one
    exact writeFirst_step token afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have hSecond :
      workRunExact? (machineFor token) 1
          (configAtWord (writeSecondState token)
            (tokenFirstSymbol token :: afterTargetLeft)
            (WorkSymbol.blank :: WorkSymbol.blank :: outsideRight)) =
        some (configAtLeftWord (rewindTargetState token)
          (tokenFirstSymbol token :: afterTargetLeft)
          (tokenSecondSymbol token ::
            WorkSymbol.blank :: outsideRight)) := by
    apply workRunExact_one
    exact writeSecond_step token afterTargetLeft
      (WorkSymbol.blank :: outsideRight)
  have rewindTargetPacked :
      ∀ symbol, symbol ∈ tokenFirstSymbol token :: target.reverse →
        PackedSymbol symbol := by
    intro symbol found
    cases found with
    | head =>
        exact tokenFirst_packed token
    | tail _ tailMember =>
        exact targetPacked symbol (List.mem_reverse.mp tailMember)
  have hRewindTarget :
      workRunExact? (machineFor token) (target.length + 1)
          (configAtLeftWord (rewindTargetState token)
            (tokenFirstSymbol token :: afterTargetLeft)
            (tokenSecondSymbol token ::
              WorkSymbol.blank :: outsideRight)) =
        some (configAtLeftWord (rewindTargetState token)
          afterBoundaryLeft targetAndTokenRight) := by
    have scanned := scanLeftExact
      (machineFor token) (rewindTargetState token)
      PackedSymbol
      (fun head left right ordinary =>
        rewindTarget_packed_step token left right head ordinary)
      (tokenFirstSymbol token :: target.reverse)
      afterBoundaryLeft
      (tokenSecondSymbol token ::
        WorkSymbol.blank :: outsideRight)
      rewindTargetPacked
    simpa [afterTargetLeft, pushLeft_eq_reverse_append,
      targetAndTokenRight, tokenSymbols, List.append_assoc] using scanned
  have hTargetBoundary :
      workRunExact? (machineFor token) 1
          (configAtLeftWord (rewindTargetState token)
            afterBoundaryLeft targetAndTokenRight) =
        some (configAtLeftWord (rewindSourceState token)
          afterSourceLeft
          (sourceTargetBoundary :: targetAndTokenRight)) := by
    apply workRunExact_one
    exact rewindTarget_boundary_step token afterSourceLeft
      targetAndTokenRight
  have rewindSourcePacked :
      ∀ symbol, symbol ∈ source.reverse → PackedSymbol symbol := by
    intro symbol found
    apply sourcePacked symbol
    simpa using found
  have hRewindSource :
      workRunExact? (machineFor token) source.length
          (configAtLeftWord (rewindSourceState token)
            afterSourceLeft
            (sourceTargetBoundary :: targetAndTokenRight)) =
        some (configAtLeftWord (rewindSourceState token)
          baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    have scanned := scanLeftExact
      (machineFor token) (rewindSourceState token)
      PackedSymbol
      (fun head left right ordinary =>
        rewindSource_packed_step token left right head ordinary)
      source.reverse baseLeft
      (sourceTargetBoundary :: targetAndTokenRight)
      rewindSourcePacked
    simpa [afterSourceLeft, pushLeft_eq_reverse_append,
      List.append_assoc] using scanned
  have hLeftBoundary :
      workRunExact? (machineFor token) 1
          (configAtLeftWord (rewindSourceState token)
            baseLeft
            (source ++
              (sourceTargetBoundary :: targetAndTokenRight))) =
        some (configAtWord acceptState baseLeft
          (source ++
            (sourceTargetBoundary :: targetAndTokenRight))) := by
    apply workRunExact_one
    exact rewindSource_boundary_step token controllerOutside
      (source ++
        (sourceTargetBoundary :: targetAndTokenRight))
  have h01 := workRunExact_compose (machineFor token)
    source.length 1 _ _ _ hSource hSourceBoundary
  have h02 := workRunExact_compose (machineFor token)
    (source.length + 1) target.length _ _ _ h01 hTarget
  have h03 := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length) 1 _ _ _ h02 hFirst
  have h04 := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length + 1) 1 _ _ _ h03 hSecond
  have h05 := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length + 1 + 1)
    (target.length + 1) _ _ _ h04 hRewindTarget
  have h06 := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1))
    1 _ _ _ h05 hTargetBoundary
  have h07 := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1) + 1)
    source.length _ _ _ h06 hRewindSource
  have complete := workRunExact_compose (machineFor token)
    (source.length + 1 + target.length + 1 + 1 +
      (target.length + 1) + 1 + source.length)
    1 _ _ _ h07 hLeftBoundary
  have stepCount :
      source.length + 1 + target.length + 1 + 1 +
          (target.length + 1) + 1 + source.length + 1 =
        packedAppendWorkSteps source target := by
    unfold packedAppendWorkSteps
    omega
  rw [stepCount] at complete
  simpa [appendPackedEntry, appendPackedFinal,
    baseLeft, targetAndTokenRight, tokenSymbols,
    List.append_assoc] using complete

/-! ### Source-driven entry and exact workspace endpoints -/

/-- The true all-input entry contract.  No decode result or target word occurs
in this configuration. -/
def rawEntryConfiguration (bits : BitString) : WorkConfiguration :=
  { state := frameSeekEndState
    tape := rawInputWorkTape bits }

/-- Canonical packed source restored byte-for-byte, focused at its first cell.
This is the endpoint a non-destructive strict-v0 grammar controller must
construct before invoking token append requests. -/
def restoredSourceTape (raw : RawCircuit) (registers : UnaryRegisters)
    (checks : List Nat) (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  match SourceParser.circuitCells raw with
  | [] =>
      { left := controllerLeftWorkspace registers checks outsideLeft
        head := WorkSymbol.blank
        right := sourceTargetBoundary ::
          WorkSymbol.blank :: WorkSymbol.blank ::
            WorkSymbol.blank :: outsideRight }
  | first :: rest =>
      { left := controllerLeftWorkspace registers checks outsideLeft
        head := first
        right := rest ++
          (sourceTargetBoundary ::
            WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight) }

def restoredSourceEntryConfiguration (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := seekSourceState .version0
    tape := restoredSourceTape raw registers checks outsideLeft outsideRight }

/-- Entry to one append request with an already emitted packed target prefix.
The prefix is source-driven controller output; it is not computed by this
configuration constructor. -/
def appendEntryTape (raw : RawCircuit) (registers : UnaryRegisters)
    (checks : List Nat) (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  match SourceParser.circuitCells raw with
  | [] =>
      { left := controllerLeftWorkspace registers checks outsideLeft
        head := WorkSymbol.blank
        right := sourceTargetBoundary ::
          (SourceParser.packedTokenCells targetPrefix ++
            (WorkSymbol.blank :: WorkSymbol.blank ::
              WorkSymbol.blank :: outsideRight)) }
  | first :: rest =>
      { left := controllerLeftWorkspace registers checks outsideLeft
        head := first
        right := rest ++
          (sourceTargetBoundary ::
            (SourceParser.packedTokenCells targetPrefix ++
              (WorkSymbol.blank :: WorkSymbol.blank ::
                WorkSymbol.blank :: outsideRight))) }

def appendEntryConfiguration (token : Token) (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := seekSourceState token
    tape := appendEntryTape raw registers checks targetPrefix
      outsideLeft outsideRight }

def appendFinalConfiguration (token : Token) (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  let source := SourceParser.circuitCells raw
  let target :=
    SourceParser.packedTokenCells targetPrefix ++ tokenSymbols token
  { state := acceptState
    tape :=
      match source with
      | [] =>
          { left := controllerLeftWorkspace registers checks outsideLeft
            head := sourceTargetBoundary
            right := target ++ (WorkSymbol.blank :: outsideRight) }
      | first :: rest =>
          { left := controllerLeftWorkspace registers checks outsideLeft
            head := first
            right := rest ++
              (sourceTargetBoundary ::
                (target ++ (WorkSymbol.blank :: outsideRight))) } }

def appendWorkSteps (raw : RawCircuit) (targetPrefix : List Token) : Nat :=
  2 * (SourceParser.circuitCells raw).length +
    2 * (SourceParser.packedTokenCells targetPrefix).length + 6

theorem appendWorkSteps_eq_packed (raw : RawCircuit)
    (targetPrefix : List Token) :
    appendWorkSteps raw targetPrefix =
      packedAppendWorkSteps (SourceParser.circuitCells raw)
        (SourceParser.packedTokenCells targetPrefix) := by
  rfl

theorem appendWorkSteps_evaluated (raw : RawCircuit)
    (targetPrefix : List Token) :
    appendWorkSteps raw targetPrefix =
      4 * (encodeCircuitTokens raw).length +
        4 * targetPrefix.length + 6 := by
  unfold appendWorkSteps
  rw [← SourceParser.packedTokenCells_encodeCircuitTokens raw,
    SourceParser.packedTokenCells_length,
    SourceParser.packedTokenCells_length]
  omega

theorem appendWorkSteps_linear_bound (raw : RawCircuit)
    (targetPrefix : List Token) :
    appendWorkSteps raw targetPrefix ≤
      4 * ((encodeCircuitTokens raw).length +
        targetPrefix.length + 2) := by
  rw [appendWorkSteps_evaluated]
  omega

/-- Exact token append for every canonical raw source, every one of the twelve
literal token requests, and arbitrary register/check/outside workspace. -/
theorem append_exact (token : Token) (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (targetPrefix : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    workRunExact? (machineFor token)
        (appendWorkSteps raw targetPrefix)
        (appendEntryConfiguration token raw registers checks
          targetPrefix outsideLeft outsideRight) =
      some (appendFinalConfiguration token raw registers checks
        targetPrefix outsideLeft outsideRight) := by
  let source := SourceParser.circuitCells raw
  let target := SourceParser.packedTokenCells targetPrefix
  let controllerOutside :=
    registerBank registers ++ checkStack checks ++ outsideLeft
  have exactPacked := appendPacked_exact token source target
    controllerOutside outsideRight
    (circuitCells_packed raw)
    (packedTokenCells_packed targetPrefix)
  have sourceNonempty : source ≠ [] := by
    exact SourceParser.circuitCells_ne_empty raw
  cases sourceEq : source with
  | nil =>
      exact (sourceNonempty sourceEq).elim
  | cons first rest =>
      simpa [appendWorkSteps_eq_packed, appendEntryConfiguration,
        appendEntryTape, appendFinalConfiguration,
        appendPackedEntry, appendPackedFinal,
        configAtWord,
        controllerLeftWorkspace, controllerOutside,
        source, target, sourceEq, tokenSymbols,
        List.append_assoc] using exactPacked

set_option maxRecDepth 200000 in
private theorem find_seekSource_blank (token : Token) :
    findWorkRule rules (seekSourceState token) WorkSymbol.blank =
      some (literalRule (seekSourceState token) WorkSymbol.blank
        deadState WorkSymbol.blank .stay) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_seekTarget_leftBoundary (token : Token) :
    findWorkRule rules (seekTargetState token) sourceLeftBoundary =
      some (literalRule (seekTargetState token) sourceLeftBoundary
        deadState sourceLeftBoundary .stay) := by
  cases token <;> decide

set_option maxRecDepth 200000 in
private theorem find_writeSecond_packed (token : Token)
    (symbol : WorkSymbol) (ordinary : PackedSymbol symbol) :
    findWorkRule rules (writeSecondState token) symbol =
      some (literalRule (writeSecondState token) symbol
        deadState symbol .stay) := by
  cases ordinary <;> cases token <;> decide

/-- A missing source/target boundary cannot be interpreted as a shorter valid
source: the token request enters the ruleless dead state immediately. -/
theorem missing_source_boundary_enters_dead (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (WorkSymbol.blank :: suffix)) =
      some (configAtWord deadState leftSide
        (WorkSymbol.blank :: suffix)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekSourceState token) leftSide
          (WorkSymbol.blank :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekSourceState token) leftSide
          (WorkSymbol.blank :: suffix)) =
      some (applyWorkRule
        (literalRule (seekSourceState token) WorkSymbol.blank
          deadState WorkSymbol.blank .stay)
        (configAtWord (seekSourceState token) leftSide
          (WorkSymbol.blank :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekSource_blank token)
    _ = some (configAtWord deadState leftSide
        (WorkSymbol.blank :: suffix)) := by
      rfl

/-- A left-boundary symbol appearing inside the target region is rejected as
malformed workspace rather than shadowing the target delimiter. -/
theorem target_boundary_collision_enters_dead (token : Token)
    (leftSide suffix : List WorkSymbol) :
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (sourceLeftBoundary :: suffix)) =
      some (configAtWord deadState leftSide
        (sourceLeftBoundary :: suffix)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (seekTargetState token) leftSide
          (sourceLeftBoundary :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (seekTargetState token) leftSide
          (sourceLeftBoundary :: suffix)) =
      some (applyWorkRule
        (literalRule (seekTargetState token) sourceLeftBoundary
          deadState sourceLeftBoundary .stay)
        (configAtWord (seekTargetState token) leftSide
          (sourceLeftBoundary :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_seekTarget_leftBoundary token)
    _ = some (configAtWord deadState leftSide
        (sourceLeftBoundary :: suffix)) := by
      rfl

/-- The second output cell must be blank.  Encountering retained packed data
there is a fail-closed workspace error. -/
theorem occupied_second_output_cell_enters_dead (token : Token)
    (leftSide suffix : List WorkSymbol) (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol) :
    workStep? (machineFor token)
        (configAtWord (writeSecondState token) leftSide
          (symbol :: suffix)) =
      some (configAtWord deadState leftSide (symbol :: suffix)) := by
  have hHalted :
      (machineFor token).isHalted
        (configAtWord (writeSecondState token) leftSide
          (symbol :: suffix)) = false := by
    cases token <;> rfl
  calc
    workStep? (machineFor token)
        (configAtWord (writeSecondState token) leftSide
          (symbol :: suffix)) =
      some (applyWorkRule
        (literalRule (writeSecondState token) symbol
          deadState symbol .stay)
        (configAtWord (writeSecondState token) leftSide
          (symbol :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ hHalted
        (find_writeSecond_packed token symbol ordinary)
    _ = some (configAtWord deadState leftSide
        (symbol :: suffix)) := by
      rfl

/-- Dead is deliberately non-halting but has no outgoing rule, so malformed
workspace cannot accidentally accept or reject through a state collision. -/
theorem dead_configuration_stuck (token : Token) (tape : WorkTape) :
    workStep? (machineFor token)
      { state := deadState, tape := tape } = none := by
  have hHalted :
      (machineFor token).isHalted
        { state := deadState, tape := tape } = false := by
    rfl
  unfold workStep?
  rw [show (machineFor token).isHalted
      { state := deadState, tape := tape } = false from hHalted]
  rw [show (machineFor token).rules = rules from rfl]
  rw [no_rule_at_dead]
  rfl

/-- Specification-only target endpoint.  It is intentionally separated from
the executable rule table: later correctness must prove that the grammar
controller issues exactly this token stream by structural source scans. -/
def targetTokens (raw : RawCircuit) : List Token :=
  encodeLockedInstanceTokens (RawBuilder.rawLockedInstance raw)

def finalTargetTape (raw : RawCircuit) (registers : UnaryRegisters)
    (checks : List Nat) (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  appendEntryTape raw registers checks (targetTokens raw)
    outsideLeft outsideRight

def finalTargetConfiguration (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := acceptState
    tape := finalTargetTape raw registers checks outsideLeft outsideRight }

theorem finalTargetConfiguration_halted (raw : RawCircuit)
    (registers : UnaryRegisters) (checks : List Nat)
    (outsideLeft outsideRight : List WorkSymbol) :
    machine.isHalted
      (finalTargetConfiguration raw registers checks
        outsideLeft outsideRight) = true := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitter
