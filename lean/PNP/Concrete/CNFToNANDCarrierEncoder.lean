/-
Copyright (c) 2026 PNP Labs.

A bounded physical carrier encoder for canonical packed CNF tokens.

Each two-bit CNF token becomes one syntactically inert NAND gate whose two
constant sources record the token bits.  The raw carrier circuit has no
inputs and has constant false as its output.  The executable layer below is
restricted to literal work-symbol tables, cursor-preserving token appenders,
and a finite program graph.  It never decodes a CNF formula and never
consults an externally supplied emission schedule.
-/

import PNP.Concrete.CNFWorkMachine
import PNP.Concrete.LockedNANDSourceParserValidTrace
import PNP.Concrete.LockedNANDTargetEmitterCursorControl
import PNP.Concrete.LockedNANDTargetEmitterCursorAppender
import PNP.Concrete.LockedNANDTargetEmitterCursorFinalizer
import PNP.Concrete.WorkMachineProgramPath
import PNP.Concrete.WorkMachineBlankEquivalence

namespace PNP.Concrete.CNFToNANDCarrierEncoder

open PNP.Concrete
open PNP.Concrete.LockedNAND
open PNP.Concrete.WorkMachineProgramGraph

namespace Source

def firstBit (token : CNFToken) : Bool :=
  token.bits.head!

def secondBit (token : CNFToken) : Bool :=
  token.bits.tail.head!

def asConstant (value : Bool) : RawSource :=
  .constant value

/-- One inert gate records the two bits of one canonical CNF token. -/
def tokenGate (token : CNFToken) : RawGate :=
  { left := asConstant (firstBit token)
    right := asConstant (secondBit token) }

/-- The bounded raw carrier.  It deliberately asserts no Boolean relation
about the CNF formula; the source bytes are retained only as constant tags. -/
def carrierCircuit (tokens : List CNFToken) : RawCircuit :=
  { inputCount := 0
    gates := tokens.map tokenGate
    output := .constant false }

theorem carrierCircuit_inputCount (tokens : List CNFToken) :
    (carrierCircuit tokens).inputCount = 0 := by
  rfl

theorem carrierCircuit_gates_length (tokens : List CNFToken) :
    (carrierCircuit tokens).gates.length = tokens.length := by
  simp [carrierCircuit]

theorem carrierCircuit_output (tokens : List CNFToken) :
    (carrierCircuit tokens).output = .constant false := by
  rfl

def recoverTokenGate (gate : RawGate) : Option CNFToken :=
  match gate.left, gate.right with
  | .constant left, .constant right =>
      some (CNFToken.ofBits left right)
  | _, _ => none

theorem recoverTokenGate_tokenGate (token : CNFToken) :
    recoverTokenGate (tokenGate token) = some token := by
  cases token <;> rfl

theorem recover_carrier_gates (tokens : List CNFToken) :
    (carrierCircuit tokens).gates.map recoverTokenGate =
      tokens.map some := by
  simp [carrierCircuit, recoverTokenGate_tokenGate]

private theorem list_map_injective {α β : Type}
    (function : α → β) (injective : Function.Injective function) :
    Function.Injective (List.map function) := by
  intro left right equality
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head rest => contradiction
  | cons head rest inductionHypothesis =>
      cases right with
      | nil => contradiction
      | cons rightHead rightRest =>
          simp only [List.map_cons, List.cons.injEq] at equality
          rw [injective equality.1,
            inductionHypothesis equality.2]

theorem carrierCircuit_injective :
    Function.Injective carrierCircuit := by
  intro left right equality
  have gatesEquality :
      (carrierCircuit left).gates =
        (carrierCircuit right).gates :=
    congrArg RawCircuit.gates equality
  apply list_map_injective tokenGate
  · intro first second gateEquality
    have recovered :=
      congrArg recoverTokenGate gateEquality
    simpa [recoverTokenGate_tokenGate] using recovered
  · simpa [carrierCircuit] using gatesEquality

def constantToken (value : Bool) : Token :=
  if value then .constantTrue else .constantFalse

def tokenGateTokens (token : CNFToken) : List Token :=
  [constantToken (firstBit token),
    constantToken (secondBit token),
    .gateEnd]

theorem encodeGateTokens_tokenGate (token : CNFToken) :
    encodeGateTokens (tokenGate token) =
      tokenGateTokens token := by
  cases token <;> rfl

def gateTokenStream : List CNFToken → List Token
  | [] => []
  | token :: rest =>
      tokenGateTokens token ++ gateTokenStream rest

theorem gateTokenStream_eq_encodeGateListTokens
    (tokens : List CNFToken) :
    gateTokenStream tokens =
      encodeGateListTokens (tokens.map tokenGate) := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      simp [gateTokenStream, encodeGateListTokens,
        encodeGateTokens_tokenGate, ih]

theorem gateTokenStream_length (tokens : List CNFToken) :
    (gateTokenStream tokens).length = 3 * tokens.length := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      simp [gateTokenStream, tokenGateTokens, ih]
      omega

private theorem replicate_unit_natEnd
    (count : Nat) :
    List.replicate count Token.unit ++ [.natEnd] =
      encodeNatTokens count := by
  induction count with
  | zero => rfl
  | succ count ih =>
      change
        Token.unit ::
            (List.replicate count Token.unit ++ [.natEnd]) =
          Token.unit :: encodeNatTokens count
      rw [ih]

def carrierTokens (tokens : List CNFToken) : List Token :=
  [.version0, .natEnd] ++
    List.replicate tokens.length .unit ++
    [.natEnd] ++ gateTokenStream tokens ++
    [.programEnd, .constantFalse,
      .outputsEnd, .instanceEnd]

theorem carrierTokens_eq_encodeCircuitTokens
    (tokens : List CNFToken) :
    carrierTokens tokens =
      encodeCircuitTokens (carrierCircuit tokens) := by
  unfold carrierTokens carrierCircuit encodeCircuitTokens
  rw [gateTokenStream_eq_encodeGateListTokens]
  simp only [List.length_map]
  change
    [.version0, .natEnd] ++
        List.replicate tokens.length .unit ++
        [.natEnd] ++
        encodeGateListTokens (tokens.map tokenGate) ++
        [.programEnd, .constantFalse,
          .outputsEnd, .instanceEnd] =
      .version0 ::
        (encodeNatTokens 0 ++
          encodeNatTokens tokens.length ++
          encodeGateListTokens (tokens.map tokenGate) ++
          [.programEnd] ++
          encodeSourceTokens (.constant false) ++
          [.outputsEnd, .instanceEnd])
  rw [show encodeNatTokens 0 = [.natEnd] by rfl,
    ← replicate_unit_natEnd tokens.length]
  simp [encodeSourceTokens, List.append_assoc]

theorem encodeCarrier_exact (tokens : List CNFToken) :
    encodeCircuit (carrierCircuit tokens) =
      encodeTokens (carrierTokens tokens) := by
  rw [carrierTokens_eq_encodeCircuitTokens]
  rfl

theorem carrierTokens_length (tokens : List CNFToken) :
    (carrierTokens tokens).length = 4 * tokens.length + 7 := by
  simp [carrierTokens, gateTokenStream_length]
  omega

theorem carrierCircuit_cells
    (tokens : List CNFToken) :
    LockedNAND.SourceParser.circuitCells (carrierCircuit tokens) =
      LockedNAND.SourceParser.packedTokenCells
        (carrierTokens tokens) := by
  rw [carrierTokens_eq_encodeCircuitTokens]
  exact
    (LockedNAND.SourceParser.packedTokenCells_encodeCircuitTokens
        (carrierCircuit tokens)).symm

theorem carrierCircuit_cells_length
    (tokens : List CNFToken) :
    (LockedNAND.SourceParser.circuitCells
      (carrierCircuit tokens)).length =
        8 * tokens.length + 14 := by
  rw [carrierCircuit_cells,
    LockedNAND.SourceParser.packedTokenCells_length,
    carrierTokens_length]
  omega

theorem rawInputWorkTape_encodeCarrier
    (tokens : List CNFToken) :
    rawInputWorkTape
        (encodeCircuit (carrierCircuit tokens)) =
      WorkTape.ofSymbols
        (LockedNAND.SourceParser.circuitCells
          (carrierCircuit tokens)) :=
  LockedNAND.SourceParser.rawInputWorkTape_encodeCircuit
    (carrierCircuit tokens)

end Source

/-! ## Literal source preparation

The canonical CNF word ends in the single packed `zeroBlank` formula pad.
Target appenders require their contextual source/target boundary immediately
after the packed source.  This fixed table checks a nonempty packed word,
checks the pad and old boundary, erases the old boundary, turns the pad into
the new boundary, and returns to the first source cell.
-/

namespace Prepare

def cellBlank : WorkSymbol := WorkSymbol.blank
def sourceLeftBoundary : WorkSymbol :=
  LockedNAND.TargetEmitter.sourceLeftBoundary
def sourceTargetBoundary : WorkSymbol :=
  LockedNAND.TargetEmitter.sourceTargetBoundary
def formulaPad : WorkSymbol := WorkSymbol.zeroBlank

namespace State

def accept : Nat := 0
def reject : Nat := 1
def first : Nat := 2
def scan : Nat := 3
def oldBoundary : Nat := 4
def installBoundary : Nat := 5
def rewind : Nat := 6

end State

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

def keep (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def write (target : Nat) (symbol : WorkSymbol)
    (move : HeadMove) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def reject (symbol : WorkSymbol) : Action :=
  keep State.reject .stay symbol

def packed (symbol : WorkSymbol) : Bool :=
  symbol == WorkSymbol.zeroZero ||
    symbol == WorkSymbol.zeroOne ||
    symbol == WorkSymbol.oneZero ||
    symbol == WorkSymbol.oneOne

def firstAction (symbol : WorkSymbol) : Action :=
  if packed symbol then keep State.scan .right symbol
  else reject symbol

def scanAction (symbol : WorkSymbol) : Action :=
  if packed symbol then keep State.scan .right symbol
  else if symbol == formulaPad then
    keep State.oldBoundary .right symbol
  else reject symbol

def oldBoundaryAction (symbol : WorkSymbol) : Action :=
  if symbol == sourceTargetBoundary then
    write State.installBoundary cellBlank .left
  else reject symbol

def installBoundaryAction (symbol : WorkSymbol) : Action :=
  if symbol == formulaPad then
    write State.rewind sourceTargetBoundary .left
  else reject symbol

def rewindAction (symbol : WorkSymbol) : Action :=
  if packed symbol then keep State.rewind .left symbol
  else if symbol == sourceLeftBoundary then
    keep State.accept .right symbol
  else reject symbol

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def statePrograms : List StateProgram :=
  [ { state := State.first, action := firstAction }
  , { state := State.scan, action := scanAction }
  , { state := State.oldBoundary, action := oldBoundaryAction }
  , { state := State.installBoundary,
      action := installBoundaryAction }
  , { state := State.rewind, action := rewindAction }
  ]

def rulesAt (program : StateProgram) : List WorkRule :=
  LockedNAND.TargetEmitter.allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machine : WorkMachine :=
  { rules := rules
    startState := State.first
    acceptState := State.accept
    rejectState := State.reject }

def compiledMachine : Machine :=
  compileWorkMachine machine

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length : rules.length = 45 := by
  rfl

set_option maxRecDepth 100000 in
theorem rules_pairwise : rules.Pairwise QueryDistinct := by
  unfold rules statePrograms rulesAt QueryDistinct
  simp [LockedNAND.TargetEmitter.allWorkSymbols,
    State.first, State.scan, State.oldBoundary,
    State.installBoundary, State.rewind,
    WorkSymbol.blank, WorkSymbol.blankZero,
    WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero,
    WorkSymbol.oneOne]

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
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

def entryTape (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  LockedNAND.TargetEmitter.configAtWord State.first
    (sourceLeftBoundary :: outsideLeft)
    (cnfTokenWorkSymbols tokens ++
      formulaPad :: sourceTargetBoundary ::
        cellBlank :: outsideRight) |>.tape

def finalTape (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  LockedNAND.TargetEmitter.configAtWord State.accept
    (sourceLeftBoundary :: outsideLeft)
    (cnfTokenWorkSymbols tokens ++
      sourceTargetBoundary :: cellBlank ::
        cellBlank :: outsideRight) |>.tape

def entryConfiguration (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.first
    tape := entryTape tokens outsideLeft outsideRight }

def finalConfiguration (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.accept
    tape := finalTape tokens outsideLeft outsideRight }

def workSteps (tokens : List CNFToken) : Nat :=
  2 * tokens.length + 4

theorem empty_rejects
    (outsideLeft outsideRight : List WorkSymbol) :
    workRunExact? machine 1
        (entryConfiguration [] outsideLeft outsideRight) =
      some
        { state := State.reject
          tape := entryTape [] outsideLeft outsideRight } := by
  rfl

private theorem exactRun_add
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final
      firstRun secondRun

private theorem first_token_step
    (token : CNFToken)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.first left (token.workSymbol :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan (token.workSymbol :: left) suffix) := by
  cases token <;> cases suffix <;> rfl

private theorem scan_token_step
    (token : CNFToken)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left (token.workSymbol :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan (token.workSymbol :: left) suffix) := by
  cases token <;> cases suffix <;> rfl

private theorem scan_tokens_exact
    (tokens : List CNFToken)
    (left suffix : List WorkSymbol) :
    workRunExact? machine tokens.length
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left
          (cnfTokenWorkSymbols tokens ++ suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan
          ((cnfTokenWorkSymbols tokens).reverse ++ left)
          suffix) := by
  induction tokens generalizing left with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      have first :=
        scan_token_step token left
          (cnfTokenWorkSymbols rest ++ suffix)
      have tail :=
        inductionHypothesis (token.workSymbol :: left)
      have combined :=
        exactRun_add 1 rest.length
          (LockedNAND.TargetEmitter.configAtWord
            State.scan left
            (token.workSymbol ::
              cnfTokenWorkSymbols rest ++ suffix))
          (LockedNAND.TargetEmitter.configAtWord
            State.scan (token.workSymbol :: left)
            (cnfTokenWorkSymbols rest ++ suffix))
          (LockedNAND.TargetEmitter.configAtWord
            State.scan
            ((cnfTokenWorkSymbols rest).reverse ++
              token.workSymbol :: left)
            suffix)
          first tail
      simpa [cnfTokenWorkSymbols, List.reverse_cons,
        List.append_assoc, Nat.add_comm] using combined

private theorem boundary_install_exact
    (left outsideRight : List WorkSymbol) :
    workRunExact? machine 3
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left
          (formulaPad :: sourceTargetBoundary ::
            cellBlank :: outsideRight)) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left
          (sourceTargetBoundary :: cellBlank ::
            cellBlank :: outsideRight)) := by
  cases left <;> rfl

private theorem rewind_symbol_step
    (symbol : WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol symbol)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind (symbol :: left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left (symbol :: suffix)) := by
  cases ordinary <;> cases left <;> rfl

private theorem rewind_nearest_exact
    (nearest left suffix : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ nearest →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine nearest.length
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind (nearest ++ left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left (nearest.reverse ++ suffix)) := by
  induction nearest generalizing suffix with
  | nil =>
      rfl
  | cons symbol rest inductionHypothesis =>
      have headOrdinary :
          LockedNAND.TargetEmitter.PackedSymbol symbol :=
        ordinary symbol (List.Mem.head rest)
      have restOrdinary :
          ∀ item, item ∈ rest →
            LockedNAND.TargetEmitter.PackedSymbol item := by
        intro item member
        exact ordinary item (List.Mem.tail symbol member)
      have first :=
        rewind_symbol_step symbol headOrdinary
          (rest ++ left) suffix
      have tail :=
        inductionHypothesis (symbol :: suffix) restOrdinary
      have combined :=
        exactRun_add 1 rest.length
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind (symbol :: rest ++ left) suffix)
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind (rest ++ left) (symbol :: suffix))
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind left
            (rest.reverse ++ symbol :: suffix))
          first tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem token_symbols_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ cnfTokenWorkSymbols tokens →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  induction tokens with
  | nil =>
      contradiction
  | cons token rest inductionHypothesis =>
      simp only [cnfTokenWorkSymbols, List.mem_cons] at member
      rcases member with equality | restMember
      · subst symbol
        cases token <;> constructor
      · exact inductionHypothesis restMember

private theorem token_symbols_reverse_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ (cnfTokenWorkSymbols tokens).reverse →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  exact token_symbols_packed tokens symbol
    (List.mem_reverse.mp member)

private theorem rewind_boundary_step
    (right outsideLeft : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind
          (sourceLeftBoundary :: outsideLeft) right) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept
          (sourceLeftBoundary :: outsideLeft) right) := by
  cases right <;> rfl

/-- Exact nonempty preparation: validate the packed word and formula pad,
relocate the source/target boundary, erase the old boundary, and refocus the
first retained token. -/
theorem canonical_exact
    (first : CNFToken) (rest : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    workRunExact? machine (workSteps (first :: rest))
        (entryConfiguration (first :: rest)
          outsideLeft outsideRight) =
      some
        (finalConfiguration (first :: rest)
          outsideLeft outsideRight) := by
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  let leftBoundary := sourceLeftBoundary :: outsideLeft
  let preparedRight :=
    sourceTargetBoundary :: cellBlank ::
      cellBlank :: outsideRight
  let afterFirst :=
    LockedNAND.TargetEmitter.configAtWord
      State.scan (first.workSymbol :: leftBoundary)
      (cnfTokenWorkSymbols rest ++
        formulaPad :: sourceTargetBoundary ::
          cellBlank :: outsideRight)
  let afterScan :=
    LockedNAND.TargetEmitter.configAtWord
      State.scan (source.reverse ++ leftBoundary)
      (formulaPad :: sourceTargetBoundary ::
        cellBlank :: outsideRight)
  let afterInstall :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.rewind (source.reverse ++ leftBoundary)
      preparedRight
  let atBoundary :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.rewind leftBoundary (source ++ preparedRight)
  have hFirst :
      workRunExact? machine 1
          (entryConfiguration tokens outsideLeft outsideRight) =
        some afterFirst := by
    simpa [tokens, source, leftBoundary, afterFirst,
      entryConfiguration, entryTape, cnfTokenWorkSymbols,
      LockedNAND.TargetEmitter.configAtWord,
      List.append_assoc] using
      first_token_step first leftBoundary
        (cnfTokenWorkSymbols rest ++
          formulaPad :: sourceTargetBoundary ::
            cellBlank :: outsideRight)
  have hScan :
      workRunExact? machine rest.length afterFirst =
        some afterScan := by
    simpa [tokens, source, leftBoundary, afterFirst,
      afterScan, cnfTokenWorkSymbols, List.reverse_cons,
      List.append_assoc] using
      scan_tokens_exact rest
        (first.workSymbol :: leftBoundary)
        (formulaPad :: sourceTargetBoundary ::
          cellBlank :: outsideRight)
  have hInstall :
      workRunExact? machine 3 afterScan =
        some afterInstall := by
    simpa [afterScan, afterInstall, preparedRight] using
      boundary_install_exact
        (source.reverse ++ leftBoundary) outsideRight
  have hRewind :
      workRunExact? machine source.length afterInstall =
        some atBoundary := by
    simpa [afterInstall, atBoundary, preparedRight,
      List.reverse_reverse] using
      rewind_nearest_exact source.reverse leftBoundary
        preparedRight
        (token_symbols_reverse_packed tokens)
  have hBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (finalConfiguration tokens outsideLeft outsideRight) := by
    simpa [atBoundary, finalConfiguration, finalTape,
      tokens, source, preparedRight, leftBoundary,
      cnfTokenWorkSymbols,
      LockedNAND.TargetEmitter.configAtWord,
      List.append_assoc] using
      rewind_boundary_step
        (source ++ preparedRight) outsideLeft
  have firstScan :=
    exactRun_add 1 rest.length _ afterFirst afterScan
      hFirst hScan
  have throughInstall :=
    exactRun_add (1 + rest.length) 3
      _ afterScan afterInstall firstScan hInstall
  have throughRewind :=
    exactRun_add (1 + rest.length + 3) source.length
      _ afterInstall atBoundary throughInstall hRewind
  have all :=
    exactRun_add
      (1 + rest.length + 3 + source.length) 1
      _ atBoundary _ throughRewind hBoundary
  have stepsEq :
      (1 + rest.length + 3 + source.length) + 1 =
        workSteps tokens := by
    simp [workSteps, tokens, source,
      cnfTokenWorkSymbols_length]
    omega
  rw [← stepsEq]
  exact all

end Prepare

/-! ## Fixed branch and rewind controls -/

namespace Match

def startState : Nat := 0
def acceptState : Nat := 1
def rejectState : Nat := 2

def ruleFor (expected read : WorkSymbol) : WorkRule :=
  { sourceState := startState
    readSymbol := read
    targetState :=
      if read == expected then acceptState else rejectState
    writeSymbol := read
    move := .stay }

def rules (expected : WorkSymbol) : List WorkRule :=
  LockedNAND.TargetEmitter.allWorkSymbols.map
    (ruleFor expected)

def machine (expected : WorkSymbol) : WorkMachine :=
  { rules := rules expected
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length (expected : WorkSymbol) :
    (rules expected).length = 9 := by
  rfl

theorem rules_pairwise (expected : WorkSymbol) :
    (rules expected).Pairwise QueryDistinct := by
  rcases expected with ⟨expectedFirst, expectedSecond⟩
  cases expectedFirst <;> cases expectedSecond <;>
    simp [rules, ruleFor, QueryDistinct,
      LockedNAND.TargetEmitter.allWorkSymbols,
      WorkSymbol.blank, WorkSymbol.blankZero,
      WorkSymbol.blankOne, WorkSymbol.zeroBlank,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneBlank, WorkSymbol.oneZero,
      WorkSymbol.oneOne]

theorem no_rule_at_accept (expected symbol : WorkSymbol) :
    findWorkRule (rules expected) acceptState symbol = none := by
  rcases expected with ⟨expectedFirst, expectedSecond⟩
  rcases symbol with ⟨first, second⟩
  cases expectedFirst <;> cases expectedSecond <;>
    cases first <;> cases second <;> decide

theorem no_rule_at_reject (expected symbol : WorkSymbol) :
    findWorkRule (rules expected) rejectState symbol = none := by
  rcases expected with ⟨expectedFirst, expectedSecond⟩
  rcases symbol with ⟨first, second⟩
  cases expectedFirst <;> cases expectedSecond <;>
    cases first <;> cases second <;> decide

theorem accept_ne_reject (expected : WorkSymbol) :
    (machine expected).acceptState ≠
      (machine expected).rejectState := by
  simp [machine, acceptState, rejectState]

theorem accepts_exact (expected : WorkSymbol)
    (tape : WorkTape) (head : tape.head = expected) :
    workRunExact? (machine expected) 1
        { state := startState, tape := tape } =
      some { state := acceptState, tape := tape } := by
  rcases expected with ⟨expectedFirst, expectedSecond⟩
  cases tape with
  | mk left tapeHead right =>
      simp only at head
      subst tapeHead
      cases expectedFirst <;> cases expectedSecond <;> rfl

theorem rejects_exact (expected actual : WorkSymbol)
    (tape : WorkTape) (head : tape.head = actual)
    (different : actual ≠ expected) :
    workRunExact? (machine expected) 1
        { state := startState, tape := tape } =
      some { state := rejectState, tape := tape } := by
  cases tape with
  | mk left tapeHead right =>
      simp only at head
      subst tapeHead
      rcases expected with
        ⟨expectedFirst, expectedSecond⟩
      rcases actual with ⟨actualFirst, actualSecond⟩
      cases expectedFirst <;> cases expectedSecond <;>
        cases actualFirst <;> cases actualSecond <;>
        first | rfl | exact (different rfl).elim

end Match

namespace Rewind

def sourceLeftBoundary : WorkSymbol :=
  LockedNAND.TargetEmitter.sourceLeftBoundary
def sourceTargetBoundary : WorkSymbol :=
  LockedNAND.TargetEmitter.sourceTargetBoundary

namespace State

def accept : Nat := 0
def reject : Nat := 1
def leaveBoundary : Nat := 2
def scanLeft : Nat := 3

end State

def targetMove (state : Nat) (symbol : WorkSymbol) :
    Nat × HeadMove :=
  if state == State.leaveBoundary then
    if symbol == sourceTargetBoundary then
      (State.scanLeft, .left)
    else (State.reject, .stay)
  else
    if symbol == WorkSymbol.zeroZero ||
        symbol == WorkSymbol.zeroOne ||
        symbol == WorkSymbol.oneZero ||
        symbol == WorkSymbol.oneOne then
      (State.scanLeft, .left)
    else if symbol == sourceLeftBoundary then
      (State.accept, .right)
    else (State.reject, .stay)

def actionRule (state : Nat) (symbol : WorkSymbol) : WorkRule :=
  { sourceState := state
    readSymbol := symbol
    targetState := (targetMove state symbol).1
    writeSymbol := symbol
    move := (targetMove state symbol).2 }

def rules : List WorkRule :=
  [State.leaveBoundary, State.scanLeft].flatMap fun state =>
    LockedNAND.TargetEmitter.allWorkSymbols.map
      (actionRule state)

def machine : WorkMachine :=
  { rules := rules
    startState := State.leaveBoundary
    acceptState := State.accept
    rejectState := State.reject }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length : rules.length = 18 := by
  rfl

set_option maxRecDepth 100000 in
theorem rules_pairwise : rules.Pairwise QueryDistinct := by
  unfold rules QueryDistinct
  simp [LockedNAND.TargetEmitter.allWorkSymbols,
    actionRule,
    State.leaveBoundary, State.scanLeft,
    WorkSymbol.blank, WorkSymbol.blankZero,
    WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero,
    WorkSymbol.oneOne]

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

private theorem exactRun_add
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final
      firstRun secondRun

private theorem leave_boundary_step
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.leaveBoundary left
          (sourceTargetBoundary :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft left
          (sourceTargetBoundary :: suffix)) := by
  cases left <;> rfl

private theorem scan_symbol_step
    (symbol : WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol symbol)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft (symbol :: left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft left (symbol :: suffix)) := by
  cases ordinary <;> cases left <;> rfl

private theorem scan_nearest_exact
    (nearest left suffix : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ nearest →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine nearest.length
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft (nearest ++ left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft left (nearest.reverse ++ suffix)) := by
  induction nearest generalizing suffix with
  | nil =>
      rfl
  | cons symbol rest inductionHypothesis =>
      have headOrdinary :=
        ordinary symbol (List.Mem.head rest)
      have restOrdinary :
          ∀ item, item ∈ rest →
            LockedNAND.TargetEmitter.PackedSymbol item := by
        intro item member
        exact ordinary item (List.Mem.tail symbol member)
      have first :=
        scan_symbol_step symbol headOrdinary
          (rest ++ left) suffix
      have tail :=
        inductionHypothesis (symbol :: suffix) restOrdinary
      have combined :=
        exactRun_add 1 rest.length
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.scanLeft (symbol :: rest ++ left) suffix)
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.scanLeft (rest ++ left) (symbol :: suffix))
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.scanLeft left
            (rest.reverse ++ symbol :: suffix))
          first tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem token_symbols_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ cnfTokenWorkSymbols tokens →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  induction tokens with
  | nil =>
      contradiction
  | cons token rest inductionHypothesis =>
      simp only [cnfTokenWorkSymbols, List.mem_cons] at member
      rcases member with equality | restMember
      · subst symbol
        cases token <;> constructor
      · exact inductionHypothesis restMember

private theorem token_symbols_reverse_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ (cnfTokenWorkSymbols tokens).reverse →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  exact token_symbols_packed tokens symbol
    (List.mem_reverse.mp member)

private theorem source_boundary_step
    (right outsideLeft : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.scanLeft
          (sourceLeftBoundary :: outsideLeft) right) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept
          (sourceLeftBoundary :: outsideLeft) right) := by
  cases right <;> rfl

def workSteps (tokens : List CNFToken) : Nat :=
  tokens.length + 2

/-- Starting on the source/target boundary, rewind a nonempty retained
canonical token word and refocus its first cell. -/
theorem canonical_exact
    (first : CNFToken) (rest : List CNFToken)
    (outsideLeft suffix : List WorkSymbol) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    workRunExact? machine (workSteps tokens)
        (LockedNAND.TargetEmitter.configAtWord
          State.leaveBoundary
          (source.reverse ++
            sourceLeftBoundary :: outsideLeft)
          (sourceTargetBoundary :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept
          (sourceLeftBoundary :: outsideLeft)
          (source ++ sourceTargetBoundary :: suffix)) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  let afterLeave :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.scanLeft
      (source.reverse ++ sourceLeftBoundary :: outsideLeft)
      (sourceTargetBoundary :: suffix)
  let atBoundary :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.scanLeft
      (sourceLeftBoundary :: outsideLeft)
      (source ++ sourceTargetBoundary :: suffix)
  have hLeave :
      workRunExact? machine 1
          (LockedNAND.TargetEmitter.configAtWord
            State.leaveBoundary
            (source.reverse ++
              sourceLeftBoundary :: outsideLeft)
            (sourceTargetBoundary :: suffix)) =
        some afterLeave := by
    simpa [afterLeave] using
      leave_boundary_step
        (source.reverse ++ sourceLeftBoundary :: outsideLeft)
        suffix
  have hScan :
      workRunExact? machine source.length afterLeave =
        some atBoundary := by
    simpa [afterLeave, atBoundary,
      List.reverse_reverse, List.append_assoc] using
      scan_nearest_exact source.reverse
        (sourceLeftBoundary :: outsideLeft)
        (sourceTargetBoundary :: suffix)
        (token_symbols_reverse_packed tokens)
  have hBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (LockedNAND.TargetEmitter.configAtWord
            State.accept
            (sourceLeftBoundary :: outsideLeft)
            (source ++ sourceTargetBoundary :: suffix)) := by
    simpa [atBoundary] using
      source_boundary_step
        (source ++ sourceTargetBoundary :: suffix)
        outsideLeft
  have firstTwo :=
    exactRun_add 1 source.length
      _ afterLeave atBoundary hLeave hScan
  have all :=
    exactRun_add (1 + source.length) 1
      _ atBoundary _ firstTwo hBoundary
  have stepsEq :
      (1 + source.length) + 1 = workSteps tokens := by
    simp [workSteps, source, cnfTokenWorkSymbols_length]
    omega
  rw [← stepsEq]
  exact all

end Rewind

/-! ## Terminal source-boundary cleanup

The reused cursor finalizer erases the retained source and its target
boundary, but intentionally leaves the source-left boundary in the left
workspace.  The downstream source parser requires a genuinely blank
extension.  This literal bridge preserves the first target cell, walks left
over exactly those erased cells, erases the old source-left boundary, and
returns to the first packed target cell.
-/

namespace BoundaryCleanup

def cellBlank : WorkSymbol := WorkSymbol.blank
def sourceLeftBoundary : WorkSymbol :=
  LockedNAND.TargetEmitter.sourceLeftBoundary

namespace State

def accept : Nat := 0
def reject : Nat := 1
def leaveTarget : Nat := 2
def seekBoundary : Nat := 3
def returnTarget : Nat := 4

end State

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

def packed (symbol : WorkSymbol) : Bool :=
  symbol == WorkSymbol.zeroZero ||
    symbol == WorkSymbol.zeroOne ||
    symbol == WorkSymbol.oneZero ||
    symbol == WorkSymbol.oneOne

def keep (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def reject (symbol : WorkSymbol) : Action :=
  keep State.reject .stay symbol

def leaveTargetAction (symbol : WorkSymbol) : Action :=
  if packed symbol then
    keep State.seekBoundary .left symbol
  else reject symbol

def seekBoundaryAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keep State.seekBoundary .left symbol
  else if symbol == sourceLeftBoundary then
    { targetState := State.returnTarget
      writeSymbol := cellBlank
      move := .right }
  else reject symbol

def returnTargetAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keep State.returnTarget .right symbol
  else if packed symbol then
    keep State.accept .stay symbol
  else reject symbol

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def statePrograms : List StateProgram :=
  [ { state := State.leaveTarget,
      action := leaveTargetAction }
  , { state := State.seekBoundary,
      action := seekBoundaryAction }
  , { state := State.returnTarget,
      action := returnTargetAction }
  ]

def rulesAt (program : StateProgram) : List WorkRule :=
  LockedNAND.TargetEmitter.allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machine : WorkMachine :=
  { rules := rules
    startState := State.leaveTarget
    acceptState := State.accept
    rejectState := State.reject }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length : rules.length = 27 := by
  rfl

set_option maxRecDepth 100000 in
theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  unfold rules statePrograms rulesAt QueryDistinct
  simp [LockedNAND.TargetEmitter.allWorkSymbols,
    State.leaveTarget, State.seekBoundary,
    State.returnTarget, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

def finalTape (source target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  TargetEmitterCursorFinalizer.tapeAtWord
    (List.replicate (source.length + 2) cellBlank ++
      outsideLeft)
    (target ++ cellBlank :: outsideRight)

def finalConfiguration (source target : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := State.accept
    tape := finalTape source target outsideLeft outsideRight }

def workSteps (source : List WorkSymbol) : Nat :=
  2 * source.length + 5

private theorem exactRun_add
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final
      firstRun secondRun

private theorem leave_target_step
    (target : WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol target)
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (TargetEmitterCursorFinalizer.configurationAtWord
          State.leaveTarget left (target :: right)) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary left (target :: right)) := by
  cases ordinary <;> cases left <;> rfl

private theorem seek_blank_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary (cellBlank :: left) right) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary left (cellBlank :: right)) := by
  cases left <;> rfl

private theorem blank_cons_replicate
    (count : Nat) :
    cellBlank :: List.replicate count cellBlank =
      List.replicate count cellBlank ++ [cellBlank] := by
  induction count with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      change
        cellBlank :: cellBlank ::
            List.replicate count cellBlank =
          cellBlank ::
            (List.replicate count cellBlank ++ [cellBlank])
      rw [inductionHypothesis]

private theorem replicate_append_one
    (count : Nat) :
    List.replicate count cellBlank ++ [cellBlank] =
      List.replicate (count + 1) cellBlank := by
  rw [List.replicate_succ, blank_cons_replicate]

private theorem seek_blanks_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary
          (List.replicate count cellBlank ++ left) right) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary left
          (List.replicate count cellBlank ++ right)) := by
  induction count generalizing right with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have first :=
        seek_blank_step
          (List.replicate count cellBlank ++ left) right
      have tail :=
        inductionHypothesis (cellBlank :: right)
      have combined :=
        exactRun_add 1 count
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.seekBoundary
            (cellBlank ::
              List.replicate count cellBlank ++ left) right)
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.seekBoundary
            (List.replicate count cellBlank ++ left)
            (cellBlank :: right))
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.seekBoundary left
            (List.replicate count cellBlank ++
              cellBlank :: right))
          first tail
      simpa [Nat.add_comm, List.replicate_succ,
        blank_cons_replicate, List.append_assoc] using combined

private theorem erase_boundary_step
    (count : Nat) (outsideLeft right : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.seekBoundary
          (sourceLeftBoundary :: outsideLeft)
          (List.replicate (count + 1) cellBlank ++ right)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget (cellBlank :: outsideLeft)
          (List.replicate (count + 1) cellBlank ++ right)) := by
  rfl

private theorem return_blank_step
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget left (cellBlank :: right)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget (cellBlank :: left) right) := by
  cases right <;> rfl

private theorem return_blanks_exact
    (count : Nat) (left right : List WorkSymbol) :
    workRunExact? machine count
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget left
          (List.replicate count cellBlank ++ right)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget
          (List.replicate count cellBlank ++ left) right) := by
  induction count generalizing left with
  | zero =>
      rfl
  | succ count inductionHypothesis =>
      have first :=
        return_blank_step left
          (List.replicate count cellBlank ++ right)
      have tail :=
        inductionHypothesis (cellBlank :: left)
      have combined :=
        exactRun_add 1 count
          (LockedNAND.TargetEmitter.configAtWord
            State.returnTarget left
            (cellBlank ::
              List.replicate count cellBlank ++ right))
          (LockedNAND.TargetEmitter.configAtWord
            State.returnTarget (cellBlank :: left)
            (List.replicate count cellBlank ++ right))
          (LockedNAND.TargetEmitter.configAtWord
            State.returnTarget
            (List.replicate count cellBlank ++
              cellBlank :: left)
            right)
          first tail
      simpa [Nat.add_comm, List.replicate_succ,
        blank_cons_replicate, List.append_assoc] using combined

private theorem accept_target_step
    (target : WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol target)
    (left right : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.returnTarget left (target :: right)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept left (target :: right)) := by
  cases ordinary <;> rfl

/-- Erase the old source-left boundary and return to the first target cell.
The entire finite left extension produced by the carrier is now blank. -/
theorem cleanup_exact
    (source : List WorkSymbol)
    (first : WorkSymbol) (rest : List WorkSymbol)
    (outsideLeft outsideRight : List WorkSymbol)
    (firstPacked :
      LockedNAND.TargetEmitter.PackedSymbol first) :
    workRunExact? machine (workSteps source)
        { state := State.leaveTarget
          tape :=
            TargetEmitterCursorFinalizer.finalTape
              source (first :: rest)
              outsideLeft outsideRight } =
      some
        (finalConfiguration source (first :: rest)
          outsideLeft outsideRight) := by
  let count := source.length + 1
  let targetRight :=
    first :: rest ++ cellBlank :: outsideRight
  let afterLeave :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.seekBoundary
      (List.replicate count cellBlank ++
        sourceLeftBoundary :: outsideLeft)
      targetRight
  let atBoundary :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.seekBoundary
      (sourceLeftBoundary :: outsideLeft)
      (List.replicate count cellBlank ++ targetRight)
  let returning :=
    LockedNAND.TargetEmitter.configAtWord
      State.returnTarget (cellBlank :: outsideLeft)
      (List.replicate count cellBlank ++ targetRight)
  let atTarget :=
    LockedNAND.TargetEmitter.configAtWord
      State.returnTarget
      (List.replicate count cellBlank ++
        cellBlank :: outsideLeft)
      targetRight
  have hLeave :
      workRunExact? machine 1
          { state := State.leaveTarget
            tape :=
              TargetEmitterCursorFinalizer.finalTape
                source (first :: rest)
                outsideLeft outsideRight } =
        some afterLeave := by
    simpa [afterLeave, count, targetRight,
      TargetEmitterCursorFinalizer.finalTape,
      TargetEmitterCursorFinalizer.tapeAtWord,
      TargetEmitterCursorFinalizer.configurationAtWord,
      sourceLeftBoundary,
      LockedNAND.TargetEmitter.sourceLeftBoundary,
      cellBlank, List.replicate_succ,
      List.append_assoc] using
      leave_target_step first firstPacked
        (List.replicate count cellBlank ++
          sourceLeftBoundary :: outsideLeft)
        (rest ++ cellBlank :: outsideRight)
  have hSeek :
      workRunExact? machine count afterLeave =
        some atBoundary := by
    simpa [afterLeave, atBoundary] using
      seek_blanks_exact count
        (sourceLeftBoundary :: outsideLeft) targetRight
  have hErase :
      workRunExact? machine 1 atBoundary =
        some returning := by
    simpa [atBoundary, returning, count] using
      erase_boundary_step source.length
        outsideLeft targetRight
  have hReturn :
      workRunExact? machine count returning =
        some atTarget := by
    simpa [returning, atTarget] using
      return_blanks_exact count
        (cellBlank :: outsideLeft) targetRight
  have hAccept :
      workRunExact? machine 1 atTarget =
        some
          (finalConfiguration source (first :: rest)
            outsideLeft outsideRight) := by
    have leftEq :
        List.replicate count cellBlank ++
            cellBlank :: outsideLeft =
          List.replicate (source.length + 2)
              cellBlank ++ outsideLeft := by
      have extended :=
        congrArg (fun word => word ++ outsideLeft)
          (replicate_append_one count)
      simpa [count, List.append_assoc] using extended
    have finalEq :
        finalConfiguration source (first :: rest)
            outsideLeft outsideRight =
          LockedNAND.TargetEmitter.configAtWord
            State.accept
            (List.replicate count cellBlank ++
              cellBlank :: outsideLeft)
            targetRight := by
      unfold finalConfiguration finalTape
      rw [← leftEq]
      simp [targetRight,
        TargetEmitterCursorFinalizer.tapeAtWord,
        LockedNAND.TargetEmitter.configAtWord]
    rw [finalEq]
    exact
      accept_target_step first firstPacked
        (List.replicate count cellBlank ++
          cellBlank :: outsideLeft)
        (rest ++ cellBlank :: outsideRight)
  have throughSeek :=
    exactRun_add 1 count _ afterLeave atBoundary
      hLeave hSeek
  have throughErase :=
    exactRun_add (1 + count) 1
      _ atBoundary returning throughSeek hErase
  have throughReturn :=
    exactRun_add (1 + count + 1) count
      _ returning atTarget throughErase hReturn
  have all :=
    exactRun_add (1 + count + 1 + count) 1
      _ atTarget _ throughReturn hAccept
  have stepsEq :
      (1 + count + 1 + count) + 1 =
        workSteps source := by
    simp [count, workSteps]
    omega
  rw [← stepsEq]
  exact all

end BoundaryCleanup

/-! ## Raw canonical-input framer

The root machine starts from the packed canonical CNF bytes and their
`zeroBlank` formula pad.  This literal prefix materializes the two contextual
boundaries required by `Prepare`; callers do not supply a preframed tape.
-/

namespace RawFramer

def cellBlank : WorkSymbol := WorkSymbol.blank
def formulaPad : WorkSymbol := Prepare.formulaPad
def sourceLeftBoundary : WorkSymbol :=
  Prepare.sourceLeftBoundary
def sourceTargetBoundary : WorkSymbol :=
  Prepare.sourceTargetBoundary

namespace State

def accept : Nat := 0
def reject : Nat := 1
def first : Nat := 2
def installLeft : Nat := 3
def scan : Nat := 4
def installTarget : Nat := 5
def leavePad : Nat := 6
def rewind : Nat := 7

end State

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

def packed (symbol : WorkSymbol) : Bool :=
  symbol == WorkSymbol.zeroZero ||
    symbol == WorkSymbol.zeroOne ||
    symbol == WorkSymbol.oneZero ||
    symbol == WorkSymbol.oneOne

def keep (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target
    writeSymbol := symbol
    move := move }

def reject (symbol : WorkSymbol) : Action :=
  keep State.reject .stay symbol

def firstAction (symbol : WorkSymbol) : Action :=
  if packed symbol then
    keep State.installLeft .left symbol
  else reject symbol

def installLeftAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    { targetState := State.scan
      writeSymbol := sourceLeftBoundary
      move := .right }
  else reject symbol

def scanAction (symbol : WorkSymbol) : Action :=
  if packed symbol then
    keep State.scan .right symbol
  else if symbol == formulaPad then
    keep State.installTarget .right symbol
  else reject symbol

def installTargetAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    { targetState := State.leavePad
      writeSymbol := sourceTargetBoundary
      move := .left }
  else reject symbol

def leavePadAction (symbol : WorkSymbol) : Action :=
  if symbol == formulaPad then
    keep State.rewind .left symbol
  else reject symbol

def rewindAction (symbol : WorkSymbol) : Action :=
  if packed symbol then
    keep State.rewind .left symbol
  else if symbol == sourceLeftBoundary then
    keep State.accept .right symbol
  else reject symbol

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def statePrograms : List StateProgram :=
  [ { state := State.first, action := firstAction }
  , { state := State.installLeft,
      action := installLeftAction }
  , { state := State.scan, action := scanAction }
  , { state := State.installTarget,
      action := installTargetAction }
  , { state := State.leavePad,
      action := leavePadAction }
  , { state := State.rewind, action := rewindAction }
  ]

def rulesAt (program : StateProgram) : List WorkRule :=
  LockedNAND.TargetEmitter.allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move }

def rules : List WorkRule :=
  statePrograms.flatMap rulesAt

def machine : WorkMachine :=
  { rules := rules
    startState := State.first
    acceptState := State.accept
    rejectState := State.reject }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length : rules.length = 54 := by
  rfl

set_option maxRecDepth 100000 in
theorem rules_pairwise :
    rules.Pairwise QueryDistinct := by
  unfold rules statePrograms rulesAt QueryDistinct
  simp [LockedNAND.TargetEmitter.allWorkSymbols,
    State.first, State.installLeft, State.scan,
    State.installTarget, State.leavePad, State.rewind,
    WorkSymbol.blank, WorkSymbol.blankZero,
    WorkSymbol.blankOne, WorkSymbol.zeroBlank,
    WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero,
    WorkSymbol.oneOne]

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

def workSteps (tokens : List CNFToken) : Nat :=
  2 * tokens.length + 6

private theorem exactRun_add
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (firstRun :
      workRunExact? machine first initial = some middle)
    (secondRun :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial =
      some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final
      firstRun secondRun

private theorem install_left_exact
    (token : CNFToken) (suffix : List WorkSymbol) :
    workRunExact? machine 2
        (LockedNAND.TargetEmitter.configAtWord
          State.first []
          (token.workSymbol :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan [sourceLeftBoundary]
          (token.workSymbol :: suffix)) := by
  cases token <;> cases suffix <;> rfl

private theorem scan_token_step
    (token : CNFToken)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left (token.workSymbol :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan (token.workSymbol :: left) suffix) := by
  cases token <;> cases suffix <;> rfl

private theorem scan_tokens_exact
    (tokens : List CNFToken)
    (left suffix : List WorkSymbol) :
    workRunExact? machine tokens.length
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left
          (cnfTokenWorkSymbols tokens ++ suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.scan
          ((cnfTokenWorkSymbols tokens).reverse ++ left)
          suffix) := by
  induction tokens generalizing left with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      have first :=
        scan_token_step token left
          (cnfTokenWorkSymbols rest ++ suffix)
      have tail :=
        inductionHypothesis (token.workSymbol :: left)
      have combined :=
        exactRun_add 1 rest.length
          (LockedNAND.TargetEmitter.configAtWord
            State.scan left
            (token.workSymbol ::
              cnfTokenWorkSymbols rest ++ suffix))
          (LockedNAND.TargetEmitter.configAtWord
            State.scan (token.workSymbol :: left)
            (cnfTokenWorkSymbols rest ++ suffix))
          (LockedNAND.TargetEmitter.configAtWord
            State.scan
            ((cnfTokenWorkSymbols rest).reverse ++
              token.workSymbol :: left)
            suffix)
          first tail
      simpa [cnfTokenWorkSymbols, List.reverse_cons,
        List.append_assoc, Nat.add_comm] using combined

private theorem install_target_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 3
        (LockedNAND.TargetEmitter.configAtWord
          State.scan left
          (formulaPad :: cellBlank :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left
          (formulaPad :: sourceTargetBoundary :: suffix)) := by
  cases left <;> rfl

private theorem rewind_symbol_step
    (symbol : WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol symbol)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind (symbol :: left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left (symbol :: suffix)) := by
  cases ordinary <;> cases left <;> rfl

private theorem rewind_nearest_exact
    (nearest left suffix : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ nearest →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact? machine nearest.length
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind (nearest ++ left) suffix) =
      some
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind left (nearest.reverse ++ suffix)) := by
  induction nearest generalizing suffix with
  | nil =>
      rfl
  | cons symbol rest inductionHypothesis =>
      have headOrdinary :=
        ordinary symbol (List.Mem.head rest)
      have restOrdinary :
          ∀ item, item ∈ rest →
            LockedNAND.TargetEmitter.PackedSymbol item := by
        intro item member
        exact ordinary item (List.Mem.tail symbol member)
      have first :=
        rewind_symbol_step symbol headOrdinary
          (rest ++ left) suffix
      have tail :=
        inductionHypothesis (symbol :: suffix) restOrdinary
      have combined :=
        exactRun_add 1 rest.length
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind (symbol :: rest ++ left) suffix)
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind (rest ++ left) (symbol :: suffix))
          (LockedNAND.TargetEmitter.configAtLeftWord
            State.rewind left
            (rest.reverse ++ symbol :: suffix))
          first tail
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using combined

private theorem token_symbols_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ cnfTokenWorkSymbols tokens →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  induction tokens with
  | nil =>
      contradiction
  | cons token rest inductionHypothesis =>
      simp only [cnfTokenWorkSymbols, List.mem_cons]
        at member
      rcases member with equality | restMember
      · subst symbol
        cases token <;> constructor
      · exact inductionHypothesis restMember

private theorem token_symbols_reverse_packed
    (tokens : List CNFToken) :
    ∀ symbol,
      symbol ∈ (cnfTokenWorkSymbols tokens).reverse →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  exact token_symbols_packed tokens symbol
    (List.mem_reverse.mp member)

private theorem rewind_boundary_step
    (right : List WorkSymbol) :
    workRunExact? machine 1
        (LockedNAND.TargetEmitter.configAtLeftWord
          State.rewind [sourceLeftBoundary] right) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept [sourceLeftBoundary] right) := by
  cases right <;> rfl

/-- Exact framing of a nonempty raw canonical token word.  The initial left
side is truly empty; the source-left boundary is manufactured from the
implicit blank cell. -/
theorem canonical_exact
    (first : CNFToken) (rest : List CNFToken)
    (suffix : List WorkSymbol) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    workRunExact? machine (workSteps tokens)
        (LockedNAND.TargetEmitter.configAtWord
          State.first []
          (source ++ formulaPad :: cellBlank :: suffix)) =
      some
        (LockedNAND.TargetEmitter.configAtWord
          State.accept [sourceLeftBoundary]
          (source ++
            formulaPad :: sourceTargetBoundary :: suffix)) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  let afterLeft :=
    LockedNAND.TargetEmitter.configAtWord
      State.scan [sourceLeftBoundary]
      (source ++ formulaPad :: cellBlank :: suffix)
  let atPad :=
    LockedNAND.TargetEmitter.configAtWord
      State.scan (source.reverse ++ [sourceLeftBoundary])
      (formulaPad :: cellBlank :: suffix)
  let afterTarget :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.rewind (source.reverse ++ [sourceLeftBoundary])
      (formulaPad :: sourceTargetBoundary :: suffix)
  let atBoundary :=
    LockedNAND.TargetEmitter.configAtLeftWord
      State.rewind [sourceLeftBoundary]
      (source ++ formulaPad :: sourceTargetBoundary :: suffix)
  have hLeft :
      workRunExact? machine 2
          (LockedNAND.TargetEmitter.configAtWord
            State.first []
            (source ++ formulaPad :: cellBlank :: suffix)) =
        some afterLeft := by
    simpa [tokens, source, afterLeft,
      cnfTokenWorkSymbols, List.append_assoc] using
      install_left_exact first
        (cnfTokenWorkSymbols rest ++
          formulaPad :: cellBlank :: suffix)
  have hScan :
      workRunExact? machine tokens.length afterLeft =
        some atPad := by
    simpa [afterLeft, atPad] using
      scan_tokens_exact tokens [sourceLeftBoundary]
        (formulaPad :: cellBlank :: suffix)
  have hTarget :
      workRunExact? machine 3 atPad =
        some afterTarget := by
    simpa [atPad, afterTarget] using
      install_target_exact
        (source.reverse ++ [sourceLeftBoundary]) suffix
  have hRewind :
      workRunExact? machine source.length afterTarget =
        some atBoundary := by
    simpa [afterTarget, atBoundary,
      List.reverse_reverse, List.append_assoc] using
      rewind_nearest_exact source.reverse
        [sourceLeftBoundary]
        (formulaPad :: sourceTargetBoundary :: suffix)
        (token_symbols_reverse_packed tokens)
  have hBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (LockedNAND.TargetEmitter.configAtWord
            State.accept [sourceLeftBoundary]
            (source ++ formulaPad ::
              sourceTargetBoundary :: suffix)) := by
    simpa [atBoundary] using
      rewind_boundary_step
        (source ++ formulaPad ::
          sourceTargetBoundary :: suffix)
  have throughScan :=
    exactRun_add 2 tokens.length
      _ afterLeft atPad hLeft hScan
  have throughTarget :=
    exactRun_add (2 + tokens.length) 3
      _ atPad afterTarget throughScan hTarget
  have throughRewind :=
    exactRun_add (2 + tokens.length + 3) source.length
      _ afterTarget atBoundary throughTarget hRewind
  have all :=
    exactRun_add
      (2 + tokens.length + 3 + source.length) 1
      _ atBoundary _ throughRewind hBoundary
  have stepsEq :
      (2 + tokens.length + 3 + source.length) + 1 =
        workSteps tokens := by
    simp [workSteps, source, cnfTokenWorkSymbols_length]
    omega
  rw [← stepsEq]
  exact all

end RawFramer

/-! ## Closed physical plan and polynomial accounting

The graph materialization layer consumes only the following finite families:
the pad preparer, five literal matchers, four cursor installers, the twelve
literal token requests for a gate, four cursor restorers, the boundary
rewinder, the four-token suffix, and terminal cleanup.  These definitions are
kept public so the next workspace layer can connect to the same literal
machines without inventing new tape conventions.
-/

def cnfTokenOrder : List CNFToken :=
  [.f, .sep, .finish, .t]

def tokenCode : CNFToken → Nat
  | .f => 0
  | .sep => 1
  | .finish => 2
  | .t => 3

theorem tokenCode_injective :
    Function.Injective tokenCode := by
  intro left right equality
  cases left <;> cases right <;> simp [tokenCode] at equality ⊢

def firstConstantToken (token : CNFToken) : Token :=
  Source.constantToken (Source.firstBit token)

def secondConstantToken (token : CNFToken) : Token :=
  Source.constantToken (Source.secondBit token)

def sourceSymbol (token : CNFToken) : WorkSymbol :=
  token.workSymbol

theorem sourceSymbol_packed (token : CNFToken) :
    LockedNAND.TargetEmitter.PackedSymbol
      (sourceSymbol token) := by
  cases token <;> constructor

/-! ## Literal program graph

The first pass appends one unary gate-count unit for every retained source
token.  The second pass appends the two constant-source tags and gate
terminator selected by that token.  All dispatch is performed by the five
fixed one-cell matchers in each pass.
-/

def controlRef (name : Nat) (program : WorkMachine) : NodeRef :=
  { name := name
    startState := program.startState }

def controlNode (name : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint) : Node :=
  { name := name
    program := program
    onAccept := onAccept
    onReject := onReject }

namespace Address

def prepare : Nat := 0
def headerVersion : Nat := 1
def headerInputEnd : Nat := 2

def countMatch (token : CNFToken) : Nat :=
  10 + tokenCode token
def countBoundary : Nat := 14
def countInstall (token : CNFToken) : Nat :=
  20 + tokenCode token
def countUnit (token : CNFToken) : Nat :=
  30 + tokenCode token
def countRestore (token : CNFToken) : Nat :=
  40 + tokenCode token
def countRewind : Nat := 44
def gateCountEnd : Nat := 45

def gateMatch (token : CNFToken) : Nat :=
  50 + tokenCode token
def gateBoundary : Nat := 54
def gateInstall (token : CNFToken) : Nat :=
  60 + tokenCode token
def gateFirst (token : CNFToken) : Nat :=
  70 + tokenCode token
def gateSecond (token : CNFToken) : Nat :=
  80 + tokenCode token
def gateEnd (token : CNFToken) : Nat :=
  90 + tokenCode token
def gateRestore (token : CNFToken) : Nat :=
  100 + tokenCode token
def gateRewind : Nat := 104

def suffixProgramEnd : Nat := 110
def suffixOutput : Nat := 111
def suffixOutputsEnd : Nat := 112
def suffixInstanceEnd : Nat := 113
def finalizer : Nat := 114
def cleanup : Nat := 115
def framer : Nat := 116

end Address

def prepareRef : NodeRef :=
  controlRef Address.prepare Prepare.machine

def framerRef : NodeRef :=
  controlRef Address.framer RawFramer.machine

def headerVersionRef : NodeRef :=
  controlRef Address.headerVersion
    (TargetEmitterCursorAppender.machineFor .version0)

def headerInputEndRef : NodeRef :=
  controlRef Address.headerInputEnd
    (TargetEmitterCursorAppender.machineFor .natEnd)

def countMatchRef (token : CNFToken) : NodeRef :=
  controlRef (Address.countMatch token)
    (Match.machine (sourceSymbol token))

def countBoundaryRef : NodeRef :=
  controlRef Address.countBoundary
    (Match.machine Prepare.sourceTargetBoundary)

def countInstallRef (token : CNFToken) : NodeRef :=
  controlRef (Address.countInstall token)
    (TargetEmitterCursorControl.installMachine
      (sourceSymbol token))

def countUnitRef (token : CNFToken) : NodeRef :=
  controlRef (Address.countUnit token)
    (TargetEmitterCursorAppender.machineFor .unit)

def countRestoreRef (token : CNFToken) : NodeRef :=
  controlRef (Address.countRestore token)
    (TargetEmitterCursorControl.restoreMachine
      (sourceSymbol token))

def countRewindRef : NodeRef :=
  controlRef Address.countRewind Rewind.machine

def gateCountEndRef : NodeRef :=
  controlRef Address.gateCountEnd
    (TargetEmitterCursorAppender.machineFor .natEnd)

def gateMatchRef (token : CNFToken) : NodeRef :=
  controlRef (Address.gateMatch token)
    (Match.machine (sourceSymbol token))

def gateBoundaryRef : NodeRef :=
  controlRef Address.gateBoundary
    (Match.machine Prepare.sourceTargetBoundary)

def gateInstallRef (token : CNFToken) : NodeRef :=
  controlRef (Address.gateInstall token)
    (TargetEmitterCursorControl.installMachine
      (sourceSymbol token))

def gateFirstRef (token : CNFToken) : NodeRef :=
  controlRef (Address.gateFirst token)
    (TargetEmitterCursorAppender.machineFor
      (firstConstantToken token))

def gateSecondRef (token : CNFToken) :=
  controlRef (Address.gateSecond token)
    (TargetEmitterCursorAppender.machineFor
      (secondConstantToken token))

def gateEndRef (token : CNFToken) : NodeRef :=
  controlRef (Address.gateEnd token)
    (TargetEmitterCursorAppender.machineFor .gateEnd)

def gateRestoreRef (token : CNFToken) : NodeRef :=
  controlRef (Address.gateRestore token)
    (TargetEmitterCursorControl.restoreMachine
      (sourceSymbol token))

def gateRewindRef : NodeRef :=
  controlRef Address.gateRewind Rewind.machine

def suffixProgramEndRef : NodeRef :=
  controlRef Address.suffixProgramEnd
    (TargetEmitterCursorAppender.machineFor .programEnd)

def suffixOutputRef : NodeRef :=
  controlRef Address.suffixOutput
    (TargetEmitterCursorAppender.machineFor .constantFalse)

def suffixOutputsEndRef : NodeRef :=
  controlRef Address.suffixOutputsEnd
    (TargetEmitterCursorAppender.machineFor .outputsEnd)

def suffixInstanceEndRef : NodeRef :=
  controlRef Address.suffixInstanceEnd
    (TargetEmitterCursorAppender.machineFor .instanceEnd)

def finalizerRef : NodeRef :=
  controlRef Address.finalizer
    TargetEmitterCursorFinalizer.machine

def cleanupRef : NodeRef :=
  controlRef Address.cleanup BoundaryCleanup.machine

def nextCountMatchRef : CNFToken → NodeRef
  | .f => countMatchRef .sep
  | .sep => countMatchRef .finish
  | .finish => countMatchRef .t
  | .t => countBoundaryRef

def nextGateMatchRef : CNFToken → NodeRef
  | .f => gateMatchRef .sep
  | .sep => gateMatchRef .finish
  | .finish => gateMatchRef .t
  | .t => gateBoundaryRef

def prepareNode : Node :=
  controlNode Address.prepare Prepare.machine
    (.node headerVersionRef) .reject

def framerNode : Node :=
  controlNode Address.framer RawFramer.machine
    (.node prepareRef) .reject

def headerVersionNode : Node :=
  controlNode Address.headerVersion
    (TargetEmitterCursorAppender.machineFor .version0)
    (.node headerInputEndRef) .reject

def headerInputEndNode : Node :=
  controlNode Address.headerInputEnd
    (TargetEmitterCursorAppender.machineFor .natEnd)
    (.node (countMatchRef .f)) .reject

def countMatchNode (token : CNFToken) : Node :=
  controlNode (Address.countMatch token)
    (Match.machine (sourceSymbol token))
    (.node (countInstallRef token))
    (.node (nextCountMatchRef token))

def countBoundaryNode : Node :=
  controlNode Address.countBoundary
    (Match.machine Prepare.sourceTargetBoundary)
    (.node countRewindRef) .reject

def countInstallNode (token : CNFToken) : Node :=
  controlNode (Address.countInstall token)
    (TargetEmitterCursorControl.installMachine
      (sourceSymbol token))
    (.node (countUnitRef token)) .reject

def countUnitNode (token : CNFToken) : Node :=
  controlNode (Address.countUnit token)
    (TargetEmitterCursorAppender.machineFor .unit)
    (.node (countRestoreRef token)) .reject

def countRestoreNode (token : CNFToken) : Node :=
  controlNode (Address.countRestore token)
    (TargetEmitterCursorControl.restoreMachine
      (sourceSymbol token))
    (.node (countMatchRef .f)) .reject

def countRewindNode : Node :=
  controlNode Address.countRewind Rewind.machine
    (.node gateCountEndRef) .reject

def gateCountEndNode : Node :=
  controlNode Address.gateCountEnd
    (TargetEmitterCursorAppender.machineFor .natEnd)
    (.node (gateMatchRef .f)) .reject

def gateMatchNode (token : CNFToken) : Node :=
  controlNode (Address.gateMatch token)
    (Match.machine (sourceSymbol token))
    (.node (gateInstallRef token))
    (.node (nextGateMatchRef token))

def gateBoundaryNode : Node :=
  controlNode Address.gateBoundary
    (Match.machine Prepare.sourceTargetBoundary)
    (.node gateRewindRef) .reject

def gateInstallNode (token : CNFToken) : Node :=
  controlNode (Address.gateInstall token)
    (TargetEmitterCursorControl.installMachine
      (sourceSymbol token))
    (.node (gateFirstRef token)) .reject

def gateFirstNode (token : CNFToken) : Node :=
  controlNode (Address.gateFirst token)
    (TargetEmitterCursorAppender.machineFor
      (firstConstantToken token))
    (.node (gateSecondRef token)) .reject

def gateSecondNode (token : CNFToken) : Node :=
  controlNode (Address.gateSecond token)
    (TargetEmitterCursorAppender.machineFor
      (secondConstantToken token))
    (.node (gateEndRef token)) .reject

def gateEndNode (token : CNFToken) : Node :=
  controlNode (Address.gateEnd token)
    (TargetEmitterCursorAppender.machineFor .gateEnd)
    (.node (gateRestoreRef token)) .reject

def gateRestoreNode (token : CNFToken) : Node :=
  controlNode (Address.gateRestore token)
    (TargetEmitterCursorControl.restoreMachine
      (sourceSymbol token))
    (.node (gateMatchRef .f)) .reject

def gateRewindNode : Node :=
  controlNode Address.gateRewind Rewind.machine
    (.node suffixProgramEndRef) .reject

def suffixProgramEndNode : Node :=
  controlNode Address.suffixProgramEnd
    (TargetEmitterCursorAppender.machineFor .programEnd)
    (.node suffixOutputRef) .reject

def suffixOutputNode : Node :=
  controlNode Address.suffixOutput
    (TargetEmitterCursorAppender.machineFor .constantFalse)
    (.node suffixOutputsEndRef) .reject

def suffixOutputsEndNode : Node :=
  controlNode Address.suffixOutputsEnd
    (TargetEmitterCursorAppender.machineFor .outputsEnd)
    (.node suffixInstanceEndRef) .reject

def suffixInstanceEndNode : Node :=
  controlNode Address.suffixInstanceEnd
    (TargetEmitterCursorAppender.machineFor .instanceEnd)
    (.node finalizerRef) .reject

def finalizerNode : Node :=
  controlNode Address.finalizer
    TargetEmitterCursorFinalizer.machine
    (.node cleanupRef) .reject

def cleanupNode : Node :=
  controlNode Address.cleanup BoundaryCleanup.machine
    .accept .reject

def prefixNodes : List Node :=
  [framerNode, prepareNode,
    headerVersionNode, headerInputEndNode]

def countNodes : List Node :=
  cnfTokenOrder.map countMatchNode ++
    [countBoundaryNode] ++
    cnfTokenOrder.map countInstallNode ++
    cnfTokenOrder.map countUnitNode ++
    cnfTokenOrder.map countRestoreNode ++
    [countRewindNode, gateCountEndNode]

def gateNodes : List Node :=
  cnfTokenOrder.map gateMatchNode ++
    [gateBoundaryNode] ++
    cnfTokenOrder.map gateInstallNode ++
    cnfTokenOrder.map gateFirstNode ++
    cnfTokenOrder.map gateSecondNode ++
    cnfTokenOrder.map gateEndNode ++
    cnfTokenOrder.map gateRestoreNode ++
    [gateRewindNode]

def suffixNodes : List Node :=
  [suffixProgramEndNode, suffixOutputNode,
    suffixOutputsEndNode, suffixInstanceEndNode,
    finalizerNode, cleanupNode]

def nodes : List Node :=
  prefixNodes ++ countNodes ++ gateNodes ++ suffixNodes

def graph : Graph :=
  { nodes := nodes
    entry := framerRef }

def machine : WorkMachine :=
  WorkMachineProgramGraph.machine graph

def compiledMachine : Machine :=
  compileWorkMachine machine

/-! ### Structural closure of the finite graph -/

private theorem nodeWellFormed_of_interfaces
    (name : Nat) (program : WorkMachine)
    (onAccept onReject : Endpoint)
    (pairwise :
      program.rules.Pairwise
        WorkMachineProgramGraph.QueryDistinct)
    (noAccept :
      ∀ symbol,
        findWorkRule program.rules
          program.acceptState symbol = none)
    (noReject :
      ∀ symbol,
        findWorkRule program.rules
          program.rejectState symbol = none)
    (acceptNeReject :
      program.acceptState ≠ program.rejectState) :
    (controlNode name program
      onAccept onReject).WellFormed := by
  exact
    ⟨pairwise,
      noRuleAt_of_findWorkRule_none
        program program.acceptState noAccept,
      noRuleAt_of_findWorkRule_none
        program program.rejectState noReject,
      acceptNeReject⟩

private theorem prepareNode_wellFormed :
    prepareNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change Prepare.rules.Pairwise Prepare.QueryDistinct
    exact Prepare.rules_pairwise
  · exact Prepare.no_rule_at_accept
  · exact Prepare.no_rule_at_reject
  · exact Prepare.accept_ne_reject

private theorem framerNode_wellFormed :
    framerNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change RawFramer.rules.Pairwise RawFramer.QueryDistinct
    exact RawFramer.rules_pairwise
  · exact RawFramer.no_rule_at_accept
  · exact RawFramer.no_rule_at_reject
  · exact RawFramer.accept_ne_reject

private theorem matchNode_wellFormed
    (name : Nat) (expected : WorkSymbol)
    (onAccept onReject : Endpoint) :
    (controlNode name (Match.machine expected)
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change (Match.rules expected).Pairwise Match.QueryDistinct
    exact Match.rules_pairwise expected
  · exact Match.no_rule_at_accept expected
  · exact Match.no_rule_at_reject expected
  · exact Match.accept_ne_reject expected

private theorem appenderNode_wellFormed
    (name : Nat) (token : Token)
    (onAccept onReject : Endpoint) :
    (controlNode name
      (TargetEmitterCursorAppender.machineFor token)
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change TargetEmitterCursorAppender.rules.Pairwise
      TargetEmitterCursorAppender.QueryDistinct
    exact TargetEmitterCursorAppender.rules_pairwise
  · exact TargetEmitterCursorAppender.no_rule_at_done token
  · exact TargetEmitterCursorAppender.no_rule_at_reject
  · exact
      TargetEmitterCursorAppender.machine_accept_ne_reject token

private theorem installNode_wellFormed
    (name : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) :
    (controlNode name
      (TargetEmitterCursorControl.installMachine original)
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change (TargetEmitterCursorControl.rules original).Pairwise
      TargetEmitterCursorControl.QueryDistinct
    exact TargetEmitterCursorControl.rules_pairwise original
  · exact TargetEmitterCursorControl.no_rule_at_installed original
  · exact TargetEmitterCursorControl.no_rule_at_reject original
  · exact TargetEmitterCursorControl.install_accept_ne_reject original

private theorem restoreNode_wellFormed
    (name : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) :
    (controlNode name
      (TargetEmitterCursorControl.restoreMachine original)
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change (TargetEmitterCursorControl.rules original).Pairwise
      TargetEmitterCursorControl.QueryDistinct
    exact TargetEmitterCursorControl.rules_pairwise original
  · exact TargetEmitterCursorControl.no_rule_at_restored original
  · exact TargetEmitterCursorControl.no_rule_at_reject original
  · exact TargetEmitterCursorControl.restore_accept_ne_reject original

private theorem rewindNode_wellFormed
    (name : Nat) (onAccept onReject : Endpoint) :
    (controlNode name Rewind.machine
      onAccept onReject).WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change Rewind.rules.Pairwise Rewind.QueryDistinct
    exact Rewind.rules_pairwise
  · exact Rewind.no_rule_at_accept
  · exact Rewind.no_rule_at_reject
  · exact Rewind.accept_ne_reject

private theorem finalizerNode_wellFormed :
    finalizerNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change TargetEmitterCursorFinalizer.rules.Pairwise
      (fun left right =>
        (left.sourceState, left.readSymbol) ≠
          (right.sourceState, right.readSymbol))
    exact TargetEmitterCursorFinalizer.rules_pairwise
  · exact TargetEmitterCursorFinalizer.no_rule_at_accept
  · exact TargetEmitterCursorFinalizer.no_rule_at_reject
  · exact TargetEmitterCursorFinalizer.accept_ne_reject

private theorem cleanupNode_wellFormed :
    cleanupNode.WellFormed := by
  apply nodeWellFormed_of_interfaces
  · change BoundaryCleanup.rules.Pairwise
      BoundaryCleanup.QueryDistinct
    exact BoundaryCleanup.rules_pairwise
  · exact BoundaryCleanup.no_rule_at_accept
  · exact BoundaryCleanup.no_rule_at_reject
  · exact BoundaryCleanup.accept_ne_reject

private theorem mappedNodes_wellFormed
    (builder : CNFToken → Node)
    (builderWellFormed :
      ∀ token, (builder token).WellFormed) :
    ∀ node, node ∈ cnfTokenOrder.map builder →
      node.WellFormed := by
  intro node member
  rcases List.mem_map.mp member with
    ⟨token, _tokenMember, equality⟩
  rw [← equality]
  exact builderWellFormed token

private theorem prefixNodes_wellFormed :
    ∀ node, node ∈ prefixNodes → node.WellFormed := by
  intro node member
  simp only [prefixNodes, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    equality | equality | equality | equality
  · subst node
    exact framerNode_wellFormed
  · subst node
    exact prepareNode_wellFormed
  · subst node
    exact appenderNode_wellFormed _ _ _ _
  · subst node
    exact appenderNode_wellFormed _ _ _ _

private theorem countNodes_wellFormed :
    ∀ node, node ∈ countNodes → node.WellFormed := by
  intro node member
  simp only [countNodes, List.mem_append] at member
  rcases member with
      (((((matchMember | boundaryMember) | installMember) |
          unitMember) | restoreMember) | finalMember)
  · exact mappedNodes_wellFormed countMatchNode
      (fun token => matchNode_wellFormed _ _ _ _)
      node matchMember
  · simp only [List.mem_singleton] at boundaryMember
    subst node
    exact matchNode_wellFormed _ _ _ _
  · exact mappedNodes_wellFormed countInstallNode
      (fun token => installNode_wellFormed _ _ _ _)
      node installMember
  · exact mappedNodes_wellFormed countUnitNode
      (fun token => appenderNode_wellFormed _ _ _ _)
      node unitMember
  · exact mappedNodes_wellFormed countRestoreNode
      (fun token => restoreNode_wellFormed _ _ _ _)
      node restoreMember
  · simp only [List.mem_cons, List.not_mem_nil,
      or_false] at finalMember
    rcases finalMember with equality | equality
    · subst node
      exact rewindNode_wellFormed _ _ _
    · subst node
      exact appenderNode_wellFormed _ _ _ _

private theorem gateNodes_wellFormed :
    ∀ node, node ∈ gateNodes → node.WellFormed := by
  intro node member
  simp only [gateNodes, List.mem_append] at member
  rcases member with
      (((((((matchMember | boundaryMember) | installMember) |
          firstMember) | secondMember) | endMember) |
          restoreMember) | rewindMember)
  · exact mappedNodes_wellFormed gateMatchNode
      (fun token => matchNode_wellFormed _ _ _ _)
      node matchMember
  · simp only [List.mem_singleton] at boundaryMember
    subst node
    exact matchNode_wellFormed _ _ _ _
  · exact mappedNodes_wellFormed gateInstallNode
      (fun token => installNode_wellFormed _ _ _ _)
      node installMember
  · exact mappedNodes_wellFormed gateFirstNode
      (fun token => appenderNode_wellFormed _ _ _ _)
      node firstMember
  · exact mappedNodes_wellFormed gateSecondNode
      (fun token => appenderNode_wellFormed _ _ _ _)
      node secondMember
  · exact mappedNodes_wellFormed gateEndNode
      (fun token => appenderNode_wellFormed _ _ _ _)
      node endMember
  · exact mappedNodes_wellFormed gateRestoreNode
      (fun token => restoreNode_wellFormed _ _ _ _)
      node restoreMember
  · simp only [List.mem_singleton] at rewindMember
    subst node
    exact rewindNode_wellFormed _ _ _

private theorem suffixNodes_wellFormed :
    ∀ node, node ∈ suffixNodes → node.WellFormed := by
  intro node member
  simp only [suffixNodes, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with
    equality | equality | equality | equality | equality | equality
  · subst node
    exact appenderNode_wellFormed _ _ _ _
  · subst node
    exact appenderNode_wellFormed _ _ _ _
  · subst node
    exact appenderNode_wellFormed _ _ _ _
  · subst node
    exact appenderNode_wellFormed _ _ _ _
  · subst node
    exact finalizerNode_wellFormed
  · subst node
    exact cleanupNode_wellFormed

private theorem nodes_wellFormed :
    ∀ node, node ∈ nodes → node.WellFormed := by
  intro node member
  simp only [nodes, List.mem_append] at member
  rcases member with
      ((prefixMember | countMember) | gateMember) |
        suffixMember
  · exact prefixNodes_wellFormed node prefixMember
  · exact countNodes_wellFormed node countMember
  · exact gateNodes_wellFormed node gateMember
  · exact suffixNodes_wellFormed node suffixMember

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem nodeNames_pairwise :
    nodes.Pairwise
      (fun left right => left.name ≠ right.name) := by
  decide

private def knownReferences : List NodeRef :=
  nodes.map Node.reference

private theorem knownReference_resolves
    (reference : NodeRef)
    (known : reference ∈ knownReferences) :
    Endpoint.Resolves nodes (.node reference) := by
  rcases List.mem_map.mp known with
    ⟨node, member, equality⟩
  rw [← equality]
  exact ⟨node, member, rfl, rfl⟩

private def referenceKnownIn :
    List NodeRef → NodeRef → Bool
  | [], _ => false
  | first :: rest, target =>
      decide (first = target) ||
        referenceKnownIn rest target

private theorem member_of_referenceKnownIn
    (references : List NodeRef) (target : NodeRef)
    (known : referenceKnownIn references target = true) :
    target ∈ references := by
  induction references with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [referenceKnownIn, Bool.or_eq_true] at known
      rcases known with firstEq | restKnown
      · have equality : first = target := by
          simpa using firstEq
        subst target
        exact List.Mem.head rest
      · exact List.Mem.tail first
          (inductionHypothesis restKnown)

private def endpointKnown : Endpoint → Bool
  | .node reference =>
      referenceKnownIn knownReferences reference
  | .accept | .reject | .dead => true

private theorem endpoint_resolves_of_known
    (endpoint : Endpoint)
    (known : endpointKnown endpoint = true) :
    Endpoint.Resolves nodes endpoint := by
  cases endpoint with
  | node reference =>
      exact knownReference_resolves reference
        (member_of_referenceKnownIn
          knownReferences reference known)
  | accept =>
      trivial
  | reject =>
      trivial
  | dead =>
      trivial

private def allNodeEndpointsKnown : List Node → Bool
  | [] => true
  | node :: rest =>
      endpointKnown node.onAccept &&
        (endpointKnown node.onReject &&
          allNodeEndpointsKnown rest)

private theorem endpoints_known_of_all
    (items : List Node)
    (allKnown : allNodeEndpointsKnown items = true)
    (node : Node) (member : node ∈ items) :
    endpointKnown node.onAccept = true ∧
      endpointKnown node.onReject = true := by
  induction items generalizing node with
  | nil =>
      contradiction
  | cons first rest inductionHypothesis =>
      simp only [allNodeEndpointsKnown, Bool.and_eq_true]
        at allKnown
      rcases allKnown with
        ⟨firstAccept, firstReject, restKnown⟩
      rcases List.mem_cons.mp member with
        equality | restMember
      · subst node
        exact ⟨firstAccept, firstReject⟩
      · exact inductionHypothesis restKnown node restMember

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem all_endpoints_known :
    allNodeEndpointsKnown nodes = true := by
  decide

private theorem nodes_endpoints_resolve :
    ∀ node, node ∈ nodes →
      Endpoint.Resolves nodes node.onAccept ∧
        Endpoint.Resolves nodes node.onReject := by
  intro node member
  rcases endpoints_known_of_all nodes
      all_endpoints_known node member with
    ⟨acceptKnown, rejectKnown⟩
  exact
    ⟨endpoint_resolves_of_known node.onAccept acceptKnown,
      endpoint_resolves_of_known node.onReject rejectKnown⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
private theorem entry_resolves :
    Endpoint.Resolves nodes (.node framerRef) := by
  apply knownReference_resolves
  apply List.mem_map.mpr
  exact
    ⟨framerNode,
      by simp [nodes, prefixNodes],
      by rfl⟩

theorem graph_wellFormed :
    graph.WellFormed := by
  exact
    ⟨nodeNames_pairwise,
      nodes_wellFormed,
      entry_resolves,
      nodes_endpoints_resolve⟩

theorem rules_pairwise :
    machine.rules.Pairwise
      WorkMachineProgramGraph.QueryDistinct :=
  WorkMachineProgramGraph.rules_pairwise graph graph_wellFormed

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState :=
  WorkMachineProgramGraph.machine_start_ne_accept graph

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_start_ne_reject graph

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState :=
  WorkMachineProgramGraph.machine_accept_ne_reject graph

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.acceptState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_accept graph symbol

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule machine.rules machine.rejectState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_reject graph symbol

theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule machine.rules
      WorkMachineProgramGraph.globalDeadState symbol = none :=
  WorkMachineProgramGraph.no_rule_at_dead graph symbol

theorem nodes_length : nodes.length = 55 := by
  rfl

private def nodeCharge (node : Node) : Nat :=
  18 + node.program.rules.length

private theorem prepareNode_charge :
    nodeCharge prepareNode = 63 := by
  change 18 + Prepare.rules.length = 63
  rw [Prepare.rules_length]

private theorem framerNode_charge :
    nodeCharge framerNode = 72 := by
  change 18 + RawFramer.rules.length = 72
  rw [RawFramer.rules_length]

private theorem matchNode_charge
    (name : Nat) (expected : WorkSymbol)
    (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name (Match.machine expected)
          onAccept onReject) =
      27 := by
  change 18 + (Match.rules expected).length = 27
  rw [Match.rules_length]

private theorem appenderNode_charge
    (name : Nat) (token : Token)
    (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name
          (TargetEmitterCursorAppender.machineFor token)
          onAccept onReject) =
      558 := by
  change 18 + TargetEmitterCursorAppender.rules.length = 558
  rw [TargetEmitterCursorAppender.rules_length]

private theorem cursorNode_charge
    (name : Nat) (original : WorkSymbol)
    (program :
      WorkSymbol → WorkMachine)
    (programRules :
      ∀ symbol, (program symbol).rules =
        TargetEmitterCursorControl.rules symbol)
    (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name (program original)
          onAccept onReject) =
      29 := by
  change 18 + (program original).rules.length = 29
  rw [programRules, TargetEmitterCursorControl.rules_length]

private theorem rewindNode_charge
    (name : Nat) (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name Rewind.machine
          onAccept onReject) =
      36 := by
  change 18 + Rewind.rules.length = 36
  rw [Rewind.rules_length]

private theorem finalizerNode_charge :
    nodeCharge finalizerNode = 24 := by
  change 18 + TargetEmitterCursorFinalizer.rules.length = 24
  rw [TargetEmitterCursorFinalizer.rules_length]

private theorem cleanupNode_charge :
    nodeCharge cleanupNode = 45 := by
  change 18 + BoundaryCleanup.rules.length = 45
  rw [BoundaryCleanup.rules_length]

private theorem installNode_charge
    (name : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name
          (TargetEmitterCursorControl.installMachine original)
          onAccept onReject) =
      29 := by
  exact cursorNode_charge name original
    TargetEmitterCursorControl.installMachine
    (fun _ => rfl) onAccept onReject

private theorem restoreNode_charge
    (name : Nat) (original : WorkSymbol)
    (onAccept onReject : Endpoint) :
    nodeCharge
        (controlNode name
          (TargetEmitterCursorControl.restoreMachine original)
          onAccept onReject) =
      29 := by
  exact cursorNode_charge name original
    TargetEmitterCursorControl.restoreMachine
    (fun _ => rfl) onAccept onReject

private theorem prefixNodes_charge :
    (prefixNodes.map nodeCharge).sum = 1251 := by
  simp [prefixNodes, headerVersionNode, headerInputEndNode,
    framerNode_charge, prepareNode_charge,
    appenderNode_charge]

private theorem countNodes_charge :
    (countNodes.map nodeCharge).sum = 3193 := by
  simp [countNodes, cnfTokenOrder, countMatchNode,
    countBoundaryNode, countInstallNode, countUnitNode,
    countRestoreNode, countRewindNode, gateCountEndNode,
    matchNode_charge, installNode_charge,
    appenderNode_charge, restoreNode_charge,
    rewindNode_charge]

private theorem gateNodes_charge :
    (gateNodes.map nodeCharge).sum = 7099 := by
  simp [gateNodes, cnfTokenOrder, gateMatchNode,
    gateBoundaryNode, gateInstallNode, gateFirstNode,
    gateSecondNode, gateEndNode, gateRestoreNode,
    gateRewindNode, matchNode_charge, installNode_charge,
    appenderNode_charge, restoreNode_charge,
    rewindNode_charge]

private theorem suffixNodes_charge :
    (suffixNodes.map nodeCharge).sum = 2301 := by
  simp [suffixNodes, suffixProgramEndNode, suffixOutputNode,
    suffixOutputsEndNode, suffixInstanceEndNode,
    appenderNode_charge, finalizerNode_charge,
    cleanupNode_charge]

theorem rules_length : machine.rules.length = 13844 := by
  change (WorkMachineProgramGraph.rules graph).length = 13844
  rw [WorkMachineProgramGraph.rules_length]
  change (nodes.map nodeCharge).sum = 13844
  rw [nodes, List.map_append, List.sum_append,
    List.map_append, List.sum_append,
    List.map_append, List.sum_append,
    prefixNodes_charge, countNodes_charge,
    gateNodes_charge, suffixNodes_charge]

def appendedTokenCount (tokens : List CNFToken) : Nat :=
  4 * tokens.length + 7

/-- Blanks following the old source boundary.  Preparation erases that
boundary, yielding exactly `2 * appendedTokenCount + 1` writable cells after
the relocated boundary. -/
def initialBlankReserve (tokens : List CNFToken) :
    List WorkSymbol :=
  List.replicate
    (2 * appendedTokenCount tokens - 1)
    WorkSymbol.blank

theorem initialBlankReserve_length (tokens : List CNFToken) :
    (initialBlankReserve tokens).length =
      2 * appendedTokenCount tokens - 1 := by
  simp [initialBlankReserve]

def targetCells (tokens : List CNFToken) :
    List WorkSymbol :=
  LockedNAND.SourceParser.packedTokenCells
    (Source.carrierTokens tokens)

theorem targetCells_length (tokens : List CNFToken) :
    (targetCells tokens).length =
      2 * appendedTokenCount tokens := by
  rw [targetCells,
    LockedNAND.SourceParser.packedTokenCells_length,
    Source.carrierTokens_length]
  simp [appendedTokenCount]

def entryPadding (tokens : List CNFToken) :
    List WorkSymbol :=
  RawFramer.cellBlank :: RawFramer.cellBlank ::
    initialBlankReserve tokens

theorem entryPadding_eq_replicate
    (tokens : List CNFToken) :
    entryPadding tokens =
      List.replicate
        (2 * appendedTokenCount tokens + 1)
        WorkSymbol.blank := by
  unfold entryPadding initialBlankReserve
  have arithmetic :
      2 * appendedTokenCount tokens + 1 =
        2 + (2 * appendedTokenCount tokens - 1) := by
    unfold appendedTokenCount
    omega
  rw [arithmetic]
  let count := 2 * appendedTokenCount tokens - 1
  change
    WorkSymbol.blank :: WorkSymbol.blank ::
        List.replicate count WorkSymbol.blank =
      List.replicate (2 + count) WorkSymbol.blank
  rw [show 2 + count = (count + 1) + 1 by omega,
    List.replicate_succ, List.replicate_succ]

def entryTape (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  (LockedNAND.TargetEmitter.configAtWord
    RawFramer.State.first outsideLeft
    (cnfTokenWorkSymbols tokens ++
      RawFramer.formulaPad ::
        (entryPadding tokens ++ outsideRight))).tape

def entryConfiguration (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := machine.startState
    tape := entryTape tokens outsideLeft outsideRight }

def finalTape (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) : WorkTape :=
  BoundaryCleanup.finalTape
    (cnfTokenWorkSymbols tokens) (targetCells tokens)
    outsideLeft outsideRight

def finalConfiguration (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape tokens outsideLeft outsideRight }

theorem final_output_eq (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    (encodeWorkTape
      (finalTape tokens outsideLeft outsideRight)).outputBits =
      encodeCircuit (Source.carrierCircuit tokens) := by
  rw [Source.encodeCarrier_exact]
  simpa [finalTape, BoundaryCleanup.finalTape,
    BoundaryCleanup.cellBlank,
    TargetEmitterCursorFinalizer.finalTape,
    TargetEmitterCursorFinalizer.tapeAtWord,
    targetCells, Source.carrierTokens,
    LockedNAND.SourceParser.packedTokenCells,
    LockedNAND.SourceParser.tokenCells,
    encodeWorkTape, Tape.outputBits] using
    TargetEmitterCursorFinalizer.final_output_eq
      (cnfTokenWorkSymbols tokens)
      (Source.carrierTokens tokens)
      outsideLeft outsideRight

private theorem workTapeOfSymbols_append_blanks
    (first : WorkSymbol) (rest : List WorkSymbol)
    (count : Nat) :
    WorkTape.BlankEquivalent
      (WorkTape.ofSymbols
        ((first :: rest) ++
          List.replicate count WorkSymbol.blank))
      (WorkTape.ofSymbols (first :: rest)) := by
  refine
    { head := rfl
      left := fun _ => rfl
      right := ?_ }
  intro index
  exact WorkTape.blankCellAt_append_replicate_blank
    rest count index

private theorem pack_token_pad
    (tokens : List CNFToken) :
    packWorkSymbols
        ((encodeTokenPairs tokens ++ [false]).map
          TapeSymbol.ofBool) =
      cnfTokenWorkSymbols tokens ++
        [RawFramer.formulaPad] := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest inductionHypothesis =>
      cases token <;>
        change _ :: packWorkSymbols
            ((encodeTokenPairs rest ++ [false]).map
              TapeSymbol.ofBool) =
          _ :: (cnfTokenWorkSymbols rest ++
            [RawFramer.formulaPad]) <;>
        exact congrArg (List.cons _) inductionHypothesis

theorem rawInputWorkTape_tokenPad
    (tokens : List CNFToken) :
    rawInputWorkTape
        (encodeTokenPairs tokens ++ [false]) =
      WorkTape.ofSymbols
        (cnfTokenWorkSymbols tokens ++
          [RawFramer.formulaPad]) := by
  unfold rawInputWorkTape
  rw [pack_token_pad]

/-- The materialized right-side reserve is indistinguishable from the
implicit blank extension of the canonical packed CNF input. -/
theorem entryTape_blankEquivalent_rawInput
    (tokens : List CNFToken) :
    WorkTape.BlankEquivalent
      (entryTape tokens [] [])
      (rawInputWorkTape
        (encodeTokenPairs tokens ++ [false])) := by
  rw [rawInputWorkTape_tokenPad]
  unfold entryTape
  rw [entryPadding_eq_replicate]
  cases tokens with
  | nil =>
      simpa [entryTape, cnfTokenWorkSymbols,
        RawFramer.formulaPad,
        LockedNAND.TargetEmitter.configAtWord,
        WorkTape.ofSymbols, List.append_assoc] using
        workTapeOfSymbols_append_blanks
          RawFramer.formulaPad []
          (2 * appendedTokenCount [] + 1)
  | cons token rest =>
      simpa [entryTape, cnfTokenWorkSymbols,
        LockedNAND.TargetEmitter.configAtWord,
        WorkTape.ofSymbols, List.append_assoc] using
        workTapeOfSymbols_append_blanks
          token.workSymbol
          (cnfTokenWorkSymbols rest ++
            [RawFramer.formulaPad])
          (2 * appendedTokenCount (token :: rest) + 1)

private theorem cleanedFinalTape_blankEquivalent
    (source : List WorkSymbol)
    (first : WorkSymbol) (rest : List WorkSymbol) :
    WorkTape.BlankEquivalent
      (BoundaryCleanup.finalTape
        source (first :: rest) [] [])
      (WorkTape.ofSymbols (first :: rest)) := by
  refine
    { head := rfl
      left := ?_
      right := ?_ }
  · intro index
    simpa [BoundaryCleanup.finalTape,
      BoundaryCleanup.cellBlank,
      TargetEmitterCursorFinalizer.tapeAtWord,
      WorkTape.ofSymbols] using
      WorkTape.blankCellAt_replicate_blank
        (source.length + 2) index
  · intro index
    simpa [BoundaryCleanup.finalTape,
      BoundaryCleanup.cellBlank,
      TargetEmitterCursorFinalizer.tapeAtWord,
      WorkTape.ofSymbols] using
      WorkTape.blankCellAt_append_blank rest index

/-- After terminal cleanup, both the erased source-left region and the
materialized output delimiter are blank extensions of the canonical carrier
input tape. -/
theorem finalTape_blankEquivalent_rawInput
    (tokens : List CNFToken) :
    WorkTape.BlankEquivalent
      (finalTape tokens [] [])
      (rawInputWorkTape
        (encodeCircuit (Source.carrierCircuit tokens))) := by
  rw [Source.rawInputWorkTape_encodeCarrier,
    Source.carrierCircuit_cells]
  let tailTokens : List Token :=
    [.natEnd] ++
      List.replicate tokens.length .unit ++
      [.natEnd] ++ Source.gateTokenStream tokens ++
      [.programEnd, .constantFalse,
        .outputsEnd, .instanceEnd]
  let restCells : List WorkSymbol :=
    LockedNAND.SourceParser.cell00 ::
      LockedNAND.SourceParser.packedTokenCells tailTokens
  have targetEquality :
      targetCells tokens =
        LockedNAND.SourceParser.cell00 :: restCells := by
    rfl
  change
    WorkTape.BlankEquivalent
      (BoundaryCleanup.finalTape
        (cnfTokenWorkSymbols tokens)
        (targetCells tokens) [] [])
      (WorkTape.ofSymbols (targetCells tokens))
  rw [targetEquality]
  exact cleanedFinalTape_blankEquivalent
    (cnfTokenWorkSymbols tokens)
    LockedNAND.SourceParser.cell00 restCells

def appenderWorkSum (tokens : List CNFToken) : Nat :=
  let count := appendedTokenCount tokens
  count * (2 * tokens.length + 6) +
    2 * count * (count - 1)

/-- A closed quadratic charge for preparation, both cursor passes, every
literal token append, both rewinds, branch bridges, and final cleanup. -/
def plannedWorkSteps (tokens : List CNFToken) : Nat :=
  appenderWorkSum tokens +
    2 * tokens.length * tokens.length +
    29 * tokens.length + 33

def workPolynomial : NatPolynomial :=
  let count :=
    .add (.mul (.constant 4) .variable) (.constant 7)
  .add
    (.add
      (.add
        (.mul count
          (.add (.mul (.constant 2) .variable)
            (.constant 6)))
        (.mul (.constant 2) (.mul count count)))
      (.add
        (.mul (.constant 2)
          (.mul .variable .variable))
        (.add (.mul (.constant 29) .variable)
          (.constant 33))))
    (.add
      (.mul (.constant 22)
        (.mul .variable .variable))
      (.add (.mul (.constant 18) .variable)
        (.constant 6)))

theorem workPolynomial_evaluated (size : Nat) :
    workPolynomial.eval size =
      let count := 4 * size + 7
      (count * (2 * size + 6) +
          2 * count * count) +
        (2 * size * size + 29 * size + 33) +
      (22 * size * size + 18 * size + 6) := by
  simp only [workPolynomial, NatPolynomial.eval_add,
    NatPolynomial.eval_mul, NatPolynomial.eval_constant,
    NatPolynomial.eval_variable]
  simp [Nat.mul_assoc, Nat.add_assoc]

theorem plannedWorkSteps_polynomial_bound
    (tokens : List CNFToken) :
    plannedWorkSteps tokens ≤
      workPolynomial.eval tokens.length := by
  unfold plannedWorkSteps appenderWorkSum appendedTokenCount
  rw [workPolynomial_evaluated]
  let count := 4 * tokens.length + 7
  have subBound : count - 1 ≤ count :=
    Nat.sub_le count 1
  have productBound :
      2 * count * (count - 1) ≤
        2 * count * count :=
    Nat.mul_le_mul_left (2 * count) subBound
  have combined := Nat.add_le_add_right
    (Nat.add_le_add_left productBound
      (count * (2 * tokens.length + 6)))
    (2 * tokens.length * tokens.length +
      29 * tokens.length + 33)
  have widened :=
    Nat.le_trans combined
      (Nat.le_add_right
        ((count * (2 * tokens.length + 6) +
            2 * count * count) +
          (2 * tokens.length * tokens.length +
            29 * tokens.length + 33))
        (22 * tokens.length * tokens.length +
          18 * tokens.length + 6))
  simpa [count, Nat.add_assoc] using widened

private theorem prepareNode_member :
    prepareNode ∈ graph.nodes := by
  simp [graph, nodes, prefixNodes]

private theorem framerNode_member :
    framerNode ∈ graph.nodes := by
  simp [graph, nodes, prefixNodes]

/-- The carrier format requires at least one packed CNF token.  An empty
source reaches the graph's global reject endpoint after the local rejection
and its literal bridge, without changing the tape. -/
theorem empty_rejects
    (outsideLeft outsideRight : List WorkSymbol) :
    workRunExact? machine 2
        (entryConfiguration [] outsideLeft outsideRight) =
      some
        { state := machine.rejectState
          tape := entryTape [] outsideLeft outsideRight } := by
  let tape := entryTape [] outsideLeft outsideRight
  have localRun :
      WorkMachineProgramPath.LocalRejectRun
        framerNode 1 tape tape := by
    change
      workRunExact? RawFramer.machine 1
          { state := RawFramer.State.first, tape := tape } =
        some
          { state := RawFramer.State.reject, tape := tape }
    subst tape
    rfl
  have path :
      WorkMachineProgramPath.AcceptPath graph
        (.node graph.entry) .reject 2 tape tape := by
    have constructed :=
      WorkMachineProgramPath.AcceptPath.stepReject
        (graph := graph) framerNode .reject 1 0
        tape tape tape framerNode_member localRun
        (WorkMachineProgramPath.AcceptPath.terminal
          (graph := graph) .reject tape)
    simpa [graph, framerRef, framerNode, controlRef,
      controlNode, Node.reference] using constructed
  simpa [entryConfiguration, tape, machine] using
    WorkMachineProgramPath.runEntryToReject
      graph 2 tape tape graph_wellFormed path

/-! ### Internal exact-path assembly -/

private theorem token_mem_order (token : CNFToken) :
    token ∈ cnfTokenOrder := by
  cases token <;> simp [cnfTokenOrder]

private theorem prefixNode_member
    {node : Node} (member : node ∈ prefixNodes) :
    node ∈ graph.nodes := by
  change node ∈ nodes
  simp only [nodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl member))

private theorem countNode_member
    {node : Node} (member : node ∈ countNodes) :
    node ∈ graph.nodes := by
  change node ∈ nodes
  simp only [nodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inr member))

private theorem gateNode_member
    {node : Node} (member : node ∈ gateNodes) :
    node ∈ graph.nodes := by
  change node ∈ nodes
  simp only [nodes, List.mem_append]
  exact Or.inl (Or.inr member)

private theorem suffixNode_member
    {node : Node} (member : node ∈ suffixNodes) :
    node ∈ graph.nodes := by
  change node ∈ nodes
  simp only [nodes, List.mem_append]
  exact Or.inr member

private theorem headerVersionNode_member :
    headerVersionNode ∈ graph.nodes := by
  apply prefixNode_member
  simp only [prefixNodes, List.mem_cons,
    List.not_mem_nil, or_false]
  exact Or.inr (Or.inr (Or.inl True.intro))

private theorem headerInputEndNode_member :
    headerInputEndNode ∈ graph.nodes := by
  apply prefixNode_member
  simp only [prefixNodes, List.mem_cons,
    List.not_mem_nil, or_false]
  exact Or.inr (Or.inr (Or.inr True.intro))

private theorem countMatchNode_member (token : CNFToken) :
    countMatchNode token ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (List.mem_map.mpr
      ⟨token, token_mem_order token, rfl⟩)))))

private theorem countBoundaryNode_member :
    countBoundaryNode ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_singleton_self countBoundaryNode)))))

private theorem countInstallNode_member (token : CNFToken) :
    countInstallNode token ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr
    (List.mem_map.mpr
      ⟨token, token_mem_order token, rfl⟩))))

private theorem countUnitNode_member (token : CNFToken) :
    countUnitNode token ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inr
    (List.mem_map.mpr
      ⟨token, token_mem_order token, rfl⟩)))

private theorem countRestoreNode_member (token : CNFToken) :
    countRestoreNode token ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append]
  exact Or.inl (Or.inr
    (List.mem_map.mpr
      ⟨token, token_mem_order token, rfl⟩))

private theorem countRewindNode_member :
    countRewindNode ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (Or.inl True.intro)

private theorem gateCountEndNode_member :
    gateCountEndNode ∈ graph.nodes := by
  apply countNode_member
  simp only [countNodes, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false]
  exact Or.inr (Or.inr True.intro)

private theorem gateMatchNode_member (token : CNFToken) :
    gateMatchNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl (Or.inl
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩)))))))

private theorem gateBoundaryNode_member :
    gateBoundaryNode ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inl (Or.inr
      (List.mem_singleton_self gateBoundaryNode)))))))

private theorem gateInstallNode_member (token : CNFToken) :
    gateInstallNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inr
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩))))))

private theorem gateFirstNode_member (token : CNFToken) :
    gateFirstNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl
    (Or.inr
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩)))))

private theorem gateSecondNode_member (token : CNFToken) :
    gateSecondNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl (Or.inl
    (Or.inr
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩))))

private theorem gateEndNode_member (token : CNFToken) :
    gateEndNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl (Or.inl
    (Or.inr
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩)))

private theorem gateRestoreNode_member (token : CNFToken) :
    gateRestoreNode token ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inl
    (Or.inr
      (List.mem_map.mpr
        ⟨token, token_mem_order token, rfl⟩))

private theorem gateRewindNode_member :
    gateRewindNode ∈ graph.nodes := by
  apply gateNode_member
  simp only [gateNodes, List.mem_append]
  exact Or.inr (List.mem_singleton_self gateRewindNode)

private theorem suffixProgramEndNode_member :
    suffixProgramEndNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem suffixOutputNode_member :
    suffixOutputNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem suffixOutputsEndNode_member :
    suffixOutputsEndNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem suffixInstanceEndNode_member :
    suffixInstanceEndNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem finalizerNode_member :
    finalizerNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem cleanupNode_member :
    cleanupNode ∈ graph.nodes := by
  apply suffixNode_member
  simp [suffixNodes]

private theorem node_accept_path
    (node : Node) (member : node ∈ graph.nodes)
    (localSteps : Nat)
    (initialTape finalTape : WorkTape)
    (localRun :
      WorkMachineProgramPath.LocalAcceptRun node
        localSteps initialTape finalTape) :
    WorkMachineProgramPath.AcceptPath graph
      (.node node.reference) node.onAccept
      (localSteps + 1) initialTape finalTape := by
  have path :=
    WorkMachineProgramPath.AcceptPath.step
      (graph := graph) node node.onAccept
      localSteps 0 initialTape finalTape finalTape
      member localRun
      (WorkMachineProgramPath.AcceptPath.terminal
        (graph := graph) node.onAccept finalTape)
  simpa using path

private theorem node_reject_path
    (node : Node) (member : node ∈ graph.nodes)
    (localSteps : Nat)
    (initialTape finalTape : WorkTape)
    (localRun :
      WorkMachineProgramPath.LocalRejectRun node
        localSteps initialTape finalTape) :
    WorkMachineProgramPath.AcceptPath graph
      (.node node.reference) node.onReject
      (localSteps + 1) initialTape finalTape := by
  have path :=
    WorkMachineProgramPath.AcceptPath.stepReject
      (graph := graph) node node.onReject
      localSteps 0 initialTape finalTape finalTape
      member localRun
      (WorkMachineProgramPath.AcceptPath.terminal
        (graph := graph) node.onReject finalTape)
  simpa using path

def dispatchSteps (token : CNFToken) : Nat :=
  2 * (tokenCode token + 1)

private theorem sourceSymbol_injective :
    Function.Injective sourceSymbol := by
  intro left right equality
  cases left <;> cases right <;>
    simp [sourceSymbol, CNFToken.workSymbol,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne] at equality ⊢

private def appendOutside
    (remaining : List Token)
    (outsideRight : List WorkSymbol) :
    List WorkSymbol :=
  List.replicate (2 * remaining.length)
      WorkSymbol.blank ++ outsideRight

private def appendReserve
    (remaining : List Token)
    (outsideRight : List WorkSymbol) :
    List WorkSymbol :=
  List.replicate (2 * remaining.length + 1)
      WorkSymbol.blank ++ outsideRight

private theorem appendReserve_cons
    (token : Token) (remaining : List Token)
    (outsideRight : List WorkSymbol) :
    appendReserve (token :: remaining) outsideRight =
      WorkSymbol.blank :: WorkSymbol.blank ::
        WorkSymbol.blank ::
          appendOutside remaining outsideRight := by
  unfold appendReserve appendOutside
  simp only [List.length_cons]
  have countEq :
      2 * (remaining.length + 1) + 1 =
        3 + 2 * remaining.length := by
    omega
  rw [countEq, ← List.replicate_append_replicate]
  rfl

private theorem appendReserve_after
    (remaining : List Token)
    (outsideRight : List WorkSymbol) :
    WorkSymbol.blank ::
        appendOutside remaining outsideRight =
      appendReserve remaining outsideRight := by
  unfold appendOutside appendReserve
  have countEq :
      2 * remaining.length + 1 =
        1 + 2 * remaining.length := by
    omega
  rw [countEq, ← List.replicate_append_replicate]
  rfl

private theorem packedTokenCells_append_single
    (emitted : List Token) (token : Token) :
    LockedNAND.SourceParser.packedTokenCells
        (emitted ++ [token]) =
      LockedNAND.SourceParser.packedTokenCells emitted ++
        LockedNAND.TargetEmitter.tokenSymbols token := by
  induction emitted with
  | nil =>
      simp [LockedNAND.SourceParser.packedTokenCells,
        LockedNAND.TargetEmitter.tokenSymbols_eq_parser_cells]
  | cons head rest inductionHypothesis =>
      simp only [List.cons_append,
        LockedNAND.SourceParser.packedTokenCells]
      rw [inductionHypothesis, List.append_assoc]

private theorem sourceCells_packed
    (tokens : List CNFToken) :
    ∀ symbol, symbol ∈ cnfTokenWorkSymbols tokens →
      LockedNAND.TargetEmitter.PackedSymbol symbol := by
  intro symbol member
  induction tokens with
  | nil =>
      contradiction
  | cons token rest inductionHypothesis =>
      simp only [cnfTokenWorkSymbols, List.mem_cons] at member
      rcases member with equality | restMember
      · subst symbol
        exact sourceSymbol_packed token
      · exact inductionHypothesis restMember

private def scanTape
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  (LockedNAND.TargetEmitter.configAtWord 0
    (before.reverse ++
      Prepare.sourceLeftBoundary :: outsideLeft)
    (after ++ Prepare.sourceTargetBoundary ::
      LockedNAND.SourceParser.packedTokenCells emitted ++
        appendReserve remaining outsideRight)).tape

private def markedTape
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  (LockedNAND.TargetEmitter.configAtWord 0
    (Prepare.sourceLeftBoundary :: outsideLeft)
    (before ++ TargetEmitterCursorControl.cursorMark ::
      after ++ Prepare.sourceTargetBoundary ::
        LockedNAND.SourceParser.packedTokenCells emitted ++
          appendReserve remaining outsideRight)).tape

private theorem configAtWord_tape_eta
    (state displayState : Nat)
    (left word : List WorkSymbol) :
    { state := state
      tape :=
        (LockedNAND.TargetEmitter.configAtWord
          displayState left word).tape } =
      LockedNAND.TargetEmitter.configAtWord
        state left word := by
  cases word <;> rfl

private theorem cursorControl_configAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    TargetEmitterCursorControl.configAtWord state left word =
      LockedNAND.TargetEmitter.configAtWord state left word := by
  cases word <;> rfl

private theorem cursorFinalizer_configurationAtWord_eq
    (state : Nat) (left word : List WorkSymbol) :
    TargetEmitterCursorFinalizer.configurationAtWord
        state left word =
      LockedNAND.TargetEmitter.configAtWord
        state left word := by
  cases word <;> rfl

private theorem plain_append_exact
    (token : Token) (source : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact?
        (TargetEmitterCursorAppender.machineFor token)
        (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted))
        { state :=
            (TargetEmitterCursorAppender.machineFor token).startState
          tape :=
            scanTape [] source emitted
              (token :: remaining) outsideLeft outsideRight } =
      some
        { state :=
            (TargetEmitterCursorAppender.machineFor token).acceptState
          tape :=
            scanTape [] source (emitted ++ [token])
              remaining outsideLeft outsideRight } := by
  have exactRun :=
    TargetEmitterCursorAppender.append_exact token source
      (LockedNAND.SourceParser.packedTokenCells emitted)
      outsideLeft (appendOutside remaining outsideRight)
      (fun symbol member =>
        TargetEmitterCursorAppender.SourceSymbol.packed
          (sourcePacked symbol member))
      (LockedNAND.TargetEmitter.packedTokenCells_packed emitted)
  simpa [TargetEmitterCursorAppender.machineFor,
    TargetEmitterCursorAppender.appendEntry,
    TargetEmitterCursorAppender.appendFinal,
    TargetEmitterCursorAppender.sourceLeftBoundary,
    TargetEmitterCursorAppender.sourceTargetBoundary,
    Prepare.sourceLeftBoundary,
    Prepare.sourceTargetBoundary,
    configAtWord_tape_eta,
    scanTape, appendReserve_cons, appendReserve_after,
    packedTokenCells_append_single, List.append_assoc] using
    exactRun

private theorem marked_append_exact
    (token : Token)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈
            TargetEmitterCursorAppender.originalSource
              before original after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact?
        (TargetEmitterCursorAppender.machineFor token)
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted))
        { state :=
            (TargetEmitterCursorAppender.machineFor token).startState
          tape :=
            markedTape before after emitted
              (token :: remaining) outsideLeft outsideRight } =
      some
        { state :=
            (TargetEmitterCursorAppender.machineFor token).acceptState
          tape :=
            markedTape before after (emitted ++ [token])
              remaining outsideLeft outsideRight } := by
  have exactRun :=
    TargetEmitterCursorAppender.append_split_exact token
      before original after
      (LockedNAND.SourceParser.packedTokenCells emitted)
      outsideLeft (appendOutside remaining outsideRight)
      sourcePacked
      (LockedNAND.TargetEmitter.packedTokenCells_packed emitted)
  simpa [TargetEmitterCursorAppender.machineFor,
    TargetEmitterCursorAppender.entryConfiguration,
    TargetEmitterCursorAppender.finalConfiguration,
    TargetEmitterCursorAppender.appendEntry,
    TargetEmitterCursorAppender.appendFinal,
    TargetEmitterCursorAppender.sourceWithCursor,
    TargetEmitterCursorControl.cursorMark,
    TargetEmitterCursorAppender.cursorMarker,
    TargetEmitterCursorAppender.sourceLeftBoundary,
    TargetEmitterCursorAppender.sourceTargetBoundary,
    Prepare.sourceLeftBoundary,
    Prepare.sourceTargetBoundary,
    configAtWord_tape_eta,
    markedTape, appendReserve_cons, appendReserve_after,
    packedTokenCells_append_single, List.append_assoc] using
    exactRun

private theorem install_cursor_exact
    (original : WorkSymbol)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (ordinary :
      LockedNAND.TargetEmitter.PackedSymbol original)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact?
        (TargetEmitterCursorControl.installMachine original)
        (before.length + 2)
        { state :=
            (TargetEmitterCursorControl.installMachine
              original).startState
          tape :=
            scanTape before (original :: after)
              emitted remaining outsideLeft outsideRight } =
      some
        { state :=
            (TargetEmitterCursorControl.installMachine
              original).acceptState
          tape :=
            markedTape before after emitted remaining
              outsideLeft outsideRight } := by
  have exactRun :=
    TargetEmitterCursorControl.install_exact original
      before after outsideLeft
      (Prepare.sourceTargetBoundary ::
        LockedNAND.SourceParser.packedTokenCells emitted ++
          appendReserve remaining outsideRight)
      ordinary beforePacked
  simpa [TargetEmitterCursorControl.installMachine,
    Prepare.sourceLeftBoundary,
    scanTape, markedTape, configAtWord_tape_eta,
    cursorControl_configAtWord_eq,
    List.append_assoc] using exactRun

private theorem restore_cursor_exact
    (original : WorkSymbol)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    workRunExact?
        (TargetEmitterCursorControl.restoreMachine original)
        (before.length + 1)
        { state :=
            (TargetEmitterCursorControl.restoreMachine
              original).startState
          tape :=
            markedTape before after emitted remaining
              outsideLeft outsideRight } =
      some
        { state :=
            (TargetEmitterCursorControl.restoreMachine
              original).acceptState
          tape :=
            scanTape (before ++ [original]) after
              emitted remaining outsideLeft outsideRight } := by
  have exactRun :=
    TargetEmitterCursorControl.restore_exact original
      before
      (after ++ Prepare.sourceTargetBoundary ::
        LockedNAND.SourceParser.packedTokenCells emitted ++
          appendReserve remaining outsideRight)
      outsideLeft beforePacked
  simpa [TargetEmitterCursorControl.restoreMachine,
    Prepare.sourceLeftBoundary,
    scanTape, markedTape, configAtWord_tape_eta,
    cursorControl_configAtWord_eq,
    List.reverse_append, List.append_assoc] using exactRun

private theorem count_match_accept_path
    (token : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol token) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef token))
      (.node (countInstallRef token))
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (countMatchNode token) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countMatchNode, controlNode, Match.machine] using
      Match.accepts_exact (sourceSymbol token) tape head
  simpa [countMatchNode, countMatchRef,
    countInstallRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (countMatchNode token)
      (countMatchNode_member token) 1 tape tape localRun

private theorem count_match_reject_path
    (expected actual : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol actual)
    (different : actual ≠ expected) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef expected))
      (.node (nextCountMatchRef expected))
      2 tape tape := by
  have symbolDifferent :
      sourceSymbol actual ≠ sourceSymbol expected := by
    intro equality
    exact different (sourceSymbol_injective equality)
  have localRun :
      WorkMachineProgramPath.LocalRejectRun
        (countMatchNode expected) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalRejectRun,
      countMatchNode, controlNode, Match.machine] using
      Match.rejects_exact
        (sourceSymbol expected) (sourceSymbol actual)
        tape head symbolDifferent
  simpa [countMatchNode, countMatchRef,
    nextCountMatchRef, controlNode, controlRef,
    Node.reference] using
    node_reject_path (countMatchNode expected)
      (countMatchNode_member expected) 1 tape tape localRun

private theorem count_dispatch_path
    (token : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol token) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef .f))
      (.node (countInstallRef token))
      (dispatchSteps token) tape tape := by
  cases token with
  | f =>
      simpa [dispatchSteps, tokenCode] using
        count_match_accept_path .f tape head
  | sep =>
      have first :=
        count_match_reject_path .f .sep tape head (by decide)
      have second :=
        count_match_accept_path .sep tape head
      simpa [dispatchSteps, tokenCode,
        nextCountMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .sep))
          (.node (countInstallRef .sep))
          2 2 tape tape tape first second
  | finish =>
      have first :=
        count_match_reject_path .f .finish tape head (by decide)
      have second :=
        count_match_reject_path .sep .finish tape head (by decide)
      have third :=
        count_match_accept_path .finish tape head
      have firstTwo :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .sep))
          (.node (countMatchRef .finish))
          2 2 tape tape tape first second
      simpa [dispatchSteps, tokenCode,
        nextCountMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .finish))
          (.node (countInstallRef .finish))
          4 2 tape tape tape firstTwo third
  | t =>
      have first :=
        count_match_reject_path .f .t tape head (by decide)
      have second :=
        count_match_reject_path .sep .t tape head (by decide)
      have third :=
        count_match_reject_path .finish .t tape head (by decide)
      have fourth :=
        count_match_accept_path .t tape head
      have firstTwo :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .sep))
          (.node (countMatchRef .finish))
          2 2 tape tape tape first second
      have firstThree :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .finish))
          (.node (countMatchRef .t))
          4 2 tape tape tape firstTwo third
      simpa [dispatchSteps, tokenCode,
        nextCountMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .t))
          (.node (countInstallRef .t))
          6 2 tape tape tape firstThree fourth

private theorem count_install_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countInstallRef token))
      (.node (countUnitRef token))
      ((before.length + 2) + 1)
      (scanTape before (sourceSymbol token :: after)
        emitted remaining outsideLeft outsideRight)
      (markedTape before after emitted remaining
        outsideLeft outsideRight) := by
  have ordinary :
      LockedNAND.TargetEmitter.PackedSymbol
        (sourceSymbol token) :=
    sourcePacked (sourceSymbol token)
      (List.mem_append.mpr
        (Or.inr (List.Mem.head after)))
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact sourcePacked symbol
      (List.mem_append.mpr (Or.inl member))
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (countInstallNode token) (before.length + 2)
        (scanTape before (sourceSymbol token :: after)
          emitted remaining outsideLeft outsideRight)
        (markedTape before after emitted remaining
          outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countInstallNode, controlNode] using
      install_cursor_exact (sourceSymbol token)
        before after emitted remaining
        outsideLeft outsideRight ordinary beforePacked
  simpa [countInstallNode, countInstallRef,
    countUnitRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (countInstallNode token)
      (countInstallNode_member token)
      (before.length + 2) _ _ localRun

private theorem count_unit_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countUnitRef token))
      (.node (countRestoreRef token))
      (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (markedTape before after emitted
        (.unit :: remaining) outsideLeft outsideRight)
      (markedTape before after (emitted ++ [.unit])
        remaining outsideLeft outsideRight) := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (countUnitNode token)
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted))
        (markedTape before after emitted
          (.unit :: remaining) outsideLeft outsideRight)
        (markedTape before after (emitted ++ [.unit])
          remaining outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countUnitNode, controlNode] using
      marked_append_exact .unit before (sourceSymbol token)
        after emitted remaining outsideLeft outsideRight
        (by
          simpa [TargetEmitterCursorAppender.originalSource] using
            sourcePacked)
  simpa [countUnitNode, countUnitRef,
    countRestoreRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (countUnitNode token)
      (countUnitNode_member token)
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells emitted))
      _ _ localRun

private theorem count_restore_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countRestoreRef token))
      (.node (countMatchRef .f))
      ((before.length + 1) + 1)
      (markedTape before after emitted remaining
        outsideLeft outsideRight)
      (scanTape (before ++ [sourceSymbol token]) after
        emitted remaining outsideLeft outsideRight) := by
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact sourcePacked symbol
      (List.mem_append.mpr (Or.inl member))
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (countRestoreNode token) (before.length + 1)
        (markedTape before after emitted remaining
          outsideLeft outsideRight)
        (scanTape (before ++ [sourceSymbol token]) after
          emitted remaining outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countRestoreNode, controlNode] using
      restore_cursor_exact (sourceSymbol token)
        before after emitted remaining
        outsideLeft outsideRight beforePacked
  simpa [countRestoreNode, countRestoreRef,
    countMatchRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (countRestoreNode token)
      (countRestoreNode_member token)
      (before.length + 1) _ _ localRun

private def countItemSteps
    (token : CNFToken) (before after : List WorkSymbol)
    (emitted : List Token) : Nat :=
  dispatchSteps token +
    ((before.length + 2) + 1) +
    (TargetEmitterCursorAppender.workSteps before after
      (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
    ((before.length + 1) + 1)

private theorem count_item_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef .f))
      (.node (countMatchRef .f))
      (countItemSteps token before after emitted)
      (scanTape before (sourceSymbol token :: after)
        emitted (.unit :: remaining) outsideLeft outsideRight)
      (scanTape (before ++ [sourceSymbol token]) after
        (emitted ++ [.unit]) remaining outsideLeft outsideRight) := by
  let initialTape :=
    scanTape before (sourceSymbol token :: after)
      emitted (.unit :: remaining) outsideLeft outsideRight
  let markedBefore :=
    markedTape before after emitted (.unit :: remaining)
      outsideLeft outsideRight
  let markedAfter :=
    markedTape before after (emitted ++ [.unit]) remaining
      outsideLeft outsideRight
  let finalTape :=
    scanTape (before ++ [sourceSymbol token]) after
      (emitted ++ [.unit]) remaining outsideLeft outsideRight
  have dispatch :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countMatchRef .f))
        (.node (countInstallRef token))
        (dispatchSteps token) initialTape initialTape := by
    apply count_dispatch_path token initialTape
    simp [initialTape, scanTape,
      LockedNAND.TargetEmitter.configAtWord]
  have install :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countInstallRef token))
        (.node (countUnitRef token))
        ((before.length + 2) + 1)
        initialTape markedBefore := by
    simpa [initialTape, markedBefore] using
      count_install_path token before after emitted
        (.unit :: remaining) outsideLeft outsideRight
        sourcePacked
  have append :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countUnitRef token))
        (.node (countRestoreRef token))
        (TargetEmitterCursorAppender.workSteps before after
            (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
        markedBefore markedAfter := by
    simpa [markedBefore, markedAfter] using
      count_unit_path token before after emitted remaining
        outsideLeft outsideRight sourcePacked
  have restore :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countRestoreRef token))
        (.node (countMatchRef .f))
        ((before.length + 1) + 1)
        markedAfter finalTape := by
    simpa [markedAfter, finalTape] using
      count_restore_path token before after
        (emitted ++ [.unit]) remaining
        outsideLeft outsideRight sourcePacked
  have throughInstall :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countInstallRef token))
      (.node (countUnitRef token))
      (dispatchSteps token) ((before.length + 2) + 1)
      initialTape initialTape markedBefore dispatch install
  have throughAppend :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countUnitRef token))
      (.node (countRestoreRef token))
      (dispatchSteps token + ((before.length + 2) + 1))
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      initialTape markedBefore markedAfter
      throughInstall append
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countRestoreRef token))
      (.node (countMatchRef .f))
      (dispatchSteps token + ((before.length + 2) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1))
      ((before.length + 1) + 1)
      initialTape markedAfter finalTape throughAppend restore
  simpa [countItemSteps, initialTape, finalTape,
    Nat.add_assoc] using all

private def countPassSteps :
    List WorkSymbol → List CNFToken → List Token → Nat
  | _, [], _ => 0
  | before, token :: rest, emitted =>
      countItemSteps token before
          (cnfTokenWorkSymbols rest) emitted +
        countPassSteps
          (before ++ [sourceSymbol token]) rest
          (emitted ++ [.unit])

private theorem count_pass_path
    (before : List WorkSymbol) (tokens : List CNFToken)
    (emitted tailSchedule : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ cnfTokenWorkSymbols tokens →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef .f))
      (.node (countMatchRef .f))
      (countPassSteps before tokens emitted)
      (scanTape before (cnfTokenWorkSymbols tokens)
        emitted
        (List.replicate tokens.length .unit ++ tailSchedule)
        outsideLeft outsideRight)
      (scanTape
        (before ++ cnfTokenWorkSymbols tokens) []
        (emitted ++ List.replicate tokens.length .unit)
        tailSchedule outsideLeft outsideRight) := by
  induction tokens generalizing before emitted with
  | nil =>
      simpa [countPassSteps, cnfTokenWorkSymbols] using
        (WorkMachineProgramPath.AcceptPath.terminal
          (graph := graph) (.node (countMatchRef .f))
          (scanTape before [] emitted tailSchedule
            outsideLeft outsideRight))
  | cons token rest inductionHypothesis =>
      let after := cnfTokenWorkSymbols rest
      let emittedAfter := emitted ++ [.unit]
      let beforeAfter := before ++ [sourceSymbol token]
      let remaining :=
        List.replicate rest.length .unit ++ tailSchedule
      let middleTape :=
        scanTape beforeAfter after emittedAfter remaining
          outsideLeft outsideRight
      have itemPacked :
          ∀ symbol,
            symbol ∈ before ++ sourceSymbol token :: after →
              LockedNAND.TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact sourcePacked symbol (by
          simpa [after, cnfTokenWorkSymbols,
            sourceSymbol] using member)
      have tailPacked :
          ∀ symbol,
            symbol ∈ beforeAfter ++ cnfTokenWorkSymbols rest →
              LockedNAND.TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact sourcePacked symbol (by
          simpa [beforeAfter, cnfTokenWorkSymbols,
            sourceSymbol, List.append_assoc] using member)
      have first :=
        count_item_path token before after emitted remaining
          outsideLeft outsideRight itemPacked
      have tail :=
        inductionHypothesis beforeAfter emittedAfter tailPacked
      have combined :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (countMatchRef .f))
          (.node (countMatchRef .f))
          (.node (countMatchRef .f))
          (countItemSteps token before after emitted)
          (countPassSteps beforeAfter rest emittedAfter)
          (scanTape before
            (sourceSymbol token :: after) emitted
            (.unit :: remaining) outsideLeft outsideRight)
          middleTape
          (scanTape
            (beforeAfter ++ cnfTokenWorkSymbols rest) []
            (emittedAfter ++
              List.replicate rest.length .unit)
            tailSchedule outsideLeft outsideRight)
          (by simpa [after, beforeAfter, emittedAfter,
              remaining, middleTape] using first)
          (by simpa [beforeAfter, emittedAfter,
              remaining, middleTape] using tail)
      simpa [countPassSteps, after, beforeAfter,
        emittedAfter, remaining, cnfTokenWorkSymbols,
        sourceSymbol, List.replicate_succ,
        List.append_assoc] using combined

private theorem plain_control_appender_path
    (name : Nat) (token : Token) (continuation : Endpoint)
    (member :
      controlNode name
          (TargetEmitterCursorAppender.machineFor token)
          continuation .reject ∈ graph.nodes)
    (source : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node
        (controlRef name
          (TargetEmitterCursorAppender.machineFor token)))
      continuation
      (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (scanTape [] source emitted
        (token :: remaining) outsideLeft outsideRight)
      (scanTape [] source (emitted ++ [token])
        remaining outsideLeft outsideRight) := by
  let node :=
    controlNode name
      (TargetEmitterCursorAppender.machineFor token)
      continuation .reject
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun node
        (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted))
        (scanTape [] source emitted
          (token :: remaining) outsideLeft outsideRight)
        (scanTape [] source (emitted ++ [token])
          remaining outsideLeft outsideRight) := by
    simpa [node, WorkMachineProgramPath.LocalAcceptRun,
      controlNode] using
      plain_append_exact token source emitted remaining
        outsideLeft outsideRight sourcePacked
  simpa [node, controlNode, controlRef,
    Node.reference] using
    node_accept_path node member
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells emitted))
      _ _ localRun

private theorem boundary_ne_sourceSymbol
    (token : CNFToken) :
    Prepare.sourceTargetBoundary ≠ sourceSymbol token := by
  cases token <;>
    decide

private theorem count_match_boundary_reject_path
    (expected : CNFToken) (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef expected))
      (.node (nextCountMatchRef expected))
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalRejectRun
        (countMatchNode expected) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalRejectRun,
      countMatchNode, controlNode, Match.machine] using
      Match.rejects_exact
        (sourceSymbol expected)
        Prepare.sourceTargetBoundary tape head
        (boundary_ne_sourceSymbol expected)
  simpa [countMatchNode, countMatchRef,
    nextCountMatchRef, controlNode, controlRef,
    Node.reference] using
    node_reject_path (countMatchNode expected)
      (countMatchNode_member expected) 1 tape tape localRun

private theorem count_boundary_accept_path
    (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node countBoundaryRef)
      (.node countRewindRef)
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        countBoundaryNode 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countBoundaryNode, controlNode, Match.machine] using
      Match.accepts_exact
        Prepare.sourceTargetBoundary tape head
  simpa [countBoundaryNode, countBoundaryRef,
    countRewindRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path countBoundaryNode
      countBoundaryNode_member 1 tape tape localRun

private theorem count_boundary_dispatch_path
    (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef .f))
      (.node countRewindRef)
      10 tape tape := by
  have first :=
    count_match_boundary_reject_path .f tape head
  have second :=
    count_match_boundary_reject_path .sep tape head
  have third :=
    count_match_boundary_reject_path .finish tape head
  have fourth :=
    count_match_boundary_reject_path .t tape head
  have fifth :=
    count_boundary_accept_path tape head
  have firstTwo :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countMatchRef .sep))
      (.node (countMatchRef .finish))
      2 2 tape tape tape first second
  have firstThree :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countMatchRef .finish))
      (.node (countMatchRef .t))
      4 2 tape tape tape firstTwo third
  have firstFour :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countMatchRef .t))
      (.node countBoundaryRef)
      6 2 tape tape tape firstThree fourth
  simpa using
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node countBoundaryRef)
      (.node countRewindRef)
      8 2 tape tape tape firstFour fifth

private theorem count_rewind_path
    (first : CNFToken) (rest : List CNFToken)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node countRewindRef)
      (.node gateCountEndRef)
      (Rewind.workSteps tokens + 1)
      (scanTape source [] emitted remaining
        outsideLeft outsideRight)
      (scanTape [] source emitted remaining
        outsideLeft outsideRight) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        countRewindNode (Rewind.workSteps tokens)
        (scanTape source [] emitted remaining
          outsideLeft outsideRight)
        (scanTape [] source emitted remaining
          outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      countRewindNode, controlNode, scanTape,
      configAtWord_tape_eta, Rewind.machine,
      Rewind.sourceLeftBoundary,
      Rewind.sourceTargetBoundary,
      Prepare.sourceLeftBoundary,
      Prepare.sourceTargetBoundary,
      List.append_assoc] using
      Rewind.canonical_exact first rest outsideLeft
        (LockedNAND.SourceParser.packedTokenCells emitted ++
          appendReserve remaining outsideRight)
  simpa [countRewindNode, countRewindRef,
    gateCountEndRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path countRewindNode
      countRewindNode_member (Rewind.workSteps tokens)
      _ _ localRun

private theorem gate_count_end_path
    (source : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node gateCountEndRef)
      (.node (gateMatchRef .f))
      (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (scanTape [] source emitted
        (.natEnd :: remaining) outsideLeft outsideRight)
      (scanTape [] source (emitted ++ [.natEnd])
        remaining outsideLeft outsideRight) := by
  simpa [gateCountEndNode, gateCountEndRef,
    gateMatchRef] using
    plain_control_appender_path Address.gateCountEnd
      .natEnd (.node (gateMatchRef .f))
      (by simpa [gateCountEndNode] using
        gateCountEndNode_member)
      source emitted remaining outsideLeft outsideRight
      sourcePacked

private theorem marked_control_appender_path
    (name : Nat) (request : Token) (continuation : Endpoint)
    (member :
      controlNode name
          (TargetEmitterCursorAppender.machineFor request)
          continuation .reject ∈ graph.nodes)
    (before : List WorkSymbol) (original : WorkSymbol)
    (after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈
            TargetEmitterCursorAppender.originalSource
              before original after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node
        (controlRef name
          (TargetEmitterCursorAppender.machineFor request)))
      continuation
      (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (markedTape before after emitted
        (request :: remaining) outsideLeft outsideRight)
      (markedTape before after (emitted ++ [request])
        remaining outsideLeft outsideRight) := by
  let node :=
    controlNode name
      (TargetEmitterCursorAppender.machineFor request)
      continuation .reject
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun node
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted))
        (markedTape before after emitted
          (request :: remaining) outsideLeft outsideRight)
        (markedTape before after (emitted ++ [request])
          remaining outsideLeft outsideRight) := by
    simpa [node, WorkMachineProgramPath.LocalAcceptRun,
      controlNode] using
      marked_append_exact request before original after
        emitted remaining outsideLeft outsideRight sourcePacked
  simpa [node, controlNode, controlRef,
    Node.reference] using
    node_accept_path node member
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells emitted))
      _ _ localRun

private theorem gate_match_accept_path
    (token : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol token) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef token))
      (.node (gateInstallRef token))
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (gateMatchNode token) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      gateMatchNode, controlNode, Match.machine] using
      Match.accepts_exact (sourceSymbol token) tape head
  simpa [gateMatchNode, gateMatchRef,
    gateInstallRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (gateMatchNode token)
      (gateMatchNode_member token) 1 tape tape localRun

private theorem gate_match_reject_path
    (expected actual : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol actual)
    (different : actual ≠ expected) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef expected))
      (.node (nextGateMatchRef expected))
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalRejectRun
        (gateMatchNode expected) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalRejectRun,
      gateMatchNode, controlNode, Match.machine] using
      Match.rejects_exact
        (sourceSymbol expected) (sourceSymbol actual)
        tape head
        (fun equality =>
          different (sourceSymbol_injective equality))
  simpa [gateMatchNode, gateMatchRef,
    nextGateMatchRef, controlNode, controlRef,
    Node.reference] using
    node_reject_path (gateMatchNode expected)
      (gateMatchNode_member expected) 1 tape tape localRun

private theorem gate_dispatch_path
    (token : CNFToken) (tape : WorkTape)
    (head : tape.head = sourceSymbol token) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef .f))
      (.node (gateInstallRef token))
      (dispatchSteps token) tape tape := by
  cases token with
  | f =>
      simpa [dispatchSteps, tokenCode] using
        gate_match_accept_path .f tape head
  | sep =>
      have first :=
        gate_match_reject_path .f .sep tape head (by decide)
      have second :=
        gate_match_accept_path .sep tape head
      simpa [dispatchSteps, tokenCode,
        nextGateMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .sep))
          (.node (gateInstallRef .sep))
          2 2 tape tape tape first second
  | finish =>
      have first :=
        gate_match_reject_path .f .finish tape head (by decide)
      have second :=
        gate_match_reject_path .sep .finish tape head (by decide)
      have third :=
        gate_match_accept_path .finish tape head
      have firstTwo :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .sep))
          (.node (gateMatchRef .finish))
          2 2 tape tape tape first second
      simpa [dispatchSteps, tokenCode,
        nextGateMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .finish))
          (.node (gateInstallRef .finish))
          4 2 tape tape tape firstTwo third
  | t =>
      have first :=
        gate_match_reject_path .f .t tape head (by decide)
      have second :=
        gate_match_reject_path .sep .t tape head (by decide)
      have third :=
        gate_match_reject_path .finish .t tape head (by decide)
      have fourth :=
        gate_match_accept_path .t tape head
      have firstTwo :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .sep))
          (.node (gateMatchRef .finish))
          2 2 tape tape tape first second
      have firstThree :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .finish))
          (.node (gateMatchRef .t))
          4 2 tape tape tape firstTwo third
      simpa [dispatchSteps, tokenCode,
        nextGateMatchRef] using
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .t))
          (.node (gateInstallRef .t))
          6 2 tape tape tape firstThree fourth

private theorem gate_install_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateInstallRef token))
      (.node (gateFirstRef token))
      ((before.length + 2) + 1)
      (scanTape before (sourceSymbol token :: after)
        emitted remaining outsideLeft outsideRight)
      (markedTape before after emitted remaining
        outsideLeft outsideRight) := by
  have ordinary :=
    sourcePacked (sourceSymbol token)
      (List.mem_append.mpr
        (Or.inr (List.Mem.head after)))
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact sourcePacked symbol
      (List.mem_append.mpr (Or.inl member))
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (gateInstallNode token) (before.length + 2)
        (scanTape before (sourceSymbol token :: after)
          emitted remaining outsideLeft outsideRight)
        (markedTape before after emitted remaining
          outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      gateInstallNode, controlNode] using
      install_cursor_exact (sourceSymbol token)
        before after emitted remaining outsideLeft
        outsideRight ordinary beforePacked
  simpa [gateInstallNode, gateInstallRef,
    gateFirstRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (gateInstallNode token)
      (gateInstallNode_member token)
      (before.length + 2) _ _ localRun

private theorem gate_restore_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateRestoreRef token))
      (.node (gateMatchRef .f))
      ((before.length + 1) + 1)
      (markedTape before after emitted remaining
        outsideLeft outsideRight)
      (scanTape (before ++ [sourceSymbol token]) after
        emitted remaining outsideLeft outsideRight) := by
  have beforePacked :
      ∀ symbol, symbol ∈ before →
        LockedNAND.TargetEmitter.PackedSymbol symbol := by
    intro symbol member
    exact sourcePacked symbol
      (List.mem_append.mpr (Or.inl member))
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        (gateRestoreNode token) (before.length + 1)
        (markedTape before after emitted remaining
          outsideLeft outsideRight)
        (scanTape (before ++ [sourceSymbol token]) after
          emitted remaining outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      gateRestoreNode, controlNode] using
      restore_cursor_exact (sourceSymbol token)
        before after emitted remaining outsideLeft
        outsideRight beforePacked
  simpa [gateRestoreNode, gateRestoreRef,
    gateMatchRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path (gateRestoreNode token)
      (gateRestoreNode_member token)
      (before.length + 1) _ _ localRun

private def gateItemSteps
    (token : CNFToken) (before after : List WorkSymbol)
    (emitted : List Token) : Nat :=
  let firstEmitted :=
    emitted ++ [firstConstantToken token]
  let secondEmitted :=
    firstEmitted ++ [secondConstantToken token]
  dispatchSteps token +
    ((before.length + 2) + 1) +
    (TargetEmitterCursorAppender.workSteps before after
      (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
    (TargetEmitterCursorAppender.workSteps before after
      (LockedNAND.SourceParser.packedTokenCells firstEmitted) + 1) +
    (TargetEmitterCursorAppender.workSteps before after
      (LockedNAND.SourceParser.packedTokenCells secondEmitted) + 1) +
    ((before.length + 1) + 1)

private theorem gate_item_path
    (token : CNFToken)
    (before after : List WorkSymbol)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ sourceSymbol token :: after →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef .f))
      (.node (gateMatchRef .f))
      (gateItemSteps token before after emitted)
      (scanTape before (sourceSymbol token :: after)
        emitted
        (Source.tokenGateTokens token ++ remaining)
        outsideLeft outsideRight)
      (scanTape (before ++ [sourceSymbol token]) after
        (emitted ++ Source.tokenGateTokens token)
        remaining outsideLeft outsideRight) := by
  let firstRequest := firstConstantToken token
  let secondRequest := secondConstantToken token
  let firstEmitted := emitted ++ [firstRequest]
  let secondEmitted := firstEmitted ++ [secondRequest]
  let gateEmitted := secondEmitted ++ [.gateEnd]
  let afterFirst :=
    secondRequest :: .gateEnd :: remaining
  let afterSecond := .gateEnd :: remaining
  let initialTape :=
    scanTape before (sourceSymbol token :: after)
      emitted (firstRequest :: afterFirst)
      outsideLeft outsideRight
  let installedTape :=
    markedTape before after emitted
      (firstRequest :: afterFirst) outsideLeft outsideRight
  let afterFirstTape :=
    markedTape before after firstEmitted afterFirst
      outsideLeft outsideRight
  let afterSecondTape :=
    markedTape before after secondEmitted afterSecond
      outsideLeft outsideRight
  let afterGateTape :=
    markedTape before after gateEmitted remaining
      outsideLeft outsideRight
  let finalTape :=
    scanTape (before ++ [sourceSymbol token]) after
      gateEmitted remaining outsideLeft outsideRight
  have splitPacked :
      ∀ symbol,
        symbol ∈
            TargetEmitterCursorAppender.originalSource
              before (sourceSymbol token) after →
          LockedNAND.TargetEmitter.PackedSymbol symbol := by
    simpa [TargetEmitterCursorAppender.originalSource] using
      sourcePacked
  have dispatch :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateMatchRef .f))
        (.node (gateInstallRef token))
        (dispatchSteps token) initialTape initialTape := by
    apply gate_dispatch_path token initialTape
    simp [initialTape, scanTape,
      LockedNAND.TargetEmitter.configAtWord]
  have install :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateInstallRef token))
        (.node (gateFirstRef token))
        ((before.length + 2) + 1)
        initialTape installedTape := by
    simpa [initialTape, installedTape] using
      gate_install_path token before after emitted
        (firstRequest :: afterFirst)
        outsideLeft outsideRight sourcePacked
  have firstAppend :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateFirstRef token))
        (.node (gateSecondRef token))
        (TargetEmitterCursorAppender.workSteps before after
            (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
        installedTape afterFirstTape := by
    simpa [gateFirstNode, gateFirstRef, gateSecondRef,
      firstRequest, installedTape, afterFirstTape] using
      marked_control_appender_path
        (Address.gateFirst token) firstRequest
        (.node (gateSecondRef token))
        (by simpa [gateFirstNode, firstRequest] using
          gateFirstNode_member token)
        before (sourceSymbol token) after emitted afterFirst
        outsideLeft outsideRight splitPacked
  have secondAppend :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateSecondRef token))
        (.node (gateEndRef token))
        (TargetEmitterCursorAppender.workSteps before after
            (LockedNAND.SourceParser.packedTokenCells firstEmitted) + 1)
        afterFirstTape afterSecondTape := by
    simpa [gateSecondNode, gateSecondRef, gateEndRef,
      secondRequest, afterFirstTape, afterSecondTape] using
      marked_control_appender_path
        (Address.gateSecond token) secondRequest
        (.node (gateEndRef token))
        (by simpa [gateSecondNode, secondRequest] using
          gateSecondNode_member token)
        before (sourceSymbol token) after firstEmitted afterSecond
        outsideLeft outsideRight splitPacked
  have endAppend :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateEndRef token))
        (.node (gateRestoreRef token))
        (TargetEmitterCursorAppender.workSteps before after
            (LockedNAND.SourceParser.packedTokenCells secondEmitted) + 1)
        afterSecondTape afterGateTape := by
    simpa [gateEndNode, gateEndRef, gateRestoreRef,
      afterSecondTape, afterGateTape] using
      marked_control_appender_path
        (Address.gateEnd token) .gateEnd
        (.node (gateRestoreRef token))
        (by simpa [gateEndNode] using
          gateEndNode_member token)
        before (sourceSymbol token) after secondEmitted remaining
        outsideLeft outsideRight splitPacked
  have restore :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateRestoreRef token))
        (.node (gateMatchRef .f))
        ((before.length + 1) + 1)
        afterGateTape finalTape := by
    simpa [afterGateTape, finalTape] using
      gate_restore_path token before after
        gateEmitted remaining outsideLeft outsideRight
        sourcePacked
  have throughInstall :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateInstallRef token))
      (.node (gateFirstRef token))
      (dispatchSteps token) ((before.length + 2) + 1)
      initialTape initialTape installedTape dispatch install
  have throughFirst :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateFirstRef token))
      (.node (gateSecondRef token))
      (dispatchSteps token + ((before.length + 2) + 1))
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      initialTape installedTape afterFirstTape
      throughInstall firstAppend
  have throughSecond :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateSecondRef token))
      (.node (gateEndRef token))
      (dispatchSteps token + ((before.length + 2) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1))
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells firstEmitted) + 1)
      initialTape afterFirstTape afterSecondTape
      throughFirst secondAppend
  have throughEnd :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateEndRef token))
      (.node (gateRestoreRef token))
      (dispatchSteps token + ((before.length + 2) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells firstEmitted) + 1))
      (TargetEmitterCursorAppender.workSteps before after
        (LockedNAND.SourceParser.packedTokenCells secondEmitted) + 1)
      initialTape afterSecondTape afterGateTape
      throughSecond endAppend
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateRestoreRef token))
      (.node (gateMatchRef .f))
      (dispatchSteps token + ((before.length + 2) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells firstEmitted) + 1) +
        (TargetEmitterCursorAppender.workSteps before after
          (LockedNAND.SourceParser.packedTokenCells secondEmitted) + 1))
      ((before.length + 1) + 1)
      initialTape afterGateTape finalTape throughEnd restore
  simpa [gateItemSteps, firstRequest, secondRequest,
    firstEmitted, secondEmitted, gateEmitted,
    afterFirst, afterSecond,
    firstConstantToken, secondConstantToken,
    initialTape, finalTape, Source.tokenGateTokens,
    Nat.add_assoc, List.append_assoc] using all

private def gatePassSteps :
    List WorkSymbol → List CNFToken → List Token → Nat
  | _, [], _ => 0
  | before, token :: rest, emitted =>
      gateItemSteps token before
          (cnfTokenWorkSymbols rest) emitted +
        gatePassSteps
          (before ++ [sourceSymbol token]) rest
          (emitted ++ Source.tokenGateTokens token)

private theorem gate_pass_path
    (before : List WorkSymbol) (tokens : List CNFToken)
    (emitted tailSchedule : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol,
        symbol ∈ before ++ cnfTokenWorkSymbols tokens →
          LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef .f))
      (.node (gateMatchRef .f))
      (gatePassSteps before tokens emitted)
      (scanTape before (cnfTokenWorkSymbols tokens)
        emitted
        (Source.gateTokenStream tokens ++ tailSchedule)
        outsideLeft outsideRight)
      (scanTape
        (before ++ cnfTokenWorkSymbols tokens) []
        (emitted ++ Source.gateTokenStream tokens)
        tailSchedule outsideLeft outsideRight) := by
  induction tokens generalizing before emitted with
  | nil =>
      simpa [gatePassSteps, cnfTokenWorkSymbols,
        Source.gateTokenStream] using
        (WorkMachineProgramPath.AcceptPath.terminal
          (graph := graph) (.node (gateMatchRef .f))
          (scanTape before [] emitted tailSchedule
            outsideLeft outsideRight))
  | cons token rest inductionHypothesis =>
      let after := cnfTokenWorkSymbols rest
      let emittedAfter :=
        emitted ++ Source.tokenGateTokens token
      let beforeAfter := before ++ [sourceSymbol token]
      let remaining :=
        Source.gateTokenStream rest ++ tailSchedule
      let middleTape :=
        scanTape beforeAfter after emittedAfter remaining
          outsideLeft outsideRight
      have itemPacked :
          ∀ symbol,
            symbol ∈ before ++ sourceSymbol token :: after →
              LockedNAND.TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact sourcePacked symbol (by
          simpa [after, cnfTokenWorkSymbols,
            sourceSymbol] using member)
      have tailPacked :
          ∀ symbol,
            symbol ∈ beforeAfter ++ cnfTokenWorkSymbols rest →
              LockedNAND.TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact sourcePacked symbol (by
          simpa [beforeAfter, cnfTokenWorkSymbols,
            sourceSymbol, List.append_assoc] using member)
      have first :=
        gate_item_path token before after emitted remaining
          outsideLeft outsideRight itemPacked
      have tail :=
        inductionHypothesis beforeAfter emittedAfter tailPacked
      have combined :=
        WorkMachineProgramPath.AcceptPath.trans
          graph (.node (gateMatchRef .f))
          (.node (gateMatchRef .f))
          (.node (gateMatchRef .f))
          (gateItemSteps token before after emitted)
          (gatePassSteps beforeAfter rest emittedAfter)
          (scanTape before
            (sourceSymbol token :: after) emitted
            (Source.tokenGateTokens token ++ remaining)
            outsideLeft outsideRight)
          middleTape
          (scanTape
            (beforeAfter ++ cnfTokenWorkSymbols rest) []
            (emittedAfter ++
              Source.gateTokenStream rest)
            tailSchedule outsideLeft outsideRight)
          (by simpa [after, beforeAfter, emittedAfter,
              remaining, middleTape] using first)
          (by simpa [beforeAfter, emittedAfter,
              remaining, middleTape] using tail)
      simpa [gatePassSteps, after, beforeAfter,
        emittedAfter, remaining, cnfTokenWorkSymbols,
        Source.gateTokenStream, sourceSymbol,
        List.append_assoc] using combined

private theorem gate_match_boundary_reject_path
    (expected : CNFToken) (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef expected))
      (.node (nextGateMatchRef expected))
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalRejectRun
        (gateMatchNode expected) 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalRejectRun,
      gateMatchNode, controlNode, Match.machine] using
      Match.rejects_exact
        (sourceSymbol expected)
        Prepare.sourceTargetBoundary tape head
        (boundary_ne_sourceSymbol expected)
  simpa [gateMatchNode, gateMatchRef,
    nextGateMatchRef, controlNode, controlRef,
    Node.reference] using
    node_reject_path (gateMatchNode expected)
      (gateMatchNode_member expected) 1 tape tape localRun

private theorem gate_boundary_accept_path
    (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node gateBoundaryRef)
      (.node gateRewindRef)
      2 tape tape := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        gateBoundaryNode 1 tape tape := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      gateBoundaryNode, controlNode, Match.machine] using
      Match.accepts_exact
        Prepare.sourceTargetBoundary tape head
  simpa [gateBoundaryNode, gateBoundaryRef,
    gateRewindRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path gateBoundaryNode
      gateBoundaryNode_member 1 tape tape localRun

private theorem gate_boundary_dispatch_path
    (tape : WorkTape)
    (head :
      tape.head = Prepare.sourceTargetBoundary) :
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef .f))
      (.node gateRewindRef)
      10 tape tape := by
  have first :=
    gate_match_boundary_reject_path .f tape head
  have second :=
    gate_match_boundary_reject_path .sep tape head
  have third :=
    gate_match_boundary_reject_path .finish tape head
  have fourth :=
    gate_match_boundary_reject_path .t tape head
  have fifth :=
    gate_boundary_accept_path tape head
  have firstTwo :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateMatchRef .sep))
      (.node (gateMatchRef .finish))
      2 2 tape tape tape first second
  have firstThree :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateMatchRef .finish))
      (.node (gateMatchRef .t))
      4 2 tape tape tape firstTwo third
  have firstFour :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateMatchRef .t))
      (.node gateBoundaryRef)
      6 2 tape tape tape firstThree fourth
  simpa using
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node gateBoundaryRef)
      (.node gateRewindRef)
      8 2 tape tape tape firstFour fifth

private theorem gate_rewind_path
    (first : CNFToken) (rest : List CNFToken)
    (emitted remaining : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node gateRewindRef)
      (.node suffixProgramEndRef)
      (Rewind.workSteps tokens + 1)
      (scanTape source [] emitted remaining
        outsideLeft outsideRight)
      (scanTape [] source emitted remaining
        outsideLeft outsideRight) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        gateRewindNode (Rewind.workSteps tokens)
        (scanTape source [] emitted remaining
          outsideLeft outsideRight)
        (scanTape [] source emitted remaining
          outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      gateRewindNode, controlNode, scanTape,
      configAtWord_tape_eta, Rewind.machine,
      Rewind.sourceLeftBoundary,
      Rewind.sourceTargetBoundary,
      Prepare.sourceLeftBoundary,
      Prepare.sourceTargetBoundary,
      List.append_assoc] using
      Rewind.canonical_exact first rest outsideLeft
        (LockedNAND.SourceParser.packedTokenCells emitted ++
          appendReserve remaining outsideRight)
  simpa [gateRewindNode, gateRewindRef,
    suffixProgramEndRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path gateRewindNode
      gateRewindNode_member (Rewind.workSteps tokens)
      _ _ localRun

private def fixedSuffixTokens : List Token :=
  [.programEnd, .constantFalse, .outputsEnd, .instanceEnd]

private def suffixSteps
    (source : List WorkSymbol) (emitted : List Token) : Nat :=
  let afterProgram := emitted ++ [.programEnd]
  let afterOutput := afterProgram ++ [.constantFalse]
  let afterOutputsEnd := afterOutput ++ [.outputsEnd]
  (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
    (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells afterProgram) + 1) +
    (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells afterOutput) + 1) +
    (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells afterOutputsEnd) + 1)

private theorem suffix_path
    (source : List WorkSymbol) (emitted : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node suffixProgramEndRef)
      (.node finalizerRef)
      (suffixSteps source emitted)
      (scanTape [] source emitted fixedSuffixTokens
        outsideLeft outsideRight)
      (scanTape [] source
        (emitted ++ fixedSuffixTokens) []
        outsideLeft outsideRight) := by
  let afterProgram := emitted ++ [.programEnd]
  let afterOutput := afterProgram ++ [.constantFalse]
  let afterOutputsEnd := afterOutput ++ [.outputsEnd]
  let afterInstanceEnd := afterOutputsEnd ++ [.instanceEnd]
  let firstTape :=
    scanTape [] source afterProgram
      [.constantFalse, .outputsEnd, .instanceEnd]
      outsideLeft outsideRight
  let secondTape :=
    scanTape [] source afterOutput
      [.outputsEnd, .instanceEnd]
      outsideLeft outsideRight
  let thirdTape :=
    scanTape [] source afterOutputsEnd
      [.instanceEnd] outsideLeft outsideRight
  let fourthTape :=
    scanTape [] source afterInstanceEnd []
      outsideLeft outsideRight
  have first :
      WorkMachineProgramPath.AcceptPath graph
        (.node suffixProgramEndRef)
        (.node suffixOutputRef)
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
        (scanTape [] source emitted fixedSuffixTokens
          outsideLeft outsideRight)
        firstTape := by
    simpa [suffixProgramEndNode, suffixProgramEndRef,
      suffixOutputRef, fixedSuffixTokens, firstTape,
      afterProgram] using
      plain_control_appender_path Address.suffixProgramEnd
        .programEnd (.node suffixOutputRef)
        (by simpa [suffixProgramEndNode] using
          suffixProgramEndNode_member)
        source emitted
        [.constantFalse, .outputsEnd, .instanceEnd]
        outsideLeft outsideRight sourcePacked
  have second :
      WorkMachineProgramPath.AcceptPath graph
        (.node suffixOutputRef)
        (.node suffixOutputsEndRef)
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells afterProgram) + 1)
        firstTape secondTape := by
    simpa [suffixOutputNode, suffixOutputRef,
      suffixOutputsEndRef, firstTape, secondTape,
      afterOutput] using
      plain_control_appender_path Address.suffixOutput
        .constantFalse (.node suffixOutputsEndRef)
        (by simpa [suffixOutputNode] using
          suffixOutputNode_member)
        source afterProgram [.outputsEnd, .instanceEnd]
        outsideLeft outsideRight sourcePacked
  have third :
      WorkMachineProgramPath.AcceptPath graph
        (.node suffixOutputsEndRef)
        (.node suffixInstanceEndRef)
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells afterOutput) + 1)
        secondTape thirdTape := by
    simpa [suffixOutputsEndNode, suffixOutputsEndRef,
      suffixInstanceEndRef, secondTape, thirdTape,
      afterOutputsEnd] using
      plain_control_appender_path Address.suffixOutputsEnd
        .outputsEnd (.node suffixInstanceEndRef)
        (by simpa [suffixOutputsEndNode] using
          suffixOutputsEndNode_member)
        source afterOutput [.instanceEnd]
        outsideLeft outsideRight sourcePacked
  have fourth :
      WorkMachineProgramPath.AcceptPath graph
        (.node suffixInstanceEndRef)
        (.node finalizerRef)
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells afterOutputsEnd) + 1)
        thirdTape fourthTape := by
    simpa [suffixInstanceEndNode, suffixInstanceEndRef,
      finalizerRef, thirdTape, fourthTape,
      afterInstanceEnd] using
      plain_control_appender_path Address.suffixInstanceEnd
        .instanceEnd (.node finalizerRef)
        (by simpa [suffixInstanceEndNode] using
          suffixInstanceEndNode_member)
        source afterOutputsEnd [] outsideLeft outsideRight
        sourcePacked
  have firstTwo :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node suffixProgramEndRef)
      (.node suffixOutputRef)
      (.node suffixOutputsEndRef)
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells afterProgram) + 1)
      (scanTape [] source emitted fixedSuffixTokens
        outsideLeft outsideRight)
      firstTape secondTape first second
  have firstThree :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node suffixProgramEndRef)
      (.node suffixOutputsEndRef)
      (.node suffixInstanceEndRef)
      ((TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
        (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells afterProgram) + 1))
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells afterOutput) + 1)
      (scanTape [] source emitted fixedSuffixTokens
        outsideLeft outsideRight)
      secondTape thirdTape firstTwo third
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node suffixProgramEndRef)
      (.node suffixInstanceEndRef)
      (.node finalizerRef)
      ((TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells emitted) + 1) +
        (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells afterProgram) + 1) +
        (TargetEmitterCursorAppender.appendWorkSteps source
          (LockedNAND.SourceParser.packedTokenCells afterOutput) + 1))
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells afterOutputsEnd) + 1)
      (scanTape [] source emitted fixedSuffixTokens
        outsideLeft outsideRight)
      thirdTape fourthTape firstThree fourth
  simpa [suffixSteps, afterProgram, afterOutput,
    afterOutputsEnd, afterInstanceEnd, fourthTape,
    fixedSuffixTokens, Nat.add_assoc,
    List.append_assoc] using all

private def postFinalizerTape
    (source : List WorkSymbol) (emitted : List Token)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkTape :=
  TargetEmitterCursorFinalizer.finalTape source
    (LockedNAND.SourceParser.packedTokenCells emitted)
    outsideLeft outsideRight

private theorem finalizer_path
    (source : List WorkSymbol) (emitted : List Token)
    (outsideLeft outsideRight : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        LockedNAND.TargetEmitter.PackedSymbol symbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node finalizerRef)
      (.node cleanupRef)
      (TargetEmitterCursorFinalizer.workSteps source + 1)
      (scanTape [] source emitted []
        outsideLeft outsideRight)
      (postFinalizerTape source emitted
        outsideLeft outsideRight) := by
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        finalizerNode
        (TargetEmitterCursorFinalizer.workSteps source)
        (scanTape [] source emitted []
          outsideLeft outsideRight)
        (postFinalizerTape source emitted
          outsideLeft outsideRight) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      finalizerNode, controlNode, scanTape,
      postFinalizerTape, appendReserve,
      configAtWord_tape_eta,
      TargetEmitterCursorFinalizer.inputConfiguration,
      TargetEmitterCursorFinalizer.finalConfiguration,
      TargetEmitterCursorFinalizer.machine,
      cursorFinalizer_configurationAtWord_eq,
      Prepare.sourceLeftBoundary,
      Prepare.sourceTargetBoundary,
      List.append_assoc] using
      TargetEmitterCursorFinalizer.finalize_exact source
        (LockedNAND.SourceParser.packedTokenCells emitted)
        outsideLeft outsideRight
        (fun symbol member =>
          Or.inl (sourcePacked symbol member))
  simpa [finalizerNode, finalizerRef, cleanupRef,
    controlNode, controlRef, Node.reference] using
    node_accept_path finalizerNode finalizerNode_member
      (TargetEmitterCursorFinalizer.workSteps source)
      _ _ localRun

private theorem cleanup_path
    (tokens : List CNFToken)
    (outsideLeft outsideRight : List WorkSymbol) :
    WorkMachineProgramPath.AcceptPath graph
      (.node cleanupRef) .accept
      (BoundaryCleanup.workSteps
          (cnfTokenWorkSymbols tokens) + 1)
      (postFinalizerTape
        (cnfTokenWorkSymbols tokens)
        (Source.carrierTokens tokens)
        outsideLeft outsideRight)
      (finalTape tokens outsideLeft outsideRight) := by
  let source := cnfTokenWorkSymbols tokens
  let target := targetCells tokens
  have targetNonempty : target ≠ [] := by
    intro equality
    have targetLength := targetCells_length tokens
    rw [show targetCells tokens = [] by
      simpa [target] using equality] at targetLength
    simp only [List.length_nil] at targetLength
    unfold appendedTokenCount at targetLength
    omega
  cases targetEquality : target with
  | nil =>
      exact (targetNonempty targetEquality).elim
  | cons first rest =>
      have targetEq :
          LockedNAND.SourceParser.packedTokenCells
              (Source.carrierTokens tokens) =
            first :: rest := by
        simpa [target, targetCells] using targetEquality
      have firstPacked :
          LockedNAND.TargetEmitter.PackedSymbol first := by
        apply LockedNAND.TargetEmitter.packedTokenCells_packed
          (Source.carrierTokens tokens) first
        have firstMember :
            first ∈ targetCells tokens := by
          rw [show targetCells tokens = first :: rest by
            simpa [target] using targetEquality]
          exact List.Mem.head rest
        simpa [targetCells] using firstMember
      have localRun :
          WorkMachineProgramPath.LocalAcceptRun
            cleanupNode
            (BoundaryCleanup.workSteps source)
            (postFinalizerTape source
              (Source.carrierTokens tokens)
              outsideLeft outsideRight)
            (finalTape tokens outsideLeft outsideRight) := by
        rw [show
          postFinalizerTape source
              (Source.carrierTokens tokens)
              outsideLeft outsideRight =
            TargetEmitterCursorFinalizer.finalTape source
              (first :: rest) outsideLeft outsideRight by
          simp [postFinalizerTape, targetEq]]
        rw [show
          finalTape tokens outsideLeft outsideRight =
            BoundaryCleanup.finalTape source
              (first :: rest) outsideLeft outsideRight by
          simp [finalTape, source, targetCells, targetEq]]
        simpa [WorkMachineProgramPath.LocalAcceptRun,
          cleanupNode, controlNode, postFinalizerTape,
          finalTape, targetCells, source, target,
          BoundaryCleanup.machine,
          BoundaryCleanup.finalConfiguration] using
          BoundaryCleanup.cleanup_exact source first rest
            outsideLeft outsideRight firstPacked
      simpa [cleanupNode, cleanupRef,
        controlNode, controlRef, Node.reference,
        source] using
        node_accept_path cleanupNode cleanupNode_member
          (BoundaryCleanup.workSteps source)
          _ _ localRun

private def framedTape (tokens : List CNFToken) :
    WorkTape :=
  Prepare.entryTape tokens [] (initialBlankReserve tokens)

private theorem framer_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    WorkMachineProgramPath.AcceptPath graph
      (.node graph.entry)
      (.node prepareRef)
      (RawFramer.workSteps tokens + 1)
      (entryTape tokens [] [])
      (framedTape tokens) := by
  dsimp only
  let tokens := first :: rest
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        framerNode (RawFramer.workSteps tokens)
        (entryTape tokens [] []) (framedTape tokens) := by
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      framerNode, controlNode, entryTape, entryPadding,
      framedTape, Prepare.entryTape,
      RawFramer.machine, configAtWord_tape_eta,
      RawFramer.sourceLeftBoundary,
      RawFramer.sourceTargetBoundary,
      RawFramer.formulaPad, RawFramer.cellBlank,
      Prepare.sourceLeftBoundary,
      Prepare.sourceTargetBoundary,
      Prepare.formulaPad, Prepare.cellBlank,
      List.append_assoc] using
      RawFramer.canonical_exact first rest
        (RawFramer.cellBlank :: initialBlankReserve tokens)
  simpa [graph, framerRef, framerNode,
    prepareRef, controlNode, controlRef,
    Node.reference] using
    node_accept_path framerNode framerNode_member
      (RawFramer.workSteps tokens) _ _ localRun

private theorem prepare_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node prepareRef)
      (.node headerVersionRef)
      (Prepare.workSteps tokens + 1)
      (framedTape tokens)
      (scanTape [] source [] (Source.carrierTokens tokens)
        [] []) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  have localRun :
      WorkMachineProgramPath.LocalAcceptRun
        prepareNode (Prepare.workSteps tokens)
        (framedTape tokens)
        (scanTape [] source [] (Source.carrierTokens tokens)
          [] []) := by
    have reserveEq :
        Prepare.cellBlank :: Prepare.cellBlank ::
            initialBlankReserve tokens =
          appendReserve (Source.carrierTokens tokens) [] := by
      change
        entryPadding tokens =
          appendReserve (Source.carrierTokens tokens) []
      rw [entryPadding_eq_replicate]
      simp [appendReserve,
        Source.carrierTokens_length, appendedTokenCount]
    simpa [WorkMachineProgramPath.LocalAcceptRun,
      prepareNode, controlNode, framedTape,
      Prepare.machine, Prepare.entryConfiguration,
      Prepare.finalConfiguration, Prepare.finalTape,
      scanTape, configAtWord_tape_eta,
      tokens, source, reserveEq,
      LockedNAND.SourceParser.packedTokenCells,
      List.append_assoc] using
      Prepare.canonical_exact first rest []
        (initialBlankReserve tokens)
  simpa [prepareNode, prepareRef, headerVersionRef,
    controlNode, controlRef, Node.reference] using
    node_accept_path prepareNode prepareNode_member
      (Prepare.workSteps tokens) _ _ localRun

private def afterHeadersSchedule
    (tokens : List CNFToken) : List Token :=
  List.replicate tokens.length .unit ++
    [.natEnd] ++ Source.gateTokenStream tokens ++
      fixedSuffixTokens

private def headerSteps
    (source : List WorkSymbol) : Nat :=
  (TargetEmitterCursorAppender.appendWorkSteps source [] + 1) +
    (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells [.version0]) + 1)

private theorem header_path
    (tokens : List CNFToken) :
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node headerVersionRef)
      (.node (countMatchRef .f))
      (headerSteps source)
      (scanTape [] source [] (Source.carrierTokens tokens)
        [] [])
      (scanTape [] source [.version0, .natEnd]
        (afterHeadersSchedule tokens) [] []) := by
  dsimp only
  let source := cnfTokenWorkSymbols tokens
  let afterVersionTape :=
    scanTape [] source [.version0]
      (.natEnd :: afterHeadersSchedule tokens) [] []
  have version :
      WorkMachineProgramPath.AcceptPath graph
        (.node headerVersionRef)
        (.node headerInputEndRef)
        (TargetEmitterCursorAppender.appendWorkSteps source [] + 1)
        (scanTape [] source [] (Source.carrierTokens tokens)
          [] [])
        afterVersionTape := by
    simpa [headerVersionNode, headerVersionRef,
      headerInputEndRef, Source.carrierTokens,
      afterHeadersSchedule, fixedSuffixTokens,
      afterVersionTape,
      LockedNAND.SourceParser.packedTokenCells,
      List.append_assoc] using
      plain_control_appender_path Address.headerVersion
        .version0 (.node headerInputEndRef)
        (by simpa [headerVersionNode] using
          headerVersionNode_member)
        source [] (.natEnd :: afterHeadersSchedule tokens)
        [] [] (sourceCells_packed tokens)
  have inputEnd :
      WorkMachineProgramPath.AcceptPath graph
        (.node headerInputEndRef)
        (.node (countMatchRef .f))
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells [.version0]) + 1)
        afterVersionTape
        (scanTape [] source [.version0, .natEnd]
          (afterHeadersSchedule tokens) [] []) := by
    simpa [headerInputEndNode, headerInputEndRef,
      afterVersionTape, List.append_assoc] using
      plain_control_appender_path Address.headerInputEnd
        .natEnd (.node (countMatchRef .f))
        (by simpa [headerInputEndNode] using
          headerInputEndNode_member)
        source [.version0] (afterHeadersSchedule tokens)
        [] [] (sourceCells_packed tokens)
  simpa [headerSteps, Nat.add_assoc] using
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node headerVersionRef)
      (.node headerInputEndRef)
      (.node (countMatchRef .f))
      (TargetEmitterCursorAppender.appendWorkSteps source [] + 1)
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells [.version0]) + 1)
      (scanTape [] source [] (Source.carrierTokens tokens)
        [] [])
      afterVersionTape
      (scanTape [] source [.version0, .natEnd]
        (afterHeadersSchedule tokens) [] [])
      version inputEnd

private def headerTokens : List Token :=
  [.version0, .natEnd]

private def countTailSchedule
    (tokens : List CNFToken) : List Token :=
  [.natEnd] ++ Source.gateTokenStream tokens ++
    fixedSuffixTokens

private def countEmitted
    (tokens : List CNFToken) : List Token :=
  headerTokens ++ List.replicate tokens.length .unit

private def gateStartEmitted
    (tokens : List CNFToken) : List Token :=
  countEmitted tokens ++ [.natEnd]

private def gateEmitted
    (tokens : List CNFToken) : List Token :=
  gateStartEmitted tokens ++ Source.gateTokenStream tokens

private def prefixSteps (tokens : List CNFToken) : Nat :=
  (RawFramer.workSteps tokens + 1) +
    (Prepare.workSteps tokens + 1) +
    headerSteps (cnfTokenWorkSymbols tokens)

private theorem prefix_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node graph.entry)
      (.node (countMatchRef .f))
      (prefixSteps tokens)
      (entryTape tokens [] [])
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] []) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  have framing := framer_path first rest
  have preparation := prepare_path first rest
  have headers := header_path tokens
  have throughPrepare :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node graph.entry) (.node prepareRef)
      (.node headerVersionRef)
      (RawFramer.workSteps tokens + 1)
      (Prepare.workSteps tokens + 1)
      (entryTape tokens [] []) (framedTape tokens)
      (scanTape [] source [] (Source.carrierTokens tokens)
        [] [])
      (by simpa [tokens] using framing)
      (by simpa [tokens, source] using preparation)
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node graph.entry) (.node headerVersionRef)
      (.node (countMatchRef .f))
      ((RawFramer.workSteps tokens + 1) +
        (Prepare.workSteps tokens + 1))
      (headerSteps source)
      (entryTape tokens [] [])
      (scanTape [] source [] (Source.carrierTokens tokens)
        [] [])
      (scanTape [] source [.version0, .natEnd]
        (afterHeadersSchedule tokens) [] [])
      throughPrepare (by simpa [source] using headers)
  simpa [prefixSteps, tokens, source, headerTokens,
    Nat.add_assoc] using all

private def countPhaseSteps
    (tokens : List CNFToken) : Nat :=
  let source := cnfTokenWorkSymbols tokens
  let emitted := countEmitted tokens
  countPassSteps [] tokens headerTokens +
    10 +
    (Rewind.workSteps tokens + 1) +
    (TargetEmitterCursorAppender.appendWorkSteps source
      (LockedNAND.SourceParser.packedTokenCells emitted) + 1)

private theorem count_phase_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node (countMatchRef .f))
      (.node (gateMatchRef .f))
      (countPhaseSteps tokens)
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] [])
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] []) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  let emitted := countEmitted tokens
  let remaining :=
    Source.gateTokenStream tokens ++ fixedSuffixTokens
  let atCountBoundary :=
    scanTape source [] emitted
      (.natEnd :: remaining) [] []
  let afterCountRewind :=
    scanTape [] source emitted
      (.natEnd :: remaining) [] []
  have packed := sourceCells_packed tokens
  have countPass :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countMatchRef .f))
        (.node (countMatchRef .f))
        (countPassSteps [] tokens headerTokens)
        (scanTape [] source headerTokens
          (afterHeadersSchedule tokens) [] [])
        atCountBoundary := by
    simpa [source, emitted, remaining,
      atCountBoundary, afterHeadersSchedule,
      countTailSchedule, countEmitted,
      headerTokens, fixedSuffixTokens,
      List.append_assoc] using
      count_pass_path [] tokens headerTokens
        (countTailSchedule tokens) [] []
        (by simpa using packed)
  have boundary :
      WorkMachineProgramPath.AcceptPath graph
        (.node (countMatchRef .f))
        (.node countRewindRef)
        10 atCountBoundary atCountBoundary := by
    apply count_boundary_dispatch_path atCountBoundary
    simp [atCountBoundary, scanTape,
      LockedNAND.TargetEmitter.configAtWord]
  have rewind :
      WorkMachineProgramPath.AcceptPath graph
        (.node countRewindRef)
        (.node gateCountEndRef)
        (Rewind.workSteps tokens + 1)
        atCountBoundary afterCountRewind := by
    simpa [tokens, source, emitted, remaining,
      atCountBoundary, afterCountRewind] using
      count_rewind_path first rest emitted
        (.natEnd :: remaining) [] []
  have countEnd :
      WorkMachineProgramPath.AcceptPath graph
        (.node gateCountEndRef)
        (.node (gateMatchRef .f))
        (TargetEmitterCursorAppender.appendWorkSteps source
            (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
        afterCountRewind
        (scanTape [] source (gateStartEmitted tokens)
          remaining [] []) := by
    simpa [emitted, remaining, afterCountRewind,
      gateStartEmitted] using
      gate_count_end_path source emitted remaining
        [] [] packed
  have throughBoundary :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node (countMatchRef .f))
      (.node countRewindRef)
      (countPassSteps [] tokens headerTokens) 10
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] [])
      atCountBoundary atCountBoundary countPass boundary
  have throughRewind :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node countRewindRef)
      (.node gateCountEndRef)
      (countPassSteps [] tokens headerTokens + 10)
      (Rewind.workSteps tokens + 1)
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] [])
      atCountBoundary afterCountRewind
      throughBoundary rewind
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (countMatchRef .f))
      (.node gateCountEndRef)
      (.node (gateMatchRef .f))
      (countPassSteps [] tokens headerTokens + 10 +
        (Rewind.workSteps tokens + 1))
      (TargetEmitterCursorAppender.appendWorkSteps source
        (LockedNAND.SourceParser.packedTokenCells emitted) + 1)
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] [])
      afterCountRewind
      (scanTape [] source (gateStartEmitted tokens)
        remaining [] [])
      throughRewind countEnd
  simpa [countPhaseSteps, tokens, source,
    emitted, remaining, Nat.add_assoc] using all

private def gatePhaseSteps
    (tokens : List CNFToken) : Nat :=
  let source := cnfTokenWorkSymbols tokens
  let emitted := gateEmitted tokens
  gatePassSteps [] tokens (gateStartEmitted tokens) +
    10 +
    (Rewind.workSteps tokens + 1) +
    suffixSteps source emitted

private theorem gate_phase_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node (gateMatchRef .f))
      (.node finalizerRef)
      (gatePhaseSteps tokens)
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] []) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  let emitted := gateEmitted tokens
  let atGateBoundary :=
    scanTape source [] emitted fixedSuffixTokens [] []
  let afterGateRewind :=
    scanTape [] source emitted fixedSuffixTokens [] []
  have packed := sourceCells_packed tokens
  have gatePass :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateMatchRef .f))
        (.node (gateMatchRef .f))
        (gatePassSteps [] tokens (gateStartEmitted tokens))
        (scanTape [] source (gateStartEmitted tokens)
          (Source.gateTokenStream tokens ++
            fixedSuffixTokens) [] [])
        atGateBoundary := by
    simpa [source, emitted, gateEmitted,
      atGateBoundary, List.append_assoc] using
      gate_pass_path [] tokens (gateStartEmitted tokens)
        fixedSuffixTokens [] [] (by simpa using packed)
  have boundary :
      WorkMachineProgramPath.AcceptPath graph
        (.node (gateMatchRef .f))
        (.node gateRewindRef)
        10 atGateBoundary atGateBoundary := by
    apply gate_boundary_dispatch_path atGateBoundary
    simp [atGateBoundary, scanTape,
      LockedNAND.TargetEmitter.configAtWord]
  have rewind :
      WorkMachineProgramPath.AcceptPath graph
        (.node gateRewindRef)
        (.node suffixProgramEndRef)
        (Rewind.workSteps tokens + 1)
        atGateBoundary afterGateRewind := by
    simpa [tokens, source, emitted,
      atGateBoundary, afterGateRewind] using
      gate_rewind_path first rest emitted
        fixedSuffixTokens [] []
  have suffix :
      WorkMachineProgramPath.AcceptPath graph
        (.node suffixProgramEndRef)
        (.node finalizerRef)
        (suffixSteps source emitted)
        afterGateRewind
        (scanTape [] source (Source.carrierTokens tokens)
          [] [] []) := by
    simpa [source, emitted, afterGateRewind,
      Source.carrierTokens, gateEmitted,
      gateStartEmitted, countEmitted, headerTokens,
      fixedSuffixTokens, List.append_assoc] using
      suffix_path source emitted [] [] packed
  have throughBoundary :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node (gateMatchRef .f))
      (.node gateRewindRef)
      (gatePassSteps [] tokens (gateStartEmitted tokens))
      10
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      atGateBoundary atGateBoundary gatePass boundary
  have throughRewind :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node gateRewindRef)
      (.node suffixProgramEndRef)
      (gatePassSteps [] tokens
        (gateStartEmitted tokens) + 10)
      (Rewind.workSteps tokens + 1)
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      atGateBoundary afterGateRewind
      throughBoundary rewind
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node (gateMatchRef .f))
      (.node suffixProgramEndRef)
      (.node finalizerRef)
      (gatePassSteps [] tokens
          (gateStartEmitted tokens) + 10 +
        (Rewind.workSteps tokens + 1))
      (suffixSteps source emitted)
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      afterGateRewind
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] [])
      throughRewind suffix
  simpa [gatePhaseSteps, tokens, source,
    emitted, Nat.add_assoc] using all

private def terminalSteps
    (tokens : List CNFToken) : Nat :=
  let source := cnfTokenWorkSymbols tokens
  (TargetEmitterCursorFinalizer.workSteps source + 1) +
    (BoundaryCleanup.workSteps source + 1)

private theorem terminal_path
    (tokens : List CNFToken) :
    let source := cnfTokenWorkSymbols tokens
    WorkMachineProgramPath.AcceptPath graph
      (.node finalizerRef) .accept
      (terminalSteps tokens)
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] [])
      (finalTape tokens [] []) := by
  dsimp only
  let source := cnfTokenWorkSymbols tokens
  have finalize :=
    finalizer_path source (Source.carrierTokens tokens)
      [] [] (sourceCells_packed tokens)
  have cleanup := cleanup_path tokens [] []
  simpa [terminalSteps, source, Nat.add_assoc] using
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node finalizerRef) (.node cleanupRef) .accept
      (TargetEmitterCursorFinalizer.workSteps source + 1)
      (BoundaryCleanup.workSteps source + 1)
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] [])
      (postFinalizerTape source
        (Source.carrierTokens tokens) [] [])
      (finalTape tokens [] [])
      finalize (by simpa [source] using cleanup)

/-- Exact graph-level work for every nonempty canonical packed CNF carrier
input.  The count is derived solely from the literal program schedule. -/
def canonicalWorkSteps (tokens : List CNFToken) : Nat :=
  prefixSteps tokens +
    countPhaseSteps tokens +
    gatePhaseSteps tokens +
    terminalSteps tokens

private theorem canonical_accept_path
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    WorkMachineProgramPath.AcceptPath graph
      (.node graph.entry) .accept
      (canonicalWorkSteps tokens)
      (entryTape tokens [] [])
      (finalTape tokens [] []) := by
  dsimp only
  let tokens := first :: rest
  let source := cnfTokenWorkSymbols tokens
  have prefixRun := prefix_path first rest
  have countRun := count_phase_path first rest
  have gateRun := gate_phase_path first rest
  have terminalRun := terminal_path tokens
  have throughCount :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node graph.entry)
      (.node (countMatchRef .f))
      (.node (gateMatchRef .f))
      (prefixSteps tokens) (countPhaseSteps tokens)
      (entryTape tokens [] [])
      (scanTape [] source headerTokens
        (afterHeadersSchedule tokens) [] [])
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      (by simpa [tokens, source] using prefixRun)
      (by simpa [tokens, source] using countRun)
  have throughGate :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node graph.entry)
      (.node (gateMatchRef .f))
      (.node finalizerRef)
      (prefixSteps tokens + countPhaseSteps tokens)
      (gatePhaseSteps tokens)
      (entryTape tokens [] [])
      (scanTape [] source (gateStartEmitted tokens)
        (Source.gateTokenStream tokens ++
          fixedSuffixTokens) [] [])
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] [])
      throughCount (by simpa [tokens, source] using gateRun)
  have all :=
    WorkMachineProgramPath.AcceptPath.trans
      graph (.node graph.entry) (.node finalizerRef) .accept
      (prefixSteps tokens + countPhaseSteps tokens +
        gatePhaseSteps tokens)
      (terminalSteps tokens)
      (entryTape tokens [] [])
      (scanTape [] source (Source.carrierTokens tokens)
        [] [] [])
      (finalTape tokens [] [])
      throughGate (by simpa [source] using terminalRun)
  simpa [canonicalWorkSteps, tokens,
    Nat.add_assoc] using all

/-- Certificate-free exact acceptance of every nonempty canonical packed
CNF word, with the precise strict-v0 carrier tape exposed at the endpoint. -/
theorem canonical_exact
    (first : CNFToken) (rest : List CNFToken) :
    let tokens := first :: rest
    workRunExact? machine (canonicalWorkSteps tokens)
        (entryConfiguration tokens [] []) =
      some (finalConfiguration tokens [] []) := by
  dsimp only
  let tokens := first :: rest
  have path := canonical_accept_path first rest
  simpa [tokens, entryConfiguration,
    finalConfiguration, machine] using
    WorkMachineProgramPath.runEntryToAccept graph
      (canonicalWorkSteps tokens)
      (entryTape tokens [] []) (finalTape tokens [] [])
      graph_wellFormed (by simpa [tokens] using path)

private theorem dispatchSteps_le_eight
    (token : CNFToken) :
    dispatchSteps token ≤ 8 := by
  cases token <;> simp [dispatchSteps, tokenCode]

private theorem countPassSteps_bound
    (before : List WorkSymbol) (tokens : List CNFToken)
    (emitted : List Token) :
    countPassSteps before tokens emitted ≤
      tokens.length *
        (4 * (before.length + tokens.length) +
          4 * (emitted.length + tokens.length) + 22) := by
  induction tokens generalizing before emitted with
  | nil =>
      simp [countPassSteps]
  | cons token rest inductionHypothesis =>
      have dispatchBound := dispatchSteps_le_eight token
      let charge :=
        4 * (before.length + (token :: rest).length) +
          4 * (emitted.length + (token :: rest).length) + 22
      have tailBound :=
        inductionHypothesis
          (before ++ [sourceSymbol token])
          (emitted ++ [Token.unit])
      have chargeEq :
          4 *
                ((before ++ [sourceSymbol token]).length +
                  rest.length) +
              4 * ((emitted ++ [Token.unit]).length +
                rest.length) + 22 =
            charge := by
        simp [charge]
        omega
      rw [chargeEq] at tailBound
      have itemBound :
          countItemSteps token before
              (cnfTokenWorkSymbols rest) emitted ≤
            charge := by
        simp [countItemSteps,
          TargetEmitterCursorAppender.workSteps,
          LockedNAND.SourceParser.packedTokenCells_length,
          cnfTokenWorkSymbols_length, charge]
        omega
      simp only [countPassSteps]
      calc
        countItemSteps token before
                (cnfTokenWorkSymbols rest) emitted +
              countPassSteps
                (before ++ [sourceSymbol token]) rest
                (emitted ++ [Token.unit]) ≤
            charge + rest.length * charge :=
          Nat.add_le_add itemBound tailBound
        _ = (token :: rest).length * charge := by
          simp [Nat.add_mul, Nat.add_comm]
        _ = (token :: rest).length *
              (4 * (before.length + (token :: rest).length) +
                4 * (emitted.length + (token :: rest).length) +
                  22) := by
          rfl

private theorem gatePassSteps_bound
    (before : List WorkSymbol) (tokens : List CNFToken)
    (emitted : List Token) :
    gatePassSteps before tokens emitted ≤
      tokens.length *
        (8 * (before.length + tokens.length) +
          12 * (emitted.length + 3 * tokens.length) + 40) := by
  induction tokens generalizing before emitted with
  | nil =>
      simp [gatePassSteps]
  | cons token rest inductionHypothesis =>
      have dispatchBound := dispatchSteps_le_eight token
      let charge :=
        8 * (before.length + (token :: rest).length) +
          12 *
            (emitted.length + 3 * (token :: rest).length) + 40
      have tailBound :=
        inductionHypothesis
          (before ++ [sourceSymbol token])
          (emitted ++ Source.tokenGateTokens token)
      have chargeEq :
          8 *
                ((before ++ [sourceSymbol token]).length +
                  rest.length) +
              12 *
                ((emitted ++ Source.tokenGateTokens token).length +
                  3 * rest.length) + 40 =
            charge := by
        simp [charge, Source.tokenGateTokens]
        omega
      rw [chargeEq] at tailBound
      have itemBound :
          gateItemSteps token before
              (cnfTokenWorkSymbols rest) emitted ≤
            charge := by
        simp [gateItemSteps,
          TargetEmitterCursorAppender.workSteps,
          LockedNAND.SourceParser.packedTokenCells_length,
          cnfTokenWorkSymbols_length,
          charge]
        omega
      simp only [gatePassSteps]
      calc
        gateItemSteps token before
                (cnfTokenWorkSymbols rest) emitted +
              gatePassSteps
                (before ++ [sourceSymbol token]) rest
                (emitted ++ Source.tokenGateTokens token) ≤
            charge + rest.length * charge :=
          Nat.add_le_add itemBound tailBound
        _ = (token :: rest).length * charge := by
          simp [Nat.add_mul, Nat.add_comm]
        _ = (token :: rest).length *
              (8 * (before.length + (token :: rest).length) +
                12 *
                  (emitted.length +
                    3 * (token :: rest).length) + 40) := by
          rfl

private theorem countEmitted_length
    (tokens : List CNFToken) :
    (countEmitted tokens).length = tokens.length + 2 := by
  simp [countEmitted, headerTokens]

private theorem gateStartEmitted_length
    (tokens : List CNFToken) :
    (gateStartEmitted tokens).length =
      tokens.length + 3 := by
  simp [gateStartEmitted, countEmitted_length]

private theorem gateEmitted_length
    (tokens : List CNFToken) :
    (gateEmitted tokens).length =
      4 * tokens.length + 3 := by
  simp [gateEmitted, gateStartEmitted_length,
    Source.gateTokenStream_length]
  omega

private theorem prefixSteps_evaluated
    (tokens : List CNFToken) :
    prefixSteps tokens = 8 * tokens.length + 30 := by
  simp [prefixSteps, RawFramer.workSteps,
    Prepare.workSteps, headerSteps,
    TargetEmitterCursorAppender.appendWorkSteps,
    LockedNAND.SourceParser.packedTokenCells_length,
    cnfTokenWorkSymbols_length]
  omega

private theorem countPhaseSteps_bound
    (tokens : List CNFToken) :
    countPhaseSteps tokens ≤
      tokens.length * (8 * tokens.length + 30) +
        7 * tokens.length + 28 := by
  have passBound :=
    countPassSteps_bound [] tokens headerTokens
  have normalizedPass :
      countPassSteps [] tokens headerTokens ≤
        tokens.length * (8 * tokens.length + 30) := by
    have chargeEq :
        4 * tokens.length +
              (4 * (2 + tokens.length) + 22) =
            8 * tokens.length + 30 := by
      omega
    simpa [headerTokens, chargeEq, Nat.add_assoc] using
      passBound
  have phaseEq :
      countPhaseSteps tokens =
        countPassSteps [] tokens headerTokens +
          7 * tokens.length + 28 := by
    simp [countPhaseSteps, Rewind.workSteps,
      TargetEmitterCursorAppender.appendWorkSteps,
      LockedNAND.SourceParser.packedTokenCells_length,
      cnfTokenWorkSymbols_length, countEmitted_length]
    omega
  rw [phaseEq]
  exact Nat.add_le_add_right normalizedPass
    (7 * tokens.length + 28)

private theorem suffixSteps_evaluated
    (tokens : List CNFToken) :
    suffixSteps (cnfTokenWorkSymbols tokens)
        (gateEmitted tokens) =
      72 * tokens.length + 100 := by
  simp [suffixSteps,
    TargetEmitterCursorAppender.appendWorkSteps,
    LockedNAND.SourceParser.packedTokenCells_length,
    cnfTokenWorkSymbols_length, gateEmitted_length]
  omega

private theorem gatePhaseSteps_bound
    (tokens : List CNFToken) :
    gatePhaseSteps tokens ≤
      tokens.length * (56 * tokens.length + 76) +
        73 * tokens.length + 113 := by
  have passBound :=
    gatePassSteps_bound [] tokens
      (gateStartEmitted tokens)
  have normalizedPass :
      gatePassSteps [] tokens (gateStartEmitted tokens) ≤
        tokens.length * (56 * tokens.length + 76) := by
    have chargeEq :
        8 * tokens.length +
              (12 *
                (tokens.length + (3 + 3 * tokens.length)) +
                40) =
            56 * tokens.length + 76 := by
      omega
    simpa [gateStartEmitted_length, chargeEq,
      Nat.add_assoc] using passBound
  have phaseEq :
      gatePhaseSteps tokens =
        gatePassSteps [] tokens (gateStartEmitted tokens) +
          73 * tokens.length + 113 := by
    unfold gatePhaseSteps
    dsimp only
    rw [suffixSteps_evaluated]
    simp [Rewind.workSteps]
    omega
  rw [phaseEq]
  have widened :
      gatePassSteps [] tokens (gateStartEmitted tokens) +
            (73 * tokens.length + 113) ≤
        tokens.length * (56 * tokens.length + 76) +
          (73 * tokens.length + 113) :=
    Nat.add_le_add_right normalizedPass
      (73 * tokens.length + 113)
  simpa [Nat.add_assoc] using widened

private theorem terminalSteps_evaluated
    (tokens : List CNFToken) :
    terminalSteps tokens = 3 * tokens.length + 8 := by
  simp [terminalSteps,
    TargetEmitterCursorFinalizer.workSteps,
    BoundaryCleanup.workSteps,
    cnfTokenWorkSymbols_length]
  omega

/-- The exact canonical execution count is bounded by the published fixed
quadratic.  This theorem is the runtime interface consumed by the outer
compiler; no schedule or path certificate is accepted from its caller. -/
theorem canonicalWorkSteps_polynomial_bound
    (tokens : List CNFToken) :
    canonicalWorkSteps tokens ≤
      workPolynomial.eval tokens.length := by
  have countBound := countPhaseSteps_bound tokens
  have gateBound := gatePhaseSteps_bound tokens
  rw [canonicalWorkSteps, prefixSteps_evaluated,
    terminalSteps_evaluated, workPolynomial_evaluated]
  let count := 4 * tokens.length + 7
  have combined :
      8 * tokens.length + 30 +
            countPhaseSteps tokens +
          gatePhaseSteps tokens +
        (3 * tokens.length + 8) ≤
      (8 * tokens.length + 30) +
          (tokens.length * (8 * tokens.length + 30) +
            7 * tokens.length + 28) +
        (tokens.length * (56 * tokens.length + 76) +
          73 * tokens.length + 113) +
        (3 * tokens.length + 8) := by
    have prefixCount :=
      Nat.add_le_add_left countBound
        (8 * tokens.length + 30)
    have throughGate :=
      Nat.add_le_add prefixCount gateBound
    exact Nat.add_le_add_right throughGate
      (3 * tokens.length + 8)
  apply Nat.le_trans combined
  dsimp only [count]
  have quadraticEq :
      tokens.length * (tokens.length * 56) =
        tokens.length * (tokens.length * 32) +
          tokens.length * (tokens.length * 2) +
          tokens.length * (tokens.length * 22) := by
    rw [show (56 : Nat) = 32 + (2 + 22) by omega]
    repeat rw [Nat.mul_add]
    rw [Nat.add_assoc]
  simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc,
    Nat.mul_comm, Nat.mul_left_comm, quadraticEq]
  omega

end PNP.Concrete.CNFToNANDCarrierEncoder
