/-
Copyright (c) 2026 PNP Labs.

Two literal binary readers for the constant-source tags in a CNF carrier
gate.  Both machines accept a false constant and reject a true constant.
The first reader advances to the following source field; the second leaves
the head on the constant's final cell so the controller can install its
cursor and rewind.
-/

import PNP.Concrete.LockedNANDTargetEmitterMachine

namespace PNP.Concrete.CNFToNANDCarrierTokenReader

open PNP.Concrete

def cell01 : WorkSymbol := WorkSymbol.zeroOne
def cell00 : WorkSymbol := WorkSymbol.zeroZero

namespace State

def start : Nat := 0
def second : Nat := 1
def accept : Nat := 2
def reject : Nat := 3
def dead : Nat := 4

end State

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

def deadAction (symbol : WorkSymbol) : Action :=
  { targetState := State.dead
    writeSymbol := symbol
    move := .stay }

def firstAction (symbol : WorkSymbol) : Action :=
  if symbol = cell01 then
    { targetState := State.second
      writeSymbol := symbol
      move := .right }
  else
    deadAction symbol

def secondAction (advance : Bool)
    (symbol : WorkSymbol) : Action :=
  let move : HeadMove := if advance then .right else .stay
  if symbol = cell00 then
    { targetState := State.accept
      writeSymbol := symbol
      move := move }
  else if symbol = cell01 then
    { targetState := State.reject
      writeSymbol := symbol
      move := move }
  else
    deadAction symbol

def allWorkSymbols : List WorkSymbol :=
  PNP.Concrete.LockedNAND.TargetEmitter.allWorkSymbols

def rulesAt (state : Nat)
    (action : WorkSymbol → Action) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let selected := action symbol
    { sourceState := state
      readSymbol := symbol
      targetState := selected.targetState
      writeSymbol := selected.writeSymbol
      move := selected.move }

def rules (advance : Bool) : List WorkRule :=
  rulesAt State.start firstAction ++
    rulesAt State.second (secondAction advance)

def machine (advance : Bool) : WorkMachine :=
  { rules := rules advance
    startState := State.start
    acceptState := State.accept
    rejectState := State.reject }

/-- Reader used for the first constant source in a carrier gate. -/
def firstSourceMachine : WorkMachine :=
  machine true

/-- Reader used for the second constant source in a carrier gate. -/
def secondSourceMachine : WorkMachine :=
  machine false

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length (advance : Bool) :
    (rules advance).length = 18 := by
  cases advance <;> rfl

private theorem rulesAt_pairwise
    (state : Nat) (action : WorkSymbol → Action) :
    (rulesAt state action).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols
    PNP.Concrete.LockedNAND.TargetEmitter.allWorkSymbols
  simp [QueryDistinct, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

theorem rules_pairwise (advance : Bool) :
    (rules advance).Pairwise QueryDistinct := by
  unfold rules
  rw [List.pairwise_append]
  refine ⟨rulesAt_pairwise _ _, rulesAt_pairwise _ _, ?_⟩
  intro left leftMember right rightMember
  unfold QueryDistinct
  have leftState :
      left.sourceState = State.start := by
    rcases List.mem_map.mp leftMember with
      ⟨symbol, _member, equality⟩
    rw [← equality]
  have rightState :
      right.sourceState = State.second := by
    rcases List.mem_map.mp rightMember with
      ⟨symbol, _member, equality⟩
    rw [← equality]
  rw [leftState, rightState]
  simp [State.start, State.second]

theorem start_ne_accept (advance : Bool) :
    (machine advance).startState ≠
      (machine advance).acceptState := by
  simp [machine, State.start, State.accept]

theorem start_ne_reject (advance : Bool) :
    (machine advance).startState ≠
      (machine advance).rejectState := by
  simp [machine, State.start, State.reject]

theorem accept_ne_reject (advance : Bool) :
    (machine advance).acceptState ≠
      (machine advance).rejectState := by
  simp [machine, State.accept, State.reject]

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (advance : Bool)
    (symbol : WorkSymbol) :
    findWorkRule (rules advance) State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases advance <;> cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (advance : Bool)
    (symbol : WorkSymbol) :
    findWorkRule (rules advance) State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases advance <;> cases first <;> cases second <;> decide

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  match word with
  | [] =>
      { state := state
        tape :=
          { left := left
            head := WorkSymbol.blank
            right := [] } }
  | head :: rest =>
      { state := state
        tape :=
          { left := left
            head := head
            right := rest } }

theorem false_exact (advance : Bool)
    (left rest : List WorkSymbol) :
    workRunExact? (machine advance) 2
        (configAtWord State.start left
          (cell01 :: cell00 :: rest)) =
      some
        (configAtWord State.accept
          (if advance then cell00 :: cell01 :: left
           else cell01 :: left)
          (if advance then rest else cell00 :: rest)) := by
  cases advance <;> cases rest <;> rfl

theorem true_exact (advance : Bool)
    (left rest : List WorkSymbol) :
    workRunExact? (machine advance) 2
        (configAtWord State.start left
          (cell01 :: cell01 :: rest)) =
      some
        (configAtWord State.reject
          (if advance then cell01 :: cell01 :: left
           else cell01 :: left)
          (if advance then rest else cell01 :: rest)) := by
  cases advance <;> cases rest <;> rfl

theorem false_halted (advance : Bool)
    (left rest : List WorkSymbol) :
    (machine advance).isHalted
      (configAtWord State.accept
        (if advance then cell00 :: cell01 :: left
         else cell01 :: left)
        (if advance then rest else cell00 :: rest)) =
      true := by
  cases advance <;> cases rest <;> rfl

theorem true_halted (advance : Bool)
    (left rest : List WorkSymbol) :
    (machine advance).isHalted
      (configAtWord State.reject
        (if advance then cell01 :: cell01 :: left
         else cell01 :: left)
        (if advance then rest else cell01 :: rest)) =
      true := by
  cases advance <;> cases rest <;> rfl

/-! ## Unmarked return to the first carrier cell

After the first counting pass the head is on the carrier's program delimiter.
This small machine scans left across ordinary packed cells and stops one cell
to the right of the retained source boundary.  Unlike cursor installation it
leaves no marker behind, so the second pass may safely install one temporary
cursor at a time.
-/

namespace Rewind

def sourceLeftBoundary : WorkSymbol :=
  PNP.Concrete.LockedNAND.TargetEmitter.sourceLeftBoundary

namespace State

def accept : Nat := 0
def reject : Nat := 1
def scan : Nat := 2

end State

def packed (symbol : WorkSymbol) : Bool :=
  symbol == WorkSymbol.zeroZero ||
    symbol == WorkSymbol.zeroOne ||
    symbol == WorkSymbol.oneZero ||
    symbol == WorkSymbol.oneOne

def action (symbol : WorkSymbol) : Action :=
  if packed symbol then
    { targetState := State.scan
      writeSymbol := symbol
      move := .left }
  else if symbol == sourceLeftBoundary then
    { targetState := State.accept
      writeSymbol := symbol
      move := .right }
  else
    { targetState := State.reject
      writeSymbol := symbol
      move := .stay }

def rules : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let selected := action symbol
    { sourceState := State.scan
      readSymbol := symbol
      targetState := selected.targetState
      writeSymbol := selected.writeSymbol
      move := selected.move }

def machine : WorkMachine :=
  { rules := rules
    startState := State.scan
    acceptState := State.accept
    rejectState := State.reject }

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rules_length : rules.length = 9 := by
  rfl

theorem rules_pairwise : rules.Pairwise QueryDistinct := by
  unfold rules allWorkSymbols
    PNP.Concrete.LockedNAND.TargetEmitter.allWorkSymbols
  simp [QueryDistinct, WorkSymbol.blank,
    WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero,
    WorkSymbol.zeroOne, WorkSymbol.oneBlank,
    WorkSymbol.oneZero, WorkSymbol.oneOne]

theorem accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases first <;> cases second <;> decide

private theorem packed_step
    (symbol : WorkSymbol)
    (ordinary :
      PNP.Concrete.LockedNAND.TargetEmitter.PackedSymbol symbol)
    (left right : List WorkSymbol) :
    workStep? machine
        { state := State.scan
          tape := { left := left, head := symbol, right := right } } =
      some
        { state := State.scan
          tape := (WorkTape.mk left symbol right).move .left } := by
  cases ordinary <;> rfl

theorem boundary_step
    (left right : List WorkSymbol) :
    workStep? machine
        { state := State.scan
          tape :=
            { left := left
              head := sourceLeftBoundary
              right := right } } =
      some
        { state := State.accept
          tape :=
            (WorkTape.mk left sourceLeftBoundary right).move .right } := by
  rfl

end Rewind

end PNP.Concrete.CNFToNANDCarrierTokenReader
