/-
Copyright (c) 2026 PNP Labs.

Literal source-field capture for the grammar-only locked-NAND target emitter.

The machine starts on the first packed cell of one canonical raw source
field.  Constants are classified directly.  Input and gate indices are
counted into the nearest unary scratch record by repeated physical scans; no
decoder or host-side source lookup occurs in the rule table.  The final cell
of the selected source field is replaced by the contextual cursor, and the
head returns to the first retained source cell.  A later cursor-aware emitter
can therefore issue the selected closed template and then restore/advance the
source cursor exactly once.
-/

import PNP.Concrete.LockedNANDTargetEmitterScratchIncrement

namespace PNP.Concrete.LockedNAND.TargetEmitterSourceCapture

open PNP.Concrete

def cell00 : WorkSymbol := WorkSymbol.zeroZero
def cell01 : WorkSymbol := WorkSymbol.zeroOne
def cell10 : WorkSymbol := WorkSymbol.oneZero
def cell11 : WorkSymbol := WorkSymbol.oneOne

def sourceLeftBoundary : WorkSymbol :=
  TargetEmitter.sourceLeftBoundary

def cursorMarker : WorkSymbol :=
  TargetEmitterCursorAppender.cursorMarker

def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

inductive SourceKind where
  | input
  | constantFalse
  | constantTrue
  | gate
deriving BEq, DecidableEq, Repr

inductive NatKind where
  | input
  | gate
deriving BEq, DecidableEq, Repr

def NatKind.sourceKind : NatKind → SourceKind
  | .input => .input
  | .gate => .gate

def firstCell : SourceKind → WorkSymbol
  | .input => cell00
  | .constantFalse => cell01
  | .constantTrue => cell01
  | .gate => cell01

def secondCell : SourceKind → WorkSymbol
  | .input => cell11
  | .constantFalse => cell00
  | .constantTrue => cell01
  | .gate => cell10

def hasNatural : SourceKind → Bool
  | .input => true
  | .constantFalse => false
  | .constantTrue => false
  | .gate => true

def startState : Nat := 0
def tagSecondState : Nat := 1
def natFirstState : Nat := 2
def natSecondState : Nat := 3
def markUnitState : Nat := 4
def rewindUnitState : Nat := 5
def incrementSeekState : Nat := 6
def incrementWriteState : Nat := 7
def incrementReturnState : Nat := 8
def resumeSeekState : Nat := 9
def resumeSecondState : Nat := 10
def rewindFinalState : Nat := 11
def acceptState : Nat := 12
def rejectState : Nat := 13
def deadState : Nat := 14

structure StateProgram where
  state : Nat
  action : WorkSymbol → Nat × WorkSymbol × HeadMove

def deadAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  (deadState, symbol, .stay)

def startAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = firstCell kind then
    (tagSecondState, symbol, .right)
  else
    deadAction symbol

def tagSecondAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = secondCell kind then
    if hasNatural kind then
      (natFirstState, symbol, .right)
    else
      (rewindFinalState, cursorMarker, .left)
  else
    deadAction symbol

def natFirstAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if hasNatural kind && symbol = cell00 then
    (natSecondState, symbol, .right)
  else
    deadAction symbol

def natSecondAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if hasNatural kind && symbol = cell01 then
    (markUnitState, symbol, .left)
  else if hasNatural kind && symbol = cell10 then
    (rewindFinalState, cursorMarker, .left)
  else
    deadAction symbol

def markUnitAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if hasNatural kind && symbol = cell00 then
    (rewindUnitState, cursorMarker, .left)
  else
    deadAction symbol

def rewindUnitAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (rewindUnitState, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (incrementSeekState, symbol, .left)
  else
    deadAction symbol

def incrementSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementSeekState, symbol, .left)
  else if symbol = unarySeparator then
    (incrementWriteState, unaryUnit, .left)
  else
    deadAction symbol

def incrementWriteAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = WorkSymbol.blank then
    (incrementReturnState, unarySeparator, .right)
  else
    deadAction symbol

def incrementReturnAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = unaryUnit then
    (incrementReturnState, symbol, .right)
  else if symbol = sourceLeftBoundary then
    (resumeSeekState, symbol, .right)
  else
    deadAction symbol

def resumeSeekAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (resumeSeekState, symbol, .right)
  else if symbol = cursorMarker then
    (resumeSecondState, cell00, .right)
  else
    deadAction symbol

def resumeSecondAction (kind : SourceKind) (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if hasNatural kind && symbol = cell01 then
    (natFirstState, symbol, .right)
  else
    deadAction symbol

def rewindFinalAction (symbol : WorkSymbol) :
    Nat × WorkSymbol × HeadMove :=
  if symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 then
    (rewindFinalState, symbol, .left)
  else if symbol = sourceLeftBoundary then
    (acceptState, symbol, .right)
  else
    deadAction symbol

def statePrograms (kind : SourceKind) : List StateProgram :=
  [ { state := startState, action := startAction kind }
  , { state := tagSecondState, action := tagSecondAction kind }
  , { state := natFirstState, action := natFirstAction kind }
  , { state := natSecondState, action := natSecondAction kind }
  , { state := markUnitState, action := markUnitAction kind }
  , { state := rewindUnitState, action := rewindUnitAction }
  , { state := incrementSeekState, action := incrementSeekAction }
  , { state := incrementWriteState, action := incrementWriteAction }
  , { state := incrementReturnState, action := incrementReturnAction }
  , { state := resumeSeekState, action := resumeSeekAction }
  , { state := resumeSecondState, action := resumeSecondAction kind }
  , { state := rewindFinalState, action := rewindFinalAction } ]

def rulesAt (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.1
      writeSymbol := action.2.1
      move := action.2.2 }

def rules (kind : SourceKind) : List WorkRule :=
  (statePrograms kind).flatMap rulesAt

def machine (kind : SourceKind) : WorkMachine :=
  { rules := rules kind
    startState := startState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachine (kind : SourceKind) : Machine :=
  compileWorkMachine (machine kind)

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem rulesAt_length (program : StateProgram) :
    (rulesAt program).length = 9 := by
  rfl

theorem statePrograms_length (kind : SourceKind) :
    (statePrograms kind).length = 12 := by
  rfl

theorem rules_length (kind : SourceKind) :
    (rules kind).length = 108 := by
  cases kind <;> rfl

private theorem rulesAt_pairwise (program : StateProgram) :
    (rulesAt program).Pairwise QueryDistinct := by
  unfold rulesAt allWorkSymbols TargetEmitter.allWorkSymbols
  simp [QueryDistinct,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem rulesAt_source
    {program : StateProgram} {rule : WorkRule}
    (member : rule ∈ rulesAt program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, equality⟩
  rw [← equality]

private theorem statePrograms_pairwise (kind : SourceKind) :
    (statePrograms kind).Pairwise
      (fun left right => left.state ≠ right.state) := by
  cases kind <;> decide

private theorem materialized_pairwise
    (programs : List StateProgram)
    (distinct :
      programs.Pairwise (fun left right => left.state ≠ right.state)) :
    (programs.flatMap rulesAt).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      simp
  | cons program rest ih =>
      rw [List.flatMap_cons, List.pairwise_append]
      refine
        ⟨rulesAt_pairwise program,
          ih (List.pairwise_cons.mp distinct).2,
          ?_⟩
      intro left leftMember right rightMember
      have leftSource := rulesAt_source leftMember
      rcases List.mem_flatMap.mp rightMember with
        ⟨rightProgram, rightProgramMember, rightRuleMember⟩
      have rightSource := rulesAt_source rightRuleMember
      have stateNe :
          program.state ≠ rightProgram.state :=
        (List.pairwise_cons.mp distinct).1 rightProgram
          rightProgramMember
      intro queryEqual
      exact stateNe
        (leftSource.symm.trans
          ((congrArg Prod.fst queryEqual).trans rightSource))

theorem rules_pairwise (kind : SourceKind) :
    (rules kind).Pairwise QueryDistinct :=
  materialized_pairwise (statePrograms kind)
    (statePrograms_pairwise kind)

theorem start_ne_accept (kind : SourceKind) :
    (machine kind).startState ≠ (machine kind).acceptState := by
  simp [machine, startState, acceptState]

theorem start_ne_reject (kind : SourceKind) :
    (machine kind).startState ≠ (machine kind).rejectState := by
  simp [machine, startState, rejectState]

theorem accept_ne_reject (kind : SourceKind) :
    (machine kind).acceptState ≠ (machine kind).rejectState := by
  simp [machine, acceptState, rejectState]

set_option maxRecDepth 100000 in
theorem no_rule_at_accept (kind : SourceKind) (symbol : WorkSymbol) :
    findWorkRule (rules kind) acceptState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases kind <;> cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_reject (kind : SourceKind) (symbol : WorkSymbol) :
    findWorkRule (rules kind) rejectState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases kind <;> cases first <;> cases second <;> decide

set_option maxRecDepth 100000 in
theorem no_rule_at_dead (kind : SourceKind) (symbol : WorkSymbol) :
    findWorkRule (rules kind) deadState symbol = none := by
  rcases symbol with ⟨first, second⟩
  cases kind <;> cases first <;> cases second <;> decide

/-! ### Canonical configurations -/

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

def scratchWord (count blankCount : Nat)
    (reserve outsideLeft : List WorkSymbol) :
    List WorkSymbol :=
  List.replicate count unaryUnit ++
    unarySeparator ::
      (List.replicate blankCount WorkSymbol.blank ++
        reserve ++ outsideLeft)

def unitPrefix : Nat → List WorkSymbol
  | 0 => []
  | count + 1 => cell00 :: cell01 :: unitPrefix count

theorem unitPrefix_length (count : Nat) :
    (unitPrefix count).length = 2 * count := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      simp only [unitPrefix, List.length_cons, ih]
      omega

theorem natCells_eq_unitPrefix (count : Nat) :
    SourceParser.natCells count =
      unitPrefix count ++ [cell00, cell10] := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      change
        cell00 :: cell01 :: SourceParser.natCells count =
          cell00 :: cell01 ::
            (unitPrefix count ++ [cell00, cell10])
      exact congrArg (List.cons cell00)
        (congrArg (List.cons cell01) ih)

def sourceCells (kind : SourceKind) (value : Nat) :
    List WorkSymbol :=
  match kind with
  | .input =>
      [cell00, cell11] ++ SourceParser.natCells value
  | .constantFalse =>
      [cell01, cell00]
  | .constantTrue =>
      [cell01, cell01]
  | .gate =>
      [cell01, cell10] ++ SourceParser.natCells value

def markedSourceCells (kind : SourceKind) (value : Nat) :
    List WorkSymbol :=
  match kind with
  | .input =>
      [cell00, cell11] ++ unitPrefix value ++
        [cell00, cursorMarker]
  | .constantFalse =>
      [cell01, cursorMarker]
  | .constantTrue =>
      [cell01, cursorMarker]
  | .gate =>
      [cell01, cell10] ++ unitPrefix value ++
        [cell00, cursorMarker]

theorem sourceCells_eq_parser
    (source : RawSource) :
    sourceCells
        (match source with
         | .input _ => .input
         | .constant false => .constantFalse
         | .constant true => .constantTrue
         | .gate _ => .gate)
        (match source with
         | .input index => index
         | .constant _ => 0
         | .gate index => index) =
      SourceParser.sourceCells source := by
  cases source with
  | input index =>
      rfl
  | constant value =>
      cases value <;> rfl
  | gate index =>
      rfl

def entryConfiguration (kind : SourceKind)
    (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord startState
    (before.reverse ++
      sourceLeftBoundary ::
        scratchWord scratch (value + 1) reserve outsideLeft)
    (sourceCells kind value ++ after)

def finalConfiguration (kind : SourceKind)
    (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord acceptState
    (sourceLeftBoundary ::
      scratchWord (scratch + value) 1 reserve outsideLeft)
    (before ++ markedSourceCells kind value ++ after)

/-! ### Exact-run calculus -/

private theorem exactRun_add (kind : SourceKind)
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst :
      workRunExact? (machine kind) first initial = some middle)
    (hSecond :
      workRunExact? (machine kind) second middle = some final) :
    workRunExact? (machine kind) (first + second) initial =
      some final := by
  induction first generalizing initial with
  | zero =>
      change some initial = some middle at hFirst
      have initialEq : initial = middle := Option.some.inj hFirst
      rw [Nat.zero_add, initialEq]
      exact hSecond
  | succ first ih =>
      cases hStep : workStep? (machine kind) initial with
      | none =>
          change
            (match workStep? (machine kind) initial with
             | none => none
             | some next =>
                 workRunExact? (machine kind) first next) =
              some middle at hFirst
          rw [hStep] at hFirst
          contradiction
      | some next =>
          have tail :
              workRunExact? (machine kind) first next =
                some middle := by
            change
              (match workStep? (machine kind) initial with
               | none => none
               | some next =>
                   workRunExact? (machine kind) first next) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? (machine kind) initial with
             | none => none
             | some next =>
                 workRunExact? (machine kind)
                   (first + second) next) =
              some final
          rw [hStep]
          exact ih next tail

private theorem exactRun_one (kind : SourceKind)
    (initial final : WorkConfiguration)
    (step :
      workStep? (machine kind) initial = some final) :
    workRunExact? (machine kind) 1 initial = some final := by
  change
    (match workStep? (machine kind) initial with
     | none => none
     | some next => some next) = some final
  rw [step]

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

private theorem scanLeftExact (kind : SourceKind) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? (machine kind)
          (configAtLeftWord state
            (head :: leftTail) rightSide) =
        some (configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machine kind) word.length
        (configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state
        leftSuffix (pushLeft word rightSide)) := by
  induction word generalizing rightSide with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed : Allowed head :=
        hAllowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? (machine kind)
            (configAtLeftWord state
              (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? (machine kind) rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide headAllowed]
      exact ih (head :: rightSide) restAllowed

private theorem scanRightExact (kind : SourceKind) (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? (machine kind)
          (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state
          (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? (machine kind) word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state
        (pushLeft word leftSide) suffix) := by
  induction word generalizing leftSide with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed : Allowed head :=
        hAllowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol found
        exact hAllowed symbol (List.Mem.tail head found)
      change
        (match workStep? (machine kind)
            (configAtWord state leftSide
              (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? (machine kind) rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) headAllowed]
      exact ih (head :: leftSide) restAllowed

private theorem packed_of_cells
    (symbol : WorkSymbol)
    (allowed :
      symbol = cell00 ∨ symbol = cell01 ∨
        symbol = cell10 ∨ symbol = cell11) :
    TargetEmitter.PackedSymbol symbol := by
  rcases allowed with rfl | rfl | rfl | rfl <;> constructor

private theorem cells_of_packed
    (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    symbol = cell00 ∨ symbol = cell01 ∨
      symbol = cell10 ∨ symbol = cell11 := by
  cases packed <;> simp [cell00, cell01, cell10, cell11]

set_option maxRecDepth 100000 in
private theorem find_rewind_unit_packed
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rules kind) rewindUnitState symbol =
      some
        { sourceState := rewindUnitState
          readSymbol := symbol
          targetState := rewindUnitState
          writeSymbol := symbol
          move := .left } := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_rewind_unit_boundary
    (kind : SourceKind) :
    findWorkRule (rules kind) rewindUnitState sourceLeftBoundary =
      some
        { sourceState := rewindUnitState
          readSymbol := sourceLeftBoundary
          targetState := incrementSeekState
          writeSymbol := sourceLeftBoundary
          move := .left } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_seek_unit
    (kind : SourceKind) :
    findWorkRule (rules kind) incrementSeekState unaryUnit =
      some
        { sourceState := incrementSeekState
          readSymbol := unaryUnit
          targetState := incrementSeekState
          writeSymbol := unaryUnit
          move := .left } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_seek_separator
    (kind : SourceKind) :
    findWorkRule (rules kind) incrementSeekState unarySeparator =
      some
        { sourceState := incrementSeekState
          readSymbol := unarySeparator
          targetState := incrementWriteState
          writeSymbol := unaryUnit
          move := .left } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_write_blank
    (kind : SourceKind) :
    findWorkRule (rules kind) incrementWriteState WorkSymbol.blank =
      some
        { sourceState := incrementWriteState
          readSymbol := WorkSymbol.blank
          targetState := incrementReturnState
          writeSymbol := unarySeparator
          move := .right } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_return_unit
    (kind : SourceKind) :
    findWorkRule (rules kind) incrementReturnState unaryUnit =
      some
        { sourceState := incrementReturnState
          readSymbol := unaryUnit
          targetState := incrementReturnState
          writeSymbol := unaryUnit
          move := .right } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_increment_return_boundary
    (kind : SourceKind) :
    findWorkRule (rules kind) incrementReturnState sourceLeftBoundary =
      some
        { sourceState := incrementReturnState
          readSymbol := sourceLeftBoundary
          targetState := resumeSeekState
          writeSymbol := sourceLeftBoundary
          move := .right } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_resume_packed
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rules kind) resumeSeekState symbol =
      some
        { sourceState := resumeSeekState
          readSymbol := symbol
          targetState := resumeSeekState
          writeSymbol := symbol
          move := .right } := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_resume_cursor
    (kind : SourceKind) :
    findWorkRule (rules kind) resumeSeekState cursorMarker =
      some
        { sourceState := resumeSeekState
          readSymbol := cursorMarker
          targetState := resumeSecondState
          writeSymbol := cell00
          move := .right } := by
  cases kind <;> decide

set_option maxRecDepth 100000 in
private theorem find_rewind_final_packed
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol) :
    findWorkRule (rules kind) rewindFinalState symbol =
      some
        { sourceState := rewindFinalState
          readSymbol := symbol
          targetState := rewindFinalState
          writeSymbol := symbol
          move := .left } := by
  cases kind <;> cases packed <;> decide

set_option maxRecDepth 100000 in
private theorem find_rewind_final_boundary
    (kind : SourceKind) :
    findWorkRule (rules kind) rewindFinalState sourceLeftBoundary =
      some
        { sourceState := rewindFinalState
          readSymbol := sourceLeftBoundary
          targetState := acceptState
          writeSymbol := sourceLeftBoundary
          move := .right } := by
  cases kind <;> decide

private theorem controller_not_halted
    (kind : SourceKind) (state : Nat)
    (stateCases :
      state = startState ∨ state = tagSecondState ∨
      state = natFirstState ∨ state = natSecondState ∨
      state = markUnitState ∨ state = rewindUnitState ∨
      state = incrementSeekState ∨ state = incrementWriteState ∨
      state = incrementReturnState ∨ state = resumeSeekState ∨
      state = resumeSecondState ∨ state = rewindFinalState)
    (tape : WorkTape) :
    (machine kind).isHalted { state := state, tape := tape } = false := by
  rcases stateCases with
    rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem rewind_unit_packed_step
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machine kind)
        (configAtLeftWord rewindUnitState
          (symbol :: leftTail) rightSide) =
      some
        (configAtLeftWord rewindUnitState
          leftTail (symbol :: rightSide)) := by
  have notHalted :=
    controller_not_halted kind rewindUnitState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (configAtLeftWord rewindUnitState
        (symbol :: leftTail) rightSide).tape
  calc
    workStep? (machine kind)
        (configAtLeftWord rewindUnitState
          (symbol :: leftTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := rewindUnitState
            readSymbol := symbol
            targetState := rewindUnitState
            writeSymbol := symbol
            move := .left }
          (configAtLeftWord rewindUnitState
            (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_unit_packed kind symbol packed)
    _ = some
        (configAtLeftWord rewindUnitState
          leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

private theorem resume_packed_step
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (leftSide rightTail : List WorkSymbol) :
    workStep? (machine kind)
        (configAtWord resumeSeekState leftSide
          (symbol :: rightTail)) =
      some
        (configAtWord resumeSeekState
          (symbol :: leftSide) rightTail) := by
  have notHalted :=
    controller_not_halted kind resumeSeekState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
      (configAtWord resumeSeekState leftSide
        (symbol :: rightTail)).tape
  calc
    workStep? (machine kind)
        (configAtWord resumeSeekState leftSide
          (symbol :: rightTail)) =
      some
        (applyWorkRule
          { sourceState := resumeSeekState
            readSymbol := symbol
            targetState := resumeSeekState
            writeSymbol := symbol
            move := .right }
          (configAtWord resumeSeekState leftSide
            (symbol :: rightTail))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_resume_packed kind symbol packed)
    _ = some
        (configAtWord resumeSeekState
          (symbol :: leftSide) rightTail) := by
      cases rightTail <;> rfl

private theorem rewind_final_packed_step
    (kind : SourceKind) (symbol : WorkSymbol)
    (packed : TargetEmitter.PackedSymbol symbol)
    (leftTail rightSide : List WorkSymbol) :
    workStep? (machine kind)
        (configAtLeftWord rewindFinalState
          (symbol :: leftTail) rightSide) =
      some
        (configAtLeftWord rewindFinalState
          leftTail (symbol :: rightSide)) := by
  have notHalted :=
    controller_not_halted kind rewindFinalState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr rfl)))))))))))
      (configAtLeftWord rewindFinalState
        (symbol :: leftTail) rightSide).tape
  calc
    workStep? (machine kind)
        (configAtLeftWord rewindFinalState
          (symbol :: leftTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := rewindFinalState
            readSymbol := symbol
            targetState := rewindFinalState
            writeSymbol := symbol
            move := .left }
          (configAtLeftWord rewindFinalState
            (symbol :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_final_packed kind symbol packed)
    _ = some
        (configAtLeftWord rewindFinalState
          leftTail (symbol :: rightSide)) := by
      cases leftTail <;> rfl

private theorem nat_first_step
    (kind : NatKind) (leftSide suffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord natFirstState leftSide
          (cell00 :: cell01 :: suffix)) =
      some
        (configAtWord natSecondState
          (cell00 :: leftSide) (cell01 :: suffix)) := by
  apply exactRun_one
  cases kind <;> rfl

private theorem nat_unit_second_step
    (kind : NatKind) (leftSide suffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord natSecondState
          (cell00 :: leftSide) (cell01 :: suffix)) =
      some
        (configAtWord markUnitState leftSide
          (cell00 :: cell01 :: suffix)) := by
  apply exactRun_one
  cases kind <;> cases leftSide <;> rfl

private theorem mark_unit_step
    (kind : NatKind) (leftWord suffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord markUnitState leftWord
          (cell00 :: cell01 :: suffix)) =
      some
        (configAtLeftWord rewindUnitState leftWord
          (cursorMarker :: cell01 :: suffix)) := by
  apply exactRun_one
  cases kind <;> cases leftWord <;> rfl

private theorem rewind_unit_boundary_step
    (kind : NatKind) (scratchTail rightSide : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtLeftWord rewindUnitState
          (sourceLeftBoundary :: scratchTail) rightSide) =
      some
        (configAtLeftWord incrementSeekState scratchTail
          (sourceLeftBoundary :: rightSide)) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind.sourceKind rewindUnitState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
      (configAtLeftWord rewindUnitState
        (sourceLeftBoundary :: scratchTail) rightSide).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtLeftWord rewindUnitState
          (sourceLeftBoundary :: scratchTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := rewindUnitState
            readSymbol := sourceLeftBoundary
            targetState := incrementSeekState
            writeSymbol := sourceLeftBoundary
            move := .left }
          (configAtLeftWord rewindUnitState
            (sourceLeftBoundary :: scratchTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_unit_boundary kind.sourceKind)
    _ = some
        (configAtLeftWord incrementSeekState scratchTail
          (sourceLeftBoundary :: rightSide)) := by
      cases scratchTail <;> rfl

private theorem increment_seek_unit_step
    (kind : NatKind) (leftTail rightSide : List WorkSymbol) :
    workStep? (machine kind.sourceKind)
        (configAtLeftWord incrementSeekState
          (unaryUnit :: leftTail) rightSide) =
      some
        (configAtLeftWord incrementSeekState
          leftTail (unaryUnit :: rightSide)) := by
  have notHalted :=
    controller_not_halted kind.sourceKind incrementSeekState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl)))))))
      (configAtLeftWord incrementSeekState
        (unaryUnit :: leftTail) rightSide).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtLeftWord incrementSeekState
          (unaryUnit :: leftTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := incrementSeekState
            readSymbol := unaryUnit
            targetState := incrementSeekState
            writeSymbol := unaryUnit
            move := .left }
          (configAtLeftWord incrementSeekState
            (unaryUnit :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_increment_seek_unit kind.sourceKind)
    _ = some
        (configAtLeftWord incrementSeekState
          leftTail (unaryUnit :: rightSide)) := by
      cases leftTail <;> rfl

private theorem increment_seek_units_exact
    (kind : NatKind) (count : Nat)
    (leftSuffix rightSide : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) count
        (configAtLeftWord incrementSeekState
          (List.replicate count unaryUnit ++ leftSuffix)
          rightSide) =
      some
        (configAtLeftWord incrementSeekState
          leftSuffix
          (List.replicate count unaryUnit ++ rightSide)) := by
  have scanned := scanLeftExact kind.sourceKind incrementSeekState
    (fun symbol => symbol = unaryUnit)
    (fun head left right equal => by
      subst head
      exact increment_seek_unit_step kind left right)
    (List.replicate count unaryUnit)
    leftSuffix rightSide (by simp)
  simpa [pushLeft_eq_reverse_append] using scanned

private theorem increment_separator_step
    (kind : NatKind) (leftTail rightSide : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtLeftWord incrementSeekState
          (unarySeparator :: leftTail) rightSide) =
      some
        (configAtLeftWord incrementWriteState
          leftTail (unaryUnit :: rightSide)) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind.sourceKind incrementSeekState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl rfl)))))))
      (configAtLeftWord incrementSeekState
        (unarySeparator :: leftTail) rightSide).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtLeftWord incrementSeekState
          (unarySeparator :: leftTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := incrementSeekState
            readSymbol := unarySeparator
            targetState := incrementWriteState
            writeSymbol := unaryUnit
            move := .left }
          (configAtLeftWord incrementSeekState
            (unarySeparator :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_increment_seek_separator kind.sourceKind)
    _ = some
        (configAtLeftWord incrementWriteState
          leftTail (unaryUnit :: rightSide)) := by
      cases leftTail <;> rfl

private theorem increment_write_step
    (kind : NatKind) (leftTail rightSide : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtLeftWord incrementWriteState
          (WorkSymbol.blank :: leftTail) rightSide) =
      some
        (configAtWord incrementReturnState
          (unarySeparator :: leftTail) rightSide) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind.sourceKind incrementWriteState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inl rfl))))))))
      (configAtLeftWord incrementWriteState
        (WorkSymbol.blank :: leftTail) rightSide).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtLeftWord incrementWriteState
          (WorkSymbol.blank :: leftTail) rightSide) =
      some
        (applyWorkRule
          { sourceState := incrementWriteState
            readSymbol := WorkSymbol.blank
            targetState := incrementReturnState
            writeSymbol := unarySeparator
            move := .right }
          (configAtLeftWord incrementWriteState
            (WorkSymbol.blank :: leftTail) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_increment_write_blank kind.sourceKind)
    _ = some
        (configAtWord incrementReturnState
          (unarySeparator :: leftTail) rightSide) := by
      cases rightSide <;> rfl

private theorem increment_return_unit_step
    (kind : NatKind) (leftSide rightTail : List WorkSymbol) :
    workStep? (machine kind.sourceKind)
        (configAtWord incrementReturnState leftSide
          (unaryUnit :: rightTail)) =
      some
        (configAtWord incrementReturnState
          (unaryUnit :: leftSide) rightTail) := by
  have notHalted :=
    controller_not_halted kind.sourceKind incrementReturnState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      (configAtWord incrementReturnState leftSide
        (unaryUnit :: rightTail)).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtWord incrementReturnState leftSide
          (unaryUnit :: rightTail)) =
      some
        (applyWorkRule
          { sourceState := incrementReturnState
            readSymbol := unaryUnit
            targetState := incrementReturnState
            writeSymbol := unaryUnit
            move := .right }
          (configAtWord incrementReturnState leftSide
            (unaryUnit :: rightTail))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_increment_return_unit kind.sourceKind)
    _ = some
        (configAtWord incrementReturnState
          (unaryUnit :: leftSide) rightTail) := by
      cases rightTail <;> rfl

private theorem increment_return_units_exact
    (kind : NatKind) (count : Nat)
    (leftSide rightSuffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) count
        (configAtWord incrementReturnState leftSide
          (List.replicate count unaryUnit ++ rightSuffix)) =
      some
        (configAtWord incrementReturnState
          (List.replicate count unaryUnit ++ leftSide)
          rightSuffix) := by
  have scanned := scanRightExact kind.sourceKind incrementReturnState
    (fun symbol => symbol = unaryUnit)
    (fun left head suffix equal => by
      subst head
      exact increment_return_unit_step kind left suffix)
    (List.replicate count unaryUnit)
    rightSuffix leftSide (by simp)
  simpa [pushLeft_eq_reverse_append] using scanned

private theorem increment_return_boundary_step
    (kind : NatKind) (leftSide rightSide : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord incrementReturnState leftSide
          (sourceLeftBoundary :: rightSide)) =
      some
        (configAtWord resumeSeekState
          (sourceLeftBoundary :: leftSide) rightSide) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind.sourceKind incrementReturnState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))))
      (configAtWord incrementReturnState leftSide
        (sourceLeftBoundary :: rightSide)).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtWord incrementReturnState leftSide
          (sourceLeftBoundary :: rightSide)) =
      some
        (applyWorkRule
          { sourceState := incrementReturnState
            readSymbol := sourceLeftBoundary
            targetState := resumeSeekState
            writeSymbol := sourceLeftBoundary
            move := .right }
          (configAtWord incrementReturnState leftSide
            (sourceLeftBoundary :: rightSide))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_increment_return_boundary kind.sourceKind)
    _ = some
        (configAtWord resumeSeekState
          (sourceLeftBoundary :: leftSide) rightSide) := by
      cases rightSide <;> rfl

private theorem resume_cursor_step
    (kind : NatKind) (leftSide suffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord resumeSeekState leftSide
          (cursorMarker :: cell01 :: suffix)) =
      some
        (configAtWord resumeSecondState
          (cell00 :: leftSide) (cell01 :: suffix)) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind.sourceKind resumeSeekState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))))
      (configAtWord resumeSeekState leftSide
        (cursorMarker :: cell01 :: suffix)).tape
  calc
    workStep? (machine kind.sourceKind)
        (configAtWord resumeSeekState leftSide
          (cursorMarker :: cell01 :: suffix)) =
      some
        (applyWorkRule
          { sourceState := resumeSeekState
            readSymbol := cursorMarker
            targetState := resumeSecondState
            writeSymbol := cell00
            move := .right }
          (configAtWord resumeSeekState leftSide
            (cursorMarker :: cell01 :: suffix))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_resume_cursor kind.sourceKind)
    _ = some
        (configAtWord resumeSecondState
          (cell00 :: leftSide) (cell01 :: suffix)) := by
      rfl

private theorem resume_second_step
    (kind : NatKind) (leftSide suffix : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord resumeSecondState
          (cell00 :: leftSide) (cell01 :: suffix)) =
      some
        (configAtWord natFirstState
          (cell01 :: cell00 :: leftSide) suffix) := by
  apply exactRun_one
  cases kind <;> cases suffix <;> rfl

def unitIterationSteps (prefixLength count : Nat) : Nat :=
  2 * prefixLength + 2 * count + 10

private theorem unit_iteration_exact
    (kind : NatKind) (sourcePrefix : List WorkSymbol)
    (count : Nat) (suffix reserve outsideLeft : List WorkSymbol)
    (prefixPacked :
      ∀ symbol, symbol ∈ sourcePrefix →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine kind.sourceKind)
        (unitIterationSteps sourcePrefix.length count)
        (configAtWord natFirstState
          (sourcePrefix.reverse ++
            sourceLeftBoundary ::
              scratchWord count 2 reserve outsideLeft)
          (cell00 :: cell01 :: suffix)) =
      some
        (configAtWord natFirstState
          ((sourcePrefix ++ [cell00, cell01]).reverse ++
            sourceLeftBoundary ::
              scratchWord (count + 1) 1 reserve outsideLeft)
          suffix) := by
  let scratchTail :=
    List.replicate count unaryUnit ++
      unarySeparator :: WorkSymbol.blank ::
        WorkSymbol.blank :: reserve ++ outsideLeft
  let markedRight :=
    cursorMarker :: cell01 :: suffix
  have hFirst := nat_first_step kind
    (sourcePrefix.reverse ++ sourceLeftBoundary :: scratchTail)
    suffix
  have hSecond := nat_unit_second_step kind
    (sourcePrefix.reverse ++ sourceLeftBoundary :: scratchTail)
    suffix
  have hMark := mark_unit_step kind
    (sourcePrefix.reverse ++ sourceLeftBoundary :: scratchTail)
    suffix
  have reversePacked :
      ∀ symbol, symbol ∈ sourcePrefix.reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    exact prefixPacked symbol (List.mem_reverse.mp found)
  have hRewind :
      workRunExact? (machine kind.sourceKind) sourcePrefix.length
          (configAtLeftWord rewindUnitState
            (sourcePrefix.reverse ++ sourceLeftBoundary :: scratchTail)
            markedRight) =
        some
          (configAtLeftWord rewindUnitState
            (sourceLeftBoundary :: scratchTail)
            (sourcePrefix ++ markedRight)) := by
    have scanned := scanLeftExact kind.sourceKind rewindUnitState
      TargetEmitter.PackedSymbol
      (fun head left right packed =>
        rewind_unit_packed_step kind.sourceKind head packed left right)
      sourcePrefix.reverse (sourceLeftBoundary :: scratchTail)
      markedRight reversePacked
    simpa [pushLeft_eq_reverse_append] using scanned
  have hBoundary :=
    rewind_unit_boundary_step kind scratchTail
      (sourcePrefix ++ markedRight)
  have hSeek := increment_seek_units_exact kind count
    (unarySeparator :: WorkSymbol.blank ::
      WorkSymbol.blank :: reserve ++ outsideLeft)
    (sourceLeftBoundary :: (sourcePrefix ++ markedRight))
  have hSeparator := increment_separator_step kind
    (WorkSymbol.blank :: WorkSymbol.blank ::
      reserve ++ outsideLeft)
    (List.replicate count unaryUnit ++
      (sourceLeftBoundary :: (sourcePrefix ++ markedRight)))
  have hWrite := increment_write_step kind
    (WorkSymbol.blank :: reserve ++ outsideLeft)
    (unaryUnit :: List.replicate count unaryUnit ++
      (sourceLeftBoundary :: (sourcePrefix ++ markedRight)))
  have hReturn := increment_return_units_exact kind (count + 1)
    (unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
    (sourceLeftBoundary :: (sourcePrefix ++ markedRight))
  have hReturnBoundary := increment_return_boundary_step kind
    (List.replicate (count + 1) unaryUnit ++
      unarySeparator :: WorkSymbol.blank :: reserve ++ outsideLeft)
    (sourcePrefix ++ markedRight)
  have hSeekCanonical :
      workRunExact? (machine kind.sourceKind) count
          (configAtLeftWord incrementSeekState scratchTail
            (sourceLeftBoundary :: (sourcePrefix ++ markedRight))) =
        some
          (configAtLeftWord incrementSeekState
            (unarySeparator :: WorkSymbol.blank ::
              WorkSymbol.blank :: reserve ++ outsideLeft)
            (List.replicate count unaryUnit ++
              (sourceLeftBoundary ::
                (sourcePrefix ++ markedRight)))) := by
    simpa [scratchTail] using hSeek
  have hReturnBoundaryCanonical :
      workRunExact? (machine kind.sourceKind) 1
          (configAtWord incrementReturnState
            (List.replicate (count + 1) unaryUnit ++
              (unarySeparator :: WorkSymbol.blank ::
                reserve ++ outsideLeft))
            (sourceLeftBoundary ::
              (sourcePrefix ++ markedRight))) =
        some
          (configAtWord resumeSeekState
            (sourceLeftBoundary ::
              List.replicate (count + 1) unaryUnit ++
                unarySeparator :: WorkSymbol.blank ::
                  reserve ++ outsideLeft)
            (sourcePrefix ++ markedRight)) := by
    simpa [List.append_assoc] using hReturnBoundary
  have hResume :
      workRunExact? (machine kind.sourceKind) sourcePrefix.length
          (configAtWord resumeSeekState
            (sourceLeftBoundary ::
              List.replicate (count + 1) unaryUnit ++
                unarySeparator :: WorkSymbol.blank ::
                  reserve ++ outsideLeft)
            (sourcePrefix ++ markedRight)) =
        some
          (configAtWord resumeSeekState
            (sourcePrefix.reverse ++
              sourceLeftBoundary ::
                List.replicate (count + 1) unaryUnit ++
                  unarySeparator :: WorkSymbol.blank ::
                    reserve ++ outsideLeft)
            markedRight) := by
    have scanned := scanRightExact kind.sourceKind resumeSeekState
      TargetEmitter.PackedSymbol
      (fun left head suffix packed =>
        resume_packed_step kind.sourceKind head packed left suffix)
      sourcePrefix markedRight
      (sourceLeftBoundary ::
        List.replicate (count + 1) unaryUnit ++
          unarySeparator :: WorkSymbol.blank ::
            reserve ++ outsideLeft)
      prefixPacked
    simpa [pushLeft_eq_reverse_append] using scanned
  have hCursor := resume_cursor_step kind
    (sourcePrefix.reverse ++
      sourceLeftBoundary ::
        List.replicate (count + 1) unaryUnit ++
          unarySeparator :: WorkSymbol.blank ::
            reserve ++ outsideLeft)
    suffix
  have hResumeSecond := resume_second_step kind
    (sourcePrefix.reverse ++
      sourceLeftBoundary ::
        List.replicate (count + 1) unaryUnit ++
          unarySeparator :: WorkSymbol.blank ::
            reserve ++ outsideLeft)
    suffix
  have h01 := exactRun_add kind.sourceKind 1 1 _ _ _ hFirst hSecond
  have h02 := exactRun_add kind.sourceKind 2 1 _ _ _ h01 hMark
  have h03 := exactRun_add kind.sourceKind 3 sourcePrefix.length
    _ _ _ h02 hRewind
  have h04 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length) 1 _ _ _ h03 hBoundary
  have h05 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1) count
    _ _ _ h04 hSeekCanonical
  have h06 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count) 1 _ _ _ h05 hSeparator
  have h07 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1) 1 _ _ _ h06 hWrite
  have h08 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1 + 1) (count + 1)
    _ _ _ h07 hReturn
  have h09 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1 + 1 + (count + 1)) 1
    _ _ _ h08 hReturnBoundaryCanonical
  have h10 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1) sourcePrefix.length
    _ _ _ h09 hResume
  have h11 := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1 + sourcePrefix.length) 1
    _ _ _ h10 hCursor
  have all := exactRun_add kind.sourceKind
    (3 + sourcePrefix.length + 1 + count + 1 + 1 +
      (count + 1) + 1 + sourcePrefix.length + 1) 1
    _ _ _ h11 hResumeSecond
  have steps :
      3 + sourcePrefix.length + 1 + count + 1 + 1 +
          (count + 1) + 1 + sourcePrefix.length + 1 + 1 =
        unitIterationSteps sourcePrefix.length count := by
    unfold unitIterationSteps
    omega
  rw [steps] at all
  simpa [scratchWord, scratchTail, markedRight,
    List.replicate_succ, List.append_assoc] using all

private theorem nat_final_second_step
    (kind : NatKind) (leftSide after : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord natSecondState
          (cell00 :: leftSide) (cell10 :: after)) =
      some
        (configAtLeftWord rewindFinalState
          (cell00 :: leftSide) (cursorMarker :: after)) := by
  apply exactRun_one
  cases kind <;> cases leftSide <;> rfl

private theorem nat_end_first_step
    (kind : NatKind) (leftSide after : List WorkSymbol) :
    workRunExact? (machine kind.sourceKind) 1
        (configAtWord natFirstState leftSide
          (cell00 :: cell10 :: after)) =
      some
        (configAtWord natSecondState
          (cell00 :: leftSide) (cell10 :: after)) := by
  apply exactRun_one
  cases kind <;> rfl

private theorem rewind_final_boundary_step
    (kind : SourceKind) (leftSide rightSide : List WorkSymbol) :
    workRunExact? (machine kind) 1
        (configAtLeftWord rewindFinalState
          (sourceLeftBoundary :: leftSide) rightSide) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary :: leftSide) rightSide) := by
  apply exactRun_one
  have notHalted :=
    controller_not_halted kind rewindFinalState
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr rfl)))))))))))
      (configAtLeftWord rewindFinalState
        (sourceLeftBoundary :: leftSide) rightSide).tape
  calc
    workStep? (machine kind)
        (configAtLeftWord rewindFinalState
          (sourceLeftBoundary :: leftSide) rightSide) =
      some
        (applyWorkRule
          { sourceState := rewindFinalState
            readSymbol := sourceLeftBoundary
            targetState := acceptState
            writeSymbol := sourceLeftBoundary
            move := .right }
          (configAtLeftWord rewindFinalState
            (sourceLeftBoundary :: leftSide) rightSide)) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_rewind_final_boundary kind)
    _ = some
        (configAtWord acceptState
          (sourceLeftBoundary :: leftSide) rightSide) := by
      cases rightSide <;> rfl

def natFinishSteps (prefixLength : Nat) : Nat :=
  prefixLength + 4

private theorem nat_finish_exact
    (kind : NatKind) (sourcePrefix : List WorkSymbol)
    (count : Nat) (after reserve outsideLeft : List WorkSymbol)
    (prefixPacked :
      ∀ symbol, symbol ∈ sourcePrefix →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine kind.sourceKind)
        (natFinishSteps sourcePrefix.length)
        (configAtWord natFirstState
          (sourcePrefix.reverse ++
            sourceLeftBoundary ::
              scratchWord count 1 reserve outsideLeft)
          (SourceParser.natCells 0 ++ after)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary ::
            scratchWord count 1 reserve outsideLeft)
          (sourcePrefix ++ [cell00, cursorMarker] ++ after)) := by
  have hFirst := nat_end_first_step kind
    (sourcePrefix.reverse ++
      sourceLeftBoundary ::
        scratchWord count 1 reserve outsideLeft)
    after
  have hSecond := nat_final_second_step kind
    (sourcePrefix.reverse ++
      sourceLeftBoundary ::
        scratchWord count 1 reserve outsideLeft)
    after
  have rewindPacked :
      ∀ symbol, symbol ∈ cell00 :: sourcePrefix.reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    simp only [List.mem_cons] at found
    rcases found with rfl | found
    · constructor
    · exact prefixPacked symbol (List.mem_reverse.mp found)
  have hRewind :
      workRunExact? (machine kind.sourceKind) (sourcePrefix.length + 1)
          (configAtLeftWord rewindFinalState
            (cell00 :: sourcePrefix.reverse ++
              sourceLeftBoundary ::
                scratchWord count 1 reserve outsideLeft)
            (cursorMarker :: after)) =
        some
          (configAtLeftWord rewindFinalState
            (sourceLeftBoundary ::
              scratchWord count 1 reserve outsideLeft)
            (sourcePrefix ++ [cell00, cursorMarker] ++ after)) := by
    have scanned := scanLeftExact kind.sourceKind rewindFinalState
      TargetEmitter.PackedSymbol
      (fun head left right packed =>
        rewind_final_packed_step kind.sourceKind head packed left right)
      (cell00 :: sourcePrefix.reverse)
      (sourceLeftBoundary ::
        scratchWord count 1 reserve outsideLeft)
      (cursorMarker :: after) rewindPacked
    simpa [pushLeft_eq_reverse_append, List.append_assoc] using scanned
  have hBoundary := rewind_final_boundary_step kind.sourceKind
    (scratchWord count 1 reserve outsideLeft)
    (sourcePrefix ++ [cell00, cursorMarker] ++ after)
  have h01 := exactRun_add kind.sourceKind 1 1 _ _ _ hFirst hSecond
  have h02 := exactRun_add kind.sourceKind 2 (sourcePrefix.length + 1)
    _ _ _ h01 hRewind
  have all := exactRun_add kind.sourceKind
    (2 + (sourcePrefix.length + 1)) 1 _ _ _ h02 hBoundary
  have steps :
      2 + (sourcePrefix.length + 1) + 1 =
        natFinishSteps sourcePrefix.length := by
    unfold natFinishSteps
    omega
  rw [steps] at all
  simpa [SourceParser.natCells,
    SourceParser.cell00, SourceParser.cell10,
    cell00, cell10] using all

def natLoopSteps : Nat → Nat → Nat → Nat
  | prefixLength, _, 0 =>
      natFinishSteps prefixLength
  | prefixLength, count, remaining + 1 =>
      unitIterationSteps prefixLength count +
        natLoopSteps (prefixLength + 2) (count + 1) remaining

private theorem unitPrefix_append_succ (used : Nat) :
    unitPrefix (used + 1) =
      unitPrefix used ++ [cell00, cell01] := by
  induction used with
  | zero =>
      rfl
  | succ used ih =>
      change
        cell00 :: cell01 :: unitPrefix (used + 1) =
          (cell00 :: cell01 :: unitPrefix used) ++
            [cell00, cell01]
      rw [ih]
      rfl

private theorem replicate_add
    (first second : Nat) (symbol : WorkSymbol) :
    List.replicate (first + second) symbol =
      List.replicate first symbol ++
        List.replicate second symbol := by
  induction first with
  | zero =>
      simp
  | succ first ih =>
      simp only [Nat.succ_add, List.replicate_succ,
        ih, List.cons_append]

private theorem nat_loop_exact
    (kind : NatKind) (basePrefix : List WorkSymbol)
    (used count remaining : Nat)
    (after reserve outsideLeft : List WorkSymbol)
    (prefixPacked :
      ∀ symbol,
        symbol ∈ basePrefix ++ unitPrefix used →
          TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine kind.sourceKind)
        (natLoopSteps
          (basePrefix ++ unitPrefix used).length count remaining)
        (configAtWord natFirstState
          ((basePrefix ++ unitPrefix used).reverse ++
            sourceLeftBoundary ::
              scratchWord count (remaining + 1)
                reserve outsideLeft)
          (SourceParser.natCells remaining ++ after)) =
      some
        (configAtWord acceptState
          (sourceLeftBoundary ::
            scratchWord (count + remaining) 1
              reserve outsideLeft)
          (basePrefix ++ unitPrefix (used + remaining) ++
            [cell00, cursorMarker] ++ after)) := by
  induction remaining generalizing used count with
  | zero =>
      simpa [natLoopSteps, Nat.add_zero] using
        nat_finish_exact kind
          (basePrefix ++ unitPrefix used) count
          after reserve outsideLeft prefixPacked
  | succ remaining ih =>
      let sourcePrefix := basePrefix ++ unitPrefix used
      have hIteration := unit_iteration_exact kind sourcePrefix count
        (SourceParser.natCells remaining ++ after)
        (List.replicate remaining WorkSymbol.blank ++ reserve)
        outsideLeft prefixPacked
      have nextPrefixPacked :
          ∀ symbol,
            symbol ∈ basePrefix ++ unitPrefix (used + 1) →
              TargetEmitter.PackedSymbol symbol := by
        intro symbol found
        rw [unitPrefix_append_succ] at found
        have membership :
            symbol ∈
              (basePrefix ++ unitPrefix used) ++
                [cell00, cell01] := by
          simpa only [List.append_assoc] using found
        rcases List.mem_append.mp membership with previous | added
        · exact prefixPacked symbol previous
        · simp only [List.mem_cons, List.not_mem_nil,
            or_false] at added
          rcases added with rfl | rfl
          · constructor
          · constructor
      have hTail :=
        ih (used + 1) (count + 1) nextPrefixPacked
      have prefixShape :
          sourcePrefix ++ [cell00, cell01] =
            basePrefix ++ unitPrefix (used + 1) := by
        dsimp only [sourcePrefix]
        rw [unitPrefix_append_succ]
        simp only [List.append_assoc]
      have scratchShape :
          scratchWord count (remaining + 1 + 1)
              reserve outsideLeft =
            scratchWord count 2
              (List.replicate remaining WorkSymbol.blank ++
                reserve)
              outsideLeft := by
        have blanks :
            List.replicate (remaining + 1 + 1)
                WorkSymbol.blank =
              List.replicate 2 WorkSymbol.blank ++
                List.replicate remaining WorkSymbol.blank := by
          rw [show remaining + 1 + 1 = 2 + remaining by omega]
          exact replicate_add 2 remaining WorkSymbol.blank
        simp only [scratchWord, blanks, List.append_assoc]
      have nextScratchShape :
          scratchWord (count + 1) 1
              (List.replicate remaining WorkSymbol.blank ++
                reserve)
              outsideLeft =
            scratchWord (count + 1) (remaining + 1)
              reserve outsideLeft := by
        have blanks :
            List.replicate (remaining + 1)
                WorkSymbol.blank =
              List.replicate 1 WorkSymbol.blank ++
                List.replicate remaining WorkSymbol.blank := by
          rw [show remaining + 1 = 1 + remaining by omega]
          exact replicate_add 1 remaining WorkSymbol.blank
        simp only [scratchWord, blanks, List.append_assoc]
      have hIterationCanonical :
          workRunExact? (machine kind.sourceKind)
              (unitIterationSteps sourcePrefix.length count)
              (configAtWord natFirstState
                (sourcePrefix.reverse ++
                  sourceLeftBoundary ::
                    scratchWord count (remaining + 1 + 1)
                      reserve outsideLeft)
                (cell00 :: cell01 ::
                  (SourceParser.natCells remaining ++ after))) =
            some
              (configAtWord natFirstState
                ((basePrefix ++ unitPrefix (used + 1)).reverse ++
                  sourceLeftBoundary ::
                    scratchWord (count + 1) (remaining + 1)
                      reserve outsideLeft)
                (SourceParser.natCells remaining ++ after)) := by
        simpa only [scratchShape, prefixShape, nextScratchShape] using
          hIteration
      have hTailCanonical :
          workRunExact? (machine kind.sourceKind)
              (natLoopSteps
                (basePrefix ++ unitPrefix (used + 1)).length
                (count + 1) remaining)
              (configAtWord natFirstState
                ((basePrefix ++ unitPrefix (used + 1)).reverse ++
                  sourceLeftBoundary ::
                    scratchWord (count + 1) (remaining + 1)
                      reserve outsideLeft)
                (SourceParser.natCells remaining ++ after)) =
            some
              (configAtWord acceptState
                (sourceLeftBoundary ::
                  scratchWord (count + 1 + remaining) 1
                    reserve outsideLeft)
                (basePrefix ++ unitPrefix (used + 1 + remaining) ++
                  [cell00, cursorMarker] ++ after)) := by
        exact hTail
      have all := exactRun_add kind.sourceKind
        (unitIterationSteps sourcePrefix.length count)
        (natLoopSteps
          (basePrefix ++ unitPrefix (used + 1)).length
          (count + 1) remaining)
        _ _ _ hIterationCanonical hTailCanonical
      have finalCount :
          count + 1 + remaining =
            count + (remaining + 1) := by
        omega
      have finalUsed :
          used + 1 + remaining =
            used + (remaining + 1) := by
        omega
      have nextPrefixLength :
          (basePrefix ++ unitPrefix (used + 1)).length =
            (basePrefix ++ unitPrefix used).length + 2 := by
        simp only [List.length_append, unitPrefix_length]
        omega
      rw [finalCount] at all
      rw [finalUsed, nextPrefixLength] at all
      simpa [natLoopSteps, sourcePrefix,
        SourceParser.natCells,
        SourceParser.cell00, SourceParser.cell01,
        cell00, cell01,
        List.append_assoc, Nat.add_assoc] using all

def naturalWorkSteps
    (beforeLength scratch value : Nat) : Nat :=
  2 + natLoopSteps (beforeLength + 2) scratch value

private theorem nat_source_exact
    (kind : NatKind) (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine kind.sourceKind)
        (naturalWorkSteps before.length scratch value)
        (entryConfiguration kind.sourceKind value scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration kind.sourceKind value scratch
          before after reserve outsideLeft) := by
  let tag : List WorkSymbol :=
    [firstCell kind.sourceKind, secondCell kind.sourceKind]
  let basePrefix := before ++ tag
  have hFirst :
      workRunExact? (machine kind.sourceKind) 1
          (entryConfiguration kind.sourceKind value scratch
            before after reserve outsideLeft) =
        some
          (configAtWord tagSecondState
            (firstCell kind.sourceKind :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch (value + 1)
                  reserve outsideLeft)
            (secondCell kind.sourceKind ::
              SourceParser.natCells value ++ after)) := by
    apply exactRun_one
    cases kind <;> rfl
  have hSecond :
      workRunExact? (machine kind.sourceKind) 1
          (configAtWord tagSecondState
            (firstCell kind.sourceKind :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch (value + 1)
                  reserve outsideLeft)
            (secondCell kind.sourceKind ::
              SourceParser.natCells value ++ after)) =
        some
          (configAtWord natFirstState
            (basePrefix.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch (value + 1)
                  reserve outsideLeft)
            (SourceParser.natCells value ++ after)) := by
    have raw :
        workRunExact? (machine kind.sourceKind) 1
            (configAtWord tagSecondState
              (firstCell kind.sourceKind :: before.reverse ++
                sourceLeftBoundary ::
                  scratchWord scratch (value + 1)
                    reserve outsideLeft)
              (secondCell kind.sourceKind ::
                SourceParser.natCells value ++ after)) =
          some
            (configAtWord natFirstState
              (secondCell kind.sourceKind ::
                firstCell kind.sourceKind :: before.reverse ++
                  sourceLeftBoundary ::
                    scratchWord scratch (value + 1)
                      reserve outsideLeft)
              (SourceParser.natCells value ++ after)) := by
      apply exactRun_one
      cases kind <;> rfl
    simpa [basePrefix, tag] using raw
  have basePacked :
      ∀ symbol, symbol ∈ basePrefix →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    simp only [basePrefix, List.mem_append] at found
    rcases found with fromBefore | fromTag
    · exact beforePacked symbol fromBefore
    · cases kind <;>
        simp [tag, firstCell, secondCell,
          cell00, cell01, cell10, cell11] at fromTag
      all_goals
        rcases fromTag with rfl | rfl <;> constructor
  have hLoop :=
    nat_loop_exact kind basePrefix 0 scratch value
      after reserve outsideLeft
      (by simpa [unitPrefix] using basePacked)
  have hLoopCanonical :
      workRunExact? (machine kind.sourceKind)
          (natLoopSteps basePrefix.length scratch value)
          (configAtWord natFirstState
            (basePrefix.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch (value + 1)
                  reserve outsideLeft)
            (SourceParser.natCells value ++ after)) =
        some
          (configAtWord acceptState
            (sourceLeftBoundary ::
              scratchWord (scratch + value) 1
                reserve outsideLeft)
            (basePrefix ++ unitPrefix value ++
              [cell00, cursorMarker] ++ after)) := by
    simpa [unitPrefix] using hLoop
  have h01 := exactRun_add kind.sourceKind 1 1 _ _ _ hFirst hSecond
  have all := exactRun_add kind.sourceKind 2
    (natLoopSteps basePrefix.length scratch value)
    _ _ _ h01 hLoopCanonical
  have steps :
      2 + natLoopSteps basePrefix.length scratch value =
        naturalWorkSteps before.length scratch value := by
    simp [naturalWorkSteps, basePrefix, tag]
  rw [steps] at all
  cases kind <;>
    simpa [entryConfiguration, finalConfiguration,
      sourceCells, markedSourceCells, basePrefix, tag,
      NatKind.sourceKind, firstCell, secondCell,
      List.append_assoc,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using all

theorem input_exact
    (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine .input)
        (naturalWorkSteps before.length scratch value)
        (entryConfiguration .input value scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration .input value scratch
          before after reserve outsideLeft) :=
  nat_source_exact .input value scratch before after
    reserve outsideLeft beforePacked

theorem gate_exact
    (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine .gate)
        (naturalWorkSteps before.length scratch value)
        (entryConfiguration .gate value scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration .gate value scratch
          before after reserve outsideLeft) :=
  nat_source_exact .gate value scratch before after
    reserve outsideLeft beforePacked

def constantWorkSteps (beforeLength : Nat) : Nat :=
  beforeLength + 4

private def constantKind : Bool → SourceKind
  | false => .constantFalse
  | true => .constantTrue

private theorem constant_exact
    (value : Bool) (scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine (constantKind value))
        (constantWorkSteps before.length)
        (entryConfiguration (constantKind value) 0 scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration (constantKind value) 0 scratch
          before after reserve outsideLeft) := by
  let kind := constantKind value
  let first := firstCell kind
  have hFirst :
      workRunExact? (machine kind) 1
          (entryConfiguration kind 0 scratch
            before after reserve outsideLeft) =
        some
          (configAtWord tagSecondState
            (first :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch 1 reserve outsideLeft)
            (secondCell kind :: after)) := by
    apply exactRun_one
    cases value <;> rfl
  have hSecond :
      workRunExact? (machine kind) 1
          (configAtWord tagSecondState
            (first :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch 1 reserve outsideLeft)
            (secondCell kind :: after)) =
        some
          (configAtLeftWord rewindFinalState
            (first :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch 1 reserve outsideLeft)
            (cursorMarker :: after)) := by
    apply exactRun_one
    cases value <;> cases before <;> rfl
  have rewindPacked :
      ∀ symbol, symbol ∈ first :: before.reverse →
        TargetEmitter.PackedSymbol symbol := by
    intro symbol found
    simp only [List.mem_cons] at found
    rcases found with rfl | found
    · cases value <;> constructor
    · exact beforePacked symbol (List.mem_reverse.mp found)
  have hRewind :
      workRunExact? (machine kind) (before.length + 1)
          (configAtLeftWord rewindFinalState
            (first :: before.reverse ++
              sourceLeftBoundary ::
                scratchWord scratch 1 reserve outsideLeft)
            (cursorMarker :: after)) =
        some
          (configAtLeftWord rewindFinalState
            (sourceLeftBoundary ::
              scratchWord scratch 1 reserve outsideLeft)
            (before ++ [first, cursorMarker] ++ after)) := by
    have scanned := scanLeftExact kind rewindFinalState
      TargetEmitter.PackedSymbol
      (fun head left right packed =>
        rewind_final_packed_step kind head packed left right)
      (first :: before.reverse)
      (sourceLeftBoundary ::
        scratchWord scratch 1 reserve outsideLeft)
      (cursorMarker :: after) rewindPacked
    simpa [pushLeft_eq_reverse_append, List.append_assoc] using scanned
  have hBoundary := rewind_final_boundary_step kind
    (scratchWord scratch 1 reserve outsideLeft)
    (before ++ [first, cursorMarker] ++ after)
  have h01 := exactRun_add kind 1 1 _ _ _ hFirst hSecond
  have h02 := exactRun_add kind 2 (before.length + 1)
    _ _ _ h01 hRewind
  have all := exactRun_add kind
    (2 + (before.length + 1)) 1 _ _ _ h02 hBoundary
  have steps :
      2 + (before.length + 1) + 1 =
        constantWorkSteps before.length := by
    unfold constantWorkSteps
    omega
  rw [steps] at all
  cases value <;>
    simpa [kind, first, constantKind,
      firstCell, cell01,
      entryConfiguration, finalConfiguration,
      sourceCells, markedSourceCells, scratchWord] using all

theorem constantFalse_exact
    (scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine .constantFalse)
        (constantWorkSteps before.length)
        (entryConfiguration .constantFalse 0 scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration .constantFalse 0 scratch
          before after reserve outsideLeft) :=
  constant_exact false scratch before after
    reserve outsideLeft beforePacked

theorem constantTrue_exact
    (scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol)
    (beforePacked :
      ∀ symbol, symbol ∈ before →
        TargetEmitter.PackedSymbol symbol) :
    workRunExact? (machine .constantTrue)
        (constantWorkSteps before.length)
        (entryConfiguration .constantTrue 0 scratch
          before after reserve outsideLeft) =
      some
        (finalConfiguration .constantTrue 0 scratch
          before after reserve outsideLeft) :=
  constant_exact true scratch before after
    reserve outsideLeft beforePacked

theorem final_halted
    (kind : SourceKind) (value scratch : Nat)
    (before after reserve outsideLeft : List WorkSymbol) :
    (machine kind).isHalted
      (finalConfiguration kind value scratch
        before after reserve outsideLeft) = true := by
  rfl

set_option maxRecDepth 100000 in
private theorem find_start_malformed
    (kind : SourceKind) (symbol : WorkSymbol)
    (malformed : symbol ≠ firstCell kind) :
    findWorkRule (rules kind) startState symbol =
      some
        { sourceState := startState
          readSymbol := symbol
          targetState := deadState
          writeSymbol := symbol
          move := .stay } := by
  rcases symbol with ⟨first, second⟩
  cases kind <;> cases first <;> cases second <;>
    simp_all [firstCell, cell00, cell01,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne]
  all_goals decide

theorem malformed_source_enters_dead
    (kind : SourceKind) (symbol : WorkSymbol)
    (left right : List WorkSymbol)
    (malformed : symbol ≠ firstCell kind) :
    workStep? (machine kind)
        (configAtWord startState left (symbol :: right)) =
      some
        (configAtWord deadState left (symbol :: right)) := by
  have notHalted :=
    controller_not_halted kind startState (Or.inl rfl)
      (configAtWord startState left (symbol :: right)).tape
  calc
    workStep? (machine kind)
        (configAtWord startState left (symbol :: right)) =
      some
        (applyWorkRule
          { sourceState := startState
            readSymbol := symbol
            targetState := deadState
            writeSymbol := symbol
            move := .stay }
          (configAtWord startState left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _ notHalted
        (find_start_malformed kind symbol malformed)
    _ = some
        (configAtWord deadState left (symbol :: right)) := by
      rfl

theorem dead_stuck (kind : SourceKind) (tape : WorkTape) :
    workStep? (machine kind)
      { state := deadState, tape := tape } = none := by
  have notHalted :
      (machine kind).isHalted
        { state := deadState, tape := tape } = false := by
    rfl
  unfold workStep?
  rw [notHalted]
  change
    (match findWorkRule (rules kind) deadState tape.head with
     | none => none
     | some rule =>
         some (applyWorkRule rule
           { state := deadState, tape := tape })) = none
  rw [no_rule_at_dead]

end PNP.Concrete.LockedNAND.TargetEmitterSourceCapture
