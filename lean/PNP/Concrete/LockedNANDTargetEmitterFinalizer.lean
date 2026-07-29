/-
Copyright (c) 2026 PNP Labs.

Literal terminal cleanup for the strict-v0 locked-NAND target emitter.

The controller retains the packed source to the left of the growing packed
target while it constructs that target.  This five-rule machine erases the
retained source and its contextual source/target boundary, then halts with the
first target cell under the head.  The ordinary compiled output convention
therefore observes the target and no controller workspace.
-/

import PNP.Concrete.LockedNANDTargetEmitterMachine

namespace PNP.Concrete.LockedNAND.TargetEmitterFinalizer

open TargetEmitter

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

/-- Four packed-source erasers and one boundary eraser.  Every other symbol
is ruleless and hence fail-closed. -/
def rules : List WorkRule :=
  [ eraseRule WorkSymbol.zeroZero eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.zeroOne eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.oneZero eraseState WorkSymbol.blank .right
  , eraseRule WorkSymbol.oneOne eraseState WorkSymbol.blank .right
  , eraseRule sourceTargetBoundary acceptState WorkSymbol.blank .right
  ]

def machine : WorkMachine :=
  { rules := rules
    startState := eraseState
    acceptState := acceptState
    rejectState := rejectState }

def compiledMachine : Machine :=
  compileWorkMachine machine

theorem rules_length : rules.length = 5 := by
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

private theorem packed_step (symbol : WorkSymbol)
    (ordinary : PackedSymbol symbol)
    (left suffix : List WorkSymbol) :
    workStep? machine
        (configurationAtWord eraseState left (symbol :: suffix)) =
      some
        (configurationAtWord eraseState
          (WorkSymbol.blank :: left) suffix) := by
  cases ordinary <;> rfl

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
    (packed : ∀ symbol, symbol ∈ source → PackedSymbol symbol) :
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
      have headPacked : PackedSymbol head :=
        packed head (List.Mem.head rest)
      have restPacked :
          ∀ symbol, symbol ∈ rest → PackedSymbol symbol := by
        intro symbol member
        exact packed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configurationAtWord eraseState left
              (head :: (rest ++ suffix))) with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      rw [packed_step head headPacked left (rest ++ suffix)]
      change
        workRunExact? machine rest.length
            (configurationAtWord eraseState
              (WorkSymbol.blank :: left) (rest ++ suffix)) = _
      rw [ih (WorkSymbol.blank :: left) restPacked]
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
             | some next => workRunExact? machine (first + second) next) =
              some final
          rw [hStep]
          exact ih next hTail

/-- Every packed retained source is erased and the first packed target cell
becomes the observable focus in exactly `source.length + 1` work steps. -/
theorem finalize_exact
    (source target outsideLeft outsideRight : List WorkSymbol)
    (packed : ∀ symbol, symbol ∈ source → PackedSymbol symbol) :
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
          (sourceLeftBoundary :: outsideLeft) packed
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

private theorem encodeWorkRight_tokenCells (token : Token) :
    encodeWorkRight (SourceParser.tokenCells token) =
      token.bits.map TapeSymbol.ofBool := by
  cases token <;> rfl

private theorem encodeWorkRight_packedTokenCells
    (tokens : List Token) :
    encodeWorkRight (SourceParser.packedTokenCells tokens) =
      (encodeTokens tokens).map TapeSymbol.ofBool := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest ih =>
      simp only [SourceParser.packedTokenCells, encodeTokens]
      rw [encodeWorkRight_append, encodeWorkRight_tokenCells,
        List.map_append, ih]

private theorem final_output_of_nonempty
    (source : List WorkSymbol) (head : WorkSymbol)
    (rest outsideLeft outsideRight : List WorkSymbol)
    (bits : BitString)
    (encoded :
      encodeWorkRight (head :: rest) =
        bits.map TapeSymbol.ofBool) :
    (encodeWorkTape
      (finalTape source (head :: rest)
        outsideLeft outsideRight)).outputBits = bits := by
  unfold finalTape
  change Tape.decodeOutputCells
      (head.first :: head.second ::
        encodeWorkRight
          (rest ++ WorkSymbol.blank :: outsideRight)) = bits
  rw [encodeWorkRight_append]
  change Tape.decodeOutputCells
      (encodeWorkRight (head :: rest) ++
        encodeWorkRight (WorkSymbol.blank :: outsideRight)) = bits
  rw [encoded]
  change Tape.decodeOutputCells
      (bits.map TapeSymbol.ofBool ++
        TapeSymbol.blank :: TapeSymbol.blank ::
          encodeWorkRight outsideRight) = bits
  exact Tape.decodeOutputCells_append_blank bits
    (TapeSymbol.blank :: encodeWorkRight outsideRight)

/-- The final focused packed token word is read as exactly the strict-v0 raw
bitstring, independently of every erased source/workspace cell to its left. -/
theorem final_output_eq (source : List WorkSymbol)
    (tokens : List Token) (outsideLeft outsideRight : List WorkSymbol) :
    (encodeWorkTape
      (finalTape source (SourceParser.packedTokenCells tokens)
        outsideLeft outsideRight)).outputBits =
      encodeTokens tokens := by
  cases tokens with
  | nil =>
      rfl
  | cons token rest =>
      have encoded :=
        encodeWorkRight_packedTokenCells (token :: rest)
      cases token <;>
        apply final_output_of_nonempty <;>
        simpa [SourceParser.packedTokenCells,
          SourceParser.tokenCells] using encoded

theorem final_isHalted
    (source target outsideLeft outsideRight : List WorkSymbol) :
    machine.isHalted
      (finalConfiguration source target outsideLeft outsideRight) = true := by
  rfl

/-- A nonpacked source cell has no erasing transition and therefore cannot
silently reach the output focus. -/
theorem malformed_source_stuck
    (left right : List WorkSymbol) :
    workStep? machine
        (configurationAtWord eraseState left
          (WorkSymbol.zeroBlank :: right)) = none := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterFinalizer
