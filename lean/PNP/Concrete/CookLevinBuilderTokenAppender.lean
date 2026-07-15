/-
Copyright (c) 2026 PNP Labs.

A literal state-selected CNF-token appender for the concrete Cook--Levin
builder.  The fixed finite rule table appends one requested token to the
workspace beyond the already-proved unary input-length tally and restores the
logical input focus.  Its distinguished start state requests the first header
token `CNFToken.t`.

This is an internal builder stage.  It is not yet composed with the input
prefix, does not compute the remaining formula header or interpret a dynamic
formula cursor, and supplies no complete formula builder, RawRefinement,
polynomial reduction, complexity-class result, or P-equals-NP theorem.
-/

import PNP.Concrete.CookLevinBuilderInputPrefix
import PNP.Concrete.CookLevinFormulaCursor

namespace PNP.Concrete

namespace CookLevin

namespace BuilderTokenAppender

open PipelineTape

/-! ### Canonical token and workspace encoding -/

/-- The four concrete CNF tokens in their reviewed rule-generation order. -/
def allTokens : List CNFToken := [.f, .t, .sep, .finish]

/-- Fixed state code for one token request. -/
def tokenCode : CNFToken → Nat
  | .f => 0
  | .t => 1
  | .sep => 2
  | .finish => 3

theorem tokenCode_injective : Function.Injective tokenCode := by
  intro left right h
  cases left <;> cases right <;> first | rfl | contradiction

/-- One work cell is exactly the raw two-bit encoding of one CNF token. -/
def tokenSymbol : CNFToken → WorkSymbol
  | .f => WorkSymbol.zeroZero
  | .t => WorkSymbol.oneOne
  | .sep => WorkSymbol.zeroOne
  | .finish => WorkSymbol.oneZero

theorem tokenSymbol_injective : Function.Injective tokenSymbol := by
  intro left right h
  cases left <;> cases right <;> first | rfl | contradiction

theorem tokenSymbol_bits (token : CNFToken) :
    [(tokenSymbol token).first, (tokenSymbol token).second] =
      token.bits.map TapeSymbol.ofBool := by
  cases token <;> rfl

/-- A phase-local delimiter between the unary tally and emitted tokens.
It deliberately reuses the left-marker symbol; control state distinguishes
the two locations. -/
def outputBoundarySymbol : WorkSymbol := WorkSymbol.blankZero

theorem outputBoundarySymbol_ne_tokenSymbol (token : CNFToken) :
    outputBoundarySymbol ≠ tokenSymbol token := by
  cases token <;> decide

theorem outputBoundarySymbol_ne_tallySymbol :
    outputBoundarySymbol ≠ BuilderInputLength.tallySymbol := by decide

theorem outputBoundarySymbol_ne_rightMarker :
    outputBoundarySymbol ≠ rightMarker := by decide

def tokenSymbols (tokens : List CNFToken) : List WorkSymbol :=
  tokens.map tokenSymbol

@[simp] theorem tokenSymbols_length (tokens : List CNFToken) :
    (tokenSymbols tokens).length = tokens.length := by
  simp [tokenSymbols]

@[simp] theorem tokenSymbols_append (left right : List CNFToken) :
    tokenSymbols (left ++ right) = tokenSymbols left ++ tokenSymbols right := by
  simp [tokenSymbols]

@[simp] theorem tokenSymbols_reverse (tokens : List CNFToken) :
    tokenSymbols tokens.reverse = (tokenSymbols tokens).reverse := by
  simp [tokenSymbols]

/-- The empty builder output has no materialized delimiter, making it exactly
the preceding tally endpoint.  The first append creates the delimiter. -/
def outputRegion : List CNFToken → List WorkSymbol
  | [] => []
  | tokens => outputBoundarySymbol :: tokenSymbols tokens

def workspaceTape (input : BitString) (outsideLeft : List WorkSymbol)
    (output : List CNFToken) : WorkTape :=
  frameWithGarbage (Tape.ofInput input) outsideLeft
    (List.replicate input.length BuilderInputLength.tallySymbol ++
      outputRegion output)

theorem workspaceTape_empty_eq_builderInputLength_finalTape
    (input : BitString) (outsideLeft : List WorkSymbol) :
    workspaceTape input outsideLeft [] =
      BuilderInputLength.finalTape input outsideLeft := by
  simp [workspaceTape, outputRegion, BuilderInputLength.finalTape]

theorem workspaceTape_represents (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    Represents (Tape.ofInput input) (workspaceTape input outsideLeft output) := by
  exact frameWithGarbage_represents _ _ _

/-! ### Fixed finite state and rule table -/

def seekInputState (token : CNFToken) : Nat := tokenCode token
def seekTallyState (token : CNFToken) : Nat := 4 + tokenCode token
def seekOutputState (token : CNFToken) : Nat := 8 + tokenCode token
def rewindOutputState : Nat := 12
def rewindTallyState : Nat := 13
def rewindInputState : Nat := 14
def acceptState : Nat := 15
def rejectState : Nat := 16

def keepRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := read
    move := move }

def writeRule (source : Nat) (read : WorkSymbol) (target : Nat)
    (write : WorkSymbol) (move : HeadMove) : WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

/-- Twelve rules for one requested token: scan the represented input, scan
the unary tally, scan the existing token output, then append the selected
token. -/
def tokenRules (token : CNFToken) : List WorkRule :=
  [keepRule (seekInputState token) WorkSymbol.blank
      (seekInputState token) .right,
   keepRule (seekInputState token) WorkSymbol.zeroBlank
      (seekInputState token) .right,
   keepRule (seekInputState token) WorkSymbol.oneBlank
      (seekInputState token) .right,
   keepRule (seekInputState token) rightMarker
      (seekTallyState token) .right,
   keepRule (seekTallyState token) BuilderInputLength.tallySymbol
      (seekTallyState token) .right,
   keepRule (seekTallyState token) outputBoundarySymbol
      (seekOutputState token) .right,
   writeRule (seekTallyState token) WorkSymbol.blank
      (seekOutputState token) outputBoundarySymbol .right,
   keepRule (seekOutputState token) (tokenSymbol .f)
      (seekOutputState token) .right,
   keepRule (seekOutputState token) (tokenSymbol .t)
      (seekOutputState token) .right,
   keepRule (seekOutputState token) (tokenSymbol .sep)
      (seekOutputState token) .right,
   keepRule (seekOutputState token) (tokenSymbol .finish)
      (seekOutputState token) .right,
   writeRule (seekOutputState token) WorkSymbol.blank rewindOutputState
      (tokenSymbol token) .left]

/-- Eleven shared rewind rules restore the logical input focus. -/
def rewindRules : List WorkRule :=
  [keepRule rewindOutputState (tokenSymbol .f) rewindOutputState .left,
   keepRule rewindOutputState (tokenSymbol .t) rewindOutputState .left,
   keepRule rewindOutputState (tokenSymbol .sep) rewindOutputState .left,
   keepRule rewindOutputState (tokenSymbol .finish) rewindOutputState .left,
   keepRule rewindOutputState outputBoundarySymbol rewindTallyState .left,
   keepRule rewindTallyState BuilderInputLength.tallySymbol
      rewindTallyState .left,
   keepRule rewindTallyState rightMarker rewindInputState .left,
   keepRule rewindInputState WorkSymbol.blank rewindInputState .left,
   keepRule rewindInputState WorkSymbol.zeroBlank rewindInputState .left,
   keepRule rewindInputState WorkSymbol.oneBlank rewindInputState .left,
   keepRule rewindInputState leftMarker acceptState .right]

/-- Literal 59-rule table.  Its construction ranges over the fixed four-token
alphabet only; neither the source input nor a formula is executable program
data. -/
def rules : List WorkRule :=
  allTokens.flatMap tokenRules ++ rewindRules

def machine : WorkMachine :=
  { rules := rules
    startState := seekInputState .t
    acceptState := acceptState
    rejectState := rejectState }

theorem rules_length : rules.length = 59 := by rfl

theorem rules_pairwise_query_distinct :
    rules.Pairwise (fun left right =>
      (left.sourceState, left.readSymbol) ≠
        (right.sourceState, right.readSymbol)) := by
  decide

theorem machine_acceptState_ne_rejectState :
    machine.acceptState ≠ machine.rejectState := by decide

/-! ### Exact configurations and costs -/

def entryConfiguration (token : CNFToken) (tape : WorkTape) :
    WorkConfiguration :=
  { state := seekInputState token, tape := tape }

def finalConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    WorkConfiguration :=
  { state := machine.acceptState
    tape := workspaceTape input outsideLeft output }

/-- The empty raw input still materializes one blank logical source cell. -/
def sourceCellCount (input : BitString) : Nat := Nat.max 1 input.length

theorem sourceCellCount_positive (input : BitString) :
    0 < sourceCellCount input := by
  unfold sourceCellCount
  exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

theorem sourceCellCount_le (input : BitString) :
    sourceCellCount input ≤ input.length + 1 := by
  unfold sourceCellCount
  exact (Nat.max_le).2 ⟨by omega, by omega⟩

/-- Exact one-way scan or rewind cost. -/
def halfSteps (input : BitString) (output : List CNFToken) : Nat :=
  sourceCellCount input + input.length + output.length + 3

/-- Exact work cost for appending one token to an existing output. -/
def workSteps (input : BitString) (output : List CNFToken) : Nat :=
  2 * halfSteps input output

/-- External raw bound for the distinguished first `T` token. -/
def firstTokenRawTimeBound : NatPolynomial := .linear 24 48

/-! ### Exact scan and rewind infrastructure -/

private def bitSymbol (bit : Bool) : WorkSymbol :=
  dataSymbol (TapeSymbol.ofBool bit)

private def bitSymbols (bits : BitString) : List WorkSymbol :=
  bits.map bitSymbol

/-- Materialized represented-input cells, including the focused blank used by
the empty raw input. -/
def sourceSymbols : BitString → List WorkSymbol
  | [] => [WorkSymbol.blank]
  | first :: rest => bitSymbols (first :: rest)

theorem sourceSymbols_length (input : BitString) :
    (sourceSymbols input).length = sourceCellCount input := by
  cases input with
  | nil => rfl
  | cons first rest =>
      simp [sourceSymbols, sourceCellCount, bitSymbols]

private theorem bitSymbols_length (bits : BitString) :
    (bitSymbols bits).length = bits.length := by
  simp [bitSymbols]

private theorem bitSymbols_append (left right : BitString) :
    bitSymbols (left ++ right) = bitSymbols left ++ bitSymbols right := by
  simp [bitSymbols]

private theorem bitSymbols_reverse (bits : BitString) :
    bitSymbols bits.reverse = (bitSymbols bits).reverse := by
  simp [bitSymbols]

private theorem replicate_cons_comm (count : Nat) (value : α)
    (tail : List α) :
    List.replicate count value ++ value :: tail =
      value :: (List.replicate count value ++ tail) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, List.cons_append]
      exact congrArg (List.cons value) ih

private def tapeAtWord (leftSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := leftSide, head := WorkSymbol.blank, right := [] }
  | head :: rest => { left := leftSide, head := head, right := rest }

private def tapeAtLeftWord (rightSide : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := WorkSymbol.blank, right := rightSide }
  | head :: rest => { left := rest, head := head, right := rightSide }

private theorem workRunExact_compose (first second : Nat)
    (start middle final : WorkConfiguration)
    (hFirst : workRunExact? machine first start = some middle)
    (hSecond : workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) start = some final := by
  induction first generalizing start with
  | zero =>
      change some start = some middle at hFirst
      have hStart : start = middle := Option.some.inj hFirst
      simpa [hStart] using hSecond
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
               | some result => workRunExact? machine first result) =
                some middle at hFirst
            rw [hStep] at hFirst
            exact hFirst
          rw [Nat.succ_add]
          change
            (match workStep? machine start with
             | none => none
             | some result => workRunExact? machine (first + second) result) =
              some final
          rw [hStep]
          exact ih next hTail

private theorem workRunExact_one (start next : WorkConfiguration)
    (hStep : workStep? machine start = some next) :
    workRunExact? machine 1 start = some next := by
  change
    (match workStep? machine start with
     | none => none
     | some result => some result) = some next
  rw [hStep]

private theorem step_seekInput_bit (request : CNFToken) (bit : Bool)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekInputState request
          tape :=
            { left := leftSide
              head := bitSymbol bit
              right := rightSide } } =
      some
        { state := seekInputState request
          tape := tapeAtWord (bitSymbol bit :: leftSide) rightSide } := by
  cases request <;> cases bit <;> rfl

private theorem seekInput_bits_exact (request : CNFToken)
    (bits : BitString) (leftSide suffix : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := seekInputState request
          tape := tapeAtWord leftSide (bitSymbols bits ++ suffix) } =
      some
        { state := seekInputState request
          tape := tapeAtWord ((bitSymbols bits).reverse ++ leftSide) suffix } := by
  induction bits generalizing leftSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := step_seekInput_bit request bit leftSide
        (bitSymbols rest ++ suffix)
      change workRunExact? machine (rest.length + 1)
          { state := seekInputState request
            tape := tapeAtWord leftSide
              (bitSymbol bit :: (bitSymbols rest ++ suffix)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := seekInputState request
            tape := tapeAtWord leftSide
              (bitSymbol bit :: (bitSymbols rest ++ suffix)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtWord]
      rw [hStep]
      simp only
      rw [ih (bitSymbol bit :: leftSide)]
      cases suffix <;> simp [tapeAtWord, bitSymbols]

private theorem seekInput_source_exact (request : CNFToken)
    (input : BitString) (leftSide suffix : List WorkSymbol) :
    workRunExact? machine (sourceSymbols input).length
        { state := seekInputState request
          tape := tapeAtWord leftSide (sourceSymbols input ++ suffix) } =
      some
        { state := seekInputState request
          tape := tapeAtWord ((sourceSymbols input).reverse ++ leftSide)
            suffix } := by
  cases input with
  | nil =>
      cases request <;> cases suffix <;> rfl
  | cons first rest =>
      simpa [sourceSymbols, bitSymbols_length] using
        (seekInput_bits_exact request (first :: rest) leftSide suffix)

private theorem step_seekInput_rightMarker (request : CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekInputState request
          tape :=
            { left := leftSide
              head := rightMarker
              right := rightSide } } =
      some
        { state := seekTallyState request
          tape := tapeAtWord (rightMarker :: leftSide) rightSide } := by
  cases request <;> rfl

private theorem step_seekTally_symbol (request : CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekTallyState request
          tape :=
            { left := leftSide
              head := BuilderInputLength.tallySymbol
              right := rightSide } } =
      some
        { state := seekTallyState request
          tape := tapeAtWord
            (BuilderInputLength.tallySymbol :: leftSide) rightSide } := by
  cases request <;> rfl

private theorem seekTally_exact (request : CNFToken) (count : Nat)
    (leftSide suffix : List WorkSymbol) :
    workRunExact? machine count
        { state := seekTallyState request
          tape := tapeAtWord leftSide
            (List.replicate count BuilderInputLength.tallySymbol ++ suffix) } =
      some
        { state := seekTallyState request
          tape := tapeAtWord
            (List.replicate count BuilderInputLength.tallySymbol ++ leftSide)
            suffix } := by
  induction count generalizing leftSide with
  | zero => rfl
  | succ count ih =>
      have hStep := step_seekTally_symbol request leftSide
        (List.replicate count BuilderInputLength.tallySymbol ++ suffix)
      change workRunExact? machine (count + 1)
          { state := seekTallyState request
            tape := tapeAtWord leftSide
              (BuilderInputLength.tallySymbol ::
                (List.replicate count BuilderInputLength.tallySymbol ++
                  suffix)) } = _
      rw [show count + 1 = Nat.succ count by omega]
      change
        (match workStep? machine
          { state := seekTallyState request
            tape := tapeAtWord leftSide
              (BuilderInputLength.tallySymbol ::
                (List.replicate count BuilderInputLength.tallySymbol ++
                  suffix)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      simp only [tapeAtWord]
      rw [hStep]
      simp only
      rw [ih (BuilderInputLength.tallySymbol :: leftSide)]
      rw [replicate_cons_comm]
      cases suffix <;> simp [tapeAtWord, List.replicate_succ]

private theorem step_seekOutput_token (request scanned : CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := seekOutputState request
          tape :=
            { left := leftSide
              head := tokenSymbol scanned
              right := rightSide } } =
      some
        { state := seekOutputState request
          tape := tapeAtWord (tokenSymbol scanned :: leftSide) rightSide } := by
  cases request <;> cases scanned <;> rfl

private theorem seekOutput_tokens_exact (request : CNFToken)
    (tokens : List CNFToken) (leftSide suffix : List WorkSymbol) :
    workRunExact? machine tokens.length
        { state := seekOutputState request
          tape := tapeAtWord leftSide (tokenSymbols tokens ++ suffix) } =
      some
        { state := seekOutputState request
          tape := tapeAtWord ((tokenSymbols tokens).reverse ++ leftSide)
            suffix } := by
  induction tokens generalizing leftSide with
  | nil => rfl
  | cons token rest ih =>
      have hStep := step_seekOutput_token request token leftSide
        (tokenSymbols rest ++ suffix)
      change workRunExact? machine (rest.length + 1)
          { state := seekOutputState request
            tape := tapeAtWord leftSide
              (tokenSymbol token :: (tokenSymbols rest ++ suffix)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := seekOutputState request
            tape := tapeAtWord leftSide
              (tokenSymbol token :: (tokenSymbols rest ++ suffix)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtWord]
      rw [hStep]
      simp only
      rw [ih (tokenSymbol token :: leftSide)]
      cases suffix <;> simp [tapeAtWord, tokenSymbols]

private theorem step_rewindOutput_token (token : CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindOutputState
          tape :=
            { left := leftSide
              head := tokenSymbol token
              right := rightSide } } =
      some
        { state := rewindOutputState
          tape := tapeAtLeftWord (tokenSymbol token :: rightSide) leftSide } := by
  cases token <;> rfl

private theorem rewindOutput_scan_exact (tokens : List CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine tokens.length
        { state := rewindOutputState
          tape := tapeAtLeftWord rightSide
            (tokenSymbols tokens ++ leftSide) } =
      some
        { state := rewindOutputState
          tape := tapeAtLeftWord
            (tokenSymbols tokens.reverse ++ rightSide) leftSide } := by
  induction tokens generalizing rightSide with
  | nil => rfl
  | cons token rest ih =>
      have hStep := step_rewindOutput_token token
        (tokenSymbols rest ++ leftSide) rightSide
      change workRunExact? machine (rest.length + 1)
          { state := rewindOutputState
            tape := tapeAtLeftWord rightSide
              (tokenSymbol token :: (tokenSymbols rest ++ leftSide)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := rewindOutputState
            tape := tapeAtLeftWord rightSide
              (tokenSymbol token :: (tokenSymbols rest ++ leftSide)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (tokenSymbol token :: rightSide)]
      cases leftSide <;>
        simp [tapeAtLeftWord, tokenSymbols, List.append_assoc]

private theorem rewindOutput_tokens_exact (tokens : List CNFToken)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine tokens.length
        { state := rewindOutputState
          tape := tapeAtLeftWord rightSide
            ((tokenSymbols tokens).reverse ++ leftSide) } =
      some
        { state := rewindOutputState
          tape := tapeAtLeftWord
            (tokenSymbols tokens ++ rightSide) leftSide } := by
  simpa [tokenSymbols_length] using
    (rewindOutput_scan_exact tokens.reverse leftSide rightSide)

private theorem step_rewindTally_symbol
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindTallyState
          tape :=
            { left := leftSide
              head := BuilderInputLength.tallySymbol
              right := rightSide } } =
      some
        { state := rewindTallyState
          tape := tapeAtLeftWord
            (BuilderInputLength.tallySymbol :: rightSide) leftSide } := by
  rfl

private theorem rewindTally_exact (count : Nat)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine count
        { state := rewindTallyState
          tape := tapeAtLeftWord rightSide
            (List.replicate count BuilderInputLength.tallySymbol ++ leftSide) } =
      some
        { state := rewindTallyState
          tape := tapeAtLeftWord
            (List.replicate count BuilderInputLength.tallySymbol ++ rightSide)
            leftSide } := by
  induction count generalizing rightSide with
  | zero => rfl
  | succ count ih =>
      have hStep := step_rewindTally_symbol
        (List.replicate count BuilderInputLength.tallySymbol ++ leftSide)
        rightSide
      change workRunExact? machine (count + 1)
          { state := rewindTallyState
            tape := tapeAtLeftWord rightSide
              (BuilderInputLength.tallySymbol ::
                (List.replicate count BuilderInputLength.tallySymbol ++
                  leftSide)) } = _
      rw [show count + 1 = Nat.succ count by omega]
      change
        (match workStep? machine
          { state := rewindTallyState
            tape := tapeAtLeftWord rightSide
              (BuilderInputLength.tallySymbol ::
                (List.replicate count BuilderInputLength.tallySymbol ++
                  leftSide)) } with
         | none => none
         | some next => workRunExact? machine count next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (BuilderInputLength.tallySymbol :: rightSide)]
      rw [replicate_cons_comm]
      cases leftSide <;> simp [tapeAtLeftWord, List.replicate_succ]

private theorem step_rewindInput_bit (bit : Bool)
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindInputState
          tape :=
            { left := leftSide
              head := bitSymbol bit
              right := rightSide } } =
      some
        { state := rewindInputState
          tape := tapeAtLeftWord (bitSymbol bit :: rightSide) leftSide } := by
  cases bit <;> rfl

private theorem rewindInput_scan_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := rewindInputState
          tape := tapeAtLeftWord rightSide (bitSymbols bits ++ leftSide) } =
      some
        { state := rewindInputState
          tape := tapeAtLeftWord
            (bitSymbols bits.reverse ++ rightSide) leftSide } := by
  induction bits generalizing rightSide with
  | nil => rfl
  | cons bit rest ih =>
      have hStep := step_rewindInput_bit bit
        (bitSymbols rest ++ leftSide) rightSide
      change workRunExact? machine (rest.length + 1)
          { state := rewindInputState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } = _
      rw [show rest.length + 1 = Nat.succ rest.length by omega]
      change
        (match workStep? machine
          { state := rewindInputState
            tape := tapeAtLeftWord rightSide
              (bitSymbol bit :: (bitSymbols rest ++ leftSide)) } with
         | none => none
         | some next => workRunExact? machine rest.length next) = _
      simp only [tapeAtLeftWord]
      rw [hStep]
      simp only
      rw [ih (bitSymbol bit :: rightSide)]
      cases leftSide <;>
        simp [tapeAtLeftWord, bitSymbols, List.append_assoc]

private theorem rewindInput_bits_exact (bits : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine bits.length
        { state := rewindInputState
          tape := tapeAtLeftWord rightSide
            ((bitSymbols bits).reverse ++ leftSide) } =
      some
        { state := rewindInputState
          tape := tapeAtLeftWord (bitSymbols bits ++ rightSide) leftSide } := by
  simpa [bitSymbols_length, bitSymbols_reverse] using
    (rewindInput_scan_exact bits.reverse leftSide rightSide)

private theorem rewindInput_source_exact (input : BitString)
    (leftSide rightSide : List WorkSymbol) :
    workRunExact? machine (sourceSymbols input).length
        { state := rewindInputState
          tape := tapeAtLeftWord rightSide
            ((sourceSymbols input).reverse ++ leftSide) } =
      some
        { state := rewindInputState
          tape := tapeAtLeftWord (sourceSymbols input ++ rightSide)
            leftSide } := by
  cases input with
  | nil =>
      cases leftSide <;> rfl
  | cons first rest =>
      simpa [sourceSymbols, bitSymbols_length] using
        (rewindInput_bits_exact (first :: rest) leftSide rightSide)

/-! ### Exact token append -/

private theorem workspaceTape_eq_sourceWord (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    workspaceTape input outsideLeft output =
      tapeAtWord (leftMarker :: outsideLeft)
        (sourceSymbols input ++
          rightMarker ::
            (List.replicate input.length BuilderInputLength.tallySymbol ++
              outputRegion output)) := by
  cases input with
  | nil =>
      simp [workspaceTape, frameWithGarbage, Tape.ofInput, sourceSymbols,
        Tape.blank, dataSymbol, WorkSymbol.blank, tapeAtWord]
  | cons first rest =>
      cases first <;>
        simp [workspaceTape, frameWithGarbage, Tape.ofInput, sourceSymbols,
          bitSymbols, bitSymbol, tapeAtWord, List.map_map,
          Function.comp_def]

private theorem step_enterOutput (request : CNFToken)
    (output : List CNFToken) (leftSide : List WorkSymbol) :
    workStep? machine
        { state := seekTallyState request
          tape := tapeAtWord leftSide (outputRegion output) } =
      some
        { state := seekOutputState request
          tape := tapeAtWord (outputBoundarySymbol :: leftSide)
            (tokenSymbols output) } := by
  cases output with
  | nil =>
      cases request <;> rfl
  | cons first rest =>
      cases request <;> cases first <;> rfl

private theorem step_appendToken (request : CNFToken)
    (leftSide : List WorkSymbol) :
    workStep? machine
        { state := seekOutputState request
          tape := tapeAtWord leftSide [] } =
      some
        { state := rewindOutputState
          tape := tapeAtLeftWord [tokenSymbol request] leftSide } := by
  cases request <;> cases leftSide <;> rfl

private theorem step_rewindOutput_boundary
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindOutputState
          tape :=
            { left := leftSide
              head := outputBoundarySymbol
              right := rightSide } } =
      some
        { state := rewindTallyState
          tape := tapeAtLeftWord (outputBoundarySymbol :: rightSide)
            leftSide } := by
  rfl

private theorem step_rewindTally_rightMarker
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindTallyState
          tape :=
            { left := leftSide
              head := rightMarker
              right := rightSide } } =
      some
        { state := rewindInputState
          tape := tapeAtLeftWord (rightMarker :: rightSide) leftSide } := by
  rfl

private theorem step_rewindInput_leftMarker
    (leftSide rightSide : List WorkSymbol) :
    workStep? machine
        { state := rewindInputState
          tape :=
            { left := leftSide
              head := leftMarker
              right := rightSide } } =
      some
        { state := acceptState
          tape := tapeAtWord (leftMarker :: leftSide) rightSide } := by
  rfl

private def sourceLeft (input : BitString)
    (outsideLeft : List WorkSymbol) : List WorkSymbol :=
  (sourceSymbols input).reverse ++ leftMarker :: outsideLeft

private def tallyLeft (input : BitString)
    (outsideLeft : List WorkSymbol) : List WorkSymbol :=
  List.replicate input.length BuilderInputLength.tallySymbol ++
    rightMarker :: sourceLeft input outsideLeft

private def outputLeft (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    List WorkSymbol :=
  (tokenSymbols output).reverse ++
    outputBoundarySymbol :: tallyLeft input outsideLeft

private def rewindStartConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : CNFToken) : WorkConfiguration :=
  { state := rewindOutputState
    tape := tapeAtLeftWord [tokenSymbol request]
      (outputLeft input outsideLeft output) }

private theorem forward_exact (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : CNFToken) :
    workRunExact? machine (halfSteps input output)
        (entryConfiguration request
          (workspaceTape input outsideLeft output)) =
      some (rewindStartConfiguration input outsideLeft output request) := by
  let c0 := entryConfiguration request
    (workspaceTape input outsideLeft output)
  let c1 : WorkConfiguration :=
    { state := seekInputState request
      tape := tapeAtWord (sourceLeft input outsideLeft)
        (rightMarker ::
          (List.replicate input.length BuilderInputLength.tallySymbol ++
            outputRegion output)) }
  let c2 : WorkConfiguration :=
    { state := seekTallyState request
      tape := tapeAtWord (rightMarker :: sourceLeft input outsideLeft)
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          outputRegion output) }
  let c3 : WorkConfiguration :=
    { state := seekTallyState request
      tape := tapeAtWord (tallyLeft input outsideLeft) (outputRegion output) }
  let c4 : WorkConfiguration :=
    { state := seekOutputState request
      tape := tapeAtWord
        (outputBoundarySymbol :: tallyLeft input outsideLeft)
        (tokenSymbols output) }
  let c5 : WorkConfiguration :=
    { state := seekOutputState request
      tape := tapeAtWord (outputLeft input outsideLeft output) [] }
  let c6 := rewindStartConfiguration input outsideLeft output request
  have hSource : workRunExact? machine (sourceSymbols input).length c0 =
      some c1 := by
    dsimp [c0, c1, entryConfiguration, sourceLeft]
    rw [workspaceTape_eq_sourceWord]
    exact seekInput_source_exact request input (leftMarker :: outsideLeft)
      (rightMarker ::
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          outputRegion output))
  have hMarker : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    dsimp [c1, c2]
    exact step_seekInput_rightMarker request (sourceLeft input outsideLeft)
      (List.replicate input.length BuilderInputLength.tallySymbol ++
        outputRegion output)
  have hTally : workRunExact? machine input.length c2 = some c3 := by
    dsimp [c2, c3, tallyLeft]
    exact seekTally_exact request input.length
      (rightMarker :: sourceLeft input outsideLeft) (outputRegion output)
  have hEnter : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    dsimp [c3, c4]
    exact step_enterOutput request output (tallyLeft input outsideLeft)
  have hOutput : workRunExact? machine output.length c4 = some c5 := by
    dsimp [c4, c5, outputLeft]
    simpa using
      (seekOutput_tokens_exact request output
        (outputBoundarySymbol :: tallyLeft input outsideLeft) [])
  have hAppend : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    dsimp [c5, c6, rewindStartConfiguration, outputLeft]
    exact step_appendToken request (outputLeft input outsideLeft output)
  have h01 := workRunExact_compose (sourceSymbols input).length 1
    c0 c1 c2 hSource hMarker
  have h02 := workRunExact_compose ((sourceSymbols input).length + 1)
    input.length c0 c2 c3 h01 hTally
  have h03 := workRunExact_compose
    (((sourceSymbols input).length + 1) + input.length) 1
    c0 c3 c4 h02 hEnter
  have h04 := workRunExact_compose
    ((((sourceSymbols input).length + 1) + input.length) + 1)
    output.length c0 c4 c5 h03 hOutput
  have h05 := workRunExact_compose
    (((((sourceSymbols input).length + 1) + input.length) + 1) +
      output.length) 1 c0 c5 c6 h04 hAppend
  have hSteps :
      (((((sourceSymbols input).length + 1) + input.length) + 1) +
          output.length) + 1 = halfSteps input output := by
    rw [sourceSymbols_length]
    unfold halfSteps
    omega
  rw [hSteps] at h05
  exact h05

private theorem rewind_exact (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : CNFToken) :
    workRunExact? machine (halfSteps input output)
        (rewindStartConfiguration input outsideLeft output request) =
      some (finalConfiguration input outsideLeft (output ++ [request])) := by
  let c0 := rewindStartConfiguration input outsideLeft output request
  let c1 : WorkConfiguration :=
    { state := rewindOutputState
      tape := tapeAtLeftWord
        (tokenSymbols output ++ [tokenSymbol request])
        (outputBoundarySymbol :: tallyLeft input outsideLeft) }
  let c2 : WorkConfiguration :=
    { state := rewindTallyState
      tape := tapeAtLeftWord
        (outputBoundarySymbol ::
          (tokenSymbols output ++ [tokenSymbol request]))
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          rightMarker :: sourceLeft input outsideLeft) }
  let c3 : WorkConfiguration :=
    { state := rewindTallyState
      tape := tapeAtLeftWord
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          outputBoundarySymbol ::
            (tokenSymbols output ++ [tokenSymbol request]))
        (rightMarker :: sourceLeft input outsideLeft) }
  let c4 : WorkConfiguration :=
    { state := rewindInputState
      tape := tapeAtLeftWord
        (rightMarker ::
          (List.replicate input.length BuilderInputLength.tallySymbol ++
            outputBoundarySymbol ::
              (tokenSymbols output ++ [tokenSymbol request])))
        (sourceLeft input outsideLeft) }
  let c5 : WorkConfiguration :=
    { state := rewindInputState
      tape := tapeAtLeftWord
        (sourceSymbols input ++
          rightMarker ::
            (List.replicate input.length BuilderInputLength.tallySymbol ++
              outputBoundarySymbol ::
                (tokenSymbols output ++ [tokenSymbol request])))
        (leftMarker :: outsideLeft) }
  let c6 := finalConfiguration input outsideLeft (output ++ [request])
  have hOutput : workRunExact? machine output.length c0 = some c1 := by
    dsimp [c0, c1, rewindStartConfiguration, outputLeft]
    simpa [List.append_assoc] using
      (rewindOutput_tokens_exact output
        (outputBoundarySymbol :: tallyLeft input outsideLeft)
        [tokenSymbol request])
  have hBoundary : workRunExact? machine 1 c1 = some c2 := by
    apply workRunExact_one
    dsimp [c1, c2, tallyLeft]
    exact step_rewindOutput_boundary
      (List.replicate input.length BuilderInputLength.tallySymbol ++
        rightMarker :: sourceLeft input outsideLeft)
      (tokenSymbols output ++ [tokenSymbol request])
  have hTally : workRunExact? machine input.length c2 = some c3 := by
    dsimp [c2, c3]
    exact rewindTally_exact input.length
      (rightMarker :: sourceLeft input outsideLeft)
      (outputBoundarySymbol ::
        (tokenSymbols output ++ [tokenSymbol request]))
  have hMarker : workRunExact? machine 1 c3 = some c4 := by
    apply workRunExact_one
    dsimp [c3, c4]
    exact step_rewindTally_rightMarker (sourceLeft input outsideLeft)
      (List.replicate input.length BuilderInputLength.tallySymbol ++
        outputBoundarySymbol ::
          (tokenSymbols output ++ [tokenSymbol request]))
  have hSource : workRunExact? machine (sourceSymbols input).length c4 =
      some c5 := by
    dsimp [c4, c5, sourceLeft]
    exact rewindInput_source_exact input (leftMarker :: outsideLeft)
      (rightMarker ::
        (List.replicate input.length BuilderInputLength.tallySymbol ++
          outputBoundarySymbol ::
            (tokenSymbols output ++ [tokenSymbol request])))
  have hFinish : workRunExact? machine 1 c5 = some c6 := by
    apply workRunExact_one
    dsimp [c5, c6, finalConfiguration]
    have hStep := step_rewindInput_leftMarker outsideLeft
      (sourceSymbols input ++
        rightMarker ::
          (List.replicate input.length BuilderInputLength.tallySymbol ++
            outputBoundarySymbol ::
              (tokenSymbols output ++ [tokenSymbol request])))
    rw [workspaceTape_eq_sourceWord]
    simpa [machine, tapeAtLeftWord, outputRegion, tokenSymbols,
      tokenSymbols_append, List.append_assoc] using hStep
  have h01 := workRunExact_compose output.length 1 c0 c1 c2
    hOutput hBoundary
  have h02 := workRunExact_compose (output.length + 1) input.length
    c0 c2 c3 h01 hTally
  have h03 := workRunExact_compose
    ((output.length + 1) + input.length) 1 c0 c3 c4 h02 hMarker
  have h04 := workRunExact_compose
    (((output.length + 1) + input.length) + 1)
    (sourceSymbols input).length c0 c4 c5 h03 hSource
  have h05 := workRunExact_compose
    ((((output.length + 1) + input.length) + 1) +
      (sourceSymbols input).length) 1 c0 c5 c6 h04 hFinish
  have hSteps :
      ((((output.length + 1) + input.length) + 1) +
          (sourceSymbols input).length) + 1 = halfSteps input output := by
    rw [sourceSymbols_length]
    unfold halfSteps
    omega
  rw [hSteps] at h05
  exact h05

/-- Every raw source word, exterior-left region, existing canonical output,
and state-selected token follows one exact finite trace and appends exactly
that token in order. -/
theorem appendToken_workRunExact (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken)
    (request : CNFToken) :
    workRunExact? machine (workSteps input output)
        (entryConfiguration request
          (workspaceTape input outsideLeft output)) =
      some (finalConfiguration input outsideLeft (output ++ [request])) := by
  have hForward := forward_exact input outsideLeft output request
  have hRewind := rewind_exact input outsideLeft output request
  have hAll := workRunExact_compose (halfSteps input output)
    (halfSteps input output)
    (entryConfiguration request (workspaceTape input outsideLeft output))
    (rewindStartConfiguration input outsideLeft output request)
    (finalConfiguration input outsideLeft (output ++ [request]))
    hForward hRewind
  simpa [workSteps, Nat.two_mul] using hAll

/-! ### Distinguished first header token -/

/-- Endpoint after the machine's distinguished start state has emitted the
first canonical formula-header token. -/
def firstHeaderFinalConfiguration (input : BitString)
    (outsideLeft : List WorkSymbol) : WorkConfiguration :=
  finalConfiguration input outsideLeft [.t]

/-- Starting from the preceding tally endpoint, the fixed machine appends the
first `T` header token in the exact displayed number of work transitions. -/
theorem firstHeaderToken_workRunExact (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workRunExact? machine (workSteps input [])
        (workStartConfiguration machine
          (BuilderInputLength.finalTape input outsideLeft)) =
      some (firstHeaderFinalConfiguration input outsideLeft) := by
  have hExact := appendToken_workRunExact input outsideLeft [] .t
  rw [workspaceTape_empty_eq_builderInputLength_finalTape] at hExact
  simpa [machine, workStartConfiguration, entryConfiguration,
    firstHeaderFinalConfiguration] using hExact

/-- The same supplied endpoint identity specialized to the already-proved
two-stage input prefix.  This theorem is endpoint transport only: this module
does not concatenate either stage's rule table. -/
theorem firstHeaderToken_after_builderInputPrefix (input : BitString) :
    workRunExact? machine (workSteps input [])
        (workStartConfiguration machine (BuilderInputPrefix.finalTape input)) =
      some (firstHeaderFinalConfiguration input
        (PipelineInputFramer.totalInputFramerOutsideLeft input)) := by
  simpa [BuilderInputPrefix.finalTape] using
    (firstHeaderToken_workRunExact input
      (PipelineInputFramer.totalInputFramerOutsideLeft input))

theorem finalConfiguration_isHalted (input : BitString)
    (outsideLeft : List WorkSymbol) (output : List CNFToken) :
    machine.isHalted (finalConfiguration input outsideLeft output) = true := by
  rfl

theorem firstTokenRawTimeBound_eval (input : BitString) :
    firstTokenRawTimeBound.eval (BitString.size input) =
      24 * input.length + 48 := by
  simp [firstTokenRawTimeBound, NatPolynomial.linear, BitString.size]

/-- Six raw transitions implement each work transition, and the distinguished
first-token trace is bounded by `24*n + 48` in external encoded-input length. -/
theorem firstTokenRawTimeBound_le (input : BitString) :
    6 * workSteps input [] ≤
      firstTokenRawTimeBound.eval (BitString.size input) := by
  rw [firstTokenRawTimeBound_eval]
  have hSource := sourceCellCount_le input
  unfold workSteps halfSteps
  simp only [List.length_nil, Nat.add_zero]
  omega

/-- Exact six-for-one raw compilation of the distinguished first-token trace. -/
theorem run_compile_firstHeaderToken_exact (input : BitString)
    (outsideLeft : List WorkSymbol) :
    run (compileWorkMachine machine) (6 * workSteps input [])
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (BuilderInputLength.finalTape input outsideLeft))) =
      encodeWorkConfiguration
        (firstHeaderFinalConfiguration input outsideLeft) := by
  exact run_compileWorkMachine_mul_of_workRunExact machine
    (workSteps input [])
    (workStartConfiguration machine
      (BuilderInputLength.finalTape input outsideLeft))
    (firstHeaderFinalConfiguration input outsideLeft)
    (firstHeaderToken_workRunExact input outsideLeft)

/-- The compiled machine reaches the first-header endpoint within the explicit
external-size polynomial. -/
theorem run_compile_firstHeaderToken_rawTimeBound (input : BitString)
    (outsideLeft : List WorkSymbol) :
    run (compileWorkMachine machine)
        (firstTokenRawTimeBound.eval (BitString.size input))
        (encodeWorkConfiguration
          (workStartConfiguration machine
            (BuilderInputLength.finalTape input outsideLeft))) =
      encodeWorkConfiguration
        (firstHeaderFinalConfiguration input outsideLeft) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps input [])
    (firstTokenRawTimeBound.eval (BitString.size input))
    (workStartConfiguration machine
      (BuilderInputLength.finalTape input outsideLeft))
    (firstHeaderFinalConfiguration input outsideLeft)
    (firstHeaderToken_workRunExact input outsideLeft)
    (finalConfiguration_isHalted input outsideLeft [.t])
    (firstTokenRawTimeBound_le input)

theorem firstHeaderToken_workBoundedDecide_accept (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workBoundedDecide machine (workSteps input [])
        (BuilderInputLength.finalTape input outsideLeft) = .accept := by
  unfold workBoundedDecide
  rw [workRun_eq_of_workRunExact machine (workSteps input [])
    (workStartConfiguration machine
      (BuilderInputLength.finalTape input outsideLeft))
    (firstHeaderFinalConfiguration input outsideLeft)
    (firstHeaderToken_workRunExact input outsideLeft)]
  rfl

/-! ### Link to the concrete Cook--Levin formula -/

/-- Every concrete tableau layout has at least one allocated symbol variable,
so its canonical unary formula-width header starts with `T`. -/
theorem formulaWidth_positive {language : Language}
    (problem : VerifierTableauProblem language) :
    0 < problem.FormulaWidth := by
  let time : Fin problem.dimensions.timeCount :=
    ⟨0, problem.dimensions.timeCount_positive⟩
  let position : Fin
      (problem.dimensions.tapeWidth problem.tableauInputMode) :=
    ⟨0, problem.dimensions.tapeWidth_positive problem.tableauInputMode⟩
  have hVariable := problem.layout.symbolVariable_lt_variableCount
    time position TapeSymbol.blank
  change problem.layout.symbolVariable time position TapeSymbol.blank <
    problem.FormulaWidth at hVariable
  omega

/-- The first direct formula-bit coordinate is the first bit of the positive
unary-width token `T`. -/
theorem formulaBitSlotDirect_zero {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaBitSlotDirect 0 = some (some true) := by
  rw [problem.formulaBitSlotDirect_eq]
  have hPositive := formulaWidth_positive problem
  generalize hWidth : problem.FormulaWidth = width at hPositive ⊢
  cases width with
  | zero => omega
  | succ width =>
      simp [VerifierTableauProblem.formulaBitSchedule,
        VerifierTableauProblem.formulaTokenSchedule,
        FormulaSchedule.pad, VerifierTableauProblem.scheduledTokenBits,
        hWidth, encodeUnaryTokens, CNFToken.bits]

/-- The second direct formula-bit coordinate is the second bit of the same
initial token. -/
theorem formulaBitSlotDirect_one {language : Language}
    (problem : VerifierTableauProblem language) :
    problem.formulaBitSlotDirect 1 = some (some true) := by
  rw [problem.formulaBitSlotDirect_eq]
  have hPositive := formulaWidth_positive problem
  generalize hWidth : problem.FormulaWidth = width at hPositive ⊢
  cases width with
  | zero => omega
  | succ width =>
      simp [VerifierTableauProblem.formulaBitSchedule,
        VerifierTableauProblem.formulaTokenSchedule,
        FormulaSchedule.pad, VerifierTableauProblem.scheduledTokenBits,
        hWidth, encodeUnaryTokens, CNFToken.bits]

/-- The literal two raw bits emitted by the fixed first-token machine are
exactly the first two bits of every concrete Cook--Levin encoded formula. -/
theorem firstHeaderToken_bits_eq_encodedFormula_take_two
    {language : Language} (problem : VerifierTableauProblem language) :
    CNFToken.t.bits = problem.encodedFormula.take 2 := by
  have hPositive := formulaWidth_positive problem
  generalize hWidth : problem.FormulaWidth = width at hPositive ⊢
  cases width with
  | zero => omega
  | succ width =>
      simp [VerifierTableauProblem.encodedFormula,
        VerifierTableauProblem.formula, LocalProgram.toFormula,
        encodeCNF, encodeCNFTokens, hWidth, encodeUnaryTokens,
        encodeTokenPairs, CNFToken.bits]

/-! ### Fail-closed negative behavior -/

def malformedTallyConfiguration (request : CNFToken)
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := seekTallyState request
    tape := { left := left, head := WorkSymbol.zeroZero, right := right } }

theorem malformedTallySymbol_isHalted_false (request : CNFToken)
    (left right : List WorkSymbol) :
    machine.isHalted (malformedTallyConfiguration request left right) = false := by
  cases request <;> rfl

theorem malformedTallySymbol_workStep_none (request : CNFToken)
    (left right : List WorkSymbol) :
    workStep? machine (malformedTallyConfiguration request left right) = none := by
  cases request <;> rfl

/-- An unexpected symbol in the tally phase remains stuck and nonhalting for
every fuel budget. -/
theorem malformedTallySymbol_timeout (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let result := workRun machine fuel
        (malformedTallyConfiguration request left right)
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none machine
    (malformedTallyConfiguration request left right) fuel
    (malformedTallySymbol_workStep_none request left right)
  rw [hRun]
  cases request <;> rfl

def malformedOutputConfiguration (request : CNFToken)
    (left right : List WorkSymbol) : WorkConfiguration :=
  { state := seekOutputState request
    tape := { left := left, head := WorkSymbol.zeroBlank, right := right } }

theorem malformedOutputSymbol_isHalted_false (request : CNFToken)
    (left right : List WorkSymbol) :
    machine.isHalted (malformedOutputConfiguration request left right) = false := by
  cases request <;> rfl

theorem malformedOutputSymbol_workStep_none (request : CNFToken)
    (left right : List WorkSymbol) :
    workStep? machine (malformedOutputConfiguration request left right) = none := by
  cases request <;> rfl

/-- An unexpected symbol in the output phase also remains timeout rather than
being reclassified as rejection. -/
theorem malformedOutputSymbol_timeout (fuel : Nat) (request : CNFToken)
    (left right : List WorkSymbol) :
    (let result := workRun machine fuel
        (malformedOutputConfiguration request left right)
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout := by
  have hRun := workRun_eq_self_of_workStep?_eq_none machine
    (malformedOutputConfiguration request left right) fuel
    (malformedOutputSymbol_workStep_none request left right)
  rw [hRun]
  cases request <;> rfl

private theorem workRunExact_succ_split_last :
    ∀ (steps : Nat) (initial final : WorkConfiguration),
      workRunExact? machine (steps + 1) initial = some final →
      ∃ before,
        workRunExact? machine steps initial = some before ∧
        workStep? machine before = some final := by
  intro steps
  induction steps with
  | zero =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => some next) = some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hNext : next = final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => some result) = some final at hRun
            rw [hStep] at hRun
            exact Option.some.inj hRun
          subst final
          exact ⟨initial, rfl, hStep⟩
  | succ steps ih =>
      intro initial final hRun
      cases hStep : workStep? machine initial with
      | none =>
          change
            (match workStep? machine initial with
             | none => none
             | some next => workRunExact? machine (steps + 1) next) =
              some final at hRun
          rw [hStep] at hRun
          contradiction
      | some next =>
          have hTail : workRunExact? machine (steps + 1) next =
              some final := by
            change
              (match workStep? machine initial with
               | none => none
               | some result => workRunExact? machine (steps + 1) result) =
                some final at hRun
            rw [hStep] at hRun
            exact hRun
          rcases ih next final hTail with ⟨before, hPrefix, hLast⟩
          refine ⟨before, ?_, hLast⟩
          change
            (match workStep? machine initial with
             | none => none
             | some result => workRunExact? machine steps result) = some before
          rw [hStep]
          exact hPrefix

private theorem isHalted_false_of_workStep_some
    (config next : WorkConfiguration)
    (hStep : workStep? machine config = some next) :
    machine.isHalted config = false := by
  cases hHalted : machine.isHalted config with
  | false => rfl
  | true =>
      unfold workStep? at hStep
      rw [hHalted] at hStep
      contradiction

private theorem workSteps_positive (input : BitString) :
    0 < workSteps input [] := by
  unfold workSteps halfSteps
  have hSource := sourceCellCount_positive input
  omega

/-- Removing the final successful transition from the first-header trace
leaves a nonhalting state and therefore reports timeout. -/
theorem firstHeaderToken_one_step_short_timeout (input : BitString)
    (outsideLeft : List WorkSymbol) :
    workBoundedDecide machine (workSteps input [] - 1)
        (BuilderInputLength.finalTape input outsideLeft) = .timeout := by
  let short := workSteps input [] - 1
  let initial := workStartConfiguration machine
    (BuilderInputLength.finalTape input outsideLeft)
  let final := firstHeaderFinalConfiguration input outsideLeft
  have hSucc : short + 1 = workSteps input [] := by
    dsimp [short]
    have hPositive := workSteps_positive input
    omega
  have hExact := firstHeaderToken_workRunExact input outsideLeft
  change workRunExact? machine (workSteps input []) initial = some final at hExact
  rw [← hSucc] at hExact
  rcases workRunExact_succ_split_last short initial final hExact with
    ⟨before, hPrefix, hLast⟩
  have hRun : workRun machine short initial = before :=
    workRun_eq_of_workRunExact machine short initial before hPrefix
  have hNotHalted := isHalted_false_of_workStep_some before final hLast
  unfold workBoundedDecide
  change
    (let result := workRun machine short initial
     if result.state == machine.acceptState then WorkVerdict.accept
     else if result.state == machine.rejectState then WorkVerdict.reject
     else WorkVerdict.timeout) = WorkVerdict.timeout
  rw [hRun]
  cases hAccept : (before.state == machine.acceptState) with
  | true =>
      unfold WorkMachine.isHalted at hNotHalted
      rw [hAccept] at hNotHalted
      contradiction
  | false =>
      cases hReject : (before.state == machine.rejectState) with
      | true =>
          unfold WorkMachine.isHalted at hNotHalted
          rw [hAccept, hReject] at hNotHalted
          contradiction
      | false => simp [hAccept, hReject]

end BuilderTokenAppender

end CookLevin

end PNP.Concrete
