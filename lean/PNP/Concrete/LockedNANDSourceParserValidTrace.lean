/-
Copyright (c) 2026 PNP Labs.

Constructive exact executions of the strict-v0 source parser on every
well-formed canonical circuit encoding.

This module is operational: it derives runs of the literal 2,052-rule work
machine.  Pure codec facts are used only to describe the canonical input word
and to obtain source-index inequalities.  No semantic decoder participates in
the machine or in transition selection.
-/

import PNP.Concrete.LockedNANDSourceParserMachine
import PNP.Concrete.LockedNANDSourceParserSemantics

namespace PNP.Concrete.LockedNAND.SourceParser

/-! ### Canonical two-bit work-cell layouts -/

/-- The two packed work cells occupied by one strict four-bit token. -/
def tokenCells : Token → List WorkSymbol
  | .version0 => [cell00, cell00]
  | .unit => [cell00, cell01]
  | .natEnd => [cell00, cell10]
  | .input => [cell00, cell11]
  | .constantFalse => [cell01, cell00]
  | .constantTrue => [cell01, cell01]
  | .gate => [cell01, cell10]
  | .gateEnd => [cell01, cell11]
  | .programEnd => [cell10, cell00]
  | .outputsEnd => [cell10, cell01]
  | .threshold => [cell10, cell10]
  | .instanceEnd => [cell10, cell11]

def packedTokenCells : List Token → List WorkSymbol
  | [] => []
  | token :: rest => tokenCells token ++ packedTokenCells rest

theorem tokenCells_length (token : Token) :
    (tokenCells token).length = 2 := by
  cases token <;> rfl

theorem packedTokenCells_length (tokens : List Token) :
    (packedTokenCells tokens).length = 2 * tokens.length := by
  induction tokens with
  | nil =>
      rfl
  | cons token rest ih =>
      simp [packedTokenCells, tokenCells_length, ih]
      omega

/-- Packed unary natural: one `00,01` pair per unit and the terminating
`00,10` pair. -/
def natCells : Nat → List WorkSymbol
  | 0 => [cell00, cell10]
  | value + 1 => cell00 :: cell01 :: natCells value

def natCellsTail : Nat → List WorkSymbol
  | 0 => [cell10]
  | value + 1 => cell01 :: natCells value

theorem natCells_length (value : Nat) :
    (natCells value).length = 2 * (value + 1) := by
  induction value with
  | zero =>
      rfl
  | succ value ih =>
      simp only [natCells, List.length_cons]
      omega

theorem natCells_eq_cons (value : Nat) :
    natCells value = cell00 :: natCellsTail value := by
  cases value <;> rfl

def sourceCells : RawSource → List WorkSymbol
  | .input index => cell00 :: cell11 :: natCells index
  | .constant false => [cell01, cell00]
  | .constant true => [cell01, cell01]
  | .gate index => cell01 :: cell10 :: natCells index

def gateCells (gate : RawGate) : List WorkSymbol :=
  sourceCells gate.left ++ sourceCells gate.right ++ [cell01, cell11]

def gateListCells : List RawGate → List WorkSymbol
  | [] => []
  | gate :: rest => gateCells gate ++ gateListCells rest

def circuitCells (raw : RawCircuit) : List WorkSymbol :=
  [cell00, cell00] ++
    natCells raw.inputCount ++
    natCells raw.gates.length ++
    gateListCells raw.gates ++
    [cell10, cell00] ++
    sourceCells raw.output ++
    [cell10, cell01, cell10, cell11]

/-- A unary field with `used` leading units temporarily borrowed. -/
def countCells : Nat → Nat → List WorkSymbol
  | 0, remaining => natCells remaining
  | used + 1, remaining =>
      cell00 :: countMark :: countCells used remaining

def borrowedCountCells : Nat → List WorkSymbol
  | 0 => []
  | used + 1 => cell00 :: countMark :: borrowedCountCells used

theorem borrowedCountCells_length (used : Nat) :
    (borrowedCountCells used).length = 2 * used := by
  induction used with
  | zero =>
      rfl
  | succ used ih =>
      simp only [borrowedCountCells, List.length_cons]
      omega

private theorem countCells_eq_borrowed_append
    (used remaining : Nat) :
    countCells used remaining =
      borrowedCountCells used ++ natCells remaining := by
  induction used with
  | zero =>
      rfl
  | succ used ih =>
      change
        cell00 :: countMark :: countCells used remaining =
          cell00 :: countMark ::
            (borrowedCountCells used ++ natCells remaining)
      rw [ih]

theorem countCells_length (used remaining : Nat) :
    (countCells used remaining).length =
      2 * (used + remaining + 1) := by
  rw [countCells_eq_borrowed_append,
    List.length_append, borrowedCountCells_length,
    natCells_length]
  omega

private theorem countCells_succ_remaining
    (used remaining : Nat) :
    countCells used (remaining + 1) =
      borrowedCountCells used ++
        cell00 :: cell01 :: natCells remaining := by
  rw [countCells_eq_borrowed_append]
  simp [natCells]

/-- A completed gate has its `gateEnd` first cell replaced by its persistent
gate anchor. -/
def markedGateCells (gate : RawGate) : List WorkSymbol :=
  sourceCells gate.left ++ sourceCells gate.right ++ [gateMark, cell11]

def markedGateListCells : List RawGate → List WorkSymbol
  | [] => []
  | gate :: rest =>
      markedGateCells gate ++ markedGateListCells rest

def borrowedGateCells (gate : RawGate) : List WorkSymbol :=
  sourceCells gate.left ++ sourceCells gate.right ++ [countMark, cell11]

def borrowedGateListCells : List RawGate → List WorkSymbol
  | [] => []
  | gate :: rest =>
      borrowedGateCells gate ++ borrowedGateListCells rest

theorem markedGateCells_length (gate : RawGate) :
    (markedGateCells gate).length = (gateCells gate).length := by
  unfold markedGateCells gateCells
  simp

theorem borrowedGateCells_length (gate : RawGate) :
    (borrowedGateCells gate).length = (gateCells gate).length := by
  unfold borrowedGateCells gateCells
  simp

theorem markedGateListCells_length (gates : List RawGate) :
    (markedGateListCells gates).length =
      (gateListCells gates).length := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [markedGateListCells, gateListCells,
        markedGateCells_length, ih]

theorem borrowedGateListCells_length (gates : List RawGate) :
    (borrowedGateListCells gates).length =
      (gateListCells gates).length := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest ih =>
      simp [borrowedGateListCells, gateListCells,
        borrowedGateCells_length, ih]

private theorem markedGateListCells_append
    (first second : List RawGate) :
    markedGateListCells (first ++ second) =
      markedGateListCells first ++ markedGateListCells second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        markedGateCells gate ++
            markedGateListCells (rest ++ second) =
          (markedGateCells gate ++ markedGateListCells rest) ++
            markedGateListCells second
      rw [ih, List.append_assoc]

private theorem borrowedGateListCells_append
    (first second : List RawGate) :
    borrowedGateListCells (first ++ second) =
      borrowedGateListCells first ++ borrowedGateListCells second := by
  induction first with
  | nil =>
      rfl
  | cons gate rest ih =>
      change
        borrowedGateCells gate ++
            borrowedGateListCells (rest ++ second) =
          (borrowedGateCells gate ++ borrowedGateListCells rest) ++
            borrowedGateListCells second
      rw [ih, List.append_assoc]

/-- Logical left-to-right prefix at a gate boundary.  `done` gates have
persistent anchors and the same number of declared-count units have been
crossed. -/
def gatePrefix (inputs : Nat) (done todo : List RawGate) :
    List WorkSymbol :=
  [cell00, cell00] ++
    natCells inputs ++
    countCells done.length todo.length ++
    markedGateListCells done

/-- Prefix after the next declared gate-count unit has been borrowed but
before that gate has acquired its persistent anchor. -/
def gateParsingPrefix (inputs : Nat) (done todo : List RawGate) :
    List WorkSymbol :=
  [cell00, cell00] ++
    natCells inputs ++
    countCells (done.length + 1) todo.length ++
    markedGateListCells done

private theorem gatePrefix_snoc
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate) :
    gatePrefix inputs (done ++ [gate]) todo =
      gateParsingPrefix inputs done todo ++ markedGateCells gate := by
  unfold gatePrefix gateParsingPrefix
  rw [markedGateListCells_append]
  simp [markedGateListCells, List.append_assoc]

theorem packedTokenCells_encodeNatTokens (value : Nat) :
    packedTokenCells (encodeNatTokens value) = natCells value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      change cell00 :: cell01 ::
          packedTokenCells (encodeNatTokens value) =
        cell00 :: cell01 :: natCells value
      exact congrArg (List.cons cell00)
        (congrArg (List.cons cell01) ih)

theorem packedTokenCells_encodeSourceTokens (source : RawSource) :
    packedTokenCells (encodeSourceTokens source) = sourceCells source := by
  cases source with
  | input index =>
      change cell00 :: cell11 ::
          packedTokenCells (encodeNatTokens index) =
        cell00 :: cell11 :: natCells index
      rw [packedTokenCells_encodeNatTokens]
  | constant value =>
      cases value <;> rfl
  | gate index =>
      change cell01 :: cell10 ::
          packedTokenCells (encodeNatTokens index) =
        cell01 :: cell10 :: natCells index
      rw [packedTokenCells_encodeNatTokens]

private theorem packedTokenCells_append
    (first second : List Token) :
    packedTokenCells (first ++ second) =
      packedTokenCells first ++ packedTokenCells second := by
  induction first with
  | nil => rfl
  | cons token rest ih =>
      change tokenCells token ++
          packedTokenCells (rest ++ second) =
        (tokenCells token ++ packedTokenCells rest) ++
          packedTokenCells second
      rw [ih, List.append_assoc]

theorem packedTokenCells_encodeGateListTokens
    (gates : List RawGate) :
    packedTokenCells (encodeGateListTokens gates) =
      gateListCells gates := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      cases gate with
      | mk left right =>
          change
            packedTokenCells
                ((encodeSourceTokens left ++ encodeSourceTokens right ++
                    [Token.gateEnd]) ++
                  encodeGateListTokens rest) =
              (sourceCells left ++ sourceCells right ++
                  [cell01, cell11]) ++
                gateListCells rest
          rw [packedTokenCells_append, packedTokenCells_append,
            packedTokenCells_append,
            packedTokenCells_encodeSourceTokens,
            packedTokenCells_encodeSourceTokens, ih]
          rfl

theorem packedTokenCells_encodeCircuitTokens (raw : RawCircuit) :
    packedTokenCells (encodeCircuitTokens raw) = circuitCells raw := by
  cases raw with
  | mk inputs gates output =>
      unfold encodeCircuitTokens circuitCells
      simp only [List.cons_append, List.nil_append]
      unfold packedTokenCells
      repeat rw [packedTokenCells_append]
      rw [packedTokenCells_encodeNatTokens,
        packedTokenCells_encodeNatTokens,
        packedTokenCells_encodeGateListTokens,
        packedTokenCells_encodeSourceTokens]
      rfl

private theorem packTokenBits (token : Token)
    (suffix : List TapeSymbol) :
    packWorkSymbols
        (token.bits.map TapeSymbol.ofBool ++ suffix) =
      tokenCells token ++ packWorkSymbols suffix := by
  cases token <;> rfl

theorem pack_encodeTokens (tokens : List Token) :
    packWorkSymbols
        ((encodeTokens tokens).map TapeSymbol.ofBool) =
      packedTokenCells tokens := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      unfold encodeTokens packedTokenCells
      rw [List.map_append, packTokenBits, ih]

theorem rawInputWorkTape_encodeCircuit (raw : RawCircuit) :
    rawInputWorkTape (encodeCircuit raw) =
      WorkTape.ofSymbols (circuitCells raw) := by
  unfold rawInputWorkTape encodeCircuit
  rw [pack_encodeTokens, packedTokenCells_encodeCircuitTokens]

theorem circuitCells_ne_empty (raw : RawCircuit) :
    circuitCells raw ≠ [] := by
  intro impossible
  cases raw with
  | mk inputs gates output =>
      unfold circuitCells at impossible
      contradiction

/-! ### Exact source endpoint -/

/-- Accepting tape: the temporary left guard has been blanked and the head
has returned to the first packed source cell. -/
def acceptedTape (raw : RawCircuit) : WorkTape :=
  match circuitCells raw with
  | [] => { left := [cellBlank], head := cellBlank, right := [] }
  | first :: rest =>
      { left := [cellBlank], head := first,
        right := rest ++ [cellBlank] }

def validFinalConfiguration (raw : RawCircuit) : WorkConfiguration :=
  { state := machine.acceptState
    tape := acceptedTape raw }

theorem validFinalConfiguration_state (raw : RawCircuit) :
    (validFinalConfiguration raw).state = machine.acceptState := by
  rfl

theorem validFinalConfiguration_isHalted (raw : RawCircuit) :
    machine.isHalted (validFinalConfiguration raw) = true := by
  rfl

theorem acceptedTape_eq_of_nonempty
    (raw : RawCircuit) (first : WorkSymbol) (rest : List WorkSymbol)
    (cellsEq : circuitCells raw = first :: rest) :
    acceptedTape raw =
      { left := [cellBlank], head := first,
        right := rest ++ [cellBlank] } := by
  unfold acceptedTape
  rw [cellsEq]

private theorem encodeWorkRight_tokenCells (token : Token) :
    encodeWorkRight (tokenCells token) =
      token.bits.map TapeSymbol.ofBool := by
  cases token <;> rfl

private theorem encodeWorkRight_packedTokenCells
    (tokens : List Token) :
    encodeWorkRight (packedTokenCells tokens) =
      (encodeTokens tokens).map TapeSymbol.ofBool := by
  induction tokens with
  | nil => rfl
  | cons token rest ih =>
      unfold packedTokenCells encodeTokens
      rw [encodeWorkRight_append, encodeWorkRight_tokenCells,
        List.map_append, ih]

theorem encodeWorkRight_circuitCells (raw : RawCircuit) :
    encodeWorkRight (circuitCells raw) =
      (encodeCircuit raw).map TapeSymbol.ofBool := by
  rw [← packedTokenCells_encodeCircuitTokens,
    encodeWorkRight_packedTokenCells]
  rfl

private theorem encodeWorkRight_length (word : List WorkSymbol) :
    (encodeWorkRight word).length = 2 * word.length := by
  induction word with
  | nil =>
      rfl
  | cons symbol rest ih =>
      change Nat.succ (Nat.succ (encodeWorkRight rest).length) =
        2 * Nat.succ rest.length
      rw [ih, Nat.mul_succ]

theorem encodeCircuit_length_eq (raw : RawCircuit) :
    (encodeCircuit raw).length =
      2 * (circuitCells raw).length := by
  have lengths :=
    congrArg List.length (encodeWorkRight_circuitCells raw)
  simpa [encodeWorkRight_length] using lengths.symm

theorem acceptedTape_outputBits (raw : RawCircuit) :
    (encodeWorkTape (acceptedTape raw)).outputBits =
      encodeCircuit raw := by
  cases cellsEq : circuitCells raw with
  | nil =>
      exact False.elim (circuitCells_ne_empty raw cellsEq)
  | cons first rest =>
      have encoded := encodeWorkRight_circuitCells raw
      rw [cellsEq] at encoded
      unfold acceptedTape
      rw [cellsEq]
      change Tape.decodeOutputCells
          (first.first :: first.second ::
            encodeWorkRight (rest ++ [cellBlank])) =
        encodeCircuit raw
      change encodeWorkRight (first :: rest) =
        (encodeCircuit raw).map TapeSymbol.ofBool at encoded
      rw [encodeWorkRight_append]
      change Tape.decodeOutputCells
          (encodeWorkRight (first :: rest) ++
            [TapeSymbol.blank, TapeSymbol.blank]) =
        encodeCircuit raw
      rw [encoded, Tape.decodeOutputCells_append_blank]

/-! ### Exact-run combinators -/

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
          have tail :
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
          exact ih next tail

private theorem exactRun_one
    (initial final : WorkConfiguration)
    (step : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change
    (match workStep? machine initial with
     | none => none
     | some next => some next) = some final
  rw [step]

/-! ### Canonical word zippers and header trace -/

def tapeAtWord (left : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := left, head := cellBlank, right := [] }
  | first :: rest => { left := left, head := first, right := rest }

def configAtWord (state : Nat) (left word : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtWord left word }

/-- Focus a nearest-first word on the left of a tape. -/
def tapeAtLeftWord (right : List WorkSymbol) :
    List WorkSymbol → WorkTape
  | [] => { left := [], head := cellBlank, right := right }
  | first :: rest => { left := rest, head := first, right := right }

def configAtLeftWord (state : Nat) (leftWord right : List WorkSymbol) :
    WorkConfiguration :=
  { state := state, tape := tapeAtLeftWord right leftWord }

/-- Move the stated ordinary word to the nearest-first left accumulator. -/
def pushCrossed : List WorkSymbol → List WorkSymbol → List WorkSymbol
  | [], left => left
  | first :: rest, left => pushCrossed rest (first :: left)

theorem pushCrossed_length
    (word left : List WorkSymbol) :
    (pushCrossed word left).length =
      word.length + left.length := by
  induction word generalizing left with
  | nil =>
      simp [pushCrossed]
  | cons symbol rest ih =>
    rw [pushCrossed, ih]
    simp only [List.length_cons]
    omega

private theorem pushCrossed_append (first second left : List WorkSymbol) :
    pushCrossed (first ++ second) left =
      pushCrossed second (pushCrossed first left) := by
  induction first generalizing left with
  | nil => rfl
  | cons symbol rest ih =>
      exact ih (symbol :: left)

private theorem pushCrossed_eq_reverse_append
    (word left : List WorkSymbol) :
    pushCrossed word left = word.reverse ++ left := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons symbol rest ih =>
      rw [pushCrossed, ih]
      simp

private theorem pushCrossed_reverse
    (word right : List WorkSymbol) :
    pushCrossed word.reverse right = word ++ right := by
  rw [pushCrossed_eq_reverse_append, List.reverse_reverse]

/-- A parser configuration whose finite logical prefix lies between the
distinguished left guard and the focused word. -/
def guardedConfig (state : Nat) (guardedPrefix word : List WorkSymbol) :
    WorkConfiguration :=
  configAtWord state (pushCrossed guardedPrefix [leftGuard]) word

private theorem guardedMoveLeft_after_write
    (guardedPrefix : List WorkSymbol)
    (head write : WorkSymbol) (suffix : List WorkSymbol) :
    ((tapeAtWord (pushCrossed guardedPrefix [leftGuard])
        (head :: suffix)).write write).moveLeft =
      tapeAtLeftWord (write :: suffix)
        (guardedPrefix.reverse ++ [leftGuard]) := by
  rw [pushCrossed_eq_reverse_append]
  cases guardedPrefix.reverse <;> rfl

/-- Symbols that may occur inside a successfully guarded canonical word,
excluding the unique guard, temporary cursor, and exterior blank. -/
def ordinaryCell (symbol : WorkSymbol) : Prop :=
  symbol = cell00 ∨ symbol = cell01 ∨ symbol = countMark ∨
    symbol = gateMark ∨ symbol = cell10 ∨ symbol = cell11

private theorem ordinaryCell_ne_leftGuard
    {symbol : WorkSymbol} (ordinary : ordinaryCell symbol) :
    symbol ≠ leftGuard := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst symbol <;> decide

private theorem ordinaryCell_ne_cursorMark
    {symbol : WorkSymbol} (ordinary : ordinaryCell symbol) :
    symbol ≠ cursorMark := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst symbol <;> decide

private theorem ordinaryCell_ne_blank
    {symbol : WorkSymbol} (ordinary : ordinaryCell symbol) :
    symbol ≠ cellBlank := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst symbol <;> decide

private theorem cell00_ordinary : ordinaryCell cell00 :=
  Or.inl rfl

private theorem cell01_ordinary : ordinaryCell cell01 :=
  Or.inr (Or.inl rfl)

private theorem countMark_ordinary : ordinaryCell countMark :=
  Or.inr (Or.inr (Or.inl rfl))

private theorem gateMark_ordinary : ordinaryCell gateMark :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

private theorem cell10_ordinary : ordinaryCell cell10 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

private theorem cell11_ordinary : ordinaryCell cell11 :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

private theorem ordinary_append
    {first second : List WorkSymbol}
    (firstOrdinary :
      ∀ symbol, symbol ∈ first → ordinaryCell symbol)
    (secondOrdinary :
      ∀ symbol, symbol ∈ second → ordinaryCell symbol) :
    ∀ symbol, symbol ∈ first ++ second → ordinaryCell symbol := by
  intro symbol member
  rcases List.mem_append.mp member with member | member
  · exact firstOrdinary symbol member
  · exact secondOrdinary symbol member

private theorem natCells_ordinary (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → ordinaryCell symbol := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h
      · subst symbol
        exact cell00_ordinary
      · rcases h with h | impossible
        · subst symbol
          exact cell10_ordinary
        · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell01_ordinary
      · exact ih symbol member

private theorem countCells_ordinary (used remaining : Nat) :
    ∀ symbol, symbol ∈ countCells used remaining →
      ordinaryCell symbol := by
  induction used with
  | zero =>
      exact natCells_ordinary remaining
  | succ used ih =>
      intro symbol member
      simp only [countCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact countMark_ordinary
      · exact ih symbol member

private theorem sourceCells_ordinary (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → ordinaryCell symbol := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell11_ordinary
      · exact natCells_ordinary index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, List.mem_cons,
          List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell00_ordinary
      · contradiction
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell01_ordinary
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        exact cell01_ordinary
      · subst symbol
        exact cell10_ordinary
      · exact natCells_ordinary index symbol member

private theorem natCells_no_gateMark (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → symbol ≠ gateMark := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih symbol member

private theorem countCells_no_gateMark (used remaining : Nat) :
    ∀ symbol, symbol ∈ countCells used remaining →
      symbol ≠ gateMark := by
  induction used with
  | zero =>
      exact natCells_no_gateMark remaining
  | succ used ih =>
      intro symbol member
      simp only [countCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih symbol member

private theorem natCells_no_countMark (value : Nat) :
    ∀ symbol, symbol ∈ natCells value → symbol ≠ countMark := by
  induction value with
  | zero =>
      intro symbol member
      simp only [natCells, List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | succ value ih =>
      intro symbol member
      simp only [natCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact ih symbol member

private theorem sourceCells_no_gateMark (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → symbol ≠ gateMark := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_gateMark index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, List.mem_cons,
          List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_gateMark index symbol member

private theorem sourceCells_no_countMark (source : RawSource) :
    ∀ symbol, symbol ∈ sourceCells source → symbol ≠ countMark := by
  cases source with
  | input index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_countMark index symbol member
  | constant value =>
      cases value <;>
        intro symbol member <;>
        simp only [sourceCells, List.mem_cons,
          List.not_mem_nil] at member <;>
        rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
  | gate index =>
      intro symbol member
      simp only [sourceCells, List.mem_cons] at member
      rcases member with h | h | member
      · subst symbol
        decide
      · subst symbol
        decide
      · exact natCells_no_countMark index symbol member

private theorem markedGateCells_ordinary (gate : RawGate) :
    ∀ symbol, symbol ∈ markedGateCells gate → ordinaryCell symbol := by
  cases gate with
  | mk left right =>
      unfold markedGateCells
      change
        ∀ symbol,
          symbol ∈
              (sourceCells left ++ sourceCells right) ++
                [gateMark, cell11] →
            ordinaryCell symbol
      apply ordinary_append
        (first := sourceCells left ++ sourceCells right)
        (second := [gateMark, cell11])
      · apply ordinary_append
          (first := sourceCells left)
          (second := sourceCells right)
        · exact sourceCells_ordinary left
        · exact sourceCells_ordinary right
      · intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact gateMark_ordinary
        · subst symbol
          exact cell11_ordinary
        · contradiction

private theorem markedGateListCells_ordinary (gates : List RawGate) :
    ∀ symbol, symbol ∈ markedGateListCells gates →
      ordinaryCell symbol := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      unfold markedGateListCells
      exact ordinary_append
        (first := markedGateCells gate)
        (second := markedGateListCells rest)
        (markedGateCells_ordinary gate) ih

private theorem markedGateCells_no_countMark (gate : RawGate) :
    ∀ symbol, symbol ∈ markedGateCells gate →
      symbol ≠ countMark := by
  cases gate with
  | mk left right =>
      intro symbol member
      unfold markedGateCells at member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact sourceCells_no_countMark left symbol member
        · exact sourceCells_no_countMark right symbol member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          decide
        · subst symbol
          decide
        · contradiction

private theorem markedGateListCells_no_countMark
    (gates : List RawGate) :
    ∀ symbol, symbol ∈ markedGateListCells gates →
      symbol ≠ countMark := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      intro symbol member
      unfold markedGateListCells at member
      rcases List.mem_append.mp member with member | member
      · exact markedGateCells_no_countMark gate symbol member
      · exact ih symbol member

private theorem borrowedGateCells_ordinary (gate : RawGate) :
    ∀ symbol, symbol ∈ borrowedGateCells gate → ordinaryCell symbol := by
  cases gate with
  | mk left right =>
      unfold borrowedGateCells
      change
        ∀ symbol,
          symbol ∈
              (sourceCells left ++ sourceCells right) ++
                [countMark, cell11] →
            ordinaryCell symbol
      apply ordinary_append
        (first := sourceCells left ++ sourceCells right)
        (second := [countMark, cell11])
      · exact ordinary_append
          (sourceCells_ordinary left) (sourceCells_ordinary right)
      · intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact countMark_ordinary
        · subst symbol
          exact cell11_ordinary
        · contradiction

private theorem borrowedGateListCells_ordinary (gates : List RawGate) :
    ∀ symbol, symbol ∈ borrowedGateListCells gates →
      ordinaryCell symbol := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      unfold borrowedGateListCells
      exact ordinary_append
        (first := borrowedGateCells gate)
        (second := borrowedGateListCells rest)
        (borrowedGateCells_ordinary gate) ih

private theorem borrowedGateCells_no_gateMark (gate : RawGate) :
    ∀ symbol, symbol ∈ borrowedGateCells gate → symbol ≠ gateMark := by
  cases gate with
  | mk left right =>
      intro symbol member
      unfold borrowedGateCells at member
      rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact sourceCells_no_gateMark left symbol member
        · exact sourceCells_no_gateMark right symbol member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          decide
        · subst symbol
          decide
        · contradiction

private theorem borrowedGateListCells_no_gateMark
    (gates : List RawGate) :
    ∀ symbol, symbol ∈ borrowedGateListCells gates →
      symbol ≠ gateMark := by
  induction gates with
  | nil =>
      intro symbol member
      contradiction
  | cons gate rest ih =>
      intro symbol member
      unfold borrowedGateListCells at member
      rcases List.mem_append.mp member with member | member
      · exact borrowedGateCells_no_gateMark gate symbol member
      · exact ih symbol member

private theorem gatePrefix_ordinary
    (inputs : Nat) (done todo : List RawGate) :
    ∀ symbol, symbol ∈ gatePrefix inputs done todo →
      ordinaryCell symbol := by
  intro symbol member
  unfold gatePrefix at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact cell00_ordinary
        · subst symbol
          exact cell00_ordinary
        · contradiction
      · exact natCells_ordinary inputs symbol member
    · exact countCells_ordinary done.length todo.length symbol member
  · exact markedGateListCells_ordinary done symbol member

private theorem scanRight_exact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ left head suffix,
      Allowed head →
      workStep? machine
          (configAtWord state left (head :: suffix)) =
        some
          (configAtWord state (head :: left) suffix))
    (word suffix left : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state left (word ++ suffix)) =
      some
        (configAtWord state (pushCrossed word left) suffix) := by
  induction word generalizing left with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed :
          Allowed head :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtWord state left
              (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtWord state
              (pushCrossed (head :: rest) left) suffix)
      rw [step left head (rest ++ suffix) headAllowed]
      exact ih (head :: left) restAllowed

private theorem scanLeft_exact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (step : ∀ head leftTail right,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) right) =
        some
          (configAtLeftWord state leftTail (head :: right)))
    (word leftSuffix right : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state (word ++ leftSuffix) right) =
      some
        (configAtLeftWord state leftSuffix
          (pushCrossed word right)) := by
  induction word generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headAllowed :
          Allowed head :=
        allowed head (List.Mem.head rest)
      have restAllowed :
          ∀ symbol, symbol ∈ rest → Allowed symbol := by
        intro symbol member
        exact allowed symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtLeftWord state
              (head :: (rest ++ leftSuffix)) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtLeftWord state leftSuffix
              (pushCrossed (head :: rest) right))
      rw [step head (rest ++ leftSuffix) right headAllowed]
      exact ih (head :: right) restAllowed

set_option maxRecDepth 100000 in
private theorem gateDecrementSeekGuard_step
    (firstWas01 : Bool) (head : WorkSymbol)
    (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases firstWas01 <;> rfl

private theorem gateDecrementSeekGuard_scan_exact
    (firstWas01 : Bool) (scannedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ scannedPrefix → ordinaryCell symbol) :
    workRunExact? machine scannedPrefix.length
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (scannedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          [leftGuard] (scannedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.gateDecrementSeekGuard firstWas01)
      ordinaryCell
      (gateDecrementSeekGuard_step firstWas01)
      scannedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem gateDecrementGuard_exact
    (firstWas01 : Bool) (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          [leftGuard] suffix) =
      some
        (configAtWord
          (State.gateDecrementVersionFirst firstWas01)
          [leftGuard] suffix) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem bootVersion_exact
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 4
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (cell00 :: cell00 :: current :: rest))) =
      some
        (configAtWord State.inputCountFirst
          [cell00, cell00, leftGuard] (current :: rest)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem inputCountUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.inputCountFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.inputCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem inputCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.inputCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.gateCountFirst
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem inputCount_exact (value : Nat)
    (left : List WorkSymbol) (current : WorkSymbol)
    (rest : List WorkSymbol) :
    ∃ steps,
      steps = 2 * (value + 1) ∧
      workRunExact? machine steps
          (configAtWord State.inputCountFirst left
            (natCells value ++ current :: rest)) =
        some
          (configAtWord State.gateCountFirst
            (pushCrossed (natCells value) left)
            (current :: rest)) := by
  induction value generalizing left with
  | zero =>
      refine ⟨2, rfl, ?_⟩
      exact inputCountEnd_exact left (current :: rest)
  | succ value ih =>
      have first :=
        inputCountUnit_exact left (natCells value ++ current :: rest)
      rcases ih (cell01 :: cell00 :: left) with
        ⟨tailSteps, tailStepsEq, tailRun⟩
      refine ⟨2 + tailSteps, ?_, ?_⟩
      · rw [tailStepsEq]
        omega
      · change
          workRunExact? machine (2 + tailSteps)
              (configAtWord State.inputCountFirst left
                (cell00 :: cell01 ::
                  (natCells value ++ current :: rest))) =
            some
              (configAtWord State.gateCountFirst
                (pushCrossed (natCells (value + 1)) left)
                (current :: rest))
        have composed := exactRun_add 2 tailSteps
          _ _ _ first tailRun
        simpa [natCells, pushCrossed] using composed

set_option maxRecDepth 100000 in
private theorem gateCountUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateCountFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.gateCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem gateCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.gateStart
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem gateCount_exact (value : Nat)
    (left : List WorkSymbol) (current : WorkSymbol)
    (rest : List WorkSymbol) :
    ∃ steps,
      steps = 2 * (value + 1) ∧
      workRunExact? machine steps
          (configAtWord State.gateCountFirst left
            (natCells value ++ current :: rest)) =
        some
          (configAtWord State.gateStart
            (pushCrossed (natCells value) left)
            (current :: rest)) := by
  induction value generalizing left with
  | zero =>
      refine ⟨2, rfl, ?_⟩
      exact gateCountEnd_exact left (current :: rest)
  | succ value ih =>
      have first :=
        gateCountUnit_exact left (natCells value ++ current :: rest)
      rcases ih (cell01 :: cell00 :: left) with
        ⟨tailSteps, tailStepsEq, tailRun⟩
      refine ⟨2 + tailSteps, ?_, ?_⟩
      · rw [tailStepsEq]
        omega
      · change
          workRunExact? machine (2 + tailSteps)
              (configAtWord State.gateCountFirst left
                (cell00 :: cell01 ::
                  (natCells value ++ current :: rest))) =
            some
              (configAtWord State.gateStart
                (pushCrossed (natCells (value + 1)) left)
                (current :: rest))
        have composed := exactRun_add 2 tailSteps
          _ _ _ first tailRun
        simpa [natCells, pushCrossed] using composed

/-- Exact boot, version, input-count, and gate-count trace for a canonical
circuit word. -/
theorem canonicalHeader_exact (inputs gateCount : Nat)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    ∃ steps,
      workRunExact? machine steps
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (cell00 :: cell00 ::
                (natCells inputs ++ natCells gateCount ++
                  current :: rest)))) =
        some
          (configAtWord State.gateStart
            (pushCrossed (natCells gateCount)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard]))
            (current :: rest)) := by
  have boot :=
    bootVersion_exact
      cell00
      (natCellsTail inputs ++ natCells gateCount ++ current :: rest)
  have bootCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (cell00 :: cell00 ::
                (natCells inputs ++ natCells gateCount ++
                  current :: rest)))) =
        some
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) := by
    simpa [natCells_eq_cons] using boot
  rcases inputCount_exact inputs
      [cell00, cell00, leftGuard]
      cell00
      (natCellsTail gateCount ++ current :: rest) with
    ⟨inputSteps, _inputStepsEq, inputRun⟩
  have inputRunCanonical :
      workRunExact? machine inputSteps
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) =
        some
          (configAtWord State.gateCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (natCells gateCount ++ current :: rest)) := by
    simpa [natCells_eq_cons] using inputRun
  rcases gateCount_exact gateCount
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      current rest with
    ⟨gateSteps, _gateStepsEq, gateRun⟩
  have throughInput := exactRun_add 4 inputSteps _ _ _
    bootCanonical inputRunCanonical
  have all := exactRun_add (4 + inputSteps) gateSteps
    _ _ _ throughInput gateRun
  exact ⟨(4 + inputSteps) + gateSteps, all⟩

/-- Fixed-cost companion to `canonicalHeader_exact`, exposing the literal
boot and two unary-count schedules for downstream polynomial arithmetic. -/
theorem canonicalHeader_fixed_exact (inputs gateCount : Nat)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine (2 * inputs + 2 * gateCount + 8)
        (workStartConfiguration machine
          (WorkTape.ofSymbols
            (cell00 :: cell00 ::
              (natCells inputs ++ natCells gateCount ++
                current :: rest)))) =
      some
        (configAtWord State.gateStart
          (pushCrossed (natCells gateCount)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard]))
          (current :: rest)) := by
  have boot :=
    bootVersion_exact
      cell00
      (natCellsTail inputs ++ natCells gateCount ++ current :: rest)
  have bootCanonical :
      workRunExact? machine 4
          (workStartConfiguration machine
            (WorkTape.ofSymbols
              (cell00 :: cell00 ::
                (natCells inputs ++ natCells gateCount ++
                  current :: rest)))) =
        some
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) := by
    simpa [natCells_eq_cons] using boot
  rcases inputCount_exact inputs
      [cell00, cell00, leftGuard]
      cell00
      (natCellsTail gateCount ++ current :: rest) with
    ⟨inputSteps, inputStepsEq, inputRun⟩
  have inputRunCanonical :
      workRunExact? machine inputSteps
          (configAtWord State.inputCountFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++ natCells gateCount ++
              current :: rest)) =
        some
          (configAtWord State.gateCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (natCells gateCount ++ current :: rest)) := by
    simpa [natCells_eq_cons] using inputRun
  rcases gateCount_exact gateCount
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      current rest with
    ⟨gateSteps, gateStepsEq, gateRun⟩
  have throughInput :=
    exactRun_add 4 inputSteps
      _ _ _ bootCanonical inputRunCanonical
  have all :=
    exactRun_add (4 + inputSteps) gateSteps
      _ _ _ throughInput gateRun
  have costEq :
      (4 + inputSteps) + gateSteps =
        2 * inputs + 2 * gateCount + 8 := by
    rw [inputStepsEq, gateStepsEq]
    omega
  rw [← costEq]
  exact all

/-! ### Source traces -/

/-- Control state entered immediately after one complete source token. -/
def sourceDoneState : SourceContinuation → Nat
  | .gateLeft => State.sourceStart .gateRight
  | .gateRight => State.gateEndFirst
  | .output => State.outputsEndFirst

/- Constants take the short, two-transition source path and leave both
packed cells unchanged. -/
set_option maxRecDepth 100000 in
theorem constantSource_exact (continuation : SourceContinuation)
    (value : Bool) (left : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord (State.sourceStart continuation) left
          (sourceCells (.constant value) ++ current :: rest)) =
      some
        (configAtWord (sourceDoneState continuation)
          (pushCrossed (sourceCells (.constant value)) left)
          (current :: rest)) := by
  cases continuation <;> cases value <;> rfl

set_option maxRecDepth 100000 in
private theorem constantSourceRemainder_exact
    (continuation : SourceContinuation) (value : Bool)
    (left : List WorkSymbol) (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord (State.sourceAfter01 continuation) left
          ((if value then cell01 else cell00) :: suffix)) =
      some
        (configAtWord (sourceDoneState continuation)
          ((if value then cell01 else cell00) :: left)
          suffix) := by
  cases continuation <;> cases value <;> rfl

/-! ### Gate-count decrement and launch -/

def firstSourceCell (firstWas01 : Bool) : WorkSymbol :=
  if firstWas01 then cell01 else cell00

def afterFirstSourceState (firstWas01 : Bool)
    (continuation : SourceContinuation) : Nat :=
  if firstWas01 then State.sourceAfter01 continuation
  else State.sourceAfter00 continuation

set_option maxRecDepth 100000 in
private theorem gateDecrementVersion_exact
    (firstWas01 : Bool) (left : List WorkSymbol)
    (suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementVersionFirst firstWas01) left
          (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementInputFirst firstWas01)
          (cell00 :: cell00 :: left) suffix) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementInputUnit_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementInputFirst firstWas01)
          (cell01 :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementInputEnd_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (cell10 :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementInput_exact
    (firstWas01 : Bool) (value : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (value + 1))
        (configAtWord
          (State.gateDecrementInputFirst firstWas01) left
          (natCells value ++ suffix)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (pushCrossed (natCells value) left)
          suffix) := by
  induction value generalizing left with
  | zero =>
      exact gateDecrementInputEnd_exact firstWas01 left
        suffix
  | succ value ih =>
      have first :=
        gateDecrementInputUnit_exact firstWas01 left
          (natCells value ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (value + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (value + 1) =
            2 * ((value + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [natCells, pushCrossed] using composed

set_option maxRecDepth 100000 in
private theorem gateDecrementCountBorrowed_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.gateDecrementCountFirst firstWas01)
          (countMark :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementCountSelect_exact
    (firstWas01 : Bool) (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (countMark :: cell00 :: left) rest) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementCount_exact
    (firstWas01 : Bool) (used : Nat)
    (left : List WorkSymbol) (suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.gateDecrementCountFirst firstWas01) left
          (borrowedCountCells used ++
            cell00 :: cell01 :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (pushCrossed (borrowedCountCells (used + 1)) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      exact gateDecrementCountSelect_exact firstWas01 left suffix
  | succ used ih =>
      have first :=
        gateDecrementCountBorrowed_exact firstWas01 left
          (borrowedCountCells used ++ cell00 :: cell01 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (used + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [borrowedCountCells, pushCrossed] using composed

set_option maxRecDepth 100000 in
private theorem gateDecrementSeekCursor_step
    (firstWas01 : Bool) (left : List WorkSymbol)
    (head : WorkSymbol) (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01) left
          (head :: suffix)) =
      some
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01)
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases firstWas01 <;> rfl

set_option maxRecDepth 100000 in
private theorem gateDecrementCursor_exact
    (firstWas01 : Bool) (left : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.gateDecrementSeekCursor firstWas01) left
          (cursorMark :: current :: rest)) =
      some
        (configAtWord
          (afterFirstSourceState firstWas01 .gateLeft)
          (firstSourceCell firstWas01 :: left)
          (current :: rest)) := by
  cases firstWas01 <;> rfl

private theorem gateDecrementForward_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate) (todo : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    ∃ steps,
      steps = (gatePrefix inputs done (gate :: todo)).length + 1 ∧
      workRunExact? machine steps
          (configAtWord
            (State.gateDecrementVersionFirst firstWas01)
            [leftGuard]
            (gatePrefix inputs done (gate :: todo) ++
              cursorMark :: current :: rest)) =
        some
          (guardedConfig
            (afterFirstSourceState firstWas01 .gateLeft)
            (gateParsingPrefix inputs done todo ++
              [firstSourceCell firstWas01])
            (current :: rest)) := by
  let afterCount : List WorkSymbol :=
    natCells todo.length ++ markedGateListCells done
  let afterHeader : List WorkSymbol :=
    countCells done.length (todo.length + 1) ++
      markedGateListCells done ++ cursorMark :: current :: rest
  have version :=
    gateDecrementVersion_exact firstWas01 [leftGuard]
      (natCells inputs ++ afterHeader)
  have input :=
    gateDecrementInput_exact firstWas01 inputs
      (cell00 :: cell00 :: [leftGuard]) afterHeader
  have count :=
    gateDecrementCount_exact firstWas01 done.length
      (pushCrossed (natCells inputs)
        (cell00 :: cell00 :: [leftGuard]))
      (afterCount ++ cursorMark :: current :: rest)
  have countCanonical :
      workRunExact? machine (2 * (done.length + 1))
          (configAtWord
            (State.gateDecrementCountFirst firstWas01)
            (pushCrossed (natCells inputs)
              (cell00 :: cell00 :: [leftGuard]))
            afterHeader) =
        some
          (configAtWord
            (State.gateDecrementSeekCursor firstWas01)
            (pushCrossed (borrowedCountCells (done.length + 1))
              (pushCrossed (natCells inputs)
                (cell00 :: cell00 :: [leftGuard])))
            (afterCount ++ cursorMark :: current :: rest)) := by
    simpa [afterHeader, afterCount, countCells_succ_remaining,
      List.append_assoc] using count
  have scan :=
    scanRight_exact
      (State.gateDecrementSeekCursor firstWas01)
      ordinaryCell
      (gateDecrementSeekCursor_step firstWas01)
      afterCount (cursorMark :: current :: rest)
      (pushCrossed (borrowedCountCells (done.length + 1))
        (pushCrossed (natCells inputs)
          (cell00 :: cell00 :: [leftGuard])))
      (ordinary_append
        (natCells_ordinary todo.length)
        (markedGateListCells_ordinary done))
  have cursor :=
    gateDecrementCursor_exact firstWas01
      (pushCrossed afterCount
        (pushCrossed (borrowedCountCells (done.length + 1))
          (pushCrossed (natCells inputs)
            (cell00 :: cell00 :: [leftGuard]))))
      current rest
  have throughInput := exactRun_add 2 (2 * (inputs + 1))
    _ _ _ version input
  have throughCount :=
    exactRun_add (2 + 2 * (inputs + 1))
      (2 * (done.length + 1))
      _ _ _ throughInput countCanonical
  have throughScan :=
    exactRun_add
      ((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1))
      afterCount.length
      _ _ _ throughCount scan
  have all :=
    exactRun_add
      (((2 + 2 * (inputs + 1)) +
        2 * (done.length + 1)) + afterCount.length)
      1 _ _ _ throughScan cursor
  let steps :=
    (((2 + 2 * (inputs + 1)) +
      2 * (done.length + 1)) + afterCount.length) + 1
  have costEq :
      steps =
        (gatePrefix inputs done (gate :: todo)).length + 1 := by
    simp only [steps, gatePrefix, afterCount,
      List.length_append, List.length_cons, List.length_nil,
      natCells_length, countCells_succ_remaining,
      borrowedCountCells_length]
    omega
  have endpointEq :
      firstSourceCell firstWas01 ::
          pushCrossed (markedGateListCells done)
            (pushCrossed (natCells todo.length)
              (pushCrossed
                (borrowedCountCells (done.length + 1))
                (pushCrossed (natCells inputs)
                  [cell00, cell00, leftGuard]))) =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          [leftGuard] := by
    unfold gateParsingPrefix
    rw [countCells_eq_borrowed_append]
    repeat rw [pushCrossed_append]
    rfl
  refine ⟨steps, ?_, ?_⟩
  · exact costEq
  · unfold guardedConfig
    rw [← endpointEq]
    simpa [steps, afterHeader, afterCount, gatePrefix,
      countCells_eq_borrowed_append, pushCrossed_append,
      List.append_assoc] using all

set_option maxRecDepth 100000 in
private theorem gateStartLaunch_exact
    (firstWas01 : Bool) (guardedPrefix : List WorkSymbol)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig State.gateStart guardedPrefix
          (firstSourceCell firstWas01 :: current :: rest)) =
      some
        (configAtLeftWord
          (State.gateDecrementSeekGuard firstWas01)
          (guardedPrefix.reverse ++ [leftGuard])
          (cursorMark :: current :: rest)) := by
  apply exactRun_one
  have raw :
      workStep? machine
          (guardedConfig State.gateStart guardedPrefix
            (firstSourceCell firstWas01 :: current :: rest)) =
        some
          { state := State.gateDecrementSeekGuard firstWas01
            tape :=
              ((tapeAtWord
                  (pushCrossed guardedPrefix [leftGuard])
                  (firstSourceCell firstWas01 :: current :: rest)).write
                cursorMark).moveLeft } := by
    cases firstWas01 <;> rfl
  rw [guardedMoveLeft_after_write] at raw
  exact raw

private theorem gateDecrement_exact
    (firstWas01 : Bool) (inputs : Nat)
    (done : List RawGate) (gate : RawGate) (todo : List RawGate)
    (current : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine
        (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (firstSourceCell firstWas01 :: current :: rest)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 .gateLeft)
          (gateParsingPrefix inputs done todo ++
            [firstSourceCell firstWas01])
          (current :: rest)) := by
  let logicalPrefix := gatePrefix inputs done (gate :: todo)
  have launch :=
    gateStartLaunch_exact firstWas01 logicalPrefix current rest
  have backward :=
    gateDecrementSeekGuard_scan_exact firstWas01 logicalPrefix
      (cursorMark :: current :: rest)
      (gatePrefix_ordinary inputs done (gate :: todo))
  have guard :=
    gateDecrementGuard_exact firstWas01
      (logicalPrefix ++ cursorMark :: current :: rest)
  rcases gateDecrementForward_exact firstWas01 inputs done gate todo
      current rest with
    ⟨forwardSteps, forwardStepsEq, forward⟩
  have throughBackward :=
    exactRun_add 1 logicalPrefix.length _ _ _ launch backward
  have throughGuard :=
    exactRun_add (1 + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have all :=
    exactRun_add ((1 + logicalPrefix.length) + 1)
      forwardSteps _ _ _ throughGuard forward
  rw [forwardStepsEq] at all
  have costEq :
      ((1 + logicalPrefix.length) + 1) +
          (logicalPrefix.length + 1) =
        2 * logicalPrefix.length + 3 := by
    omega
  rw [costEq] at all
  simpa [logicalPrefix] using all

set_option maxRecDepth 100000 in
private theorem gateEnd_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.gateEndFirst left
          (cell01 :: cell11 :: suffix)) =
      some
        (configAtWord State.gateStart
          (cell11 :: gateMark :: left) suffix) := by
  rfl

private theorem gateEndGuarded_exact
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate)
    (suffix : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.gateEndFirst
          (gateParsingPrefix inputs done todo ++
            sourceCells gate.left ++ sourceCells gate.right)
          (cell01 :: cell11 :: suffix)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ [gate]) todo)
          suffix) := by
  have base :=
    gateEnd_exact
      (pushCrossed
        (gateParsingPrefix inputs done todo ++
          sourceCells gate.left ++ sourceCells gate.right)
        [leftGuard])
      suffix
  have endpointEq :
      cell11 :: gateMark ::
          pushCrossed
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left ++ sourceCells gate.right)
            [leftGuard] =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            ((sourceCells gate.left ++ sourceCells gate.right) ++
              [gateMark, cell11]))
          [leftGuard] := by
    simp only [pushCrossed_append, pushCrossed]
  rw [gatePrefix_snoc]
  unfold guardedConfig markedGateCells
  rw [← endpointEq]
  exact base

/- One complete declared gate whose two inputs are constants: decrement the
declared gate count, parse both source tokens, install the persistent gate
anchor, and return to the next gate boundary. -/
set_option maxRecDepth 100000 in
theorem constantGate_exact
    (inputs : Nat) (done todo : List RawGate)
    (leftValue rightValue : Bool)
    (after : List WorkSymbol) :
    let gate : RawGate :=
      { left := .constant leftValue
        right := .constant rightValue }
    workRunExact? machine
        (2 * (gatePrefix inputs done (gate :: todo)).length + 8)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (gateCells gate ++ gateListCells todo ++ after)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ [gate]) todo)
          (gateListCells todo ++ after)) := by
  dsimp only
  let gate : RawGate :=
    { left := .constant leftValue
      right := .constant rightValue }
  have decrement :=
    gateDecrement_exact true inputs done gate todo
      (if leftValue then cell01 else cell00)
      (sourceCells (.constant rightValue) ++
        [cell01, cell11] ++ gateListCells todo ++ after)
  have leftSource :=
    constantSourceRemainder_exact .gateLeft leftValue
      (pushCrossed
        (gateParsingPrefix inputs done todo ++ [cell01])
        [leftGuard])
      (sourceCells (.constant rightValue) ++
        [cell01, cell11] ++ gateListCells todo ++ after)
  have leftEndpointEq :
      (if leftValue then cell01 else cell00) ::
          pushCrossed
            (gateParsingPrefix inputs done todo ++ [cell01])
            [leftGuard] =
        pushCrossed
          (gateParsingPrefix inputs done todo ++
            sourceCells (.constant leftValue))
          [leftGuard] := by
    cases leftValue <;>
      simp [sourceCells, pushCrossed_append, pushCrossed]
  have leftSourceCanonical :
      workRunExact? machine 1
          (guardedConfig (State.sourceAfter01 .gateLeft)
            (gateParsingPrefix inputs done todo ++ [cell01])
            ((if leftValue then cell01 else cell00) ::
              sourceCells (.constant rightValue) ++
                [cell01, cell11] ++ gateListCells todo ++ after)) =
        some
          (guardedConfig (State.sourceStart .gateRight)
            (gateParsingPrefix inputs done todo ++
              sourceCells (.constant leftValue))
            (sourceCells (.constant rightValue) ++
              [cell01, cell11] ++ gateListCells todo ++ after)) := by
    unfold guardedConfig
    rw [← leftEndpointEq]
    simpa [sourceDoneState] using leftSource
  have rightSource :=
    constantSource_exact .gateRight rightValue
      (pushCrossed
        (gateParsingPrefix inputs done todo ++
          sourceCells (.constant leftValue))
        [leftGuard])
      cell01
      (cell11 :: gateListCells todo ++ after)
  have rightEndpointEq :
      pushCrossed (sourceCells (.constant rightValue))
          (pushCrossed
            (gateParsingPrefix inputs done todo ++
              sourceCells (.constant leftValue))
            [leftGuard]) =
        pushCrossed
          ((gateParsingPrefix inputs done todo ++
              sourceCells (.constant leftValue)) ++
            sourceCells (.constant rightValue))
          [leftGuard] := by
    exact
      (pushCrossed_append
        (gateParsingPrefix inputs done todo ++
          sourceCells (.constant leftValue))
        (sourceCells (.constant rightValue))
        [leftGuard]).symm
  have rightSourceCanonical :
      workRunExact? machine 2
          (guardedConfig (State.sourceStart .gateRight)
            (gateParsingPrefix inputs done todo ++
              sourceCells (.constant leftValue))
            (sourceCells (.constant rightValue) ++
              [cell01, cell11] ++ gateListCells todo ++ after)) =
        some
          (guardedConfig State.gateEndFirst
            (gateParsingPrefix inputs done todo ++
              sourceCells (.constant leftValue) ++
              sourceCells (.constant rightValue))
            (cell01 :: cell11 :: gateListCells todo ++ after)) := by
    unfold guardedConfig
    rw [← rightEndpointEq]
    simpa [sourceDoneState, sourceCells, List.append_assoc]
      using rightSource
  have ending :=
    gateEndGuarded_exact inputs done gate todo
      (gateListCells todo ++ after)
  have throughLeft :=
    exactRun_add
      (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
      1 _ _ _ decrement leftSourceCanonical
  have throughRight :=
    exactRun_add
      ((2 * (gatePrefix inputs done (gate :: todo)).length + 3) + 1)
      2 _ _ _ throughLeft rightSourceCanonical
  have all :=
    exactRun_add
      (((2 * (gatePrefix inputs done (gate :: todo)).length + 3) + 1) + 2)
      2 _ _ _ throughRight ending
  have costEq :
      (((2 * (gatePrefix inputs done (gate :: todo)).length + 3) + 1) + 2) +
          2 =
        2 * (gatePrefix inputs done (gate :: todo)).length + 8 := by
    omega
  have initialWordEq :
      firstSourceCell true ::
          (if leftValue then cell01 else cell00) ::
            (sourceCells (.constant rightValue) ++
              [cell01, cell11] ++ gateListCells todo ++ after) =
        gateCells gate ++ gateListCells todo ++ after := by
    cases leftValue <;>
      simp [firstSourceCell, gate, gateCells, sourceCells,
        List.append_assoc]
  rw [costEq] at all
  rw [← initialWordEq]
  simpa [gate, guardedConfig,
    pushCrossed_append, List.append_assoc] using all

/-! ### Indexed reference traces -/

/-- Canonical checkpoint at the first cell of a unary input-source index.
`used` input-count units are temporarily borrowed and `between` is the
ordinary word between the input-count field and this index. -/
def inputReferenceConfiguration
    (continuation : SourceContinuation)
    (used remaining : Nat) (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol) :
    WorkConfiguration :=
  guardedConfig (State.indexFirst .input continuation)
    ([cell00, cell00] ++ countCells used remaining ++ between)
    (natCells index ++ suffix)

/-- Successful input-reference endpoint, with every temporary count marker
restored and the unary index moved into the guarded prefix. -/
def inputReferenceSuccessConfiguration
    (continuation : SourceContinuation)
    (inputCount : Nat) (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol) :
    WorkConfiguration :=
  guardedConfig (sourceDoneState continuation)
    ([cell00, cell00] ++ natCells inputCount ++
      between ++ natCells index)
    suffix

/-- Canonical checkpoint at the first cell of a unary prior-gate index. -/
def gateReferenceConfiguration
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol) :
    WorkConfiguration :=
  guardedConfig (State.indexFirst .priorGate continuation)
    (header ++
      borrowedGateListCells borrowed ++
      markedGateListCells available ++ between)
    (natCells index ++ suffix)

/-- Canonical fixed header crossed while checking a prior-gate reference. -/
def gateReferenceHeader
    (inputs gateCountUsed gateCountRemaining : Nat) :
    List WorkSymbol :=
  [cell00, cell00] ++ natCells inputs ++
    countCells gateCountUsed gateCountRemaining

/-- Successful prior-gate endpoint with every borrowed anchor and unary
cursor restored. -/
def gateReferenceSuccessConfiguration
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (gates : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol) :
    WorkConfiguration :=
  guardedConfig (sourceDoneState continuation)
    (header ++ markedGateListCells gates ++
      between ++ natCells index)
    suffix

private theorem gateReferenceHeader_ordinary
    (inputs gateCountUsed gateCountRemaining : Nat) :
    ∀ symbol,
      symbol ∈
          gateReferenceHeader inputs gateCountUsed gateCountRemaining →
        ordinaryCell symbol := by
  intro symbol member
  unfold gateReferenceHeader at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell00_ordinary
      · contradiction
    · exact natCells_ordinary inputs symbol member
  · exact
      countCells_ordinary gateCountUsed gateCountRemaining symbol member

private theorem gateReferenceHeader_no_gateMark
    (inputs gateCountUsed gateCountRemaining : Nat) :
    ∀ symbol,
      symbol ∈
          gateReferenceHeader inputs gateCountUsed gateCountRemaining →
        symbol ≠ gateMark := by
  intro symbol member
  unfold gateReferenceHeader at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        decide
      · subst symbol
        decide
      · contradiction
    · exact natCells_no_gateMark inputs symbol member
  · exact
      countCells_no_gateMark gateCountUsed gateCountRemaining
        symbol member

def consumeAfterGuardState (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  match bound with
  | .input => State.consumeInputVersionFirst bound continuation
  | .priorGate => State.consumeGateAnchor bound continuation

def finishAfterGuardState (bound : ReferenceBound)
    (continuation : SourceContinuation) : Nat :=
  match bound with
  | .input => State.finishInputVersionFirst bound continuation
  | .priorGate => State.finishGateCheckAnchor bound continuation

set_option maxRecDepth 100000 in
theorem referenceIndexFirst_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (guardedPrefix : List WorkSymbol)
    (second : WorkSymbol) (rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.indexFirst bound continuation)
          guardedPrefix (cell00 :: second :: rest)) =
      some
        (guardedConfig (State.indexSecond bound continuation)
          (guardedPrefix ++ [cell00]) (second :: rest)) := by
  cases bound <;> cases continuation <;>
    unfold guardedConfig <;>
    rw [pushCrossed_append] <;> rfl

set_option maxRecDepth 100000 in
theorem referenceIndexUnitLaunch_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (guardedPrefix : List WorkSymbol)
    (rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.indexSecond bound continuation)
          (guardedPrefix ++ [cell00]) (cell01 :: rest)) =
      some
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          ((guardedPrefix ++ [cell00]).reverse ++ [leftGuard])
          (cursorMark :: rest)) := by
  apply exactRun_one
  have raw :
      workStep? machine
          (guardedConfig (State.indexSecond bound continuation)
            (guardedPrefix ++ [cell00]) (cell01 :: rest)) =
        some
          { state := State.consumeSeekGuard bound continuation
            tape :=
              ((tapeAtWord
                  (pushCrossed (guardedPrefix ++ [cell00])
                    [leftGuard])
                  (cell01 :: rest)).write cursorMark).moveLeft } := by
    cases bound <;> cases continuation <;> rfl
  rw [guardedMoveLeft_after_write] at raw
  exact raw

set_option maxRecDepth 100000 in
theorem referenceIndexFinishLaunch_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (guardedPrefix : List WorkSymbol)
    (rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.indexSecond bound continuation)
          (guardedPrefix ++ [cell00]) (cell10 :: rest)) =
      some
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          ((guardedPrefix ++ [cell00]).reverse ++ [leftGuard])
          (cursorMark :: rest)) := by
  apply exactRun_one
  have raw :
      workStep? machine
          (guardedConfig (State.indexSecond bound continuation)
            (guardedPrefix ++ [cell00]) (cell10 :: rest)) =
        some
          { state := State.finishSeekGuard bound continuation
            tape :=
              ((tapeAtWord
                  (pushCrossed (guardedPrefix ++ [cell00])
                    [leftGuard])
                  (cell10 :: rest)).write cursorMark).moveLeft } := by
    cases bound <;> cases continuation <;> rfl
  rw [guardedMoveLeft_after_write] at raw
  exact raw

set_option maxRecDepth 100000 in
private theorem referenceConsumeSeekGuard_step
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases bound <;> cases continuation <;> rfl

theorem referenceConsumeSeekGuard_scan_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.consumeSeekGuard bound continuation)
      ordinaryCell
      (referenceConsumeSeekGuard_step bound continuation)
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
theorem referenceConsumeGuard_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.consumeSeekGuard bound continuation)
          [leftGuard] suffix) =
      some
        (configAtWord
          (consumeAfterGuardState bound continuation)
          [leftGuard] suffix) := by
  cases bound <;> cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem referenceFinishSeekGuard_step
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases bound <;> cases continuation <;> rfl

theorem referenceFinishSeekGuard_scan_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.finishSeekGuard bound continuation)
      ordinaryCell
      (referenceFinishSeekGuard_step bound continuation)
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
theorem referenceFinishGuard_exact
    (bound : ReferenceBound)
    (continuation : SourceContinuation)
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.finishSeekGuard bound continuation)
          [leftGuard] suffix) =
      some
        (configAtWord
          (finishAfterGuardState bound continuation)
          [leftGuard] suffix) := by
  cases bound <;> cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputConsumeVersion_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.consumeInputVersionFirst .input continuation)
          left (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.consumeInputFirst .input continuation)
          (cell00 :: cell00 :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputConsumeBorrowed_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.consumeInputFirst .input continuation)
          left (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.consumeInputFirst .input continuation)
          (countMark :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputConsumeSelect_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.consumeInputFirst .input continuation)
          left (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.consumeSeekCursor .input continuation)
          (countMark :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputConsumeExhausted_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.consumeInputFirst .input continuation)
          left (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.cleanupSeekGuard
          (cell00 :: left) (cell10 :: rest)) := by
  cases continuation <;> rfl

theorem inputConsumeCount_exact
    (continuation : SourceContinuation)
    (used : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.consumeInputFirst .input continuation) left
          (borrowedCountCells used ++
            cell00 :: cell01 :: suffix)) =
      some
        (configAtWord
          (State.consumeSeekCursor .input continuation)
          (pushCrossed (borrowedCountCells (used + 1)) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      exact inputConsumeSelect_exact continuation left suffix
  | succ used ih =>
      have first :=
        inputConsumeBorrowed_exact continuation left
          (borrowedCountCells used ++ cell00 :: cell01 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (used + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [borrowedCountCells, pushCrossed] using composed

theorem inputConsumeCountExhausted_exact
    (continuation : SourceContinuation)
    (used : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.consumeInputFirst .input continuation) left
          (borrowedCountCells used ++
            cell00 :: cell10 :: suffix)) =
      some
        (configAtWord State.cleanupSeekGuard
          (cell00 :: pushCrossed (borrowedCountCells used) left)
          (cell10 :: suffix)) := by
  induction used generalizing left with
  | zero =>
      exact inputConsumeExhausted_exact continuation left suffix
  | succ used ih =>
      have first :=
        inputConsumeBorrowed_exact continuation left
          (borrowedCountCells used ++ cell00 :: cell10 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (used + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [borrowedCountCells, pushCrossed] using composed

set_option maxRecDepth 100000 in
private theorem inputConsumeSeekCursor_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord
          (State.consumeSeekCursor .input continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.consumeSeekCursor .input continuation)
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputConsumeCursor_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.consumeSeekCursor .input continuation)
          left (cursorMark :: rest)) =
      some
        (configAtWord
          (State.indexFirst .input continuation)
          (cell01 :: left) rest) := by
  cases continuation <;> rfl

private theorem inputReferencePrefix_ordinary
    (used remaining : Nat) (between : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    ∀ symbol,
      symbol ∈
          ([cell00, cell00] ++ countCells used remaining ++ between) →
        ordinaryCell symbol := by
  intro symbol member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | h | impossible
      · subst symbol
        exact cell00_ordinary
      · subst symbol
        exact cell00_ordinary
      · contradiction
    · exact countCells_ordinary used remaining symbol member
  · exact betweenOrdinary symbol member

/-- Exact cost of borrowing one input-count unit for one unary index unit. -/
def inputReferenceConsumeUnitSteps
    (used remaining : Nat) (between : List WorkSymbol) : Nat :=
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used (remaining + 1) ++ between
  let forwardScan := natCells remaining ++ between ++ [cell00]
  2 + (guardedPrefix ++ [cell00]).length + 1 +
    2 + 2 * (used + 1) + forwardScan.length + 1

/-- One unary input-index unit is crossed against the next unborrowed
declared-input unit.  The arbitrary tail is preserved exactly, so malformed
unary-token traces can reuse the same cursor sweep before they reject. -/
theorem inputReferenceConsumeUnitTail_exact
    (continuation : SourceContinuation)
    (used remaining : Nat)
    (between indexTail : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    workRunExact? machine
        (inputReferenceConsumeUnitSteps used remaining between)
        (guardedConfig (State.indexFirst .input continuation)
          ([cell00, cell00] ++ countCells used (remaining + 1) ++
            between)
          (cell00 :: cell01 :: indexTail)) =
      some
        (guardedConfig (State.indexFirst .input continuation)
          ([cell00, cell00] ++ countCells (used + 1) remaining ++
            (between ++ [cell00, cell01]))
          indexTail) := by
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used (remaining + 1) ++ between
  let forwardScan := natCells remaining ++ between ++ [cell00]
  let indexSuffix := indexTail
  have first :=
    referenceIndexFirst_exact .input continuation guardedPrefix
      cell01 indexSuffix
  have launch :=
    referenceIndexUnitLaunch_exact .input continuation guardedPrefix
      indexSuffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have prefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol :=
    inputReferencePrefix_ordinary used (remaining + 1) between
      betweenOrdinary
  have scanPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix ++ [cell00] →
        ordinaryCell symbol :=
    ordinary_append prefixOrdinary
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact cell00_ordinary
        · contradiction)
  have backward :=
    referenceConsumeSeekGuard_scan_exact .input continuation
      (guardedPrefix ++ [cell00]) (cursorMark :: indexSuffix)
      scanPrefixOrdinary
  have guard :=
    referenceConsumeGuard_exact .input continuation
      ((guardedPrefix ++ [cell00]) ++ cursorMark :: indexSuffix)
  have version :=
    inputConsumeVersion_exact continuation [leftGuard]
      (countCells used (remaining + 1) ++
        between ++ [cell00] ++ cursorMark :: indexSuffix)
  have count :=
    inputConsumeCount_exact continuation used
      [cell00, cell00, leftGuard]
      (forwardScan ++ cursorMark :: indexSuffix)
  have countCanonical :
      workRunExact? machine (2 * (used + 1))
          (configAtWord
            (State.consumeInputFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used (remaining + 1) ++
              between ++ [cell00] ++ cursorMark :: indexSuffix)) =
        some
          (configAtWord
            (State.consumeSeekCursor .input continuation)
            (pushCrossed (borrowedCountCells (used + 1))
              [cell00, cell00, leftGuard])
            (forwardScan ++ cursorMark :: indexSuffix)) := by
    simpa [forwardScan, countCells_succ_remaining,
      List.append_assoc] using count
  have forwardOrdinary :
      ∀ symbol, symbol ∈ forwardScan → ordinaryCell symbol := by
    unfold forwardScan
    apply ordinary_append
    · apply ordinary_append
      · exact natCells_ordinary remaining
      · exact betweenOrdinary
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have forward :=
    scanRight_exact
      (State.consumeSeekCursor .input continuation)
      ordinaryCell
      (inputConsumeSeekCursor_step continuation)
      forwardScan (cursorMark :: indexSuffix)
      (pushCrossed (borrowedCountCells (used + 1))
        [cell00, cell00, leftGuard])
      forwardOrdinary
  have cursor :=
    inputConsumeCursor_exact continuation
      (pushCrossed forwardScan
        (pushCrossed (borrowedCountCells (used + 1))
          [cell00, cell00, leftGuard]))
      indexSuffix
  have cursorCanonical :
      workRunExact? machine 1
          (configAtWord
            (State.consumeSeekCursor .input continuation)
            (pushCrossed forwardScan
              (pushCrossed (borrowedCountCells (used + 1))
                [cell00, cell00, leftGuard]))
            (cursorMark :: indexSuffix)) =
        some
          (configAtWord
            (State.indexFirst .input continuation)
            (cell01 ::
              pushCrossed forwardScan
                (pushCrossed (borrowedCountCells (used + 1))
                  [cell00, cell00, leftGuard]))
            indexSuffix) := by
    exact cursor
  have throughBackward :=
    exactRun_add 2 (guardedPrefix ++ [cell00]).length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add
      (2 + (guardedPrefix ++ [cell00]).length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      ((2 + (guardedPrefix ++ [cell00]).length) + 1) 2
      _ _ _ throughGuard version
  have throughCount :=
    exactRun_add
      (((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2)
      (2 * (used + 1))
      _ _ _ throughVersion countCanonical
  have throughForward :=
    exactRun_add
      ((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1))
      forwardScan.length
      _ _ _ throughCount forward
  have all :=
    exactRun_add
      (((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + forwardScan.length)
      1 _ _ _ throughForward cursorCanonical
  have endpointEq :
      cell01 ::
          pushCrossed forwardScan
            (pushCrossed (borrowedCountCells (used + 1))
              [cell00, cell00, leftGuard]) =
        pushCrossed
          ([cell00, cell00] ++ countCells (used + 1) remaining ++
            (between ++ [cell00, cell01]))
          [leftGuard] := by
    unfold forwardScan
    rw [countCells_eq_borrowed_append]
    repeat rw [pushCrossed_append]
    rfl
  unfold inputReferenceConsumeUnitSteps
  unfold guardedConfig
  rw [← endpointEq]
  simpa [guardedPrefix, forwardScan, indexSuffix, guardedConfig,
    List.append_assoc] using all

/-- One in-range canonical unary input-index unit is crossed against the next
unborrowed declared-input unit.  Both cursors remain on tape for the recursive
index trace. -/
theorem inputReferenceConsumeUnit_exact
    (continuation : SourceContinuation)
    (used remaining index : Nat)
    (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    workRunExact? machine
        (inputReferenceConsumeUnitSteps used remaining between)
        (inputReferenceConfiguration continuation used (remaining + 1)
          between (index + 1) suffix) =
      some
        (inputReferenceConfiguration continuation (used + 1) remaining
          (between ++ [cell00, cell01]) index suffix) := by
  simpa [inputReferenceConfiguration, natCells, List.append_assoc] using
    inputReferenceConsumeUnitTail_exact continuation used remaining
      between (natCells index ++ suffix) betweenOrdinary

set_option maxRecDepth 100000 in
private theorem inputFinishVersion_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputVersionFirst .input continuation)
          left (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.finishInputCheckFirst .input continuation)
          (cell00 :: cell00 :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishCheckBorrowed_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputCheckFirst .input continuation)
          left (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.finishInputCheckFirst .input continuation)
          (countMark :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishCheckWitness_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputCheckFirst .input continuation)
          left (cell00 :: cell01 :: rest)) =
      some
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          (cell00 :: left) (cell01 :: rest)) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishCheckExhausted_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputCheckFirst .input continuation)
          left (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.cleanupSeekGuard
          (cell00 :: left) (cell10 :: rest)) := by
  cases continuation <;> rfl

theorem inputFinishCheck_exact
    (continuation : SourceContinuation)
    (used : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.finishInputCheckFirst .input continuation) left
          (borrowedCountCells used ++
            cell00 :: cell01 :: suffix)) =
      some
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          (cell00 :: pushCrossed (borrowedCountCells used) left)
          (cell01 :: suffix)) := by
  induction used generalizing left with
  | zero =>
      exact inputFinishCheckWitness_exact continuation left suffix
  | succ used ih =>
      have first :=
        inputFinishCheckBorrowed_exact continuation left
          (borrowedCountCells used ++ cell00 :: cell01 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (used + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [borrowedCountCells, pushCrossed] using composed

theorem inputFinishCheckExhaustedRun_exact
    (continuation : SourceContinuation)
    (used : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + 1))
        (configAtWord
          (State.finishInputCheckFirst .input continuation) left
          (borrowedCountCells used ++
            cell00 :: cell10 :: suffix)) =
      some
        (configAtWord State.cleanupSeekGuard
          (cell00 :: pushCrossed (borrowedCountCells used) left)
          (cell10 :: suffix)) := by
  induction used generalizing left with
  | zero =>
      exact inputFinishCheckExhausted_exact continuation left suffix
  | succ used ih =>
      have first :=
        inputFinishCheckBorrowed_exact continuation left
          (borrowedCountCells used ++ cell00 :: cell10 :: suffix)
      have tail := ih (countMark :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (used + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (used + 1) =
            2 * ((used + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [borrowedCountCells, pushCrossed] using composed

set_option maxRecDepth 100000 in
private theorem inputFinishReturnGuard_step
    (continuation : SourceContinuation)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases continuation <;> rfl

theorem inputFinishReturnGuard_scan_exact
    (continuation : SourceContinuation)
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.finishInputReturnGuard .input continuation)
      ordinaryCell
      (inputFinishReturnGuard_step continuation)
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem inputFinishReturnGuard_exact
    (continuation : SourceContinuation)
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.finishInputReturnGuard .input continuation)
          [leftGuard] suffix) =
      some
        (configAtWord
          (State.finishInputRestoreVersionFirst .input continuation)
          [leftGuard] suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishRestoreVersion_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputRestoreVersionFirst .input continuation)
          left (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          (cell00 :: cell00 :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishRestoreBorrowed_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          left (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          (cell01 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishRestoreUnit_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          left (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          (cell01 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishRestoreEnd_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          left (cell00 :: cell10 :: rest)) =
      some
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          (cell10 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

private theorem inputFinishRestoreNat_exact
    (continuation : SourceContinuation)
    (remaining : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (remaining + 1))
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          left (natCells remaining ++ suffix)) =
      some
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          (pushCrossed (natCells remaining) left) suffix) := by
  induction remaining generalizing left with
  | zero =>
      exact inputFinishRestoreEnd_exact continuation left suffix
  | succ remaining ih =>
      have first :=
        inputFinishRestoreUnit_exact continuation left
          (natCells remaining ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have composed := exactRun_add 2 (2 * (remaining + 1))
        _ _ _ first tail
      have costEq :
          2 + 2 * (remaining + 1) =
            2 * ((remaining + 1) + 1) := by
        omega
      rw [costEq] at composed
      simpa [natCells, pushCrossed] using composed

theorem inputFinishRestoreCount_exact
    (continuation : SourceContinuation)
    (used remaining : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + remaining + 1))
        (configAtWord
          (State.finishInputRestoreFirst .input continuation)
          left (countCells used remaining ++ suffix)) =
      some
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          (pushCrossed (natCells (used + remaining)) left)
          suffix) := by
  induction used generalizing left with
  | zero =>
      simpa [countCells] using
        inputFinishRestoreNat_exact continuation remaining left suffix
  | succ used ih =>
      have first :=
        inputFinishRestoreBorrowed_exact continuation left
          (countCells used remaining ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have composed :=
        exactRun_add 2 (2 * (used + remaining + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (used + remaining + 1) =
            2 * ((used + 1) + remaining + 1) := by
        omega
      have totalEq :
          (used + 1) + remaining = (used + remaining) + 1 := by
        omega
      have endpointEq :
          pushCrossed (natCells (used + remaining))
              (cell01 :: cell00 :: left) =
            pushCrossed (natCells ((used + 1) + remaining))
              left := by
        rw [totalEq]
        simp [natCells, pushCrossed]
      rw [costEq] at composed
      rw [endpointEq] at composed
      simpa [countCells] using composed

set_option maxRecDepth 100000 in
private theorem inputFinishSeekCursor_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem inputFinishCursor_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.finishInputSeekCursor .input continuation)
          left (cursorMark :: suffix)) =
      some
        (configAtWord (sourceDoneState continuation)
          (cell10 :: left) suffix) := by
  cases continuation <;> rfl

/-- Exact cost of the strict in-range witness check and full restoration at
the unary index terminator. -/
def inputReferenceFinishSteps
    (used spare : Nat) (between : List WorkSymbol) : Nat :=
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used (spare + 1) ++ between
  let checkPrefix :=
    [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
  let cursorScan := between ++ [cell00]
  2 + (guardedPrefix ++ [cell00]).length + 1 +
    2 + 2 * (used + 1) + checkPrefix.length + 1 +
    2 + 2 * (used + (spare + 1) + 1) +
    cursorScan.length + 1

/-- Finishing an in-range input reference witnesses one still-unborrowed
input unit, restores every input-count marker, restores the unary terminator,
and enters the source continuation. -/
theorem inputReferenceFinishInRange_exact
    (continuation : SourceContinuation)
    (used spare : Nat) (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    workRunExact? machine
        (inputReferenceFinishSteps used spare between)
        (inputReferenceConfiguration continuation used (spare + 1)
          between 0 suffix) =
      some
        (inputReferenceSuccessConfiguration continuation
          (used + (spare + 1)) between 0 suffix) := by
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used (spare + 1) ++ between
  let checkPrefix :=
    [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
  let checkSuffix :=
    natCells spare ++ between ++ [cell00, cursorMark] ++ suffix
  let cursorScan := between ++ [cell00]
  have first :=
    referenceIndexFirst_exact .input continuation guardedPrefix
      cell10 suffix
  have launch :=
    referenceIndexFinishLaunch_exact .input continuation guardedPrefix
      suffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have prefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol :=
    inputReferencePrefix_ordinary used (spare + 1) between
      betweenOrdinary
  have scanPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix ++ [cell00] →
        ordinaryCell symbol :=
    ordinary_append prefixOrdinary
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact cell00_ordinary
        · contradiction)
  have backward :=
    referenceFinishSeekGuard_scan_exact .input continuation
      (guardedPrefix ++ [cell00]) (cursorMark :: suffix)
      scanPrefixOrdinary
  have guard :=
    referenceFinishGuard_exact .input continuation
      ((guardedPrefix ++ [cell00]) ++ cursorMark :: suffix)
  have version :=
    inputFinishVersion_exact continuation [leftGuard]
      (countCells used (spare + 1) ++
        between ++ [cell00, cursorMark] ++ suffix)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord
            (finishAfterGuardState .input continuation)
            [leftGuard]
            ((guardedPrefix ++ [cell00]) ++ cursorMark :: suffix)) =
        some
          (configAtWord
            (State.finishInputCheckFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used (spare + 1) ++
              between ++ [cell00, cursorMark] ++ suffix)) := by
    simpa [finishAfterGuardState, guardedPrefix,
      List.append_assoc] using version
  have check :=
    inputFinishCheck_exact continuation used
      [cell00, cell00, leftGuard] checkSuffix
  have checkCanonical :
      workRunExact? machine (2 * (used + 1))
          (configAtWord
            (State.finishInputCheckFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used (spare + 1) ++
              between ++ [cell00, cursorMark] ++ suffix)) =
        some
          (configAtLeftWord
            (State.finishInputReturnGuard .input continuation)
            (checkPrefix.reverse ++ [leftGuard])
            (cell01 :: checkSuffix)) := by
    have returnLeftEq :
        cell00 ::
            pushCrossed (borrowedCountCells used)
              [cell00, cell00, leftGuard] =
          checkPrefix.reverse ++ [leftGuard] := by
      rw [← pushCrossed_eq_reverse_append]
      unfold checkPrefix
      repeat rw [pushCrossed_append]
      rfl
    rw [← returnLeftEq]
    simpa [checkSuffix, countCells_succ_remaining,
      List.append_assoc] using check
  have checkPrefixOrdinary :
      ∀ symbol, symbol ∈ checkPrefix → ordinaryCell symbol := by
    unfold checkPrefix
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact cell00_ordinary
        · subst symbol
          exact cell00_ordinary
        · contradiction
      · exact countCells_ordinary used 0 symbol (by
          rw [countCells_eq_borrowed_append]
          exact List.mem_append.mpr (Or.inl member))
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have returnScan :=
    inputFinishReturnGuard_scan_exact continuation checkPrefix
      (cell01 :: checkSuffix) checkPrefixOrdinary
  have returnGuard :=
    inputFinishReturnGuard_exact continuation
      (checkPrefix ++ cell01 :: checkSuffix)
  have restoreVersion :=
    inputFinishRestoreVersion_exact continuation [leftGuard]
      (countCells used (spare + 1) ++
        between ++ [cell00, cursorMark] ++ suffix)
  have restoreVersionCanonical :
      workRunExact? machine 2
          (configAtWord
            (State.finishInputRestoreVersionFirst .input continuation)
            [leftGuard] (checkPrefix ++ cell01 :: checkSuffix)) =
        some
          (configAtWord
            (State.finishInputRestoreFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used (spare + 1) ++
              between ++ [cell00, cursorMark] ++ suffix)) := by
    simpa [checkPrefix, checkSuffix, countCells_succ_remaining,
      List.append_assoc] using restoreVersion
  have restoreCount :=
    inputFinishRestoreCount_exact continuation used (spare + 1)
      [cell00, cell00, leftGuard]
      (between ++ [cell00, cursorMark] ++ suffix)
  have restoreCountCanonical :
      workRunExact? machine (2 * (used + (spare + 1) + 1))
          (configAtWord
            (State.finishInputRestoreFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used (spare + 1) ++
              between ++ [cell00, cursorMark] ++ suffix)) =
        some
          (configAtWord
            (State.finishInputSeekCursor .input continuation)
            (pushCrossed (natCells (used + (spare + 1)))
              [cell00, cell00, leftGuard])
            (between ++ [cell00, cursorMark] ++ suffix)) := by
    simpa only [List.append_assoc] using restoreCount
  have cursorScanOrdinary :
      ∀ symbol, symbol ∈ cursorScan → ordinaryCell symbol := by
    unfold cursorScan
    apply ordinary_append
    · exact betweenOrdinary
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have seekCursor :=
    scanRight_exact
      (State.finishInputSeekCursor .input continuation)
      ordinaryCell
      (inputFinishSeekCursor_step continuation)
      cursorScan (cursorMark :: suffix)
      (pushCrossed (natCells (used + (spare + 1)))
        [cell00, cell00, leftGuard])
      cursorScanOrdinary
  have seekCursorCanonical :
      workRunExact? machine cursorScan.length
          (configAtWord
            (State.finishInputSeekCursor .input continuation)
            (pushCrossed (natCells (used + (spare + 1)))
              [cell00, cell00, leftGuard])
            (between ++ [cell00, cursorMark] ++ suffix)) =
        some
          (configAtWord
            (State.finishInputSeekCursor .input continuation)
            (pushCrossed cursorScan
              (pushCrossed (natCells (used + (spare + 1)))
                [cell00, cell00, leftGuard]))
            (cursorMark :: suffix)) := by
    simpa [cursorScan, List.append_assoc] using seekCursor
  have cursor :=
    inputFinishCursor_exact continuation
      (pushCrossed cursorScan
        (pushCrossed (natCells (used + (spare + 1)))
          [cell00, cell00, leftGuard]))
      suffix
  have throughBackward :=
    exactRun_add 2 (guardedPrefix ++ [cell00]).length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add
      (2 + (guardedPrefix ++ [cell00]).length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      ((2 + (guardedPrefix ++ [cell00]).length) + 1) 2
      _ _ _ throughGuard versionCanonical
  have throughCheck :=
    exactRun_add
      (((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2)
      (2 * (used + 1))
      _ _ _ throughVersion checkCanonical
  have throughReturnScan :=
    exactRun_add
      ((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1))
      checkPrefix.length
      _ _ _ throughCheck returnScan
  have throughReturnGuard :=
    exactRun_add
      (((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + checkPrefix.length)
      1 _ _ _ throughReturnScan returnGuard
  have throughRestoreVersion :=
    exactRun_add
      ((((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + checkPrefix.length) + 1)
      2 _ _ _ throughReturnGuard restoreVersionCanonical
  have throughRestoreCount :=
    exactRun_add
      (((((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + checkPrefix.length) + 1) + 2)
      (2 * (used + (spare + 1) + 1))
      _ _ _ throughRestoreVersion restoreCountCanonical
  have throughSeek :=
    exactRun_add
      ((((((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + checkPrefix.length) + 1) + 2) +
        2 * (used + (spare + 1) + 1))
      cursorScan.length
      _ _ _ throughRestoreCount seekCursorCanonical
  have all :=
    exactRun_add
      (((((((((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2) +
        2 * (used + 1)) + checkPrefix.length) + 1) + 2) +
        2 * (used + (spare + 1) + 1)) + cursorScan.length)
      1 _ _ _ throughSeek cursor
  have endpointEq :
      cell10 ::
          pushCrossed cursorScan
            (pushCrossed (natCells (used + (spare + 1)))
              [cell00, cell00, leftGuard]) =
        pushCrossed
          ([cell00, cell00] ++ natCells (used + (spare + 1)) ++
            between ++ natCells 0)
          [leftGuard] := by
    unfold cursorScan
    repeat rw [pushCrossed_append]
    rfl
  unfold inputReferenceFinishSteps
  unfold inputReferenceConfiguration
  unfold inputReferenceSuccessConfiguration
  unfold guardedConfig
  rw [← endpointEq]
  simpa [guardedPrefix, checkPrefix, checkSuffix, cursorScan,
    inputReferenceConfiguration, guardedConfig, natCells,
    countCells_succ_remaining, countCells_eq_borrowed_append,
    pushCrossed_append, List.append_assoc] using all

/-- Exact recursive schedule for an input reference known to be in range. -/
def inputReferenceInRangeSteps
    (used remaining : Nat) (between : List WorkSymbol) :
    Nat → Nat
  | 0 =>
      match remaining with
      | 0 => 0
      | spare + 1 => inputReferenceFinishSteps used spare between
  | index + 1 =>
      match remaining with
      | 0 => 0
      | rest + 1 =>
          inputReferenceConsumeUnitSteps used rest between +
            inputReferenceInRangeSteps (used + 1) rest
              (between ++ [cell00, cell01]) index

/-- Every strictly in-range input reference returns to its source
continuation with the entire declared input count and unary index restored
bit-for-bit. -/
theorem inputReferenceInRange_exact
    (continuation : SourceContinuation)
    (used remaining index : Nat)
    (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (inRange : index < remaining) :
    workRunExact? machine
        (inputReferenceInRangeSteps used remaining between index)
        (inputReferenceConfiguration continuation used remaining
          between index suffix) =
      some
        (inputReferenceSuccessConfiguration continuation
          (used + remaining) between index suffix) := by
  induction index generalizing used remaining between with
  | zero =>
      cases remaining with
      | zero =>
          omega
      | succ spare =>
          simpa [inputReferenceInRangeSteps] using
            inputReferenceFinishInRange_exact continuation used spare
              between suffix betweenOrdinary
  | succ index ih =>
      cases remaining with
      | zero =>
          omega
      | succ rest =>
          have tailInRange : index < rest := by
            omega
          have nextBetweenOrdinary :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  ordinaryCell symbol := by
            apply ordinary_append
            · exact betweenOrdinary
            · intro symbol member
              simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                exact cell00_ordinary
              · subst symbol
                exact cell01_ordinary
              · contradiction
          have first :=
            inputReferenceConsumeUnit_exact continuation used rest index
              between suffix betweenOrdinary
          have tail :=
            ih (used + 1) rest (between ++ [cell00, cell01])
              nextBetweenOrdinary tailInRange
          have tailCanonical :
              workRunExact? machine
                  (inputReferenceInRangeSteps (used + 1) rest
                    (between ++ [cell00, cell01]) index)
                  (inputReferenceConfiguration continuation
                    (used + 1) rest
                    (between ++ [cell00, cell01]) index suffix) =
                some
                  (inputReferenceSuccessConfiguration continuation
                    (used + (rest + 1)) between (index + 1) suffix) := by
            have totalEq :
                (used + 1) + rest = used + (rest + 1) := by
              omega
            rw [totalEq] at tail
            simpa [inputReferenceSuccessConfiguration, natCells,
              List.append_assoc] using tail
          have all :=
            exactRun_add
              (inputReferenceConsumeUnitSteps used rest between)
              (inputReferenceInRangeSteps (used + 1) rest
                (between ++ [cell00, cell01]) index)
              _ _ _ first tailCanonical
          simpa [inputReferenceInRangeSteps] using all

/-- Canonical cleanup entry produced by a failed strict input-bound check. -/
def inputReferenceCleanupConfiguration
    (failurePrefix failureSuffix : List WorkSymbol) :
    WorkConfiguration :=
  guardedConfig State.cleanupSeekGuard failurePrefix
    (cell10 :: failureSuffix)

private theorem inputFailureLeft_eq (used : Nat) :
    cell00 ::
        pushCrossed (borrowedCountCells used)
          [cell00, cell00, leftGuard] =
      pushCrossed
        ([cell00, cell00] ++ borrowedCountCells used ++ [cell00])
        [leftGuard] := by
  repeat rw [pushCrossed_append]
  rfl

def inputReferenceExhaustedSteps
    (used : Nat) (between : List WorkSymbol) : Nat :=
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used 0 ++ between
  2 + (guardedPrefix ++ [cell00]).length + 1 +
    2 + 2 * (used + 1)

/-- A further unary index unit after all declared input units have been
borrowed fails exactly on the input-count terminator, preserving an arbitrary
unary-token tail for malformed-input traces. -/
theorem inputReferenceConsumeExhaustedTail_exact
    (continuation : SourceContinuation)
    (used : Nat) (between indexTail : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    let failurePrefix :=
      [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
    let failureSuffix :=
      between ++ [cell00, cursorMark] ++ indexTail
    workRunExact? machine
        (inputReferenceExhaustedSteps used between)
        (guardedConfig (State.indexFirst .input continuation)
          ([cell00, cell00] ++ countCells used 0 ++ between)
          (cell00 :: cell01 :: indexTail)) =
      some
        (inputReferenceCleanupConfiguration
          failurePrefix failureSuffix) := by
  dsimp only
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used 0 ++ between
  let indexSuffix := indexTail
  let failurePrefix :=
    [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
  let failureSuffix :=
    between ++ [cell00, cursorMark] ++ indexSuffix
  have first :=
    referenceIndexFirst_exact .input continuation guardedPrefix
      cell01 indexSuffix
  have launch :=
    referenceIndexUnitLaunch_exact .input continuation guardedPrefix
      indexSuffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have prefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol :=
    inputReferencePrefix_ordinary used 0 between betweenOrdinary
  have scanPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix ++ [cell00] →
        ordinaryCell symbol :=
    ordinary_append prefixOrdinary
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact cell00_ordinary
        · contradiction)
  have backward :=
    referenceConsumeSeekGuard_scan_exact .input continuation
      (guardedPrefix ++ [cell00]) (cursorMark :: indexSuffix)
      scanPrefixOrdinary
  have guard :=
    referenceConsumeGuard_exact .input continuation
      ((guardedPrefix ++ [cell00]) ++ cursorMark :: indexSuffix)
  have version :=
    inputConsumeVersion_exact continuation [leftGuard]
      (countCells used 0 ++ between ++ [cell00, cursorMark] ++
        indexSuffix)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord
            (consumeAfterGuardState .input continuation)
            [leftGuard]
            ((guardedPrefix ++ [cell00]) ++
              cursorMark :: indexSuffix)) =
        some
          (configAtWord
            (State.consumeInputFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used 0 ++ between ++
              [cell00, cursorMark] ++ indexSuffix)) := by
    simpa [consumeAfterGuardState, guardedPrefix,
      List.append_assoc] using version
  have exhausted :=
    inputConsumeCountExhausted_exact continuation used
      [cell00, cell00, leftGuard]
      (between ++ [cell00, cursorMark] ++ indexSuffix)
  have exhaustedCanonical :
      workRunExact? machine (2 * (used + 1))
          (configAtWord
            (State.consumeInputFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used 0 ++ between ++
              [cell00, cursorMark] ++ indexSuffix)) =
        some
          (inputReferenceCleanupConfiguration
            failurePrefix failureSuffix) := by
    unfold inputReferenceCleanupConfiguration guardedConfig
    unfold failurePrefix failureSuffix
    rw [← inputFailureLeft_eq]
    simpa [countCells_eq_borrowed_append, natCells,
      List.append_assoc, pushCrossed_append] using exhausted
  have throughBackward :=
    exactRun_add 2 (guardedPrefix ++ [cell00]).length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add
      (2 + (guardedPrefix ++ [cell00]).length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      ((2 + (guardedPrefix ++ [cell00]).length) + 1) 2
      _ _ _ throughGuard versionCanonical
  have all :=
    exactRun_add
      (((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2)
      (2 * (used + 1))
      _ _ _ throughVersion exhaustedCanonical
  unfold inputReferenceExhaustedSteps
  simpa [guardedPrefix, indexSuffix, failurePrefix, failureSuffix,
    guardedConfig, List.append_assoc] using all

/-- Canonical specialization of the exhausted input-reference unit trace. -/
theorem inputReferenceConsumeExhausted_exact
    (continuation : SourceContinuation)
    (used index : Nat) (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    let failurePrefix :=
      [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
    let failureSuffix :=
      between ++ [cell00, cursorMark] ++ natCells index ++ suffix
    workRunExact? machine
        (inputReferenceExhaustedSteps used between)
        (inputReferenceConfiguration continuation used 0
          between (index + 1) suffix) =
      some
        (inputReferenceCleanupConfiguration
          failurePrefix failureSuffix) := by
  simpa [inputReferenceConfiguration, natCells, List.append_assoc] using
    inputReferenceConsumeExhaustedTail_exact continuation used between
      (natCells index ++ suffix) betweenOrdinary

/-- An index terminator after borrowing every declared input unit fails the
strict `< inputCount` witness check on that same count terminator. -/
theorem inputReferenceFinishExhausted_exact
    (continuation : SourceContinuation)
    (used : Nat) (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    let failurePrefix :=
      [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
    let failureSuffix :=
      between ++ [cell00, cursorMark] ++ suffix
    workRunExact? machine
        (inputReferenceExhaustedSteps used between)
        (inputReferenceConfiguration continuation used 0
          between 0 suffix) =
      some
        (inputReferenceCleanupConfiguration
          failurePrefix failureSuffix) := by
  dsimp only
  let guardedPrefix :=
    [cell00, cell00] ++ countCells used 0 ++ between
  let failurePrefix :=
    [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
  let failureSuffix :=
    between ++ [cell00, cursorMark] ++ suffix
  have first :=
    referenceIndexFirst_exact .input continuation guardedPrefix
      cell10 suffix
  have launch :=
    referenceIndexFinishLaunch_exact .input continuation guardedPrefix
      suffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have prefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol :=
    inputReferencePrefix_ordinary used 0 between betweenOrdinary
  have scanPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix ++ [cell00] →
        ordinaryCell symbol :=
    ordinary_append prefixOrdinary
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact cell00_ordinary
        · contradiction)
  have backward :=
    referenceFinishSeekGuard_scan_exact .input continuation
      (guardedPrefix ++ [cell00]) (cursorMark :: suffix)
      scanPrefixOrdinary
  have guard :=
    referenceFinishGuard_exact .input continuation
      ((guardedPrefix ++ [cell00]) ++ cursorMark :: suffix)
  have version :=
    inputFinishVersion_exact continuation [leftGuard]
      (countCells used 0 ++ between ++ [cell00, cursorMark] ++ suffix)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord
            (finishAfterGuardState .input continuation)
            [leftGuard]
            ((guardedPrefix ++ [cell00]) ++ cursorMark :: suffix)) =
        some
          (configAtWord
            (State.finishInputCheckFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used 0 ++ between ++
              [cell00, cursorMark] ++ suffix)) := by
    simpa [finishAfterGuardState, guardedPrefix,
      List.append_assoc] using version
  have exhausted :=
    inputFinishCheckExhaustedRun_exact continuation used
      [cell00, cell00, leftGuard]
      (between ++ [cell00, cursorMark] ++ suffix)
  have exhaustedCanonical :
      workRunExact? machine (2 * (used + 1))
          (configAtWord
            (State.finishInputCheckFirst .input continuation)
            [cell00, cell00, leftGuard]
            (countCells used 0 ++ between ++
              [cell00, cursorMark] ++ suffix)) =
        some
          (inputReferenceCleanupConfiguration
            failurePrefix failureSuffix) := by
    unfold inputReferenceCleanupConfiguration guardedConfig
    unfold failurePrefix failureSuffix
    rw [← inputFailureLeft_eq]
    simpa [countCells_eq_borrowed_append, natCells,
      List.append_assoc, pushCrossed_append] using exhausted
  have throughBackward :=
    exactRun_add 2 (guardedPrefix ++ [cell00]).length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add
      (2 + (guardedPrefix ++ [cell00]).length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      ((2 + (guardedPrefix ++ [cell00]).length) + 1) 2
      _ _ _ throughGuard versionCanonical
  have all :=
    exactRun_add
      (((2 + (guardedPrefix ++ [cell00]).length) + 1) + 2)
      (2 * (used + 1))
      _ _ _ throughVersion exhaustedCanonical
  unfold inputReferenceExhaustedSteps
  unfold inputReferenceConfiguration
  simpa [guardedPrefix, failurePrefix, failureSuffix,
    guardedConfig, natCells, List.append_assoc] using all

/-- Exact recursive schedule for an input reference known to be out of
range.  The zero/zero branch fails the strict witness check; a positive index
over a zero remainder fails while trying to borrow another count unit. -/
def inputReferenceOutOfRangeSteps
    (used remaining : Nat) (between : List WorkSymbol) :
    Nat → Nat
  | 0 =>
      match remaining with
      | 0 => inputReferenceExhaustedSteps used between
      | _ + 1 => 0
  | index + 1 =>
      match remaining with
      | 0 => inputReferenceExhaustedSteps used between
      | rest + 1 =>
          inputReferenceConsumeUnitSteps used rest between +
            inputReferenceOutOfRangeSteps (used + 1) rest
              (between ++ [cell00, cell01]) index

/-- Every out-of-range input reference reaches the literal cleanup state at
the declared-input terminator.  The existential words expose the exact
guarded cleanup configuration to the total-trace module. -/
theorem inputReferenceOutOfRange_cleanupEntry
    (continuation : SourceContinuation)
    (used remaining index : Nat)
    (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (outOfRange : remaining ≤ index) :
    ∃ failurePrefix failureSuffix,
      workRunExact? machine
          (inputReferenceOutOfRangeSteps used remaining between index)
          (inputReferenceConfiguration continuation used remaining
            between index suffix) =
        some
          (inputReferenceCleanupConfiguration
            failurePrefix failureSuffix) := by
  induction index generalizing used remaining between with
  | zero =>
      have remainingEq : remaining = 0 := by
        omega
      subst remaining
      let failurePrefix :=
        [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
      let failureSuffix :=
        between ++ [cell00, cursorMark] ++ suffix
      refine ⟨failurePrefix, failureSuffix, ?_⟩
      have base :=
        inputReferenceFinishExhausted_exact continuation used
          between suffix betweenOrdinary
      simpa [inputReferenceOutOfRangeSteps,
        failurePrefix, failureSuffix] using base
  | succ index ih =>
      cases remaining with
      | zero =>
          let failurePrefix :=
            [cell00, cell00] ++ borrowedCountCells used ++ [cell00]
          let failureSuffix :=
            between ++ [cell00, cursorMark] ++ natCells index ++ suffix
          refine ⟨failurePrefix, failureSuffix, ?_⟩
          have base :=
            inputReferenceConsumeExhausted_exact continuation used index
              between suffix betweenOrdinary
          simpa [inputReferenceOutOfRangeSteps,
            failurePrefix, failureSuffix] using base
      | succ rest =>
          have tailOutOfRange : rest ≤ index := by
            omega
          have nextBetweenOrdinary :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  ordinaryCell symbol := by
            apply ordinary_append
            · exact betweenOrdinary
            · intro symbol member
              simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                exact cell00_ordinary
              · subst symbol
                exact cell01_ordinary
              · contradiction
          have first :=
            inputReferenceConsumeUnit_exact continuation used rest index
              between suffix betweenOrdinary
          rcases ih (used + 1) rest
              (between ++ [cell00, cell01])
              nextBetweenOrdinary tailOutOfRange with
            ⟨failurePrefix, failureSuffix, tail⟩
          refine ⟨failurePrefix, failureSuffix, ?_⟩
          have all :=
            exactRun_add
              (inputReferenceConsumeUnitSteps used rest between)
              (inputReferenceOutOfRangeSteps (used + 1) rest
                (between ++ [cell00, cell01]) index)
              _ _ _ first tail
          simpa [inputReferenceOutOfRangeSteps] using all

def ordinaryNonGateAnchor (symbol : WorkSymbol) : Prop :=
  ordinaryCell symbol ∧ symbol ≠ gateMark

set_option maxRecDepth 100000 in
private theorem gateConsumeAnchorScan_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (allowed : ordinaryNonGateAnchor head) :
    workStep? machine
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          (head :: left) suffix) := by
  rcases allowed.1 with h | h | h | h | h | h <;>
    subst head
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · exact False.elim (allowed.2 rfl)
  · cases continuation <;> rfl
  · cases continuation <;> rfl

theorem gateConsumeAnchorScan_exact
    (continuation : SourceContinuation)
    (left scan suffix : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ scan → ordinaryNonGateAnchor symbol) :
    workRunExact? machine scan.length
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          left (scan ++ suffix)) =
      some
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          (pushCrossed scan left) suffix) := by
  exact scanRight_exact
    (State.consumeGateAnchor .priorGate continuation)
    ordinaryNonGateAnchor
    (gateConsumeAnchorScan_step continuation)
    scan suffix left allowed

set_option maxRecDepth 100000 in
private theorem gateConsumeAnchor_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          left (gateMark :: suffix)) =
      some
        (configAtWord
          (State.consumeSeekCursor .priorGate continuation)
          (countMark :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateConsumeSeekCursor_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord
          (State.consumeSeekCursor .priorGate continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.consumeSeekCursor .priorGate continuation)
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateConsumeCursor_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.consumeSeekCursor .priorGate continuation)
          left (cursorMark :: rest)) =
      some
        (configAtWord
          (State.indexFirst .priorGate continuation)
          (cell01 :: left) rest) := by
  cases continuation <;> rfl

def gateReferenceConsumeUnitSteps
    (header : List WorkSymbol)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol) : Nat :=
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++
      markedGateListCells (gate :: available) ++ between
  let anchorScan :=
    header ++ borrowedGateListCells borrowed ++
      sourceCells gate.left ++ sourceCells gate.right
  let cursorScan :=
    cell11 :: markedGateListCells available ++ between ++ [cell00]
  2 + (guardedPrefix ++ [cell00]).length + 1 +
    anchorScan.length + 1 + cursorScan.length + 1

/-- One unary prior-gate index unit borrows the next completed gate anchor.
The arbitrary index tail is preserved exactly for reuse by malformed-token
failure traces. -/
theorem gateReferenceConsumeUnitTail_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol)
    (indexTail : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    workRunExact? machine
        (gateReferenceConsumeUnitSteps
          header borrowed gate available between)
        (guardedConfig (State.indexFirst .priorGate continuation)
          (header ++ borrowedGateListCells borrowed ++
            markedGateListCells (gate :: available) ++ between)
          (cell00 :: cell01 :: indexTail)) =
      some
        (guardedConfig (State.indexFirst .priorGate continuation)
          (header ++ borrowedGateListCells (borrowed ++ [gate]) ++
            markedGateListCells available ++
            (between ++ [cell00, cell01]))
          indexTail) := by
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++
      markedGateListCells (gate :: available) ++ between
  let anchorScan :=
    header ++ borrowedGateListCells borrowed ++
      sourceCells gate.left ++ sourceCells gate.right
  let cursorScan :=
    cell11 :: markedGateListCells available ++ between ++ [cell00]
  let indexSuffix := indexTail
  have first :=
    referenceIndexFirst_exact .priorGate continuation guardedPrefix
      cell01 indexSuffix
  have launch :=
    referenceIndexUnitLaunch_exact .priorGate continuation guardedPrefix
      indexSuffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have guardedPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol := by
    unfold guardedPrefix
    apply ordinary_append
    · apply ordinary_append
      · apply ordinary_append
        · exact headerOrdinary
        · exact borrowedGateListCells_ordinary borrowed
      · exact markedGateListCells_ordinary (gate :: available)
    · exact betweenOrdinary
  have scanPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix ++ [cell00] →
        ordinaryCell symbol :=
    ordinary_append guardedPrefixOrdinary
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact cell00_ordinary
        · contradiction)
  have backward :=
    referenceConsumeSeekGuard_scan_exact .priorGate continuation
      (guardedPrefix ++ [cell00]) (cursorMark :: indexSuffix)
      scanPrefixOrdinary
  have guard :=
    referenceConsumeGuard_exact .priorGate continuation
      ((guardedPrefix ++ [cell00]) ++ cursorMark :: indexSuffix)
  have anchorScanAllowed :
      ∀ symbol, symbol ∈ anchorScan →
        ordinaryNonGateAnchor symbol := by
    intro symbol member
    unfold anchorScan at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact
            ⟨headerOrdinary symbol member,
              headerNoGateMark symbol member⟩
        · have ordinary :=
            borrowedGateListCells_ordinary borrowed symbol member
          exact
            ⟨ordinary,
              borrowedGateListCells_no_gateMark borrowed symbol member⟩
      · have ordinary := sourceCells_ordinary gate.left symbol member
        exact
          ⟨ordinary, sourceCells_no_gateMark gate.left symbol member⟩
    · have ordinary := sourceCells_ordinary gate.right symbol member
      exact
        ⟨ordinary, sourceCells_no_gateMark gate.right symbol member⟩
  have anchor :=
    gateConsumeAnchorScan_exact continuation [leftGuard]
      anchorScan
      (gateMark :: cursorScan ++ cursorMark :: indexSuffix)
      anchorScanAllowed
  have anchorSelect :=
    gateConsumeAnchor_exact continuation
      (pushCrossed anchorScan [leftGuard])
      (cursorScan ++ cursorMark :: indexSuffix)
  have cursorScanOrdinary :
      ∀ symbol, symbol ∈ cursorScan → ordinaryCell symbol := by
    unfold cursorScan
    intro symbol member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · simp only [List.mem_cons] at member
        rcases member with h | member
        · subst symbol
          exact cell11_ordinary
        · exact markedGateListCells_ordinary available symbol member
      · exact betweenOrdinary symbol member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have cursorScanRun :=
    scanRight_exact
      (State.consumeSeekCursor .priorGate continuation)
      ordinaryCell
      (gateConsumeSeekCursor_step continuation)
      cursorScan (cursorMark :: indexSuffix)
      (countMark :: pushCrossed anchorScan [leftGuard])
      cursorScanOrdinary
  have cursor :=
    gateConsumeCursor_exact continuation
      (pushCrossed cursorScan
        (countMark :: pushCrossed anchorScan [leftGuard]))
      indexSuffix
  have cursorCanonical :
      workRunExact? machine 1
          (configAtWord
            (State.consumeSeekCursor .priorGate continuation)
            (pushCrossed cursorScan
              (countMark :: pushCrossed anchorScan [leftGuard]))
            (cursorMark :: indexSuffix)) =
        some
          (configAtWord
            (State.indexFirst .priorGate continuation)
            (cell01 ::
              pushCrossed cursorScan
                (countMark :: pushCrossed anchorScan [leftGuard]))
            indexSuffix) := by
    exact cursor
  have anchorCanonical :
      workRunExact? machine anchorScan.length
          (configAtWord
            (consumeAfterGuardState .priorGate continuation)
            [leftGuard]
            ((guardedPrefix ++ [cell00]) ++
              cursorMark :: indexSuffix)) =
        some
          (configAtWord
            (State.consumeGateAnchor .priorGate continuation)
            (pushCrossed anchorScan [leftGuard])
            (gateMark :: cursorScan ++ cursorMark :: indexSuffix)) := by
    simpa [consumeAfterGuardState, guardedPrefix, anchorScan,
      cursorScan, markedGateListCells, markedGateCells,
      List.append_assoc] using anchor
  have throughBackward :=
    exactRun_add 2 (guardedPrefix ++ [cell00]).length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add
      (2 + (guardedPrefix ++ [cell00]).length) 1
      _ _ _ throughBackward guard
  have throughAnchor :=
    exactRun_add
      ((2 + (guardedPrefix ++ [cell00]).length) + 1)
      anchorScan.length
      _ _ _ throughGuard anchorCanonical
  have throughSelect :=
    exactRun_add
      (((2 + (guardedPrefix ++ [cell00]).length) + 1) +
        anchorScan.length)
      1 _ _ _ throughAnchor anchorSelect
  have throughCursorScan :=
    exactRun_add
      ((((2 + (guardedPrefix ++ [cell00]).length) + 1) +
        anchorScan.length) + 1)
      cursorScan.length
      _ _ _ throughSelect cursorScanRun
  have all :=
    exactRun_add
      (((((2 + (guardedPrefix ++ [cell00]).length) + 1) +
        anchorScan.length) + 1) + cursorScan.length)
      1 _ _ _ throughCursorScan cursorCanonical
  have endpointEq :
      cell01 ::
          pushCrossed cursorScan
            (countMark :: pushCrossed anchorScan [leftGuard]) =
        pushCrossed
          (header ++ borrowedGateListCells (borrowed ++ [gate]) ++
            markedGateListCells available ++
            (between ++ [cell00, cell01]))
          [leftGuard] := by
    unfold anchorScan cursorScan
    rw [borrowedGateListCells_append]
    unfold borrowedGateListCells borrowedGateCells
    repeat rw [pushCrossed_append]
    rfl
  unfold gateReferenceConsumeUnitSteps
  unfold guardedConfig
  rw [← endpointEq]
  simpa [guardedPrefix, anchorScan, cursorScan, indexSuffix,
    guardedConfig, List.append_assoc] using all

/-- One in-range canonical unary prior-gate index unit borrows the next
completed gate anchor, restores the unary-unit cursor, and advances to the
next index unit. -/
theorem gateReferenceConsumeUnit_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol) :
    workRunExact? machine
        (gateReferenceConsumeUnitSteps
          header borrowed gate available between)
        (gateReferenceConfiguration continuation header borrowed
          (gate :: available) between (index + 1) suffix) =
      some
        (gateReferenceConfiguration continuation header
          (borrowed ++ [gate]) available
          (between ++ [cell00, cell01]) index suffix) := by
  simpa [gateReferenceConfiguration, natCells, List.append_assoc] using
    gateReferenceConsumeUnitTail_exact continuation header borrowed gate
      available between (natCells index ++ suffix)
      headerOrdinary headerNoGateMark betweenOrdinary

set_option maxRecDepth 100000 in
private theorem gateFinishCheckAnchor_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (allowed : ordinaryNonGateAnchor head) :
    workStep? machine
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          (head :: left) suffix) := by
  rcases allowed.1 with h | h | h | h | h | h <;>
    subst head
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · exact False.elim (allowed.2 rfl)
  · cases continuation <;> rfl
  · cases continuation <;> rfl

private theorem gateFinishCheckAnchorScan_exact
    (continuation : SourceContinuation)
    (left scan suffix : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ scan → ordinaryNonGateAnchor symbol) :
    workRunExact? machine scan.length
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          left (scan ++ suffix)) =
      some
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          (pushCrossed scan left) suffix) := by
  exact scanRight_exact
    (State.finishGateCheckAnchor .priorGate continuation)
    ordinaryNonGateAnchor
    (gateFinishCheckAnchor_step continuation)
    scan suffix left allowed

set_option maxRecDepth 100000 in
private theorem gateFinishAnchor_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          left (gateMark :: suffix)) =
      some
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          left (gateMark :: suffix)) := by
  cases continuation <;> cases left <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishReturnGuard_step
    (continuation : SourceContinuation)
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          (head :: leftTail) right) =
      some
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> cases continuation <;> rfl

private theorem gateFinishReturnGuard_scan_exact
    (continuation : SourceContinuation)
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact
      (State.finishGateReturnGuard .priorGate continuation)
      ordinaryCell
      (gateFinishReturnGuard_step continuation)
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem gateFinishReturnGuard_exact
    (continuation : SourceContinuation)
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord
          (State.finishGateReturnGuard .priorGate continuation)
          [leftGuard] suffix) =
      some
        (configAtWord
          (State.finishGateVersionFirst .priorGate continuation)
          [leftGuard] suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishVersion_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateVersionFirst .priorGate continuation)
          left (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord
          (State.finishGateInputFirst .priorGate continuation)
          (cell00 :: cell00 :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishInputUnit_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateInputFirst .priorGate continuation)
          left (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.finishGateInputFirst .priorGate continuation)
          (cell01 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishInputEnd_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateInputFirst .priorGate continuation)
          left (cell00 :: cell10 :: rest)) =
      some
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          (cell10 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

private theorem gateFinishInput_exact
    (continuation : SourceContinuation)
    (inputs : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (inputs + 1))
        (configAtWord
          (State.finishGateInputFirst .priorGate continuation)
          left (natCells inputs ++ suffix)) =
      some
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          (pushCrossed (natCells inputs) left) suffix) := by
  induction inputs generalizing left with
  | zero =>
      exact gateFinishInputEnd_exact continuation left suffix
  | succ inputs ih =>
      have first :=
        gateFinishInputUnit_exact continuation left
          (natCells inputs ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (inputs + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (inputs + 1) =
            2 * ((inputs + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, pushCrossed] using all

set_option maxRecDepth 100000 in
private theorem gateFinishCountBorrowed_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          left (cell00 :: countMark :: rest)) =
      some
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          (countMark :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishCountUnit_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          left (cell00 :: cell01 :: rest)) =
      some
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          (cell01 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishCountEnd_exact
    (continuation : SourceContinuation)
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          left (cell00 :: cell10 :: rest)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (cell10 :: cell00 :: left) rest) := by
  cases continuation <;> rfl

private theorem gateFinishCountNat_exact
    (continuation : SourceContinuation)
    (remaining : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (remaining + 1))
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          left (natCells remaining ++ suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (pushCrossed (natCells remaining) left) suffix) := by
  induction remaining generalizing left with
  | zero =>
      exact gateFinishCountEnd_exact continuation left suffix
  | succ remaining ih =>
      have first :=
        gateFinishCountUnit_exact continuation left
          (natCells remaining ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (remaining + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (remaining + 1) =
            2 * ((remaining + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, pushCrossed] using all

private theorem gateFinishCount_exact
    (continuation : SourceContinuation)
    (used remaining : Nat)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (used + remaining + 1))
        (configAtWord
          (State.finishGateCountFirst .priorGate continuation)
          left (countCells used remaining ++ suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (pushCrossed (countCells used remaining) left) suffix) := by
  induction used generalizing left with
  | zero =>
      simpa [countCells] using
        gateFinishCountNat_exact continuation remaining left suffix
  | succ used ih =>
      have first :=
        gateFinishCountBorrowed_exact continuation left
          (countCells used remaining ++ suffix)
      have tail := ih (countMark :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (used + remaining + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (used + remaining + 1) =
            2 * ((used + 1) + remaining + 1) := by
        omega
      rw [costEq] at all
      simpa [countCells, pushCrossed] using all

def ordinaryNonCountMarker (symbol : WorkSymbol) : Prop :=
  ordinaryCell symbol ∧ symbol ≠ countMark

set_option maxRecDepth 100000 in
private theorem gateFinishRestoreScan_step
    (continuation : SourceContinuation)
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (allowed : ordinaryNonCountMarker head) :
    workStep? machine
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (head :: suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (head :: left) suffix) := by
  rcases allowed.1 with h | h | h | h | h | h <;>
    subst head
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · exact False.elim (allowed.2 rfl)
  · cases continuation <;> rfl
  · cases continuation <;> rfl
  · cases continuation <;> rfl

private theorem gateFinishRestoreScan_exact
    (continuation : SourceContinuation)
    (left scan suffix : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ scan → ordinaryNonCountMarker symbol) :
    workRunExact? machine scan.length
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (scan ++ suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (pushCrossed scan left) suffix) := by
  exact scanRight_exact
    (State.finishGateRestore .priorGate continuation)
    ordinaryNonCountMarker
    (gateFinishRestoreScan_step continuation)
    scan suffix left allowed

set_option maxRecDepth 100000 in
private theorem gateFinishRestoreMarker_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (countMark :: suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (gateMark :: left) suffix) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishRestoreCursor_exact
    (continuation : SourceContinuation)
    (left suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (cursorMark :: suffix)) =
      some
        (configAtWord (sourceDoneState continuation)
          (cell10 :: left) suffix) := by
  cases continuation <;> rfl

private theorem gateFinishRestoreGate_exact
    (continuation : SourceContinuation)
    (gate : RawGate)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (borrowedGateCells gate).length
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (borrowedGateCells gate ++ suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (pushCrossed (markedGateCells gate) left) suffix) := by
  let sourceScan := sourceCells gate.left ++ sourceCells gate.right
  have sourceAllowed :
      ∀ symbol, symbol ∈ sourceScan →
        ordinaryNonCountMarker symbol := by
    intro symbol member
    unfold sourceScan at member
    rcases List.mem_append.mp member with member | member
    · exact
        ⟨sourceCells_ordinary gate.left symbol member,
          sourceCells_no_countMark gate.left symbol member⟩
    · exact
        ⟨sourceCells_ordinary gate.right symbol member,
          sourceCells_no_countMark gate.right symbol member⟩
  have source :=
    gateFinishRestoreScan_exact continuation left sourceScan
      (countMark :: cell11 :: suffix) sourceAllowed
  have marker :=
    gateFinishRestoreMarker_exact continuation
      (pushCrossed sourceScan left) (cell11 :: suffix)
  have ending :=
    gateFinishRestoreScan_exact continuation
      (gateMark :: pushCrossed sourceScan left)
      [cell11] suffix
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | impossible
        · subst symbol
          exact ⟨cell11_ordinary, by decide⟩
        · contradiction)
  have throughMarker :=
    exactRun_add sourceScan.length 1
      _ _ _ source marker
  have all :=
    exactRun_add (sourceScan.length + 1) 1
      _ _ _ throughMarker ending
  have costEq :
      sourceScan.length + 1 + 1 =
        (borrowedGateCells gate).length := by
    unfold sourceScan borrowedGateCells
    simp only [List.length_append, List.length_cons, List.length_nil]
  rw [costEq] at all
  simpa [sourceScan, borrowedGateCells, markedGateCells,
    pushCrossed, pushCrossed_append, List.append_assoc] using all

private theorem gateFinishRestoreGateList_exact
    (continuation : SourceContinuation)
    (gates : List RawGate)
    (left suffix : List WorkSymbol) :
    workRunExact? machine (borrowedGateListCells gates).length
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          left (borrowedGateListCells gates ++ suffix)) =
      some
        (configAtWord
          (State.finishGateRestore .priorGate continuation)
          (pushCrossed (markedGateListCells gates) left)
          suffix) := by
  induction gates generalizing left with
  | nil =>
      rfl
  | cons gate rest ih =>
      have first :=
        gateFinishRestoreGate_exact continuation gate left
          (borrowedGateListCells rest ++ suffix)
      have tail :=
        ih (pushCrossed (markedGateCells gate) left)
      have all :=
        exactRun_add
          (borrowedGateCells gate).length
          (borrowedGateListCells rest).length
          _ _ _ first tail
      simpa [borrowedGateListCells, markedGateListCells,
        pushCrossed_append, List.append_assoc] using all

/-- Exact cost of the successful strict prior-gate witness check and complete
restoration at the unary-index terminator. -/
def gateReferenceFinishSteps
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol) : Nat :=
  let header :=
    gateReferenceHeader inputs gateCountUsed gateCountRemaining
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++
      markedGateListCells (gate :: available) ++ between
  let sweep := guardedPrefix ++ [cell00]
  let checkScan :=
    header ++ borrowedGateListCells borrowed ++
      sourceCells gate.left ++ sourceCells gate.right
  let restoreScan :=
    markedGateListCells (gate :: available) ++ between ++ [cell00]
  2 + sweep.length + 1 +
    checkScan.length + 1 + checkScan.length + 1 +
    2 + 2 * (inputs + 1) +
    2 * (gateCountUsed + gateCountRemaining + 1) +
    (borrowedGateListCells borrowed).length +
    restoreScan.length + 1

/-- Finishing an in-range prior-gate reference witnesses one unborrowed gate
anchor, restores every temporarily borrowed gate anchor and the unary
terminator, and enters the source continuation. -/
theorem gateReferenceFinishInRange_exact
    (continuation : SourceContinuation)
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoCountMark :
      ∀ symbol, symbol ∈ between → symbol ≠ countMark) :
    let header :=
      gateReferenceHeader inputs gateCountUsed gateCountRemaining
    workRunExact? machine
        (gateReferenceFinishSteps inputs gateCountUsed
          gateCountRemaining borrowed gate available between)
        (gateReferenceConfiguration continuation header borrowed
          (gate :: available) between 0 suffix) =
      some
        (gateReferenceSuccessConfiguration continuation header
          (borrowed ++ gate :: available) between 0 suffix) := by
  dsimp only
  let header :=
    gateReferenceHeader inputs gateCountUsed gateCountRemaining
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++
      markedGateListCells (gate :: available) ++ between
  let sweep := guardedPrefix ++ [cell00]
  let checkScan :=
    header ++ borrowedGateListCells borrowed ++
      sourceCells gate.left ++ sourceCells gate.right
  let referenceRest :=
    borrowedGateListCells borrowed ++
      markedGateListCells (gate :: available) ++ between ++
      [cell00, cursorMark] ++ suffix
  let afterAnchor :=
    cell11 :: markedGateListCells available ++ between ++
      [cell00, cursorMark] ++ suffix
  let restoreScan :=
    markedGateListCells (gate :: available) ++ between ++ [cell00]
  have first :=
    referenceIndexFirst_exact .priorGate continuation guardedPrefix
      cell10 suffix
  have launch :=
    referenceIndexFinishLaunch_exact .priorGate continuation
      guardedPrefix suffix
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have guardedPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol := by
    unfold guardedPrefix
    apply ordinary_append
    · apply ordinary_append
      · apply ordinary_append
        · exact
            gateReferenceHeader_ordinary
              inputs gateCountUsed gateCountRemaining
        · exact borrowedGateListCells_ordinary borrowed
      · exact markedGateListCells_ordinary (gate :: available)
    · exact betweenOrdinary
  have sweepOrdinary :
      ∀ symbol, symbol ∈ sweep → ordinaryCell symbol := by
    unfold sweep
    apply ordinary_append
    · exact guardedPrefixOrdinary
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have backward :=
    referenceFinishSeekGuard_scan_exact .priorGate continuation
      sweep (cursorMark :: suffix) sweepOrdinary
  have guard :=
    referenceFinishGuard_exact .priorGate continuation
      (sweep ++ cursorMark :: suffix)
  have checkAllowed :
      ∀ symbol, symbol ∈ checkScan →
        ordinaryNonGateAnchor symbol := by
    intro symbol member
    unfold checkScan at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact
            ⟨gateReferenceHeader_ordinary
                inputs gateCountUsed gateCountRemaining symbol member,
              gateReferenceHeader_no_gateMark
                inputs gateCountUsed gateCountRemaining symbol member⟩
        · exact
            ⟨borrowedGateListCells_ordinary borrowed symbol member,
              borrowedGateListCells_no_gateMark borrowed symbol member⟩
      · exact
          ⟨sourceCells_ordinary gate.left symbol member,
            sourceCells_no_gateMark gate.left symbol member⟩
    · exact
        ⟨sourceCells_ordinary gate.right symbol member,
          sourceCells_no_gateMark gate.right symbol member⟩
  have check :=
    gateFinishCheckAnchorScan_exact continuation [leftGuard]
      checkScan (gateMark :: afterAnchor) checkAllowed
  have checkCanonical :
      workRunExact? machine checkScan.length
          (configAtWord
            (finishAfterGuardState .priorGate continuation)
            [leftGuard] (sweep ++ cursorMark :: suffix)) =
        some
          (configAtWord
            (State.finishGateCheckAnchor .priorGate continuation)
            (pushCrossed checkScan [leftGuard])
            (gateMark :: afterAnchor)) := by
    simpa [finishAfterGuardState, sweep, guardedPrefix, checkScan,
      afterAnchor, markedGateListCells, markedGateCells,
      List.append_assoc] using check
  have anchor :=
    gateFinishAnchor_exact continuation
      (pushCrossed checkScan [leftGuard]) afterAnchor
  have returning :=
    gateFinishReturnGuard_scan_exact continuation
      checkScan (gateMark :: afterAnchor)
      (fun symbol member => (checkAllowed symbol member).1)
  have returningCanonical :
      workRunExact? machine checkScan.length
          (configAtLeftWord
            (State.finishGateReturnGuard .priorGate continuation)
            (pushCrossed checkScan [leftGuard])
            (gateMark :: afterAnchor)) =
        some
          (configAtLeftWord
            (State.finishGateReturnGuard .priorGate continuation)
            [leftGuard] (sweep ++ cursorMark :: suffix)) := by
    simpa [pushCrossed_eq_reverse_append, sweep, guardedPrefix,
      checkScan, afterAnchor, markedGateListCells, markedGateCells,
      List.append_assoc] using returning
  have returnGuard :=
    gateFinishReturnGuard_exact continuation
      (sweep ++ cursorMark :: suffix)
  have version :=
    gateFinishVersion_exact continuation [leftGuard]
      (natCells inputs ++
        countCells gateCountUsed gateCountRemaining ++ referenceRest)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord
            (State.finishGateVersionFirst .priorGate continuation)
            [leftGuard] (sweep ++ cursorMark :: suffix)) =
        some
          (configAtWord
            (State.finishGateInputFirst .priorGate continuation)
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gateCountUsed gateCountRemaining ++
              referenceRest)) := by
    simpa [sweep, guardedPrefix, header, referenceRest,
      gateReferenceHeader, List.append_assoc] using version
  have input :=
    gateFinishInput_exact continuation inputs
      [cell00, cell00, leftGuard]
      (countCells gateCountUsed gateCountRemaining ++ referenceRest)
  have inputCanonical :
      workRunExact? machine (2 * (inputs + 1))
          (configAtWord
            (State.finishGateInputFirst .priorGate continuation)
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gateCountUsed gateCountRemaining ++
              referenceRest)) =
        some
          (configAtWord
            (State.finishGateCountFirst .priorGate continuation)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (countCells gateCountUsed gateCountRemaining ++
              referenceRest)) := by
    simpa [List.append_assoc] using input
  have count :=
    gateFinishCount_exact continuation
      gateCountUsed gateCountRemaining
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      referenceRest
  let headerLeft := pushCrossed header [leftGuard]
  have countCanonical :
      workRunExact? machine
          (2 * (gateCountUsed + gateCountRemaining + 1))
          (configAtWord
            (State.finishGateCountFirst .priorGate continuation)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (countCells gateCountUsed gateCountRemaining ++
              referenceRest)) =
        some
          (configAtWord
            (State.finishGateRestore .priorGate continuation)
            headerLeft referenceRest) := by
    have headerLeftEq :
        pushCrossed
            (countCells gateCountUsed gateCountRemaining)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard]) =
          headerLeft := by
      unfold headerLeft header gateReferenceHeader
      repeat rw [pushCrossed_append]
      rfl
    rw [← headerLeftEq]
    exact count
  have restoreBorrowed :=
    gateFinishRestoreGateList_exact continuation borrowed
      headerLeft
      (markedGateListCells (gate :: available) ++ between ++
        [cell00, cursorMark] ++ suffix)
  have restoreBorrowedCanonical :
      workRunExact? machine (borrowedGateListCells borrowed).length
          (configAtWord
            (State.finishGateRestore .priorGate continuation)
            headerLeft referenceRest) =
        some
          (configAtWord
            (State.finishGateRestore .priorGate continuation)
            (pushCrossed (markedGateListCells borrowed) headerLeft)
            (restoreScan ++ cursorMark :: suffix)) := by
    simpa [referenceRest, restoreScan, List.append_assoc]
      using restoreBorrowed
  have restoreScanAllowed :
      ∀ symbol, symbol ∈ restoreScan →
        ordinaryNonCountMarker symbol := by
    intro symbol member
    unfold restoreScan at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact
          ⟨markedGateListCells_ordinary
              (gate :: available) symbol member,
            markedGateListCells_no_countMark
              (gate :: available) symbol member⟩
      · exact
          ⟨betweenOrdinary symbol member,
            betweenNoCountMark symbol member⟩
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact ⟨cell00_ordinary, by decide⟩
      · contradiction
  have restoreTail :=
    gateFinishRestoreScan_exact continuation
      (pushCrossed (markedGateListCells borrowed) headerLeft)
      restoreScan (cursorMark :: suffix) restoreScanAllowed
  have cursor :=
    gateFinishRestoreCursor_exact continuation
      (pushCrossed restoreScan
        (pushCrossed (markedGateListCells borrowed) headerLeft))
      suffix
  have throughBackward :=
    exactRun_add 2 sweep.length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add (2 + sweep.length) 1
      _ _ _ throughBackward guard
  have throughCheck :=
    exactRun_add ((2 + sweep.length) + 1) checkScan.length
      _ _ _ throughGuard checkCanonical
  have throughAnchor :=
    exactRun_add
      (((2 + sweep.length) + 1) + checkScan.length) 1
      _ _ _ throughCheck anchor
  have throughReturn :=
    exactRun_add
      ((((2 + sweep.length) + 1) + checkScan.length) + 1)
      checkScan.length
      _ _ _ throughAnchor returningCanonical
  have throughReturnGuard :=
    exactRun_add
      (((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length)
      1 _ _ _ throughReturn returnGuard
  have throughVersion :=
    exactRun_add
      ((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1)
      2 _ _ _ throughReturnGuard versionCanonical
  have throughInput :=
    exactRun_add
      (((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1) + 2)
      (2 * (inputs + 1))
      _ _ _ throughVersion inputCanonical
  have throughCount :=
    exactRun_add
      ((((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1) + 2) + 2 * (inputs + 1))
      (2 * (gateCountUsed + gateCountRemaining + 1))
      _ _ _ throughInput countCanonical
  have throughBorrowed :=
    exactRun_add
      (((((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1) + 2) + 2 * (inputs + 1)) +
        2 * (gateCountUsed + gateCountRemaining + 1))
      (borrowedGateListCells borrowed).length
      _ _ _ throughCount restoreBorrowedCanonical
  have throughRestore :=
    exactRun_add
      ((((((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1) + 2) + 2 * (inputs + 1)) +
        2 * (gateCountUsed + gateCountRemaining + 1)) +
        (borrowedGateListCells borrowed).length)
      restoreScan.length
      _ _ _ throughBorrowed restoreTail
  have all :=
    exactRun_add
      (((((((((((2 + sweep.length) + 1) + checkScan.length) + 1) +
        checkScan.length) + 1) + 2) + 2 * (inputs + 1)) +
        2 * (gateCountUsed + gateCountRemaining + 1)) +
        (borrowedGateListCells borrowed).length) +
        restoreScan.length)
      1 _ _ _ throughRestore cursor
  have endpointEq :
      cell10 ::
          pushCrossed restoreScan
            (pushCrossed (markedGateListCells borrowed) headerLeft) =
        pushCrossed
          (header ++
            markedGateListCells (borrowed ++ gate :: available) ++
            between ++ natCells 0)
          [leftGuard] := by
    unfold headerLeft restoreScan
    rw [markedGateListCells_append]
    unfold markedGateListCells natCells
    repeat rw [pushCrossed_append]
    rfl
  unfold gateReferenceFinishSteps
  unfold gateReferenceConfiguration
  unfold gateReferenceSuccessConfiguration
  unfold guardedConfig
  rw [← endpointEq]
  simpa [header, guardedPrefix, sweep, checkScan, referenceRest,
    afterAnchor, restoreScan, guardedConfig, natCells,
    List.append_assoc] using all

set_option maxRecDepth 100000 in
private theorem gateConsumeNoAnchor_exact
    (continuation : SourceContinuation)
    (left indexTail : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.consumeGateAnchor .priorGate continuation)
          left (cursorMark :: indexTail)) =
      some
        (configAtWord State.cleanupSeekGuard
          left (cursorMark :: indexTail)) := by
  cases continuation <;> rfl

set_option maxRecDepth 100000 in
private theorem gateFinishNoAnchor_exact
    (continuation : SourceContinuation)
    (left indexTail : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord
          (State.finishGateCheckAnchor .priorGate continuation)
          left (cursorMark :: indexTail)) =
      some
        (configAtWord State.cleanupSeekGuard
          left (cursorMark :: indexTail)) := by
  cases continuation <;> rfl

/-- Exact cost of discovering that no further prior-gate anchor exists. -/
def gateReferenceExhaustedSteps
    (header : List WorkSymbol)
    (borrowed : List RawGate)
    (between : List WorkSymbol) : Nat :=
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++ between
  let sweep := guardedPrefix ++ [cell00]
  2 + sweep.length + 1 + sweep.length + 1

/-- A further unary prior-gate index unit after every available gate has been
borrowed reaches cleanup at the preserved cursor.  The arbitrary index tail
is not interpreted. -/
theorem gateReferenceConsumeExhaustedTail_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate)
    (between indexTail : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoGateMark :
      ∀ symbol, symbol ∈ between → symbol ≠ gateMark) :
    workRunExact? machine
        (gateReferenceExhaustedSteps header borrowed between)
        (guardedConfig (State.indexFirst .priorGate continuation)
          (header ++ borrowedGateListCells borrowed ++ between)
          (cell00 :: cell01 :: indexTail)) =
      some
        (guardedConfig State.cleanupSeekGuard
          ((header ++ borrowedGateListCells borrowed ++ between) ++
            [cell00])
          (cursorMark :: indexTail)) := by
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++ between
  let sweep := guardedPrefix ++ [cell00]
  have first :=
    referenceIndexFirst_exact .priorGate continuation guardedPrefix
      cell01 indexTail
  have launch :=
    referenceIndexUnitLaunch_exact .priorGate continuation guardedPrefix
      indexTail
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have guardedPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol := by
    unfold guardedPrefix
    apply ordinary_append
    · apply ordinary_append
      · exact headerOrdinary
      · exact borrowedGateListCells_ordinary borrowed
    · exact betweenOrdinary
  have sweepOrdinary :
      ∀ symbol, symbol ∈ sweep → ordinaryCell symbol := by
    unfold sweep
    apply ordinary_append
    · exact guardedPrefixOrdinary
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have sweepNoGateMark :
      ∀ symbol, symbol ∈ sweep → symbol ≠ gateMark := by
    intro symbol member
    unfold sweep guardedPrefix at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact headerNoGateMark symbol member
        · exact
            borrowedGateListCells_no_gateMark borrowed symbol member
      · exact betweenNoGateMark symbol member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        decide
      · contradiction
  have backward :=
    referenceConsumeSeekGuard_scan_exact .priorGate continuation
      sweep (cursorMark :: indexTail) sweepOrdinary
  have guard :=
    referenceConsumeGuard_exact .priorGate continuation
      (sweep ++ cursorMark :: indexTail)
  have forward :=
    gateConsumeAnchorScan_exact continuation [leftGuard]
      sweep (cursorMark :: indexTail)
      (fun symbol member =>
        ⟨sweepOrdinary symbol member,
          sweepNoGateMark symbol member⟩)
  have forwardCanonical :
      workRunExact? machine sweep.length
          (configAtWord
            (consumeAfterGuardState .priorGate continuation)
            [leftGuard] (sweep ++ cursorMark :: indexTail)) =
        some
          (configAtWord
            (State.consumeGateAnchor .priorGate continuation)
            (pushCrossed sweep [leftGuard])
            (cursorMark :: indexTail)) := by
    simpa [consumeAfterGuardState] using forward
  have failure :=
    gateConsumeNoAnchor_exact continuation
      (pushCrossed sweep [leftGuard]) indexTail
  have throughBackward :=
    exactRun_add 2 sweep.length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add (2 + sweep.length) 1
      _ _ _ throughBackward guard
  have throughForward :=
    exactRun_add ((2 + sweep.length) + 1) sweep.length
      _ _ _ throughGuard forwardCanonical
  have all :=
    exactRun_add (((2 + sweep.length) + 1) + sweep.length) 1
      _ _ _ throughForward failure
  unfold gateReferenceExhaustedSteps
  unfold guardedConfig
  simpa [guardedPrefix, sweep, guardedConfig, List.append_assoc]
    using all

/-- Canonical specialization of the exhausted prior-gate unit trace. -/
theorem gateReferenceConsumeExhausted_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoGateMark :
      ∀ symbol, symbol ∈ between → symbol ≠ gateMark) :
    workRunExact? machine
        (gateReferenceExhaustedSteps header borrowed between)
        (gateReferenceConfiguration continuation header borrowed []
          between (index + 1) suffix) =
      some
        (guardedConfig State.cleanupSeekGuard
          ((header ++ borrowedGateListCells borrowed ++ between) ++
            [cell00])
          (cursorMark :: natCells index ++ suffix)) := by
  simpa [gateReferenceConfiguration, markedGateListCells, natCells,
    List.append_assoc] using
    gateReferenceConsumeExhaustedTail_exact continuation header borrowed
      between (natCells index ++ suffix)
      headerOrdinary headerNoGateMark betweenOrdinary betweenNoGateMark

/-- An index terminator with no remaining gate anchor reaches cleanup at the
same preserved cursor, without interpreting the arbitrary following tail. -/
theorem gateReferenceFinishExhaustedTail_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate)
    (between indexTail : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoGateMark :
      ∀ symbol, symbol ∈ between → symbol ≠ gateMark) :
    workRunExact? machine
        (gateReferenceExhaustedSteps header borrowed between)
        (guardedConfig (State.indexFirst .priorGate continuation)
          (header ++ borrowedGateListCells borrowed ++ between)
          (cell00 :: cell10 :: indexTail)) =
      some
        (guardedConfig State.cleanupSeekGuard
          ((header ++ borrowedGateListCells borrowed ++ between) ++
            [cell00])
          (cursorMark :: indexTail)) := by
  let guardedPrefix :=
    header ++ borrowedGateListCells borrowed ++ between
  let sweep := guardedPrefix ++ [cell00]
  have first :=
    referenceIndexFirst_exact .priorGate continuation guardedPrefix
      cell10 indexTail
  have launch :=
    referenceIndexFinishLaunch_exact .priorGate continuation guardedPrefix
      indexTail
  have indexLaunch := exactRun_add 1 1 _ _ _ first launch
  have guardedPrefixOrdinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol := by
    unfold guardedPrefix
    apply ordinary_append
    · apply ordinary_append
      · exact headerOrdinary
      · exact borrowedGateListCells_ordinary borrowed
    · exact betweenOrdinary
  have sweepOrdinary :
      ∀ symbol, symbol ∈ sweep → ordinaryCell symbol := by
    unfold sweep
    apply ordinary_append
    · exact guardedPrefixOrdinary
    · intro symbol member
      simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        exact cell00_ordinary
      · contradiction
  have sweepNoGateMark :
      ∀ symbol, symbol ∈ sweep → symbol ≠ gateMark := by
    intro symbol member
    unfold sweep guardedPrefix at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · exact headerNoGateMark symbol member
        · exact
            borrowedGateListCells_no_gateMark borrowed symbol member
      · exact betweenNoGateMark symbol member
    · simp only [List.mem_cons, List.not_mem_nil] at member
      rcases member with h | impossible
      · subst symbol
        decide
      · contradiction
  have backward :=
    referenceFinishSeekGuard_scan_exact .priorGate continuation
      sweep (cursorMark :: indexTail) sweepOrdinary
  have guard :=
    referenceFinishGuard_exact .priorGate continuation
      (sweep ++ cursorMark :: indexTail)
  have forward :=
    gateFinishCheckAnchorScan_exact continuation [leftGuard]
      sweep (cursorMark :: indexTail)
      (fun symbol member =>
        ⟨sweepOrdinary symbol member,
          sweepNoGateMark symbol member⟩)
  have forwardCanonical :
      workRunExact? machine sweep.length
          (configAtWord
            (finishAfterGuardState .priorGate continuation)
            [leftGuard] (sweep ++ cursorMark :: indexTail)) =
        some
          (configAtWord
            (State.finishGateCheckAnchor .priorGate continuation)
            (pushCrossed sweep [leftGuard])
            (cursorMark :: indexTail)) := by
    simpa [finishAfterGuardState] using forward
  have failure :=
    gateFinishNoAnchor_exact continuation
      (pushCrossed sweep [leftGuard]) indexTail
  have throughBackward :=
    exactRun_add 2 sweep.length
      _ _ _ indexLaunch backward
  have throughGuard :=
    exactRun_add (2 + sweep.length) 1
      _ _ _ throughBackward guard
  have throughForward :=
    exactRun_add ((2 + sweep.length) + 1) sweep.length
      _ _ _ throughGuard forwardCanonical
  have all :=
    exactRun_add (((2 + sweep.length) + 1) + sweep.length) 1
      _ _ _ throughForward failure
  unfold gateReferenceExhaustedSteps
  unfold guardedConfig
  simpa [guardedPrefix, sweep, guardedConfig, List.append_assoc]
    using all

/-- Canonical zero-index specialization of the no-anchor finish trace. -/
theorem gateReferenceFinishExhausted_exact
    (continuation : SourceContinuation)
    (header : List WorkSymbol)
    (borrowed : List RawGate)
    (between suffix : List WorkSymbol)
    (headerOrdinary :
      ∀ symbol, symbol ∈ header → ordinaryCell symbol)
    (headerNoGateMark :
      ∀ symbol, symbol ∈ header → symbol ≠ gateMark)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoGateMark :
      ∀ symbol, symbol ∈ between → symbol ≠ gateMark) :
    workRunExact? machine
        (gateReferenceExhaustedSteps header borrowed between)
        (gateReferenceConfiguration continuation header borrowed []
          between 0 suffix) =
      some
        (guardedConfig State.cleanupSeekGuard
          ((header ++ borrowedGateListCells borrowed ++ between) ++
            [cell00])
          (cursorMark :: suffix)) := by
  simpa [gateReferenceConfiguration, markedGateListCells, natCells,
    List.append_assoc] using
    gateReferenceFinishExhaustedTail_exact continuation header borrowed
      between suffix
      headerOrdinary headerNoGateMark betweenOrdinary betweenNoGateMark

/-- Exact recursive schedule for an in-range prior-gate reference. -/
def gateReferenceInRangeSteps
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol) : Nat → Nat
  | 0 =>
      match available with
      | [] => 0
      | gate :: rest =>
          gateReferenceFinishSteps inputs gateCountUsed
            gateCountRemaining borrowed gate rest between
  | index + 1 =>
      match available with
      | [] => 0
      | gate :: rest =>
          gateReferenceConsumeUnitSteps
              (gateReferenceHeader inputs
                gateCountUsed gateCountRemaining)
              borrowed gate rest between +
            gateReferenceInRangeSteps inputs gateCountUsed
              gateCountRemaining (borrowed ++ [gate]) rest
              (between ++ [cell00, cell01]) index

/-- Every strictly in-range prior-gate reference restores the complete gate
anchor list and unary index before entering its source continuation. -/
theorem gateReferenceInRange_exact
    (continuation : SourceContinuation)
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoCountMark :
      ∀ symbol, symbol ∈ between → symbol ≠ countMark)
    (inRange : index < available.length) :
    let header :=
      gateReferenceHeader inputs gateCountUsed gateCountRemaining
    workRunExact? machine
        (gateReferenceInRangeSteps inputs gateCountUsed
          gateCountRemaining borrowed available between index)
        (gateReferenceConfiguration continuation header borrowed
          available between index suffix) =
      some
        (gateReferenceSuccessConfiguration continuation header
          (borrowed ++ available) between index suffix) := by
  dsimp only
  let header :=
    gateReferenceHeader inputs gateCountUsed gateCountRemaining
  induction index generalizing borrowed available between with
  | zero =>
      cases available with
      | nil =>
          simp at inRange
      | cons gate rest =>
          simpa [gateReferenceInRangeSteps, header] using
            gateReferenceFinishInRange_exact continuation
              inputs gateCountUsed gateCountRemaining
              borrowed gate rest between suffix
              betweenOrdinary betweenNoCountMark
  | succ index ih =>
      cases available with
      | nil =>
          simp at inRange
      | cons gate rest =>
          have tailInRange : index < rest.length := by
            simpa using inRange
          have nextBetweenOrdinary :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  ordinaryCell symbol := by
            apply ordinary_append
            · exact betweenOrdinary
            · intro symbol member
              simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                exact cell00_ordinary
              · subst symbol
                exact cell01_ordinary
              · contradiction
          have nextBetweenNoCountMark :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  symbol ≠ countMark := by
            intro symbol member
            rcases List.mem_append.mp member with member | member
            · exact betweenNoCountMark symbol member
            · simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                decide
              · subst symbol
                decide
              · contradiction
          have first :=
            gateReferenceConsumeUnit_exact continuation header borrowed
              gate rest between index suffix
              (gateReferenceHeader_ordinary
                inputs gateCountUsed gateCountRemaining)
              (gateReferenceHeader_no_gateMark
                inputs gateCountUsed gateCountRemaining)
              betweenOrdinary
          have tail :=
            ih (borrowed ++ [gate]) rest
              (between ++ [cell00, cell01])
              nextBetweenOrdinary nextBetweenNoCountMark tailInRange
          have tailCanonical :
              workRunExact? machine
                  (gateReferenceInRangeSteps inputs gateCountUsed
                    gateCountRemaining (borrowed ++ [gate]) rest
                    (between ++ [cell00, cell01]) index)
                  (gateReferenceConfiguration continuation header
                    (borrowed ++ [gate]) rest
                    (between ++ [cell00, cell01]) index suffix) =
                some
                  (gateReferenceSuccessConfiguration continuation header
                    (borrowed ++ gate :: rest)
                    between (index + 1) suffix) := by
            simpa [gateReferenceSuccessConfiguration, natCells,
              List.append_assoc] using tail
          have all :=
            exactRun_add
              (gateReferenceConsumeUnitSteps header borrowed
                gate rest between)
              (gateReferenceInRangeSteps inputs gateCountUsed
                gateCountRemaining (borrowed ++ [gate]) rest
                (between ++ [cell00, cell01]) index)
              _ _ _ first tailCanonical
          simpa [gateReferenceInRangeSteps, header] using all

/-- Exact recursive schedule for an out-of-range prior-gate reference. -/
def gateReferenceOutOfRangeSteps
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol) : Nat → Nat
  | 0 =>
      match available with
      | [] =>
          gateReferenceExhaustedSteps
            (gateReferenceHeader inputs
              gateCountUsed gateCountRemaining)
            borrowed between
      | _ :: _ => 0
  | index + 1 =>
      match available with
      | [] =>
          gateReferenceExhaustedSteps
            (gateReferenceHeader inputs
              gateCountUsed gateCountRemaining)
            borrowed between
      | gate :: rest =>
          gateReferenceConsumeUnitSteps
              (gateReferenceHeader inputs
                gateCountUsed gateCountRemaining)
              borrowed gate rest between +
            gateReferenceOutOfRangeSteps inputs gateCountUsed
              gateCountRemaining (borrowed ++ [gate]) rest
              (between ++ [cell00, cell01]) index

/-- Every out-of-range prior-gate reference reaches literal guarded cleanup
at the preserved unary cursor. -/
theorem gateReferenceOutOfRange_cleanupEntry
    (continuation : SourceContinuation)
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) (suffix : List WorkSymbol)
    (betweenOrdinary :
      ∀ symbol, symbol ∈ between → ordinaryCell symbol)
    (betweenNoGateMark :
      ∀ symbol, symbol ∈ between → symbol ≠ gateMark)
    (outOfRange : available.length ≤ index) :
    let header :=
      gateReferenceHeader inputs gateCountUsed gateCountRemaining
    ∃ failurePrefix failureSuffix,
      workRunExact? machine
          (gateReferenceOutOfRangeSteps inputs gateCountUsed
            gateCountRemaining borrowed available between index)
          (gateReferenceConfiguration continuation header borrowed
            available between index suffix) =
        some
          (guardedConfig State.cleanupSeekGuard failurePrefix
            (cursorMark :: failureSuffix)) := by
  dsimp only
  let header :=
    gateReferenceHeader inputs gateCountUsed gateCountRemaining
  induction index generalizing borrowed available between with
  | zero =>
      have availableEq : available = [] := by
        cases available with
        | nil => rfl
        | cons gate rest =>
            simp at outOfRange
      subst available
      refine
        ⟨(header ++ borrowedGateListCells borrowed ++ between) ++
            [cell00],
          suffix, ?_⟩
      simpa [gateReferenceOutOfRangeSteps, header] using
        gateReferenceFinishExhausted_exact continuation header borrowed
          between suffix
          (gateReferenceHeader_ordinary
            inputs gateCountUsed gateCountRemaining)
          (gateReferenceHeader_no_gateMark
            inputs gateCountUsed gateCountRemaining)
          betweenOrdinary betweenNoGateMark
  | succ index ih =>
      cases available with
      | nil =>
          refine
            ⟨(header ++ borrowedGateListCells borrowed ++ between) ++
                [cell00],
              natCells index ++ suffix, ?_⟩
          simpa [gateReferenceOutOfRangeSteps, header] using
            gateReferenceConsumeExhausted_exact continuation header
              borrowed between index suffix
              (gateReferenceHeader_ordinary
                inputs gateCountUsed gateCountRemaining)
              (gateReferenceHeader_no_gateMark
                inputs gateCountUsed gateCountRemaining)
              betweenOrdinary betweenNoGateMark
      | cons gate rest =>
          have tailOutOfRange : rest.length ≤ index := by
            simpa using outOfRange
          have nextBetweenOrdinary :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  ordinaryCell symbol := by
            apply ordinary_append
            · exact betweenOrdinary
            · intro symbol member
              simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                exact cell00_ordinary
              · subst symbol
                exact cell01_ordinary
              · contradiction
          have nextBetweenNoGateMark :
              ∀ symbol,
                symbol ∈ between ++ [cell00, cell01] →
                  symbol ≠ gateMark := by
            intro symbol member
            rcases List.mem_append.mp member with member | member
            · exact betweenNoGateMark symbol member
            · simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                decide
              · subst symbol
                decide
              · contradiction
          have first :=
            gateReferenceConsumeUnit_exact continuation header borrowed
              gate rest between index suffix
              (gateReferenceHeader_ordinary
                inputs gateCountUsed gateCountRemaining)
              (gateReferenceHeader_no_gateMark
                inputs gateCountUsed gateCountRemaining)
              betweenOrdinary
          rcases
              ih (borrowed ++ [gate]) rest
                (between ++ [cell00, cell01])
                nextBetweenOrdinary nextBetweenNoGateMark
                tailOutOfRange with
            ⟨failurePrefix, failureSuffix, tail⟩
          refine ⟨failurePrefix, failureSuffix, ?_⟩
          have all :=
            exactRun_add
              (gateReferenceConsumeUnitSteps header borrowed
                gate rest between)
              (gateReferenceOutOfRangeSteps inputs gateCountUsed
                gateCountRemaining (borrowed ++ [gate]) rest
                (between ++ [cell00, cell01]) index)
              _ _ _ first tail
          simpa [gateReferenceOutOfRangeSteps, header] using all

/-! ### Complete well-formed source and gate traces -/

def sourceContextPrefix
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol) : List WorkSymbol :=
  gateReferenceHeader inputs gateCountUsed gateCountRemaining ++
    markedGateListCells priorGates ++ before

def sourceFirstWas01 : RawSource → Bool
  | .input _ => false
  | .constant _ => true
  | .gate _ => true

def sourceRemainderCells : RawSource → List WorkSymbol
  | .input index => cell11 :: natCells index
  | .constant false => [cell00]
  | .constant true => [cell01]
  | .gate index => cell10 :: natCells index

def sourceSecondCell : RawSource → WorkSymbol
  | .input _ => cell11
  | .constant false => cell00
  | .constant true => cell01
  | .gate _ => cell10

def sourceAfterSecondCells : RawSource → List WorkSymbol
  | .input index => natCells index
  | .constant _ => []
  | .gate index => natCells index

private theorem sourceCells_eq_first_remainder (source : RawSource) :
    sourceCells source =
      firstSourceCell (sourceFirstWas01 source) ::
        sourceRemainderCells source := by
  cases source with
  | input index => rfl
  | constant value =>
      cases value <;> rfl
  | gate index => rfl

private theorem sourceRemainderCells_eq_second (source : RawSource) :
    sourceRemainderCells source =
      sourceSecondCell source :: sourceAfterSecondCells source := by
  cases source with
  | input index => rfl
  | constant value =>
      cases value <;> rfl
  | gate index => rfl

set_option maxRecDepth 100000 in
private theorem sourceStartFirst_exact
    (continuation : SourceContinuation)
    (firstWas01 : Bool)
    (guardedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.sourceStart continuation)
          guardedPrefix
          (firstSourceCell firstWas01 :: rest)) =
      some
        (guardedConfig
          (afterFirstSourceState firstWas01 continuation)
          (guardedPrefix ++ [firstSourceCell firstWas01])
          rest) := by
  cases continuation <;> cases firstWas01 <;>
    unfold guardedConfig <;>
    rw [pushCrossed_append] <;> rfl

set_option maxRecDepth 100000 in
private theorem inputSourceIndexLaunch_exact
    (continuation : SourceContinuation)
    (guardedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter00 continuation)
          guardedPrefix (cell11 :: rest)) =
      some
        (guardedConfig (State.indexFirst .input continuation)
          (guardedPrefix ++ [cell11]) rest) := by
  cases continuation <;>
    unfold guardedConfig <;>
    rw [pushCrossed_append] <;> rfl

set_option maxRecDepth 100000 in
private theorem gateSourceIndexLaunch_exact
    (continuation : SourceContinuation)
    (guardedPrefix rest : List WorkSymbol) :
    workRunExact? machine 1
        (guardedConfig (State.sourceAfter01 continuation)
          guardedPrefix (cell10 :: rest)) =
      some
        (guardedConfig (State.indexFirst .priorGate continuation)
          (guardedPrefix ++ [cell10]) rest) := by
  cases continuation <;>
    unfold guardedConfig <;>
    rw [pushCrossed_append] <;> rfl

def sourceRemainderSteps
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol) : RawSource → Nat
  | .constant _ => 1
  | .input index =>
      let inputBetween :=
        countCells gateCountUsed gateCountRemaining ++
          markedGateListCells priorGates ++ before ++
          [cell00, cell11]
      1 + inputReferenceInRangeSteps 0 inputs inputBetween index
  | .gate index =>
      let gateBetween := before ++ [cell01, cell10]
      1 + gateReferenceInRangeSteps inputs gateCountUsed
        gateCountRemaining [] priorGates gateBetween index

theorem sourceRemainder_exact
    (continuation : SourceContinuation)
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) (suffix : List WorkSymbol)
    (beforeOrdinary :
      ∀ symbol, symbol ∈ before → ordinaryCell symbol)
    (beforeNoCountMark :
      ∀ symbol, symbol ∈ before → symbol ≠ countMark)
    (wellFormed :
      source.wellFormed inputs priorGates.length = true) :
    let context :=
      sourceContextPrefix inputs gateCountUsed gateCountRemaining
        priorGates before
    workRunExact? machine
        (sourceRemainderSteps inputs gateCountUsed gateCountRemaining
          priorGates before source)
        (guardedConfig
          (afterFirstSourceState (sourceFirstWas01 source)
            continuation)
          (context ++ [firstSourceCell (sourceFirstWas01 source)])
          (sourceRemainderCells source ++ suffix)) =
      some
        (guardedConfig (sourceDoneState continuation)
          (context ++ sourceCells source) suffix) := by
  dsimp only
  let context :=
    sourceContextPrefix inputs gateCountUsed gateCountRemaining
      priorGates before
  cases source with
  | constant value =>
      have base :=
        constantSourceRemainder_exact continuation value
          (pushCrossed (context ++ [cell01]) [leftGuard])
          suffix
      unfold sourceRemainderSteps
      unfold guardedConfig
      cases value <;>
        simpa [context, sourceContextPrefix, sourceFirstWas01,
          afterFirstSourceState, firstSourceCell,
          sourceRemainderCells, sourceCells,
          sourceDoneState, pushCrossed_append, pushCrossed,
          List.append_assoc] using base
  | input index =>
      have inRange : index < inputs := by
        simpa [RawSource.wellFormed] using wellFormed
      let inputBetween :=
        countCells gateCountUsed gateCountRemaining ++
          markedGateListCells priorGates ++ before ++
          [cell00, cell11]
      have inputBetweenOrdinary :
          ∀ symbol, symbol ∈ inputBetween → ordinaryCell symbol := by
        unfold inputBetween
        apply ordinary_append
        · apply ordinary_append
          · apply ordinary_append
            · exact
                countCells_ordinary
                  gateCountUsed gateCountRemaining
            · exact markedGateListCells_ordinary priorGates
          · exact beforeOrdinary
        · intro symbol member
          simp only [List.mem_cons, List.not_mem_nil] at member
          rcases member with h | h | impossible
          · subst symbol
            exact cell00_ordinary
          · subst symbol
            exact cell11_ordinary
          · contradiction
      have launch :=
        inputSourceIndexLaunch_exact continuation
          (context ++ [cell00]) (natCells index ++ suffix)
      have launchCanonical :
          workRunExact? machine 1
              (guardedConfig (State.sourceAfter00 continuation)
                (context ++ [cell00])
                (cell11 :: natCells index ++ suffix)) =
            some
              (guardedConfig (State.indexFirst .input continuation)
                (context ++ [cell00, cell11])
                (natCells index ++ suffix)) := by
        simpa [List.append_assoc] using launch
      have reference :=
        inputReferenceInRange_exact continuation 0 inputs index
          inputBetween suffix inputBetweenOrdinary inRange
      have referenceCanonical :
          workRunExact? machine
              (inputReferenceInRangeSteps 0 inputs
                inputBetween index)
              (guardedConfig (State.indexFirst .input continuation)
                (context ++ [cell00, cell11])
                (natCells index ++ suffix)) =
            some
              (guardedConfig (sourceDoneState continuation)
                (context ++ sourceCells (.input index)) suffix) := by
        simpa [inputReferenceConfiguration,
          inputReferenceSuccessConfiguration,
          context, sourceContextPrefix, inputBetween,
          gateReferenceHeader, countCells, sourceCells,
          List.append_assoc] using reference
      have all :=
        exactRun_add 1
          (inputReferenceInRangeSteps 0 inputs inputBetween index)
          _ _ _ launchCanonical referenceCanonical
      unfold sourceRemainderSteps
      simpa [context, inputBetween, sourceFirstWas01,
        afterFirstSourceState, firstSourceCell,
        sourceRemainderCells, sourceCells,
        List.append_assoc] using all
  | gate index =>
      have inRange : index < priorGates.length := by
        simpa [RawSource.wellFormed] using wellFormed
      let gateBetween := before ++ [cell01, cell10]
      have gateBetweenOrdinary :
          ∀ symbol, symbol ∈ gateBetween → ordinaryCell symbol := by
        unfold gateBetween
        apply ordinary_append
        · exact beforeOrdinary
        · intro symbol member
          simp only [List.mem_cons, List.not_mem_nil] at member
          rcases member with h | h | impossible
          · subst symbol
            exact cell01_ordinary
          · subst symbol
            exact cell10_ordinary
          · contradiction
      have gateBetweenNoCountMark :
          ∀ symbol, symbol ∈ gateBetween → symbol ≠ countMark := by
        intro symbol member
        unfold gateBetween at member
        rcases List.mem_append.mp member with member | member
        · exact beforeNoCountMark symbol member
        · simp only [List.mem_cons, List.not_mem_nil] at member
          rcases member with h | h | impossible
          · subst symbol
            decide
          · subst symbol
            decide
          · contradiction
      have launch :=
        gateSourceIndexLaunch_exact continuation
          (context ++ [cell01]) (natCells index ++ suffix)
      have launchCanonical :
          workRunExact? machine 1
              (guardedConfig (State.sourceAfter01 continuation)
                (context ++ [cell01])
                (cell10 :: natCells index ++ suffix)) =
            some
              (guardedConfig
                (State.indexFirst .priorGate continuation)
                (context ++ [cell01, cell10])
                (natCells index ++ suffix)) := by
        simpa [List.append_assoc] using launch
      have reference :=
        gateReferenceInRange_exact continuation
          inputs gateCountUsed gateCountRemaining
          [] priorGates gateBetween index suffix
          gateBetweenOrdinary gateBetweenNoCountMark inRange
      have referenceCanonical :
          workRunExact? machine
              (gateReferenceInRangeSteps inputs gateCountUsed
                gateCountRemaining [] priorGates gateBetween index)
              (guardedConfig
                (State.indexFirst .priorGate continuation)
                (context ++ [cell01, cell10])
                (natCells index ++ suffix)) =
            some
              (guardedConfig (sourceDoneState continuation)
                (context ++ sourceCells (.gate index)) suffix) := by
        simpa [gateReferenceConfiguration,
          gateReferenceSuccessConfiguration,
          context, sourceContextPrefix, gateBetween,
          borrowedGateListCells, sourceCells,
          List.append_assoc] using reference
      have all :=
        exactRun_add 1
          (gateReferenceInRangeSteps inputs gateCountUsed
            gateCountRemaining [] priorGates gateBetween index)
          _ _ _ launchCanonical referenceCanonical
      unfold sourceRemainderSteps
      simpa [context, gateBetween, sourceFirstWas01,
        afterFirstSourceState, firstSourceCell,
        sourceRemainderCells, sourceCells,
        List.append_assoc] using all

def sourceSteps
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) : Nat :=
  1 + sourceRemainderSteps inputs gateCountUsed gateCountRemaining
    priorGates before source

theorem source_exact
    (continuation : SourceContinuation)
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) (suffix : List WorkSymbol)
    (beforeOrdinary :
      ∀ symbol, symbol ∈ before → ordinaryCell symbol)
    (beforeNoCountMark :
      ∀ symbol, symbol ∈ before → symbol ≠ countMark)
    (wellFormed :
      source.wellFormed inputs priorGates.length = true) :
    let context :=
      sourceContextPrefix inputs gateCountUsed gateCountRemaining
        priorGates before
    workRunExact? machine
        (sourceSteps inputs gateCountUsed gateCountRemaining
          priorGates before source)
        (guardedConfig (State.sourceStart continuation)
          context (sourceCells source ++ suffix)) =
      some
        (guardedConfig (sourceDoneState continuation)
          (context ++ sourceCells source) suffix) := by
  dsimp only
  let context :=
    sourceContextPrefix inputs gateCountUsed gateCountRemaining
      priorGates before
  have launch :=
    sourceStartFirst_exact continuation (sourceFirstWas01 source)
      context (sourceRemainderCells source ++ suffix)
  have launchCanonical :
      workRunExact? machine 1
          (guardedConfig (State.sourceStart continuation)
            context (sourceCells source ++ suffix)) =
        some
          (guardedConfig
            (afterFirstSourceState (sourceFirstWas01 source)
              continuation)
            (context ++ [firstSourceCell (sourceFirstWas01 source)])
            (sourceRemainderCells source ++ suffix)) := by
    simpa [sourceCells_eq_first_remainder, List.append_assoc]
      using launch
  have remainder :=
    sourceRemainder_exact continuation inputs gateCountUsed
      gateCountRemaining priorGates before source suffix
      beforeOrdinary beforeNoCountMark wellFormed
  have all :=
    exactRun_add 1
      (sourceRemainderSteps inputs gateCountUsed gateCountRemaining
        priorGates before source)
      _ _ _ launchCanonical remainder
  simpa [sourceSteps, context] using all

def gateSteps
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate) : Nat :=
  2 * (gatePrefix inputs done (gate :: todo)).length + 3 +
    sourceRemainderSteps inputs (done.length + 1) todo.length
      done [] gate.left +
    sourceSteps inputs (done.length + 1) todo.length
      done (sourceCells gate.left) gate.right +
    2

/-- Exact cost of gate-count decrement and launch at the remainder of the
left source token. -/
def gateSourceLaunchSteps
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate) : Nat :=
  2 * (gatePrefix inputs done (gate :: todo)).length + 3

/-- Gate parsing reaches the canonical after-first-cell left-source
checkpoint without assuming that either source is well formed.  Failure
traces reuse this boundary before dispatching on the remaining source token. -/
theorem gateLeftRemainder_exact
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate)
    (after : List WorkSymbol) :
    workRunExact? machine
        (gateSourceLaunchSteps inputs done gate todo)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (gateCells gate ++ gateListCells todo ++ after)) =
      some
        (guardedConfig
          (afterFirstSourceState
            (sourceFirstWas01 gate.left) .gateLeft)
          (sourceContextPrefix inputs (done.length + 1)
            todo.length done [] ++
            [firstSourceCell (sourceFirstWas01 gate.left)])
          (sourceRemainderCells gate.left ++
            sourceCells gate.right ++ [cell01, cell11] ++
            gateListCells todo ++ after)) := by
  have decrement :=
    gateDecrement_exact (sourceFirstWas01 gate.left)
      inputs done gate todo
      (sourceSecondCell gate.left)
      (sourceAfterSecondCells gate.left ++
        sourceCells gate.right ++ [cell01, cell11] ++
        gateListCells todo ++ after)
  unfold gateSourceLaunchSteps
  simpa [gateCells, sourceCells_eq_first_remainder,
    sourceRemainderCells_eq_second, sourceContextPrefix,
    gateReferenceHeader, gateParsingPrefix,
    List.append_assoc] using decrement

theorem gate_exact
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (todo : List RawGate)
    (after : List WorkSymbol)
    (wellFormed :
      gate.wellFormed inputs done.length = true) :
    workRunExact? machine (gateSteps inputs done gate todo)
        (guardedConfig State.gateStart
          (gatePrefix inputs done (gate :: todo))
          (gateCells gate ++ gateListCells todo ++ after)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ [gate]) todo)
          (gateListCells todo ++ after)) := by
  simp only [RawGate.wellFormed, Bool.and_eq_true] at wellFormed
  have leftWellFormed :
      gate.left.wellFormed inputs done.length = true := by
    exact wellFormed.1
  have rightWellFormed :
      gate.right.wellFormed inputs done.length = true := by
    exact wellFormed.2
  have decrementCanonical :
      workRunExact? machine
          (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
          (guardedConfig State.gateStart
            (gatePrefix inputs done (gate :: todo))
            (gateCells gate ++ gateListCells todo ++ after)) =
        some
          (guardedConfig
            (afterFirstSourceState
              (sourceFirstWas01 gate.left) .gateLeft)
            (sourceContextPrefix inputs (done.length + 1)
              todo.length done [] ++
              [firstSourceCell (sourceFirstWas01 gate.left)])
            (sourceRemainderCells gate.left ++
              sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) := by
    simpa [gateSourceLaunchSteps] using
      gateLeftRemainder_exact inputs done gate todo after
  have leftSource :=
    sourceRemainder_exact .gateLeft inputs
      (done.length + 1) todo.length done [] gate.left
      (sourceCells gate.right ++ [cell01, cell11] ++
        gateListCells todo ++ after)
      (by intro symbol member; contradiction)
      (by intro symbol member; contradiction)
      leftWellFormed
  have leftSourceCanonical :
      workRunExact? machine
          (sourceRemainderSteps inputs (done.length + 1) todo.length
            done [] gate.left)
          (guardedConfig
            (afterFirstSourceState
              (sourceFirstWas01 gate.left) .gateLeft)
            (sourceContextPrefix inputs (done.length + 1)
              todo.length done [] ++
              [firstSourceCell (sourceFirstWas01 gate.left)])
            (sourceRemainderCells gate.left ++
              sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) =
        some
          (guardedConfig (State.sourceStart .gateRight)
            (sourceContextPrefix inputs (done.length + 1)
              todo.length done [] ++ sourceCells gate.left)
            (sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) := by
    simpa [sourceDoneState, List.append_assoc] using leftSource
  have rightSource :=
    source_exact .gateRight inputs
      (done.length + 1) todo.length done
      (sourceCells gate.left) gate.right
      ([cell01, cell11] ++ gateListCells todo ++ after)
      (sourceCells_ordinary gate.left)
      (sourceCells_no_countMark gate.left)
      rightWellFormed
  have rightSourceCanonical :
      workRunExact? machine
          (sourceSteps inputs (done.length + 1) todo.length
            done (sourceCells gate.left) gate.right)
          (guardedConfig (State.sourceStart .gateRight)
            (sourceContextPrefix inputs (done.length + 1)
              todo.length done [] ++ sourceCells gate.left)
            (sourceCells gate.right ++ [cell01, cell11] ++
              gateListCells todo ++ after)) =
        some
          (guardedConfig State.gateEndFirst
            (gateParsingPrefix inputs done todo ++
              sourceCells gate.left ++ sourceCells gate.right)
            (cell01 :: cell11 :: gateListCells todo ++ after)) := by
    simpa [sourceContextPrefix, gateReferenceHeader,
      gateParsingPrefix, sourceDoneState, List.append_assoc]
      using rightSource
  have ending :=
    gateEndGuarded_exact inputs done gate todo
      (gateListCells todo ++ after)
  have throughLeft :=
    exactRun_add
      (2 * (gatePrefix inputs done (gate :: todo)).length + 3)
      (sourceRemainderSteps inputs (done.length + 1) todo.length
        done [] gate.left)
      _ _ _ decrementCanonical leftSourceCanonical
  have throughRight :=
    exactRun_add
      ((2 * (gatePrefix inputs done (gate :: todo)).length + 3) +
        sourceRemainderSteps inputs (done.length + 1) todo.length
          done [] gate.left)
      (sourceSteps inputs (done.length + 1) todo.length
        done (sourceCells gate.left) gate.right)
      _ _ _ throughLeft rightSourceCanonical
  have all :=
    exactRun_add
      (((2 * (gatePrefix inputs done (gate :: todo)).length + 3) +
        sourceRemainderSteps inputs (done.length + 1) todo.length
          done [] gate.left) +
        sourceSteps inputs (done.length + 1) todo.length
          done (sourceCells gate.left) gate.right)
      2 _ _ _ throughRight ending
  simpa [gateSteps, List.append_assoc] using all

def gatesSteps
    (inputs : Nat) (done : List RawGate) :
    List RawGate → Nat
  | [] => 0
  | gate :: rest =>
      gateSteps inputs done gate rest +
        gatesSteps inputs (done ++ [gate]) rest

theorem gates_exact
    (inputs : Nat) (done gates : List RawGate)
    (after : List WorkSymbol)
    (wellFormed :
      rawGatesWellFormed inputs done.length gates = true) :
    workRunExact? machine (gatesSteps inputs done gates)
        (guardedConfig State.gateStart
          (gatePrefix inputs done gates)
          (gateListCells gates ++ after)) =
      some
        (guardedConfig State.gateStart
          (gatePrefix inputs (done ++ gates) [])
          after) := by
  induction gates generalizing done with
  | nil =>
      simp only [gatesSteps, gateListCells, List.nil_append,
        List.append_nil, workRunExact?]
  | cons gate rest ih =>
      simp only [rawGatesWellFormed, Bool.and_eq_true] at wellFormed
      have first :=
        gate_exact inputs done gate rest after wellFormed.1
      have restWellFormed :
          rawGatesWellFormed inputs (done ++ [gate]).length rest =
            true := by
        simpa [List.length_append] using wellFormed.2
      have tail :=
        ih (done ++ [gate]) restWellFormed
      have tailCanonical :
          workRunExact? machine
              (gatesSteps inputs (done ++ [gate]) rest)
              (guardedConfig State.gateStart
                (gatePrefix inputs (done ++ [gate]) rest)
                (gateListCells rest ++ after)) =
            some
              (guardedConfig State.gateStart
                (gatePrefix inputs (done ++ gate :: rest) [])
                after) := by
        simpa [List.append_assoc] using tail
      have all :=
        exactRun_add
          (gateSteps inputs done gate rest)
          (gatesSteps inputs (done ++ [gate]) rest)
          _ _ _ first tailCanonical
      simpa [gatesSteps, gateListCells, List.append_assoc] using all

/-! ### Program terminator and output launch -/

set_option maxRecDepth 100000 in
private theorem programEndLaunch_exact
    (guardedPrefix rest : List WorkSymbol) :
    workRunExact? machine 2
        (guardedConfig State.gateStart guardedPrefix
          (cell10 :: cell00 :: rest)) =
      some
        (configAtLeftWord State.programCountSeekGuard
          (cursorMark :: guardedPrefix.reverse ++ [leftGuard])
          (cell00 :: rest)) := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append]
  rfl

set_option maxRecDepth 100000 in
private theorem programSeekGuardCursor_exact
    (leftTail right : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord State.programCountSeekGuard
          (cursorMark :: leftTail) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          leftTail (cursorMark :: right)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSeekGuard_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtLeftWord State.programCountSeekGuard
          (head :: leftTail) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          leftTail (head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> rfl

private theorem programSeekGuard_scan_exact
    (guardedPrefix right : List WorkSymbol)
    (ordinary :
      ∀ symbol, symbol ∈ guardedPrefix → ordinaryCell symbol) :
    workRunExact? machine guardedPrefix.length
        (configAtLeftWord State.programCountSeekGuard
          (guardedPrefix.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord State.programCountSeekGuard
          [leftGuard] (guardedPrefix ++ right)) := by
  have scan :=
    scanLeft_exact State.programCountSeekGuard ordinaryCell
      programSeekGuard_step
      guardedPrefix.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
  simpa [pushCrossed_reverse] using scan

set_option maxRecDepth 100000 in
private theorem programSeekGuard_exact
    (suffix : List WorkSymbol) :
    workRunExact? machine 1
        (configAtLeftWord State.programCountSeekGuard
          [leftGuard] suffix) =
      some
        (configAtWord State.programSkipVersionFirst
          [leftGuard] suffix) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipVersion_exact
    (left suffix : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipVersionFirst left
          (cell00 :: cell00 :: suffix)) =
      some
        (configAtWord State.programSkipInputFirst
          (cell00 :: cell00 :: left) suffix) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipInputUnit_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipInputFirst left
          (cell00 :: cell01 :: rest)) =
      some
        (configAtWord State.programSkipInputFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipInputEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programSkipInputFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.programCountFirst
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem programSkipInput_exact
    (inputs : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (inputs + 1))
        (configAtWord State.programSkipInputFirst left
          (natCells inputs ++ suffix)) =
      some
        (configAtWord State.programCountFirst
          (pushCrossed (natCells inputs) left) suffix) := by
  induction inputs generalizing left with
  | zero =>
      exact programSkipInputEnd_exact left suffix
  | succ inputs ih =>
      have first :=
        programSkipInputUnit_exact left
          (natCells inputs ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (inputs + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (inputs + 1) =
            2 * ((inputs + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [natCells, pushCrossed] using all

set_option maxRecDepth 100000 in
private theorem programCountMarker_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programCountFirst left
          (cell00 :: countMark :: rest)) =
      some
        (configAtWord State.programCountFirst
          (cell01 :: cell00 :: left) rest) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programCountEnd_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 2
        (configAtWord State.programCountFirst left
          (cell00 :: cell10 :: rest)) =
      some
        (configAtWord State.programSeekCursor
          (cell10 :: cell00 :: left) rest) := by
  rfl

private theorem programCountRestore_exact
    (gateCount : Nat) (left suffix : List WorkSymbol) :
    workRunExact? machine (2 * (gateCount + 1))
        (configAtWord State.programCountFirst left
          (countCells gateCount 0 ++ suffix)) =
      some
        (configAtWord State.programSeekCursor
          (pushCrossed (natCells gateCount) left) suffix) := by
  induction gateCount generalizing left with
  | zero =>
      exact programCountEnd_exact left suffix
  | succ gateCount ih =>
      have first :=
        programCountMarker_exact left
          (countCells gateCount 0 ++ suffix)
      have tail := ih (cell01 :: cell00 :: left)
      have all :=
        exactRun_add 2 (2 * (gateCount + 1))
          _ _ _ first tail
      have costEq :
          2 + 2 * (gateCount + 1) =
            2 * ((gateCount + 1) + 1) := by
        omega
      rw [costEq] at all
      simpa [countCells, natCells, pushCrossed] using all

set_option maxRecDepth 100000 in
private theorem programSeekCursor_step
    (left : List WorkSymbol) (head : WorkSymbol)
    (suffix : List WorkSymbol)
    (ordinary : ordinaryCell head) :
    workStep? machine
        (configAtWord State.programSeekCursor
          left (head :: suffix)) =
      some
        (configAtWord State.programSeekCursor
          (head :: left) suffix) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head <;> rfl

set_option maxRecDepth 100000 in
private theorem programCursor_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord State.programSeekCursor left
          (cursorMark :: cell00 :: rest)) =
      some
        (configAtWord State.programSkipSecond
          (cell10 :: left) (cell00 :: rest)) := by
  rfl

set_option maxRecDepth 100000 in
private theorem programSkipSecond_exact
    (left rest : List WorkSymbol) :
    workRunExact? machine 1
        (configAtWord State.programSkipSecond left
          (cell00 :: rest)) =
      some
        (configAtWord (State.sourceStart .output)
          (cell00 :: left) rest) := by
  rfl

def programEndSteps (inputs : Nat) (gates : List RawGate) : Nat :=
  let logicalPrefix := gatePrefix inputs gates []
  2 + 1 + logicalPrefix.length + 1 +
    2 + 2 * (inputs + 1) + 2 * (gates.length + 1) +
    (markedGateListCells gates).length + 1 + 1

/-- The program terminator restores the declared gate-count field, retains
the persistent gate anchors, restores its cursor, and launches the output
source. -/
theorem programEnd_exact
    (inputs : Nat) (gates : List RawGate)
    (rest : List WorkSymbol) :
    workRunExact? machine (programEndSteps inputs gates)
        (guardedConfig State.gateStart
          (gatePrefix inputs gates [])
          (cell10 :: cell00 :: rest)) =
      some
        (guardedConfig (State.sourceStart .output)
          (sourceContextPrefix inputs 0 gates.length gates
            [cell10, cell00])
          rest) := by
  let logicalPrefix := gatePrefix inputs gates []
  let afterCount :=
    markedGateListCells gates ++
      cursorMark :: cell00 :: rest
  have launch :=
    programEndLaunch_exact logicalPrefix rest
  have cursorLeft :=
    programSeekGuardCursor_exact
      (logicalPrefix.reverse ++ [leftGuard])
      (cell00 :: rest)
  have backward :=
    programSeekGuard_scan_exact logicalPrefix
      (cursorMark :: cell00 :: rest)
      (gatePrefix_ordinary inputs gates [])
  have guard :=
    programSeekGuard_exact
      (logicalPrefix ++ cursorMark :: cell00 :: rest)
  have version :=
    programSkipVersion_exact [leftGuard]
      (natCells inputs ++ countCells gates.length 0 ++ afterCount)
  have versionCanonical :
      workRunExact? machine 2
          (configAtWord State.programSkipVersionFirst
            [leftGuard]
            (logicalPrefix ++ cursorMark :: cell00 :: rest)) =
        some
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gates.length 0 ++ afterCount)) := by
    simpa [logicalPrefix, gatePrefix, afterCount,
      List.append_assoc] using version
  have input :=
    programSkipInput_exact inputs
      [cell00, cell00, leftGuard]
      (countCells gates.length 0 ++ afterCount)
  have inputCanonical :
      workRunExact? machine (2 * (inputs + 1))
          (configAtWord State.programSkipInputFirst
            [cell00, cell00, leftGuard]
            (natCells inputs ++
              countCells gates.length 0 ++ afterCount)) =
        some
          (configAtWord State.programCountFirst
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])
            (countCells gates.length 0 ++ afterCount)) := by
    simpa [List.append_assoc] using input
  have count :=
    programCountRestore_exact gates.length
      (pushCrossed (natCells inputs)
        [cell00, cell00, leftGuard])
      afterCount
  have scan :=
    scanRight_exact State.programSeekCursor ordinaryCell
      programSeekCursor_step
      (markedGateListCells gates)
      (cursorMark :: cell00 :: rest)
      (pushCrossed (natCells gates.length)
        (pushCrossed (natCells inputs)
          [cell00, cell00, leftGuard]))
      (markedGateListCells_ordinary gates)
  have cursor :=
    programCursor_exact
      (pushCrossed (markedGateListCells gates)
        (pushCrossed (natCells gates.length)
          (pushCrossed (natCells inputs)
            [cell00, cell00, leftGuard])))
      rest
  have skip :=
    programSkipSecond_exact
      (cell10 ::
        pushCrossed (markedGateListCells gates)
          (pushCrossed (natCells gates.length)
            (pushCrossed (natCells inputs)
              [cell00, cell00, leftGuard])))
      rest
  have throughCursorLeft :=
    exactRun_add 2 1 _ _ _ launch cursorLeft
  have throughBackward :=
    exactRun_add (2 + 1) logicalPrefix.length
      _ _ _ throughCursorLeft backward
  have throughGuard :=
    exactRun_add ((2 + 1) + logicalPrefix.length) 1
      _ _ _ throughBackward guard
  have throughVersion :=
    exactRun_add
      (((2 + 1) + logicalPrefix.length) + 1)
      2 _ _ _ throughGuard versionCanonical
  have throughInput :=
    exactRun_add
      ((((2 + 1) + logicalPrefix.length) + 1) + 2)
      (2 * (inputs + 1))
      _ _ _ throughVersion inputCanonical
  have throughCount :=
    exactRun_add
      (((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1))
      (2 * (gates.length + 1))
      _ _ _ throughInput count
  have throughScan :=
    exactRun_add
      ((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1))
      (markedGateListCells gates).length
      _ _ _ throughCount scan
  have throughCursor :=
    exactRun_add
      (((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1)) +
        (markedGateListCells gates).length)
      1 _ _ _ throughScan cursor
  have all :=
    exactRun_add
      ((((((((2 + 1) + logicalPrefix.length) + 1) + 2) +
        2 * (inputs + 1)) + 2 * (gates.length + 1)) +
        (markedGateListCells gates).length) + 1)
      1 _ _ _ throughCursor skip
  have endpointEq :
      cell00 :: cell10 ::
          pushCrossed (markedGateListCells gates)
            (pushCrossed (natCells gates.length)
              (pushCrossed (natCells inputs)
                [cell00, cell00, leftGuard])) =
        pushCrossed
          (sourceContextPrefix inputs 0 gates.length gates
            [cell10, cell00])
          [leftGuard] := by
    unfold sourceContextPrefix gateReferenceHeader
    simp only [countCells]
    repeat rw [pushCrossed_append]
    rfl
  unfold programEndSteps
  unfold guardedConfig
  rw [← endpointEq]
  simpa [logicalPrefix, afterCount, guardedConfig,
    List.append_assoc] using all

/-! ### Final delimiters and accepting restoration -/

def markedCircuitCells (raw : RawCircuit) : List WorkSymbol :=
  [cell00, cell00] ++
    natCells raw.inputCount ++
    natCells raw.gates.length ++
    markedGateListCells raw.gates ++
    [cell10, cell00] ++
    sourceCells raw.output ++
    [cell10, cell01, cell10, cell11]

theorem markedCircuitCells_length (raw : RawCircuit) :
    (markedCircuitCells raw).length =
      (circuitCells raw).length := by
  unfold markedCircuitCells circuitCells
  simp only [List.length_append, markedGateListCells_length]

set_option maxRecDepth 100000 in
private theorem finalDelimiters_exact
    (guardedPrefix : List WorkSymbol) :
    workRunExact? machine 5
        (guardedConfig State.outputsEndFirst guardedPrefix
          [cell10, cell01, cell10, cell11]) =
      some
        (configAtLeftWord State.successRestoreLeft
          ((guardedPrefix ++
            [cell10, cell01, cell10, cell11]).reverse ++
            [leftGuard])
          [cellBlank]) := by
  unfold guardedConfig
  rw [pushCrossed_eq_reverse_append]
  simp [List.reverse_append]
  rfl

def restorePersistentSymbol (symbol : WorkSymbol) : WorkSymbol :=
  if symbol == gateMark then cell01 else symbol

set_option maxRecDepth 100000 in
private theorem successRestore_step
    (head : WorkSymbol) (leftTail right : List WorkSymbol)
    (ordinary : ordinaryCell head)
    (noCountMark : head ≠ countMark) :
    workStep? machine
        (configAtLeftWord State.successRestoreLeft
          (head :: leftTail) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          leftTail (restorePersistentSymbol head :: right)) := by
  rcases ordinary with h | h | h | h | h | h <;>
    subst head
  · rfl
  · rfl
  · exact False.elim (noCountMark rfl)
  · rfl
  · rfl
  · rfl

private theorem successRestoreNearest_exact
    (word leftSuffix right : List WorkSymbol)
    (ordinary : ∀ symbol, symbol ∈ word → ordinaryCell symbol)
    (noCountMark :
      ∀ symbol, symbol ∈ word → symbol ≠ countMark) :
    workRunExact? machine word.length
        (configAtLeftWord State.successRestoreLeft
          (word ++ leftSuffix) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          leftSuffix
          (pushCrossed (word.map restorePersistentSymbol) right)) := by
  induction word generalizing right with
  | nil =>
      rfl
  | cons head rest ih =>
      have headOrdinary :=
        ordinary head (List.Mem.head rest)
      have headNoCountMark :=
        noCountMark head (List.Mem.head rest)
      have restOrdinary :
          ∀ symbol, symbol ∈ rest → ordinaryCell symbol := by
        intro symbol member
        exact ordinary symbol (List.Mem.tail head member)
      have restNoCountMark :
          ∀ symbol, symbol ∈ rest → symbol ≠ countMark := by
        intro symbol member
        exact noCountMark symbol (List.Mem.tail head member)
      change
        (match workStep? machine
            (configAtLeftWord State.successRestoreLeft
              (head :: (rest ++ leftSuffix)) right) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) =
          some
            (configAtLeftWord State.successRestoreLeft
              leftSuffix
              (pushCrossed
                ((head :: rest).map restorePersistentSymbol)
                right))
      rw [successRestore_step head (rest ++ leftSuffix) right
        headOrdinary headNoCountMark]
      exact
        ih (restorePersistentSymbol head :: right)
          restOrdinary restNoCountMark

private theorem successRestoreWord_exact
    (word right : List WorkSymbol)
    (ordinary : ∀ symbol, symbol ∈ word → ordinaryCell symbol)
    (noCountMark :
      ∀ symbol, symbol ∈ word → symbol ≠ countMark) :
    workRunExact? machine word.length
        (configAtLeftWord State.successRestoreLeft
          (word.reverse ++ [leftGuard]) right) =
      some
        (configAtLeftWord State.successRestoreLeft
          [leftGuard]
          (word.map restorePersistentSymbol ++ right)) := by
  have scan :=
    successRestoreNearest_exact word.reverse [leftGuard] right
      (by
        intro symbol member
        exact ordinary symbol (by simpa using member))
      (by
        intro symbol member
        exact noCountMark symbol (by simpa using member))
  simpa [List.map_reverse, pushCrossed_reverse] using scan

private theorem restorePersistentSymbol_eq_self
    {symbol : WorkSymbol} (notGateMark : symbol ≠ gateMark) :
    restorePersistentSymbol symbol = symbol := by
  simp [restorePersistentSymbol, notGateMark]

private theorem map_restore_eq_self
    (word : List WorkSymbol)
    (noGateMark :
      ∀ symbol, symbol ∈ word → symbol ≠ gateMark) :
    word.map restorePersistentSymbol = word := by
  induction word with
  | nil =>
      rfl
  | cons head rest ih =>
      have headNe := noGateMark head (List.Mem.head rest)
      have restNe :
          ∀ symbol, symbol ∈ rest → symbol ≠ gateMark := by
        intro symbol member
        exact noGateMark symbol (List.Mem.tail head member)
      simp [restorePersistentSymbol_eq_self headNe, ih restNe]

private theorem map_restore_natCells (value : Nat) :
    (natCells value).map restorePersistentSymbol =
      natCells value :=
  map_restore_eq_self (natCells value) (natCells_no_gateMark value)

private theorem map_restore_sourceCells (source : RawSource) :
    (sourceCells source).map restorePersistentSymbol =
      sourceCells source :=
  map_restore_eq_self (sourceCells source)
    (sourceCells_no_gateMark source)

private theorem map_restore_markedGateCells (gate : RawGate) :
    (markedGateCells gate).map restorePersistentSymbol =
      gateCells gate := by
  unfold markedGateCells gateCells
  rw [List.map_append, List.map_append,
    map_restore_sourceCells, map_restore_sourceCells]
  rfl

private theorem map_restore_markedGateListCells
    (gates : List RawGate) :
    (markedGateListCells gates).map restorePersistentSymbol =
      gateListCells gates := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest ih =>
      unfold markedGateListCells gateListCells
      rw [List.map_append, map_restore_markedGateCells, ih]

private theorem map_restore_markedCircuitCells (raw : RawCircuit) :
    (markedCircuitCells raw).map restorePersistentSymbol =
      circuitCells raw := by
  unfold markedCircuitCells circuitCells
  simp only [List.map_append, List.map_cons, List.map_nil,
    map_restore_natCells, map_restore_markedGateListCells,
    map_restore_sourceCells]
  rfl

private theorem markedCircuitCells_ordinary (raw : RawCircuit) :
    ∀ symbol, symbol ∈ markedCircuitCells raw →
      ordinaryCell symbol := by
  unfold markedCircuitCells
  apply ordinary_append
  · apply ordinary_append
    · apply ordinary_append
      · apply ordinary_append
        · apply ordinary_append
          · apply ordinary_append
            · intro symbol member
              simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                exact cell00_ordinary
              · subst symbol
                exact cell00_ordinary
              · contradiction
            · exact natCells_ordinary raw.inputCount
          · exact natCells_ordinary raw.gates.length
        · exact markedGateListCells_ordinary raw.gates
      · intro symbol member
        simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          exact cell10_ordinary
        · subst symbol
          exact cell00_ordinary
        · contradiction
    · exact sourceCells_ordinary raw.output
  · intro symbol member
    simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | h | h | impossible
    · subst symbol
      exact cell10_ordinary
    · subst symbol
      exact cell01_ordinary
    · subst symbol
      exact cell10_ordinary
    · subst symbol
      exact cell11_ordinary
    · contradiction

private theorem markedCircuitCells_no_countMark (raw : RawCircuit) :
    ∀ symbol, symbol ∈ markedCircuitCells raw →
      symbol ≠ countMark := by
  unfold markedCircuitCells
  intro symbol member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_append.mp member with member | member
        · rcases List.mem_append.mp member with member | member
          · rcases List.mem_append.mp member with member | member
            · simp only [List.mem_cons, List.not_mem_nil] at member
              rcases member with h | h | impossible
              · subst symbol
                decide
              · subst symbol
                decide
              · contradiction
            · exact
                natCells_no_countMark raw.inputCount symbol member
          · exact
              natCells_no_countMark raw.gates.length symbol member
        · exact
            markedGateListCells_no_countMark raw.gates symbol member
      · simp only [List.mem_cons, List.not_mem_nil] at member
        rcases member with h | h | impossible
        · subst symbol
          decide
        · subst symbol
          decide
        · contradiction
    · exact sourceCells_no_countMark raw.output symbol member
  · simp only [List.mem_cons, List.not_mem_nil] at member
    rcases member with h | h | h | h | impossible
    · subst symbol
      decide
    · subst symbol
      decide
    · subst symbol
      decide
    · subst symbol
      decide
    · contradiction

set_option maxRecDepth 100000 in
private theorem successRestoreGuard_exact (raw : RawCircuit) :
    workRunExact? machine 1
        (configAtLeftWord State.successRestoreLeft
          [leftGuard] (circuitCells raw ++ [cellBlank])) =
      some (validFinalConfiguration raw) := by
  cases raw <;> rfl

def finalRestoreSteps (raw : RawCircuit) : Nat :=
  5 + (markedCircuitCells raw).length + 1

/-- Exact final delimiter, EOF, leftward gate-anchor restoration, and accept
trace.  The endpoint has the original encoded source and an explicit trailing
blank. -/
theorem finalRestore_exact (raw : RawCircuit) :
    workRunExact? machine (finalRestoreSteps raw)
        (guardedConfig State.outputsEndFirst
          (sourceContextPrefix raw.inputCount 0 raw.gates.length
            raw.gates [cell10, cell00] ++
            sourceCells raw.output)
          [cell10, cell01, cell10, cell11]) =
      some (validFinalConfiguration raw) := by
  let guardedPrefix :=
    sourceContextPrefix raw.inputCount 0 raw.gates.length
      raw.gates [cell10, cell00] ++ sourceCells raw.output
  have delimiters :=
    finalDelimiters_exact guardedPrefix
  have delimitersCanonical :
      workRunExact? machine 5
          (guardedConfig State.outputsEndFirst guardedPrefix
            [cell10, cell01, cell10, cell11]) =
        some
          (configAtLeftWord State.successRestoreLeft
            ((markedCircuitCells raw).reverse ++ [leftGuard])
            [cellBlank]) := by
    simpa [guardedPrefix, markedCircuitCells,
      sourceContextPrefix, gateReferenceHeader, countCells,
      List.append_assoc] using delimiters
  have restore :=
    successRestoreWord_exact (markedCircuitCells raw)
      [cellBlank] (markedCircuitCells_ordinary raw)
      (markedCircuitCells_no_countMark raw)
  have restoreCanonical :
      workRunExact? machine (markedCircuitCells raw).length
          (configAtLeftWord State.successRestoreLeft
            ((markedCircuitCells raw).reverse ++ [leftGuard])
            [cellBlank]) =
        some
          (configAtLeftWord State.successRestoreLeft
            [leftGuard] (circuitCells raw ++ [cellBlank])) := by
    rw [map_restore_markedCircuitCells] at restore
    exact restore
  have guard := successRestoreGuard_exact raw
  have throughRestore :=
    exactRun_add 5 (markedCircuitCells raw).length
      _ _ _ delimitersCanonical restoreCanonical
  have all :=
    exactRun_add (5 + (markedCircuitCells raw).length) 1
      _ _ _ throughRestore guard
  simpa [finalRestoreSteps, guardedPrefix] using all

/-! ### Whole canonical accepting trace -/

def circuitAfterHeaderCells (raw : RawCircuit) : List WorkSymbol :=
  gateListCells raw.gates ++
    [cell10, cell00] ++ sourceCells raw.output ++
    [cell10, cell01, cell10, cell11]

private theorem circuitAfterHeaderCells_ne_empty (raw : RawCircuit) :
    circuitAfterHeaderCells raw ≠ [] := by
  simp [circuitAfterHeaderCells]

def canonicalSteps (raw : RawCircuit) : Nat :=
  2 * raw.inputCount + 2 * raw.gates.length + 8 +
    gatesSteps raw.inputCount [] raw.gates +
    programEndSteps raw.inputCount raw.gates +
    sourceSteps raw.inputCount 0 raw.gates.length raw.gates
      [cell10, cell00] raw.output +
    finalRestoreSteps raw

/-- Exact operational accepting trace for every canonical well-formed raw
circuit.  The witness is the literal recursive schedule used by the later
polynomial-bound proof. -/
theorem canonical_exact
    (raw : RawCircuit) (wellFormed : raw.wellFormed = true) :
    workRunExact? machine (canonicalSteps raw)
        (workStartConfiguration machine
          (rawInputWorkTape (encodeCircuit raw))) =
      some (validFinalConfiguration raw) := by
  simp only [RawCircuit.wellFormed, Bool.and_eq_true] at wellFormed
  let afterGates :=
    [cell10, cell00] ++ sourceCells raw.output ++
      [cell10, cell01, cell10, cell11]
  have gatesWellFormed :
      rawGatesWellFormed raw.inputCount 0 raw.gates = true :=
    wellFormed.1
  have outputWellFormed :
      raw.output.wellFormed raw.inputCount raw.gates.length = true :=
    wellFormed.2
  cases cellsEq : circuitAfterHeaderCells raw with
  | nil =>
      exact False.elim (circuitAfterHeaderCells_ne_empty raw cellsEq)
  | cons current rest =>
      have header :=
        canonicalHeader_fixed_exact raw.inputCount raw.gates.length
          current rest
      have headerLeftEq :
          pushCrossed
              (gatePrefix raw.inputCount [] raw.gates)
              [leftGuard] =
            pushCrossed (natCells raw.gates.length)
              (pushCrossed (natCells raw.inputCount)
                [cell00, cell00, leftGuard]) := by
        unfold gatePrefix
        simp only [markedGateListCells, List.append_nil]
        repeat rw [pushCrossed_append]
        rfl
      have headerCanonical :
          workRunExact? machine
              (2 * raw.inputCount + 2 * raw.gates.length + 8)
              (workStartConfiguration machine
                (rawInputWorkTape (encodeCircuit raw))) =
            some
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount [] raw.gates)
                (gateListCells raw.gates ++ afterGates)) := by
        rw [← cellsEq] at header
        rw [rawInputWorkTape_encodeCircuit]
        unfold guardedConfig
        rw [headerLeftEq]
        simpa [circuitCells, circuitAfterHeaderCells,
          afterGates, gatePrefix, countCells, markedGateListCells,
          pushCrossed_append, List.append_assoc] using header
      have gates :=
        gates_exact raw.inputCount [] raw.gates afterGates
          gatesWellFormed
      have gatesCanonical :
          workRunExact? machine
              (gatesSteps raw.inputCount [] raw.gates)
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount [] raw.gates)
                (gateListCells raw.gates ++ afterGates)) =
            some
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount raw.gates [])
                afterGates) := by
        simpa using gates
      have program :=
        programEnd_exact raw.inputCount raw.gates
          (sourceCells raw.output ++
            [cell10, cell01, cell10, cell11])
      have programCanonical :
          workRunExact? machine
              (programEndSteps raw.inputCount raw.gates)
              (guardedConfig State.gateStart
                (gatePrefix raw.inputCount raw.gates [])
                afterGates) =
            some
              (guardedConfig (State.sourceStart .output)
                (sourceContextPrefix raw.inputCount 0
                  raw.gates.length raw.gates [cell10, cell00])
                (sourceCells raw.output ++
                  [cell10, cell01, cell10, cell11])) := by
        simpa [afterGates, List.append_assoc] using program
      have output :=
        source_exact .output raw.inputCount 0 raw.gates.length
          raw.gates [cell10, cell00] raw.output
          [cell10, cell01, cell10, cell11]
          (by
            intro symbol member
            simp only [List.mem_cons, List.not_mem_nil] at member
            rcases member with h | h | impossible
            · subst symbol
              exact cell10_ordinary
            · subst symbol
              exact cell00_ordinary
            · contradiction)
          (by
            intro symbol member
            simp only [List.mem_cons, List.not_mem_nil] at member
            rcases member with h | h | impossible
            · subst symbol
              decide
            · subst symbol
              decide
            · contradiction)
          outputWellFormed
      have restore := finalRestore_exact raw
      have throughGates :=
        exactRun_add
          (2 * raw.inputCount + 2 * raw.gates.length + 8)
          (gatesSteps raw.inputCount [] raw.gates)
          _ _ _ headerCanonical gatesCanonical
      have throughProgram :=
        exactRun_add
          ((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates)
          (programEndSteps raw.inputCount raw.gates)
          _ _ _ throughGates programCanonical
      have throughOutput :=
        exactRun_add
          (((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates) +
            programEndSteps raw.inputCount raw.gates)
          (sourceSteps raw.inputCount 0 raw.gates.length raw.gates
            [cell10, cell00] raw.output)
          _ _ _ throughProgram output
      have all :=
        exactRun_add
          ((((2 * raw.inputCount + 2 * raw.gates.length + 8) +
            gatesSteps raw.inputCount [] raw.gates) +
            programEndSteps raw.inputCount raw.gates) +
            sourceSteps raw.inputCount 0 raw.gates.length raw.gates
              [cell10, cell00] raw.output)
          (finalRestoreSteps raw)
          _ _ _ throughOutput restore
      simpa [canonicalSteps] using all

/-! ### Footprint-preserving schedule bounds -/

def inputReferenceFootprint
    (used remaining : Nat) (between : List WorkSymbol)
    (index : Nat) : Nat :=
  ([cell00, cell00] ++ countCells used remaining ++ between).length +
    (natCells index).length

private theorem inputReferenceConsumeUnit_bound
    (used remaining index : Nat)
    (between : List WorkSymbol) :
    inputReferenceConsumeUnitSteps used remaining between ≤
      8 *
        (inputReferenceFootprint used (remaining + 1)
          between (index + 1) + 1) := by
  unfold inputReferenceConsumeUnitSteps inputReferenceFootprint
  simp only [List.length_append, List.length_cons, List.length_nil,
    countCells_length, natCells_length]
  omega

private theorem inputReferenceFinish_bound
    (used spare : Nat) (between : List WorkSymbol) :
    inputReferenceFinishSteps used spare between ≤
      8 *
        (inputReferenceFootprint used (spare + 1)
          between 0 + 1) := by
  unfold inputReferenceFinishSteps inputReferenceFootprint
  simp only [List.length_append, List.length_cons, List.length_nil,
    countCells_length, borrowedCountCells_length, natCells_length]
  omega

theorem inputReferenceInRangeSteps_bound
    (used remaining : Nat) (between : List WorkSymbol)
    (index : Nat) :
    inputReferenceInRangeSteps used remaining between index ≤
      8 * (index + 1) *
        (inputReferenceFootprint used remaining between index + 1) := by
  induction index generalizing used remaining between with
  | zero =>
      cases remaining with
      | zero =>
          simp [inputReferenceInRangeSteps]
      | succ spare =>
          have atom :=
            inputReferenceFinish_bound used spare between
          simpa [inputReferenceInRangeSteps] using atom
  | succ index ih =>
      cases remaining with
      | zero =>
          simp [inputReferenceInRangeSteps]
      | succ rest =>
          have atom :=
            inputReferenceConsumeUnit_bound
              used rest index between
          have tail :=
            ih (used + 1) rest
              (between ++ [cell00, cell01])
          have footprintEq :
              inputReferenceFootprint (used + 1) rest
                  (between ++ [cell00, cell01]) index =
                inputReferenceFootprint used (rest + 1)
                  between (index + 1) := by
            unfold inputReferenceFootprint
            simp only [List.length_append, List.length_cons,
              List.length_nil, countCells_length, natCells_length]
            omega
          have combined :=
            Nat.add_le_add atom tail
          rw [footprintEq] at combined
          have costEq :
              8 *
                    (inputReferenceFootprint used (rest + 1)
                      between (index + 1) + 1) +
                  8 * (index + 1) *
                    (inputReferenceFootprint used (rest + 1)
                      between (index + 1) + 1) =
                8 * ((index + 1) + 1) *
                  (inputReferenceFootprint used (rest + 1)
                    between (index + 1) + 1) := by
            calc
              _ =
                  (8 + 8 * (index + 1)) *
                    (inputReferenceFootprint used (rest + 1)
                      between (index + 1) + 1) := by
                rw [Nat.add_mul]
              _ = _ := by
                apply congrArg (fun coefficient =>
                  coefficient *
                    (inputReferenceFootprint used (rest + 1)
                      between (index + 1) + 1))
                rw [Nat.mul_add, Nat.mul_one]
                exact Nat.add_comm _ _
          rw [costEq] at combined
          change
            inputReferenceConsumeUnitSteps used rest between +
                inputReferenceInRangeSteps (used + 1) rest
                  (between ++ [cell00, cell01]) index ≤
              8 * ((index + 1) + 1) *
                (inputReferenceFootprint used (rest + 1)
                  between (index + 1) + 1)
          exact combined

def gateReferenceFootprint
    (header : List WorkSymbol)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) : Nat :=
  (header ++ borrowedGateListCells borrowed ++
      markedGateListCells available ++ between).length +
    (natCells index).length

private theorem gateReferenceConsumeUnit_bound
    (header : List WorkSymbol)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) :
    gateReferenceConsumeUnitSteps
        header borrowed gate available between ≤
      8 *
        (gateReferenceFootprint header borrowed
          (gate :: available) between (index + 1) + 1) := by
  unfold gateReferenceConsumeUnitSteps gateReferenceFootprint
  simp only [List.length_append, List.length_cons, List.length_nil,
    borrowedGateListCells_length, markedGateListCells_length,
    natCells_length, gateListCells, gateCells]
  omega

private theorem gateReferenceFinish_bound
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed : List RawGate) (gate : RawGate)
    (available : List RawGate)
    (between : List WorkSymbol) :
    gateReferenceFinishSteps inputs gateCountUsed gateCountRemaining
        borrowed gate available between ≤
      8 *
        (gateReferenceFootprint
          (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
          borrowed (gate :: available) between 0 + 1) := by
  unfold gateReferenceFinishSteps gateReferenceFootprint
  unfold gateReferenceHeader
  simp only [List.length_append, List.length_cons, List.length_nil,
    borrowedGateListCells_length, markedGateListCells_length,
    countCells_length, natCells_length,
    gateListCells, gateCells]
  omega

theorem gateReferenceInRangeSteps_bound
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) :
    gateReferenceInRangeSteps inputs gateCountUsed gateCountRemaining
        borrowed available between index ≤
      8 * (index + 1) *
        (gateReferenceFootprint
          (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
          borrowed available between index + 1) := by
  let header :=
    gateReferenceHeader inputs gateCountUsed gateCountRemaining
  induction index generalizing borrowed available between with
  | zero =>
      cases available with
      | nil =>
          simp [gateReferenceInRangeSteps]
      | cons gate rest =>
          have atom :=
            gateReferenceFinish_bound inputs gateCountUsed
              gateCountRemaining borrowed gate rest between
          simpa [gateReferenceInRangeSteps, header] using atom
  | succ index ih =>
      cases available with
      | nil =>
          simp [gateReferenceInRangeSteps]
      | cons gate rest =>
          have atom :=
            gateReferenceConsumeUnit_bound header borrowed gate rest
              between index
          have tail :=
            ih (borrowed ++ [gate]) rest
              (between ++ [cell00, cell01])
          have footprintEq :
              gateReferenceFootprint header (borrowed ++ [gate])
                  rest (between ++ [cell00, cell01]) index =
                gateReferenceFootprint header borrowed
                  (gate :: rest) between (index + 1) := by
            unfold gateReferenceFootprint
            rw [borrowedGateListCells_append]
            simp only [List.length_append, List.length_cons,
              List.length_nil, borrowedGateListCells,
              borrowedGateCells_length,
              markedGateListCells_length, gateListCells,
              natCells_length]
            omega
          have combined :=
            Nat.add_le_add atom tail
          rw [footprintEq] at combined
          have costEq :
              8 *
                    (gateReferenceFootprint header borrowed
                      (gate :: rest) between (index + 1) + 1) +
                  8 * (index + 1) *
                    (gateReferenceFootprint header borrowed
                      (gate :: rest) between (index + 1) + 1) =
                8 * ((index + 1) + 1) *
                  (gateReferenceFootprint header borrowed
                    (gate :: rest) between (index + 1) + 1) := by
            calc
              _ =
                  (8 + 8 * (index + 1)) *
                    (gateReferenceFootprint header borrowed
                      (gate :: rest) between (index + 1) + 1) := by
                rw [Nat.add_mul]
              _ = _ := by
                apply congrArg (fun coefficient =>
                  coefficient *
                    (gateReferenceFootprint header borrowed
                      (gate :: rest) between (index + 1) + 1))
                rw [Nat.mul_add, Nat.mul_one]
                exact Nat.add_comm _ _
          rw [costEq] at combined
          change
            gateReferenceConsumeUnitSteps header borrowed gate rest
                between +
                gateReferenceInRangeSteps inputs gateCountUsed
                  gateCountRemaining (borrowed ++ [gate]) rest
                  (between ++ [cell00, cell01]) index ≤
              8 * ((index + 1) + 1) *
                (gateReferenceFootprint header borrowed
                  (gate :: rest) between (index + 1) + 1)
          exact combined

private theorem inputReferenceInRangeSteps_square_bound
    (used remaining : Nat) (between : List WorkSymbol)
    (index : Nat) :
    inputReferenceInRangeSteps used remaining between index ≤
      8 *
        ((inputReferenceFootprint used remaining between index + 1) *
          (inputReferenceFootprint used remaining between index + 1)) := by
  have run :=
    inputReferenceInRangeSteps_bound used remaining between index
  have indexLe :
      index + 1 ≤
        inputReferenceFootprint used remaining between index + 1 := by
    unfold inputReferenceFootprint
    simp only [List.length_append, List.length_cons, List.length_nil,
      countCells_length, natCells_length]
    omega
  have scaled := Nat.mul_le_mul_left 8 indexLe
  have squared :=
    Nat.mul_le_mul_right
      (inputReferenceFootprint used remaining between index + 1)
      scaled
  exact Nat.le_trans run (by
    simpa [Nat.mul_assoc] using squared)

private theorem gateReferenceInRangeSteps_square_bound
    (inputs gateCountUsed gateCountRemaining : Nat)
    (borrowed available : List RawGate)
    (between : List WorkSymbol)
    (index : Nat) :
    gateReferenceInRangeSteps inputs gateCountUsed gateCountRemaining
        borrowed available between index ≤
      8 *
        ((gateReferenceFootprint
            (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
            borrowed available between index + 1) *
          (gateReferenceFootprint
            (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
            borrowed available between index + 1)) := by
  have run :=
    gateReferenceInRangeSteps_bound inputs gateCountUsed
      gateCountRemaining borrowed available between index
  have indexLe :
      index + 1 ≤
        gateReferenceFootprint
            (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
            borrowed available between index + 1 := by
    unfold gateReferenceFootprint
    simp only [List.length_append, natCells_length]
    omega
  have scaled := Nat.mul_le_mul_left 8 indexLe
  have squared :=
    Nat.mul_le_mul_right
      (gateReferenceFootprint
        (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
        borrowed available between index + 1)
      scaled
  exact Nat.le_trans run (by
    simpa [Nat.mul_assoc] using squared)

/-! ### Source and gate schedule bounds -/

def sourceSpan
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) : Nat :=
  (sourceContextPrefix inputs gateCountUsed gateCountRemaining
      priorGates before ++ sourceCells source).length

private theorem inputSourceFootprint_eq
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (index : Nat) :
    inputReferenceFootprint 0 inputs
        (countCells gateCountUsed gateCountRemaining ++
          markedGateListCells priorGates ++ before ++
          [cell00, cell11])
        index =
      sourceSpan inputs gateCountUsed gateCountRemaining
        priorGates before (.input index) := by
  unfold inputReferenceFootprint sourceSpan sourceContextPrefix
  unfold gateReferenceHeader
  simp only [List.length_append, List.length_cons, List.length_nil,
    countCells, sourceCells]
  omega

private theorem gateSourceFootprint_eq
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (index : Nat) :
    gateReferenceFootprint
        (gateReferenceHeader inputs gateCountUsed gateCountRemaining)
        [] priorGates (before ++ [cell01, cell10]) index =
      sourceSpan inputs gateCountUsed gateCountRemaining
        priorGates before (.gate index) := by
  unfold gateReferenceFootprint sourceSpan sourceContextPrefix
  simp only [borrowedGateListCells,
    List.length_append, List.length_cons, List.length_nil,
    sourceCells]
  omega

theorem sourceRemainderSteps_bound
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) :
    sourceRemainderSteps inputs gateCountUsed gateCountRemaining
        priorGates before source ≤
      1 +
        8 *
          ((sourceSpan inputs gateCountUsed gateCountRemaining
              priorGates before source + 1) *
            (sourceSpan inputs gateCountUsed gateCountRemaining
              priorGates before source + 1)) := by
  cases source with
  | constant value =>
      simp [sourceRemainderSteps]
  | input index =>
      have run :=
        inputReferenceInRangeSteps_square_bound 0 inputs
          (countCells gateCountUsed gateCountRemaining ++
            markedGateListCells priorGates ++ before ++
            [cell00, cell11])
          index
      rw [inputSourceFootprint_eq inputs gateCountUsed
        gateCountRemaining priorGates before index] at run
      simpa [sourceRemainderSteps] using Nat.add_le_add_left run 1
  | gate index =>
      have run :=
        gateReferenceInRangeSteps_square_bound inputs gateCountUsed
          gateCountRemaining [] priorGates
          (before ++ [cell01, cell10]) index
      rw [gateSourceFootprint_eq inputs gateCountUsed
        gateCountRemaining priorGates before index] at run
      simpa [sourceRemainderSteps] using Nat.add_le_add_left run 1

theorem sourceSteps_bound
    (inputs gateCountUsed gateCountRemaining : Nat)
    (priorGates : List RawGate)
    (before : List WorkSymbol)
    (source : RawSource) :
    sourceSteps inputs gateCountUsed gateCountRemaining
        priorGates before source ≤
      2 +
        8 *
          ((sourceSpan inputs gateCountUsed gateCountRemaining
              priorGates before source + 1) *
            (sourceSpan inputs gateCountUsed gateCountRemaining
              priorGates before source + 1)) := by
  unfold sourceSteps
  have run :=
    sourceRemainderSteps_bound inputs gateCountUsed gateCountRemaining
      priorGates before source
  omega

def gateWorkspace
    (inputs : Nat) (done gates : List RawGate) : Nat :=
  (gatePrefix inputs done gates).length +
    (gateListCells gates).length

theorem gateWorkspace_step
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (rest : List RawGate) :
    gateWorkspace inputs done (gate :: rest) =
      gateWorkspace inputs (done ++ [gate]) rest := by
  unfold gateWorkspace
  rw [gatePrefix_snoc]
  unfold gateParsingPrefix gatePrefix
  simp only [List.length_append, List.length_cons, List.length_nil,
    gateListCells, markedGateCells_length,
    markedGateListCells_length, countCells_length, natCells_length]
  omega

private theorem gateLeftSpan_le_workspace
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (rest : List RawGate) :
    sourceSpan inputs (done.length + 1) rest.length done []
        gate.left ≤
      gateWorkspace inputs done (gate :: rest) := by
  unfold sourceSpan sourceContextPrefix gateReferenceHeader
  unfold gateWorkspace gatePrefix
  simp only [List.length_append, List.length_cons, List.length_nil,
    gateListCells, gateCells, countCells_length, natCells_length,
    markedGateListCells_length]
  omega

private theorem gateRightSpan_le_workspace
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (rest : List RawGate) :
    sourceSpan inputs (done.length + 1) rest.length done
        (sourceCells gate.left) gate.right ≤
      gateWorkspace inputs done (gate :: rest) := by
  unfold sourceSpan sourceContextPrefix gateReferenceHeader
  unfold gateWorkspace gatePrefix
  simp only [List.length_append, List.length_cons, List.length_nil,
    gateListCells, gateCells, countCells_length, natCells_length,
    markedGateListCells_length]
  omega

theorem gateSteps_bound
    (inputs : Nat) (done : List RawGate)
    (gate : RawGate) (rest : List RawGate) :
    gateSteps inputs done gate rest ≤
      64 *
        ((gateWorkspace inputs done (gate :: rest) + 1) *
          (gateWorkspace inputs done (gate :: rest) + 1)) := by
  let workspace := gateWorkspace inputs done (gate :: rest)
  let square := (workspace + 1) * (workspace + 1)
  have leftSpan :=
    gateLeftSpan_le_workspace inputs done gate rest
  have rightSpan :=
    gateRightSpan_le_workspace inputs done gate rest
  have leftSucc :
      sourceSpan inputs (done.length + 1) rest.length done []
          gate.left + 1 ≤
        workspace + 1 := by
    omega
  have rightSucc :
      sourceSpan inputs (done.length + 1) rest.length done
          (sourceCells gate.left) gate.right + 1 ≤
        workspace + 1 := by
    omega
  have leftSquare := Nat.mul_le_mul leftSucc leftSucc
  have rightSquare := Nat.mul_le_mul rightSucc rightSucc
  change
    (sourceSpan inputs (done.length + 1) rest.length done []
        gate.left + 1) *
        (sourceSpan inputs (done.length + 1) rest.length done []
          gate.left + 1) ≤ square at leftSquare
  change
    (sourceSpan inputs (done.length + 1) rest.length done
        (sourceCells gate.left) gate.right + 1) *
        (sourceSpan inputs (done.length + 1) rest.length done
          (sourceCells gate.left) gate.right + 1) ≤ square at rightSquare
  have remainderRun :=
    sourceRemainderSteps_bound inputs (done.length + 1) rest.length
      done [] gate.left
  have rightRun :=
    sourceSteps_bound inputs (done.length + 1) rest.length done
      (sourceCells gate.left) gate.right
  have remainderBound :
      sourceRemainderSteps inputs (done.length + 1) rest.length
          done [] gate.left ≤
        1 + 8 * square :=
    Nat.le_trans remainderRun
      (Nat.add_le_add_left (Nat.mul_le_mul_left 8 leftSquare) 1)
  have rightBound :
      sourceSteps inputs (done.length + 1) rest.length done
          (sourceCells gate.left) gate.right ≤
        2 + 8 * square :=
    Nat.le_trans rightRun
      (Nat.add_le_add_left (Nat.mul_le_mul_left 8 rightSquare) 2)
  have oneLe : 1 ≤ square := by
    have positive : 1 ≤ workspace + 1 := by omega
    have product :=
      Nat.mul_le_mul_left (workspace + 1) positive
    exact Nat.le_trans positive (by simpa [square] using product)
  have prefixBound :
      (gatePrefix inputs done (gate :: rest)).length ≤ square := by
    have prefixLe :
        (gatePrefix inputs done (gate :: rest)).length ≤
          workspace := by
      simp [workspace, gateWorkspace]
    have workspaceLe : workspace + 1 ≤ square := by
      have positive : 1 ≤ workspace + 1 := by omega
      simpa [square] using
        Nat.mul_le_mul_left (workspace + 1) positive
    omega
  unfold gateSteps
  change _ ≤ 64 * square
  omega

theorem gatesSteps_bound
    (inputs : Nat) (done gates : List RawGate) :
    gatesSteps inputs done gates ≤
      gates.length *
        (64 *
          ((gateWorkspace inputs done gates + 1) *
            (gateWorkspace inputs done gates + 1))) := by
  induction gates generalizing done with
  | nil =>
      simp [gatesSteps]
  | cons gate rest ih =>
      have head := gateSteps_bound inputs done gate rest
      have tail := ih (done ++ [gate])
      rw [← gateWorkspace_step inputs done gate rest] at tail
      simp only [gatesSteps, List.length_cons]
      calc
        gateSteps inputs done gate rest +
              gatesSteps inputs (done ++ [gate]) rest ≤
            64 *
                ((gateWorkspace inputs done (gate :: rest) + 1) *
                  (gateWorkspace inputs done (gate :: rest) + 1)) +
              rest.length *
                (64 *
                  ((gateWorkspace inputs done (gate :: rest) + 1) *
                    (gateWorkspace inputs done (gate :: rest) + 1))) :=
          Nat.add_le_add head tail
        _ = Nat.succ rest.length *
              (64 *
                ((gateWorkspace inputs done (gate :: rest) + 1) *
                  (gateWorkspace inputs done (gate :: rest) + 1))) := by
          simp [Nat.succ_mul, Nat.add_comm]

/-! ### Explicit polynomial envelope -/

/-- A deliberately conservative cubic work-transition envelope.  The parser
uses at most a constant number of complete sweeps per encoded unary unit. -/
def validWorkBound (bitLength : Nat) : Nat :=
  4096 * (bitLength + 1) * (bitLength + 1) * (bitLength + 1)

/-- Six raw transitions implement each work transition. -/
def validRawBound (bitLength : Nat) : Nat :=
  6 * validWorkBound bitLength

theorem validWorkBound_zero :
    validWorkBound 0 = 4096 := by
  rfl

theorem validRawBound_eq (bitLength : Nat) :
    validRawBound bitLength = 6 * validWorkBound bitLength := by
  rfl

private def cellCube (cells : Nat) : Nat :=
  (cells + 1) * (cells + 1) * (cells + 1)

private theorem one_le_cellCube (cells : Nat) :
    1 ≤ cellCube cells := by
  have one : 1 ≤ cells + 1 := by omega
  have square :
      cells + 1 ≤ (cells + 1) * (cells + 1) := by
    simpa using Nat.mul_le_mul_left (cells + 1) one
  have cube :
      (cells + 1) * (cells + 1) ≤ cellCube cells := by
    simpa [cellCube] using
      Nat.mul_le_mul_left ((cells + 1) * (cells + 1)) one
  exact Nat.le_trans one (Nat.le_trans square cube)

private theorem cell_le_cellCube (cells : Nat) :
    cells ≤ cellCube cells := by
  have cellsLe : cells ≤ cells + 1 := by omega
  have one : 1 ≤ cells + 1 := by omega
  have square :
      cells + 1 ≤ (cells + 1) * (cells + 1) := by
    simpa using Nat.mul_le_mul_left (cells + 1) one
  have cube :
      (cells + 1) * (cells + 1) ≤ cellCube cells := by
    simpa [cellCube] using
      Nat.mul_le_mul_left ((cells + 1) * (cells + 1)) one
  exact Nat.le_trans cellsLe (Nat.le_trans square cube)

private theorem succSquare_le_cellCube (cells : Nat) :
    (cells + 1) * (cells + 1) ≤ cellCube cells := by
  have one : 1 ≤ cells + 1 := by omega
  simpa [cellCube] using
    Nat.mul_le_mul_left ((cells + 1) * (cells + 1)) one

private theorem cellCube_mono
    {left right : Nat} (bound : left ≤ right) :
    cellCube left ≤ cellCube right := by
  have successorBound : left + 1 ≤ right + 1 := by omega
  unfold cellCube
  exact
    Nat.mul_le_mul (Nat.mul_le_mul successorBound successorBound)
      successorBound

private theorem initialGateWorkspace_le (raw : RawCircuit) :
    gateWorkspace raw.inputCount [] raw.gates ≤
      (circuitCells raw).length := by
  simp [gateWorkspace, gatePrefix, circuitCells, countCells,
    markedGateListCells]
  omega

private theorem canonicalGateCount_le (raw : RawCircuit) :
    raw.gates.length ≤ (circuitCells raw).length := by
  simp [circuitCells, natCells_length]
  omega

private theorem canonicalHeaderSteps_le (raw : RawCircuit) :
    2 * raw.inputCount + 2 * raw.gates.length + 8 ≤
      (circuitCells raw).length := by
  simp [circuitCells, natCells_length]
  omega

private theorem programEndSteps_eq
    (inputs : Nat) (gates : List RawGate) :
    programEndSteps inputs gates =
      2 * (gatePrefix inputs gates []).length + 6 := by
  simp [programEndSteps, gatePrefix, countCells_length,
    natCells_length, markedGateListCells_length]
  omega

private theorem canonicalProgramPrefix_le (raw : RawCircuit) :
    (gatePrefix raw.inputCount raw.gates []).length ≤
      (circuitCells raw).length := by
  simp [gatePrefix, circuitCells, countCells_length,
    natCells_length, markedGateListCells_length]

private theorem canonicalOutputSpan_le (raw : RawCircuit) :
    sourceSpan raw.inputCount 0 raw.gates.length raw.gates
        [cell10, cell00] raw.output ≤
      (circuitCells raw).length := by
  simp [sourceSpan, sourceContextPrefix, gateReferenceHeader,
    circuitCells, countCells, markedGateListCells_length]

private theorem finalRestoreSteps_eq (raw : RawCircuit) :
    finalRestoreSteps raw = (circuitCells raw).length + 6 := by
  simp [finalRestoreSteps, markedCircuitCells_length]
  omega

private theorem canonicalGatesSteps_le_cube (raw : RawCircuit) :
    gatesSteps raw.inputCount [] raw.gates ≤
      64 * cellCube (circuitCells raw).length := by
  let cells := (circuitCells raw).length
  let workspace := gateWorkspace raw.inputCount [] raw.gates
  have run := gatesSteps_bound raw.inputCount [] raw.gates
  have countBound : raw.gates.length ≤ cells + 1 := by
    have base := canonicalGateCount_le raw
    omega
  have workspaceBound : workspace + 1 ≤ cells + 1 := by
    have base := initialGateWorkspace_le raw
    omega
  have squareBound :=
    Nat.mul_le_mul workspaceBound workspaceBound
  have productBound :=
    Nat.mul_le_mul countBound squareBound
  have scaled := Nat.mul_le_mul_left 64 productBound
  exact Nat.le_trans run (by
    simpa [cells, workspace, cellCube, Nat.mul_assoc,
      Nat.mul_comm, Nat.mul_left_comm] using scaled)

private theorem canonicalProgramSteps_le_cube (raw : RawCircuit) :
    programEndSteps raw.inputCount raw.gates ≤
      8 * cellCube (circuitCells raw).length := by
  have costEq := programEndSteps_eq raw.inputCount raw.gates
  have prefixBound := canonicalProgramPrefix_le raw
  have cellsBound := cell_le_cellCube (circuitCells raw).length
  have one := one_le_cellCube (circuitCells raw).length
  rw [costEq]
  omega

private theorem canonicalOutputSteps_le_cube (raw : RawCircuit) :
    sourceSteps raw.inputCount 0 raw.gates.length raw.gates
        [cell10, cell00] raw.output ≤
      10 * cellCube (circuitCells raw).length := by
  let cells := (circuitCells raw).length
  let span :=
    sourceSpan raw.inputCount 0 raw.gates.length raw.gates
      [cell10, cell00] raw.output
  have run :=
    sourceSteps_bound raw.inputCount 0 raw.gates.length raw.gates
      [cell10, cell00] raw.output
  have spanBase := canonicalOutputSpan_le raw
  have spanBound : span + 1 ≤ cells + 1 := by omega
  have squareBase := Nat.mul_le_mul spanBound spanBound
  have squareBound :
      (span + 1) * (span + 1) ≤ cellCube cells :=
    Nat.le_trans squareBase (succSquare_le_cellCube cells)
  have one := one_le_cellCube cells
  exact Nat.le_trans run (by
    change
      2 + 8 * ((span + 1) * (span + 1)) ≤
        10 * cellCube cells
    omega)

private theorem canonicalRestoreSteps_le_cube (raw : RawCircuit) :
    finalRestoreSteps raw ≤
      7 * cellCube (circuitCells raw).length := by
  rw [finalRestoreSteps_eq]
  have cellsBound := cell_le_cellCube (circuitCells raw).length
  have one := one_le_cellCube (circuitCells raw).length
  omega

private theorem canonicalSteps_le_cellCube (raw : RawCircuit) :
    canonicalSteps raw ≤
      128 * cellCube (circuitCells raw).length := by
  have headerBase := canonicalHeaderSteps_le raw
  have cellsBound := cell_le_cellCube (circuitCells raw).length
  have headerBound :
      2 * raw.inputCount + 2 * raw.gates.length + 8 ≤
        cellCube (circuitCells raw).length :=
    Nat.le_trans headerBase cellsBound
  have gatesBound := canonicalGatesSteps_le_cube raw
  have programBound := canonicalProgramSteps_le_cube raw
  have outputBound := canonicalOutputSteps_le_cube raw
  have restoreBound := canonicalRestoreSteps_le_cube raw
  unfold canonicalSteps
  omega

/-- The exact canonical schedule fits inside the public cubic work bound.
Malformed source indices only shorten the recursive reference schedules, so
this arithmetic statement does not require a well-formedness premise. -/
theorem canonicalSteps_le_validWorkBound (raw : RawCircuit) :
    canonicalSteps raw ≤
      validWorkBound (encodeCircuit raw).length := by
  let cells := (circuitCells raw).length
  let bits := (encodeCircuit raw).length
  have run := canonicalSteps_le_cellCube raw
  have lengthEq := encodeCircuit_length_eq raw
  have cellsLeBits : cells ≤ bits := by omega
  have cubeBound : cellCube cells ≤ cellCube bits :=
    cellCube_mono cellsLeBits
  have scaled := Nat.mul_le_mul_left 128 cubeBound
  have coefficient :=
    Nat.mul_le_mul_right (cellCube bits)
      (show 128 ≤ 4096 by omega)
  calc
    canonicalSteps raw ≤ 128 * cellCube cells := by
      simpa [cells] using run
    _ ≤ 128 * cellCube bits := scaled
    _ ≤ 4096 * cellCube bits := coefficient
    _ = validWorkBound (encodeCircuit raw).length := by
      simp [bits, cellCube, validWorkBound, Nat.mul_assoc]

/-- A canonical well-formed source has a literal accepting work trace within
the advertised polynomial schedule. -/
theorem wellFormed_exact
    (raw : RawCircuit) (wellFormed : raw.wellFormed = true) :
    ∃ steps,
      steps ≤ validWorkBound (encodeCircuit raw).length ∧
      workRunExact? machine steps
        (workStartConfiguration machine
          (rawInputWorkTape (encodeCircuit raw))) =
        some (validFinalConfiguration raw) := by
  refine
    ⟨canonicalSteps raw, canonicalSteps_le_validWorkBound raw, ?_⟩
  exact canonical_exact raw wellFormed

end PNP.Concrete.LockedNAND.SourceParser
