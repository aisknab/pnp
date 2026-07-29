/-
Copyright (c) 2026 PNP Labs.

Source-driven unary ledger construction for the strict-v0 locked-NAND target
emitter.

The controller-facing layout is deliberately fixed-capacity.  Immediately
beyond the retained source's left boundary lies the zero NatLoop scratch
record, followed by a source-derived blank reserve.  A distinct ledger
boundary then precedes six slots in `UnaryRegisters` order.  Every slot has a
start boundary, a unary payload, a movable separator, and blank remainder.
Consequently later current-gate and output-index increments do not shift any
neighboring record.  A distinct trailing stack boundary follows the sixth
slot, so the next fixed controller can locate its initially blank stack without
inspecting any variable unary payload.

The executable transition table below inspects only the literal nine-symbol
work alphabet and strict-v0 source tags.  In particular, its rules do not call
`decodeCircuit`, `RawCircuit.normalize`, the raw builder, target-byte
functions, or a semantic schedule lookup.
-/

import PNP.Concrete.LockedNANDTargetEmitterGrammarScanner
import PNP.Concrete.LockedNANDTargetEmitterMachine
import PNP.Concrete.PipelineMachineSimulation

namespace PNP.Concrete.LockedNAND.TargetEmitterLedger

open PNP.Concrete

/-! ### Frozen controller-facing ledger layout -/

def cellBlank : WorkSymbol := WorkSymbol.blank
def sourceLeftBoundary : WorkSymbol :=
  TargetEmitter.sourceLeftBoundary
def sourceTargetBoundary : WorkSymbol :=
  TargetEmitter.sourceTargetBoundary
def unaryUnit : WorkSymbol := TargetEmitter.unaryUnit
def unarySeparator : WorkSymbol := TargetEmitter.unarySeparator

/-- Contextual boundary between the NatLoop reserve and fixed ledger slots. -/
def ledgerBoundary : WorkSymbol := WorkSymbol.blankOne

/-- Contextual start delimiter for every fixed-capacity slot. -/
def slotBoundary : WorkSymbol := WorkSymbol.oneOne

/-- Movable end of a slot's unary payload. -/
def slotSeparator : WorkSymbol := unarySeparator

/-- Contextual boundary immediately after the sixth fixed-capacity slot. -/
def stackBoundary : WorkSymbol := WorkSymbol.zeroOne

/-- Temporary far edge used only while reserving a slot. -/
private def activeEnd : WorkSymbol := WorkSymbol.zeroZero

def packed00 : WorkSymbol := WorkSymbol.zeroZero
def packed01 : WorkSymbol := WorkSymbol.zeroOne
def packed10 : WorkSymbol := WorkSymbol.oneZero
def packed11 : WorkSymbol := WorkSymbol.oneOne

def slotCapacity (raw : RawCircuit) : Nat :=
  64 * (SourceParser.circuitCells raw).length + 64

def slotWord (capacity value : Nat) : List WorkSymbol :=
  [slotBoundary] ++
    TargetEmitter.unaryWord value ++
    [slotSeparator] ++
    List.replicate (capacity - value) cellBlank

inductive Slot where
  | inputCount
  | normalizedGateCount
  | carrierWidth
  | baseline
  | currentGate
  | outputIndex
deriving BEq, DecidableEq, Repr

namespace Slot

def all : List Slot :=
  [.inputCount, .normalizedGateCount, .carrierWidth,
    .baseline, .currentGate, .outputIndex]

def index : Slot → Nat
  | .inputCount => 0
  | .normalizedGateCount => 1
  | .carrierWidth => 2
  | .baseline => 3
  | .currentGate => 4
  | .outputIndex => 5

end Slot

def slotValue (registers : TargetEmitter.UnaryRegisters) : Slot → Nat
  | .inputCount => registers.inputCount
  | .normalizedGateCount => registers.normalizedGateCount
  | .carrierWidth => registers.carrierWidth
  | .baseline => registers.baseline
  | .currentGate => registers.currentGate
  | .outputIndex => registers.outputIndex

def slotBank (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  Slot.all.flatMap fun slot =>
    slotWord capacity (slotValue registers slot)

def ledgerWord (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) : List WorkSymbol :=
  ledgerBoundary ::
    (slotBank capacity registers ++ [stackBoundary])

def zeroScratchReserve (capacity : Nat) : List WorkSymbol :=
  [unarySeparator] ++ List.replicate capacity cellBlank

def ledgerLeftWorkspace (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (outsideLeft : List WorkSymbol) : List WorkSymbol :=
  sourceLeftBoundary ::
    (zeroScratchReserve capacity ++
      ledgerWord capacity registers ++ outsideLeft)

theorem slot_all_length : Slot.all.length = 6 := by
  rfl

theorem slotWord_length_of_le
    (capacity value : Nat) (bounded : value ≤ capacity) :
    (slotWord capacity value).length = capacity + 2 := by
  simp [slotWord, TargetEmitter.unaryWord]
  omega

theorem zeroScratchReserve_length (capacity : Nat) :
    (zeroScratchReserve capacity).length = capacity + 1 := by
  simp [zeroScratchReserve]

theorem ledgerWord_has_trailing_stackBoundary
    (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters) :
    ledgerWord capacity registers =
      ledgerBoundary ::
        (slotBank capacity registers ++ [stackBoundary]) := by
  rfl

/-! ### Independent literal source-tag arithmetic -/

/-- Exact source-template weight selected by one literal strict-v0 tag. -/
def sourceMacroWeight : RawSource → Nat
  | .input _ => 10
  | .constant false => 3
  | .constant true => 2
  | .gate _ => 10

def gateMacroWeight (gate : RawGate) : Nat :=
  sourceMacroWeight gate.left + sourceMacroWeight gate.right + 18

def gateListMacroWeight : List RawGate → Nat
  | [] => 0
  | gate :: rest =>
      gateMacroWeight gate + gateListMacroWeight rest

theorem gateListMacroWeight_append
    (initial suffix : List RawGate) :
    gateListMacroWeight (initial ++ suffix) =
      gateListMacroWeight initial + gateListMacroWeight suffix := by
  induction initial with
  | nil => simp [gateListMacroWeight]
  | cons gate rest ih =>
      simp [gateListMacroWeight, ih, Nat.add_assoc]

def normalizationAddedGates : RawSource → Nat
  | .gate _ => 0
  | .input _ => 2
  | .constant _ => 1

def normalizationMacroWeight : RawSource → Nat
  | .gate _ => 0
  | .input _ => 68
  | .constant false => 22
  | .constant true => 24

def normalizedGateCount (raw : RawCircuit) : Nat :=
  raw.gates.length + normalizationAddedGates raw.output

def carrierWidthValue (raw : RawCircuit) : Nat :=
  raw.inputCount + 6 * normalizedGateCount raw + 1

def baselineValue (raw : RawCircuit) : Nat :=
  gateListMacroWeight raw.gates +
    normalizationMacroWeight raw.output +
    2 * (3 * normalizedGateCount raw - 1)

def ledgerRegisters (raw : RawCircuit) :
    TargetEmitter.UnaryRegisters :=
  { inputCount := raw.inputCount
    normalizedGateCount := normalizedGateCount raw
    carrierWidth := carrierWidthValue raw
    baseline := baselineValue raw
    currentGate := 0
    outputIndex := 0 }

theorem sourceMacroWeight_eq_rawBuilder (source : RawSource) :
    sourceMacroWeight source =
      RawBuilder.sourceMacroGateCount source := by
  cases source with
  | input index => rfl
  | gate index => rfl
  | constant value =>
      cases value <;> rfl

theorem gateMacroWeight_eq_rawBuilder (gate : RawGate) :
    gateMacroWeight gate = RawBuilder.gateMacroGateCount gate := by
  cases gate
  simp [gateMacroWeight, RawBuilder.gateMacroGateCount,
    sourceMacroWeight_eq_rawBuilder]

theorem gateListMacroWeight_eq_rawBuilder (gates : List RawGate) :
    gateListMacroWeight gates =
      RawBuilder.gateListMacroGateCount gates := by
  induction gates with
  | nil => rfl
  | cons gate rest ih =>
      simp [gateListMacroWeight, RawBuilder.gateListMacroGateCount,
        gateMacroWeight_eq_rawBuilder, ih]

theorem normalizedGateCount_eq_normalize (raw : RawCircuit) :
    normalizedGateCount raw = raw.normalize.gates.length := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [normalizedGateCount, normalizationAddedGates,
            RawCircuit.normalize]
      | input index =>
          simp [normalizedGateCount, normalizationAddedGates,
            RawCircuit.normalize]
      | constant value =>
          cases value <;>
            simp [normalizedGateCount, normalizationAddedGates,
              RawCircuit.normalize]

theorem gateListMacroWeight_normalize (raw : RawCircuit) :
    gateListMacroWeight raw.normalize.gates =
      gateListMacroWeight raw.gates +
        normalizationMacroWeight raw.output := by
  cases raw with
  | mk inputs gates output =>
      cases output with
      | gate index =>
          simp [RawCircuit.normalize, normalizationMacroWeight]
      | input index =>
          rw [show
            ({ inputCount := inputs, gates := gates,
                output := RawSource.input index } : RawCircuit).normalize.gates =
              gates ++
                [{ left := .input index, right := .constant true },
                 { left := .gate gates.length,
                   right := .gate gates.length }] by rfl]
          rw [gateListMacroWeight_append]
          simp [gateListMacroWeight,
            gateMacroWeight, sourceMacroWeight,
            normalizationMacroWeight]
      | constant value =>
          cases value with
          | false =>
              rw [show
                ({ inputCount := inputs, gates := gates,
                    output := RawSource.constant false } :
                    RawCircuit).normalize.gates =
                  gates ++
                    [{ left := .constant true,
                       right := .constant true }] by rfl]
              rw [gateListMacroWeight_append]
              simp [gateListMacroWeight, gateMacroWeight,
                sourceMacroWeight, normalizationMacroWeight]
          | true =>
              rw [show
                ({ inputCount := inputs, gates := gates,
                    output := RawSource.constant true } :
                    RawCircuit).normalize.gates =
                  gates ++
                    [{ left := .constant false,
                       right := .constant false }] by rfl]
              rw [gateListMacroWeight_append]
              simp [gateListMacroWeight, gateMacroWeight,
                sourceMacroWeight, normalizationMacroWeight]

theorem baselineValue_eq_rawBuilder_formula (raw : RawCircuit) :
    baselineValue raw =
      RawBuilder.gateListMacroGateCount raw.normalize.gates +
        2 * (3 * raw.normalize.gates.length - 1) := by
  rw [← gateListMacroWeight_eq_rawBuilder]
  rw [gateListMacroWeight_normalize]
  rw [← normalizedGateCount_eq_normalize]
  rfl

theorem baselineValue_eq_rawLockedInstance (raw : RawCircuit) :
    baselineValue raw = (RawBuilder.rawLockedInstance raw).baseline := by
  rw [RawBuilder.rawLockedInstance_baseline]
  exact baselineValue_eq_rawBuilder_formula raw

/-! ### Slot shape and logical decoding -/

structure SlotShape (capacity value : Nat)
    (word : List WorkSymbol) : Prop where
  bounded : value ≤ capacity
  exact : word = slotWord capacity value

structure LedgerShape (capacity : Nat)
    (registers : TargetEmitter.UnaryRegisters)
    (word : List WorkSymbol) : Prop where
  inputBound : registers.inputCount ≤ capacity
  normalizedGateBound : registers.normalizedGateCount ≤ capacity
  carrierWidthBound : registers.carrierWidth ≤ capacity
  baselineBound : registers.baseline ≤ capacity
  currentGateBound : registers.currentGate ≤ capacity
  outputIndexBound : registers.outputIndex ≤ capacity
  exact : word = ledgerWord capacity registers

def decodeUnaryPrefix : List WorkSymbol → Nat :=
  fun word => (word.takeWhile (· == unaryUnit)).length

theorem decodeUnaryPrefix_slotWord
    (capacity value : Nat) :
    decodeUnaryPrefix
        (TargetEmitter.unaryWord value ++
          [slotSeparator] ++
          List.replicate (capacity - value) cellBlank) =
      value := by
  have different :
      (WorkSymbol.oneBlank == WorkSymbol.zeroBlank) = false := by
    rfl
  simp [decodeUnaryPrefix, TargetEmitter.unaryWord,
    unaryUnit, unarySeparator, slotSeparator,
    TargetEmitter.unaryUnit, TargetEmitter.unarySeparator,
    different, List.takeWhile]

/-! ### Capacity proofs -/

private theorem sourceMacroWeight_le_ten
    (source : RawSource) :
    sourceMacroWeight source ≤ 10 := by
  cases source with
  | input index => simp [sourceMacroWeight]
  | gate index => simp [sourceMacroWeight]
  | constant value => cases value <;> simp [sourceMacroWeight]

private theorem gateMacroWeight_le_thirtyEight
    (gate : RawGate) :
    gateMacroWeight gate ≤ 38 := by
  cases gate with
  | mk left right =>
      change
        sourceMacroWeight left + sourceMacroWeight right + 18 ≤ 38
      have leftBound := sourceMacroWeight_le_ten left
      have rightBound := sourceMacroWeight_le_ten right
      omega

private theorem gateListMacroWeight_le
    (gates : List RawGate) :
    gateListMacroWeight gates ≤ 38 * gates.length := by
  induction gates with
  | nil => exact Nat.le_refl _
  | cons gate rest ih =>
      simp only [gateListMacroWeight, List.length_cons]
      have gateBound := gateMacroWeight_le_thirtyEight gate
      omega

private theorem normalizationAddedGates_le_two
    (source : RawSource) :
    normalizationAddedGates source ≤ 2 := by
  cases source with
  | input index => simp [normalizationAddedGates]
  | gate index => simp [normalizationAddedGates]
  | constant value =>
      cases value <;> simp [normalizationAddedGates]

private theorem normalizationMacroWeight_le_sixtyEight
    (source : RawSource) :
    normalizationMacroWeight source ≤ 68 := by
  cases source with
  | input index => simp [normalizationMacroWeight]
  | gate index => simp [normalizationMacroWeight]
  | constant value =>
      cases value <;> simp [normalizationMacroWeight]

private theorem sourceCells_length_ge_two
    (source : RawSource) :
    2 ≤ (SourceParser.sourceCells source).length := by
  cases source with
  | input index =>
      simp [SourceParser.sourceCells,
        SourceParser.natCells_length]
  | gate index =>
      simp [SourceParser.sourceCells,
        SourceParser.natCells_length]
  | constant value =>
      cases value <;> decide

private theorem circuitCells_length_ge_fourteen
    (raw : RawCircuit) :
    14 ≤ (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      have outputLength := sourceCells_length_ge_two output
      simp [SourceParser.circuitCells,
        SourceParser.natCells_length]
      omega

private theorem inputCount_le_circuitCells_length
    (raw : RawCircuit) :
    raw.inputCount ≤ (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      simp [SourceParser.circuitCells,
        SourceParser.natCells_length]
      omega

private theorem gateCount_le_circuitCells_length
    (raw : RawCircuit) :
    raw.gates.length ≤
      (SourceParser.circuitCells raw).length := by
  cases raw with
  | mk inputs gates output =>
      simp [SourceParser.circuitCells,
        SourceParser.natCells_length]
      omega

theorem normalizedGateCount_le_slotCapacity
    (raw : RawCircuit) :
    normalizedGateCount raw ≤ slotCapacity raw := by
  have added := normalizationAddedGates_le_two raw.output
  have gates := gateCount_le_circuitCells_length raw
  have cells := circuitCells_length_ge_fourteen raw
  unfold normalizedGateCount slotCapacity
  omega

theorem carrierWidthValue_le_slotCapacity
    (raw : RawCircuit) :
    carrierWidthValue raw ≤ slotCapacity raw := by
  have inputs := inputCount_le_circuitCells_length raw
  have gates := gateCount_le_circuitCells_length raw
  have added := normalizationAddedGates_le_two raw.output
  have cells := circuitCells_length_ge_fourteen raw
  unfold carrierWidthValue normalizedGateCount slotCapacity
  omega

theorem baselineValue_le_slotCapacity
    (raw : RawCircuit) :
    baselineValue raw ≤ slotCapacity raw := by
  have gateWeights := gateListMacroWeight_le raw.gates
  have normalizationWeight :=
    normalizationMacroWeight_le_sixtyEight raw.output
  have added := normalizationAddedGates_le_two raw.output
  have gates := gateCount_le_circuitCells_length raw
  have cells := circuitCells_length_ge_fourteen raw
  unfold baselineValue normalizedGateCount slotCapacity
  omega

theorem inputCount_le_slotCapacity (raw : RawCircuit) :
    raw.inputCount ≤ slotCapacity raw := by
  have inputs := inputCount_le_circuitCells_length raw
  unfold slotCapacity
  omega

theorem ledgerShape (raw : RawCircuit) :
    LedgerShape (slotCapacity raw) (ledgerRegisters raw)
      (ledgerWord (slotCapacity raw) (ledgerRegisters raw)) := by
  refine
    { inputBound := inputCount_le_slotCapacity raw
      normalizedGateBound :=
        normalizedGateCount_le_slotCapacity raw
      carrierWidthBound :=
        carrierWidthValue_le_slotCapacity raw
      baselineBound := baselineValue_le_slotCapacity raw
      currentGateBound := by simp [ledgerRegisters, slotCapacity]
      outputIndexBound := by simp [ledgerRegisters, slotCapacity]
      exact := rfl }

theorem ledgerRegisters_normalizedGateCount
    (raw : RawCircuit) :
    (ledgerRegisters raw).normalizedGateCount =
      raw.normalize.gates.length := by
  exact normalizedGateCount_eq_normalize raw

theorem ledgerRegisters_carrierWidth
    (raw : RawCircuit) :
    (ledgerRegisters raw).carrierWidth =
      (RawBuilder.rawLockedInstance raw).candidate.inputCount := by
  rw [RawBuilder.rawLockedInstance_inputCount]
  rw [← normalizedGateCount_eq_normalize]
  cases raw with
  | mk inputs gates output =>
      cases output with
      | input index =>
          rfl
      | gate index =>
          rfl
      | constant value =>
          cases value <;> rfl

theorem ledgerRegisters_baseline
    (raw : RawCircuit) :
    (ledgerRegisters raw).baseline =
      (RawBuilder.rawLockedInstance raw).baseline := by
  exact baselineValue_eq_rawLockedInstance raw

/-! ### Literal source-driven controller -/

inductive Phase where
  | scratch
  | inputCount
  | normalizedGateCount
  | carrierWidth
  | baseline
  | currentGate
  | outputIndex
deriving BEq, DecidableEq, Repr

namespace Phase

def all : List Phase :=
  [.scratch, .inputCount, .normalizedGateCount, .carrierWidth,
    .baseline, .currentGate, .outputIndex]

def code : Phase → Nat
  | .scratch => 0
  | .inputCount => 1
  | .normalizedGateCount => 2
  | .carrierWidth => 3
  | .baseline => 4
  | .currentGate => 5
  | .outputIndex => 6

def next? : Phase → Option Phase
  | .scratch => some .inputCount
  | .inputCount => some .normalizedGateCount
  | .normalizedGateCount => some .carrierWidth
  | .carrierWidth => some .baseline
  | .baseline => some .currentGate
  | .currentGate => some .outputIndex
  | .outputIndex => none

end Phase

inductive Metric where
  | inputCount
  | normalizedGateCount
  | carrierWidth
  | baseline
deriving BEq, DecidableEq, Repr

namespace Metric

def all : List Metric :=
  [.inputCount, .normalizedGateCount, .carrierWidth, .baseline]

def code : Metric → Nat
  | .inputCount => 0
  | .normalizedGateCount => 1
  | .carrierWidth => 2
  | .baseline => 3

def phase : Metric → Phase
  | .inputCount => .inputCount
  | .normalizedGateCount => .normalizedGateCount
  | .carrierWidth => .carrierWidth
  | .baseline => .baseline

def maxContribution : Metric → Nat
  | .inputCount => 1
  | .normalizedGateCount => 2
  | .carrierWidth => 13
  | .baseline => 80

end Metric

inductive SimplePhase where
  | scratch
  | currentGate
  | outputIndex
deriving BEq, DecidableEq, Repr

namespace SimplePhase

def all : List SimplePhase :=
  [.scratch, .currentGate, .outputIndex]

def code : SimplePhase → Nat
  | .scratch => 0
  | .currentGate => 1
  | .outputIndex => 2

def phase : SimplePhase → Phase
  | .scratch => .scratch
  | .currentGate => .currentGate
  | .outputIndex => .outputIndex

end SimplePhase

inductive SourceContinuation where
  | gateLeft
  | gateRight
  | output
deriving BEq, DecidableEq, Repr

namespace SourceContinuation

def all : List SourceContinuation :=
  [.gateLeft, .gateRight, .output]

def code : SourceContinuation → Nat
  | .gateLeft => 0
  | .gateRight => 1
  | .output => 2

end SourceContinuation

inductive SourceKind where
  | input
  | constantFalse
  | constantTrue
  | gate
deriving BEq, DecidableEq, Repr

private def boolCode : Bool → Nat
  | false => 0
  | true => 1

/-- Finite parser position used while rescanning the retained literal word.
No counter or decoded circuit is stored in control. -/
inductive ParseState where
  | versionFirst
  | versionSecond
  | inputNatFirst
  | inputNatSecond
  | gateNatFirst
  | gateNatSecond
  | gateStart (seenGate : Bool)
  | sourceStart (seenGate : Bool) (continuation : SourceContinuation)
  | sourceAfter00 (seenGate : Bool)
      (continuation : SourceContinuation)
  | sourceAfter01 (seenGate : Bool)
      (continuation : SourceContinuation)
  | sourceNatFirst (seenGate : Bool)
      (continuation : SourceContinuation)
  | sourceNatSecond (seenGate : Bool)
      (continuation : SourceContinuation)
  | gateEndFirst (seenGate : Bool)
  | gateEndSecond (seenGate : Bool)
  | programEndSecond (seenGate : Bool)
  | outputsEndFirst
  | outputsEndSecond
  | instanceEndFirst
  | instanceEndSecond
  | done
deriving BEq, DecidableEq, Repr

namespace ParseState

private def sourceCode
    (seenGate : Bool) (continuation : SourceContinuation) : Nat :=
  2 * continuation.code + boolCode seenGate

def code : ParseState → Nat
  | .versionFirst => 0
  | .versionSecond => 1
  | .inputNatFirst => 2
  | .inputNatSecond => 3
  | .gateNatFirst => 4
  | .gateNatSecond => 5
  | .gateStart false => 6
  | .gateStart true => 7
  | .sourceStart seen continuation =>
      8 + 5 * sourceCode seen continuation
  | .sourceAfter00 seen continuation =>
      9 + 5 * sourceCode seen continuation
  | .sourceAfter01 seen continuation =>
      10 + 5 * sourceCode seen continuation
  | .sourceNatFirst seen continuation =>
      11 + 5 * sourceCode seen continuation
  | .sourceNatSecond seen continuation =>
      12 + 5 * sourceCode seen continuation
  | .gateEndFirst false => 38
  | .gateEndFirst true => 39
  | .gateEndSecond false => 40
  | .gateEndSecond true => 41
  | .programEndSecond false => 42
  | .programEndSecond true => 43
  | .outputsEndFirst => 44
  | .outputsEndSecond => 45
  | .instanceEndFirst => 46
  | .instanceEndSecond => 47
  | .done => 48

private def sourceStates
    (seenGate : Bool) (continuation : SourceContinuation) :
    List ParseState :=
  [.sourceStart seenGate continuation,
   .sourceAfter00 seenGate continuation,
   .sourceAfter01 seenGate continuation,
   .sourceNatFirst seenGate continuation,
   .sourceNatSecond seenGate continuation]

def all : List ParseState :=
  [.versionFirst, .versionSecond,
   .inputNatFirst, .inputNatSecond,
   .gateNatFirst, .gateNatSecond,
   .gateStart false, .gateStart true] ++
  ([false, true].flatMap fun seen =>
    SourceContinuation.all.flatMap (sourceStates seen) ++
      [.gateEndFirst seen, .gateEndSecond seen,
       .programEndSecond seen]) ++
  [.outputsEndFirst, .outputsEndSecond,
   .instanceEndFirst, .instanceEndSecond, .done]

end ParseState

private def afterSource
    (seenGate : Bool) : SourceContinuation → ParseState
  | .gateLeft => .sourceStart seenGate .gateRight
  | .gateRight => .gateEndFirst seenGate
  | .output => .outputsEndFirst

private def headerInputUnitContribution : Metric → Nat
  | .inputCount => 1
  | .carrierWidth => 1
  | .normalizedGateCount => 0
  | .baseline => 0

private def sourceContribution
    (metric : Metric) (continuation : SourceContinuation)
    (seenGate : Bool) (kind : SourceKind) : Nat :=
  match continuation with
  | .output =>
      match metric, kind with
      | .inputCount, _ => 0
      | .normalizedGateCount, .input => 2
      | .normalizedGateCount, .constantFalse => 1
      | .normalizedGateCount, .constantTrue => 1
      | .normalizedGateCount, .gate => 0
      | .carrierWidth, .input => 13
      | .carrierWidth, .constantFalse => 7
      | .carrierWidth, .constantTrue => 7
      | .carrierWidth, .gate => 1
      | .baseline, .input => if seenGate then 80 else 78
      | .baseline, .constantFalse => if seenGate then 28 else 26
      | .baseline, .constantTrue => if seenGate then 30 else 28
      | .baseline, .gate => 0
  | .gateLeft | .gateRight =>
      match metric, kind with
      | .baseline, .input => 10
      | .baseline, .constantFalse => 3
      | .baseline, .constantTrue => 2
      | .baseline, .gate => 10
      | _, _ => 0

private def gateEndContribution
    (metric : Metric) (seenGate : Bool) : Nat :=
  match metric with
  | .inputCount => 0
  | .normalizedGateCount => 1
  | .carrierWidth => 6
  | .baseline => if seenGate then 24 else 22

/-- One literal parser transition and the unary contribution attached to that
cell.  It is a closed finite grammar function used only while materializing
the rule rows. -/
def parseStep (metric : Metric) :
    ParseState → WorkSymbol → Option (ParseState × Nat)
  | .versionFirst, symbol =>
      if symbol == packed00 then some (.versionSecond, 0) else none
  | .versionSecond, symbol =>
      if symbol == packed00 then some (.inputNatFirst, 0) else none
  | .inputNatFirst, symbol =>
      if symbol == packed00 then some (.inputNatSecond, 0) else none
  | .inputNatSecond, symbol =>
      if symbol == packed01 then
        some (.inputNatFirst, headerInputUnitContribution metric)
      else if symbol == packed10 then
        some (.gateNatFirst, 0)
      else none
  | .gateNatFirst, symbol =>
      if symbol == packed00 then some (.gateNatSecond, 0) else none
  | .gateNatSecond, symbol =>
      if symbol == packed01 then some (.gateNatFirst, 0)
      else if symbol == packed10 then some (.gateStart false, 0)
      else none
  | .gateStart seen, symbol =>
      if symbol == packed00 then
        some (.sourceAfter00 seen .gateLeft, 0)
      else if symbol == packed01 then
        some (.sourceAfter01 seen .gateLeft, 0)
      else if symbol == packed10 then
        some (.programEndSecond seen, 0)
      else none
  | .sourceStart seen continuation, symbol =>
      if symbol == packed00 then
        some (.sourceAfter00 seen continuation, 0)
      else if symbol == packed01 then
        some (.sourceAfter01 seen continuation, 0)
      else none
  | .sourceAfter00 seen continuation, symbol =>
      if symbol == packed11 then
        some (.sourceNatFirst seen continuation,
          sourceContribution metric continuation seen .input)
      else none
  | .sourceAfter01 seen continuation, symbol =>
      if symbol == packed00 then
        some (afterSource seen continuation,
          sourceContribution metric continuation seen .constantFalse)
      else if symbol == packed01 then
        some (afterSource seen continuation,
          sourceContribution metric continuation seen .constantTrue)
      else if symbol == packed10 then
        some (.sourceNatFirst seen continuation,
          sourceContribution metric continuation seen .gate)
      else none
  | .sourceNatFirst seen continuation, symbol =>
      if symbol == packed00 then
        some (.sourceNatSecond seen continuation, 0)
      else none
  | .sourceNatSecond seen continuation, symbol =>
      if symbol == packed01 then
        some (.sourceNatFirst seen continuation, 0)
      else if symbol == packed10 then
        some (afterSource seen continuation, 0)
      else none
  | .gateEndFirst seen, symbol =>
      if symbol == packed01 then some (.gateEndSecond seen, 0)
      else none
  | .gateEndSecond seen, symbol =>
      if symbol == packed11 then
        some (.gateStart true, gateEndContribution metric seen)
      else none
  | .programEndSecond seen, symbol =>
      if symbol == packed00 then
        some (.sourceStart seen .output, 0)
      else none
  | .outputsEndFirst, symbol =>
      if symbol == packed10 then some (.outputsEndSecond, 0) else none
  | .outputsEndSecond, symbol =>
      if symbol == packed01 then some (.instanceEndFirst, 0) else none
  | .instanceEndFirst, symbol =>
      if symbol == packed10 then some (.instanceEndSecond, 0) else none
  | .instanceEndSecond, symbol =>
      if symbol == packed11 then some (.done, 0) else none
  | .done, _ => none

/-! ### Finite state namespace -/

namespace State

def accept : Nat := 0
def reject : Nat := 1
def dead : Nat := 2
def boot : Nat := 3
def installBoundary : Nat := 4
def installScratchSeparator : Nat := 5

def simpleScan (phase : SimplePhase) : Nat :=
  100 + phase.code
def simpleSeekBoundary (phase : SimplePhase) : Nat :=
  110 + phase.code
def simpleSeekActive (phase : SimplePhase) : Nat :=
  120 + phase.code
def simpleRestoreCursor (phase : SimplePhase) : Nat :=
  130 + phase.code

def metricBegin (metric : Metric) : Nat :=
  200 + metric.code
def parse (metric : Metric) (position : ParseState) : Nat :=
  1000 + 100 * metric.code + position.code
def metricSeekBoundary (metric : Metric) (value : Nat) : Nat :=
  2000 + 100 * metric.code + value
def encodeScratchSeparator (metric : Metric) (remaining : Nat) : Nat :=
  3000 + 100 * metric.code + remaining
def encodeScratchBlank (metric : Metric) (remaining : Nat) : Nat :=
  4000 + 100 * metric.code + remaining
def metricSeekActive (metric : Metric) : Nat :=
  5000 + metric.code

inductive ExtendPurpose where
  | base (phase : Phase)
  | simpleCell (phase : SimplePhase)
  | metricCell (metric : Metric)
deriving BEq, DecidableEq, Repr

namespace ExtendPurpose

def all : List ExtendPurpose :=
  Phase.all.map .base ++
    SimplePhase.all.map .simpleCell ++
    Metric.all.map .metricCell

def code : ExtendPurpose → Nat
  | .base phase => phase.code
  | .simpleCell phase => 7 + phase.code
  | .metricCell metric => 10 + metric.code

end ExtendPurpose

def extend (purpose : ExtendPurpose) (remaining : Nat) : Nat :=
  6000 + 100 * purpose.code + remaining
def returnAfterExtend (purpose : ExtendPurpose) : Nat :=
  8000 + purpose.code

def returnScratch (metric : Metric) : Nat :=
  8100 + metric.code
def decodeScratch (metric : Metric) (value : Nat) : Nat :=
  9000 + 100 * metric.code + value
def resetScratchUnits (metric : Metric) (value : Nat) : Nat :=
  10000 + 100 * metric.code + value
def resetScratchReturn (metric : Metric) (value : Nat) : Nat :=
  11000 + 100 * metric.code + value
def writeScratchSeparator (metric : Metric) (value : Nat) : Nat :=
  12000 + 100 * metric.code + value
def seekActiveForGrowth (metric : Metric) (value : Nat) : Nat :=
  13000 + 100 * metric.code + value
def seekSlotSeparator (metric : Metric) (value : Nat) : Nat :=
  14000 + 100 * metric.code + value
def growSlotSeparator (metric : Metric) (remaining : Nat) : Nat :=
  15000 + 100 * metric.code + remaining
def growSlotBlank (metric : Metric) (remaining : Nat) : Nat :=
  16000 + 100 * metric.code + remaining
def returnToSource (metric : Metric) : Nat :=
  17000 + metric.code
def restoreMetricCursor (metric : Metric) : Nat :=
  17100 + metric.code
def afterMetricCell (metric : Metric) : Nat :=
  17200 + metric.code
def rewindSource (metric : Metric) : Nat :=
  17300 + metric.code

def finishSource (phase : Phase) : Nat :=
  18000 + phase.code
def finishWorkspace (phase : Phase) : Nat :=
  18100 + phase.code
def prepareScratchSlotBoundary : Nat := 18200
def prepareSlotSeparator (phase : Phase) : Nat :=
  18300 + phase.code
def launchBase (phase : Phase) : Nat :=
  18400 + phase.code
def finalReturnWorkspace : Nat := 18500
def targetBlankOne : Nat := 18600
def targetBlankTwo : Nat := 18601
def targetTurnLeft : Nat := 18602
def targetSeekBoundary : Nat := 18603
def stackOutsideBlank : Nat := 18604

end State

/-! ### Literal action rows -/

structure Action where
  targetState : Nat
  writeSymbol : WorkSymbol
  move : HeadMove

structure StateProgram where
  state : Nat
  action : WorkSymbol → Action

def keepAction (target : Nat) (move : HeadMove)
    (symbol : WorkSymbol) : Action :=
  { targetState := target, writeSymbol := symbol, move := move }

def writeAction (target : Nat) (write : WorkSymbol)
    (move : HeadMove) : Action :=
  { targetState := target, writeSymbol := write, move := move }

def deadAction (symbol : WorkSymbol) : Action :=
  keepAction State.dead .stay symbol

def markerFor? (symbol : WorkSymbol) : Option WorkSymbol :=
  if symbol == packed00 then some WorkSymbol.blankZero
  else if symbol == packed01 then some WorkSymbol.blankOne
  else if symbol == packed10 then some WorkSymbol.zeroBlank
  else if symbol == packed11 then some WorkSymbol.oneBlank
  else none

def originalForMarker? (symbol : WorkSymbol) : Option WorkSymbol :=
  if symbol == WorkSymbol.blankZero then some packed00
  else if symbol == WorkSymbol.blankOne then some packed01
  else if symbol == WorkSymbol.zeroBlank then some packed10
  else if symbol == WorkSymbol.oneBlank then some packed11
  else none

def isPacked (symbol : WorkSymbol) : Bool :=
  symbol == packed00 || symbol == packed01 ||
    symbol == packed10 || symbol == packed11

def isLayoutSymbol (symbol : WorkSymbol) : Bool :=
  symbol == cellBlank || symbol == unaryUnit ||
    symbol == unarySeparator || symbol == ledgerBoundary ||
    symbol == slotBoundary

def phaseEntryState : Phase → Nat
  | .scratch => State.simpleScan .scratch
  | .inputCount => State.metricBegin .inputCount
  | .normalizedGateCount => State.metricBegin .normalizedGateCount
  | .carrierWidth => State.metricBegin .carrierWidth
  | .baseline => State.metricBegin .baseline
  | .currentGate => State.simpleScan .currentGate
  | .outputIndex => State.simpleScan .outputIndex

private def bootAction (symbol : WorkSymbol) : Action :=
  if isPacked symbol then
    keepAction State.installBoundary .left symbol
  else deadAction symbol

private def installBoundaryAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction State.installScratchSeparator
      sourceLeftBoundary .left
  else deadAction symbol

private def installScratchSeparatorAction
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction (State.launchBase .scratch)
      unarySeparator .left
  else deadAction symbol

private def simpleScanAction
    (phase : SimplePhase) (symbol : WorkSymbol) : Action :=
  match markerFor? symbol with
  | some marker =>
      writeAction (State.simpleSeekBoundary phase) marker .left
  | none =>
      if symbol == cellBlank then
        if phase == .outputIndex then
          writeAction State.targetBlankOne sourceTargetBoundary .right
        else
          keepAction (State.finishSource phase.phase) .left symbol
      else deadAction symbol

private def simpleSeekBoundaryAction
    (phase : SimplePhase) (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction (State.simpleSeekActive phase) .left symbol
  else if isPacked symbol then
    keepAction (State.simpleSeekBoundary phase) .left symbol
  else deadAction symbol

private def simpleSeekActiveAction
    (phase : SimplePhase) (symbol : WorkSymbol) : Action :=
  if symbol == activeEnd then
    writeAction
      (State.extend (.simpleCell phase) 63) cellBlank .left
  else if isLayoutSymbol symbol then
    keepAction (State.simpleSeekActive phase) .left symbol
  else deadAction symbol

private def simpleRestoreCursorAction
    (phase : SimplePhase) (symbol : WorkSymbol) : Action :=
  match originalForMarker? symbol with
  | some original =>
      writeAction (State.simpleScan phase) original .right
  | none =>
      if isPacked symbol then
        keepAction (State.simpleRestoreCursor phase) .right symbol
      else deadAction symbol

private def metricBeginAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  match markerFor? symbol with
  | some marker =>
      writeAction (State.rewindSource metric) marker .left
  | none => deadAction symbol

private def parseAction
    (metric : Metric) (position : ParseState)
    (symbol : WorkSymbol) : Action :=
  match originalForMarker? symbol with
  | some original =>
      match parseStep metric position original with
      | some (_next, contribution) =>
          keepAction
            (State.metricSeekBoundary metric contribution)
            .left symbol
      | none => deadAction symbol
  | none =>
      if isPacked symbol then
        match parseStep metric position symbol with
        | some (next, _contribution) =>
            keepAction (State.parse metric next) .right symbol
        | none => deadAction symbol
      else deadAction symbol

private def metricSeekBoundaryAction
    (metric : Metric) (contribution : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction
      (State.seekActiveForGrowth metric contribution)
      .left symbol
  else if isPacked symbol then
    keepAction
      (State.metricSeekBoundary metric contribution)
      .left symbol
  else deadAction symbol

private def encodeScratchSeparatorAction
    (metric : Metric) (remaining : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == unarySeparator then
    if remaining = 0 then
      keepAction (State.metricSeekActive metric) .left symbol
    else
      writeAction
        (State.encodeScratchBlank metric (remaining - 1))
        unaryUnit .left
  else deadAction symbol

private def encodeScratchBlankAction
    (metric : Metric) (remaining : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction
      (State.encodeScratchSeparator metric remaining)
      unarySeparator .stay
  else deadAction symbol

private def metricSeekActiveAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  if symbol == activeEnd then
    writeAction
      (State.extend (.metricCell metric) 63) cellBlank .left
  else if isLayoutSymbol symbol then
    keepAction (State.metricSeekActive metric) .left symbol
  else deadAction symbol

private def extendAction
    (purpose : State.ExtendPurpose) (remaining : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    if remaining = 0 then
      writeAction (State.returnAfterExtend purpose)
        activeEnd .right
    else
      keepAction (State.extend purpose (remaining - 1))
        .left symbol
  else deadAction symbol

private def returnAfterExtendAction
    (purpose : State.ExtendPurpose)
    (symbol : WorkSymbol) : Action :=
  match purpose with
  | .base phase =>
      if symbol == sourceLeftBoundary then
        keepAction (phaseEntryState phase) .right symbol
      else if isLayoutSymbol symbol then
        keepAction (State.returnAfterExtend purpose) .right symbol
      else deadAction symbol
  | .simpleCell phase =>
      if symbol == sourceLeftBoundary then
        keepAction (State.simpleRestoreCursor phase) .right symbol
      else if isLayoutSymbol symbol then
        keepAction (State.returnAfterExtend purpose) .right symbol
      else deadAction symbol
  | .metricCell metric =>
      if symbol == sourceLeftBoundary then
        keepAction (State.restoreMetricCursor metric) .right symbol
      else if isLayoutSymbol symbol then
        keepAction (State.returnAfterExtend purpose) .right symbol
      else deadAction symbol

private def returnScratchAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction (State.returnScratch metric) .right symbol
  else if symbol == unarySeparator then
    keepAction (State.decodeScratch metric 0) .right symbol
  else deadAction symbol

private def decodeScratchAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == unaryUnit then
    if value < 80 then
      keepAction (State.decodeScratch metric (value + 1))
        .right symbol
    else deadAction symbol
  else if symbol == sourceLeftBoundary then
    keepAction (State.resetScratchUnits metric value)
      .left symbol
  else deadAction symbol

private def resetScratchUnitsAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == unaryUnit then
    writeAction (State.resetScratchUnits metric value)
      cellBlank .left
  else if symbol == unarySeparator then
    writeAction (State.resetScratchReturn metric value)
      cellBlank .right
  else deadAction symbol

private def resetScratchReturnAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction (State.resetScratchReturn metric value)
      .right symbol
  else if symbol == sourceLeftBoundary then
    keepAction (State.writeScratchSeparator metric value)
      .left symbol
  else deadAction symbol

private def writeScratchSeparatorAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction (State.seekActiveForGrowth metric value)
      unarySeparator .left
  else deadAction symbol

private def seekActiveForGrowthAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == activeEnd then
    keepAction (State.seekSlotSeparator metric value)
      .right symbol
  else if isLayoutSymbol symbol then
    keepAction (State.seekActiveForGrowth metric value)
      .left symbol
  else deadAction symbol

private def seekSlotSeparatorAction
    (metric : Metric) (value : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == slotSeparator then
    if value = 0 then
      keepAction (State.metricSeekActive metric) .left symbol
    else
      writeAction
        (State.growSlotBlank metric (value - 1))
        unaryUnit .left
  else if symbol == cellBlank then
    keepAction (State.seekSlotSeparator metric value)
      .right symbol
  else deadAction symbol

private def growSlotSeparatorAction
    (metric : Metric) (remaining : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == slotSeparator then
    if remaining = 0 then
      keepAction (State.metricSeekActive metric) .left symbol
    else
      writeAction
        (State.growSlotBlank metric (remaining - 1))
        unaryUnit .left
  else deadAction symbol

private def growSlotBlankAction
    (metric : Metric) (remaining : Nat)
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction
      (State.growSlotSeparator metric remaining)
      slotSeparator .stay
  else deadAction symbol

private def returnToSourceAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction (State.restoreMetricCursor metric) .right symbol
  else if isLayoutSymbol symbol then
    keepAction (State.returnToSource metric) .right symbol
  else deadAction symbol

private def restoreMetricCursorAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  match originalForMarker? symbol with
  | some original =>
      writeAction (State.afterMetricCell metric) original .right
  | none =>
      if isPacked symbol then
        keepAction (State.restoreMetricCursor metric) .right symbol
      else deadAction symbol

private def afterMetricCellAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  match markerFor? symbol with
  | some marker =>
      writeAction (State.rewindSource metric) marker .left
  | none =>
      if symbol == cellBlank then
        keepAction (State.finishSource metric.phase) .left symbol
      else deadAction symbol

private def rewindSourceAction
    (metric : Metric) (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction (State.parse metric .versionFirst) .right symbol
  else if isPacked symbol then
    keepAction (State.rewindSource metric) .left symbol
  else deadAction symbol

private def finishSourceAction
    (phase : Phase) (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction (State.finishWorkspace phase) .left symbol
  else if isPacked symbol then
    keepAction (State.finishSource phase) .left symbol
  else deadAction symbol

private def finishWorkspaceAction
    (phase : Phase) (symbol : WorkSymbol) : Action :=
  if symbol == activeEnd then
    match phase.next? with
    | none =>
        writeAction State.stackOutsideBlank stackBoundary .left
    | some next =>
        if phase == .scratch then
          writeAction State.prepareScratchSlotBoundary
            ledgerBoundary .left
        else
          writeAction (State.prepareSlotSeparator next)
            slotBoundary .left
  else if isLayoutSymbol symbol then
    keepAction (State.finishWorkspace phase) .left symbol
  else deadAction symbol

private def prepareScratchSlotBoundaryAction
    (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction
      (State.prepareSlotSeparator .inputCount)
      slotBoundary .left
  else deadAction symbol

private def prepareSlotSeparatorAction
    (phase : Phase) (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    writeAction (State.launchBase phase)
      slotSeparator .left
  else deadAction symbol

private def launchBaseAction
    (phase : Phase) (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction (State.extend (.base phase) 63) .left symbol
  else deadAction symbol

private def finalReturnWorkspaceAction
    (symbol : WorkSymbol) : Action :=
  if symbol == sourceLeftBoundary then
    keepAction State.accept .right symbol
  else if isLayoutSymbol symbol || symbol == stackBoundary then
    keepAction State.finalReturnWorkspace .right symbol
  else deadAction symbol

private def stackOutsideBlankAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction State.finalReturnWorkspace .right symbol
  else deadAction symbol

private def targetBlankOneAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction State.targetBlankTwo .right symbol
  else deadAction symbol

private def targetBlankTwoAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction State.targetTurnLeft .right symbol
  else deadAction symbol

private def targetTurnLeftAction (symbol : WorkSymbol) : Action :=
  if symbol == cellBlank then
    keepAction State.targetSeekBoundary .left symbol
  else deadAction symbol

private def targetSeekBoundaryAction (symbol : WorkSymbol) : Action :=
  if symbol == sourceTargetBoundary then
    keepAction (State.finishSource .outputIndex) .left symbol
  else if symbol == cellBlank then
    keepAction State.targetSeekBoundary .left symbol
  else deadAction symbol

private def fixedPrograms : List StateProgram :=
  [ { state := State.boot, action := bootAction }
  , { state := State.installBoundary,
      action := installBoundaryAction }
  , { state := State.installScratchSeparator,
      action := installScratchSeparatorAction }
  , { state := State.prepareScratchSlotBoundary,
      action := prepareScratchSlotBoundaryAction }
  , { state := State.finalReturnWorkspace,
      action := finalReturnWorkspaceAction }
  , { state := State.targetBlankOne,
      action := targetBlankOneAction }
  , { state := State.targetBlankTwo,
      action := targetBlankTwoAction }
  , { state := State.targetTurnLeft,
      action := targetTurnLeftAction }
  , { state := State.targetSeekBoundary,
      action := targetSeekBoundaryAction }
  , { state := State.stackOutsideBlank,
      action := stackOutsideBlankAction } ]

private def simplePrograms (phase : SimplePhase) :
    List StateProgram :=
  [ { state := State.simpleScan phase,
      action := simpleScanAction phase }
  , { state := State.simpleSeekBoundary phase,
      action := simpleSeekBoundaryAction phase }
  , { state := State.simpleSeekActive phase,
      action := simpleSeekActiveAction phase }
  , { state := State.simpleRestoreCursor phase,
      action := simpleRestoreCursorAction phase } ]

private def metricFixedPrograms (metric : Metric) :
    List StateProgram :=
  [ { state := State.metricBegin metric,
      action := metricBeginAction metric }
  , { state := State.metricSeekActive metric,
      action := metricSeekActiveAction metric }
  , { state := State.returnScratch metric,
      action := returnScratchAction metric }
  , { state := State.returnToSource metric,
      action := returnToSourceAction metric }
  , { state := State.restoreMetricCursor metric,
      action := restoreMetricCursorAction metric }
  , { state := State.afterMetricCell metric,
      action := afterMetricCellAction metric }
  , { state := State.rewindSource metric,
      action := rewindSourceAction metric } ]

private def parsePrograms
    (metric : Metric) : List StateProgram :=
  ParseState.all.map fun position =>
    { state := State.parse metric position
      action := parseAction metric position }

private def boundedMetricPrograms
    (metric : Metric) (value : Nat) : List StateProgram :=
  [ { state := State.metricSeekBoundary metric value,
      action := metricSeekBoundaryAction metric value }
  , { state := State.encodeScratchSeparator metric value,
      action := encodeScratchSeparatorAction metric value }
  , { state := State.encodeScratchBlank metric value,
      action := encodeScratchBlankAction metric value }
  , { state := State.decodeScratch metric value,
      action := decodeScratchAction metric value }
  , { state := State.resetScratchUnits metric value,
      action := resetScratchUnitsAction metric value }
  , { state := State.resetScratchReturn metric value,
      action := resetScratchReturnAction metric value }
  , { state := State.writeScratchSeparator metric value,
      action := writeScratchSeparatorAction metric value }
  , { state := State.seekActiveForGrowth metric value,
      action := seekActiveForGrowthAction metric value }
  , { state := State.seekSlotSeparator metric value,
      action := seekSlotSeparatorAction metric value }
  , { state := State.growSlotSeparator metric value,
      action := growSlotSeparatorAction metric value }
  , { state := State.growSlotBlank metric value,
      action := growSlotBlankAction metric value } ]

private def metricPrograms (metric : Metric) :
    List StateProgram :=
  metricFixedPrograms metric ++
    parsePrograms metric ++
    (List.range (metric.maxContribution + 1)).flatMap
      (boundedMetricPrograms metric)

private def extendPrograms
    (purpose : State.ExtendPurpose) : List StateProgram :=
  (List.range 64).map fun remaining =>
    { state := State.extend purpose remaining
      action := extendAction purpose remaining }

private def returnPrograms
    (purpose : State.ExtendPurpose) : List StateProgram :=
  [{ state := State.returnAfterExtend purpose,
     action := returnAfterExtendAction purpose }]

private def phasePrograms (phase : Phase) :
    List StateProgram :=
  [ { state := State.finishSource phase,
      action := finishSourceAction phase }
  , { state := State.finishWorkspace phase,
      action := finishWorkspaceAction phase }
  , { state := State.prepareSlotSeparator phase,
      action := prepareSlotSeparatorAction phase }
  , { state := State.launchBase phase,
      action := launchBaseAction phase } ]

private def sortedParseStates : List ParseState :=
  [.versionFirst, .versionSecond,
   .inputNatFirst, .inputNatSecond,
   .gateNatFirst, .gateNatSecond,
   .gateStart false, .gateStart true] ++
  (SourceContinuation.all.flatMap fun continuation =>
    [false, true].flatMap fun seen =>
      ParseState.sourceStates seen continuation) ++
  [.gateEndFirst false, .gateEndFirst true,
   .gateEndSecond false, .gateEndSecond true,
   .programEndSecond false, .programEndSecond true] ++
  [.outputsEndFirst, .outputsEndSecond,
   .instanceEndFirst, .instanceEndSecond, .done]

private def simpleBandPrograms
    (stateOf : SimplePhase → Nat)
    (actionOf : SimplePhase → WorkSymbol → Action) :
    List StateProgram :=
  SimplePhase.all.map fun phase =>
    { state := stateOf phase, action := actionOf phase }

private def metricBandPrograms
    (stateOf : Metric → Nat)
    (actionOf : Metric → WorkSymbol → Action) :
    List StateProgram :=
  Metric.all.map fun metric =>
    { state := stateOf metric, action := actionOf metric }

private def boundedMetricBandPrograms
    (stateOf : Metric → Nat → Nat)
    (actionOf : Metric → Nat → WorkSymbol → Action) :
    List StateProgram :=
  Metric.all.flatMap fun metric =>
    (List.range (metric.maxContribution + 1)).map fun value =>
      { state := stateOf metric value
        action := actionOf metric value }

private def phaseBandPrograms
    (stateOf : Phase → Nat)
    (actionOf : Phase → WorkSymbol → Action) :
    List StateProgram :=
  Phase.all.map fun phase =>
    { state := stateOf phase, action := actionOf phase }

private def lowPrograms : List StateProgram :=
  [ { state := State.boot, action := bootAction }
  , { state := State.installBoundary,
      action := installBoundaryAction }
  , { state := State.installScratchSeparator,
      action := installScratchSeparatorAction } ]

private def parseBandPrograms : List StateProgram :=
  Metric.all.flatMap fun metric =>
    sortedParseStates.map fun position =>
      { state := State.parse metric position
        action := parseAction metric position }

private def highPrograms : List StateProgram :=
  [ { state := State.finalReturnWorkspace,
      action := finalReturnWorkspaceAction }
  , { state := State.targetBlankOne,
      action := targetBlankOneAction }
  , { state := State.targetBlankTwo,
      action := targetBlankTwoAction }
  , { state := State.targetTurnLeft,
      action := targetTurnLeftAction }
  , { state := State.targetSeekBoundary,
      action := targetSeekBoundaryAction }
  , { state := State.stackOutsideBlank,
      action := stackOutsideBlankAction } ]

/-- The explicit numeric state bands, in their exact materialization order. -/
private def stateProgramBands : List (List StateProgram) :=
  [ lowPrograms
  , simpleBandPrograms State.simpleScan simpleScanAction
  , simpleBandPrograms State.simpleSeekBoundary
      simpleSeekBoundaryAction
  , simpleBandPrograms State.simpleSeekActive simpleSeekActiveAction
  , simpleBandPrograms State.simpleRestoreCursor
      simpleRestoreCursorAction
  , metricBandPrograms State.metricBegin metricBeginAction
  , parseBandPrograms
  , boundedMetricBandPrograms State.metricSeekBoundary
      metricSeekBoundaryAction
  , boundedMetricBandPrograms State.encodeScratchSeparator
      encodeScratchSeparatorAction
  , boundedMetricBandPrograms State.encodeScratchBlank
      encodeScratchBlankAction
  , metricBandPrograms State.metricSeekActive metricSeekActiveAction
  , State.ExtendPurpose.all.flatMap extendPrograms
  , State.ExtendPurpose.all.flatMap returnPrograms
  , metricBandPrograms State.returnScratch returnScratchAction
  , boundedMetricBandPrograms State.decodeScratch decodeScratchAction
  , boundedMetricBandPrograms State.resetScratchUnits
      resetScratchUnitsAction
  , boundedMetricBandPrograms State.resetScratchReturn
      resetScratchReturnAction
  , boundedMetricBandPrograms State.writeScratchSeparator
      writeScratchSeparatorAction
  , boundedMetricBandPrograms State.seekActiveForGrowth
      seekActiveForGrowthAction
  , boundedMetricBandPrograms State.seekSlotSeparator
      seekSlotSeparatorAction
  , boundedMetricBandPrograms State.growSlotSeparator
      growSlotSeparatorAction
  , boundedMetricBandPrograms State.growSlotBlank growSlotBlankAction
  , metricBandPrograms State.returnToSource returnToSourceAction
  , metricBandPrograms State.restoreMetricCursor
      restoreMetricCursorAction
  , metricBandPrograms State.afterMetricCell afterMetricCellAction
  , metricBandPrograms State.rewindSource rewindSourceAction
  , phaseBandPrograms State.finishSource finishSourceAction
  , phaseBandPrograms State.finishWorkspace finishWorkspaceAction
  , [ { state := State.prepareScratchSlotBoundary,
        action := prepareScratchSlotBoundaryAction } ]
  , phaseBandPrograms State.prepareSlotSeparator
      prepareSlotSeparatorAction
  , phaseBandPrograms State.launchBase launchBaseAction
  , highPrograms ]

/-- Closed finite program in strictly increasing numeric state order.  Every
comprehension ranges over an explicitly bounded list; `raw` never appears in
this definition.  The explicit bands avoid an opaque sorting pass and make the
kernel-checked adjacent-state certificate linear in the number of rows. -/
def statePrograms : List StateProgram :=
  stateProgramBands.flatMap id

def allWorkSymbols : List WorkSymbol :=
  TargetEmitter.allWorkSymbols

def stateRules (program : StateProgram) : List WorkRule :=
  allWorkSymbols.map fun symbol =>
    let action := program.action symbol
    { sourceState := program.state
      readSymbol := symbol
      targetState := action.targetState
      writeSymbol := action.writeSymbol
      move := action.move }

def rules : List WorkRule :=
  statePrograms.flatMap stateRules

def machine : WorkMachine :=
  { rules := rules
    startState := State.boot
    acceptState := State.accept
    rejectState := State.reject }

def compiledMachine : Machine :=
  compileWorkMachine machine

def QueryDistinct (left right : WorkRule) : Prop :=
  (left.sourceState, left.readSymbol) ≠
    (right.sourceState, right.readSymbol)

theorem allWorkSymbols_length :
    allWorkSymbols.length = 9 := by
  rfl

theorem stateRules_length (program : StateProgram) :
    (stateRules program).length = 9 := by
  rfl

set_option maxRecDepth 1000000 in
theorem statePrograms_length :
    statePrograms.length = 2284 := by
  rfl

def ruleCount : Nat := 20556

set_option maxRecDepth 1000000 in
theorem rules_length :
    rules.length = ruleCount := by
  have materializedLength :
      ∀ programs : List StateProgram,
        (programs.flatMap stateRules).length =
          9 * programs.length := by
    intro programs
    induction programs with
    | nil => rfl
    | cons first rest ih =>
        simp only [List.flatMap_cons, List.length_append,
          stateRules_length, ih, List.length_cons, Nat.mul_succ]
        omega
  unfold rules ruleCount
  rw [materializedLength, statePrograms_length]

/-! ### Structural rule-table distinctness -/

private def adjacentStateIncreasing :
    List StateProgram → Bool
  | [] => true
  | [_single] => true
  | first :: second :: rest =>
      decide (first.state < second.state) &&
        adjacentStateIncreasing (second :: rest)

private theorem adjacent_head_lt :
    ∀ {first : StateProgram} {rest : List StateProgram},
      adjacentStateIncreasing (first :: rest) = true →
      ∀ program, program ∈ rest →
        first.state < program.state
  | first, [], _ => by
      intro program member
      contradiction
  | first, second :: rest, increasing => by
      intro program member
      have parts :
          decide (first.state < second.state) = true ∧
            adjacentStateIncreasing (second :: rest) = true := by
        simpa only [adjacentStateIncreasing, Bool.and_eq_true]
          using increasing
      have firstSecond : first.state < second.state :=
        of_decide_eq_true parts.1
      have tailIncreasing :
          adjacentStateIncreasing (second :: rest) = true :=
        parts.2
      rcases List.mem_cons.mp member with equal | tailMember
      · subst program
        exact firstSecond
      · exact Nat.lt_trans firstSecond
          (adjacent_head_lt tailIncreasing program tailMember)

private theorem pairwise_lt_of_adjacent :
    ∀ programs : List StateProgram,
      adjacentStateIncreasing programs = true →
      programs.Pairwise
        (fun left right => left.state < right.state)
  | [], _ => List.Pairwise.nil
  | first :: rest, increasing => by
      refine List.Pairwise.cons ?_ ?_
      · exact adjacent_head_lt increasing
      · cases rest with
        | nil =>
            exact List.Pairwise.nil
        | cons second tail =>
            have parts :
                decide (first.state < second.state) = true ∧
                  adjacentStateIncreasing (second :: tail) = true := by
              simpa only [adjacentStateIncreasing, Bool.and_eq_true]
                using increasing
            exact pairwise_lt_of_adjacent
              (second :: tail) parts.2

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
private theorem statePrograms_adjacent_increasing :
    adjacentStateIncreasing statePrograms = true := by
  rfl

private theorem statePrograms_pairwise_state_distinct :
    statePrograms.Pairwise
      (fun left right => left.state ≠ right.state) := by
  have increasing :=
    pairwise_lt_of_adjacent statePrograms
      statePrograms_adjacent_increasing
  exact increasing.imp (by
    intro left right less equal
    exact (Nat.ne_of_lt less) equal)

private theorem stateRules_source_eq
    {program : StateProgram} {rule : WorkRule}
    (member : rule ∈ stateRules program) :
    rule.sourceState = program.state := by
  rcases List.mem_map.mp member with
    ⟨symbol, _symbolMember, ruleEq⟩
  rw [← ruleEq]

private theorem stateRules_pairwise
    (program : StateProgram) :
    (stateRules program).Pairwise QueryDistinct := by
  unfold stateRules allWorkSymbols TargetEmitter.allWorkSymbols
  simp [QueryDistinct,
    WorkSymbol.blank, WorkSymbol.blankZero, WorkSymbol.blankOne,
    WorkSymbol.zeroBlank, WorkSymbol.zeroZero, WorkSymbol.zeroOne,
    WorkSymbol.oneBlank, WorkSymbol.oneZero, WorkSymbol.oneOne]

private theorem materializedPrograms_pairwise
    (programs : List StateProgram)
    (distinct :
      programs.Pairwise (fun left right =>
        left.state ≠ right.state)) :
    (programs.flatMap stateRules).Pairwise QueryDistinct := by
  induction programs with
  | nil =>
      exact List.Pairwise.nil
  | cons program rest ih =>
      cases distinct with
      | cons headDistinct tailDistinct =>
          change
            (stateRules program ++
              rest.flatMap stateRules).Pairwise QueryDistinct
          rw [List.pairwise_append]
          refine
            ⟨stateRules_pairwise program,
             ih tailDistinct, ?_⟩
          intro left leftMember right rightMember queryEq
          rcases List.mem_flatMap.mp rightMember with
            ⟨rightProgram, rightProgramMember,
             rightRuleMember⟩
          have sourceNe :=
            headDistinct rightProgram rightProgramMember
          have leftSource := stateRules_source_eq leftMember
          have rightSource := stateRules_source_eq rightRuleMember
          exact sourceNe
            (leftSource.symm.trans
              ((congrArg Prod.fst queryEq).trans rightSource))

theorem rules_pairwise_query_distinct :
    rules.Pairwise QueryDistinct :=
  materializedPrograms_pairwise statePrograms
    statePrograms_pairwise_state_distinct

theorem machine_start_ne_accept :
    machine.startState ≠ machine.acceptState := by
  decide

theorem machine_start_ne_reject :
    machine.startState ≠ machine.rejectState := by
  decide

theorem machine_accept_ne_reject :
    machine.acceptState ≠ machine.rejectState := by
  decide

private def statesAtLeastThree :
    List StateProgram → Bool
  | [] => true
  | program :: rest =>
      decide (3 ≤ program.state) && statesAtLeastThree rest

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem statePrograms_at_least_three :
    statesAtLeastThree statePrograms = true := by
  rfl

private theorem state_ge_three_of_mem
    (programs : List StateProgram)
    (bounded : statesAtLeastThree programs = true)
    (program : StateProgram) (member : program ∈ programs) :
    3 ≤ program.state := by
  induction programs with
  | nil =>
      contradiction
  | cons first rest ih =>
      have parts :
          decide (3 ≤ first.state) = true ∧
            statesAtLeastThree rest = true := by
        simpa only [statesAtLeastThree, Bool.and_eq_true]
          using bounded
      rcases List.mem_cons.mp member with equal | tailMember
      · subst program
        exact of_decide_eq_true parts.1
      · exact ih parts.2 tailMember

private theorem rule_source_ge_three
    {rule : WorkRule} (member : rule ∈ rules) :
    3 ≤ rule.sourceState := by
  rcases List.mem_flatMap.mp member with
    ⟨program, programMember, ruleMember⟩
  rw [stateRules_source_eq ruleMember]
  exact state_ge_three_of_mem statePrograms
    statePrograms_at_least_three program programMember

private theorem findWorkRule_none_of_source_lt_three
    (localRules : List WorkRule)
    (bounded :
      ∀ rule, rule ∈ localRules → 3 ≤ rule.sourceState)
    (state : Nat) (stateSmall : state < 3)
    (symbol : WorkSymbol) :
    findWorkRule localRules state symbol = none := by
  induction localRules with
  | nil =>
      rfl
  | cons first rest ih =>
      have firstMember : first ∈ first :: rest :=
        List.mem_cons_self
      have firstBound := bounded first firstMember
      rw [findWorkRule_cons_of_not_matches]
      · exact ih (by
          intro rule member
          exact bounded rule (List.mem_cons_of_mem first member))
      · omega

theorem no_rule_at_accept (symbol : WorkSymbol) :
    findWorkRule rules State.accept symbol = none :=
  findWorkRule_none_of_source_lt_three rules
    (fun rule member => rule_source_ge_three member)
    State.accept (by decide) symbol

theorem no_rule_at_reject (symbol : WorkSymbol) :
    findWorkRule rules State.reject symbol = none :=
  findWorkRule_none_of_source_lt_three rules
    (fun rule member => rule_source_ge_three member)
    State.reject (by decide) symbol

theorem no_rule_at_dead (symbol : WorkSymbol) :
    findWorkRule rules State.dead symbol = none :=
  findWorkRule_none_of_source_lt_three rules
    (fun rule member => rule_source_ge_three member)
    State.dead (by decide) symbol

theorem acceptConfiguration_halted (tape : WorkTape) :
    machine.isHalted { state := State.accept, tape := tape } = true := by
  rfl

theorem deadConfiguration_not_halted (tape : WorkTape) :
    machine.isHalted { state := State.dead, tape := tape } = false := by
  rfl

/-! ### Structural transition interface -/

private def literalRule (source : Nat) (read : WorkSymbol)
    (target : Nat) (write : WorkSymbol) (move : HeadMove) :
    WorkRule :=
  { sourceState := source
    readSymbol := read
    targetState := target
    writeSymbol := write
    move := move }

private theorem allWorkSymbols_complete (symbol : WorkSymbol) :
    symbol ∈ allWorkSymbols := by
  cases symbol with
  | mk first second =>
      cases first <;> cases second <;>
        simp [allWorkSymbols, TargetEmitter.allWorkSymbols,
          WorkSymbol.blank, WorkSymbol.blankZero,
          WorkSymbol.blankOne, WorkSymbol.zeroBlank,
          WorkSymbol.zeroZero, WorkSymbol.zeroOne,
          WorkSymbol.oneBlank, WorkSymbol.oneZero,
          WorkSymbol.oneOne]

private theorem simplePhase_mem_all (phase : SimplePhase) :
    phase ∈ SimplePhase.all := by
  cases phase <;> simp [SimplePhase.all]

private theorem metric_mem_all (metric : Metric) :
    metric ∈ Metric.all := by
  cases metric <;> simp [Metric.all]

private theorem phase_mem_all (phase : Phase) :
    phase ∈ Phase.all := by
  cases phase <;> simp [Phase.all]

private theorem extendPurpose_mem_all
    (purpose : State.ExtendPurpose) :
    purpose ∈ State.ExtendPurpose.all := by
  cases purpose with
  | base phase =>
      cases phase <;>
        simp [State.ExtendPurpose.all, Phase.all,
          SimplePhase.all, Metric.all]
  | simpleCell phase =>
      cases phase <;>
        simp [State.ExtendPurpose.all, Phase.all,
          SimplePhase.all, Metric.all]
  | metricCell metric =>
      cases metric <;>
        simp [State.ExtendPurpose.all, Phase.all,
          SimplePhase.all, Metric.all]

private theorem parseState_mem_sorted (position : ParseState) :
    position ∈ sortedParseStates := by
  cases position with
  | versionFirst | versionSecond | inputNatFirst | inputNatSecond |
      gateNatFirst | gateNatSecond | outputsEndFirst |
      outputsEndSecond | instanceEndFirst | instanceEndSecond | done =>
      simp [sortedParseStates]
  | gateStart seen =>
      cases seen <;> simp [sortedParseStates]
  | gateEndFirst seen =>
      cases seen <;> simp [sortedParseStates]
  | gateEndSecond seen =>
      cases seen <;> simp [sortedParseStates]
  | programEndSecond seen =>
      cases seen <;> simp [sortedParseStates]
  | sourceStart seen continuation =>
      cases seen <;> cases continuation <;>
        simp [sortedParseStates, SourceContinuation.all,
          ParseState.sourceStates]
  | sourceAfter00 seen continuation =>
      cases seen <;> cases continuation <;>
        simp [sortedParseStates, SourceContinuation.all,
          ParseState.sourceStates]
  | sourceAfter01 seen continuation =>
      cases seen <;> cases continuation <;>
        simp [sortedParseStates, SourceContinuation.all,
          ParseState.sourceStates]
  | sourceNatFirst seen continuation =>
      cases seen <;> cases continuation <;>
        simp [sortedParseStates, SourceContinuation.all,
          ParseState.sourceStates]
  | sourceNatSecond seen continuation =>
      cases seen <;> cases continuation <;>
        simp [sortedParseStates, SourceContinuation.all,
          ParseState.sourceStates]

private theorem program_mem_of_band
    {band : List StateProgram} {program : StateProgram}
    (bandMember : band ∈ stateProgramBands)
    (programMember : program ∈ band) :
    program ∈ statePrograms := by
  unfold statePrograms
  exact List.mem_flatMap.mpr
    ⟨band, bandMember, by simpa using programMember⟩

private theorem simpleBand_program_mem
    (stateOf : SimplePhase → Nat)
    (actionOf : SimplePhase → WorkSymbol → Action)
    (bandMember :
      simpleBandPrograms stateOf actionOf ∈ stateProgramBands)
    (phase : SimplePhase) :
    ({ state := stateOf phase, action := actionOf phase } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band bandMember
  exact List.mem_map.mpr
    ⟨phase, simplePhase_mem_all phase, rfl⟩

private theorem metricBand_program_mem
    (stateOf : Metric → Nat)
    (actionOf : Metric → WorkSymbol → Action)
    (bandMember :
      metricBandPrograms stateOf actionOf ∈ stateProgramBands)
    (metric : Metric) :
    ({ state := stateOf metric, action := actionOf metric } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band bandMember
  exact List.mem_map.mpr
    ⟨metric, metric_mem_all metric, rfl⟩

private theorem boundedMetricBand_program_mem
    (stateOf : Metric → Nat → Nat)
    (actionOf : Metric → Nat → WorkSymbol → Action)
    (bandMember :
      boundedMetricBandPrograms stateOf actionOf ∈
        stateProgramBands)
    (metric : Metric) (value : Nat)
    (bounded : value ≤ metric.maxContribution) :
    ({ state := stateOf metric value
       action := actionOf metric value } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band bandMember
  apply List.mem_flatMap.mpr
  refine ⟨metric, metric_mem_all metric, ?_⟩
  apply List.mem_map.mpr
  refine ⟨value, List.mem_range.mpr ?_, rfl⟩
  omega

private theorem phaseBand_program_mem
    (stateOf : Phase → Nat)
    (actionOf : Phase → WorkSymbol → Action)
    (bandMember :
      phaseBandPrograms stateOf actionOf ∈ stateProgramBands)
    (phase : Phase) :
    ({ state := stateOf phase, action := actionOf phase } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band bandMember
  exact List.mem_map.mpr
    ⟨phase, phase_mem_all phase, rfl⟩

private theorem parse_program_mem
    (metric : Metric) (position : ParseState) :
    ({ state := State.parse metric position
       action := parseAction metric position } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band
    (show parseBandPrograms ∈ stateProgramBands by
      simp [stateProgramBands])
  apply List.mem_flatMap.mpr
  refine ⟨metric, metric_mem_all metric, ?_⟩
  exact List.mem_map.mpr
    ⟨position, parseState_mem_sorted position, rfl⟩

private theorem extend_program_mem
    (purpose : State.ExtendPurpose) (remaining : Nat)
    (bounded : remaining < 64) :
    ({ state := State.extend purpose remaining
       action := extendAction purpose remaining } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band
    (show State.ExtendPurpose.all.flatMap extendPrograms ∈
        stateProgramBands by
      simp [stateProgramBands])
  apply List.mem_flatMap.mpr
  refine ⟨purpose, extendPurpose_mem_all purpose, ?_⟩
  exact List.mem_map.mpr
    ⟨remaining, List.mem_range.mpr bounded, rfl⟩

private theorem return_program_mem
    (purpose : State.ExtendPurpose) :
    ({ state := State.returnAfterExtend purpose
       action := returnAfterExtendAction purpose } :
      StateProgram) ∈ statePrograms := by
  apply program_mem_of_band
    (show State.ExtendPurpose.all.flatMap returnPrograms ∈
        stateProgramBands by
      simp [stateProgramBands])
  apply List.mem_flatMap.mpr
  refine ⟨purpose, extendPurpose_mem_all purpose, ?_⟩
  simp [returnPrograms]

private theorem findWorkRule_eq_some_of_mem
    {localRules : List WorkRule} {selected : WorkRule}
    (pairwise : localRules.Pairwise QueryDistinct)
    (member : selected ∈ localRules) :
    findWorkRule localRules selected.sourceState
      selected.readSymbol = some selected := by
  induction localRules with
  | nil =>
      contradiction
  | cons first rest ih =>
      cases pairwise with
      | cons headDistinct tailDistinct =>
          rcases List.mem_cons.mp member with equal | tailMember
          · subst selected
            exact findWorkRule_cons_of_matches
              first rest first.sourceState first.readSymbol
              ⟨rfl, rfl⟩
          · rw [findWorkRule_cons_of_not_matches]
            · exact ih tailDistinct tailMember
            · simp_all [QueryDistinct]

private theorem materializedRule_mem
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) :
    let action := program.action symbol
    literalRule program.state symbol action.targetState
      action.writeSymbol action.move ∈ rules := by
  dsimp only
  apply List.mem_flatMap.mpr
  refine ⟨program, programMember, ?_⟩
  apply List.mem_map.mpr
  refine ⟨symbol, allWorkSymbols_complete symbol, ?_⟩
  rfl

private theorem find_program_rule
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) :
    let action := program.action symbol
    findWorkRule rules program.state symbol =
      some (literalRule program.state symbol action.targetState
        action.writeSymbol action.move) := by
  dsimp only
  exact findWorkRule_eq_some_of_mem
    rules_pairwise_query_distinct
    (materializedRule_mem program programMember symbol)

def configAtWord (state : Nat)
    (left word : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtWord state left word

def configAtLeftWord (state : Nat)
    (leftWord right : List WorkSymbol) : WorkConfiguration :=
  TargetEmitter.configAtLeftWord state leftWord right

private theorem program_state_not_halted
    (program : StateProgram) (member : program ∈ statePrograms)
    (tape : WorkTape) :
    machine.isHalted { state := program.state, tape := tape } = false := by
  have stateBound :=
    state_ge_three_of_mem statePrograms
      statePrograms_at_least_three program member
  have acceptNe : program.state ≠ State.accept := by
    unfold State.accept
    omega
  have rejectNe : program.state ≠ State.reject := by
    unfold State.reject
    omega
  simp [machine, WorkMachine.isHalted, acceptNe, rejectNe]

private theorem moveLeftFromWord
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) (action : Action)
    (actionEq : program.action symbol = action)
    (left right : List WorkSymbol)
    (moveEq : action.move = .left) :
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (configAtLeftWord action.targetState left
        (action.writeSymbol :: right)) := by
  have found := find_program_rule program programMember symbol
  rw [actionEq] at found
  have foundLeft :
      findWorkRule rules program.state symbol =
        some (literalRule program.state symbol
          action.targetState action.writeSymbol .left) := by
    simpa [moveEq] using found
  calc
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule program.state symbol action.targetState
          action.writeSymbol .left)
        (configAtWord program.state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _
        (program_state_not_halted program programMember _) foundLeft
    _ = some (configAtLeftWord action.targetState left
        (action.writeSymbol :: right)) := by
      cases left <;> rfl

private theorem moveLeftFromLeftWord
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) (action : Action)
    (actionEq : program.action symbol = action)
    (left right : List WorkSymbol)
    (moveEq : action.move = .left) :
    workStep? machine
        (configAtLeftWord program.state (symbol :: left) right) =
      some (configAtLeftWord action.targetState left
        (action.writeSymbol :: right)) := by
  have found := find_program_rule program programMember symbol
  rw [actionEq] at found
  have foundLeft :
      findWorkRule rules program.state symbol =
        some (literalRule program.state symbol
          action.targetState action.writeSymbol .left) := by
    simpa [moveEq] using found
  calc
    workStep? machine
        (configAtLeftWord program.state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule program.state symbol action.targetState
          action.writeSymbol .left)
        (configAtLeftWord program.state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _
        (program_state_not_halted program programMember _) foundLeft
    _ = some (configAtLeftWord action.targetState left
        (action.writeSymbol :: right)) := by
      cases left <;> rfl

private theorem moveRightFromWord
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) (action : Action)
    (actionEq : program.action symbol = action)
    (left right : List WorkSymbol)
    (moveEq : action.move = .right) :
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (configAtWord action.targetState
        (action.writeSymbol :: left) right) := by
  have found := find_program_rule program programMember symbol
  rw [actionEq] at found
  have foundRight :
      findWorkRule rules program.state symbol =
        some (literalRule program.state symbol
          action.targetState action.writeSymbol .right) := by
    simpa [moveEq] using found
  calc
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule program.state symbol action.targetState
          action.writeSymbol .right)
        (configAtWord program.state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _
        (program_state_not_halted program programMember _) foundRight
    _ = some (configAtWord action.targetState
        (action.writeSymbol :: left) right) := by
      cases right <;> rfl

private theorem moveRightFromLeftWord
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) (action : Action)
    (actionEq : program.action symbol = action)
    (left right : List WorkSymbol)
    (moveEq : action.move = .right) :
    workStep? machine
        (configAtLeftWord program.state (symbol :: left) right) =
      some (configAtWord action.targetState
        (action.writeSymbol :: left) right) := by
  have found := find_program_rule program programMember symbol
  rw [actionEq] at found
  have foundRight :
      findWorkRule rules program.state symbol =
        some (literalRule program.state symbol
          action.targetState action.writeSymbol .right) := by
    simpa [moveEq] using found
  calc
    workStep? machine
        (configAtLeftWord program.state (symbol :: left) right) =
      some (applyWorkRule
        (literalRule program.state symbol action.targetState
          action.writeSymbol .right)
        (configAtLeftWord program.state (symbol :: left) right)) :=
      workStep?_eq_apply_of_find _ _ _
        (program_state_not_halted program programMember _) foundRight
    _ = some (configAtWord action.targetState
        (action.writeSymbol :: left) right) := by
      cases right <;> rfl

private theorem stayAtWord
    (program : StateProgram) (programMember : program ∈ statePrograms)
    (symbol : WorkSymbol) (action : Action)
    (actionEq : program.action symbol = action)
    (left right : List WorkSymbol)
    (moveEq : action.move = .stay) :
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (configAtWord action.targetState left
        (action.writeSymbol :: right)) := by
  have found := find_program_rule program programMember symbol
  rw [actionEq] at found
  have foundStay :
      findWorkRule rules program.state symbol =
        some (literalRule program.state symbol
          action.targetState action.writeSymbol .stay) := by
    simpa [moveEq] using found
  calc
    workStep? machine
        (configAtWord program.state left (symbol :: right)) =
      some (applyWorkRule
        (literalRule program.state symbol action.targetState
          action.writeSymbol .stay)
        (configAtWord program.state left (symbol :: right))) :=
      workStep?_eq_apply_of_find _ _ _
        (program_state_not_halted program programMember _) foundStay
    _ = some (configAtWord action.targetState left
        (action.writeSymbol :: right)) := by
      rfl

private theorem exactRun_add
    (first second : Nat)
    (initial middle final : WorkConfiguration)
    (hFirst :
      workRunExact? machine first initial = some middle)
    (hSecond :
      workRunExact? machine second middle = some final) :
    workRunExact? machine (first + second) initial = some final :=
  PipelineMachineSimulation.workRunExact?_compose
    machine first second initial middle final hFirst hSecond

private theorem exactRun_one
    (initial final : WorkConfiguration)
    (step : workStep? machine initial = some final) :
    workRunExact? machine 1 initial = some final := by
  change
    (match workStep? machine initial with
     | none => none
     | some next => workRunExact? machine 0 next) =
      some final
  rw [step]
  rfl

private theorem scanLeftExact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ head leftTail rightSide,
      Allowed head →
      workStep? machine
          (configAtLeftWord state (head :: leftTail) rightSide) =
        some (configAtLeftWord state
          leftTail (head :: rightSide)))
    (word leftSuffix rightSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtLeftWord state
          (word ++ leftSuffix) rightSide) =
      some (configAtLeftWord state leftSuffix
        (word.reverse ++ rightSide)) := by
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
        (match workStep? machine
          (configAtLeftWord state
            (head :: (rest ++ leftSuffix)) rightSide) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) = _
      rw [hStep head (rest ++ leftSuffix) rightSide headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: rightSide) restAllowed

private theorem scanRightExact (state : Nat)
    (Allowed : WorkSymbol → Prop)
    (hStep : ∀ leftSide head suffix,
      Allowed head →
      workStep? machine
          (configAtWord state leftSide (head :: suffix)) =
        some (configAtWord state (head :: leftSide) suffix))
    (word suffix leftSide : List WorkSymbol)
    (hAllowed : ∀ symbol, symbol ∈ word → Allowed symbol) :
    workRunExact? machine word.length
        (configAtWord state leftSide (word ++ suffix)) =
      some (configAtWord state
        (word.reverse ++ leftSide) suffix) := by
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
        (match workStep? machine
          (configAtWord state leftSide
            (head :: (rest ++ suffix))) with
         | none => none
         | some next =>
             workRunExact? machine rest.length next) = _
      rw [hStep leftSide head (rest ++ suffix) headAllowed]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (head :: leftSide) restAllowed

/-! ### Exact literal parser paths and their capacity invariant -/

/-- A proof-level path through the fixed literal parser.  The contribution is
the sum of the unary units selected by the traversed source cells.  Packedness
is stored locally so exact tape motion never relies on a semantic decoder. -/
private inductive ParsePath (metric : Metric) :
    ParseState → List WorkSymbol → ParseState → Nat → Prop where
  | nil (position : ParseState) :
      ParsePath metric position [] position 0
  | cons {position next final : ParseState}
      {symbol : WorkSymbol} {rest : List WorkSymbol}
      {contribution tailContribution : Nat}
      (packed : TargetEmitter.PackedSymbol symbol)
      (step :
        parseStep metric position symbol =
          some (next, contribution))
      (tail :
        ParsePath metric next rest final tailContribution) :
      ParsePath metric position (symbol :: rest) final
        (contribution + tailContribution)

private theorem parsePath_append
    {metric : Metric} {start middle final : ParseState}
    {first second : List WorkSymbol}
    {firstContribution secondContribution : Nat}
    (left :
      ParsePath metric start first middle firstContribution)
    (right :
      ParsePath metric middle second final secondContribution) :
    ParsePath metric start (first ++ second) final
      (firstContribution + secondContribution) := by
  induction left with
  | nil position =>
      simpa using right
  | @cons position next middle symbol rest contribution
      tailContribution packed step tail inductionHypothesis =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ParsePath.cons packed step (inductionHypothesis right)

private theorem parsePath_single
    {metric : Metric} {start next : ParseState}
    {symbol : WorkSymbol} {contribution : Nat}
    (packed : TargetEmitter.PackedSymbol symbol)
    (step :
      parseStep metric start symbol = some (next, contribution)) :
    ParsePath metric start [symbol] next contribution := by
  simpa using
    ParsePath.cons packed step (ParsePath.nil next)

private theorem parsePath_two
    {metric : Metric} {start middle final : ParseState}
    {first second : WorkSymbol}
    {firstContribution secondContribution : Nat}
    (firstPacked : TargetEmitter.PackedSymbol first)
    (secondPacked : TargetEmitter.PackedSymbol second)
    (firstStep :
      parseStep metric start first =
        some (middle, firstContribution))
    (secondStep :
      parseStep metric middle second =
        some (final, secondContribution)) :
    ParsePath metric start [first, second] final
      (firstContribution + secondContribution) := by
  exact
    ParsePath.cons firstPacked firstStep
      (ParsePath.cons secondPacked secondStep
        (ParsePath.nil final))

private theorem packed00_eq_sourceCell00 :
    packed00 = SourceParser.cell00 := by
  rfl

private theorem packed01_eq_sourceCell01 :
    packed01 = SourceParser.cell01 := by
  rfl

private theorem packed10_eq_sourceCell10 :
    packed10 = SourceParser.cell10 := by
  rfl

private theorem packed11_eq_sourceCell11 :
    packed11 = SourceParser.cell11 := by
  rfl

attribute [local simp] packed00 packed01 packed10 packed11
  SourceParser.cell00 SourceParser.cell01
  SourceParser.cell10 SourceParser.cell11

/-- Sixteen units of finite-state credit are accumulated immediately before
the sole source transition whose contribution may exceed 64. -/
private def parseCredit : ParseState → Nat
  | .sourceAfter00 _ .output => 16
  | _ => 0

private theorem parseStep_credit_closed
    (metric : Metric) (position : ParseState)
    (symbol : WorkSymbol) :
    match parseStep metric position symbol with
    | none => True
    | some (next, contribution) =>
        contribution + parseCredit next ≤
          64 + parseCredit position := by
  cases metric <;>
    cases position <;>
    try { cases ‹Bool› } <;>
    try { cases ‹SourceContinuation› } <;>
    rcases symbol with ⟨first, second⟩ <;>
    cases first <;> cases second <;>
    simp [parseStep, parseCredit, headerInputUnitContribution,
      sourceContribution, gateEndContribution, packed00, packed01,
      packed10, packed11,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne]
  all_goals
    split <;> try simp_all [afterSource] <;> try omega
  all_goals
    split <;> try simp_all <;> omega

private theorem parseStep_credit
    (metric : Metric) (position next : ParseState)
    (symbol : WorkSymbol) (contribution : Nat)
    (step :
      parseStep metric position symbol =
        some (next, contribution)) :
    contribution + parseCredit next ≤
      64 + parseCredit position := by
  have closed :=
    parseStep_credit_closed metric position symbol
  rw [step] at closed
  exact closed

private theorem headerInputUnitContribution_le
    (metric : Metric) :
    headerInputUnitContribution metric ≤ metric.maxContribution := by
  cases metric <;> decide

private theorem sourceContribution_le
    (metric : Metric) (continuation : SourceContinuation)
    (seen : Bool) (kind : SourceKind) :
    sourceContribution metric continuation seen kind ≤
      metric.maxContribution := by
  cases metric <;> cases continuation <;>
    cases seen <;> cases kind <;> decide

private theorem gateEndContribution_le
    (metric : Metric) (seen : Bool) :
    gateEndContribution metric seen ≤ metric.maxContribution := by
  cases metric <;> cases seen <;> decide

private theorem parseStep_contribution_closed
    (metric : Metric) (position : ParseState)
    (symbol : WorkSymbol) :
    match parseStep metric position symbol with
    | none => True
    | some (_next, contribution) =>
        contribution ≤ metric.maxContribution := by
  cases position <;>
    rcases symbol with ⟨first, second⟩ <;>
    cases first <;> cases second <;>
    simp [parseStep, packed00, packed01, packed10, packed11,
      WorkSymbol.zeroZero, WorkSymbol.zeroOne,
      WorkSymbol.oneZero, WorkSymbol.oneOne,
      headerInputUnitContribution_le, sourceContribution_le,
      gateEndContribution_le]

private theorem parseStep_contribution_le
    (metric : Metric) (position next : ParseState)
    (symbol : WorkSymbol) (contribution : Nat)
    (step :
      parseStep metric position symbol =
        some (next, contribution)) :
    contribution ≤ metric.maxContribution := by
  have closed :=
    parseStep_contribution_closed metric position symbol
  rw [step] at closed
  exact closed

private theorem parsePath_credit
    {metric : Metric} {start final : ParseState}
    {word : List WorkSymbol} {contribution : Nat}
    (path : ParsePath metric start word final contribution) :
    contribution + parseCredit final ≤
      64 * word.length + parseCredit start := by
  induction path with
  | nil position =>
      simp
  | @cons position next final symbol rest headContribution
      tailContribution packed step tail inductionHypothesis =>
      have localBound :=
        parseStep_credit metric position next symbol
          headContribution step
      simp only [List.length_cons]
      omega

private theorem parsePath_packed
    {metric : Metric} {start final : ParseState}
    {word : List WorkSymbol} {contribution : Nat}
    (path : ParsePath metric start word final contribution) :
    ∀ symbol, symbol ∈ word →
      TargetEmitter.PackedSymbol symbol := by
  induction path with
  | nil position =>
      intro symbol member
      contradiction
  | @cons position next final head rest headContribution
      tailContribution packed step tail inductionHypothesis =>
      intro symbol member
      rcases List.mem_cons.mp member with equal | inTail
      · subst symbol
        exact packed
      · exact inductionHypothesis symbol inTail

private theorem parsePrefix_capacity
    {metric : Metric} {position : ParseState}
    {word : List WorkSymbol} {contribution : Nat}
    (path :
      ParsePath metric .versionFirst word position contribution) :
    contribution ≤ 64 * word.length := by
  have bounded := parsePath_credit path
  simp [parseCredit] at bounded
  omega

private theorem originalForMarker?_eq_none_of_packed
    {symbol : WorkSymbol}
    (packed : TargetEmitter.PackedSymbol symbol) :
    originalForMarker? symbol = none := by
  cases packed <;> rfl

private theorem isPacked_eq_true_of_packed
    {symbol : WorkSymbol}
    (packed : TargetEmitter.PackedSymbol symbol) :
    isPacked symbol = true := by
  cases packed <;> rfl

private theorem parse_path_exact
    {metric : Metric} {start final : ParseState}
    {word : List WorkSymbol} {contribution : Nat}
    (path : ParsePath metric start word final contribution)
    (left suffix : List WorkSymbol) :
    workRunExact? machine word.length
        (configAtWord (State.parse metric start)
          left (word ++ suffix)) =
      some
        (configAtWord (State.parse metric final)
          (word.reverse ++ left) suffix) := by
  induction path generalizing left with
  | nil position =>
      rfl
  | @cons position next final symbol rest headContribution
      tailContribution packed step tail inductionHypothesis =>
      let program : StateProgram :=
        { state := State.parse metric position
          action := parseAction metric position }
      have member : program ∈ statePrograms :=
        parse_program_mem metric position
      let middle :=
        configAtWord (State.parse metric next)
          (symbol :: left) (rest ++ suffix)
      have first :
          workRunExact? machine 1
              (configAtWord (State.parse metric position)
                left (symbol :: rest ++ suffix)) =
            some middle := by
        apply exactRun_one
        apply moveRightFromWord program member symbol
          (keepAction (State.parse metric next) .right symbol)
        · simp [program, parseAction,
            originalForMarker?_eq_none_of_packed packed,
            isPacked_eq_true_of_packed packed, step]
        · rfl
      have remainder :
          workRunExact? machine rest.length middle =
            some
              (configAtWord (State.parse metric final)
                (rest.reverse ++ symbol :: left) suffix) := by
        simpa [middle] using inductionHypothesis (symbol :: left)
      have complete :=
        exactRun_add 1 rest.length _ middle _ first remainder
      simpa [List.reverse_cons, List.append_assoc,
        Nat.add_comm] using complete

private theorem input_nat_parsePath
    (metric : Metric) (value : Nat) :
    ParsePath metric .inputNatFirst
      (SourceParser.natCells value) .gateNatFirst
      (value * headerInputUnitContribution metric) := by
  induction value with
  | zero =>
      simpa [SourceParser.natCells] using
        (parsePath_two
          (metric := metric)
          (middle := .inputNatSecond)
          (firstContribution := 0)
          (secondContribution := 0)
          .zeroZero .oneZero (by rfl) (by rfl))
  | succ value inductionHypothesis =>
      have first :
          ParsePath metric .inputNatFirst
            [packed00, packed01] .inputNatFirst
            (headerInputUnitContribution metric) := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .inputNatSecond)
            (firstContribution := 0)
            (secondContribution :=
              headerInputUnitContribution metric)
            .zeroZero .zeroOne (by rfl) (by rfl))
      have complete :=
        parsePath_append first inductionHypothesis
      simpa [SourceParser.natCells, Nat.succ_eq_add_one,
        Nat.add_mul, Nat.add_comm] using complete

private theorem gate_nat_parsePath
    (metric : Metric) (value : Nat) :
    ParsePath metric .gateNatFirst
      (SourceParser.natCells value) (.gateStart false) 0 := by
  induction value with
  | zero =>
      simpa [SourceParser.natCells] using
        (parsePath_two
          (metric := metric)
          (middle := .gateNatSecond)
          (firstContribution := 0)
          (secondContribution := 0)
          .zeroZero .oneZero (by rfl) (by rfl))
  | succ value inductionHypothesis =>
      have first :
          ParsePath metric .gateNatFirst
            [packed00, packed01] .gateNatFirst 0 := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .gateNatSecond)
            (firstContribution := 0)
            (secondContribution := 0)
            .zeroZero .zeroOne (by rfl) (by rfl))
      have complete :=
        parsePath_append first inductionHypothesis
      simpa [SourceParser.natCells] using complete

private theorem source_nat_parsePath
    (metric : Metric) (seen : Bool)
    (continuation : SourceContinuation) (value : Nat) :
    ParsePath metric (.sourceNatFirst seen continuation)
      (SourceParser.natCells value)
      (afterSource seen continuation) 0 := by
  induction value with
  | zero =>
      simpa [SourceParser.natCells] using
        (parsePath_two
          (metric := metric)
          (middle := .sourceNatSecond seen continuation)
          (firstContribution := 0)
          (secondContribution := 0)
          .zeroZero .oneZero (by rfl) (by rfl))
  | succ value inductionHypothesis =>
      have first :
          ParsePath metric (.sourceNatFirst seen continuation)
            [packed00, packed01]
            (.sourceNatFirst seen continuation) 0 := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .sourceNatSecond seen continuation)
            (firstContribution := 0)
            (secondContribution := 0)
            .zeroZero .zeroOne (by rfl) (by rfl))
      have complete :=
        parsePath_append first inductionHypothesis
      simpa [SourceParser.natCells] using complete

private def sourceKind : RawSource → SourceKind
  | .input _ => .input
  | .constant false => .constantFalse
  | .constant true => .constantTrue
  | .gate _ => .gate

private theorem source_parsePath
    (metric : Metric) (seen : Bool)
    (continuation : SourceContinuation) (source : RawSource) :
    ParsePath metric (.sourceStart seen continuation)
      (SourceParser.sourceCells source)
      (afterSource seen continuation)
      (sourceContribution metric continuation seen
        (sourceKind source)) := by
  cases source with
  | input index =>
      have initialPath :
          ParsePath metric (.sourceStart seen continuation)
            [packed00, packed11]
            (.sourceNatFirst seen continuation)
            (sourceContribution metric continuation seen .input) := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .sourceAfter00 seen continuation)
            (firstContribution := 0)
            (secondContribution :=
              sourceContribution metric continuation seen .input)
            .zeroZero .oneOne (by rfl) (by rfl))
      have complete :=
        parsePath_append initialPath
          (source_nat_parsePath metric seen continuation index)
      simpa [SourceParser.sourceCells, sourceKind] using complete
  | gate index =>
      have initialPath :
          ParsePath metric (.sourceStart seen continuation)
            [packed01, packed10]
            (.sourceNatFirst seen continuation)
            (sourceContribution metric continuation seen .gate) := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .sourceAfter01 seen continuation)
            (firstContribution := 0)
            (secondContribution :=
              sourceContribution metric continuation seen .gate)
            .zeroOne .oneZero (by rfl) (by rfl))
      have complete :=
        parsePath_append initialPath
          (source_nat_parsePath metric seen continuation index)
      simpa [SourceParser.sourceCells, sourceKind] using complete
  | constant value =>
      cases value with
      | false =>
          simpa [SourceParser.sourceCells, sourceKind] using
            (parsePath_two
              (metric := metric)
              (middle := .sourceAfter01 seen continuation)
              (firstContribution := 0)
              (secondContribution :=
                sourceContribution metric continuation seen
                  .constantFalse)
              .zeroOne .zeroZero (by rfl) (by rfl))
      | true =>
          simpa [SourceParser.sourceCells, sourceKind] using
            (parsePath_two
              (metric := metric)
              (middle := .sourceAfter01 seen continuation)
              (firstContribution := 0)
              (secondContribution :=
                sourceContribution metric continuation seen
                  .constantTrue)
              .zeroOne .zeroOne (by rfl) (by rfl))

private theorem gate_left_parsePath
    (metric : Metric) (seen : Bool) (source : RawSource) :
    ParsePath metric (.gateStart seen)
      (SourceParser.sourceCells source)
      (.sourceStart seen .gateRight)
      (sourceContribution metric .gateLeft seen
        (sourceKind source)) := by
  cases source with
  | input index =>
      have initialPath :
          ParsePath metric (.gateStart seen)
            [packed00, packed11]
            (.sourceNatFirst seen .gateLeft)
            (sourceContribution metric .gateLeft seen .input) := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .sourceAfter00 seen .gateLeft)
            (firstContribution := 0)
            (secondContribution :=
              sourceContribution metric .gateLeft seen .input)
            .zeroZero .oneOne (by rfl) (by rfl))
      have complete :=
        parsePath_append initialPath
          (source_nat_parsePath metric seen .gateLeft index)
      simpa [SourceParser.sourceCells, sourceKind, afterSource]
        using complete
  | gate index =>
      have initialPath :
          ParsePath metric (.gateStart seen)
            [packed01, packed10]
            (.sourceNatFirst seen .gateLeft)
            (sourceContribution metric .gateLeft seen .gate) := by
        simpa using
          (parsePath_two
            (metric := metric)
            (middle := .sourceAfter01 seen .gateLeft)
            (firstContribution := 0)
            (secondContribution :=
              sourceContribution metric .gateLeft seen .gate)
            .zeroOne .oneZero (by rfl) (by rfl))
      have complete :=
        parsePath_append initialPath
          (source_nat_parsePath metric seen .gateLeft index)
      simpa [SourceParser.sourceCells, sourceKind, afterSource]
        using complete
  | constant value =>
      cases value with
      | false =>
          simpa [SourceParser.sourceCells, sourceKind, afterSource] using
            (parsePath_two
              (metric := metric)
              (middle := .sourceAfter01 seen .gateLeft)
              (firstContribution := 0)
              (secondContribution :=
                sourceContribution metric .gateLeft seen
                  .constantFalse)
              .zeroOne .zeroZero (by rfl) (by rfl))
      | true =>
          simpa [SourceParser.sourceCells, sourceKind, afterSource] using
            (parsePath_two
              (metric := metric)
              (middle := .sourceAfter01 seen .gateLeft)
              (firstContribution := 0)
              (secondContribution :=
                sourceContribution metric .gateLeft seen
                  .constantTrue)
              .zeroOne .zeroOne (by rfl) (by rfl))

private def gateContribution
    (metric : Metric) (seen : Bool) (gate : RawGate) : Nat :=
  sourceContribution metric .gateLeft seen (sourceKind gate.left) +
    sourceContribution metric .gateRight seen (sourceKind gate.right) +
    gateEndContribution metric seen

private theorem gate_parsePath
    (metric : Metric) (seen : Bool) (gate : RawGate) :
    ParsePath metric (.gateStart seen)
      (SourceParser.gateCells gate) (.gateStart true)
      (gateContribution metric seen gate) := by
  have left := gate_left_parsePath metric seen gate.left
  have right :=
    source_parsePath metric seen .gateRight gate.right
  have throughSources := parsePath_append left right
  have ending :
      ParsePath metric (.gateEndFirst seen)
        [packed01, packed11] (.gateStart true)
        (gateEndContribution metric seen) := by
    simpa using
      (parsePath_two
        (metric := metric)
        (middle := .gateEndSecond seen)
        (firstContribution := 0)
        (secondContribution := gateEndContribution metric seen)
        .zeroOne .oneOne (by rfl) (by rfl))
  have complete := parsePath_append throughSources ending
  simpa [SourceParser.gateCells, gateContribution,
    afterSource, Nat.add_assoc] using complete

private def gatesContribution
    (metric : Metric) (seen : Bool) : List RawGate → Nat
  | [] => 0
  | gate :: rest =>
      gateContribution metric seen gate +
        gatesContribution metric true rest

private def seenAfterGates
    (seen : Bool) : List RawGate → Bool
  | [] => seen
  | _ :: _ => true

private theorem seenAfterGates_true
    (gates : List RawGate) :
    seenAfterGates true gates = true := by
  cases gates <;> rfl

private theorem gates_parsePath
    (metric : Metric) (seen : Bool) (gates : List RawGate) :
    ParsePath metric (.gateStart seen)
      (SourceParser.gateListCells gates)
      (.gateStart (seenAfterGates seen gates))
      (gatesContribution metric seen gates) := by
  induction gates generalizing seen with
  | nil =>
      exact ParsePath.nil (.gateStart seen)
  | cons gate rest inductionHypothesis =>
      have first := gate_parsePath metric seen gate
      have remaining := inductionHypothesis true
      rw [seenAfterGates_true] at remaining
      have complete := parsePath_append first remaining
      simpa [SourceParser.gateListCells, gatesContribution,
        seenAfterGates] using complete

private theorem finish_parsePath
    (metric : Metric) (seen : Bool) (output : RawSource) :
    ParsePath metric (.gateStart seen)
      ([packed10, packed00] ++
        SourceParser.sourceCells output ++
        [packed10, packed01, packed10, packed11])
      .done
      (sourceContribution metric .output seen
        (sourceKind output)) := by
  have initialPath :
      ParsePath metric (.gateStart seen)
        [packed10, packed00] (.sourceStart seen .output) 0 := by
    simpa using
      (parsePath_two
        (metric := metric)
        (middle := .programEndSecond seen)
        (firstContribution := 0)
        (secondContribution := 0)
        .oneZero .zeroZero (by rfl) (by rfl))
  have source := source_parsePath metric seen .output output
  have throughSource := parsePath_append initialPath source
  have suffixFirst :
      ParsePath metric .outputsEndFirst
        [packed10, packed01] .instanceEndFirst 0 := by
    simpa using
      (parsePath_two
        (metric := metric)
        (middle := .outputsEndSecond)
        (firstContribution := 0)
        (secondContribution := 0)
        .oneZero .zeroOne (by rfl) (by rfl))
  have suffixSecond :
      ParsePath metric .instanceEndFirst
        [packed10, packed11] .done 0 := by
    simpa using
      (parsePath_two
        (metric := metric)
        (middle := .instanceEndSecond)
        (firstContribution := 0)
        (secondContribution := 0)
        .oneZero .oneOne (by rfl) (by rfl))
  have suffix :
      ParsePath metric .outputsEndFirst
        [packed10, packed01, packed10, packed11] .done 0 := by
    simpa using parsePath_append suffixFirst suffixSecond
  have complete := parsePath_append throughSource suffix
  simpa [afterSource] using complete

private def metricContribution
    (metric : Metric) (raw : RawCircuit) : Nat :=
  raw.inputCount * headerInputUnitContribution metric +
    gatesContribution metric false raw.gates +
    sourceContribution metric .output
      (seenAfterGates false raw.gates) (sourceKind raw.output)

private theorem circuit_parsePath
    (metric : Metric) (raw : RawCircuit) :
    ParsePath metric .versionFirst
      (SourceParser.circuitCells raw) .done
      (metricContribution metric raw) := by
  have version :
      ParsePath metric .versionFirst
        [packed00, packed00] .inputNatFirst 0 := by
    simpa using
      (parsePath_two
        (metric := metric)
        (middle := .versionSecond)
        (firstContribution := 0)
        (secondContribution := 0)
        .zeroZero .zeroZero (by rfl) (by rfl))
  have inputs := input_nat_parsePath metric raw.inputCount
  have gatesNat := gate_nat_parsePath metric raw.gates.length
  have gates := gates_parsePath metric false raw.gates
  have finish :=
    finish_parsePath metric
      (seenAfterGates false raw.gates) raw.output
  have throughInputs := parsePath_append version inputs
  have throughGateNat := parsePath_append throughInputs gatesNat
  have throughGates := parsePath_append throughGateNat gates
  have complete := parsePath_append throughGates finish
  simpa [SourceParser.circuitCells, metricContribution,
    List.append_assoc, Nat.add_assoc] using complete

private theorem gatesContribution_inputCount
    (seen : Bool) (gates : List RawGate) :
    gatesContribution .inputCount seen gates = 0 := by
  induction gates generalizing seen with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [gatesContribution, gateContribution,
        sourceContribution, gateEndContribution,
        inductionHypothesis]

private theorem gatesContribution_normalizedGateCount
    (seen : Bool) (gates : List RawGate) :
    gatesContribution .normalizedGateCount seen gates =
      gates.length := by
  induction gates generalizing seen with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [gatesContribution, gateContribution,
        sourceContribution, gateEndContribution,
        inductionHypothesis]
      omega

private theorem gatesContribution_carrierWidth
    (seen : Bool) (gates : List RawGate) :
    gatesContribution .carrierWidth seen gates =
      6 * gates.length := by
  induction gates generalizing seen with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      simp [gatesContribution, gateContribution,
        sourceContribution, gateEndContribution,
        inductionHypothesis]
      omega

private theorem normalized_output_contribution
    (seen : Bool) (output : RawSource) :
    sourceContribution .normalizedGateCount .output seen
        (sourceKind output) =
      normalizationAddedGates output := by
  cases output with
  | input index =>
      rfl
  | gate index =>
      rfl
  | constant value =>
      cases value <;> rfl

private theorem carrier_output_contribution
    (seen : Bool) (output : RawSource) :
    sourceContribution .carrierWidth .output seen
        (sourceKind output) =
      6 * normalizationAddedGates output + 1 := by
  cases output with
  | input index =>
      rfl
  | gate index =>
      rfl
  | constant value =>
      cases value <;> rfl

private theorem baseline_gate_side_contribution
    (continuation : SourceContinuation)
    (side : continuation = .gateLeft ∨
      continuation = .gateRight)
    (seen : Bool) (source : RawSource) :
    sourceContribution .baseline continuation seen
        (sourceKind source) =
      sourceMacroWeight source := by
  rcases side with equal | equal <;>
    subst continuation <;>
    cases source with
    | input index => rfl
    | gate index => rfl
    | constant value => cases value <;> rfl

private theorem gateContribution_baseline_true
    (gate : RawGate) :
    gateContribution .baseline true gate =
      gateMacroWeight gate + 6 := by
  cases gate with
  | mk left right =>
      rw [gateContribution, gateMacroWeight]
      rw [baseline_gate_side_contribution .gateLeft
        (Or.inl rfl) true left]
      rw [baseline_gate_side_contribution .gateRight
        (Or.inr rfl) true right]
      rfl

private theorem gateContribution_baseline_false
    (gate : RawGate) :
    gateContribution .baseline false gate =
      gateMacroWeight gate + 4 := by
  cases gate with
  | mk left right =>
      rw [gateContribution, gateMacroWeight]
      rw [baseline_gate_side_contribution .gateLeft
        (Or.inl rfl) false left]
      rw [baseline_gate_side_contribution .gateRight
        (Or.inr rfl) false right]
      rfl

private theorem gatesContribution_baseline_true
    (gates : List RawGate) :
    gatesContribution .baseline true gates =
      gateListMacroWeight gates + 6 * gates.length := by
  induction gates with
  | nil =>
      rfl
  | cons gate rest inductionHypothesis =>
      rw [gatesContribution, gateContribution_baseline_true,
        inductionHypothesis]
      simp only [gateListMacroWeight, List.length_cons]
      omega

private theorem gatesContribution_baseline_false_cons
    (gate : RawGate) (rest : List RawGate) :
    gatesContribution .baseline false (gate :: rest) =
      gateListMacroWeight (gate :: rest) +
        4 + 6 * rest.length := by
  rw [gatesContribution, gateContribution_baseline_false,
    gatesContribution_baseline_true]
  simp only [gateListMacroWeight]
  omega

set_option linter.unusedSimpArgs false in
private theorem metricContribution_eq_slotValue
    (metric : Metric) (raw : RawCircuit) :
    metricContribution metric raw =
      slotValue (ledgerRegisters raw)
        (match metric with
         | .inputCount => .inputCount
         | .normalizedGateCount => .normalizedGateCount
         | .carrierWidth => .carrierWidth
         | .baseline => .baseline) := by
  cases metric with
  | inputCount =>
      simp [metricContribution, gatesContribution_inputCount,
        headerInputUnitContribution, sourceContribution,
        ledgerRegisters, slotValue]
  | normalizedGateCount =>
      rw [metricContribution,
        gatesContribution_normalizedGateCount,
        normalized_output_contribution]
      simp [headerInputUnitContribution, ledgerRegisters,
        slotValue, normalizedGateCount]
  | carrierWidth =>
      rw [metricContribution, gatesContribution_carrierWidth,
        carrier_output_contribution]
      simp [headerInputUnitContribution, ledgerRegisters,
        slotValue, carrierWidthValue, normalizedGateCount]
      omega
  | baseline =>
      cases raw with
      | mk inputs gates output =>
          cases gates with
          | nil =>
              cases output with
              | input index =>
                  simp [metricContribution, gatesContribution,
                    seenAfterGates, sourceContribution, sourceKind,
                    headerInputUnitContribution,
                    ledgerRegisters, slotValue, baselineValue,
                    normalizedGateCount, normalizationAddedGates,
                    normalizationMacroWeight, gateListMacroWeight]
              | gate index =>
                  simp [metricContribution, gatesContribution,
                    seenAfterGates, sourceContribution, sourceKind,
                    headerInputUnitContribution,
                    ledgerRegisters, slotValue, baselineValue,
                    normalizedGateCount, normalizationAddedGates,
                    normalizationMacroWeight, gateListMacroWeight]
              | constant value =>
                  cases value <;>
                    simp [metricContribution, gatesContribution,
                      seenAfterGates, sourceContribution, sourceKind,
                      headerInputUnitContribution,
                      ledgerRegisters, slotValue, baselineValue,
                      normalizedGateCount, normalizationAddedGates,
                      normalizationMacroWeight, gateListMacroWeight]
          | cons gate rest =>
              rw [metricContribution,
                gatesContribution_baseline_false_cons]
              cases output with
              | input index =>
                  simp [seenAfterGates, sourceContribution, sourceKind,
                    headerInputUnitContribution,
                    ledgerRegisters, slotValue, baselineValue,
                    normalizedGateCount, normalizationAddedGates,
                    normalizationMacroWeight, gateListMacroWeight]
                  omega
              | gate index =>
                  simp [seenAfterGates, sourceContribution, sourceKind,
                    headerInputUnitContribution,
                    ledgerRegisters, slotValue, baselineValue,
                    normalizedGateCount, normalizationAddedGates,
                    normalizationMacroWeight, gateListMacroWeight]
                  omega
              | constant value =>
                  cases value <;>
                    simp [seenAfterGates, sourceContribution, sourceKind,
                      headerInputUnitContribution,
                      ledgerRegisters, slotValue, baselineValue,
                      normalizedGateCount, normalizationAddedGates,
                      normalizationMacroWeight, gateListMacroWeight] <;>
                    omega

private theorem replicate_succ_append {α : Type}
    (count : Nat) (item : α) :
    List.replicate (count + 1) item =
      List.replicate count item ++ [item] := by
  induction count with
  | zero =>
      rfl
  | succ count ih =>
      change
        item :: List.replicate (count + 1) item =
          item :: (List.replicate count item ++ [item])
      rw [ih]

private theorem extend_exact
    (purpose : State.ExtendPurpose)
    (remaining : Nat) (bounded : remaining < 64)
    (right : List WorkSymbol) :
    workRunExact? machine (remaining + 1)
        (configAtWord (State.extend purpose remaining) []
          (cellBlank :: right)) =
      some
        (configAtWord (State.returnAfterExtend purpose)
          [activeEnd]
          (List.replicate remaining cellBlank ++ right)) := by
  induction remaining generalizing right with
  | zero =>
      apply exactRun_one
      apply moveRightFromWord
        ({ state := State.extend purpose 0
           action := extendAction purpose 0 } : StateProgram)
        (extend_program_mem purpose 0 (by decide))
        cellBlank
        (writeAction (State.returnAfterExtend purpose)
          activeEnd .right)
      · simp [extendAction, cellBlank]
      · rfl
  | succ remaining ih =>
      have remainingBound : remaining < 64 := by omega
      let middle :=
        configAtWord (State.extend purpose remaining) []
          (cellBlank :: cellBlank :: right)
      have first :
          workRunExact? machine 1
              (configAtWord
                (State.extend purpose (remaining + 1)) []
                (cellBlank :: right)) =
            some middle := by
        apply exactRun_one
        apply moveLeftFromWord
          ({ state := State.extend purpose (remaining + 1)
             action := extendAction purpose (remaining + 1) } :
            StateProgram)
          (extend_program_mem purpose (remaining + 1) bounded)
          cellBlank
          (keepAction (State.extend purpose remaining)
            .left cellBlank)
        · simp [extendAction, cellBlank]
        · rfl
      have rest :
          workRunExact? machine (remaining + 1) middle =
            some
              (configAtWord
                (State.returnAfterExtend purpose)
                [activeEnd]
                (List.replicate (remaining + 1) cellBlank ++
                  right)) := by
        simpa [middle, replicate_succ_append, List.append_assoc]
          using ih remainingBound (cellBlank :: right)
      have complete := exactRun_add 1 (remaining + 1)
        _ middle _ first rest
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using complete

private theorem grow_separator_exact
    (metric : Metric) (remaining reserve : Nat)
    (bounded : remaining ≤ metric.maxContribution)
    (fits : remaining ≤ reserve)
    (right : List WorkSymbol) :
    workRunExact? machine (2 * remaining + 1)
        (configAtWord
          (State.growSlotSeparator metric remaining)
          (List.replicate reserve cellBlank ++ [activeEnd])
          (slotSeparator :: right)) =
      some
        (configAtLeftWord (State.metricSeekActive metric)
          (List.replicate (reserve - remaining) cellBlank ++
            [activeEnd])
          (slotSeparator ::
            List.replicate remaining unaryUnit ++ right)) := by
  induction remaining generalizing reserve right with
  | zero =>
      let program : StateProgram :=
        { state := State.growSlotSeparator metric 0
          action := growSlotSeparatorAction metric 0 }
      have member : program ∈ statePrograms := by
        exact boundedMetricBand_program_mem
          State.growSlotSeparator growSlotSeparatorAction
          (by simp [stateProgramBands]) metric 0
          (Nat.zero_le _)
      apply exactRun_one
      apply moveLeftFromWord program member slotSeparator
        (keepAction (State.metricSeekActive metric)
          .left slotSeparator)
      · simp [program, growSlotSeparatorAction, slotSeparator]
      · rfl
  | succ remaining inductionHypothesis =>
      cases reserve with
      | zero =>
          omega
      | succ reserve =>
          have remainingBound :
              remaining ≤ metric.maxContribution := by
            omega
          have remainingFits : remaining ≤ reserve := by
            omega
          let separatorProgram : StateProgram :=
            { state :=
                State.growSlotSeparator metric (remaining + 1)
              action :=
                growSlotSeparatorAction metric (remaining + 1) }
          let blankProgram : StateProgram :=
            { state := State.growSlotBlank metric remaining
              action := growSlotBlankAction metric remaining }
          have separatorMember :
              separatorProgram ∈ statePrograms := by
            exact boundedMetricBand_program_mem
              State.growSlotSeparator growSlotSeparatorAction
              (by simp [stateProgramBands]) metric (remaining + 1)
              bounded
          have blankMember : blankProgram ∈ statePrograms := by
            exact boundedMetricBand_program_mem
              State.growSlotBlank growSlotBlankAction
              (by simp [stateProgramBands]) metric remaining
              remainingBound
          let afterSeparator :=
            configAtLeftWord (State.growSlotBlank metric remaining)
              (List.replicate (reserve + 1) cellBlank ++
                [activeEnd])
              (unaryUnit :: right)
          have separatorStep :
              workRunExact? machine 1
                  (configAtWord
                    (State.growSlotSeparator metric (remaining + 1))
                    (List.replicate (reserve + 1) cellBlank ++
                      [activeEnd])
                    (slotSeparator :: right)) =
                some afterSeparator := by
            apply exactRun_one
            apply moveLeftFromWord separatorProgram separatorMember
              slotSeparator
              (writeAction (State.growSlotBlank metric remaining)
                unaryUnit .left)
            · simp [separatorProgram, growSlotSeparatorAction,
                slotSeparator]
            · rfl
          let afterBlank :=
            configAtWord
              (State.growSlotSeparator metric remaining)
              (List.replicate reserve cellBlank ++ [activeEnd])
              (slotSeparator :: unaryUnit :: right)
          have blankStep :
              workRunExact? machine 1 afterSeparator =
                some afterBlank := by
            apply exactRun_one
            have stayed := stayAtWord blankProgram blankMember
              cellBlank
              (writeAction
                (State.growSlotSeparator metric remaining)
                slotSeparator .stay)
              (by simp [blankProgram, growSlotBlankAction, cellBlank])
              (List.replicate reserve cellBlank ++ [activeEnd])
              (unaryUnit :: right)
              rfl
            simpa [afterSeparator, afterBlank, blankProgram,
              writeAction, cellBlank, configAtLeftWord,
              configAtWord, TargetEmitter.configAtLeftWord,
              TargetEmitter.configAtWord,
              List.replicate_succ] using stayed
          have rest :
              workRunExact? machine (2 * remaining + 1)
                  afterBlank =
                some
                  (configAtLeftWord
                    (State.metricSeekActive metric)
                    (List.replicate
                        (reserve - remaining) cellBlank ++
                      [activeEnd])
                    (slotSeparator ::
                      List.replicate (remaining + 1) unaryUnit ++
                        right)) := by
            have recursive :=
              inductionHypothesis reserve remainingBound
                remainingFits (unaryUnit :: right)
            simpa [afterBlank, replicate_succ_append,
              List.append_assoc] using recursive
          have firstTwo :=
            exactRun_add 1 1 _ afterSeparator afterBlank
              separatorStep blankStep
          have complete :=
            exactRun_add (1 + 1) (2 * remaining + 1)
              _ afterBlank _ firstTwo rest
          have reserveDifference :
              reserve + 1 - (remaining + 1) =
                reserve - remaining := by
            omega
          rw [reserveDifference]
          have stepCount :
              2 * (remaining + 1) + 1 =
                1 + 1 + (2 * remaining + 1) := by
            omega
          rw [stepCount]
          exact complete

private theorem seek_and_grow_exact
    (metric : Metric) (contribution reserve : Nat)
    (bounded : contribution ≤ metric.maxContribution)
    (fits : contribution ≤ reserve)
    (right : List WorkSymbol) :
    workRunExact? machine (2 * contribution + 1)
        (configAtWord
          (State.seekSlotSeparator metric contribution)
          (List.replicate reserve cellBlank ++ [activeEnd])
          (slotSeparator :: right)) =
      some
        (configAtLeftWord (State.metricSeekActive metric)
          (List.replicate (reserve - contribution) cellBlank ++
            [activeEnd])
          (slotSeparator ::
            List.replicate contribution unaryUnit ++ right)) := by
  cases contribution with
  | zero =>
      let program : StateProgram :=
        { state := State.seekSlotSeparator metric 0
          action := seekSlotSeparatorAction metric 0 }
      have member : program ∈ statePrograms := by
        exact boundedMetricBand_program_mem
          State.seekSlotSeparator seekSlotSeparatorAction
          (by simp [stateProgramBands]) metric 0
          (Nat.zero_le _)
      apply exactRun_one
      apply moveLeftFromWord program member slotSeparator
        (keepAction (State.metricSeekActive metric)
          .left slotSeparator)
      · simp [program, seekSlotSeparatorAction, slotSeparator]
      · rfl
  | succ remaining =>
      cases reserve with
      | zero =>
          omega
      | succ reserve =>
          have remainingBound :
              remaining ≤ metric.maxContribution := by
            omega
          have remainingFits : remaining ≤ reserve := by
            omega
          let seekProgram : StateProgram :=
            { state :=
                State.seekSlotSeparator metric (remaining + 1)
              action :=
                seekSlotSeparatorAction metric (remaining + 1) }
          let blankProgram : StateProgram :=
            { state := State.growSlotBlank metric remaining
              action := growSlotBlankAction metric remaining }
          have seekMember : seekProgram ∈ statePrograms := by
            exact boundedMetricBand_program_mem
              State.seekSlotSeparator seekSlotSeparatorAction
              (by simp [stateProgramBands]) metric (remaining + 1)
              bounded
          have blankMember : blankProgram ∈ statePrograms := by
            exact boundedMetricBand_program_mem
              State.growSlotBlank growSlotBlankAction
              (by simp [stateProgramBands]) metric remaining
              remainingBound
          let afterSeparator :=
            configAtLeftWord (State.growSlotBlank metric remaining)
              (List.replicate (reserve + 1) cellBlank ++
                [activeEnd])
              (unaryUnit :: right)
          have separatorStep :
              workRunExact? machine 1
                  (configAtWord
                    (State.seekSlotSeparator metric (remaining + 1))
                    (List.replicate (reserve + 1) cellBlank ++
                      [activeEnd])
                    (slotSeparator :: right)) =
                some afterSeparator := by
            apply exactRun_one
            apply moveLeftFromWord seekProgram seekMember slotSeparator
              (writeAction (State.growSlotBlank metric remaining)
                unaryUnit .left)
            · simp [seekProgram, seekSlotSeparatorAction,
                slotSeparator]
            · rfl
          let afterBlank :=
            configAtWord
              (State.growSlotSeparator metric remaining)
              (List.replicate reserve cellBlank ++ [activeEnd])
              (slotSeparator :: unaryUnit :: right)
          have blankStep :
              workRunExact? machine 1 afterSeparator =
                some afterBlank := by
            apply exactRun_one
            have stayed := stayAtWord blankProgram blankMember
              cellBlank
              (writeAction
                (State.growSlotSeparator metric remaining)
                slotSeparator .stay)
              (by simp [blankProgram, growSlotBlankAction, cellBlank])
              (List.replicate reserve cellBlank ++ [activeEnd])
              (unaryUnit :: right)
              rfl
            simpa [afterSeparator, afterBlank, blankProgram,
              writeAction, cellBlank, configAtLeftWord,
              configAtWord, TargetEmitter.configAtLeftWord,
              TargetEmitter.configAtWord,
              List.replicate_succ] using stayed
          have rest :
              workRunExact? machine (2 * remaining + 1)
                  afterBlank =
                some
                  (configAtLeftWord
                    (State.metricSeekActive metric)
                    (List.replicate
                        (reserve - remaining) cellBlank ++
                      [activeEnd])
                    (slotSeparator ::
                      List.replicate (remaining + 1) unaryUnit ++
                        right)) := by
            have recursive :=
              grow_separator_exact metric remaining reserve
                remainingBound remainingFits (unaryUnit :: right)
            simpa [afterBlank, replicate_succ_append,
              List.append_assoc] using recursive
          have firstTwo :=
            exactRun_add 1 1 _ afterSeparator afterBlank
              separatorStep blankStep
          have complete :=
            exactRun_add (1 + 1) (2 * remaining + 1)
              _ afterBlank _ firstTwo rest
          have reserveDifference :
              reserve + 1 - (remaining + 1) =
                reserve - remaining := by
            omega
          rw [reserveDifference]
          have stepCount :
              2 * (remaining + 1) + 1 =
                1 + 1 + (2 * remaining + 1) := by
            omega
          rw [stepCount]
          exact complete

inductive LayoutSymbol : WorkSymbol → Prop where
  | blank : LayoutSymbol cellBlank
  | unaryUnit : LayoutSymbol unaryUnit
  | unarySeparator : LayoutSymbol unarySeparator
  | ledgerBoundary : LayoutSymbol ledgerBoundary
  | slotBoundary : LayoutSymbol slotBoundary

inductive MarkerPair : WorkSymbol → WorkSymbol → Prop where
  | zeroZero : MarkerPair packed00 WorkSymbol.blankZero
  | zeroOne : MarkerPair packed01 WorkSymbol.blankOne
  | oneZero : MarkerPair packed10 WorkSymbol.zeroBlank
  | oneOne : MarkerPair packed11 WorkSymbol.oneBlank

private theorem markerPair_marker
    {original marker : WorkSymbol}
    (pair : MarkerPair original marker) :
    markerFor? original = some marker := by
  cases pair <;> rfl

private theorem markerPair_original
    {original marker : WorkSymbol}
    (pair : MarkerPair original marker) :
    originalForMarker? marker = some original := by
  cases pair <;> rfl

private theorem markerPair_packed
    {original marker : WorkSymbol}
    (pair : MarkerPair original marker) :
    TargetEmitter.PackedSymbol original := by
  cases pair <;> constructor

private theorem packed_has_marker
    {symbol : WorkSymbol}
    (packed : TargetEmitter.PackedSymbol symbol) :
    ∃ marker, MarkerPair symbol marker := by
  cases packed with
  | zeroZero => exact ⟨WorkSymbol.blankZero, .zeroZero⟩
  | zeroOne => exact ⟨WorkSymbol.blankOne, .zeroOne⟩
  | oneZero => exact ⟨WorkSymbol.zeroBlank, .oneZero⟩
  | oneOne => exact ⟨WorkSymbol.oneBlank, .oneOne⟩

private theorem layout_isLayout
    {symbol : WorkSymbol} (layout : LayoutSymbol symbol) :
    isLayoutSymbol symbol = true := by
  cases layout <;> rfl

private theorem layout_replicate_blank
    (count : Nat) (symbol : WorkSymbol)
    (member : symbol ∈ List.replicate count cellBlank) :
    LayoutSymbol symbol := by
  have equal := List.eq_of_mem_replicate member
  subst symbol
  exact .blank

private theorem layout_reverse
    (word : List WorkSymbol)
    (allowed : ∀ symbol, symbol ∈ word → LayoutSymbol symbol)
    (symbol : WorkSymbol) (member : symbol ∈ word.reverse) :
    LayoutSymbol symbol := by
  exact allowed symbol (List.mem_reverse.mp member)

private def metricLayout
    (fixed : List WorkSymbol) (value reserve : Nat) :
    List WorkSymbol :=
  fixed ++
    slotBoundary ::
      (List.replicate value unaryUnit ++
        slotSeparator :: List.replicate reserve cellBlank)

private theorem metricLayout_length
    (fixed : List WorkSymbol) (value reserve : Nat) :
    (metricLayout fixed value reserve).length =
      fixed.length + value + reserve + 2 := by
  simp [metricLayout]
  omega

private theorem metricLayout_allowed
    (fixed : List WorkSymbol)
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol)
    (value reserve : Nat) :
    ∀ symbol, symbol ∈ metricLayout fixed value reserve →
      LayoutSymbol symbol := by
  intro symbol member
  rcases List.mem_append.mp member with inFixed | inSlot
  · exact fixedAllowed symbol inFixed
  · simp only [List.mem_cons] at inSlot
    rcases inSlot with equal | inRest
    · subst symbol
      exact .slotBoundary
    · rcases List.mem_append.mp inRest with inUnits | inSeparator
      · have equal := List.eq_of_mem_replicate inUnits
        subst symbol
        exact .unaryUnit
      · simp only [List.mem_cons] at inSeparator
        rcases inSeparator with equal | inBlanks
        · subst symbol
          exact .unarySeparator
        · exact layout_replicate_blank reserve symbol inBlanks

private theorem metricLayout_reverse
    (fixed : List WorkSymbol) (value reserve : Nat) :
    (metricLayout fixed value reserve).reverse =
      List.replicate reserve cellBlank ++
        slotSeparator ::
          (List.replicate value unaryUnit ++
            slotBoundary :: fixed.reverse) := by
  simp [metricLayout, List.reverse_append,
    List.reverse_replicate, List.append_assoc]

private theorem replicate_add_word
    {α : Type} (first second : Nat) (item : α) :
    List.replicate (first + second) item =
      List.replicate first item ++
        List.replicate second item := by
  induction first with
  | zero =>
      simp
  | succ first inductionHypothesis =>
      simp only [Nat.succ_add, List.replicate_succ,
        List.cons_append, inductionHypothesis]

def metricCellSteps
    (processed layout : List WorkSymbol)
    (reserve contribution : Nat) : Nat :=
  136 + 4 * processed.length + 2 * layout.length +
    2 * reserve + contribution

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
private theorem metric_cell_exact
    (metric : Metric)
    (processed rest fixed : List WorkSymbol)
    (position next : ParseState)
    (value reserve contribution : Nat)
    (current marker : WorkSymbol)
    (prefixPath :
      ParsePath metric .versionFirst processed position value)
    (pair : MarkerPair current marker)
    (step :
      parseStep metric position current =
        some (next, contribution))
    (capacityEq :
      value + reserve = 64 * (processed.length + 1))
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol) :
    let layout := metricLayout fixed value reserve
    let nextLayout :=
      metricLayout fixed (value + contribution)
        (reserve - contribution + 64)
    workRunExact? machine
        (metricCellSteps processed layout reserve contribution)
        (configAtLeftWord (State.rewindSource metric)
          (processed.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          (marker :: rest)) =
      some
        (configAtWord (State.afterMetricCell metric)
          ((processed ++ [current]).reverse ++
            sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
          rest) := by
  dsimp only
  let layout := metricLayout fixed value reserve
  let nextReserve := reserve - contribution + 64
  let nextLayout :=
    metricLayout fixed (value + contribution) nextReserve
  have processedPacked := parsePath_packed prefixPath
  have contributionBound :=
    parseStep_contribution_le metric position next current
      contribution step
  have extendedPath :
      ParsePath metric .versionFirst
        (processed ++ [current]) next (value + contribution) := by
    have currentPath :=
      parsePath_single (markerPair_packed pair) step
    simpa using parsePath_append prefixPath currentPath
  have prefixCapacity := parsePrefix_capacity extendedPath
  have prefixCapacity' :
      value + contribution ≤ 64 * (processed.length + 1) := by
    simpa using prefixCapacity
  have fits : contribution ≤ reserve := by
    omega
  let rewindProgram : StateProgram :=
    { state := State.rewindSource metric
      action := rewindSourceAction metric }
  let seekBoundaryProgram : StateProgram :=
    { state := State.metricSeekBoundary metric contribution
      action := metricSeekBoundaryAction metric contribution }
  let seekActiveProgram : StateProgram :=
    { state := State.seekActiveForGrowth metric contribution
      action := seekActiveForGrowthAction metric contribution }
  let seekSeparatorProgram : StateProgram :=
    { state := State.seekSlotSeparator metric contribution
      action := seekSlotSeparatorAction metric contribution }
  let extendSeekProgram : StateProgram :=
    { state := State.metricSeekActive metric
      action := metricSeekActiveAction metric }
  let returnProgram : StateProgram :=
    { state := State.returnAfterExtend (.metricCell metric)
      action := returnAfterExtendAction (.metricCell metric) }
  let restoreProgram : StateProgram :=
    { state := State.restoreMetricCursor metric
      action := restoreMetricCursorAction metric }
  let parserProgram : StateProgram :=
    { state := State.parse metric position
      action := parseAction metric position }
  have rewindMember : rewindProgram ∈ statePrograms := by
    exact metricBand_program_mem State.rewindSource rewindSourceAction
      (by simp [stateProgramBands]) metric
  have seekBoundaryMember :
      seekBoundaryProgram ∈ statePrograms := by
    exact boundedMetricBand_program_mem State.metricSeekBoundary
      metricSeekBoundaryAction (by simp [stateProgramBands])
      metric contribution contributionBound
  have seekActiveMember : seekActiveProgram ∈ statePrograms := by
    exact boundedMetricBand_program_mem State.seekActiveForGrowth
      seekActiveForGrowthAction (by simp [stateProgramBands])
      metric contribution contributionBound
  have seekSeparatorMember :
      seekSeparatorProgram ∈ statePrograms := by
    exact boundedMetricBand_program_mem State.seekSlotSeparator
      seekSlotSeparatorAction (by simp [stateProgramBands])
      metric contribution contributionBound
  have extendSeekMember : extendSeekProgram ∈ statePrograms := by
    exact metricBand_program_mem State.metricSeekActive
      metricSeekActiveAction (by simp [stateProgramBands]) metric
  have returnMember : returnProgram ∈ statePrograms :=
    return_program_mem (.metricCell metric)
  have restoreMember : restoreProgram ∈ statePrograms := by
    exact metricBand_program_mem State.restoreMetricCursor
      restoreMetricCursorAction (by simp [stateProgramBands]) metric
  have parserMember : parserProgram ∈ statePrograms :=
    parse_program_mem metric position
  let atBoundary :=
    configAtLeftWord (State.rewindSource metric)
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (processed ++ marker :: rest)
  have rewind :
      workRunExact? machine processed.length
          (configAtLeftWord (State.rewindSource metric)
            (processed.reverse ++
              sourceLeftBoundary :: (layout ++ [activeEnd]))
            (marker :: rest)) =
        some atBoundary := by
    have scan := scanLeftExact (State.rewindSource metric)
      TargetEmitter.PackedSymbol
      (fun head leftTail rightSide packed => by
        apply moveLeftFromLeftWord rewindProgram rewindMember head
          (keepAction (State.rewindSource metric) .left head)
        · cases packed <;> rfl
        · rfl)
      processed.reverse
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
      (by
        intro symbol member
        exact processedPacked symbol (List.mem_reverse.mp member))
    simpa [atBoundary, List.reverse_reverse,
      List.append_assoc] using scan
  let atParser :=
    configAtWord (State.parse metric .versionFirst)
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (processed ++ marker :: rest)
  have crossToParser :
      workRunExact? machine 1 atBoundary = some atParser := by
    apply exactRun_one
    apply moveRightFromLeftWord rewindProgram rewindMember
      sourceLeftBoundary
      (keepAction (State.parse metric .versionFirst)
        .right sourceLeftBoundary)
    · rfl
    · rfl
  let atMarker :=
    configAtWord (State.parse metric position)
      (processed.reverse ++
        sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
  have parsePrefix :
      workRunExact? machine processed.length atParser =
        some atMarker := by
    have parsed :=
      parse_path_exact prefixPath
        (sourceLeftBoundary :: (layout ++ [activeEnd]))
        (marker :: rest)
    simpa [atParser, atMarker] using parsed
  let afterMarker :=
    configAtLeftWord
      (State.metricSeekBoundary metric contribution)
      (processed.reverse ++
        sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
  have parseMarker :
      workRunExact? machine 1 atMarker = some afterMarker := by
    apply exactRun_one
    apply moveLeftFromWord parserProgram parserMember marker
      (keepAction
        (State.metricSeekBoundary metric contribution)
        .left marker)
    · simp [parserProgram, parseAction,
        markerPair_original pair, step]
    · rfl
  let backAtBoundary :=
    configAtLeftWord
      (State.metricSeekBoundary metric contribution)
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (processed ++ marker :: rest)
  have seekBoundary :
      workRunExact? machine processed.length afterMarker =
        some backAtBoundary := by
    have scan := scanLeftExact
      (State.metricSeekBoundary metric contribution)
      TargetEmitter.PackedSymbol
      (fun head leftTail rightSide packed => by
        apply moveLeftFromLeftWord seekBoundaryProgram
          seekBoundaryMember head
          (keepAction
            (State.metricSeekBoundary metric contribution)
            .left head)
        · cases packed <;> rfl
        · rfl)
      processed.reverse
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
      (by
        intro symbol member
        exact processedPacked symbol (List.mem_reverse.mp member))
    simpa [afterMarker, backAtBoundary,
      List.reverse_reverse, List.append_assoc] using scan
  let atLayout :=
    configAtLeftWord
      (State.seekActiveForGrowth metric contribution)
      (layout ++ [activeEnd])
      (sourceLeftBoundary :: processed ++ marker :: rest)
  have crossToLayout :
      workRunExact? machine 1 backAtBoundary =
        some atLayout := by
    apply exactRun_one
    apply moveLeftFromLeftWord seekBoundaryProgram
      seekBoundaryMember sourceLeftBoundary
      (keepAction
        (State.seekActiveForGrowth metric contribution)
        .left sourceLeftBoundary)
    · rfl
    · rfl
  let atActive :=
    configAtLeftWord
      (State.seekActiveForGrowth metric contribution)
      [activeEnd]
      (layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have seekActive :
      workRunExact? machine layout.length atLayout =
        some atActive := by
    have scan := scanLeftExact
      (State.seekActiveForGrowth metric contribution)
      LayoutSymbol
      (fun head leftTail rightSide allowed => by
        apply moveLeftFromLeftWord seekActiveProgram
          seekActiveMember head
          (keepAction
            (State.seekActiveForGrowth metric contribution)
            .left head)
        · cases allowed <;> rfl
        · rfl)
      layout [activeEnd]
      (sourceLeftBoundary :: processed ++ marker :: rest)
      (metricLayout_allowed fixed fixedAllowed value reserve)
    simpa [atLayout, atActive] using scan
  let atSeekSeparator :=
    configAtWord
      (State.seekSlotSeparator metric contribution)
      [activeEnd]
      (layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have turnAtActive :
      workRunExact? machine 1 atActive =
        some atSeekSeparator := by
    apply exactRun_one
    apply moveRightFromLeftWord seekActiveProgram seekActiveMember
      activeEnd
      (keepAction
        (State.seekSlotSeparator metric contribution)
        .right activeEnd)
    · rfl
    · rfl
  let slotRight :=
    List.replicate value unaryUnit ++
      slotBoundary :: fixed.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest
  let atSeparator :=
    configAtWord
      (State.seekSlotSeparator metric contribution)
      (List.replicate reserve cellBlank ++ [activeEnd])
      (slotSeparator :: slotRight)
  have seekSeparator :
      workRunExact? machine reserve atSeekSeparator =
        some atSeparator := by
    have scan := scanRightExact
      (State.seekSlotSeparator metric contribution)
      (fun symbol => symbol = cellBlank)
      (fun leftSide head suffix equal => by
        subst head
        apply moveRightFromWord seekSeparatorProgram
          seekSeparatorMember cellBlank
          (keepAction
            (State.seekSlotSeparator metric contribution)
            .right cellBlank)
        · simp [seekSeparatorProgram, seekSlotSeparatorAction,
            cellBlank, slotSeparator, unarySeparator,
            TargetEmitter.unarySeparator,
            WorkSymbol.blank, WorkSymbol.oneBlank]
        · rfl)
      (List.replicate reserve cellBlank)
      (slotSeparator :: slotRight) [activeEnd]
      (by
        intro symbol member
        exact List.eq_of_mem_replicate member)
    simpa [atSeekSeparator, atSeparator, slotRight,
      layout, metricLayout_reverse, List.reverse_replicate,
      List.append_assoc] using scan
  let afterGrowth :=
    configAtLeftWord (State.metricSeekActive metric)
      (List.replicate (reserve - contribution) cellBlank ++
        [activeEnd])
      (slotSeparator ::
        List.replicate (value + contribution) unaryUnit ++
          slotBoundary :: fixed.reverse ++
            sourceLeftBoundary :: processed ++ marker :: rest)
  have grow :
      workRunExact? machine (2 * contribution + 1)
          atSeparator =
        some afterGrowth := by
    have grown :=
      seek_and_grow_exact metric contribution reserve
        contributionBound fits slotRight
    have combinedUnits :
        List.replicate contribution unaryUnit ++
            List.replicate value unaryUnit =
          List.replicate (value + contribution) unaryUnit := by
      rw [← replicate_add_word]
      rw [Nat.add_comm]
    have combinedRight :
        List.replicate contribution unaryUnit ++
            (List.replicate value unaryUnit ++
              slotBoundary :: fixed.reverse ++
                sourceLeftBoundary :: processed ++ marker :: rest) =
          List.replicate (value + contribution) unaryUnit ++
            slotBoundary :: fixed.reverse ++
              sourceLeftBoundary :: processed ++ marker :: rest := by
      simp only [List.cons_append, List.append_assoc]
      rw [← List.append_assoc, combinedUnits]
    have growthRight :
        slotSeparator ::
            List.replicate contribution unaryUnit ++ slotRight =
          slotSeparator ::
            List.replicate (value + contribution) unaryUnit ++
              slotBoundary :: fixed.reverse ++
                sourceLeftBoundary :: processed ++ marker :: rest := by
      simpa only [slotRight, List.cons_append] using
        congrArg (List.cons slotSeparator) combinedRight
    rw [growthRight] at grown
    simpa only [atSeparator, afterGrowth, slotRight] using grown
  let atExtendActive :=
    configAtLeftWord (State.metricSeekActive metric)
      [activeEnd]
      (List.replicate (reserve - contribution) cellBlank ++
        slotSeparator ::
          List.replicate (value + contribution) unaryUnit ++
            slotBoundary :: fixed.reverse ++
              sourceLeftBoundary :: processed ++ marker :: rest)
  have seekExtendActive :
      workRunExact? machine (reserve - contribution)
          afterGrowth =
        some atExtendActive := by
    have blankAction :
        extendSeekProgram.action cellBlank =
          keepAction (State.metricSeekActive metric)
            .left cellBlank := by
      rfl
    have scan := scanLeftExact (State.metricSeekActive metric)
      (fun symbol => symbol = cellBlank)
      (fun head leftTail rightSide equal => by
        subst head
        apply moveLeftFromLeftWord extendSeekProgram
          extendSeekMember cellBlank
          (keepAction (State.metricSeekActive metric)
            .left cellBlank)
        · exact blankAction
        · rfl)
      (List.replicate (reserve - contribution) cellBlank)
      [activeEnd]
      (slotSeparator ::
        List.replicate (value + contribution) unaryUnit ++
          slotBoundary :: fixed.reverse ++
            sourceLeftBoundary :: processed ++ marker :: rest)
      (by
        intro symbol member
        exact List.eq_of_mem_replicate member)
    simpa [afterGrowth, atExtendActive,
      List.reverse_replicate] using scan
  let atExtend :=
    configAtWord (State.extend (.metricCell metric) 63) []
      (cellBlank :: cellBlank ::
        List.replicate (reserve - contribution) cellBlank ++
          slotSeparator ::
            List.replicate (value + contribution) unaryUnit ++
              slotBoundary :: fixed.reverse ++
                sourceLeftBoundary :: processed ++ marker :: rest)
  have launchExtend :
      workRunExact? machine 1 atExtendActive =
        some atExtend := by
    apply exactRun_one
    have activeAction :
        extendSeekProgram.action activeEnd =
          writeAction (State.extend (.metricCell metric) 63)
            cellBlank .left := by
      rfl
    have moved := moveLeftFromLeftWord extendSeekProgram
      extendSeekMember activeEnd
      (writeAction (State.extend (.metricCell metric) 63)
        cellBlank .left)
      activeAction
      ([] : List WorkSymbol)
      (List.replicate (reserve - contribution) cellBlank ++
        slotSeparator ::
          List.replicate (value + contribution) unaryUnit ++
            slotBoundary :: fixed.reverse ++
              sourceLeftBoundary :: processed ++ marker :: rest)
      rfl
    simpa [atExtendActive, atExtend, extendSeekProgram,
      writeAction, activeEnd, cellBlank, List.append_assoc,
      configAtLeftWord, configAtWord,
      TargetEmitter.configAtLeftWord,
      TargetEmitter.configAtWord] using moved
  let growthLayout :=
    metricLayout fixed (value + contribution)
      (reserve - contribution)
  let returning :=
    configAtWord
      (State.returnAfterExtend (.metricCell metric))
      [activeEnd]
      (List.replicate 64 cellBlank ++ growthLayout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have extend :
      workRunExact? machine 64 atExtend = some returning := by
    have extended := extend_exact (.metricCell metric) 63
      (by decide)
      (cellBlank ::
        List.replicate (reserve - contribution) cellBlank ++
          slotSeparator ::
            List.replicate (value + contribution) unaryUnit ++
              slotBoundary :: fixed.reverse ++
                sourceLeftBoundary :: processed ++ marker :: rest)
    have growthReverse :
        growthLayout.reverse =
          List.replicate (reserve - contribution) cellBlank ++
            slotSeparator ::
              (List.replicate (value + contribution) unaryUnit ++
                slotBoundary :: fixed.reverse) := by
      exact metricLayout_reverse fixed (value + contribution)
        (reserve - contribution)
    have extendRight :
        List.replicate 63 cellBlank ++
              (cellBlank ::
                List.replicate (reserve - contribution) cellBlank ++
                  slotSeparator ::
                    List.replicate (value + contribution) unaryUnit ++
                      slotBoundary :: fixed.reverse ++
                        sourceLeftBoundary :: processed ++ marker :: rest) =
          List.replicate 64 cellBlank ++ growthLayout.reverse ++
            sourceLeftBoundary :: processed ++ marker :: rest := by
      rw [show
        List.replicate 64 cellBlank =
          List.replicate 63 cellBlank ++ [cellBlank] by
        exact replicate_succ_append 63 cellBlank]
      rw [growthReverse]
      simp only [List.append_assoc, List.cons_append,
        List.nil_append]
    rw [extendRight] at extended
    simpa only [atExtend, returning, Nat.reduceAdd,
      List.cons_append] using extended
  let returnWord :=
    List.replicate 64 cellBlank ++ growthLayout.reverse
  let returnedBoundary :=
    configAtWord
      (State.returnAfterExtend (.metricCell metric))
      (nextLayout ++ [activeEnd])
      (sourceLeftBoundary :: processed ++ marker :: rest)
  have returnScan :
      workRunExact? machine returnWord.length returning =
        some returnedBoundary := by
    have scan := scanRightExact
      (State.returnAfterExtend (.metricCell metric))
      LayoutSymbol
      (fun leftSide head suffix allowed => by
        apply moveRightFromWord returnProgram returnMember head
          (keepAction
            (State.returnAfterExtend (.metricCell metric))
            .right head)
        · cases allowed <;> rfl
        · rfl)
      returnWord
      (sourceLeftBoundary :: processed ++ marker :: rest)
      [activeEnd]
      (by
        intro symbol member
        rcases List.mem_append.mp member with blank | inLayout
        · exact layout_replicate_blank 64 symbol blank
        · exact layout_reverse growthLayout
            (metricLayout_allowed fixed fixedAllowed
              (value + contribution) (reserve - contribution))
            symbol inLayout)
    have returnedLeft :
        returnWord.reverse ++ [activeEnd] =
          nextLayout ++ [activeEnd] := by
      simp only [returnWord, growthLayout, nextLayout,
        nextReserve, metricLayout, List.reverse_append,
        List.reverse_reverse, List.reverse_replicate,
        List.append_assoc]
      rw [replicate_add_word
        (reserve - contribution) 64 cellBlank]
      simp only [List.cons_append, List.append_assoc]
    simpa only [returning, returnedBoundary, returnWord,
      returnedLeft, List.append_assoc] using scan
  let atRestore :=
    configAtWord (State.restoreMetricCursor metric)
      (sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
      (processed ++ marker :: rest)
  have returnBoundary :
      workRunExact? machine 1 returnedBoundary =
        some atRestore := by
    apply exactRun_one
    apply moveRightFromWord returnProgram returnMember
      sourceLeftBoundary
      (keepAction (State.restoreMetricCursor metric)
        .right sourceLeftBoundary)
    · rfl
    · rfl
  let restoredMarker :=
    configAtWord (State.restoreMetricCursor metric)
      (processed.reverse ++
        sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
      (marker :: rest)
  have restore :
      workRunExact? machine processed.length atRestore =
        some restoredMarker := by
    have scan := scanRightExact
      (State.restoreMetricCursor metric)
      TargetEmitter.PackedSymbol
      (fun leftSide head suffix packed => by
        apply moveRightFromWord restoreProgram restoreMember head
          (keepAction (State.restoreMetricCursor metric)
            .right head)
        · cases packed <;> rfl
        · rfl)
      processed (marker :: rest)
      (sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
      processedPacked
    simpa [atRestore, restoredMarker] using scan
  have restoreMarker :
      workRunExact? machine 1 restoredMarker =
        some
          (configAtWord (State.afterMetricCell metric)
            ((processed ++ [current]).reverse ++
              sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
            rest) := by
    apply exactRun_one
    have restoreAction :
        restoreProgram.action marker =
          writeAction (State.afterMetricCell metric)
            current .right := by
      simp [restoreProgram, restoreMetricCursorAction,
        markerPair_original pair]
    have moved := moveRightFromWord restoreProgram
      restoreMember marker
      (writeAction (State.afterMetricCell metric)
        current .right)
      restoreAction
      (processed.reverse ++
        sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
      rest
      rfl
    simpa [restoredMarker, restoreProgram, writeAction,
      List.reverse_append, List.append_assoc] using moved
  have run01 := exactRun_add processed.length 1
    _ atBoundary atParser rewind crossToParser
  have run02 := exactRun_add (processed.length + 1)
    processed.length _ atParser atMarker run01 parsePrefix
  have run03 := exactRun_add
    (processed.length + 1 + processed.length) 1
    _ atMarker afterMarker run02 parseMarker
  have run04 := exactRun_add
    (processed.length + 1 + processed.length + 1)
    processed.length _ afterMarker backAtBoundary
    run03 seekBoundary
  have run05 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length) 1
    _ backAtBoundary atLayout run04 crossToLayout
  have run06 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1) layout.length
    _ atLayout atActive run05 seekActive
  have run07 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length) 1
    _ atActive atSeekSeparator run06 turnAtActive
  have run08 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1) reserve
    _ atSeekSeparator atSeparator run07 seekSeparator
  have run09 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve)
    (2 * contribution + 1)
    _ atSeparator afterGrowth run08 grow
  have run10 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1))
    (reserve - contribution)
    _ afterGrowth atExtendActive run09 seekExtendActive
  have run11 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution))
    1 _ atExtendActive atExtend run10 launchExtend
  have run12 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution) + 1)
    64 _ atExtend returning run11 extend
  have run13 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution) +
        1 + 64)
    returnWord.length _ returning returnedBoundary run12 returnScan
  have run14 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution) +
        1 + 64 + returnWord.length)
    1 _ returnedBoundary atRestore run13 returnBoundary
  have run15 := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution) +
        1 + 64 + returnWord.length + 1)
    processed.length _ atRestore restoredMarker run14 restore
  have complete := exactRun_add
    (processed.length + 1 + processed.length + 1 +
      processed.length + 1 + layout.length + 1 + reserve +
        (2 * contribution + 1) + (reserve - contribution) +
        1 + 64 + returnWord.length + 1 + processed.length)
    1 _ restoredMarker _ run15 restoreMarker
  have stepCount :
      metricCellSteps processed layout reserve contribution =
        processed.length + 1 + processed.length + 1 +
          processed.length + 1 + layout.length + 1 + reserve +
          (2 * contribution + 1) + (reserve - contribution) +
          1 + 64 + returnWord.length + 1 +
          processed.length + 1 := by
    have fitsDifference :
        reserve - contribution + contribution = reserve := by
      omega
    have growthLength : growthLayout.length = layout.length := by
      simp [growthLayout, layout, metricLayout_length]
      omega
    simp only [metricCellSteps, returnWord, List.length_append,
      List.length_replicate, List.length_reverse, growthLength]
    omega
  rw [stepCount]
  exact complete

def metricPassStepsFrom
    (metric : Metric) (fixed processed : List WorkSymbol)
    (position : ParseState) (value reserve : Nat) :
    List WorkSymbol → Nat
  | [] => 1
  | current :: rest =>
      match parseStep metric position current with
      | none => 0
      | some (next, contribution) =>
          1 +
            metricCellSteps processed
              (metricLayout fixed value reserve)
              reserve contribution +
            metricPassStepsFrom metric fixed
              (processed ++ [current]) next
              (value + contribution)
              (reserve - contribution + 64) rest

private def metricFinalReserve
    (processed todo : List WorkSymbol)
    (value contribution : Nat) : Nat :=
  64 * ((processed ++ todo).length + 1) -
    (value + contribution)

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
private theorem metric_pass_after_exact
    (metric : Metric)
    (fixed processed todo suffix : List WorkSymbol)
    (position : ParseState)
    (value reserve contribution : Nat)
    (prefixPath :
      ParsePath metric .versionFirst processed position value)
    (tailPath :
      ParsePath metric position todo .done contribution)
    (capacityEq :
      value + reserve = 64 * (processed.length + 1))
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol) :
    workRunExact? machine
        (metricPassStepsFrom metric fixed processed
          position value reserve todo)
        (configAtWord (State.afterMetricCell metric)
          (processed.reverse ++
            sourceLeftBoundary ::
              (metricLayout fixed value reserve ++ [activeEnd]))
          (todo ++ cellBlank :: suffix)) =
      some
        (configAtLeftWord (State.finishSource metric.phase)
          ((processed ++ todo).reverse ++
            sourceLeftBoundary ::
              (metricLayout fixed (value + contribution)
                (metricFinalReserve processed todo
                  value contribution) ++ [activeEnd]))
          (cellBlank :: suffix)) := by
  generalize finalEq : ParseState.done = final at tailPath
  induction tailPath generalizing processed value reserve with
  | nil position =>
      let program : StateProgram :=
        { state := State.afterMetricCell metric
          action := afterMetricCellAction metric }
      have member : program ∈ statePrograms := by
        exact metricBand_program_mem State.afterMetricCell
          afterMetricCellAction (by simp [stateProgramBands]) metric
      have reserveEq :
          metricFinalReserve processed [] value 0 = reserve := by
        simp [metricFinalReserve]
        omega
      change
        workRunExact? machine 1
            (configAtWord (State.afterMetricCell metric)
              (processed.reverse ++
                sourceLeftBoundary ::
                  (metricLayout fixed value reserve ++ [activeEnd]))
              (cellBlank :: suffix)) =
          some _
      apply exactRun_one
      have blankAction :
          program.action cellBlank =
            keepAction (State.finishSource metric.phase)
              .left cellBlank := by
        rfl
      have moved := moveLeftFromWord program member cellBlank
        (keepAction (State.finishSource metric.phase)
          .left cellBlank)
        blankAction
        (processed.reverse ++
          sourceLeftBoundary ::
            (metricLayout fixed value reserve ++ [activeEnd]))
        suffix rfl
      simpa [program, keepAction, reserveEq,
        List.append_assoc] using moved
  | @cons position next final current rest
      headContribution tailContribution packed step tail
      inductionHypothesis =>
      obtain ⟨marker, pair⟩ := packed_has_marker packed
      let program : StateProgram :=
        { state := State.afterMetricCell metric
          action := afterMetricCellAction metric }
      have member : program ∈ statePrograms := by
        exact metricBand_program_mem State.afterMetricCell
          afterMetricCellAction (by simp [stateProgramBands]) metric
      let layout := metricLayout fixed value reserve
      let afterMark :=
        configAtLeftWord (State.rewindSource metric)
          (processed.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          (marker :: rest ++ cellBlank :: suffix)
      have mark :
          workRunExact? machine 1
              (configAtWord (State.afterMetricCell metric)
                (processed.reverse ++
                  sourceLeftBoundary :: (layout ++ [activeEnd]))
                (current :: rest ++ cellBlank :: suffix)) =
            some afterMark := by
        apply exactRun_one
        have moved := moveLeftFromWord program member current
          (writeAction (State.rewindSource metric)
            marker .left)
          (by simp [program, afterMetricCellAction,
            markerPair_marker pair])
          (processed.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          (rest ++ cellBlank :: suffix) rfl
        simpa [afterMark, program, writeAction,
          List.append_assoc] using moved
      let nextReserve := reserve - headContribution + 64
      let nextLayout :=
        metricLayout fixed (value + headContribution) nextReserve
      let afterCell :=
        configAtWord (State.afterMetricCell metric)
          ((processed ++ [current]).reverse ++
            sourceLeftBoundary :: (nextLayout ++ [activeEnd]))
          (rest ++ cellBlank :: suffix)
      have cell :
          workRunExact? machine
              (metricCellSteps processed layout reserve
                headContribution)
              afterMark =
            some afterCell := by
        simpa [afterMark, afterCell, layout, nextLayout,
          nextReserve, List.append_assoc] using
          metric_cell_exact metric processed
            (rest ++ cellBlank :: suffix) fixed
            position next value reserve headContribution
            current marker prefixPath pair step capacityEq
            fixedAllowed
      have nextPrefix :
          ParsePath metric .versionFirst
            (processed ++ [current]) next
            (value + headContribution) := by
        have currentPath :=
          parsePath_single (markerPair_packed pair) step
        simpa using parsePath_append prefixPath currentPath
      have nextCapacity :
          value + headContribution + nextReserve =
            64 * ((processed ++ [current]).length + 1) := by
        have prefixCapacity := parsePrefix_capacity nextPrefix
        have fits : headContribution ≤ reserve := by
          simp only [List.length_append, List.length_singleton]
            at prefixCapacity
          omega
        simp [nextReserve]
        omega
      have restRun :
          workRunExact? machine
              (metricPassStepsFrom metric fixed
                (processed ++ [current]) next
                (value + headContribution) nextReserve rest)
              afterCell =
            some
              (configAtLeftWord
                (State.finishSource metric.phase)
                (((processed ++ [current]) ++ rest).reverse ++
                  sourceLeftBoundary ::
                    (metricLayout fixed
                      ((value + headContribution) +
                        tailContribution)
                      (metricFinalReserve
                        (processed ++ [current]) rest
                        (value + headContribution)
                        tailContribution) ++ [activeEnd]))
                (cellBlank :: suffix)) := by
        simpa [afterCell, nextLayout] using
          inductionHypothesis
            (processed ++ [current])
            (value + headContribution) nextReserve
            nextPrefix nextCapacity finalEq
      have throughCell := exactRun_add 1
        (metricCellSteps processed layout reserve
          headContribution)
        _ afterMark afterCell mark cell
      have complete := exactRun_add
        (1 + metricCellSteps processed layout reserve
          headContribution)
        (metricPassStepsFrom metric fixed
          (processed ++ [current]) next
          (value + headContribution) nextReserve rest)
        _ afterCell _ throughCell restRun
      rw [metricPassStepsFrom, step]
      simpa only [layout, nextReserve, Nat.add_assoc,
        List.cons_append, List.nil_append, List.append_assoc,
        metricFinalReserve] using complete

private theorem metricPassStepsFrom_positive
    {metric : Metric} {fixed processed word : List WorkSymbol}
    {position final : ParseState} {value reserve contribution : Nat}
    (path :
      ParsePath metric position word final contribution) :
    0 <
      metricPassStepsFrom metric fixed processed
        position value reserve word := by
  cases path with
  | nil position =>
      simp [metricPassStepsFrom]
  | @cons position next final symbol rest
      headContribution tailContribution packed step tail =>
      simp only [metricPassStepsFrom, step]
      exact Nat.add_pos_left
        (Nat.add_pos_left (Nat.zero_lt_succ 0) _) _

private theorem exactRun_same_after_first
    (steps : Nat) (positive : 0 < steps)
    (left right middle : WorkConfiguration)
    (leftStep : workStep? machine left = some middle)
    (rightStep : workStep? machine right = some middle) :
    workRunExact? machine steps left =
      workRunExact? machine steps right := by
  cases steps with
  | zero =>
      contradiction
  | succ remaining =>
      change
        (match workStep? machine left with
         | none => none
         | some next =>
             workRunExact? machine remaining next) =
          (match workStep? machine right with
           | none => none
           | some next =>
               workRunExact? machine remaining next)
      rw [leftStep, rightStep]

def metricPassSteps
    (metric : Metric) (fixed : List WorkSymbol)
    (raw : RawCircuit) : Nat :=
  metricPassStepsFrom metric fixed [] .versionFirst 0 64
    (SourceParser.circuitCells raw)

private theorem metricFinalReserve_circuit
    (raw : RawCircuit) (contribution : Nat) :
    metricFinalReserve [] (SourceParser.circuitCells raw)
        0 contribution =
      slotCapacity raw - contribution := by
  simp [metricFinalReserve, slotCapacity]
  omega

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 1000000 in
private theorem metric_pass_exact
    (metric : Metric) (fixed : List WorkSymbol)
    (raw : RawCircuit)
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol) :
    workRunExact? machine (metricPassSteps metric fixed raw)
        (configAtWord (State.metricBegin metric)
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (SourceParser.circuitCells raw ++ [cellBlank])) =
      some
        (configAtLeftWord (State.finishSource metric.phase)
          ((SourceParser.circuitCells raw).reverse ++
            sourceLeftBoundary ::
              (metricLayout fixed
                (metricContribution metric raw)
                (slotCapacity raw -
                  metricContribution metric raw) ++ [activeEnd]))
          [cellBlank]) := by
  let cells := SourceParser.circuitCells raw
  have path := circuit_parsePath metric raw
  have cellsPacked := parsePath_packed path
  have positive :
      0 <
        metricPassStepsFrom metric fixed [] .versionFirst
          0 64 cells :=
    metricPassStepsFrom_positive path
  have afterRun :=
    metric_pass_after_exact metric fixed [] cells []
      .versionFirst 0 64 (metricContribution metric raw)
      (ParsePath.nil .versionFirst) path
      (by simp) fixedAllowed
  have reserveEq :=
    metricFinalReserve_circuit raw
      (metricContribution metric raw)
  cases cellsEq : cells with
  | nil =>
      have impossible : SourceParser.circuitCells raw = [] := by
        simpa [cells] using cellsEq
      exact False.elim
        (SourceParser.circuitCells_ne_empty raw impossible)
  | cons first rest =>
      have firstPacked : TargetEmitter.PackedSymbol first := by
        have firstMember : first ∈ cells := by
          rw [cellsEq]
          exact List.Mem.head rest
        apply cellsPacked first
        simpa [cells] using firstMember
      obtain ⟨marker, pair⟩ := packed_has_marker firstPacked
      let beginProgram : StateProgram :=
        { state := State.metricBegin metric
          action := metricBeginAction metric }
      let afterProgram : StateProgram :=
        { state := State.afterMetricCell metric
          action := afterMetricCellAction metric }
      have beginMember : beginProgram ∈ statePrograms := by
        exact metricBand_program_mem State.metricBegin
          metricBeginAction (by simp [stateProgramBands]) metric
      have afterMember : afterProgram ∈ statePrograms := by
        exact metricBand_program_mem State.afterMetricCell
          afterMetricCellAction (by simp [stateProgramBands]) metric
      let middle :=
        configAtLeftWord (State.rewindSource metric)
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (marker :: rest ++ [cellBlank])
      have beginStep :
          workStep? machine
              (configAtWord (State.metricBegin metric)
                (sourceLeftBoundary ::
                  (metricLayout fixed 0 64 ++ [activeEnd]))
                (first :: rest ++ [cellBlank])) =
            some middle := by
        have moved := moveLeftFromWord beginProgram beginMember first
          (writeAction (State.rewindSource metric) marker .left)
          (by simp [beginProgram, metricBeginAction,
            markerPair_marker pair])
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (rest ++ [cellBlank]) rfl
        simpa [middle, beginProgram, writeAction,
          List.append_assoc] using moved
      have afterStep :
          workStep? machine
              (configAtWord (State.afterMetricCell metric)
                (sourceLeftBoundary ::
                  (metricLayout fixed 0 64 ++ [activeEnd]))
                (first :: rest ++ [cellBlank])) =
            some middle := by
        have moved := moveLeftFromWord afterProgram afterMember first
          (writeAction (State.rewindSource metric) marker .left)
          (by simp [afterProgram, afterMetricCellAction,
            markerPair_marker pair])
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (rest ++ [cellBlank]) rfl
        simpa [middle, afterProgram, writeAction,
          List.append_assoc] using moved
      have sameRun := exactRun_same_after_first
        (metricPassStepsFrom metric fixed [] .versionFirst
          0 64 cells) positive
        (configAtWord (State.metricBegin metric)
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (cells ++ [cellBlank]))
        (configAtWord (State.afterMetricCell metric)
          (sourceLeftBoundary ::
            (metricLayout fixed 0 64 ++ [activeEnd]))
          (cells ++ [cellBlank]))
        middle
        (by simpa [cellsEq] using beginStep)
        (by simpa [cellsEq] using afterStep)
      have beginRun :
          workRunExact? machine
              (metricPassStepsFrom metric fixed []
                .versionFirst 0 64 cells)
              (configAtWord (State.metricBegin metric)
                (sourceLeftBoundary ::
                  (metricLayout fixed 0 64 ++ [activeEnd]))
                (cells ++ [cellBlank])) =
            some
              (configAtLeftWord
                (State.finishSource metric.phase)
                (cells.reverse ++
                  sourceLeftBoundary ::
                    (metricLayout fixed
                      (metricContribution metric raw)
                      (slotCapacity raw -
                        metricContribution metric raw) ++
                      [activeEnd]))
                [cellBlank]) := by
        rw [sameRun]
        simpa [cells, reserveEq, List.append_assoc] using afterRun
      simpa [metricPassSteps, cells] using beginRun

private theorem metricLayout_eq_append_slotWord
    (fixed : List WorkSymbol) (capacity value : Nat) :
    metricLayout fixed value (capacity - value) =
      fixed ++ slotWord capacity value := by
  simp [metricLayout, slotWord, TargetEmitter.unaryWord,
    unaryUnit, List.append_assoc]

def simpleCellSteps
    (processed layout : List WorkSymbol) : Nat :=
  133 + 2 * processed.length + 2 * layout.length

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem simple_cell_exact
    (phase : SimplePhase)
    (processed layout rest : List WorkSymbol)
    (current marker : WorkSymbol)
    (pair : MarkerPair current marker)
    (processedPacked :
      ∀ symbol, symbol ∈ processed →
        TargetEmitter.PackedSymbol symbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (simpleCellSteps processed layout)
        (configAtWord (State.simpleScan phase)
          (processed.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          (current :: rest)) =
      some
        (configAtWord (State.simpleScan phase)
          ((processed ++ [current]).reverse ++
            sourceLeftBoundary ::
              (layout ++ List.replicate 64 cellBlank ++
                [activeEnd]))
          rest) := by
  let scanProgram : StateProgram :=
    { state := State.simpleScan phase
      action := simpleScanAction phase }
  let seekBoundaryProgram : StateProgram :=
    { state := State.simpleSeekBoundary phase
      action := simpleSeekBoundaryAction phase }
  let seekActiveProgram : StateProgram :=
    { state := State.simpleSeekActive phase
      action := simpleSeekActiveAction phase }
  let restoreProgram : StateProgram :=
    { state := State.simpleRestoreCursor phase
      action := simpleRestoreCursorAction phase }
  let returnProgram : StateProgram :=
    { state := State.returnAfterExtend (.simpleCell phase)
      action := returnAfterExtendAction (.simpleCell phase) }
  have scanMember : scanProgram ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleScan
      simpleScanAction (by simp [stateProgramBands]) phase
  have seekBoundaryMember :
      seekBoundaryProgram ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleSeekBoundary
      simpleSeekBoundaryAction
      (by simp [stateProgramBands]) phase
  have seekActiveMember : seekActiveProgram ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleSeekActive
      simpleSeekActiveAction (by simp [stateProgramBands]) phase
  have restoreMember : restoreProgram ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleRestoreCursor
      simpleRestoreCursorAction
      (by simp [stateProgramBands]) phase
  have returnMember : returnProgram ∈ statePrograms := by
    exact return_program_mem (.simpleCell phase)
  let afterMark :=
    configAtLeftWord (State.simpleSeekBoundary phase)
      (processed.reverse ++
        sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
  have mark :
      workRunExact? machine 1
          (configAtWord (State.simpleScan phase)
            (processed.reverse ++
              sourceLeftBoundary :: (layout ++ [activeEnd]))
            (current :: rest)) =
        some afterMark := by
    apply exactRun_one
    apply moveLeftFromWord scanProgram scanMember current
      (writeAction (State.simpleSeekBoundary phase)
        marker .left)
    · simp [scanProgram, simpleScanAction,
        markerPair_marker pair]
    · rfl
  let atBoundary :=
    configAtLeftWord (State.simpleSeekBoundary phase)
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (processed ++ marker :: rest)
  have seekBoundary :
      workRunExact? machine processed.length afterMark =
        some atBoundary := by
    have scan := scanLeftExact
      (State.simpleSeekBoundary phase)
      TargetEmitter.PackedSymbol
      (fun head leftTail rightSide packed => by
        apply moveLeftFromLeftWord seekBoundaryProgram
          seekBoundaryMember head
          (keepAction (State.simpleSeekBoundary phase)
            .left head)
        · cases packed <;> rfl
        · rfl)
      processed.reverse
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (marker :: rest)
      (by
        intro symbol member
        exact processedPacked symbol
          (List.mem_reverse.mp member))
    simpa [afterMark, atBoundary, List.reverse_reverse,
      List.append_assoc] using scan
  let atLayout :=
    configAtLeftWord (State.simpleSeekActive phase)
      (layout ++ [activeEnd])
      (sourceLeftBoundary :: processed ++ marker :: rest)
  have crossBoundary :
      workRunExact? machine 1 atBoundary = some atLayout := by
    apply exactRun_one
    apply moveLeftFromLeftWord seekBoundaryProgram
      seekBoundaryMember sourceLeftBoundary
      (keepAction (State.simpleSeekActive phase)
        .left sourceLeftBoundary)
    · simp [seekBoundaryProgram, simpleSeekBoundaryAction,
        sourceLeftBoundary, TargetEmitter.sourceLeftBoundary]
    · rfl
  let atActive :=
    configAtLeftWord (State.simpleSeekActive phase)
      [activeEnd]
      (layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have seekActive :
      workRunExact? machine layout.length atLayout =
        some atActive := by
    have scan := scanLeftExact
      (State.simpleSeekActive phase)
      LayoutSymbol
      (fun head leftTail rightSide allowed => by
        apply moveLeftFromLeftWord seekActiveProgram
          seekActiveMember head
          (keepAction (State.simpleSeekActive phase)
            .left head)
        · cases allowed <;> rfl
        · rfl)
      layout [activeEnd]
      (sourceLeftBoundary :: processed ++ marker :: rest)
      layoutAllowed
    simpa [atLayout, atActive, List.append_assoc] using scan
  let atExtend :=
    configAtWord (State.extend (.simpleCell phase) 63) []
      (cellBlank :: cellBlank :: layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have launchExtend :
      workRunExact? machine 1 atActive = some atExtend := by
    apply exactRun_one
    have moved := moveLeftFromLeftWord seekActiveProgram
      seekActiveMember activeEnd
      (writeAction (State.extend (.simpleCell phase) 63)
        cellBlank .left)
      (by simp [seekActiveProgram, simpleSeekActiveAction,
        activeEnd, cellBlank])
      ([] : List WorkSymbol)
      (layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
      rfl
    simpa [atActive, atExtend, seekActiveProgram, writeAction,
      cellBlank, configAtLeftWord,
      configAtWord, TargetEmitter.configAtLeftWord,
      TargetEmitter.configAtWord] using moved
  let returning :=
    configAtWord
      (State.returnAfterExtend (.simpleCell phase))
      [activeEnd]
      (List.replicate 64 cellBlank ++ layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
  have extend :
      workRunExact? machine 64 atExtend = some returning := by
    have extended := extend_exact (.simpleCell phase) 63
      (by decide)
      (cellBlank :: layout.reverse ++
        sourceLeftBoundary :: processed ++ marker :: rest)
    simpa [atExtend, returning, replicate_succ_append,
      List.append_assoc] using extended
  let returnWord :=
    List.replicate 64 cellBlank ++ layout.reverse
  let returnedBoundary :=
    configAtWord
      (State.returnAfterExtend (.simpleCell phase))
      (layout ++ List.replicate 64 cellBlank ++ [activeEnd])
      (sourceLeftBoundary :: processed ++ marker :: rest)
  have returnScan :
      workRunExact? machine returnWord.length returning =
        some returnedBoundary := by
    have scan := scanRightExact
      (State.returnAfterExtend (.simpleCell phase))
      LayoutSymbol
      (fun leftSide head suffix allowed => by
        apply moveRightFromWord returnProgram returnMember head
          (keepAction
            (State.returnAfterExtend (.simpleCell phase))
            .right head)
        · cases allowed <;> rfl
        · rfl)
      returnWord
      (sourceLeftBoundary :: processed ++ marker :: rest)
      [activeEnd]
      (by
        intro symbol member
        rcases List.mem_append.mp member with blank | inLayout
        · exact layout_replicate_blank 64 symbol blank
        · exact layout_reverse layout layoutAllowed symbol inLayout)
    simpa [returning, returnedBoundary, returnWord,
      List.reverse_append, List.reverse_reverse,
      List.reverse_replicate, List.append_assoc] using scan
  let atRestore :=
    configAtWord (State.simpleRestoreCursor phase)
      (sourceLeftBoundary ::
        (layout ++ List.replicate 64 cellBlank ++ [activeEnd]))
      (processed ++ marker :: rest)
  have returnBoundary :
      workRunExact? machine 1 returnedBoundary =
        some atRestore := by
    apply exactRun_one
    apply moveRightFromWord returnProgram returnMember
      sourceLeftBoundary
      (keepAction (State.simpleRestoreCursor phase)
        .right sourceLeftBoundary)
    · simp [returnProgram, returnAfterExtendAction,
        sourceLeftBoundary, TargetEmitter.sourceLeftBoundary]
    · rfl
  let atMarker :=
    configAtWord (State.simpleRestoreCursor phase)
      (processed.reverse ++ sourceLeftBoundary ::
        (layout ++ List.replicate 64 cellBlank ++ [activeEnd]))
      (marker :: rest)
  have restore :
      workRunExact? machine processed.length atRestore =
        some atMarker := by
    have scan := scanRightExact
      (State.simpleRestoreCursor phase)
      TargetEmitter.PackedSymbol
      (fun leftSide head suffix packed => by
        apply moveRightFromWord restoreProgram restoreMember head
          (keepAction (State.simpleRestoreCursor phase)
            .right head)
        · cases packed <;> rfl
        · rfl)
      processed (marker :: rest)
      (sourceLeftBoundary ::
        (layout ++ List.replicate 64 cellBlank ++ [activeEnd]))
      processedPacked
    simpa [atRestore, atMarker, List.append_assoc] using scan
  have restoreMarker :
      workRunExact? machine 1 atMarker =
        some
          (configAtWord (State.simpleScan phase)
            ((processed ++ [current]).reverse ++
              sourceLeftBoundary ::
                (layout ++ List.replicate 64 cellBlank ++
                  [activeEnd]))
            rest) := by
    apply exactRun_one
    have moved := moveRightFromWord restoreProgram restoreMember
      marker
      (writeAction (State.simpleScan phase) current .right)
      (by simp [restoreProgram, simpleRestoreCursorAction,
        markerPair_original pair])
      (processed.reverse ++ sourceLeftBoundary ::
        (layout ++ List.replicate 64 cellBlank ++ [activeEnd]))
      rest rfl
    simpa [atMarker, restoreProgram, writeAction,
      List.reverse_append, List.append_assoc] using moved
  have throughSeek := exactRun_add 1 processed.length
    _ afterMark atBoundary mark seekBoundary
  have throughBoundary := exactRun_add
    (1 + processed.length) 1 _ atBoundary atLayout
    throughSeek crossBoundary
  have throughLayout := exactRun_add
    (1 + processed.length + 1) layout.length
    _ atLayout atActive throughBoundary seekActive
  have throughLaunch := exactRun_add
    (1 + processed.length + 1 + layout.length) 1
    _ atActive atExtend throughLayout launchExtend
  have throughExtend := exactRun_add
    (1 + processed.length + 1 + layout.length + 1) 64
    _ atExtend returning throughLaunch extend
  have throughReturn := exactRun_add
    (1 + processed.length + 1 + layout.length + 1 + 64)
    returnWord.length _ returning returnedBoundary
    throughExtend returnScan
  have throughReturnBoundary := exactRun_add
    (1 + processed.length + 1 + layout.length + 1 + 64 +
      returnWord.length) 1 _ returnedBoundary atRestore
    throughReturn returnBoundary
  have throughRestore := exactRun_add
    (1 + processed.length + 1 + layout.length + 1 + 64 +
      returnWord.length + 1) processed.length
    _ atRestore atMarker throughReturnBoundary restore
  have complete := exactRun_add
    (1 + processed.length + 1 + layout.length + 1 + 64 +
      returnWord.length + 1 + processed.length) 1
    _ atMarker _ throughRestore restoreMarker
  have stepCount :
      simpleCellSteps processed layout =
        1 + processed.length + 1 + layout.length + 1 + 64 +
          returnWord.length + 1 + processed.length + 1 := by
    simp only [simpleCellSteps, returnWord, List.length_append,
      List.length_reverse, List.length_replicate]
    omega
  rw [stepCount]
  exact complete

def growLayout :
    List WorkSymbol → List WorkSymbol → List WorkSymbol
  | layout, [] => layout
  | layout, _symbol :: rest =>
      growLayout
        (layout ++ List.replicate 64 cellBlank) rest

def simplePassSteps :
    List WorkSymbol → List WorkSymbol → List WorkSymbol → Nat
  | _processed, _layout, [] => 0
  | processed, layout, _symbol :: rest =>
      simpleCellSteps processed layout +
        simplePassSteps
          (processed ++ [_symbol])
          (layout ++ List.replicate 64 cellBlank)
          rest

private theorem growLayout_allowed
    (layout word : List WorkSymbol)
    (allowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    ∀ symbol, symbol ∈ growLayout layout word →
      LayoutSymbol symbol := by
  induction word generalizing layout with
  | nil =>
      exact allowed
  | cons head rest ih =>
      apply ih
      intro symbol member
      rcases List.mem_append.mp member with inLayout | inBlanks
      · exact allowed symbol inLayout
      · exact layout_replicate_blank 64 symbol inBlanks

private theorem growLayout_eq_append_replicate
    (layout word : List WorkSymbol) :
    growLayout layout word =
      layout ++
        List.replicate (64 * word.length) cellBlank := by
  induction word generalizing layout with
  | nil =>
      simp [growLayout]
  | cons head rest inductionHypothesis =>
      rw [growLayout, inductionHypothesis]
      rw [List.append_assoc]
      rw [← replicate_add_word]
      congr 2
      simp only [List.length_cons]
      omega

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem simple_pass_exact
    (phase : SimplePhase)
    (processed layout todo suffix : List WorkSymbol)
    (processedPacked :
      ∀ symbol, symbol ∈ processed →
        TargetEmitter.PackedSymbol symbol)
    (todoPacked :
      ∀ symbol, symbol ∈ todo →
        TargetEmitter.PackedSymbol symbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine
        (simplePassSteps processed layout todo)
        (configAtWord (State.simpleScan phase)
          (processed.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          (todo ++ suffix)) =
      some
        (configAtWord (State.simpleScan phase)
          ((processed ++ todo).reverse ++
            sourceLeftBoundary ::
              (growLayout layout todo ++ [activeEnd]))
          suffix) := by
  induction todo generalizing processed layout with
  | nil =>
      simp [simplePassSteps, growLayout, workRunExact?]
  | cons current rest ih =>
      have currentPacked :
          TargetEmitter.PackedSymbol current :=
        todoPacked current (List.Mem.head rest)
      obtain ⟨marker, pair⟩ := packed_has_marker currentPacked
      have restPacked :
          ∀ symbol, symbol ∈ rest →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        exact todoPacked symbol (List.Mem.tail current member)
      have nextProcessedPacked :
          ∀ symbol, symbol ∈ processed ++ [current] →
            TargetEmitter.PackedSymbol symbol := by
        intro symbol member
        rcases List.mem_append.mp member with inProcessed | atCurrent
        · exact processedPacked symbol inProcessed
        · have equal : symbol = current := by
            simpa using atCurrent
          subst symbol
          exact currentPacked
      have nextLayoutAllowed :
          ∀ symbol,
            symbol ∈ layout ++ List.replicate 64 cellBlank →
              LayoutSymbol symbol := by
        intro symbol member
        rcases List.mem_append.mp member with inLayout | inBlanks
        · exact layoutAllowed symbol inLayout
        · exact layout_replicate_blank 64 symbol inBlanks
      let middle :=
        configAtWord (State.simpleScan phase)
          ((processed ++ [current]).reverse ++
            sourceLeftBoundary ::
              (layout ++ List.replicate 64 cellBlank ++
                [activeEnd]))
          (rest ++ suffix)
      have first :
          workRunExact? machine
              (simpleCellSteps processed layout)
              (configAtWord (State.simpleScan phase)
                (processed.reverse ++
                  sourceLeftBoundary :: (layout ++ [activeEnd]))
                (current :: rest ++ suffix)) =
            some middle := by
        simpa [middle, List.append_assoc] using
          simple_cell_exact phase processed layout
            (rest ++ suffix) current marker pair
            processedPacked layoutAllowed
      have second :
          workRunExact? machine
              (simplePassSteps
                (processed ++ [current])
                (layout ++ List.replicate 64 cellBlank)
                rest)
              middle =
            some
              (configAtWord (State.simpleScan phase)
                ((processed ++ current :: rest).reverse ++
                  sourceLeftBoundary ::
                    (growLayout
                      (layout ++ List.replicate 64 cellBlank)
                      rest ++ [activeEnd]))
                suffix) := by
        simpa [middle, List.append_assoc] using
          ih (processed ++ [current])
            (layout ++ List.replicate 64 cellBlank)
            nextProcessedPacked restPacked nextLayoutAllowed
      have complete := exactRun_add
        (simpleCellSteps processed layout)
        (simplePassSteps
          (processed ++ [current])
          (layout ++ List.replicate 64 cellBlank)
          rest)
        _ middle _ first second
      change
        workRunExact? machine
            (simpleCellSteps processed layout +
              simplePassSteps
                (processed ++ [current])
                (layout ++ List.replicate 64 cellBlank)
                rest)
            _ =
          some _
      simpa only [List.cons_append, List.append_assoc,
        growLayout] using complete

def simplePhaseSteps
    (layout : List WorkSymbol) (raw : RawCircuit) : Nat :=
  simplePassSteps [] layout (SourceParser.circuitCells raw) + 1

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem simple_pass_finish_exact
    (phase : SimplePhase) (phaseNotOutput : phase ≠ .outputIndex)
    (layout : List WorkSymbol) (raw : RawCircuit)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (simplePhaseSteps layout raw)
        (configAtWord (State.simpleScan phase)
          (sourceLeftBoundary :: (layout ++ [activeEnd]))
          (SourceParser.circuitCells raw ++ [cellBlank])) =
      some
        (configAtLeftWord
          (State.finishSource phase.phase)
          ((SourceParser.circuitCells raw).reverse ++
            sourceLeftBoundary ::
              (growLayout layout
                (SourceParser.circuitCells raw) ++ [activeEnd]))
          [cellBlank]) := by
  let cells := SourceParser.circuitCells raw
  have cellsPath := circuit_parsePath .inputCount raw
  have cellsPacked := parsePath_packed cellsPath
  let middle :=
    configAtWord (State.simpleScan phase)
      (cells.reverse ++
        sourceLeftBoundary ::
          (growLayout layout cells ++ [activeEnd]))
      [cellBlank]
  have pass :
      workRunExact? machine
          (simplePassSteps [] layout cells)
          (configAtWord (State.simpleScan phase)
            (sourceLeftBoundary :: (layout ++ [activeEnd]))
            (cells ++ [cellBlank])) =
        some middle := by
    simpa [middle, cells, List.append_assoc] using
      simple_pass_exact phase [] layout cells [cellBlank]
        (by
          intro symbol member
          contradiction)
        cellsPacked layoutAllowed
  let program : StateProgram :=
    { state := State.simpleScan phase
      action := simpleScanAction phase }
  have member : program ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleScan
      simpleScanAction (by simp [stateProgramBands]) phase
  have blankAction :
      program.action cellBlank =
        keepAction (State.finishSource phase.phase)
          .left cellBlank := by
    cases phase with
    | scratch => rfl
    | currentGate => rfl
    | outputIndex => exact False.elim (phaseNotOutput rfl)
  have finish :
      workRunExact? machine 1 middle =
        some
          (configAtLeftWord
            (State.finishSource phase.phase)
            (cells.reverse ++
              sourceLeftBoundary ::
                (growLayout layout cells ++ [activeEnd]))
            [cellBlank]) := by
    apply exactRun_one
    have moved := moveLeftFromWord program member cellBlank
      (keepAction (State.finishSource phase.phase)
        .left cellBlank)
      blankAction
      (cells.reverse ++
        sourceLeftBoundary ::
          (growLayout layout cells ++ [activeEnd]))
      ([] : List WorkSymbol) rfl
    simpa [middle, program, keepAction] using moved
  have complete := exactRun_add
    (simplePassSteps [] layout cells) 1
    _ middle _ pass finish
  simpa [simplePhaseSteps, cells] using complete

def outputTargetSteps : Nat := 7

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem output_target_exact
    (source layout : List WorkSymbol) :
    workRunExact? machine outputTargetSteps
        (configAtWord (State.simpleScan .outputIndex)
          (source.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          [cellBlank]) =
      some
        (configAtLeftWord (State.finishSource .outputIndex)
          (source.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          [sourceTargetBoundary,
           cellBlank, cellBlank, cellBlank]) := by
  let sourceLeft :=
    source.reverse ++
      sourceLeftBoundary :: (layout ++ [activeEnd])
  let scanProgram : StateProgram :=
    { state := State.simpleScan .outputIndex
      action := simpleScanAction .outputIndex }
  let blankOneProgram : StateProgram :=
    { state := State.targetBlankOne
      action := targetBlankOneAction }
  let blankTwoProgram : StateProgram :=
    { state := State.targetBlankTwo
      action := targetBlankTwoAction }
  let turnProgram : StateProgram :=
    { state := State.targetTurnLeft
      action := targetTurnLeftAction }
  let seekProgram : StateProgram :=
    { state := State.targetSeekBoundary
      action := targetSeekBoundaryAction }
  have scanMember : scanProgram ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleScan
      simpleScanAction (by simp [stateProgramBands]) .outputIndex
  have blankOneMember : blankOneProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [blankOneProgram, highPrograms]
  have blankTwoMember : blankTwoProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [blankTwoProgram, highPrograms]
  have turnMember : turnProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [turnProgram, highPrograms]
  have seekMember : seekProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [seekProgram, highPrograms]
  let afterBoundary :=
    configAtWord State.targetBlankOne
      (sourceTargetBoundary :: sourceLeft) []
  have writeBoundary :
      workRunExact? machine 1
          (configAtWord (State.simpleScan .outputIndex)
            sourceLeft [cellBlank]) =
        some afterBoundary := by
    apply exactRun_one
    have moved := moveRightFromWord scanProgram scanMember
      cellBlank
      (writeAction State.targetBlankOne
        sourceTargetBoundary .right)
      (by rfl) sourceLeft [] rfl
    simpa [afterBoundary, scanProgram, writeAction] using moved
  let afterBlankOne :=
    configAtWord State.targetBlankTwo
      (cellBlank :: sourceTargetBoundary :: sourceLeft) []
  have blankOne :
      workRunExact? machine 1 afterBoundary =
        some afterBlankOne := by
    apply exactRun_one
    have moved := moveRightFromWord blankOneProgram
      blankOneMember cellBlank
      (keepAction State.targetBlankTwo .right cellBlank)
      (by rfl)
      (sourceTargetBoundary :: sourceLeft) [] rfl
    simpa [afterBoundary, afterBlankOne,
      blankOneProgram, keepAction, configAtWord,
      TargetEmitter.configAtWord, cellBlank] using moved
  let afterBlankTwo :=
    configAtWord State.targetTurnLeft
      (cellBlank :: cellBlank ::
        sourceTargetBoundary :: sourceLeft) []
  have blankTwo :
      workRunExact? machine 1 afterBlankOne =
        some afterBlankTwo := by
    apply exactRun_one
    have moved := moveRightFromWord blankTwoProgram
      blankTwoMember cellBlank
      (keepAction State.targetTurnLeft .right cellBlank)
      (by rfl)
      (cellBlank :: sourceTargetBoundary :: sourceLeft) [] rfl
    simpa [afterBlankOne, afterBlankTwo,
      blankTwoProgram, keepAction, configAtWord,
      TargetEmitter.configAtWord, cellBlank] using moved
  let afterTurn :=
    configAtLeftWord State.targetSeekBoundary
      (cellBlank :: cellBlank ::
        sourceTargetBoundary :: sourceLeft)
      [cellBlank]
  have turn :
      workRunExact? machine 1 afterBlankTwo =
        some afterTurn := by
    apply exactRun_one
    have moved := moveLeftFromWord turnProgram turnMember
      cellBlank
      (keepAction State.targetSeekBoundary .left cellBlank)
      (by rfl)
      (cellBlank :: cellBlank ::
        sourceTargetBoundary :: sourceLeft)
      [] rfl
    simpa [afterBlankTwo, afterTurn,
      turnProgram, keepAction, configAtWord,
      configAtLeftWord, TargetEmitter.configAtWord,
      TargetEmitter.configAtLeftWord, cellBlank] using moved
  let atBoundary :=
    configAtLeftWord State.targetSeekBoundary
      (sourceTargetBoundary :: sourceLeft)
      [cellBlank, cellBlank, cellBlank]
  have seek :
      workRunExact? machine 2 afterTurn =
        some atBoundary := by
    have scanned := scanLeftExact State.targetSeekBoundary
      (fun symbol => symbol = cellBlank)
      (fun head leftTail rightSide equal => by
        subst head
        apply moveLeftFromLeftWord seekProgram seekMember
          cellBlank
          (keepAction State.targetSeekBoundary .left cellBlank)
        · rfl
        · rfl)
      [cellBlank, cellBlank]
      (sourceTargetBoundary :: sourceLeft)
      [cellBlank]
      (by
        intro symbol member
        simp only [List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with equal | equal
        · exact equal
        · exact equal)
    simpa [afterTurn, atBoundary] using scanned
  have crossBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (configAtLeftWord (State.finishSource .outputIndex)
            sourceLeft
            [sourceTargetBoundary,
             cellBlank, cellBlank, cellBlank]) := by
    apply exactRun_one
    apply moveLeftFromLeftWord seekProgram seekMember
      sourceTargetBoundary
      (keepAction (State.finishSource .outputIndex)
        .left sourceTargetBoundary)
    · rfl
    · rfl
  have run01 := exactRun_add 1 1
    _ afterBoundary afterBlankOne writeBoundary blankOne
  have run02 := exactRun_add (1 + 1) 1
    _ afterBlankOne afterBlankTwo run01 blankTwo
  have run03 := exactRun_add (1 + 1 + 1) 1
    _ afterBlankTwo afterTurn run02 turn
  have run04 := exactRun_add (1 + 1 + 1 + 1) 2
    _ afterTurn atBoundary run03 seek
  have complete := exactRun_add
    (1 + 1 + 1 + 1 + 2) 1
    _ atBoundary _ run04 crossBoundary
  change workRunExact? machine 7 _ = some _
  simpa [sourceLeft] using complete

def outputPhaseSteps
    (layout : List WorkSymbol) (raw : RawCircuit) : Nat :=
  simplePassSteps [] layout (SourceParser.circuitCells raw) +
    outputTargetSteps

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem output_pass_finish_exact
    (layout : List WorkSymbol) (raw : RawCircuit)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (outputPhaseSteps layout raw)
        (configAtWord (State.simpleScan .outputIndex)
          (sourceLeftBoundary :: (layout ++ [activeEnd]))
          (SourceParser.circuitCells raw ++ [cellBlank])) =
      some
        (configAtLeftWord (State.finishSource .outputIndex)
          ((SourceParser.circuitCells raw).reverse ++
            sourceLeftBoundary ::
              (growLayout layout
                (SourceParser.circuitCells raw) ++ [activeEnd]))
          [sourceTargetBoundary,
           cellBlank, cellBlank, cellBlank]) := by
  let cells := SourceParser.circuitCells raw
  have cellsPath := circuit_parsePath .inputCount raw
  have cellsPacked := parsePath_packed cellsPath
  let middle :=
    configAtWord (State.simpleScan .outputIndex)
      (cells.reverse ++
        sourceLeftBoundary ::
          (growLayout layout cells ++ [activeEnd]))
      [cellBlank]
  have pass :
      workRunExact? machine
          (simplePassSteps [] layout cells)
          (configAtWord (State.simpleScan .outputIndex)
            (sourceLeftBoundary :: (layout ++ [activeEnd]))
            (cells ++ [cellBlank])) =
        some middle := by
    simpa [middle, cells, List.append_assoc] using
      simple_pass_exact .outputIndex [] layout cells [cellBlank]
        (by
          intro symbol member
          contradiction)
        cellsPacked layoutAllowed
  have target :
      workRunExact? machine outputTargetSteps middle =
        some
          (configAtLeftWord (State.finishSource .outputIndex)
            (cells.reverse ++
              sourceLeftBoundary ::
                (growLayout layout cells ++ [activeEnd]))
            [sourceTargetBoundary,
             cellBlank, cellBlank, cellBlank]) := by
    simpa [middle] using
      output_target_exact cells (growLayout layout cells)
  have complete := exactRun_add
    (simplePassSteps [] layout cells) outputTargetSteps
    _ middle _ pass target
  simpa [outputPhaseSteps, cells] using complete

def baseSteps (baseFixed : List WorkSymbol) : Nat :=
  130 + baseFixed.length

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem base_exact
    (phase : Phase)
    (baseFixed sourceWord : List WorkSymbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ baseFixed → LayoutSymbol symbol) :
    workRunExact? machine (baseSteps baseFixed)
        (configAtWord (State.launchBase phase) []
          (cellBlank :: baseFixed.reverse ++
            sourceLeftBoundary :: sourceWord)) =
      some
        (configAtWord (phaseEntryState phase)
          (sourceLeftBoundary ::
            (baseFixed ++ List.replicate 64 cellBlank ++
              [activeEnd]))
          sourceWord) := by
  let launchProgram : StateProgram :=
    { state := State.launchBase phase
      action := launchBaseAction phase }
  let returnProgram : StateProgram :=
    { state := State.returnAfterExtend (.base phase)
      action := returnAfterExtendAction (.base phase) }
  have launchMember : launchProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.launchBase launchBaseAction
      (by simp [stateProgramBands]) phase
  have returnMember : returnProgram ∈ statePrograms :=
    return_program_mem (.base phase)
  let atExtend :=
    configAtWord (State.extend (.base phase) 63) []
      (cellBlank :: cellBlank :: baseFixed.reverse ++
        sourceLeftBoundary :: sourceWord)
  have launch :
      workRunExact? machine 1
          (configAtWord (State.launchBase phase) []
            (cellBlank :: baseFixed.reverse ++
              sourceLeftBoundary :: sourceWord)) =
        some atExtend := by
    apply exactRun_one
    have moved := moveLeftFromWord launchProgram launchMember
      cellBlank
      (keepAction (State.extend (.base phase) 63)
        .left cellBlank)
      (by rfl)
      ([] : List WorkSymbol)
      (baseFixed.reverse ++ sourceLeftBoundary :: sourceWord)
      rfl
    simpa [atExtend, launchProgram, keepAction,
      cellBlank, configAtLeftWord, configAtWord,
      TargetEmitter.configAtLeftWord,
      TargetEmitter.configAtWord] using moved
  let returning :=
    configAtWord (State.returnAfterExtend (.base phase))
      [activeEnd]
      (List.replicate 64 cellBlank ++ baseFixed.reverse ++
        sourceLeftBoundary :: sourceWord)
  have extend :
      workRunExact? machine 64 atExtend = some returning := by
    have extended := extend_exact (.base phase) 63 (by decide)
      (cellBlank :: baseFixed.reverse ++
        sourceLeftBoundary :: sourceWord)
    simpa [atExtend, returning, replicate_succ_append,
      List.append_assoc] using extended
  let returnWord :=
    List.replicate 64 cellBlank ++ baseFixed.reverse
  let atBoundary :=
    configAtWord (State.returnAfterExtend (.base phase))
      (baseFixed ++ List.replicate 64 cellBlank ++ [activeEnd])
      (sourceLeftBoundary :: sourceWord)
  have returnScan :
      workRunExact? machine returnWord.length returning =
        some atBoundary := by
    have scan := scanRightExact
      (State.returnAfterExtend (.base phase))
      LayoutSymbol
      (fun leftSide head suffix allowed => by
        apply moveRightFromWord returnProgram returnMember head
          (keepAction (State.returnAfterExtend (.base phase))
            .right head)
        · cases allowed <;> rfl
        · rfl)
      returnWord (sourceLeftBoundary :: sourceWord)
      [activeEnd]
      (by
        intro symbol member
        rcases List.mem_append.mp member with blank | inFixed
        · exact layout_replicate_blank 64 symbol blank
        · exact layout_reverse baseFixed layoutAllowed
            symbol inFixed)
    simpa [returning, atBoundary, returnWord,
      List.reverse_append, List.reverse_reverse,
      List.reverse_replicate, List.append_assoc] using scan
  have crossBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (configAtWord (phaseEntryState phase)
            (sourceLeftBoundary ::
              (baseFixed ++ List.replicate 64 cellBlank ++
                [activeEnd]))
            sourceWord) := by
    apply exactRun_one
    apply moveRightFromWord returnProgram returnMember
      sourceLeftBoundary
      (keepAction (phaseEntryState phase) .right
        sourceLeftBoundary)
    · rfl
    · rfl
  have throughExtend := exactRun_add 1 64
    _ atExtend returning launch extend
  have throughReturn := exactRun_add (1 + 64)
    returnWord.length _ returning atBoundary
    throughExtend returnScan
  have complete := exactRun_add
    (1 + 64 + returnWord.length) 1
    _ atBoundary _ throughReturn crossBoundary
  have stepCount :
      baseSteps baseFixed =
        1 + 64 + returnWord.length + 1 := by
    simp only [baseSteps, returnWord, List.length_append,
      List.length_reverse, List.length_replicate]
    omega
  rw [stepCount]
  exact complete

def finishScanSteps
    (source layout : List WorkSymbol) : Nat :=
  source.length + 1 + layout.length

private theorem finish_scan_exact
    (phase : Phase)
    (source layout right : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        TargetEmitter.PackedSymbol symbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (finishScanSteps source layout)
        (configAtLeftWord (State.finishSource phase)
          (source.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          right) =
      some
        (configAtLeftWord (State.finishWorkspace phase)
          [activeEnd]
          (layout.reverse ++ sourceLeftBoundary :: source ++ right)) := by
  let sourceProgram : StateProgram :=
    { state := State.finishSource phase
      action := finishSourceAction phase }
  let workspaceProgram : StateProgram :=
    { state := State.finishWorkspace phase
      action := finishWorkspaceAction phase }
  have sourceMember : sourceProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.finishSource
      finishSourceAction (by simp [stateProgramBands]) phase
  have workspaceMember : workspaceProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.finishWorkspace
      finishWorkspaceAction (by simp [stateProgramBands]) phase
  let atBoundary :=
    configAtLeftWord (State.finishSource phase)
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      (source ++ right)
  have scanSource :
      workRunExact? machine source.length
          (configAtLeftWord (State.finishSource phase)
            (source.reverse ++
              sourceLeftBoundary :: (layout ++ [activeEnd]))
            right) =
        some atBoundary := by
    have scan := scanLeftExact (State.finishSource phase)
      TargetEmitter.PackedSymbol
      (fun head leftTail rightSide packed => by
        apply moveLeftFromLeftWord sourceProgram sourceMember head
          (keepAction (State.finishSource phase) .left head)
        · cases packed <;> rfl
        · rfl)
      source.reverse
      (sourceLeftBoundary :: (layout ++ [activeEnd]))
      right
      (by
        intro symbol member
        exact sourcePacked symbol (List.mem_reverse.mp member))
    simpa [atBoundary, List.reverse_reverse,
      List.append_assoc] using scan
  let atLayout :=
    configAtLeftWord (State.finishWorkspace phase)
      (layout ++ [activeEnd])
      (sourceLeftBoundary :: source ++ right)
  have crossBoundary :
      workRunExact? machine 1 atBoundary = some atLayout := by
    apply exactRun_one
    apply moveLeftFromLeftWord sourceProgram sourceMember
      sourceLeftBoundary
      (keepAction (State.finishWorkspace phase)
        .left sourceLeftBoundary)
    · rfl
    · rfl
  have scanLayout :
      workRunExact? machine layout.length atLayout =
        some
          (configAtLeftWord (State.finishWorkspace phase)
            [activeEnd]
            (layout.reverse ++
              sourceLeftBoundary :: source ++ right)) := by
    have scan := scanLeftExact (State.finishWorkspace phase)
      LayoutSymbol
      (fun head leftTail rightSide allowed => by
        apply moveLeftFromLeftWord workspaceProgram
          workspaceMember head
          (keepAction (State.finishWorkspace phase)
            .left head)
        · cases allowed <;> rfl
        · rfl)
      layout [activeEnd]
      (sourceLeftBoundary :: source ++ right)
      layoutAllowed
    simpa [atLayout, List.append_assoc] using scan
  have throughBoundary := exactRun_add source.length 1
    _ atBoundary atLayout scanSource crossBoundary
  have complete := exactRun_add (source.length + 1)
    layout.length _ atLayout _ throughBoundary scanLayout
  change
    workRunExact? machine
      (source.length + 1 + layout.length) _ = some _
  exact complete

def nextBaseFixed
    (phase : Phase) (layout : List WorkSymbol) :
    List WorkSymbol :=
  if phase == .scratch then
    layout ++ [ledgerBoundary, slotBoundary, slotSeparator]
  else
    layout ++ [slotBoundary, slotSeparator]

def finishLaunchSteps (phase : Phase) : Nat :=
  if phase == .scratch then 3 else 2

private theorem finish_to_launch_exact
    (phase next : Phase) (nextEq : phase.next? = some next)
    (layout source right : List WorkSymbol) :
    workRunExact? machine (finishLaunchSteps phase)
        (configAtLeftWord (State.finishWorkspace phase)
          [activeEnd]
          (layout.reverse ++ sourceLeftBoundary :: source ++ right)) =
      some
        (configAtWord (State.launchBase next) []
          (cellBlank :: (nextBaseFixed phase layout).reverse ++
            sourceLeftBoundary :: source ++ right)) := by
  let workspaceProgram : StateProgram :=
    { state := State.finishWorkspace phase
      action := finishWorkspaceAction phase }
  let prepareProgram : StateProgram :=
    { state := State.prepareSlotSeparator next
      action := prepareSlotSeparatorAction next }
  have workspaceMember : workspaceProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.finishWorkspace
      finishWorkspaceAction (by simp [stateProgramBands]) phase
  have prepareMember : prepareProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.prepareSlotSeparator
      prepareSlotSeparatorAction
      (by simp [stateProgramBands]) next
  by_cases scratchTrue : (phase == .scratch) = true
  · have phaseEq : phase = .scratch := by
      cases phase with
      | scratch => rfl
      | inputCount | normalizedGateCount | carrierWidth |
          baseline | currentGate | outputIndex =>
          contradiction
    subst phase
    simp only [Phase.next?] at nextEq
    cases nextEq
    let scratchProgram : StateProgram :=
      { state := State.prepareScratchSlotBoundary
        action := prepareScratchSlotBoundaryAction }
    have scratchMember : scratchProgram ∈ statePrograms := by
      apply program_mem_of_band
        (show
          ([{ state := State.prepareScratchSlotBoundary,
              action := prepareScratchSlotBoundaryAction }] :
            List StateProgram) ∈ stateProgramBands by
          simp [stateProgramBands])
      simp [scratchProgram]
    let afterActive :=
      configAtLeftWord State.prepareScratchSlotBoundary []
        (ledgerBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
    have activeStep :
        workRunExact? machine 1
            (configAtLeftWord (State.finishWorkspace .scratch)
              [activeEnd]
              (layout.reverse ++
                sourceLeftBoundary :: source ++ right)) =
          some afterActive := by
      apply exactRun_one
      have moved := moveLeftFromLeftWord workspaceProgram
        workspaceMember activeEnd
        (writeAction State.prepareScratchSlotBoundary
          ledgerBoundary .left)
        (by rfl)
        ([] : List WorkSymbol)
        (layout.reverse ++ sourceLeftBoundary :: source ++ right)
        rfl
      simpa [afterActive, workspaceProgram, writeAction,
        configAtLeftWord, TargetEmitter.configAtLeftWord]
        using moved
    let afterScratchBoundary :=
      configAtLeftWord
        (State.prepareSlotSeparator .inputCount) []
        (slotBoundary :: ledgerBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
    have scratchBoundaryStep :
        workRunExact? machine 1 afterActive =
          some afterScratchBoundary := by
      apply exactRun_one
      have moved := moveLeftFromLeftWord scratchProgram
        scratchMember cellBlank
        (writeAction
          (State.prepareSlotSeparator .inputCount)
          slotBoundary .left)
        (by rfl)
        ([] : List WorkSymbol)
        (ledgerBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
        rfl
      simpa [afterActive, afterScratchBoundary,
        scratchProgram, writeAction, cellBlank,
        configAtLeftWord, TargetEmitter.configAtLeftWord]
        using moved
    have separatorStep :
        workRunExact? machine 1 afterScratchBoundary =
          some
            (configAtWord (State.launchBase .inputCount) []
              (cellBlank ::
                (nextBaseFixed .scratch layout).reverse ++
                  sourceLeftBoundary :: source ++ right)) := by
      apply exactRun_one
      have moved := moveLeftFromLeftWord prepareProgram
        prepareMember cellBlank
        (writeAction (State.launchBase .inputCount)
          slotSeparator .left)
        (by rfl)
        ([] : List WorkSymbol)
        (slotBoundary :: ledgerBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
        rfl
      have nextFixed :
          nextBaseFixed .scratch layout =
            layout ++
              [ledgerBoundary, slotBoundary, slotSeparator] := by
        rfl
      simpa [afterScratchBoundary, prepareProgram,
        nextFixed, slotSeparator, writeAction, cellBlank,
        configAtLeftWord, configAtWord,
        TargetEmitter.configAtLeftWord,
        TargetEmitter.configAtWord, List.reverse_append,
        List.append_assoc] using moved
    have throughBoundary := exactRun_add 1 1
      _ afterActive afterScratchBoundary
      activeStep scratchBoundaryStep
    have complete := exactRun_add (1 + 1) 1
      _ afterScratchBoundary _ throughBoundary separatorStep
    have stepCount : finishLaunchSteps .scratch = 3 := by
      rfl
    rw [stepCount]
    exact complete
  · have scratchFalse : (phase == .scratch) = false := by
      cases equality : (phase == .scratch) with
      | false => rfl
      | true => exact False.elim (scratchTrue equality)
    let afterActive :=
      configAtLeftWord (State.prepareSlotSeparator next) []
        (slotBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
    have activeStep :
        workRunExact? machine 1
            (configAtLeftWord (State.finishWorkspace phase)
              [activeEnd]
              (layout.reverse ++
                sourceLeftBoundary :: source ++ right)) =
          some afterActive := by
      apply exactRun_one
      have moved := moveLeftFromLeftWord workspaceProgram
        workspaceMember activeEnd
        (writeAction (State.prepareSlotSeparator next)
          slotBoundary .left)
        (by
          simp [workspaceProgram, finishWorkspaceAction,
            nextEq, scratchFalse, activeEnd])
        ([] : List WorkSymbol)
        (layout.reverse ++ sourceLeftBoundary :: source ++ right)
        rfl
      simpa [afterActive, workspaceProgram, writeAction,
        configAtLeftWord, TargetEmitter.configAtLeftWord]
        using moved
    have separatorStep :
        workRunExact? machine 1 afterActive =
          some
            (configAtWord (State.launchBase next) []
              (cellBlank ::
                (nextBaseFixed phase layout).reverse ++
                  sourceLeftBoundary :: source ++ right)) := by
      apply exactRun_one
      have moved := moveLeftFromLeftWord prepareProgram
        prepareMember cellBlank
        (writeAction (State.launchBase next)
          slotSeparator .left)
        (by rfl)
        ([] : List WorkSymbol)
        (slotBoundary :: layout.reverse ++
          sourceLeftBoundary :: source ++ right)
        rfl
      simpa [afterActive, prepareProgram, nextBaseFixed,
        scratchFalse, slotSeparator, writeAction, cellBlank,
        configAtLeftWord, configAtWord,
        TargetEmitter.configAtLeftWord,
        TargetEmitter.configAtWord, List.reverse_append,
        List.append_assoc] using moved
    have complete := exactRun_add 1 1
      _ afterActive _ activeStep separatorStep
    have stepCount : finishLaunchSteps phase = 2 := by
      simp [finishLaunchSteps, scratchFalse]
    rw [stepCount]
    exact complete

private theorem nextBaseFixed_allowed
    (phase : Phase) (layout : List WorkSymbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    ∀ symbol, symbol ∈ nextBaseFixed phase layout →
      LayoutSymbol symbol := by
  intro symbol member
  by_cases scratch : (phase == .scratch) = true
  · rw [nextBaseFixed, if_pos scratch] at member
    rcases List.mem_append.mp member with inLayout | inSuffix
    · exact layoutAllowed symbol inLayout
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at inSuffix
      rcases inSuffix with equal | equal | equal
      · subst symbol
        exact .ledgerBoundary
      · subst symbol
        exact .slotBoundary
      · subst symbol
        exact .unarySeparator
  · have scratchFalse : (phase == .scratch) = false := by
      cases equality : (phase == .scratch) with
      | false => rfl
      | true => exact False.elim (scratch equality)
    have fixedEq :
        nextBaseFixed phase layout =
          layout ++ [slotBoundary, slotSeparator] := by
      simp [nextBaseFixed, scratchFalse]
    rw [fixedEq] at member
    rcases List.mem_append.mp member with inLayout | inSuffix
    · exact layoutAllowed symbol inLayout
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at inSuffix
      rcases inSuffix with equal | equal
      · subst symbol
        exact .slotBoundary
      · subst symbol
        exact .unarySeparator

def phaseTransitionSteps
    (phase : Phase) (source layout : List WorkSymbol) : Nat :=
  finishScanSteps source layout +
    finishLaunchSteps phase +
    baseSteps (nextBaseFixed phase layout)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem phase_transition_exact
    (phase next : Phase) (nextEq : phase.next? = some next)
    (source layout right : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        TargetEmitter.PackedSymbol symbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine
        (phaseTransitionSteps phase source layout)
        (configAtLeftWord (State.finishSource phase)
          (source.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          right) =
      some
        (configAtWord (phaseEntryState next)
          (sourceLeftBoundary ::
            (nextBaseFixed phase layout ++
              List.replicate 64 cellBlank ++ [activeEnd]))
          (source ++ right)) := by
  let atWorkspace :=
    configAtLeftWord (State.finishWorkspace phase)
      [activeEnd]
      (layout.reverse ++ sourceLeftBoundary :: source ++ right)
  have finish :
      workRunExact? machine (finishScanSteps source layout)
          (configAtLeftWord (State.finishSource phase)
            (source.reverse ++
              sourceLeftBoundary :: (layout ++ [activeEnd]))
            right) =
        some atWorkspace := by
    simpa [atWorkspace] using
      finish_scan_exact phase source layout right
        sourcePacked layoutAllowed
  let atLaunch :=
    configAtWord (State.launchBase next) []
      (cellBlank :: (nextBaseFixed phase layout).reverse ++
        sourceLeftBoundary :: source ++ right)
  have launch :
      workRunExact? machine (finishLaunchSteps phase)
          atWorkspace =
        some atLaunch := by
    simpa [atWorkspace, atLaunch] using
      finish_to_launch_exact phase next nextEq layout source right
  have base :
      workRunExact? machine
          (baseSteps (nextBaseFixed phase layout))
          atLaunch =
        some
          (configAtWord (phaseEntryState next)
            (sourceLeftBoundary ::
              (nextBaseFixed phase layout ++
                List.replicate 64 cellBlank ++ [activeEnd]))
            (source ++ right)) := by
    simpa [atLaunch] using
      base_exact next (nextBaseFixed phase layout)
        (source ++ right)
        (nextBaseFixed_allowed phase layout layoutAllowed)
  have throughLaunch := exactRun_add
    (finishScanSteps source layout)
    (finishLaunchSteps phase)
    _ atWorkspace atLaunch finish launch
  have complete := exactRun_add
    (finishScanSteps source layout +
      finishLaunchSteps phase)
    (baseSteps (nextBaseFixed phase layout))
    _ atLaunch _ throughLaunch base
  simpa [phaseTransitionSteps, Nat.add_assoc] using complete

def finalWorkspaceSteps (layout : List WorkSymbol) : Nat :=
  layout.length + 4

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem final_workspace_exact
    (layout source target : List WorkSymbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (finalWorkspaceSteps layout)
        (configAtLeftWord (State.finishWorkspace .outputIndex)
          [activeEnd]
          (layout.reverse ++
            sourceLeftBoundary :: source ++ target)) =
      some
        (configAtWord State.accept
          (sourceLeftBoundary ::
            (layout ++ [stackBoundary, cellBlank]))
          (source ++ target)) := by
  let workspaceProgram : StateProgram :=
    { state := State.finishWorkspace .outputIndex
      action := finishWorkspaceAction .outputIndex }
  let outsideProgram : StateProgram :=
    { state := State.stackOutsideBlank
      action := stackOutsideBlankAction }
  let returnProgram : StateProgram :=
    { state := State.finalReturnWorkspace
      action := finalReturnWorkspaceAction }
  have workspaceMember : workspaceProgram ∈ statePrograms := by
    exact phaseBand_program_mem State.finishWorkspace
      finishWorkspaceAction
      (by simp [stateProgramBands]) .outputIndex
  have outsideMember : outsideProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [outsideProgram, highPrograms]
  have returnMember : returnProgram ∈ statePrograms := by
    apply program_mem_of_band
      (show highPrograms ∈ stateProgramBands by
        simp [stateProgramBands])
    simp [returnProgram, highPrograms]
  let atOutside :=
    configAtLeftWord State.stackOutsideBlank []
      (stackBoundary :: layout.reverse ++
        sourceLeftBoundary :: source ++ target)
  have installStack :
      workRunExact? machine 1
          (configAtLeftWord
            (State.finishWorkspace .outputIndex)
            [activeEnd]
            (layout.reverse ++
              sourceLeftBoundary :: source ++ target)) =
        some atOutside := by
    apply exactRun_one
    have moved := moveLeftFromLeftWord workspaceProgram
      workspaceMember activeEnd
      (writeAction State.stackOutsideBlank
        stackBoundary .left)
      (by rfl) [] (layout.reverse ++
        sourceLeftBoundary :: source ++ target) rfl
    simpa [atOutside, workspaceProgram, writeAction,
      List.append_assoc] using moved
  let atStack :=
    configAtWord State.finalReturnWorkspace [cellBlank]
      (stackBoundary :: layout.reverse ++
        sourceLeftBoundary :: source ++ target)
  have retainOutside :
      workRunExact? machine 1 atOutside =
        some atStack := by
    apply exactRun_one
    have moved := moveRightFromWord outsideProgram
      outsideMember cellBlank
      (keepAction State.finalReturnWorkspace
        .right cellBlank)
      (by rfl) []
      (stackBoundary :: layout.reverse ++
        sourceLeftBoundary :: source ++ target) rfl
    simpa [atOutside, atStack, outsideProgram, keepAction,
      configAtWord, configAtLeftWord,
      TargetEmitter.configAtWord,
      TargetEmitter.configAtLeftWord, cellBlank] using moved
  let returnWord := stackBoundary :: layout.reverse
  let atBoundary :=
    configAtWord State.finalReturnWorkspace
      (layout ++ [stackBoundary, cellBlank])
      (sourceLeftBoundary :: source ++ target)
  have returnScan :
      workRunExact? machine returnWord.length atStack =
        some atBoundary := by
    have scan := scanRightExact State.finalReturnWorkspace
      (fun symbol =>
        symbol = stackBoundary ∨ LayoutSymbol symbol)
      (fun leftSide head suffix allowed => by
        apply moveRightFromWord returnProgram returnMember head
          (keepAction State.finalReturnWorkspace .right head)
        · rcases allowed with equal | isLayout
          · subst head
            rfl
          · cases isLayout <;> rfl
        · rfl)
      returnWord
      (sourceLeftBoundary :: source ++ target)
      [cellBlank]
      (by
        intro symbol member
        rcases List.mem_cons.mp member with equal | inLayout
        · exact Or.inl equal
        · exact Or.inr
            (layout_reverse layout layoutAllowed symbol inLayout))
    simpa [atStack, atBoundary, returnWord,
      List.reverse_cons, List.reverse_reverse,
      List.append_assoc] using scan
  have crossBoundary :
      workRunExact? machine 1 atBoundary =
        some
          (configAtWord State.accept
            (sourceLeftBoundary ::
              (layout ++ [stackBoundary, cellBlank]))
            (source ++ target)) := by
    apply exactRun_one
    have moved := moveRightFromWord returnProgram returnMember
      sourceLeftBoundary
      (keepAction State.accept .right sourceLeftBoundary)
      (by rfl)
      (layout ++ [stackBoundary, cellBlank])
      (source ++ target) rfl
    simpa [atBoundary, returnProgram, keepAction,
      List.append_assoc] using moved
  have run01 := exactRun_add 1 1
    _ atOutside atStack installStack retainOutside
  have run02 := exactRun_add (1 + 1) returnWord.length
    _ atStack atBoundary run01 returnScan
  have complete := exactRun_add
    (1 + 1 + returnWord.length) 1
    _ atBoundary _ run02 crossBoundary
  have stepCount :
      finalWorkspaceSteps layout =
        1 + 1 + returnWord.length + 1 := by
    simp [finalWorkspaceSteps, returnWord]
    omega
  rw [stepCount]
  exact complete

def finalPhaseSteps
    (source layout : List WorkSymbol) : Nat :=
  finishScanSteps source layout + finalWorkspaceSteps layout

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 1000000 in
private theorem final_phase_exact
    (source layout target : List WorkSymbol)
    (sourcePacked :
      ∀ symbol, symbol ∈ source →
        TargetEmitter.PackedSymbol symbol)
    (layoutAllowed :
      ∀ symbol, symbol ∈ layout → LayoutSymbol symbol) :
    workRunExact? machine (finalPhaseSteps source layout)
        (configAtLeftWord (State.finishSource .outputIndex)
          (source.reverse ++
            sourceLeftBoundary :: (layout ++ [activeEnd]))
          target) =
      some
        (configAtWord State.accept
          (sourceLeftBoundary ::
            (layout ++ [stackBoundary, cellBlank]))
          (source ++ target)) := by
  let atWorkspace :=
    configAtLeftWord (State.finishWorkspace .outputIndex)
      [activeEnd]
      (layout.reverse ++ sourceLeftBoundary :: source ++ target)
  have finish :
      workRunExact? machine (finishScanSteps source layout)
          (configAtLeftWord (State.finishSource .outputIndex)
            (source.reverse ++
              sourceLeftBoundary :: (layout ++ [activeEnd]))
            target) =
        some atWorkspace := by
    simpa [atWorkspace] using
      finish_scan_exact .outputIndex source layout target
        sourcePacked layoutAllowed
  have close :
      workRunExact? machine (finalWorkspaceSteps layout)
          atWorkspace =
        some
          (configAtWord State.accept
            (sourceLeftBoundary ::
              (layout ++ [stackBoundary, cellBlank]))
            (source ++ target)) := by
    simpa [atWorkspace] using
      final_workspace_exact layout source target layoutAllowed
  have complete := exactRun_add
    (finishScanSteps source layout)
    (finalWorkspaceSteps layout)
    _ atWorkspace _ finish close
  simpa [finalPhaseSteps] using complete

/-! ### Canonical entry and exact physical endpoint -/

def entryConfiguration (raw : RawCircuit) : WorkConfiguration :=
  { state := machine.startState
    tape :=
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape }

def bootSteps : Nat := 3

private theorem boot_exact (raw : RawCircuit) :
    workRunExact? machine bootSteps (entryConfiguration raw) =
      some
        (configAtWord (State.launchBase .scratch) []
          (cellBlank :: [unarySeparator].reverse ++
            sourceLeftBoundary ::
              (SourceParser.circuitCells raw ++ [cellBlank]))) := by
  let cells := SourceParser.circuitCells raw
  have path := circuit_parsePath .inputCount raw
  have cellsPacked := parsePath_packed path
  cases cellsEq : cells with
  | nil =>
      have impossible : SourceParser.circuitCells raw = [] := by
        simpa [cells] using cellsEq
      exact False.elim
        (SourceParser.circuitCells_ne_empty raw impossible)
  | cons first rest =>
      have firstPacked : TargetEmitter.PackedSymbol first := by
        have firstMember : first ∈ cells := by
          rw [cellsEq]
          exact List.Mem.head rest
        exact cellsPacked first (by simpa [cells] using firstMember)
      let bootProgram : StateProgram :=
        { state := State.boot, action := bootAction }
      let boundaryProgram : StateProgram :=
        { state := State.installBoundary,
          action := installBoundaryAction }
      let scratchProgram : StateProgram :=
        { state := State.installScratchSeparator,
          action := installScratchSeparatorAction }
      have bootMember : bootProgram ∈ statePrograms := by
        apply program_mem_of_band
          (show lowPrograms ∈ stateProgramBands by
            simp [stateProgramBands])
        simp [bootProgram, lowPrograms]
      have boundaryMember : boundaryProgram ∈ statePrograms := by
        apply program_mem_of_band
          (show lowPrograms ∈ stateProgramBands by
            simp [stateProgramBands])
        simp [boundaryProgram, lowPrograms]
      have scratchMember : scratchProgram ∈ statePrograms := by
        apply program_mem_of_band
          (show lowPrograms ∈ stateProgramBands by
            simp [stateProgramBands])
        simp [scratchProgram, lowPrograms]
      let afterBoot :=
        configAtLeftWord State.installBoundary [cellBlank]
          (first :: rest ++ [cellBlank])
      have boot :
          workRunExact? machine 1 (entryConfiguration raw) =
            some afterBoot := by
        apply exactRun_one
        have moved := moveLeftFromWord bootProgram bootMember first
          (keepAction State.installBoundary .left first)
          (by simp [bootProgram, bootAction,
            isPacked_eq_true_of_packed firstPacked])
          [cellBlank] (rest ++ [cellBlank]) rfl
        simpa [entryConfiguration,
          TargetEmitterGrammarScanner.acceptedConfiguration,
          SourceParser.acceptedTape, cells, cellsEq,
          afterBoot, bootProgram, keepAction,
          machine, cellBlank, SourceParser.cellBlank,
          configAtWord, TargetEmitter.configAtWord,
          List.append_assoc] using moved
      let afterBoundary :=
        configAtLeftWord State.installScratchSeparator []
          (sourceLeftBoundary :: first :: rest ++ [cellBlank])
      have boundary :
          workRunExact? machine 1 afterBoot =
            some afterBoundary := by
        apply exactRun_one
        have moved := moveLeftFromLeftWord boundaryProgram
          boundaryMember cellBlank
          (writeAction State.installScratchSeparator
            sourceLeftBoundary .left)
          (by rfl) []
          (first :: rest ++ [cellBlank]) rfl
        simpa [afterBoot, afterBoundary,
          boundaryProgram, writeAction] using moved
      have scratch :
          workRunExact? machine 1 afterBoundary =
            some
              (configAtWord (State.launchBase .scratch) []
                (cellBlank :: [unarySeparator].reverse ++
                  sourceLeftBoundary ::
                    (first :: rest ++ [cellBlank]))) := by
        apply exactRun_one
        have moved := moveLeftFromWord scratchProgram
          scratchMember cellBlank
          (writeAction (State.launchBase .scratch)
            unarySeparator .left)
          (by rfl) []
          (sourceLeftBoundary :: first :: rest ++ [cellBlank]) rfl
        simpa [afterBoundary, scratchProgram, writeAction,
          configAtWord, configAtLeftWord,
          TargetEmitter.configAtWord,
          TargetEmitter.configAtLeftWord, cellBlank,
          List.append_assoc] using moved
      have throughBoundary := exactRun_add 1 1
        _ afterBoot afterBoundary boot boundary
      have complete := exactRun_add (1 + 1) 1
        _ afterBoundary _ throughBoundary scratch
      change workRunExact? machine 3 (entryConfiguration raw) =
        some _
      simpa [cells, cellsEq, List.append_assoc] using complete

def finalTape (raw : RawCircuit) : WorkTape :=
  match SourceParser.circuitCells raw with
  | [] =>
      { left :=
          ledgerLeftWorkspace (slotCapacity raw)
            (ledgerRegisters raw) [cellBlank]
        head := cellBlank
        right :=
          [sourceTargetBoundary, cellBlank, cellBlank, cellBlank] }
  | first :: rest =>
      { left :=
          ledgerLeftWorkspace (slotCapacity raw)
            (ledgerRegisters raw) [cellBlank]
        head := first
        right :=
          rest ++
            [sourceTargetBoundary, cellBlank, cellBlank, cellBlank] }

def finalConfiguration (raw : RawCircuit) : WorkConfiguration :=
  { state := machine.acceptState
    tape := finalTape raw }

theorem entryConfiguration_is_scanner_tape
    (raw : RawCircuit) :
    (entryConfiguration raw).tape =
      (TargetEmitterGrammarScanner.acceptedConfiguration raw).tape := by
  rfl

theorem finalConfiguration_state (raw : RawCircuit) :
    (finalConfiguration raw).state = machine.acceptState := by
  rfl

theorem finalConfiguration_halted (raw : RawCircuit) :
    machine.isHalted (finalConfiguration raw) = true := by
  rfl

theorem finalConfiguration_left (raw : RawCircuit) :
    (finalConfiguration raw).tape.left =
      ledgerLeftWorkspace (slotCapacity raw)
        (ledgerRegisters raw) [cellBlank] := by
  unfold finalConfiguration finalTape
  cases cellsEq : SourceParser.circuitCells raw <;> rfl

theorem finalConfiguration_source_and_blank_target
    (raw : RawCircuit) :
    let cells := SourceParser.circuitCells raw
    match cells with
    | [] =>
        (finalConfiguration raw).tape.head = cellBlank ∧
        (finalConfiguration raw).tape.right =
          [sourceTargetBoundary, cellBlank, cellBlank, cellBlank]
    | first :: rest =>
        (finalConfiguration raw).tape.head = first ∧
        (finalConfiguration raw).tape.right =
          rest ++
            [sourceTargetBoundary, cellBlank, cellBlank, cellBlank] := by
  dsimp only
  cases cellsEq : SourceParser.circuitCells raw with
  | nil =>
      simp [finalConfiguration, finalTape, cellsEq]
  | cons first rest =>
      simp [finalConfiguration, finalTape, cellsEq]

/-! ### Canonical phase layouts -/

def scratchReserveLayout (raw : RawCircuit) : List WorkSymbol :=
  zeroScratchReserve (slotCapacity raw)

def inputCountLayout (raw : RawCircuit) : List WorkSymbol :=
  scratchReserveLayout raw ++ [ledgerBoundary] ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).inputCount

def normalizedGateCountLayout
    (raw : RawCircuit) : List WorkSymbol :=
  inputCountLayout raw ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).normalizedGateCount

def carrierWidthLayout (raw : RawCircuit) : List WorkSymbol :=
  normalizedGateCountLayout raw ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).carrierWidth

def baselineLayout (raw : RawCircuit) : List WorkSymbol :=
  carrierWidthLayout raw ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).baseline

def currentGateLayout (raw : RawCircuit) : List WorkSymbol :=
  baselineLayout raw ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).currentGate

def outputIndexLayout (raw : RawCircuit) : List WorkSymbol :=
  currentGateLayout raw ++
    slotWord (slotCapacity raw)
      (ledgerRegisters raw).outputIndex

private theorem zeroScratchReserve_allowed (capacity : Nat) :
    ∀ symbol, symbol ∈ zeroScratchReserve capacity →
      LayoutSymbol symbol := by
  intro symbol member
  change
    symbol ∈ unarySeparator ::
      List.replicate capacity cellBlank at member
  simp only [List.mem_cons] at member
  rcases member with equal | inBlanks
  · subst symbol
    exact .unarySeparator
  · exact layout_replicate_blank capacity symbol inBlanks

private theorem slotWord_allowed (capacity value : Nat) :
    ∀ symbol, symbol ∈ slotWord capacity value →
      LayoutSymbol symbol := by
  intro symbol member
  have normalized :
      slotWord capacity value =
      slotBoundary ::
        (List.replicate value unaryUnit ++
          slotSeparator ::
            List.replicate (capacity - value) cellBlank) := by
    simp [slotWord, TargetEmitter.unaryWord, unaryUnit,
      List.append_assoc]
  rw [normalized] at member
  simp only [List.mem_cons] at member
  rcases member with equal | member
  · subst symbol
    exact .slotBoundary
  · rcases List.mem_append.mp member with inUnits | member
    · have equal := List.eq_of_mem_replicate inUnits
      subst symbol
      exact .unaryUnit
    · simp only [List.mem_cons] at member
      rcases member with equal | inBlanks
      · subst symbol
        exact .unarySeparator
      · exact layout_replicate_blank
          (capacity - value) symbol inBlanks

private theorem append_layout_allowed
    (left right : List WorkSymbol)
    (leftAllowed :
      ∀ symbol, symbol ∈ left → LayoutSymbol symbol)
    (rightAllowed :
      ∀ symbol, symbol ∈ right → LayoutSymbol symbol) :
    ∀ symbol, symbol ∈ left ++ right →
      LayoutSymbol symbol := by
  intro symbol member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact leftAllowed symbol inLeft
  · exact rightAllowed symbol inRight

private theorem scratchReserveLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ scratchReserveLayout raw →
      LayoutSymbol symbol :=
  zeroScratchReserve_allowed (slotCapacity raw)

private theorem inputCountLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ inputCountLayout raw →
      LayoutSymbol symbol := by
  apply append_layout_allowed
  · apply append_layout_allowed
    · exact scratchReserveLayout_allowed raw
    · intro symbol member
      simp only [List.mem_singleton] at member
      subst symbol
      exact .ledgerBoundary
  · exact slotWord_allowed _ _

private theorem normalizedGateCountLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ normalizedGateCountLayout raw →
      LayoutSymbol symbol :=
  append_layout_allowed _ _
    (inputCountLayout_allowed raw) (slotWord_allowed _ _)

private theorem carrierWidthLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ carrierWidthLayout raw →
      LayoutSymbol symbol :=
  append_layout_allowed _ _
    (normalizedGateCountLayout_allowed raw) (slotWord_allowed _ _)

private theorem baselineLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ baselineLayout raw →
      LayoutSymbol symbol :=
  append_layout_allowed _ _
    (carrierWidthLayout_allowed raw) (slotWord_allowed _ _)

private theorem currentGateLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ currentGateLayout raw →
      LayoutSymbol symbol :=
  append_layout_allowed _ _
    (baselineLayout_allowed raw) (slotWord_allowed _ _)

private theorem outputIndexLayout_allowed (raw : RawCircuit) :
    ∀ symbol, symbol ∈ outputIndexLayout raw →
      LayoutSymbol symbol :=
  append_layout_allowed _ _
    (currentGateLayout_allowed raw) (slotWord_allowed _ _)

private theorem scratch_grow_eq (raw : RawCircuit) :
    growLayout
        ([unarySeparator] ++
          List.replicate 64 cellBlank)
        (SourceParser.circuitCells raw) =
      scratchReserveLayout raw := by
  rw [growLayout_eq_append_replicate]
  have capacityEq :
      slotCapacity raw =
        64 + 64 * (SourceParser.circuitCells raw).length := by
    simp [slotCapacity]
    omega
  rw [scratchReserveLayout, zeroScratchReserve, capacityEq,
    replicate_add_word]
  simp

private theorem metric_entry_layout
    (fixed : List WorkSymbol) :
    fixed ++ [slotBoundary, slotSeparator] ++
        List.replicate 64 cellBlank =
      metricLayout fixed 0 64 := by
  simp [metricLayout, List.append_assoc]

private theorem zero_slot_grow_eq
    (fixed : List WorkSymbol) (raw : RawCircuit) :
    growLayout
        (fixed ++ [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank)
        (SourceParser.circuitCells raw) =
      fixed ++ slotWord (slotCapacity raw) 0 := by
  rw [growLayout_eq_append_replicate]
  have slotZeroEq :
      fixed ++ slotWord (slotCapacity raw) 0 =
        fixed ++ [slotBoundary, slotSeparator] ++
          List.replicate (slotCapacity raw) cellBlank := by
    simp [slotWord, TargetEmitter.unaryWord,
      List.append_assoc]
  rw [slotZeroEq]
  have capacityEq :
      slotCapacity raw =
        64 + 64 * (SourceParser.circuitCells raw).length := by
    simp [slotCapacity]
    omega
  rw [capacityEq, replicate_add_word]
  simp [List.append_assoc]

private def metricSlot : Metric → Slot
  | .inputCount => .inputCount
  | .normalizedGateCount => .normalizedGateCount
  | .carrierWidth => .carrierWidth
  | .baseline => .baseline

set_option maxHeartbeats 1000000 in
private theorem metric_pass_canonical_exact
    (metric : Metric) (fixed : List WorkSymbol)
    (raw : RawCircuit)
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol) :
    workRunExact? machine (metricPassSteps metric fixed raw)
        (configAtWord (State.metricBegin metric)
          (sourceLeftBoundary ::
            (fixed ++ [slotBoundary, slotSeparator] ++
              List.replicate 64 cellBlank ++ [activeEnd]))
          (SourceParser.circuitCells raw ++ [cellBlank])) =
      some
        (configAtLeftWord (State.finishSource metric.phase)
          ((SourceParser.circuitCells raw).reverse ++
            sourceLeftBoundary ::
              (fixed ++
                slotWord (slotCapacity raw)
                  (slotValue (ledgerRegisters raw)
                    (metricSlot metric)) ++ [activeEnd]))
          [cellBlank]) := by
  have exactRun := metric_pass_exact metric fixed raw fixedAllowed
  rw [← metric_entry_layout fixed] at exactRun
  rw [metricContribution_eq_slotValue metric raw] at exactRun
  rw [metricLayout_eq_append_slotWord] at exactRun
  simpa [metricSlot, List.append_assoc] using exactRun

theorem outputIndexLayout_eq_slotBank (raw : RawCircuit) :
    outputIndexLayout raw =
      scratchReserveLayout raw ++
        (ledgerBoundary ::
          slotBank (slotCapacity raw) (ledgerRegisters raw)) := by
  simp [outputIndexLayout, currentGateLayout, baselineLayout,
    carrierWidthLayout, normalizedGateCountLayout,
    inputCountLayout, slotBank, Slot.all,
    slotValue, List.append_assoc]

theorem outputIndexLayout_with_stack
    (raw : RawCircuit) :
    outputIndexLayout raw ++ [stackBoundary] =
      scratchReserveLayout raw ++
        ledgerWord (slotCapacity raw) (ledgerRegisters raw) := by
  rw [outputIndexLayout_eq_slotBank]
  simp [ledgerWord, List.append_assoc]

def scratchInitialLayout : List WorkSymbol :=
  [unarySeparator] ++ List.replicate 64 cellBlank

def currentGateInitialLayout
    (raw : RawCircuit) : List WorkSymbol :=
  baselineLayout raw ++ [slotBoundary, slotSeparator] ++
    List.replicate 64 cellBlank

def outputIndexInitialLayout
    (raw : RawCircuit) : List WorkSymbol :=
  currentGateLayout raw ++ [slotBoundary, slotSeparator] ++
    List.replicate 64 cellBlank

private theorem scratchInitialLayout_allowed :
    ∀ symbol, symbol ∈ scratchInitialLayout →
      LayoutSymbol symbol := by
  intro symbol member
  simp only [scratchInitialLayout, List.mem_append] at member
  rcases member with inSeparator | inBlanks
  · have equal : symbol = unarySeparator := by
      simpa using inSeparator
    subst symbol
    exact .unarySeparator
  · exact layout_replicate_blank 64 symbol inBlanks

private theorem metricInitialLayout_allowed
    (fixed : List WorkSymbol)
    (fixedAllowed :
      ∀ symbol, symbol ∈ fixed → LayoutSymbol symbol) :
    ∀ symbol,
      symbol ∈
        fixed ++ [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank →
      LayoutSymbol symbol := by
  intro symbol member
  rcases List.mem_append.mp member with inPrefix | inBlanks
  · rcases List.mem_append.mp inPrefix with inFixed | inMarkers
    · exact fixedAllowed symbol inFixed
    · simp only [List.mem_cons, List.not_mem_nil,
        or_false] at inMarkers
      rcases inMarkers with equal | equal
      · subst symbol
        exact .slotBoundary
      · subst symbol
        exact .unarySeparator
  · exact layout_replicate_blank 64 symbol inBlanks

private theorem finalConfiguration_eq_canonicalWord
    (raw : RawCircuit) :
    configAtWord State.accept
        (ledgerLeftWorkspace (slotCapacity raw)
          (ledgerRegisters raw) [cellBlank])
        (SourceParser.circuitCells raw ++
          [sourceTargetBoundary,
           cellBlank, cellBlank, cellBlank]) =
      finalConfiguration raw := by
  cases cellsEq : SourceParser.circuitCells raw with
  | nil =>
      exact False.elim
        (SourceParser.circuitCells_ne_empty raw cellsEq)
  | cons first rest =>
      simp [configAtWord, TargetEmitter.configAtWord,
        finalConfiguration, finalTape, cellsEq,
        machine]

def workSteps (raw : RawCircuit) : Nat :=
  bootSteps +
    baseSteps [unarySeparator] +
    simplePhaseSteps scratchInitialLayout raw +
    phaseTransitionSteps .scratch
      (SourceParser.circuitCells raw) (scratchReserveLayout raw) +
    metricPassSteps .inputCount
      (scratchReserveLayout raw ++ [ledgerBoundary]) raw +
    phaseTransitionSteps .inputCount
      (SourceParser.circuitCells raw) (inputCountLayout raw) +
    metricPassSteps .normalizedGateCount
      (inputCountLayout raw) raw +
    phaseTransitionSteps .normalizedGateCount
      (SourceParser.circuitCells raw)
      (normalizedGateCountLayout raw) +
    metricPassSteps .carrierWidth
      (normalizedGateCountLayout raw) raw +
    phaseTransitionSteps .carrierWidth
      (SourceParser.circuitCells raw) (carrierWidthLayout raw) +
    metricPassSteps .baseline
      (carrierWidthLayout raw) raw +
    phaseTransitionSteps .baseline
      (SourceParser.circuitCells raw) (baselineLayout raw) +
    simplePhaseSteps (currentGateInitialLayout raw) raw +
    phaseTransitionSteps .currentGate
      (SourceParser.circuitCells raw) (currentGateLayout raw) +
    outputPhaseSteps (outputIndexInitialLayout raw) raw +
    finalPhaseSteps
      (SourceParser.circuitCells raw) (outputIndexLayout raw)

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 1000000 in
theorem exact_execution (raw : RawCircuit) :
    workRunExact? machine (workSteps raw)
        (entryConfiguration raw) =
      some (finalConfiguration raw) := by
  let cells := SourceParser.circuitCells raw
  let sourceWord := cells ++ [cellBlank]
  have cellsPath := circuit_parsePath .inputCount raw
  have cellsPacked := parsePath_packed cellsPath
  let afterBoot :=
    configAtWord (State.launchBase .scratch) []
      (cellBlank :: [unarySeparator].reverse ++
        sourceLeftBoundary :: sourceWord)
  have runBoot :
      workRunExact? machine bootSteps (entryConfiguration raw) =
        some afterBoot := by
    simpa [afterBoot, sourceWord, cells] using boot_exact raw
  let atScratch :=
    configAtWord (State.simpleScan .scratch)
      (sourceLeftBoundary ::
        (scratchInitialLayout ++ [activeEnd]))
      sourceWord
  have runScratchBase :
      workRunExact? machine (baseSteps [unarySeparator])
          afterBoot =
        some atScratch := by
    simpa [afterBoot, atScratch, scratchInitialLayout,
      phaseEntryState,
      sourceWord, cells, List.append_assoc] using
      base_exact .scratch [unarySeparator] sourceWord
        (by
          intro symbol member
          simp only [List.mem_singleton] at member
          subst symbol
          exact .unarySeparator)
  let afterScratch :=
    configAtLeftWord (State.finishSource .scratch)
      (cells.reverse ++
        sourceLeftBoundary ::
          (scratchReserveLayout raw ++ [activeEnd]))
      [cellBlank]
  have runScratch :
      workRunExact? machine
          (simplePhaseSteps scratchInitialLayout raw)
          atScratch =
        some afterScratch := by
    have exactRun :=
      simple_pass_finish_exact .scratch (by decide)
        scratchInitialLayout raw scratchInitialLayout_allowed
    rw [scratchInitialLayout, scratch_grow_eq] at exactRun
    simpa [atScratch, afterScratch, scratchInitialLayout,
      SimplePhase.phase, sourceWord, cells]
      using exactRun
  let inputFixed :=
    scratchReserveLayout raw ++ [ledgerBoundary]
  let atInput :=
    configAtWord (State.metricBegin .inputCount)
      (sourceLeftBoundary ::
        (inputFixed ++ [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank ++ [activeEnd]))
      sourceWord
  have runToInput :
      workRunExact? machine
          (phaseTransitionSteps .scratch cells
            (scratchReserveLayout raw))
          afterScratch =
        some atInput := by
    have exactRun :=
      phase_transition_exact .scratch .inputCount rfl
        cells (scratchReserveLayout raw) [cellBlank]
        cellsPacked (scratchReserveLayout_allowed raw)
    rw [show
      nextBaseFixed .scratch (scratchReserveLayout raw) =
        scratchReserveLayout raw ++
          [ledgerBoundary, slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterScratch, atInput, inputFixed, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let afterInput :=
    configAtLeftWord (State.finishSource .inputCount)
      (cells.reverse ++
        sourceLeftBoundary ::
          (inputCountLayout raw ++ [activeEnd]))
      [cellBlank]
  have runInput :
      workRunExact? machine
          (metricPassSteps .inputCount inputFixed raw)
          atInput =
        some afterInput := by
    have exactRun :=
      metric_pass_canonical_exact .inputCount inputFixed raw
        (by
          apply append_layout_allowed
          · exact scratchReserveLayout_allowed raw
          · intro symbol member
            simp only [List.mem_singleton] at member
            subst symbol
            exact .ledgerBoundary)
    simpa [atInput, afterInput, inputFixed, inputCountLayout,
      metricSlot, slotValue, ledgerRegisters, Metric.phase,
      sourceWord, cells,
      List.append_assoc] using exactRun
  let atNormalized :=
    configAtWord (State.metricBegin .normalizedGateCount)
      (sourceLeftBoundary ::
        (inputCountLayout raw ++
          [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank ++ [activeEnd]))
      sourceWord
  have runToNormalized :
      workRunExact? machine
          (phaseTransitionSteps .inputCount cells
            (inputCountLayout raw))
          afterInput =
        some atNormalized := by
    have exactRun :=
      phase_transition_exact .inputCount
        .normalizedGateCount rfl cells
        (inputCountLayout raw) [cellBlank]
        cellsPacked (inputCountLayout_allowed raw)
    rw [show
      nextBaseFixed .inputCount (inputCountLayout raw) =
        inputCountLayout raw ++
          [slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterInput, atNormalized, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let afterNormalized :=
    configAtLeftWord
      (State.finishSource .normalizedGateCount)
      (cells.reverse ++
        sourceLeftBoundary ::
          (normalizedGateCountLayout raw ++ [activeEnd]))
      [cellBlank]
  have runNormalized :
      workRunExact? machine
          (metricPassSteps .normalizedGateCount
            (inputCountLayout raw) raw)
          atNormalized =
        some afterNormalized := by
    have exactRun :=
      metric_pass_canonical_exact .normalizedGateCount
        (inputCountLayout raw) raw
        (inputCountLayout_allowed raw)
    simpa [atNormalized, afterNormalized,
      normalizedGateCountLayout, metricSlot, slotValue,
      ledgerRegisters, Metric.phase, sourceWord, cells,
      List.append_assoc] using exactRun
  let atCarrier :=
    configAtWord (State.metricBegin .carrierWidth)
      (sourceLeftBoundary ::
        (normalizedGateCountLayout raw ++
          [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank ++ [activeEnd]))
      sourceWord
  have runToCarrier :
      workRunExact? machine
          (phaseTransitionSteps .normalizedGateCount cells
            (normalizedGateCountLayout raw))
          afterNormalized =
        some atCarrier := by
    have exactRun :=
      phase_transition_exact .normalizedGateCount
        .carrierWidth rfl cells
        (normalizedGateCountLayout raw) [cellBlank]
        cellsPacked (normalizedGateCountLayout_allowed raw)
    rw [show
      nextBaseFixed .normalizedGateCount
          (normalizedGateCountLayout raw) =
        normalizedGateCountLayout raw ++
          [slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterNormalized, atCarrier, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let afterCarrier :=
    configAtLeftWord (State.finishSource .carrierWidth)
      (cells.reverse ++
        sourceLeftBoundary ::
          (carrierWidthLayout raw ++ [activeEnd]))
      [cellBlank]
  have runCarrier :
      workRunExact? machine
          (metricPassSteps .carrierWidth
            (normalizedGateCountLayout raw) raw)
          atCarrier =
        some afterCarrier := by
    have exactRun :=
      metric_pass_canonical_exact .carrierWidth
        (normalizedGateCountLayout raw) raw
        (normalizedGateCountLayout_allowed raw)
    simpa [atCarrier, afterCarrier, carrierWidthLayout,
      metricSlot, slotValue, ledgerRegisters, Metric.phase,
      sourceWord, cells,
      List.append_assoc] using exactRun
  let atBaseline :=
    configAtWord (State.metricBegin .baseline)
      (sourceLeftBoundary ::
        (carrierWidthLayout raw ++
          [slotBoundary, slotSeparator] ++
          List.replicate 64 cellBlank ++ [activeEnd]))
      sourceWord
  have runToBaseline :
      workRunExact? machine
          (phaseTransitionSteps .carrierWidth cells
            (carrierWidthLayout raw))
          afterCarrier =
        some atBaseline := by
    have exactRun :=
      phase_transition_exact .carrierWidth .baseline rfl
        cells (carrierWidthLayout raw) [cellBlank]
        cellsPacked (carrierWidthLayout_allowed raw)
    rw [show
      nextBaseFixed .carrierWidth (carrierWidthLayout raw) =
        carrierWidthLayout raw ++
          [slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterCarrier, atBaseline, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let afterBaseline :=
    configAtLeftWord (State.finishSource .baseline)
      (cells.reverse ++
        sourceLeftBoundary ::
          (baselineLayout raw ++ [activeEnd]))
      [cellBlank]
  have runBaseline :
      workRunExact? machine
          (metricPassSteps .baseline
            (carrierWidthLayout raw) raw)
          atBaseline =
        some afterBaseline := by
    have exactRun :=
      metric_pass_canonical_exact .baseline
        (carrierWidthLayout raw) raw
        (carrierWidthLayout_allowed raw)
    simpa [atBaseline, afterBaseline, baselineLayout,
      metricSlot, slotValue, ledgerRegisters, Metric.phase,
      sourceWord, cells,
      List.append_assoc] using exactRun
  let atCurrent :=
    configAtWord (State.simpleScan .currentGate)
      (sourceLeftBoundary ::
        (currentGateInitialLayout raw ++ [activeEnd]))
      sourceWord
  have runToCurrent :
      workRunExact? machine
          (phaseTransitionSteps .baseline cells
            (baselineLayout raw))
          afterBaseline =
        some atCurrent := by
    have exactRun :=
      phase_transition_exact .baseline .currentGate rfl
        cells (baselineLayout raw) [cellBlank]
        cellsPacked (baselineLayout_allowed raw)
    rw [show
      nextBaseFixed .baseline (baselineLayout raw) =
        baselineLayout raw ++ [slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterBaseline, atCurrent,
      currentGateInitialLayout, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let afterCurrent :=
    configAtLeftWord (State.finishSource .currentGate)
      (cells.reverse ++
        sourceLeftBoundary ::
          (currentGateLayout raw ++ [activeEnd]))
      [cellBlank]
  have runCurrent :
      workRunExact? machine
          (simplePhaseSteps (currentGateInitialLayout raw) raw)
          atCurrent =
        some afterCurrent := by
    have exactRun :=
      simple_pass_finish_exact .currentGate (by decide)
        (currentGateInitialLayout raw) raw
        (metricInitialLayout_allowed
          (baselineLayout raw) (baselineLayout_allowed raw))
    have grown :=
      zero_slot_grow_eq (baselineLayout raw) raw
    rw [currentGateInitialLayout] at exactRun
    rw [grown] at exactRun
    simpa [atCurrent, afterCurrent,
      currentGateInitialLayout, currentGateLayout,
      ledgerRegisters, SimplePhase.phase, sourceWord, cells,
      List.append_assoc] using exactRun
  let atOutput :=
    configAtWord (State.simpleScan .outputIndex)
      (sourceLeftBoundary ::
        (outputIndexInitialLayout raw ++ [activeEnd]))
      sourceWord
  have runToOutput :
      workRunExact? machine
          (phaseTransitionSteps .currentGate cells
            (currentGateLayout raw))
          afterCurrent =
        some atOutput := by
    have exactRun :=
      phase_transition_exact .currentGate .outputIndex rfl
        cells (currentGateLayout raw) [cellBlank]
        cellsPacked (currentGateLayout_allowed raw)
    rw [show
      nextBaseFixed .currentGate (currentGateLayout raw) =
        currentGateLayout raw ++ [slotBoundary, slotSeparator] by
      rfl] at exactRun
    simpa [afterCurrent, atOutput,
      outputIndexInitialLayout, sourceWord,
      phaseEntryState, cells, List.append_assoc] using exactRun
  let target :=
    [sourceTargetBoundary, cellBlank, cellBlank, cellBlank]
  let afterOutput :=
    configAtLeftWord (State.finishSource .outputIndex)
      (cells.reverse ++
        sourceLeftBoundary ::
          (outputIndexLayout raw ++ [activeEnd]))
      target
  have runOutput :
      workRunExact? machine
          (outputPhaseSteps (outputIndexInitialLayout raw) raw)
          atOutput =
        some afterOutput := by
    have exactRun :=
      output_pass_finish_exact
        (outputIndexInitialLayout raw) raw
        (metricInitialLayout_allowed
          (currentGateLayout raw) (currentGateLayout_allowed raw))
    have grown :=
      zero_slot_grow_eq (currentGateLayout raw) raw
    rw [outputIndexInitialLayout] at exactRun
    rw [grown] at exactRun
    simpa [atOutput, afterOutput, target,
      outputIndexInitialLayout, outputIndexLayout,
      ledgerRegisters, sourceWord, cells,
      List.append_assoc] using exactRun
  have runFinal :
      workRunExact? machine
          (finalPhaseSteps cells (outputIndexLayout raw))
          afterOutput =
        some (finalConfiguration raw) := by
    have exactRun :=
      final_phase_exact cells (outputIndexLayout raw) target
        cellsPacked (outputIndexLayout_allowed raw)
    have layoutStack := outputIndexLayout_with_stack raw
    have canonicalFinal :=
      finalConfiguration_eq_canonicalWord raw
    rw [show
      outputIndexLayout raw ++ [stackBoundary, cellBlank] =
        (outputIndexLayout raw ++ [stackBoundary]) ++
          [cellBlank] by
      simp [List.append_assoc]] at exactRun
    rw [layoutStack] at exactRun
    rw [← canonicalFinal]
    simpa [afterOutput, target, scratchReserveLayout,
      ledgerLeftWorkspace, sourceWord, cells,
      List.append_assoc] using exactRun
  have run01 := exactRun_add bootSteps
    (baseSteps [unarySeparator])
    _ afterBoot atScratch runBoot runScratchBase
  have run02 := exactRun_add
    (bootSteps + baseSteps [unarySeparator])
    (simplePhaseSteps scratchInitialLayout raw)
    _ atScratch afterScratch run01 runScratch
  have run03 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw)
    (phaseTransitionSteps .scratch cells
      (scratchReserveLayout raw))
    _ afterScratch atInput run02 runToInput
  have run04 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw))
    (metricPassSteps .inputCount inputFixed raw)
    _ atInput afterInput run03 runInput
  have run05 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw)
    (phaseTransitionSteps .inputCount cells
      (inputCountLayout raw))
    _ afterInput atNormalized run04 runToNormalized
  have run06 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw))
    (metricPassSteps .normalizedGateCount
      (inputCountLayout raw) raw)
    _ atNormalized afterNormalized run05 runNormalized
  have run07 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw)
    (phaseTransitionSteps .normalizedGateCount cells
      (normalizedGateCountLayout raw))
    _ afterNormalized atCarrier run06 runToCarrier
  have run08 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw))
    (metricPassSteps .carrierWidth
      (normalizedGateCountLayout raw) raw)
    _ atCarrier afterCarrier run07 runCarrier
  have run09 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw)
    (phaseTransitionSteps .carrierWidth cells
      (carrierWidthLayout raw))
    _ afterCarrier atBaseline run08 runToBaseline
  have run10 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw))
    (metricPassSteps .baseline (carrierWidthLayout raw) raw)
    _ atBaseline afterBaseline run09 runBaseline
  have run11 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw) +
      metricPassSteps .baseline (carrierWidthLayout raw) raw)
    (phaseTransitionSteps .baseline cells (baselineLayout raw))
    _ afterBaseline atCurrent run10 runToCurrent
  have run12 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw) +
      metricPassSteps .baseline (carrierWidthLayout raw) raw +
      phaseTransitionSteps .baseline cells (baselineLayout raw))
    (simplePhaseSteps (currentGateInitialLayout raw) raw)
    _ atCurrent afterCurrent run11 runCurrent
  have run13 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw) +
      metricPassSteps .baseline (carrierWidthLayout raw) raw +
      phaseTransitionSteps .baseline cells (baselineLayout raw) +
      simplePhaseSteps (currentGateInitialLayout raw) raw)
    (phaseTransitionSteps .currentGate cells
      (currentGateLayout raw))
    _ afterCurrent atOutput run12 runToOutput
  have run14 := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw) +
      metricPassSteps .baseline (carrierWidthLayout raw) raw +
      phaseTransitionSteps .baseline cells (baselineLayout raw) +
      simplePhaseSteps (currentGateInitialLayout raw) raw +
      phaseTransitionSteps .currentGate cells
        (currentGateLayout raw))
    (outputPhaseSteps (outputIndexInitialLayout raw) raw)
    _ atOutput afterOutput run13 runOutput
  have complete := exactRun_add
    (bootSteps + baseSteps [unarySeparator] +
      simplePhaseSteps scratchInitialLayout raw +
      phaseTransitionSteps .scratch cells
        (scratchReserveLayout raw) +
      metricPassSteps .inputCount inputFixed raw +
      phaseTransitionSteps .inputCount cells
        (inputCountLayout raw) +
      metricPassSteps .normalizedGateCount
        (inputCountLayout raw) raw +
      phaseTransitionSteps .normalizedGateCount cells
        (normalizedGateCountLayout raw) +
      metricPassSteps .carrierWidth
        (normalizedGateCountLayout raw) raw +
      phaseTransitionSteps .carrierWidth cells
        (carrierWidthLayout raw) +
      metricPassSteps .baseline (carrierWidthLayout raw) raw +
      phaseTransitionSteps .baseline cells (baselineLayout raw) +
      simplePhaseSteps (currentGateInitialLayout raw) raw +
      phaseTransitionSteps .currentGate cells
        (currentGateLayout raw) +
      outputPhaseSteps (outputIndexInitialLayout raw) raw)
    (finalPhaseSteps cells (outputIndexLayout raw))
    _ afterOutput _ run14 runFinal
  simpa [workSteps, inputFixed, cells,
    Nat.add_assoc] using complete

/-! ### Explicit source-length runtime bound -/

private theorem simplePassSteps_le
    (processed layout todo : List WorkSymbol) :
    simplePassSteps processed layout todo ≤
      todo.length *
        (133 + 2 * (processed.length + todo.length) +
          2 * (layout.length + 64 * todo.length)) := by
  induction todo generalizing processed layout with
  | nil =>
      simp [simplePassSteps]
  | cons current rest inductionHypothesis =>
      let factor :=
        133 + 2 * (processed.length + (current :: rest).length) +
          2 * (layout.length + 64 * (current :: rest).length)
      have headBound :
          simpleCellSteps processed layout ≤ factor := by
        unfold simpleCellSteps
        dsimp [factor]
        omega
      have tailBound :
          simplePassSteps (processed ++ [current])
              (layout ++ List.replicate 64 cellBlank) rest ≤
            rest.length * factor := by
        have tailRaw :=
          inductionHypothesis (processed ++ [current])
            (layout ++ List.replicate 64 cellBlank)
        have factorEq :
            133 +
                2 * ((processed ++ [current]).length + rest.length) +
                2 *
                  ((layout ++ List.replicate 64 cellBlank).length +
                    64 * rest.length) =
              factor := by
          dsimp [factor]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        rw [factorEq] at tailRaw
        exact tailRaw
      rw [simplePassSteps]
      calc
        simpleCellSteps processed layout +
              simplePassSteps (processed ++ [current])
                (layout ++ List.replicate 64 cellBlank) rest ≤
            factor + rest.length * factor :=
          Nat.add_le_add headBound tailBound
        _ = (current :: rest).length * factor := by
          simp only [List.length_cons, Nat.succ_mul]
          omega

private theorem metricPassStepsFrom_le
    (metric : Metric) (fixed processed todo : List WorkSymbol)
    (position final : ParseState) (value reserve contribution : Nat)
    (prefixPath :
      ParsePath metric .versionFirst processed position value)
    (tailPath :
      ParsePath metric position todo final contribution)
    (capacityEq :
      value + reserve = 64 * (processed.length + 1)) :
    metricPassStepsFrom metric fixed processed
        position value reserve todo ≤
      todo.length *
          (477 + 260 * (processed.length + todo.length) +
            2 * fixed.length) +
        1 := by
  induction tailPath generalizing processed value reserve with
  | nil position =>
      simp [metricPassStepsFrom]
  | @cons position next final current rest
      headContribution tailContribution packed step tail
      inductionHypothesis =>
      let factor :=
        477 +
          260 * (processed.length + (current :: rest).length) +
          2 * fixed.length
      have contributionBound :
          headContribution ≤ 80 := by
        have localBound :=
          parseStep_contribution_le metric position next
            current headContribution step
        have metricBound : metric.maxContribution ≤ 80 := by
          cases metric <;> decide
        exact Nat.le_trans localBound metricBound
      have reserveBound :
          reserve ≤ 64 * (processed.length + 1) := by
        omega
      have layoutLength :=
        metricLayout_length fixed value reserve
      have headBound :
          1 +
              metricCellSteps processed
                (metricLayout fixed value reserve)
                reserve headContribution ≤
            factor := by
        unfold metricCellSteps
        rw [layoutLength]
        dsimp [factor]
        omega
      have nextPrefix :
          ParsePath metric .versionFirst
            (processed ++ [current]) next
            (value + headContribution) := by
        have currentPath :=
          parsePath_single packed step
        simpa using parsePath_append prefixPath currentPath
      let nextReserve := reserve - headContribution + 64
      have nextCapacity :
          value + headContribution + nextReserve =
            64 * ((processed ++ [current]).length + 1) := by
        have prefixCapacity := parsePrefix_capacity nextPrefix
        have fits : headContribution ≤ reserve := by
          simp only [List.length_append, List.length_singleton]
            at prefixCapacity
          omega
        simp [nextReserve]
        omega
      have tailBound :
          metricPassStepsFrom metric fixed
              (processed ++ [current]) next
              (value + headContribution) nextReserve rest ≤
            rest.length * factor + 1 := by
        have tailRaw :=
          inductionHypothesis
            (processed ++ [current])
            (value + headContribution) nextReserve
            nextPrefix nextCapacity
        have factorEq :
            477 +
                260 *
                  ((processed ++ [current]).length + rest.length) +
                2 * fixed.length =
              factor := by
          dsimp [factor]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        rw [factorEq] at tailRaw
        exact tailRaw
      rw [metricPassStepsFrom, step]
      calc
        1 +
              metricCellSteps processed
                (metricLayout fixed value reserve)
                reserve headContribution +
              metricPassStepsFrom metric fixed
                (processed ++ [current]) next
                (value + headContribution)
                (reserve - headContribution + 64) rest ≤
            factor + (rest.length * factor + 1) :=
          Nat.add_le_add headBound tailBound
        _ = (current :: rest).length * factor + 1 := by
          simp only [List.length_cons, Nat.succ_mul]
          omega

private theorem metricPassSteps_le
    (metric : Metric) (fixed : List WorkSymbol)
    (raw : RawCircuit) :
    metricPassSteps metric fixed raw ≤
      (SourceParser.circuitCells raw).length *
          (477 +
            260 * (SourceParser.circuitCells raw).length +
            2 * fixed.length) +
        1 := by
  have path := circuit_parsePath metric raw
  simpa [metricPassSteps] using
    metricPassStepsFrom_le metric fixed []
      (SourceParser.circuitCells raw) .versionFirst .done
      0 64 (metricContribution metric raw)
      (ParsePath.nil .versionFirst) path (by simp)

private theorem scratchReserveLayout_length (raw : RawCircuit) :
    (scratchReserveLayout raw).length =
      64 * (SourceParser.circuitCells raw).length + 65 := by
  simp [scratchReserveLayout, zeroScratchReserve,
    slotCapacity]

private theorem inputCountLayout_length (raw : RawCircuit) :
    (inputCountLayout raw).length =
      128 * (SourceParser.circuitCells raw).length + 132 := by
  simp only [inputCountLayout, List.length_append,
    List.length_singleton]
  rw [scratchReserveLayout_length,
    slotWord_length_of_le _ _ (ledgerShape raw).inputBound]
  simp [slotCapacity]
  omega

private theorem normalizedGateCountLayout_length
    (raw : RawCircuit) :
    (normalizedGateCountLayout raw).length =
      192 * (SourceParser.circuitCells raw).length + 198 := by
  simp only [normalizedGateCountLayout, List.length_append]
  rw [inputCountLayout_length,
    slotWord_length_of_le _ _
      (ledgerShape raw).normalizedGateBound]
  simp [slotCapacity]
  omega

private theorem carrierWidthLayout_length (raw : RawCircuit) :
    (carrierWidthLayout raw).length =
      256 * (SourceParser.circuitCells raw).length + 264 := by
  simp only [carrierWidthLayout, List.length_append]
  rw [normalizedGateCountLayout_length,
    slotWord_length_of_le _ _
      (ledgerShape raw).carrierWidthBound]
  simp [slotCapacity]
  omega

private theorem baselineLayout_length (raw : RawCircuit) :
    (baselineLayout raw).length =
      320 * (SourceParser.circuitCells raw).length + 330 := by
  simp only [baselineLayout, List.length_append]
  rw [carrierWidthLayout_length,
    slotWord_length_of_le _ _
      (ledgerShape raw).baselineBound]
  simp [slotCapacity]
  omega

private theorem currentGateLayout_length (raw : RawCircuit) :
    (currentGateLayout raw).length =
      384 * (SourceParser.circuitCells raw).length + 396 := by
  simp only [currentGateLayout, List.length_append]
  rw [baselineLayout_length,
    slotWord_length_of_le _ _
      (show
        (ledgerRegisters raw).currentGate ≤ slotCapacity raw by
        simp [ledgerRegisters, slotCapacity])]
  simp [slotCapacity]
  omega

private theorem outputIndexLayout_length (raw : RawCircuit) :
    (outputIndexLayout raw).length =
      448 * (SourceParser.circuitCells raw).length + 462 := by
  simp only [outputIndexLayout, List.length_append]
  rw [currentGateLayout_length,
    slotWord_length_of_le _ _
      (show
        (ledgerRegisters raw).outputIndex ≤ slotCapacity raw by
        simp [ledgerRegisters, slotCapacity])]
  simp [slotCapacity]
  omega

private theorem currentGateInitialLayout_length
    (raw : RawCircuit) :
    (currentGateInitialLayout raw).length =
      320 * (SourceParser.circuitCells raw).length + 396 := by
  simp [currentGateInitialLayout, baselineLayout_length]

private theorem outputIndexInitialLayout_length
    (raw : RawCircuit) :
    (outputIndexInitialLayout raw).length =
      384 * (SourceParser.circuitCells raw).length + 462 := by
  simp [outputIndexInitialLayout, currentGateLayout_length]

private theorem metricPassSteps_uniform
    (metric : Metric) (fixed : List WorkSymbol)
    (raw : RawCircuit)
    (fixedBound :
      fixed.length ≤
        256 * (SourceParser.circuitCells raw).length + 264) :
    metricPassSteps metric fixed raw ≤
      (SourceParser.circuitCells raw).length *
          (1005 +
            772 * (SourceParser.circuitCells raw).length) +
        1 := by
  have base := metricPassSteps_le metric fixed raw
  have factorBound :
      477 + 260 * (SourceParser.circuitCells raw).length +
          2 * fixed.length ≤
        1005 + 772 * (SourceParser.circuitCells raw).length := by
    omega
  have scaled :=
    Nat.mul_le_mul_left
      (SourceParser.circuitCells raw).length factorBound
  omega

private theorem simplePassSteps_uniform
    (layout : List WorkSymbol) (raw : RawCircuit)
    (layoutBound :
      layout.length ≤
        448 * (SourceParser.circuitCells raw).length + 462) :
    simplePassSteps [] layout
        (SourceParser.circuitCells raw) ≤
      (SourceParser.circuitCells raw).length *
        (1057 +
          1026 * (SourceParser.circuitCells raw).length) := by
  have base :
      simplePassSteps [] layout
          (SourceParser.circuitCells raw) ≤
        (SourceParser.circuitCells raw).length *
          (133 + 2 * (SourceParser.circuitCells raw).length +
            2 *
              (layout.length +
                64 * (SourceParser.circuitCells raw).length)) := by
    simpa using
      simplePassSteps_le [] layout
        (SourceParser.circuitCells raw)
  have factorBound :
      133 +
          2 * (SourceParser.circuitCells raw).length +
          2 *
            (layout.length +
              64 * (SourceParser.circuitCells raw).length) ≤
        1057 +
          1026 * (SourceParser.circuitCells raw).length := by
    omega
  exact Nat.le_trans base
    (Nat.mul_le_mul_left
      (SourceParser.circuitCells raw).length factorBound)

private theorem finishLaunchSteps_le_three (phase : Phase) :
    finishLaunchSteps phase ≤ 3 := by
  cases phase <;> decide

private theorem nextBaseFixed_length_le
    (phase : Phase) (layout : List WorkSymbol) :
    (nextBaseFixed phase layout).length ≤ layout.length + 3 := by
  unfold nextBaseFixed
  split <;> simp

private theorem phaseTransitionSteps_le
    (phase : Phase) (source layout : List WorkSymbol) :
    phaseTransitionSteps phase source layout ≤
      source.length + 2 * layout.length + 137 := by
  have launchBound := finishLaunchSteps_le_three phase
  have fixedBound := nextBaseFixed_length_le phase layout
  unfold phaseTransitionSteps finishScanSteps baseSteps
  omega

/-- Explicit quadratic work-step budget in the retained packed source length. -/
def polynomialWorkBound (raw : RawCircuit) : Nat :=
  let n := (SourceParser.circuitCells raw).length
  let metricBound := n * (1005 + 772 * n) + 1
  let simpleBound := n * (1057 + 1026 * n)
  let transitionBound := 769 * n + 929
  let finalBound := 897 * n + 929
  4 * metricBound + 3 * simpleBound +
    6 * transitionBound + finalBound + 143

set_option maxRecDepth 1000000 in
theorem workSteps_le_polynomialWorkBound (raw : RawCircuit) :
    workSteps raw ≤ polynomialWorkBound raw := by
  let n := (SourceParser.circuitCells raw).length
  let metricBound := n * (1005 + 772 * n) + 1
  let simpleBound := n * (1057 + 1026 * n)
  let transitionBound := 769 * n + 929
  let finalBound := 897 * n + 929
  have inputMetric :=
    metricPassSteps_uniform .inputCount
      (scratchReserveLayout raw ++ [ledgerBoundary]) raw
      (by
        rw [List.length_append, List.length_singleton,
          scratchReserveLayout_length]
        omega)
  have normalizedMetric :=
    metricPassSteps_uniform .normalizedGateCount
      (inputCountLayout raw) raw
      (by
        rw [inputCountLayout_length]
        omega)
  have carrierMetric :=
    metricPassSteps_uniform .carrierWidth
      (normalizedGateCountLayout raw) raw
      (by
        rw [normalizedGateCountLayout_length]
        omega)
  have baselineMetric :=
    metricPassSteps_uniform .baseline
      (carrierWidthLayout raw) raw
      (by
        rw [carrierWidthLayout_length]
        exact Nat.le_refl _)
  have scratchSimple :=
    simplePassSteps_uniform scratchInitialLayout raw
      (by
        simp [scratchInitialLayout])
  have currentSimple :=
    simplePassSteps_uniform (currentGateInitialLayout raw) raw
      (by
        rw [currentGateInitialLayout_length]
        omega)
  have outputSimple :=
    simplePassSteps_uniform (outputIndexInitialLayout raw) raw
      (by
        rw [outputIndexInitialLayout_length]
        omega)
  have scratchTransition :=
    phaseTransitionSteps_le .scratch
      (SourceParser.circuitCells raw) (scratchReserveLayout raw)
  have inputTransition :=
    phaseTransitionSteps_le .inputCount
      (SourceParser.circuitCells raw) (inputCountLayout raw)
  have normalizedTransition :=
    phaseTransitionSteps_le .normalizedGateCount
      (SourceParser.circuitCells raw)
      (normalizedGateCountLayout raw)
  have carrierTransition :=
    phaseTransitionSteps_le .carrierWidth
      (SourceParser.circuitCells raw) (carrierWidthLayout raw)
  have baselineTransition :=
    phaseTransitionSteps_le .baseline
      (SourceParser.circuitCells raw) (baselineLayout raw)
  have currentTransition :=
    phaseTransitionSteps_le .currentGate
      (SourceParser.circuitCells raw) (currentGateLayout raw)
  have finalPhaseBound :
      finalPhaseSteps (SourceParser.circuitCells raw)
          (outputIndexLayout raw) ≤
        finalBound := by
    unfold finalPhaseSteps finishScanSteps finalWorkspaceSteps
    rw [outputIndexLayout_length]
    dsimp [finalBound, n]
    omega
  have scratchTransitionBound :
      phaseTransitionSteps .scratch
          (SourceParser.circuitCells raw)
          (scratchReserveLayout raw) ≤
        transitionBound := by
    rw [scratchReserveLayout_length] at scratchTransition
    dsimp [transitionBound, n]
    omega
  have inputTransitionBound :
      phaseTransitionSteps .inputCount
          (SourceParser.circuitCells raw)
          (inputCountLayout raw) ≤
        transitionBound := by
    rw [inputCountLayout_length] at inputTransition
    dsimp [transitionBound, n]
    omega
  have normalizedTransitionBound :
      phaseTransitionSteps .normalizedGateCount
          (SourceParser.circuitCells raw)
          (normalizedGateCountLayout raw) ≤
        transitionBound := by
    rw [normalizedGateCountLayout_length]
      at normalizedTransition
    dsimp [transitionBound, n]
    omega
  have carrierTransitionBound :
      phaseTransitionSteps .carrierWidth
          (SourceParser.circuitCells raw)
          (carrierWidthLayout raw) ≤
        transitionBound := by
    rw [carrierWidthLayout_length] at carrierTransition
    dsimp [transitionBound, n]
    omega
  have baselineTransitionBound :
      phaseTransitionSteps .baseline
          (SourceParser.circuitCells raw)
          (baselineLayout raw) ≤
        transitionBound := by
    rw [baselineLayout_length] at baselineTransition
    dsimp [transitionBound, n]
    omega
  have currentTransitionBound :
      phaseTransitionSteps .currentGate
          (SourceParser.circuitCells raw)
          (currentGateLayout raw) ≤
        transitionBound := by
    rw [currentGateLayout_length] at currentTransition
    dsimp [transitionBound, n]
    omega
  change
    bootSteps + baseSteps [unarySeparator] +
        simplePhaseSteps scratchInitialLayout raw +
        phaseTransitionSteps .scratch
          (SourceParser.circuitCells raw)
          (scratchReserveLayout raw) +
        metricPassSteps .inputCount
          (scratchReserveLayout raw ++ [ledgerBoundary]) raw +
        phaseTransitionSteps .inputCount
          (SourceParser.circuitCells raw) (inputCountLayout raw) +
        metricPassSteps .normalizedGateCount
          (inputCountLayout raw) raw +
        phaseTransitionSteps .normalizedGateCount
          (SourceParser.circuitCells raw)
          (normalizedGateCountLayout raw) +
        metricPassSteps .carrierWidth
          (normalizedGateCountLayout raw) raw +
        phaseTransitionSteps .carrierWidth
          (SourceParser.circuitCells raw)
          (carrierWidthLayout raw) +
        metricPassSteps .baseline
          (carrierWidthLayout raw) raw +
        phaseTransitionSteps .baseline
          (SourceParser.circuitCells raw) (baselineLayout raw) +
        simplePhaseSteps (currentGateInitialLayout raw) raw +
        phaseTransitionSteps .currentGate
          (SourceParser.circuitCells raw)
          (currentGateLayout raw) +
        outputPhaseSteps (outputIndexInitialLayout raw) raw +
        finalPhaseSteps (SourceParser.circuitCells raw)
          (outputIndexLayout raw) ≤
      polynomialWorkBound raw
  unfold simplePhaseSteps outputPhaseSteps
  dsimp [polynomialWorkBound, metricBound, simpleBound,
    transitionBound, finalBound, n, bootSteps, baseSteps,
    outputTargetSteps] at *
  omega

def workTimePolynomial : NatPolynomial :=
  .add (NatPolynomial.quadratic 6166 6650)
    (NatPolynomial.linear 12702 0)

theorem workTimePolynomial_eval (sourceLength : Nat) :
    workTimePolynomial.eval sourceLength =
      6166 * sourceLength * sourceLength +
        12702 * sourceLength + 6650 := by
  simp [workTimePolynomial, NatPolynomial.quadratic,
    NatPolynomial.linear]
  omega

theorem polynomialWorkBound_eq (raw : RawCircuit) :
    polynomialWorkBound raw =
      6166 * (SourceParser.circuitCells raw).length *
          (SourceParser.circuitCells raw).length +
        12702 * (SourceParser.circuitCells raw).length + 6650 := by
  unfold polynomialWorkBound
  dsimp only
  simp only [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm]
  omega

def compiledTimePolynomial : NatPolynomial :=
  .mul (.constant 6) workTimePolynomial

theorem compiledTimePolynomial_eval (raw : RawCircuit) :
    compiledTimePolynomial.eval
        (SourceParser.circuitCells raw).length =
      6 * polynomialWorkBound raw := by
  simp [compiledTimePolynomial, workTimePolynomial_eval,
    polynomialWorkBound_eq]

theorem compiledSteps_le_timePolynomial (raw : RawCircuit) :
    6 * workSteps raw ≤
      compiledTimePolynomial.eval
        (SourceParser.circuitCells raw).length := by
  rw [compiledTimePolynomial_eval]
  exact Nat.mul_le_mul_left 6
    (workSteps_le_polynomialWorkBound raw)

/-! ### Compiled execution interface -/

theorem run_compiled_exact (raw : RawCircuit) :
    run compiledMachine (6 * workSteps raw)
        (encodeWorkConfiguration (entryConfiguration raw)) =
      encodeWorkConfiguration (finalConfiguration raw) := by
  exact run_compileWorkMachine_mul_of_workRunExact
    machine (workSteps raw) (entryConfiguration raw)
    (finalConfiguration raw) (exact_execution raw)

theorem run_compiled_bounded (raw : RawCircuit) :
    run compiledMachine
        (compiledTimePolynomial.eval
          (SourceParser.circuitCells raw).length)
        (encodeWorkConfiguration (entryConfiguration raw)) =
      encodeWorkConfiguration (finalConfiguration raw) := by
  exact run_compileWorkMachine_of_workRunExact_halted_le
    machine (workSteps raw)
    (compiledTimePolynomial.eval
      (SourceParser.circuitCells raw).length)
    (entryConfiguration raw) (finalConfiguration raw)
    (exact_execution raw) (finalConfiguration_halted raw)
    (compiledSteps_le_timePolynomial raw)

theorem run_compiled_bounded_blankEquivalent
    (raw : RawCircuit) (initial : Configuration)
    (equivalent :
      Configuration.BlankEquivalent initial
        (encodeWorkConfiguration (entryConfiguration raw))) :
    Configuration.BlankEquivalent
      (run compiledMachine
        (compiledTimePolynomial.eval
          (SourceParser.circuitCells raw).length)
        initial)
      (encodeWorkConfiguration (finalConfiguration raw)) := by
  have transported :=
    run_blankEquivalent compiledMachine
      (compiledTimePolynomial.eval
        (SourceParser.circuitCells raw).length)
      equivalent
  rw [run_compiled_bounded raw] at transported
  exact transported

/-! ### Fail-closed malformed workspace -/

theorem malformed_source_boundary_enters_dead
    (left right : List WorkSymbol) :
    workStep? machine
        (configAtWord (State.simpleScan .scratch) left
          (sourceLeftBoundary :: right)) =
      some
        (configAtWord State.dead left
          (sourceLeftBoundary :: right)) := by
  let program : StateProgram :=
    { state := State.simpleScan .scratch
      action := simpleScanAction .scratch }
  have member : program ∈ statePrograms := by
    exact simpleBand_program_mem State.simpleScan
      simpleScanAction (by simp [stateProgramBands]) .scratch
  have stopped :=
    stayAtWord program member sourceLeftBoundary
      (deadAction sourceLeftBoundary) (by rfl)
      left right rfl
  simpa [program, deadAction, keepAction] using stopped

theorem dead_configuration_stuck (tape : WorkTape) :
    workStep? machine { state := State.dead, tape := tape } = none := by
  have notHalted :
      machine.isHalted { state := State.dead, tape := tape } = false := by
    rfl
  unfold workStep?
  rw [notHalted]
  rw [show machine.rules = rules from rfl]
  rw [no_rule_at_dead]
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterLedger
