/-
Copyright (c) 2026 PNP Labs.

Closed symbolic program for the grammar-only locked-NAND target emitter.

The definitions in this file describe only the six literal NAND templates
and arithmetic expressions over the controller's unary registers.  They take
no raw circuit, decoded value, semantic candidate, or precomputed target.
Consequently the later finite controller can compile these closed lists into
literal work-machine control while obtaining every variable coordinate from
the retained source and unary workspace.
-/

import PNP.Concrete.LockedNANDTargetEmitterMachine

namespace PNP.Concrete.LockedNAND.TargetEmitterPlan

/-! ### Source-derived unary expressions -/

/-- A physical unary value available to the fixed emitter controller.
`captured` is the index of the uniquely cursor-marked source field.  `scratch`
is reserved for the check-stack pop operation; ordinary computed expressions
do not use it. -/
inductive Counter where
  | inputCount
  | normalizedGateCount
  | carrierWidth
  | baseline
  | currentGate
  | outputIndex
  | captured
  | scratch
deriving BEq, DecidableEq, Repr

/-- An addition-only expression.  Repeated terms are literal coefficients,
which keeps the machine compiler finite and avoids a multiplication
instruction. -/
structure NatExpression where
  terms : List Counter
  offset : Nat
deriving BEq, DecidableEq, Repr

namespace NatExpression

def zero : NatExpression :=
  { terms := [], offset := 0 }

def counter (value : Counter) : NatExpression :=
  { terms := [value], offset := 0 }

def constant (value : Nat) : NatExpression :=
  { terms := [], offset := value }

def add (left right : NatExpression) : NatExpression :=
  { terms := left.terms ++ right.terms
    offset := left.offset + right.offset }

def addOffset (expression : NatExpression) (value : Nat) :
    NatExpression :=
  { expression with offset := expression.offset + value }

def scale (coefficient : Nat) (expression : NatExpression) :
    NatExpression :=
  { terms := (List.replicate coefficient expression.terms).flatten
    offset := coefficient * expression.offset }

def evaluateCounter
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) : Counter → Nat
  | .inputCount => registers.inputCount
  | .normalizedGateCount => registers.normalizedGateCount
  | .carrierWidth => registers.carrierWidth
  | .baseline => registers.baseline
  | .currentGate => registers.currentGate
  | .outputIndex => registers.outputIndex
  | .captured => captured
  | .scratch => scratch

def evaluate (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) (expression : NatExpression) : Nat :=
  expression.offset +
    (expression.terms.map
      (evaluateCounter registers captured scratch)).sum

theorem evaluate_zero
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) :
    evaluate registers captured scratch zero = 0 := by
  rfl

theorem evaluate_counter
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) (value : Counter) :
    evaluate registers captured scratch (counter value) =
      evaluateCounter registers captured scratch value := by
  simp [evaluate, counter]

theorem evaluate_constant
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch value : Nat) :
    evaluate registers captured scratch (constant value) = value := by
  rfl

theorem evaluate_add
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) (left right : NatExpression) :
    evaluate registers captured scratch (add left right) =
      evaluate registers captured scratch left +
        evaluate registers captured scratch right := by
  simp [evaluate, add, List.map_append, List.sum_append]
  omega

theorem evaluate_addOffset
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch value : Nat) (expression : NatExpression) :
    evaluate registers captured scratch
        (addOffset expression value) =
      evaluate registers captured scratch expression + value := by
  simp [evaluate, addOffset]
  omega

end NatExpression

def inputCount : NatExpression :=
  NatExpression.counter .inputCount

def normalizedGateCount : NatExpression :=
  NatExpression.counter .normalizedGateCount

def carrierWidth : NatExpression :=
  NatExpression.counter .carrierWidth

def baseline : NatExpression :=
  NatExpression.counter .baseline

def currentGate : NatExpression :=
  NatExpression.counter .currentGate

def outputIndex : NatExpression :=
  NatExpression.counter .outputIndex

def capturedIndex : NatExpression :=
  NatExpression.counter .captured

def poppedCheck : NatExpression :=
  NatExpression.counter .scratch

def sourceLock (side : Nat) : NatExpression :=
  NatExpression.addOffset
    (NatExpression.add inputCount
      (NatExpression.add
        (NatExpression.scale 3 normalizedGateCount)
        (NatExpression.scale 2 currentGate)))
    side

def occurrence (side : Nat) : NatExpression :=
  NatExpression.addOffset
    (NatExpression.add inputCount
      (NatExpression.add normalizedGateCount
        (NatExpression.scale 2 currentGate)))
    side

def traceLock : NatExpression :=
  NatExpression.add inputCount
    (NatExpression.add
      (NatExpression.scale 5 normalizedGateCount)
      currentGate)

def traceCoordinate : NatExpression :=
  NatExpression.add inputCount currentGate

def rawGateTrace : NatExpression :=
  NatExpression.add capturedIndex inputCount

def finalLock : NatExpression :=
  NatExpression.add inputCount
    (NatExpression.scale 6 normalizedGateCount)

def localGate (index : Nat) : NatExpression :=
  NatExpression.addOffset outputIndex index

def checkAt (relative : Nat) : NatExpression :=
  NatExpression.addOffset outputIndex relative

def currentGateAt (bias : Nat) : NatExpression :=
  NatExpression.addOffset currentGate bias

def sourceLockAt (gateBias side : Nat) : NatExpression :=
  NatExpression.addOffset (sourceLock side) (2 * gateBias)

def occurrenceAt (gateBias side : Nat) : NatExpression :=
  NatExpression.addOffset (occurrence side) (2 * gateBias)

def traceLockAt (gateBias : Nat) : NatExpression :=
  NatExpression.addOffset traceLock gateBias

def traceCoordinateAt (gateBias : Nat) : NatExpression :=
  NatExpression.addOffset traceCoordinate gateBias

theorem sourceLock_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch side : Nat) :
    (sourceLock side).evaluate registers captured scratch =
      registers.inputCount +
        3 * registers.normalizedGateCount +
        2 * registers.currentGate + side := by
  simp [sourceLock, inputCount, normalizedGateCount, currentGate,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.addOffset, NatExpression.scale,
    NatExpression.counter, NatExpression.evaluateCounter]
  omega

theorem occurrence_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch side : Nat) :
    (occurrence side).evaluate registers captured scratch =
      registers.inputCount +
        registers.normalizedGateCount +
        2 * registers.currentGate + side := by
  simp [occurrence, inputCount, normalizedGateCount, currentGate,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.addOffset, NatExpression.scale,
    NatExpression.counter, NatExpression.evaluateCounter]
  omega

theorem traceLock_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) :
    traceLock.evaluate registers captured scratch =
      registers.inputCount +
        5 * registers.normalizedGateCount +
        registers.currentGate := by
  simp [traceLock, inputCount, normalizedGateCount, currentGate,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.scale, NatExpression.counter,
    NatExpression.evaluateCounter]
  omega

theorem traceCoordinate_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) :
    traceCoordinate.evaluate registers captured scratch =
      registers.inputCount + registers.currentGate := by
  simp [traceCoordinate, inputCount, currentGate,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.counter, NatExpression.evaluateCounter]

theorem rawGateTrace_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) :
    rawGateTrace.evaluate registers captured scratch =
      registers.inputCount + captured := by
  simp [rawGateTrace, inputCount, capturedIndex,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.counter, NatExpression.evaluateCounter,
    Nat.add_comm]

theorem finalLock_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) :
    finalLock.evaluate registers captured scratch =
      registers.inputCount +
        6 * registers.normalizedGateCount := by
  simp [finalLock, inputCount, normalizedGateCount,
    NatExpression.evaluate, NatExpression.add,
    NatExpression.scale, NatExpression.counter,
    NatExpression.evaluateCounter]
  omega

theorem localGate_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch index : Nat) :
    (localGate index).evaluate registers captured scratch =
      registers.outputIndex + index := by
  simp [localGate, outputIndex, NatExpression.evaluate,
    NatExpression.addOffset, NatExpression.counter,
    NatExpression.evaluateCounter]
  omega

theorem checkAt_evaluated
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch relative : Nat) :
    (checkAt relative).evaluate registers captured scratch =
      registers.outputIndex + relative := by
  simp [checkAt, outputIndex, NatExpression.evaluate,
    NatExpression.addOffset, NatExpression.counter,
    NatExpression.evaluateCounter]
  omega

/-! ### Closed source and gate language -/

inductive PlannedSource where
  | input (coordinate : NatExpression)
  | constant (value : Bool)
  | gate (coordinate : NatExpression)
deriving BEq, DecidableEq, Repr

structure PlannedGate where
  left : PlannedSource
  right : PlannedSource
deriving BEq, DecidableEq, Repr

def PlannedSource.evaluate
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) : PlannedSource → RawSource
  | .input coordinate =>
      .input (coordinate.evaluate registers captured scratch)
  | .constant value => .constant value
  | .gate coordinate =>
      .gate (coordinate.evaluate registers captured scratch)

def PlannedGate.evaluate
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat) (gate : PlannedGate) : RawGate :=
  { left := gate.left.evaluate registers captured scratch
    right := gate.right.evaluate registers captured scratch }

inductive TemplateSource where
  | binding (index : Nat)
  | localGate (index : Nat)
deriving BEq, DecidableEq, Repr

structure TemplateGate where
  left : TemplateSource
  right : TemplateSource
deriving BEq, DecidableEq, Repr

def TemplateSource.instantiateAt
    (base : NatExpression) (bindings : List PlannedSource) :
    TemplateSource → PlannedSource
  | .binding index =>
      bindings.getD index (.constant false)
  | .localGate index =>
      .gate (NatExpression.addOffset base index)

def TemplateGate.instantiateAt
    (base : NatExpression) (bindings : List PlannedSource)
    (gate : TemplateGate) : PlannedGate :=
  { left := gate.left.instantiateAt base bindings
    right := gate.right.instantiateAt base bindings }

def instantiateTemplateAt
    (base : NatExpression)
    (bindings : List PlannedSource)
    (template : List TemplateGate) : List PlannedGate :=
  template.map (TemplateGate.instantiateAt base bindings)

def instantiateTemplate
    (bindings : List PlannedSource)
    (template : List TemplateGate) : List PlannedGate :=
  instantiateTemplateAt outputIndex bindings template

/-! ### Six literal legacy templates -/

def equalityTemplate : List TemplateGate :=
  [ { left := .binding 0, right := .binding 1 }
  , { left := .binding 0, right := .binding 2 }
  , { left := .localGate 0, right := .localGate 0 }
  , { left := .localGate 2, right := .binding 2 }
  , { left := .binding 0, right := .localGate 0 }
  , { left := .localGate 4, right := .localGate 4 }
  , { left := .localGate 5, right := .localGate 1 }
  , { left := .localGate 3, right := .localGate 6 }
  , { left := .binding 0, right := .binding 0 }
  , { left := .localGate 8, right := .binding 1 }
  ]

def constantZeroTemplate : List TemplateGate :=
  [ { left := .binding 0, right := .binding 1 }
  , { left := .binding 0, right := .localGate 0 }
  , { left := .localGate 1, right := .localGate 1 }
  ]

def constantOneTemplate : List TemplateGate :=
  [ { left := .binding 0, right := .binding 1 }
  , { left := .localGate 0, right := .localGate 0 }
  ]

def traceTemplate : List TemplateGate :=
  [ { left := .binding 0, right := .binding 1 }
  , { left := .localGate 0, right := .localGate 0 }
  , { left := .binding 0, right := .binding 2 }
  , { left := .binding 0, right := .binding 3 }
  , { left := .localGate 1, right := .localGate 2 }
  , { left := .localGate 1, right := .binding 2 }
  , { left := .localGate 5, right := .localGate 5 }
  , { left := .localGate 6, right := .localGate 3 }
  , { left := .binding 0, right := .localGate 0 }
  , { left := .localGate 8, right := .localGate 8 }
  , { left := .localGate 9, right := .binding 2 }
  , { left := .localGate 10, right := .localGate 10 }
  , { left := .localGate 11, right := .binding 3 }
  , { left := .localGate 4, right := .localGate 7 }
  , { left := .localGate 13, right := .localGate 13 }
  , { left := .localGate 14, right := .localGate 12 }
  , { left := .binding 0, right := .binding 0 }
  , { left := .localGate 16, right := .binding 1 }
  ]

def prefixTemplate : List TemplateGate :=
  [ { left := .binding 0, right := .binding 1 }
  , { left := .localGate 0, right := .localGate 0 }
  ]

def finalTemplate : List TemplateGate :=
  [ { left := .binding 1, right := .binding 2 }
  , { left := .localGate 0, right := .localGate 0 }
  , { left := .binding 0, right := .localGate 1 }
  , { left := .localGate 2, right := .localGate 2 }
  ]

theorem equalityTemplate_length :
    equalityTemplate.length = 10 := by
  rfl

theorem constantZeroTemplate_length :
    constantZeroTemplate.length = 3 := by
  rfl

theorem constantOneTemplate_length :
    constantOneTemplate.length = 2 := by
  rfl

theorem traceTemplate_length :
    traceTemplate.length = 18 := by
  rfl

theorem prefixTemplate_length :
    prefixTemplate.length = 2 := by
  rfl

theorem finalTemplate_length :
    finalTemplate.length = 4 := by
  rfl

/-! ### Fixed macro selections -/

inductive SourceKind where
  | input
  | constantFalse
  | constantTrue
  | gate
deriving BEq, DecidableEq, Repr

def sourceBindings (kind : SourceKind) (side : Nat) :
    List PlannedSource :=
  let lock := PlannedSource.input (sourceLock side)
  let seen := PlannedSource.input (occurrence side)
  match kind with
  | .input =>
      [lock, seen, .input capturedIndex]
  | .constantFalse =>
      [lock, seen]
  | .constantTrue =>
      [lock, seen]
  | .gate =>
      [lock, seen, .input rawGateTrace]

def sourceTemplate : SourceKind → List TemplateGate
  | .input => equalityTemplate
  | .constantFalse => constantZeroTemplate
  | .constantTrue => constantOneTemplate
  | .gate => equalityTemplate

def sourcePlan (kind : SourceKind) (side : Nat) :
    List PlannedGate :=
  instantiateTemplate (sourceBindings kind side)
    (sourceTemplate kind)

def sourceCheckRelative : SourceKind → Nat
  | .input => 7
  | .constantFalse => 2
  | .constantTrue => 1
  | .gate => 7

def sourceGateCount : SourceKind → Nat
  | .input => 10
  | .constantFalse => 3
  | .constantTrue => 2
  | .gate => 10

def traceBindings : List PlannedSource :=
  [ .input traceLock
  , .input traceCoordinate
  , .input (occurrence 0)
  , .input (occurrence 1)
  ]

def tracePlan : List PlannedGate :=
  instantiateTemplate traceBindings traceTemplate

def syntheticGateBindings
    (gateBias sourceGateBias side : Nat) :
    List PlannedSource :=
  [ .input (sourceLockAt gateBias side)
  , .input (occurrenceAt gateBias side)
  , .input (traceCoordinateAt sourceGateBias)
  ]

def syntheticGatePlan
    (gateBias sourceGateBias side : Nat) :
    List PlannedGate :=
  instantiateTemplate
    (syntheticGateBindings gateBias sourceGateBias side)
    equalityTemplate

def traceBindingsAt (gateBias : Nat) : List PlannedSource :=
  [ .input (traceLockAt gateBias)
  , .input (traceCoordinateAt gateBias)
  , .input (occurrenceAt gateBias 0)
  , .input (occurrenceAt gateBias 1)
  ]

def tracePlanAt (gateBias : Nat) : List PlannedGate :=
  instantiateTemplate (traceBindingsAt gateBias) traceTemplate

def traceCheckRelative : Nat := 15
def traceGateCount : Nat := 18

def prefixBindings : List PlannedSource :=
  [.gate poppedCheck, .gate poppedCheck]

def finalBindings (outputTrace : NatExpression)
    (prefixOutput : PlannedSource) : List PlannedSource :=
  [ .input finalLock
  , prefixOutput
  , .input outputTrace
  ]

def finalPositivePlan (outputTrace : NatExpression) :
    List PlannedGate :=
  instantiateTemplateAt
    (NatExpression.addOffset outputIndex 1)
    (finalBindings outputTrace (.gate outputIndex))
    finalTemplate

def finalZeroPlan : List PlannedGate :=
  instantiateTemplateAt outputIndex
    (finalBindings rawGateTrace (.constant false))
    finalTemplate

/-! ### Closed primitive programs

These lists are compile-time control syntax.  They contain no circuit value
and no target word.  A later module maps each constructor to one audited
literal work machine and connects the renamed halt endpoints.
-/

inductive CursorMode where
  | plain
  | marked
deriving BEq, DecidableEq, Repr

inductive Primitive where
  | append (mode : CursorMode) (token : Token)
  | resetScratch
  | addRegister (counter : Counter)
  | reloadCaptured
  | incrementScratch
  | emitScratchNat (mode : CursorMode)
  | pushCheck
  | popCheck
  | compareRegister (counter : Counter)
  | incrementRegister (counter : Counter)
deriving BEq, DecidableEq, Repr

def repeatPrimitive (count : Nat) (operation : Primitive) :
    List Primitive :=
  List.replicate count operation

def counterOperation : Counter → Option Primitive
  | .inputCount => some (.addRegister .inputCount)
  | .normalizedGateCount =>
      some (.addRegister .normalizedGateCount)
  | .carrierWidth => some (.addRegister .carrierWidth)
  | .baseline => some (.addRegister .baseline)
  | .currentGate => some (.addRegister .currentGate)
  | .outputIndex => some (.addRegister .outputIndex)
  | .captured => some .reloadCaptured
  | .scratch => none

def compileTerms : List Counter → Option (List Primitive)
  | [] => some []
  | term :: rest => do
      let operation ← counterOperation term
      let tail ← compileTerms rest
      pure (operation :: tail)

/-- Compute a fresh unary natural in scratch without emitting it.
Expressions containing `scratch` are rejected because resetting scratch
would destroy the caller-owned popped check. -/
def computeNatural
    (expression : NatExpression) : Option (List Primitive) := do
  let terms ← compileTerms expression.terms
  pure ([.resetScratch] ++ terms ++
    repeatPrimitive expression.offset .incrementScratch)

/-- Compute a fresh unary natural and emit its `unit* natEnd` encoding. -/
def compileNatural (mode : CursorMode)
    (expression : NatExpression) : Option (List Primitive) := do
  let computation ← computeNatural expression
  pure (computation ++ [.emitScratchNat mode])

/-- Emit the source grammar for one planned source. -/
def compileSource (mode : CursorMode) :
    PlannedSource → Option (List Primitive)
  | .constant false => some [.append mode .constantFalse]
  | .constant true => some [.append mode .constantTrue]
  | .input coordinate => do
      let natural ← compileNatural mode coordinate
      pure (.append mode .input :: natural)
  | .gate coordinate => do
      let natural ← compileNatural mode coordinate
      pure (.append mode .gate :: natural)

def compileGate (mode : CursorMode)
    (gate : PlannedGate) : Option (List Primitive) := do
  let left ← compileSource mode gate.left
  let right ← compileSource mode gate.right
  pure (left ++ right ++ [.append mode .gateEnd])

def compileGates (mode : CursorMode) :
    List PlannedGate → Option (List Primitive)
  | [] => some []
  | gate :: rest => do
      let first ← compileGate mode gate
      let tail ← compileGates mode rest
      pure (first ++ tail)

def compileCheckPush (relative : Nat) :
    Option (List Primitive) := do
  let coordinate ← computeNatural (checkAt relative)
  pure (coordinate ++ [.pushCheck])

def sourceProgram (kind : SourceKind) (side : Nat) :
    Option (List Primitive) := do
  let gates ← compileGates .marked (sourcePlan kind side)
  let check ← compileCheckPush (sourceCheckRelative kind)
  pure
    (gates ++ check ++
      repeatPrimitive (sourceGateCount kind)
        (.incrementRegister .outputIndex) ++
      [.resetScratch])

def traceProgram : Option (List Primitive) := do
  let gates ← compileGates .marked tracePlan
  let check ← compileCheckPush traceCheckRelative
  pure
    (gates ++ check ++
      repeatPrimitive traceGateCount
        (.incrementRegister .outputIndex) ++
      [.resetScratch])

def syntheticGateSourceProgram
    (gateBias sourceGateBias side : Nat) :
    Option (List Primitive) := do
  let gates ← compileGates .marked
    (syntheticGatePlan gateBias sourceGateBias side)
  let check ← compileCheckPush (sourceCheckRelative .gate)
  pure
    (gates ++ check ++
      repeatPrimitive (sourceGateCount .gate)
        (.incrementRegister .outputIndex) ++
      [.resetScratch])

def traceProgramAt (gateBias : Nat) :
    Option (List Primitive) := do
  let gates ← compileGates .marked (tracePlanAt gateBias)
  let check ← compileCheckPush traceCheckRelative
  pure
    (gates ++ check ++
      repeatPrimitive traceGateCount
        (.incrementRegister .outputIndex) ++
      [.resetScratch])

def inputNormalizationProgram : Option (List Primitive) := do
  let firstLeft ← sourceProgram .input 0
  let firstRight ← sourceProgram .constantTrue 1
  let firstTrace ← traceProgram
  let secondLeft ← syntheticGateSourceProgram 1 0 0
  let secondRight ← syntheticGateSourceProgram 1 0 1
  let secondTrace ← traceProgramAt 1
  pure
    (firstLeft ++ firstRight ++ firstTrace ++
      secondLeft ++ secondRight ++ secondTrace ++
      [.incrementRegister .currentGate])

def constantNormalizationKind (value : Bool) : SourceKind :=
  if value then .constantFalse else .constantTrue

def constantNormalizationProgram
    (value : Bool) : Option (List Primitive) := do
  let left ← sourceProgram (constantNormalizationKind value) 0
  let right ← sourceProgram (constantNormalizationKind value) 1
  let trace ← traceProgram
  pure (left ++ right ++ trace)

def finalPositiveProgram
    (outputTrace : NatExpression) : Option (List Primitive) := do
  let gates ← compileGates .marked
    (finalPositivePlan outputTrace)
  pure (gates ++ [.resetScratch])

def finalZeroProgram : Option (List Primitive) := do
  let gates ← compileGates .marked finalZeroPlan
  pure (gates ++ [.resetScratch])

def headerProgram : Option (List Primitive) := do
  let width ← compileNatural .plain carrierWidth
  let gateCount ← compileNatural .plain
    (NatExpression.addOffset baseline 4)
  let outputCount ← compileNatural .plain
    (NatExpression.addOffset baseline 1)
  pure
    ([.append .plain .version0] ++ width ++ gateCount ++
      outputCount)

def emitPoppedGateSource (mode : CursorMode) : List Primitive :=
  [.append mode .gate, .emitScratchNat mode]

/-- Tail of the first right-fold link.  A conditional `popCheck` immediately
before this list has already loaded the newest record.  The next record is
then serialized in place, so only one scratch register is required.
`outputIndex` still names the first free gate while both gates are emitted
and is advanced once to name the newly exposed second gate. -/
def firstPrefixProgram : Option (List Primitive) := do
  let firstLocal ← compileSource .marked (.gate outputIndex)
  pure
    (emitPoppedGateSource .marked ++
      [.resetScratch, .popCheck] ++
      emitPoppedGateSource .marked ++
      [.append .marked .gateEnd] ++
      firstLocal ++ firstLocal ++
      [.append .marked .gateEnd,
       .incrementRegister .outputIndex,
       .resetScratch])

/-- Tail of every later right-fold link.  A conditional `popCheck` node is
placed immediately before this list by the controller.  That popped check is
temporarily pushed back while the accumulator coordinate is computed, because
`compileSource` resets scratch.  Scratch is cleared again for the literal pop
machine; that matching pop then restores exactly the newest check before it is
serialized as the second source. -/
def nextPrefixTailProgram : Option (List Primitive) := do
  let accumulator ← compileSource .marked (.gate outputIndex)
  let firstLocal ← compileSource .marked
    (.gate (NatExpression.addOffset outputIndex 1))
  pure
    ([.pushCheck] ++ accumulator ++ [.resetScratch, .popCheck] ++
      emitPoppedGateSource .marked ++
      [.append .marked .gateEnd] ++
      firstLocal ++ firstLocal ++
      [.append .marked .gateEnd,
       .incrementRegister .outputIndex,
       .incrementRegister .outputIndex,
       .resetScratch])

def outputLoopItemProgram : List Primitive :=
  [.append .marked .gate,
   .emitScratchNat .marked,
   .incrementScratch]

def outputLoopFinishProgram : List Primitive :=
  [ .incrementScratch
  , .incrementScratch
  , .incrementScratch
  , .append .marked .gate
  , .emitScratchNat .marked
  , .append .marked .outputsEnd
  , .resetScratch
  , .addRegister .baseline
  , .append .marked .threshold
  , .emitScratchNat .marked
  , .append .marked .instanceEnd
  ]

def beginOutputProgram : List Primitive :=
  [.append .marked .programEnd, .resetScratch]

theorem sourceProgram_closed
    (kind : SourceKind) (side : Nat) :
    ∃ program, sourceProgram kind side = some program := by
  cases kind <;> exact ⟨_, rfl⟩

theorem traceProgram_closed :
    ∃ program, traceProgram = some program := by
  exact ⟨_, rfl⟩

theorem syntheticGateSourceProgram_closed
    (gateBias sourceGateBias side : Nat) :
    ∃ program,
      syntheticGateSourceProgram gateBias sourceGateBias side =
        some program := by
  exact ⟨_, rfl⟩

theorem traceProgramAt_closed (gateBias : Nat) :
    ∃ program, traceProgramAt gateBias = some program := by
  exact ⟨_, rfl⟩

theorem inputNormalizationProgram_closed :
    ∃ program, inputNormalizationProgram = some program := by
  exact ⟨_, rfl⟩

theorem constantNormalizationProgram_closed (value : Bool) :
    ∃ program,
      constantNormalizationProgram value = some program := by
  cases value <;> exact ⟨_, rfl⟩

theorem finalPositiveRawGateProgram_closed :
    ∃ program,
      finalPositiveProgram rawGateTrace = some program := by
  exact ⟨_, rfl⟩

theorem finalPositiveNormalizedProgram_closed :
    ∃ program,
      finalPositiveProgram traceCoordinate = some program := by
  exact ⟨_, rfl⟩

theorem finalZeroProgram_closed :
    ∃ program, finalZeroProgram = some program := by
  exact ⟨_, rfl⟩

theorem headerProgram_closed :
    ∃ program, headerProgram = some program := by
  exact ⟨_, rfl⟩

theorem firstPrefixProgram_closed :
    ∃ program, firstPrefixProgram = some program := by
  exact ⟨_, rfl⟩

theorem nextPrefixTailProgram_closed :
    ∃ program, nextPrefixTailProgram = some program := by
  exact ⟨_, rfl⟩

/-! ### Structural comparison with the established direct templates -/

private def TemplateSource.toRaw : TemplateSource → RawSource
  | .binding index => .input index
  | .localGate index => .gate index

private def TemplateGate.toRaw (gate : TemplateGate) : RawGate :=
  { left := gate.left.toRaw
    right := gate.right.toRaw }

private def rawTemplate (template : List TemplateGate) : List RawGate :=
  template.map TemplateGate.toRaw

private theorem evaluate_getD
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch index : Nat)
    (bindings : List PlannedSource)
    (fallback : PlannedSource) :
    (bindings.getD index fallback).evaluate
        registers captured scratch =
      (bindings.map
        (PlannedSource.evaluate registers captured scratch)).getD
          index
          (fallback.evaluate registers captured scratch) := by
  induction bindings generalizing index with
  | nil =>
      cases index <;> rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero => rfl
      | succ index =>
          exact inductionHypothesis index

private theorem evaluate_instantiateSource
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat)
    (base : NatExpression) (bindings : List PlannedSource)
    (source : TemplateSource) :
    (source.instantiateAt base bindings).evaluate
        registers captured scratch =
      RawBuilder.instantiateSource
        (base.evaluate registers captured scratch)
        (RawBuilder.listBinding
          (bindings.map
            (PlannedSource.evaluate registers captured scratch)))
        source.toRaw := by
  cases source with
  | binding index =>
      simp only [TemplateSource.instantiateAt,
        TemplateSource.toRaw, RawBuilder.instantiateSource,
        RawBuilder.listBinding]
      rw [evaluate_getD]
      rfl
  | localGate index =>
      simp [TemplateSource.instantiateAt,
        TemplateSource.toRaw, PlannedSource.evaluate,
        RawBuilder.instantiateSource,
        NatExpression.evaluate_addOffset]

private theorem evaluate_instantiateGate
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat)
    (base : NatExpression) (bindings : List PlannedSource)
    (gate : TemplateGate) :
    (gate.instantiateAt base bindings).evaluate
        registers captured scratch =
      RawBuilder.instantiateGate
        (base.evaluate registers captured scratch)
        (RawBuilder.listBinding
          (bindings.map
            (PlannedSource.evaluate registers captured scratch)))
        gate.toRaw := by
  cases gate with
  | mk left right =>
      simp only [TemplateGate.instantiateAt,
        PlannedGate.evaluate, TemplateGate.toRaw,
        RawBuilder.instantiateGate]
      rw [evaluate_instantiateSource,
        evaluate_instantiateSource]

theorem evaluate_instantiateTemplateAt
    (registers : TargetEmitter.UnaryRegisters)
    (captured scratch : Nat)
    (base : NatExpression) (bindings : List PlannedSource)
    (template : List TemplateGate) :
    (instantiateTemplateAt base bindings template).map
        (PlannedGate.evaluate registers captured scratch) =
      (template.map TemplateGate.toRaw).map
          (RawBuilder.instantiateGate
            (base.evaluate registers captured scratch)
            (RawBuilder.listBinding
              (bindings.map
                (PlannedSource.evaluate registers captured scratch)))) := by
  induction template with
  | nil => rfl
  | cons gate rest inductionHypothesis =>
      change
        (gate.instantiateAt base bindings).evaluate
              registers captured scratch ::
            (instantiateTemplateAt base bindings rest).map
              (PlannedGate.evaluate registers captured scratch) =
          RawBuilder.instantiateGate
                (base.evaluate registers captured scratch)
                (RawBuilder.listBinding
                  (bindings.map
                    (PlannedSource.evaluate
                      registers captured scratch)))
                gate.toRaw ::
            (rest.map TemplateGate.toRaw).map
              (RawBuilder.instantiateGate
                (base.evaluate registers captured scratch)
                (RawBuilder.listBinding
                  (bindings.map
                    (PlannedSource.evaluate
                      registers captured scratch))))
      rw [evaluate_instantiateGate, inductionHypothesis]

theorem raw_equalityTemplate :
    rawTemplate equalityTemplate = RawBuilder.equalityTemplate := by
  rfl

theorem raw_constantZeroTemplate :
    rawTemplate constantZeroTemplate =
      RawBuilder.constantZeroTemplate := by
  rfl

theorem raw_constantOneTemplate :
    rawTemplate constantOneTemplate =
      RawBuilder.constantOneTemplate := by
  rfl

theorem raw_traceTemplate :
    rawTemplate traceTemplate = RawBuilder.traceTemplate := by
  rfl

theorem raw_prefixTemplate :
    rawTemplate prefixTemplate = RawBuilder.prefixTemplate := by
  rfl

theorem raw_finalTemplate :
    rawTemplate finalTemplate = RawBuilder.finalTemplate := by
  rfl

end PNP.Concrete.LockedNAND.TargetEmitterPlan
