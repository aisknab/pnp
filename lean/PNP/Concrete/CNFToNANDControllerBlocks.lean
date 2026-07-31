/-
Copyright (c) 2026 PNP Labs.

Closed physical blocks used by the finite CNF-to-NAND carrier controller.

The controller keeps a cursor in the retained carrier source, so every output
block uses the cursor-aware (`marked`) emitter.  The six-slot ledger is used as
follows:

* `inputCount` stores the decoded CNF width;
* `currentGate` stores the exact final compiler gate count `D`;
* `outputIndex` alternates between the next free gate coordinate and, during
  a postfix fold, the coordinate of the current accumulated result;
* the carrier's retained `carrierWidth` is the unique formula-stack marker.

No definition in this file reads a decoded formula or selects a program from
host data.  Every list below is a closed finite list of already-literal
emitter primitives.
-/

import PNP.Concrete.CNFToNANDEmitterPlan

namespace PNP.Concrete.CNFToNANDControllerBlocks

open PNP.Concrete.LockedNAND
open PNP.Concrete.LockedNAND.TargetEmitterPlan
open PNP.Concrete.CNFToNANDEmitterPlan

abbrev Primitive :=
  PNP.Concrete.LockedNAND.TargetEmitterPlan.Primitive

def mode :
    PNP.Concrete.LockedNAND.TargetEmitterPlan.CursorMode :=
  .marked

/-! ## First-pass counters and branch predicates -/

def countWidthUnitProgram : List Primitive :=
  [.incrementRegister .inputCount]

def countClauseProgram : List Primitive :=
  repeatPrimitive 2 (.incrementRegister .currentGate)

def countLiteralProgram : List Primitive :=
  repeatPrimitive 3 (.incrementRegister .currentGate)

def countValidNegativeProgram : List Primitive :=
  [.incrementRegister .currentGate]

def countEmptyFormulaProgram : List Primitive :=
  [.incrementRegister .currentGate]

def resetLiteralIndexProgram : List Primitive :=
  [.resetScratch]

def advanceLiteralIndexProgram : List Primitive :=
  [.incrementScratch]

/-- Accept exactly when the current literal index has reached the CNF width.
The controller uses the reject endpoint only while the index is strictly
smaller, and switches to an overflow state before it could become greater. -/
def compareLiteralIndexToWidthProgram : List Primitive :=
  [.compareRegister .inputCount]

/-- Accept on the empty-clause/false sentinel `D`; reject only for real gate
coordinates, which are strictly smaller than `D`. -/
def compareCoordinateToFalseProgram : List Primitive :=
  [.compareRegister .currentGate]

/-- Accept on the unique carrier-width formula marker; reject for every
clause descriptor, all of which are strictly smaller. -/
def compareCoordinateToFormulaMarkerProgram : List Primitive :=
  [.compareRegister .carrierWidth]

/-! ## Stack initialization -/

def initializeFormulaStackProgram : List Primitive :=
  pushFormulaMarkerProgram

def initializeClauseStackProgram : List Primitive :=
  pushTotalGateSentinelProgram

/-! ## Literal compilation

After the literal's unary terminator has been observed, scratch contains its
index whenever the literal is in range.  Every case leaves one descriptor on
the check stack and restores `outputIndex` to the next free coordinate.
-/

/-- Positive in-range literal: emit `nand x x`, push that negated literal,
and advance one gate. -/
def emitPositiveLiteralProgram : List Primitive :=
  emitSelfNANDProgram mode .inputScratch ++
    pushGateAtProgram 0 ++
    advanceOutputIndexProgram 1

/-- Negative in-range literal: emit the literal's own self-NAND followed by
the clause-level self-NAND, push the second gate, and advance two gates. -/
def emitNegativeLiteralProgram : List Primitive :=
  emitSelfNANDProgram mode .inputScratch ++
    emitSelfNANDProgram mode (.gateAt 0) ++
    pushGateAtProgram 1 ++
    advanceOutputIndexProgram 2

/-- Either polarity of an out-of-range literal is false.  The clause plan
first negates that false source, so this emits one `nand false false`. -/
def emitInvalidLiteralProgram : List Primitive :=
  emitSelfNANDProgram mode (.constant false) ++
    pushGateAtProgram 0 ++
    advanceOutputIndexProgram 1

/-! ## Clause postfix fold

During the fold `outputIndex` points at the accumulated clause result rather
than the next free coordinate.  The next physical gate is therefore
`outputIndex + 1`.  This one-cell lag makes the previous result available
without subtraction or an extra retained register.
-/

/-- Seed a nonempty clause from its newest literal and the recursive false
base.  Two gates are emitted; advancing once leaves `outputIndex` pointing at
the resulting disjunction gate. -/
def seedClauseProgram : List Primitive :=
  emitSelfNANDProgram mode (.constant false) ++
    emitGateProgram mode .gateScratch (.gateAt 0) ++
    advanceOutputIndexProgram 1

/-- Fold one earlier literal into the accumulated suffix.  The old result is
at `gateAt 0`, its negation is emitted at `gateAt 1`, and the new result at
`gateAt 2`; advancing twice again points at the result.

The popped literal coordinate initially lives in scratch.  Evaluating
`gateAt 0` uses that same scratch register, so the coordinate is first
re-pushed and then popped again after the suffix-negation gate.  This is a
physical preservation step only; it emits no gate and leaves the postfix
gate order unchanged. -/
def extendClauseProgram : List Primitive :=
  [.pushCheck] ++
    emitSelfNANDProgram mode (.gateAt 0) ++
    popCoordinateProgram ++
    emitGateProgram mode .gateScratch (.gateAt 1) ++
    advanceOutputIndexProgram 2

/-- Store the completed clause descriptor and restore the ordinary
next-free interpretation of `outputIndex`. -/
def finishNonemptyClauseProgram : List Primitive :=
  pushGateAtProgram 0 ++
    advanceOutputIndexProgram 1

/-- An empty clause is represented by the distinguished false sentinel. -/
def finishEmptyClauseProgram : List Primitive :=
  pushTotalGateSentinelProgram

/-! ## Formula conjunction fold -/

inductive ClauseSource where
  | constantFalse
  | gateScratch
deriving BEq, DecidableEq, Repr

def ClauseSource.emission : ClauseSource → EmissionSource
  | .constantFalse => .constant false
  | .gateScratch => .gateScratch

/-- Fold the newest clause against the recursive true base.  Advancing once
leaves `outputIndex` on the two-gate conjunction result. -/
def seedFormulaProgram (source : ClauseSource) : List Primitive :=
  emitGateProgram mode source.emission (.constant true) ++
    emitSelfNANDProgram mode (.gateAt 0) ++
    advanceOutputIndexProgram 1

/-- Fold one earlier clause against the accumulated suffix. -/
def extendFormulaProgram (source : ClauseSource) : List Primitive :=
  emitGateProgram mode source.emission (.gateAt 0) ++
    emitSelfNANDProgram mode (.gateAt 1) ++
    advanceOutputIndexProgram 2

/-- Normalize the true value of the zero-clause formula to one mandatory NAND
gate.  `outputIndex = 0` already names that final gate, so no advance occurs. -/
def emitEmptyFormulaProgram : List Primitive :=
  emitSelfNANDProgram mode (.constant false)

/-! ## Circuit framing -/

def emitCircuitHeaderProgram : List Primitive :=
  circuitHeaderProgram mode

def emitCircuitSuffixProgram : List Primitive :=
  circuitSuffixProgram mode

/-! ## Literal-compiler closure

These propositions expose that every controller block expands to a finite
list of existing literal work machines.  They are intentionally structural;
runtime safety and exact traces belong to the controller proof.
-/

private theorem MachineClosed.append
    {first second : List Primitive}
    (firstClosed : MachineClosed first)
    (secondClosed : MachineClosed second) :
    MachineClosed (first ++ second) := by
  rcases firstClosed with ⟨firstMachines, firstEq⟩
  rcases secondClosed with ⟨secondMachines, secondEq⟩
  exact
    ⟨firstMachines ++ secondMachines,
      PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.compileProgram_append
        first second firstMachines secondMachines
        firstEq secondEq⟩

private theorem fixedClosed
    (program : List Primitive)
    (compiled :
      ∃ machines,
        PNP.Concrete.LockedNAND.TargetEmitterPrimitiveCompiler.compileProgram
            program =
          some machines) :
    MachineClosed program :=
  compiled

theorem countWidthUnitProgram_closed :
    MachineClosed countWidthUnitProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem countClauseProgram_closed :
    MachineClosed countClauseProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem countLiteralProgram_closed :
    MachineClosed countLiteralProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem countValidNegativeProgram_closed :
    MachineClosed countValidNegativeProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem countEmptyFormulaProgram_closed :
    MachineClosed countEmptyFormulaProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem resetLiteralIndexProgram_closed :
    MachineClosed resetLiteralIndexProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem advanceLiteralIndexProgram_closed :
    MachineClosed advanceLiteralIndexProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem compareLiteralIndexToWidthProgram_closed :
    MachineClosed compareLiteralIndexToWidthProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem compareCoordinateToFalseProgram_closed :
    MachineClosed compareCoordinateToFalseProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem compareCoordinateToFormulaMarkerProgram_closed :
    MachineClosed compareCoordinateToFormulaMarkerProgram :=
  fixedClosed _ ⟨_, rfl⟩

theorem initializeFormulaStackProgram_closed :
    MachineClosed initializeFormulaStackProgram :=
  pushFormulaMarkerProgram_closed

theorem initializeClauseStackProgram_closed :
    MachineClosed initializeClauseStackProgram :=
  pushTotalGateSentinelProgram_closed

theorem emitPositiveLiteralProgram_closed :
    MachineClosed emitPositiveLiteralProgram := by
  unfold emitPositiveLiteralProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitSelfNANDProgram_closed mode .inputScratch)
      (pushGateAtProgram_closed 0))
    (advanceOutputIndexProgram_closed 1)

theorem emitNegativeLiteralProgram_closed :
    MachineClosed emitNegativeLiteralProgram := by
  unfold emitNegativeLiteralProgram
  exact MachineClosed.append
    (MachineClosed.append
      (MachineClosed.append
        (emitSelfNANDProgram_closed mode .inputScratch)
        (emitSelfNANDProgram_closed mode (.gateAt 0)))
      (pushGateAtProgram_closed 1))
    (advanceOutputIndexProgram_closed 2)

theorem emitInvalidLiteralProgram_closed :
    MachineClosed emitInvalidLiteralProgram := by
  unfold emitInvalidLiteralProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitSelfNANDProgram_closed mode (.constant false))
      (pushGateAtProgram_closed 0))
    (advanceOutputIndexProgram_closed 1)

theorem seedClauseProgram_closed :
    MachineClosed seedClauseProgram := by
  unfold seedClauseProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitSelfNANDProgram_closed mode (.constant false))
      (emitGateProgram_closed mode .gateScratch (.gateAt 0)))
    (advanceOutputIndexProgram_closed 1)

theorem extendClauseProgram_closed :
    MachineClosed extendClauseProgram := by
  unfold extendClauseProgram
  exact MachineClosed.append
    (MachineClosed.append
      (MachineClosed.append
        (MachineClosed.append
          (fixedClosed _ ⟨_, rfl⟩)
          (emitSelfNANDProgram_closed mode (.gateAt 0)))
        popCoordinateProgram_closed)
      (emitGateProgram_closed mode .gateScratch (.gateAt 1)))
    (advanceOutputIndexProgram_closed 2)

theorem finishNonemptyClauseProgram_closed :
    MachineClosed finishNonemptyClauseProgram := by
  unfold finishNonemptyClauseProgram
  exact MachineClosed.append
    (pushGateAtProgram_closed 0)
    (advanceOutputIndexProgram_closed 1)

theorem finishEmptyClauseProgram_closed :
    MachineClosed finishEmptyClauseProgram :=
  pushTotalGateSentinelProgram_closed

theorem seedFormulaProgram_closed (source : ClauseSource) :
    MachineClosed (seedFormulaProgram source) := by
  unfold seedFormulaProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitGateProgram_closed mode source.emission (.constant true))
      (emitSelfNANDProgram_closed mode (.gateAt 0)))
    (advanceOutputIndexProgram_closed 1)

theorem extendFormulaProgram_closed (source : ClauseSource) :
    MachineClosed (extendFormulaProgram source) := by
  unfold extendFormulaProgram
  exact MachineClosed.append
    (MachineClosed.append
      (emitGateProgram_closed mode source.emission (.gateAt 0))
      (emitSelfNANDProgram_closed mode (.gateAt 1)))
    (advanceOutputIndexProgram_closed 2)

theorem emitEmptyFormulaProgram_closed :
    MachineClosed emitEmptyFormulaProgram :=
  emitSelfNANDProgram_closed mode (.constant false)

theorem emitCircuitHeaderProgram_closed :
    MachineClosed emitCircuitHeaderProgram :=
  circuitHeaderProgram_closed mode

theorem emitCircuitSuffixProgram_closed :
    MachineClosed emitCircuitSuffixProgram :=
  circuitSuffixProgram_closed mode

end PNP.Concrete.CNFToNANDControllerBlocks
