/-
Copyright (c) 2026 PNP Labs.

Intrinsically topological direct-wire realizations of the report's local
locked-NAND macros.  Gate order and exposed-output order follow the displayed
macro definitions exactly.  This file makes no global-builder, cross-instance
distinctness, or threshold claim.
-/

import PNP.NANDEnumerator
import PNP.LockedNANDPrefix

namespace PNP
namespace DirectWire

/-! ## Constant-free syntax audit -/

/-- A source is constant-free exactly when it is an input or prior gate. -/
def Source.hasNoConstant {inputs gates : Nat} : Source inputs gates → Bool
  | .input _ => true
  | .constant _ => false
  | .gate _ => true

def Gate.hasNoConstant {inputs gates : Nat} (gate : Gate inputs gates) : Bool :=
  gate.left.hasNoConstant && gate.right.hasNoConstant

/-- Check every source of every gate in an intrinsically topological program. -/
def Program.hasNoConstant {inputs gates : Nat} : Program inputs gates → Bool
  | .empty => true
  | .snoc initial gate => initial.hasNoConstant && gate.hasNoConstant

/-! ## Output valuations in report order -/

def emptyValuation : Valuation 0 := fun index => Fin.elim0 index

def EqualityMacroOutputs.toValuation (outputs : EqualityMacroOutputs) :
    Valuation 10 :=
  let v1 := emptyValuation.snoc outputs.a1
  let v2 := v1.snoc outputs.a2
  let v3 := v2.snoc outputs.a3
  let v4 := v3.snoc outputs.a4
  let v5 := v4.snoc outputs.a5
  let v6 := v5.snoc outputs.a6
  let v7 := v6.snoc outputs.a7
  let v8 := v7.snoc outputs.a8
  let v9 := v8.snoc outputs.a9
  v9.snoc outputs.a10

def ConstantOneMacroOutputs.toValuation (outputs : ConstantOneMacroOutputs) :
    Valuation 2 :=
  (emptyValuation.snoc outputs.b1).snoc outputs.b2

def ConstantZeroMacroOutputs.toValuation (outputs : ConstantZeroMacroOutputs) :
    Valuation 3 :=
  ((emptyValuation.snoc outputs.d1).snoc outputs.d2).snoc outputs.d3

def TraceMacroOutputs.toValuation (outputs : TraceMacroOutputs) : Valuation 18 :=
  let v1 := emptyValuation.snoc outputs.q1
  let v2 := v1.snoc outputs.q2
  let v3 := v2.snoc outputs.q3
  let v4 := v3.snoc outputs.q4
  let v5 := v4.snoc outputs.q5
  let v6 := v5.snoc outputs.q6
  let v7 := v6.snoc outputs.q7
  let v8 := v7.snoc outputs.q8
  let v9 := v8.snoc outputs.q9
  let v10 := v9.snoc outputs.q10
  let v11 := v10.snoc outputs.q11
  let v12 := v11.snoc outputs.q12
  let v13 := v12.snoc outputs.q13
  let v14 := v13.snoc outputs.q14
  let v15 := v14.snoc outputs.q15
  let v16 := v15.snoc outputs.q16
  let v17 := v16.snoc outputs.q17
  v17.snoc outputs.q18

def PrefixAndOutputs.toValuation (outputs : PrefixAndOutputs) : Valuation 2 :=
  (emptyValuation.snoc outputs.neg).snoc outputs.out

/-! ## Shared output wiring -/

/-- Expose every gate in source order, adding no gates or constants. -/
def exposeAllGates {inputs gates : Nat} (program : Program inputs gates) :
    Candidate inputs gates gates :=
  Candidate.ofDirectWireWord program ⟨fun gate => .gate gate⟩

theorem exposeAllGates_program {inputs gates : Nat}
    (program : Program inputs gates) :
    (exposeAllGates program).program = program := rfl

theorem exposeAllGates_source {inputs gates : Nat}
    (program : Program inputs gates) (gate : Fin gates) :
    (exposeAllGates program).directWireWord.source gate = .gate gate :=
  Candidate.ofDirectWireWord_pointwise program
    ⟨fun gate => .gate gate⟩ gate

/-! ## Equality macro: 3 inputs, 10 gates, 10 gate outputs -/

def equalityDirectProgram : Program 3 10 :=
  let p0 : Program 3 0 := .empty
  let p1 := p0.snoc ⟨.input ⟨0, by decide⟩, .input ⟨1, by decide⟩⟩
  let p2 := p1.snoc ⟨.input ⟨0, by decide⟩, .input ⟨2, by decide⟩⟩
  let p3 := p2.snoc ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩
  let p4 := p3.snoc ⟨.gate ⟨2, by decide⟩, .input ⟨2, by decide⟩⟩
  let p5 := p4.snoc ⟨.input ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩
  let p6 := p5.snoc ⟨.gate ⟨4, by decide⟩, .gate ⟨4, by decide⟩⟩
  let p7 := p6.snoc ⟨.gate ⟨5, by decide⟩, .gate ⟨1, by decide⟩⟩
  let p8 := p7.snoc ⟨.gate ⟨3, by decide⟩, .gate ⟨6, by decide⟩⟩
  let p9 := p8.snoc ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩
  p9.snoc ⟨.gate ⟨8, by decide⟩, .input ⟨1, by decide⟩⟩

def equalityDirect : Candidate 3 10 10 :=
  exposeAllGates equalityDirectProgram

theorem equalityDirect_size : equalityDirect.program.size = 10 := rfl

theorem equalityDirect_output_source (output : Fin 10) :
    equalityDirect.directWireWord.source output = .gate output :=
  exposeAllGates_source equalityDirectProgram output

theorem equalityDirect_semantics (input : Valuation 3) (output : Fin 10) :
    equalityDirect.semantics input output =
      EqualityMacroOutputs.toValuation
        (equalityMacro (input ⟨0, by decide⟩) (input ⟨1, by decide⟩)
          (input ⟨2, by decide⟩)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [equalityDirect_output_source]
  rfl

theorem equalityDirect_no_internal_constants :
    equalityDirect.program.hasNoConstant = true := rfl

/-! ## Constant-one macro: 2 inputs, 2 gates, 2 gate outputs -/

def constantOneDirectProgram : Program 2 2 :=
  let p0 : Program 2 0 := .empty
  let p1 := p0.snoc ⟨.input fin2Zero, .input fin2One⟩
  p1.snoc ⟨.gate fin1Zero, .gate fin1Zero⟩

def constantOneDirect : Candidate 2 2 2 :=
  exposeAllGates constantOneDirectProgram

theorem constantOneDirect_size : constantOneDirect.program.size = 2 := rfl

theorem constantOneDirect_output_source (output : Fin 2) :
    constantOneDirect.directWireWord.source output = .gate output :=
  exposeAllGates_source constantOneDirectProgram output

theorem constantOneDirect_semantics (input : Valuation 2) (output : Fin 2) :
    constantOneDirect.semantics input output =
      ConstantOneMacroOutputs.toValuation
        (constantOneMacro (input fin2Zero) (input fin2One)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [constantOneDirect_output_source]
  rfl

theorem constantOneDirect_no_internal_constants :
    constantOneDirect.program.hasNoConstant = true := rfl

/-! ## Constant-zero macro: 2 inputs, 3 gates, 3 gate outputs -/

def constantZeroDirectProgram : Program 2 3 :=
  let p0 : Program 2 0 := .empty
  let p1 := p0.snoc ⟨.input fin2Zero, .input fin2One⟩
  let p2 := p1.snoc ⟨.input fin2Zero, .gate fin1Zero⟩
  p2.snoc ⟨.gate ⟨1, by decide⟩, .gate ⟨1, by decide⟩⟩

def constantZeroDirect : Candidate 2 3 3 :=
  exposeAllGates constantZeroDirectProgram

theorem constantZeroDirect_size : constantZeroDirect.program.size = 3 := rfl

theorem constantZeroDirect_output_source (output : Fin 3) :
    constantZeroDirect.directWireWord.source output = .gate output :=
  exposeAllGates_source constantZeroDirectProgram output

theorem constantZeroDirect_semantics (input : Valuation 2) (output : Fin 3) :
    constantZeroDirect.semantics input output =
      ConstantZeroMacroOutputs.toValuation
        (constantZeroMacro (input fin2Zero) (input fin2One)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [constantZeroDirect_output_source]
  rfl

theorem constantZeroDirect_no_internal_constants :
    constantZeroDirect.program.hasNoConstant = true := rfl

/-! ## Trace macro: 4 inputs, 18 gates, 18 gate outputs -/

def traceDirectProgram : Program 4 18 :=
  let p0 : Program 4 0 := .empty
  let p1 := p0.snoc ⟨.input ⟨0, by decide⟩, .input ⟨1, by decide⟩⟩
  let p2 := p1.snoc ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩
  let p3 := p2.snoc ⟨.input ⟨0, by decide⟩, .input ⟨2, by decide⟩⟩
  let p4 := p3.snoc ⟨.input ⟨0, by decide⟩, .input ⟨3, by decide⟩⟩
  let p5 := p4.snoc ⟨.gate ⟨1, by decide⟩, .gate ⟨2, by decide⟩⟩
  let p6 := p5.snoc ⟨.gate ⟨1, by decide⟩, .input ⟨2, by decide⟩⟩
  let p7 := p6.snoc ⟨.gate ⟨5, by decide⟩, .gate ⟨5, by decide⟩⟩
  let p8 := p7.snoc ⟨.gate ⟨6, by decide⟩, .gate ⟨3, by decide⟩⟩
  let p9 := p8.snoc ⟨.input ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩
  let p10 := p9.snoc ⟨.gate ⟨8, by decide⟩, .gate ⟨8, by decide⟩⟩
  let p11 := p10.snoc ⟨.gate ⟨9, by decide⟩, .input ⟨2, by decide⟩⟩
  let p12 := p11.snoc ⟨.gate ⟨10, by decide⟩, .gate ⟨10, by decide⟩⟩
  let p13 := p12.snoc ⟨.gate ⟨11, by decide⟩, .input ⟨3, by decide⟩⟩
  let p14 := p13.snoc ⟨.gate ⟨4, by decide⟩, .gate ⟨7, by decide⟩⟩
  let p15 := p14.snoc ⟨.gate ⟨13, by decide⟩, .gate ⟨13, by decide⟩⟩
  let p16 := p15.snoc ⟨.gate ⟨14, by decide⟩, .gate ⟨12, by decide⟩⟩
  let p17 := p16.snoc ⟨.input ⟨0, by decide⟩, .input ⟨0, by decide⟩⟩
  p17.snoc ⟨.gate ⟨16, by decide⟩, .input ⟨1, by decide⟩⟩

def traceDirect : Candidate 4 18 18 :=
  exposeAllGates traceDirectProgram

theorem traceDirect_size : traceDirect.program.size = 18 := rfl

theorem traceDirect_output_source (output : Fin 18) :
    traceDirect.directWireWord.source output = .gate output :=
  exposeAllGates_source traceDirectProgram output

theorem traceDirect_semantics (input : Valuation 4) (output : Fin 18) :
    traceDirect.semantics input output =
      TraceMacroOutputs.toValuation
        (traceMacro (input ⟨0, by decide⟩) (input ⟨1, by decide⟩)
          (input ⟨2, by decide⟩) (input ⟨3, by decide⟩)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [traceDirect_output_source]
  rfl

theorem traceDirect_no_internal_constants :
    traceDirect.program.hasNoConstant = true := rfl

/-! ## Prefix AND node: 2 inputs, 2 gates, 2 gate outputs -/

def prefixAndDirectProgram : Program 2 2 :=
  let p0 : Program 2 0 := .empty
  let p1 := p0.snoc ⟨.input fin2Zero, .input fin2One⟩
  p1.snoc ⟨.gate fin1Zero, .gate fin1Zero⟩

def prefixAndDirect : Candidate 2 2 2 :=
  exposeAllGates prefixAndDirectProgram

theorem prefixAndDirect_size : prefixAndDirect.program.size = 2 := rfl

theorem prefixAndDirect_output_source (output : Fin 2) :
    prefixAndDirect.directWireWord.source output = .gate output :=
  exposeAllGates_source prefixAndDirectProgram output

theorem prefixAndDirect_semantics (input : Valuation 2) (output : Fin 2) :
    prefixAndDirect.semantics input output =
      PrefixAndOutputs.toValuation
        (prefixAndMacro (input fin2Zero) (input fin2One)) output := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [prefixAndDirect_output_source]
  rfl

theorem prefixAndDirect_no_internal_constants :
    prefixAndDirect.program.hasNoConstant = true := rfl

/-! ## Final conjunction: 3 inputs, 4 gates, final gate output -/

def finalConjunctionDirectProgram : Program 3 4 :=
  let p0 : Program 3 0 := .empty
  let p1 := p0.snoc ⟨.input ⟨1, by decide⟩, .input ⟨2, by decide⟩⟩
  let p2 := p1.snoc ⟨.gate ⟨0, by decide⟩, .gate ⟨0, by decide⟩⟩
  let p3 := p2.snoc ⟨.input ⟨0, by decide⟩, .gate ⟨1, by decide⟩⟩
  p3.snoc ⟨.gate ⟨2, by decide⟩, .gate ⟨2, by decide⟩⟩

def finalConjunctionDirect : Candidate 3 4 1 :=
  Candidate.ofDirectWireWord finalConjunctionDirectProgram
    ⟨fun _ => .gate ⟨3, by decide⟩⟩

theorem finalConjunctionDirect_size :
    finalConjunctionDirect.program.size = 4 := rfl

theorem finalConjunctionDirect_output_source :
    finalConjunctionDirect.directWireWord.source fin1Zero =
      .gate ⟨3, by decide⟩ := by
  exact Candidate.ofDirectWireWord_pointwise finalConjunctionDirectProgram
    ⟨fun _ => .gate ⟨3, by decide⟩⟩ fin1Zero

theorem finalConjunctionDirect_semantics (input : Valuation 3) :
    finalConjunctionDirect.semantics input fin1Zero =
      finalConjunction4 (input ⟨0, by decide⟩) (input ⟨1, by decide⟩)
        (input ⟨2, by decide⟩) := by
  unfold Candidate.semantics DirectWire.semantics DirectWireWord.eval
  rw [finalConjunctionDirect_output_source]
  rfl

theorem finalConjunctionDirect_no_internal_constants :
    finalConjunctionDirect.program.hasNoConstant = true := rfl

end DirectWire
end PNP
