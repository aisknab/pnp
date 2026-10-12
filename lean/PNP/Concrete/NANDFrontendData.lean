/-
Copyright (c) 2026 PNP Labs.

Exact finite data emitted by the concrete circuit-to-formula frontend.
Gate order, repeated literals, the two constant units and the final output unit
are preserved. The original input width is distinct from the frontend width.
-/

import PNP.Concrete.CNFDecoderGrammar
import PNP.Concrete.LockedNANDEncoding

namespace PNP.Concrete.NANDFrontend

def sourceIndex (inputs : Nat) : LockedNAND.RawSource → Nat
  | .input index => index
  | .constant false => inputs
  | .constant true => inputs + 1
  | .gate index => inputs + 2 + index

def unitClause (index : Nat) (positive : Bool) : List CNFLiteral :=
  [⟨positive, index⟩, ⟨positive, index⟩, ⟨positive, index⟩]

def gateClauses (inputs ordinal : Nat) (gate : LockedNAND.RawGate) : List (List CNFLiteral) :=
  let left := sourceIndex inputs gate.left
  let right := sourceIndex inputs gate.right
  let output := inputs + 2 + ordinal
  [[⟨false, left⟩, ⟨false, right⟩, ⟨false, output⟩],
   [⟨true, left⟩, ⟨true, output⟩, ⟨true, output⟩],
   [⟨true, right⟩, ⟨true, output⟩, ⟨true, output⟩]]

def gatesClauses (inputs : Nat) : Nat → List LockedNAND.RawGate → List (List CNFLiteral)
  | _, [] => []
  | ordinal, gate :: rest => gateClauses inputs ordinal gate ++ gatesClauses inputs (ordinal + 1) rest

def formula (circuit : LockedNAND.RawCircuit) : CNFFormula :=
  ⟨circuit.inputCount + 2 + circuit.gates.length,
   [unitClause circuit.inputCount false, unitClause (circuit.inputCount + 1) true] ++
     gatesClauses circuit.inputCount 0 circuit.gates ++
     [unitClause (sourceIndex circuit.inputCount circuit.output) true]⟩

/-- Original width, then the exact frontend formula record. -/
def recordData (originalWidth : Nat) (value : CNFFormula) : BitString :=
  true :: (List.replicate originalWidth true ++ false :: CNFRegisterDecoder.formulaData value)

def circuitData (circuit : LockedNAND.RawCircuit) : BitString :=
  recordData circuit.inputCount (formula circuit)

def literalBits (positive : Bool) (index : Nat) : BitString :=
  [positive, positive] ++ List.replicate (2 * index) true ++ [false, false]

def threeBits (first second third : CNFLiteral) : BitString :=
  [false, true] ++ literalBits first.positive first.variableIndex ++
    literalBits second.positive second.variableIndex ++
    literalBits third.positive third.variableIndex ++ [true, false]

theorem encodeTokenPairs_append (first second : List CNFToken) :
    encodeTokenPairs (first ++ second) = encodeTokenPairs first ++ encodeTokenPairs second := by
  induction first with
  | nil => rfl
  | cons token rest ih =>
      simp only [List.cons_append, encodeTokenPairs, ih, List.append_assoc]

theorem twiceUnary_succ (index : Nat) :
    List.replicate (2 * (index + 1)) true =
      true :: true :: List.replicate (2 * index) true := by
  have count : 2 * (index + 1) = (2 * index + 1) + 1 := by omega
  rw [count]
  rfl

theorem unaryTokenBits (index : Nat) :
    encodeTokenPairs (encodeUnaryTokens index) =
      List.replicate (2 * index) true ++ [false, false] := by
  induction index with
  | zero => rfl
  | succ index ih =>
      simp only [encodeUnaryTokens, encodeTokenPairs, CNFToken.bits, ih, twiceUnary_succ,
        List.cons_append, List.nil_append]

theorem literalBits_exact (positive : Bool) (index : Nat) :
    literalBits positive index = encodeTokenPairs (encodeLiteralTokens ⟨positive, index⟩) := by
  cases positive <;>
    simp only [literalBits, encodeLiteralTokens, encodeTokenPairs, CNFToken.bits, unaryTokenBits,
      Bool.false_eq_true, ↓reduceIte, List.cons_append, List.nil_append]

theorem literalBits_length (positive : Bool) (index : Nat) :
    (literalBits positive index).length = 2 * index + 4 := by
  simp only [literalBits, List.length_append, List.length_cons, List.length_nil, List.length_replicate]
  omega

theorem literalBits_reverse (positive : Bool) (index : Nat) :
    (literalBits positive index).reverse =
      [false, false] ++ List.replicate (2 * index) true ++ [positive, positive] := by
  simp only [literalBits, List.reverse_append, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]

theorem threeBits_exact (first second third : CNFLiteral) :
    threeBits first second third = encodeTokenPairs (encodeClauseTokens [first, second, third]) := by
  simp only [threeBits, literalBits_exact, encodeClauseTokens, encodeLiteralListTokens,
    encodeTokenPairs_append, encodeTokenPairs, CNFToken.bits, List.append_nil, List.cons_append,
    List.nil_append, List.append_assoc]

theorem threeBits_length (first second third : CNFLiteral) :
    (threeBits first second third).length =
      2 * first.variableIndex + 2 * second.variableIndex + 2 * third.variableIndex + 16 := by
  simp only [threeBits, List.length_append, List.length_cons, List.length_nil, literalBits_length]
  omega

theorem gateClauses_length (inputs ordinal : Nat) (gate : LockedNAND.RawGate) :
    (gateClauses inputs ordinal gate).length = 3 := rfl

theorem gatesClauses_length (inputs ordinal : Nat) (gates : List LockedNAND.RawGate) :
    (gatesClauses inputs ordinal gates).length = 3 * gates.length := by
  induction gates generalizing ordinal with
  | nil => rfl
  | cons gate rest ih =>
      simp only [gatesClauses, List.length_append, gateClauses_length, ih, List.length_cons]
      omega

theorem formula_width (circuit : LockedNAND.RawCircuit) :
    (formula circuit).variableCount = circuit.inputCount + 2 + circuit.gates.length := rfl

theorem formula_clauses_length (circuit : LockedNAND.RawCircuit) :
    (formula circuit).clauses.length = 3 * circuit.gates.length + 3 := by
  simp only [formula, List.length_append, List.length_cons, List.length_nil, gatesClauses_length]
  omega

end PNP.Concrete.NANDFrontend
