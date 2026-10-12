/-
Copyright (c) 2026 PNP Labs.

Connection of the raw circuit readers to the exact gate-clause emitter. The
canonical theorem covers every gate and arbitrary unary indices, with a literal
finite program and exact execution cost.
-/

import PNP.Concrete.NANDFrontendMarkers
import PNP.Concrete.NANDFrontendGate

namespace PNP.Concrete.NANDFrontend

open BitRegister

theorem circuitBits_append (left right : List LockedNAND.Token) :
    LockedNAND.encodeTokens (left ++ right) =
      LockedNAND.encodeTokens left ++ LockedNAND.encodeTokens right := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.cons_append, LockedNAND.encodeTokens, ih, List.append_assoc]

theorem source_canonical_run (program : Program 9) (base : Nat) (operand : Operand)
    (next failure inputs : Nat) (r : Registers) (source : LockedNAND.RawSource) (suffix : BitString)
    (original : r.inputs = List.replicate inputs true)
    (placed : Segment program base (sourceCode base operand next failure)) :
    BitRegister.run program (sourceReadFuel source)
        (({r with input := LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens source) ++ suffix}).state base) =
      (operand.write {r with input := suffix} (List.replicate (sourceIndex inputs source) true)).state next := by
  have h := source_run program base operand next failure r
    (LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens source) ++ suffix) placed
  rw [original, sourceScan_canonical] at h
  simpa only [sourceResultRegisters, readerExit, original] using h

def gateReadCode (base next failure : Nat) : List (Instruction 9) :=
  sourceCode base .left (base + 98) failure ++
    sourceCode (base + 98) .right (base + 196) failure ++
    markerCode (base + 196) .gateEnd (base + 208) failure ++
    gateCode (base + 208) (base + 301) ++ [.push 3 true next]

theorem gateReadCode_length (base next failure : Nat) :
    (gateReadCode base next failure).length = 302 := by
  simp only [gateReadCode, List.length_append, sourceCode_length, markerCode_length, gateCode_length]
  rfl

theorem gateRead_segments (program : Program 9) (base next failure : Nat)
    (placed : Segment program base (gateReadCode base next failure)) :
    Segment program base (sourceCode base .left (base + 98) failure) ∧
      Segment program (base + 98) (sourceCode (base + 98) .right (base + 196) failure) ∧
      Segment program (base + 196) (markerCode (base + 196) .gateEnd (base + 208) failure) ∧
      Segment program (base + 208) (gateCode (base + 208) (base + 301)) ∧
      BitRegister.lookup program.code (base + 301) = some (.push 3 true next) := by
  have whole : Segment program base
      (sourceCode base .left (base + 98) failure ++
        (sourceCode (base + 98) .right (base + 196) failure ++
          (markerCode (base + 196) .gateEnd (base + 208) failure ++
            (gateCode (base + 208) (base + 301) ++ [.push 3 true next])))) := by
    simpa only [gateReadCode, List.append_assoc] using placed
  have left := Segment.head _ _ whole
  have rest1 := Segment.tail _ _ whole
  rw [sourceCode_length] at rest1
  have right := Segment.head _ _ rest1
  have rest2 := Segment.tail _ _ rest1
  rw [sourceCode_length] at rest2
  have sum1 : base + 98 + 98 = base + 196 := by omega
  rw [sum1] at rest2
  have marker := Segment.head _ _ rest2
  have rest3 := Segment.tail _ _ rest2
  rw [markerCode_length] at rest3
  have sum2 : base + 196 + 12 = base + 208 := by omega
  rw [sum2] at rest3
  have emitter := Segment.head _ _ rest3
  have ending := Segment.tail _ _ rest3
  rw [gateCode_length] at ending
  have sum3 : base + 208 + 93 = base + 301 := by omega
  rw [sum3] at ending
  have last := ending 0 (by change 0 < 1; decide)
  simp only [Nat.add_zero, BitRegister.lookup] at last
  exact ⟨left, right, marker, emitter, last⟩

def preparedGate (inputs ordinal : Nat) (gate : LockedNAND.RawGate) (r : Registers) : Registers :=
  {r with
    inputs := List.replicate inputs true
    gate := List.replicate (inputs + 2 + ordinal) true
    left := List.replicate (sourceIndex inputs gate.left) true
    right := List.replicate (sourceIndex inputs gate.right) true}

def gateReadFuel (inputs ordinal : Nat) (gate : LockedNAND.RawGate) : Nat :=
  sourceReadFuel gate.left + sourceReadFuel gate.right + 8 +
    (8 * sourceIndex inputs gate.left + 8 * sourceIndex inputs gate.right +
      20 * (inputs + 2 + ordinal) + 66) + 1

def emittedGate (inputs ordinal : Nat) (gate : LockedNAND.RawGate)
    (r : Registers) (suffix : BitString) : Registers :=
  {r with
    input := suffix
    inputs := List.replicate inputs true
    gate := List.replicate (inputs + 2 + (ordinal + 1)) true
    left := List.replicate (sourceIndex inputs gate.left) true
    right := List.replicate (sourceIndex inputs gate.right) true
    temp := []
    reversed := (encodeTokenPairs (encodeClauseListTokens (gateClauses inputs ordinal gate))).reverse ++ r.reversed}

theorem gateRead_canonical (program : Program 9) (base next failure inputs ordinal : Nat)
    (r : Registers) (gate : LockedNAND.RawGate) (suffix : BitString)
    (placed : Segment program base (gateReadCode base next failure)) :
    BitRegister.run program (gateReadFuel inputs ordinal gate)
        (({r with
          input := LockedNAND.encodeTokens (LockedNAND.encodeGateTokens gate) ++ suffix
          inputs := List.replicate inputs true
          gate := List.replicate (inputs + 2 + ordinal) true}).state base) =
      (emittedGate inputs ordinal gate r suffix).state next := by
  have segments := gateRead_segments program base next failure placed
  let leftSuffix := LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens gate.right) ++
    (LockedNAND.Token.gateEnd.bits ++ suffix)
  let r0 : Registers := {r with
    inputs := List.replicate inputs true
    gate := List.replicate (inputs + 2 + ordinal) true}
  let r1 : Registers := {r0 with
    input := leftSuffix
    left := List.replicate (sourceIndex inputs gate.left) true}
  let r2 : Registers := {r1 with
    input := LockedNAND.Token.gateEnd.bits ++ suffix
    right := List.replicate (sourceIndex inputs gate.right) true}
  let r3 : Registers := {r2 with input := suffix}
  have h1 := source_canonical_run program base .left (base + 98) failure inputs r0
    gate.left leftSuffix rfl segments.1
  have h2 := source_canonical_run program (base + 98) .right (base + 196) failure inputs r1
    gate.right (LockedNAND.Token.gateEnd.bits ++ suffix) rfl segments.2.1
  have h3 := marker_canonical program (base + 196) .gateEnd (base + 208) failure r2
    suffix segments.2.2.1
  have h4 := gate_run program (base + 208) (base + 301) r3 segments.2.2.2.1
  have fuel : gateReadFuel inputs ordinal gate =
      sourceReadFuel gate.left + (sourceReadFuel gate.right + (8 + (gateFuel r3 + 1))) := by
    simp only [gateReadFuel, gateFuel, r3, r2, r1, r0, List.length_replicate]
    omega
  have bytes : LockedNAND.encodeTokens (LockedNAND.encodeGateTokens gate) ++ suffix =
      LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens gate.left) ++ leftSuffix := by
    simp only [LockedNAND.encodeGateTokens, circuitBits_append, LockedNAND.encodeTokens,
      List.append_assoc, List.append_nil, leftSuffix]
  rw [fuel, bytes]
  change BitRegister.run program _ (({r0 with input := LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens gate.left) ++ leftSuffix}).state base) = _
  rw [BitRegister.run_add, h1]
  change BitRegister.run program _ (r1.state (base + 98)) = _
  rw [BitRegister.run_add, h2]
  change BitRegister.run program _ (r2.state (base + 196)) = _
  rw [BitRegister.run_add, h3]
  change BitRegister.run program _ (r3.state (base + 208)) = _
  rw [BitRegister.run_add, h4]
  have encoded : gateBits r3 =
      encodeTokenPairs (encodeClauseListTokens (gateClauses inputs ordinal gate)) :=
    gateBits_canonical inputs ordinal gate {r with input := suffix, inputs := List.replicate inputs true}
  rw [encoded]
  simp only [BitRegister.run, BitRegister.step, Registers.state, segments.2.2.2.2,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.set, Store.indexCases, emittedGate, r3, r2, r1, r0]
  rw [show inputs + 2 + (ordinal + 1) = (inputs + 2 + ordinal) + 1 by omega]
  rfl

end PNP.Concrete.NANDFrontend
