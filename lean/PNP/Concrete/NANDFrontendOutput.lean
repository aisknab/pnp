/-
Copyright (c) 2026 PNP Labs.

Complete output-reference and end-of-input validation. Both required closing
markers and the absence of trailing bits are checked before writing the final
positive clause and packing the successful result.
-/

import PNP.Concrete.NANDFrontendOutputTail

namespace PNP.Concrete.NANDFrontend

open BitRegister

def outputCode (base next failure : Nat) : List (Instruction 9) :=
  sourceCode base .left (base + 98) failure ++
    markerCode (base + 98) .outputsEnd (base + 110) failure ++
    markerCode (base + 110) .instanceEnd (base + 122) failure ++
    [.branch 0 (base + 123) failure failure] ++ outputTailCode (base + 123) next

theorem outputCode_length (base next failure : Nat) : (outputCode base next failure).length = 173 := by
  simp only [outputCode, List.length_append, sourceCode_length, markerCode_length, outputTailCode_length]
  rfl

theorem output_segments (program : Program 9) (base next failure : Nat)
    (placed : Segment program base (outputCode base next failure)) :
    Segment program base (sourceCode base .left (base + 98) failure) ∧
      Segment program (base + 98) (markerCode (base + 98) .outputsEnd (base + 110) failure) ∧
      Segment program (base + 110) (markerCode (base + 110) .instanceEnd (base + 122) failure) ∧
      BitRegister.lookup program.code (base + 122) = some (.branch 0 (base + 123) failure failure) ∧
      Segment program (base + 123) (outputTailCode (base + 123) next) := by
  have whole : Segment program base (sourceCode base .left (base + 98) failure ++
      (markerCode (base + 98) .outputsEnd (base + 110) failure ++
        (markerCode (base + 110) .instanceEnd (base + 122) failure ++
          ([.branch 0 (base + 123) failure failure] ++ outputTailCode (base + 123) next)))) := by
    simpa only [outputCode, List.append_assoc] using placed
  have source := Segment.head _ _ whole
  have rest1 := Segment.tail _ _ whole
  rw [sourceCode_length] at rest1
  have first := Segment.head _ _ rest1
  have rest2 := Segment.tail _ _ rest1
  rw [markerCode_length] at rest2
  have n110 : base + 98 + 12 = base + 110 := by omega
  rw [n110] at rest2
  have second := Segment.head _ _ rest2
  have rest3 := Segment.tail _ _ rest2
  rw [markerCode_length] at rest3
  have n122 : base + 110 + 12 = base + 122 := by omega
  rw [n122] at rest3
  have branch := Segment.head _ _ rest3
  have hb := branch 0 (by change 0 < 1; decide)
  simp only [Nat.add_zero, BitRegister.lookup] at hb
  have tail := Segment.tail _ _ rest3
  change Segment program (base + 122 + 1) _ at tail
  have n123 : base + 122 + 1 = base + 123 := by omega
  rw [n123] at tail
  exact ⟨source, first, second, hb, tail⟩

def outputSource (r : Registers) : SourceResult := sourceScan r.inputs r.left r.input

def afterOutputSource (r : Registers) : Registers := sourceResultRegisters .left r (outputSource r)

def outputMarker (r : Registers) : MatchResult :=
  matchScan LockedNAND.Token.outputsEnd.bits (afterOutputSource r).input

def afterOutputMarker (r : Registers) : Registers :=
  {afterOutputSource r with input := (outputMarker r).rest}

def instanceMarker (r : Registers) : MatchResult :=
  matchScan LockedNAND.Token.instanceEnd.bits (afterOutputMarker r).input

def beforeOutputTail (r : Registers) : Registers :=
  {afterOutputMarker r with input := (instanceMarker r).rest}

def outputResult (r : Registers) : BlockResult :=
  match (outputSource r).valid with
  | false => ⟨(outputSource r).fuel, afterOutputSource r, false⟩
  | true =>
      match (outputMarker r).valid with
      | false => ⟨(outputSource r).fuel + (outputMarker r).fuel, afterOutputMarker r, false⟩
      | true =>
          match (instanceMarker r).valid with
          | false =>
              ⟨(outputSource r).fuel + ((outputMarker r).fuel + (instanceMarker r).fuel),
                beforeOutputTail r, false⟩
          | true =>
              match (beforeOutputTail r).input with
              | [] =>
                  ⟨(outputSource r).fuel + ((outputMarker r).fuel +
                      ((instanceMarker r).fuel + (1 + outputTailFuel (beforeOutputTail r)))),
                    finishedOutput (beforeOutputTail r), true⟩
              | _ :: _ =>
                  ⟨(outputSource r).fuel + ((outputMarker r).fuel + ((instanceMarker r).fuel + 1)),
                    beforeOutputTail r, false⟩

theorem output_result_run (program : Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment program base (outputCode base next failure)) :
    BitRegister.run program (outputResult r).fuel (r.state base) =
      (outputResult r).state.state (readerExit (outputResult r).valid next failure) := by
  have ps := output_segments program base next failure placed
  have source := source_run program base .left (base + 98) failure r r.input ps.1
  change BitRegister.run program (outputSource r).fuel (r.state base) =
    (afterOutputSource r).state (readerExit (outputSource r).valid (base + 98) failure) at source
  have first := marker_run program (base + 98) .outputsEnd (base + 110) failure
    (afterOutputSource r) (afterOutputSource r).input ps.2.1
  change BitRegister.run program (outputMarker r).fuel ((afterOutputSource r).state (base + 98)) =
    (afterOutputMarker r).state (readerExit (outputMarker r).valid (base + 110) failure) at first
  have second := marker_run program (base + 110) .instanceEnd (base + 122) failure
    (afterOutputMarker r) (afterOutputMarker r).input ps.2.2.1
  change BitRegister.run program (instanceMarker r).fuel ((afterOutputMarker r).state (base + 110)) =
    (beforeOutputTail r).state (readerExit (instanceMarker r).valid (base + 122) failure) at second
  cases hs : (outputSource r).valid with
  | false => simpa only [outputResult, hs, readerExit] using source
  | true =>
      simp only [hs, readerExit] at source
      cases ho : (outputMarker r).valid with
      | false =>
          simp only [outputResult, hs, ho, readerExit]
          rw [BitRegister.run_add, source]
          simpa only [ho, readerExit] using first
      | true =>
          simp only [ho, readerExit] at first
          cases hi : (instanceMarker r).valid with
          | false =>
              simp only [outputResult, hs, ho, hi, readerExit]
              rw [BitRegister.run_add, source, BitRegister.run_add, first]
              simpa only [hi, readerExit] using second
          | true =>
              simp only [hi, readerExit] at second
              cases remaining : (beforeOutputTail r).input with
              | nil =>
                  simp only [outputResult, hs, ho, hi, remaining, readerExit]
                  rw [BitRegister.run_add, source, BitRegister.run_add, first,
                    BitRegister.run_add, second, BitRegister.run_add]
                  have branch : BitRegister.run program 1 ((beforeOutputTail r).state (base + 122)) =
                      (beforeOutputTail r).state (base + 123) := by
                    simp only [BitRegister.run, BitRegister.step, Registers.state, ps.2.2.2.1,
                      Instruction.execute, Instruction.nextControl, Instruction.update,
                      Registers.store, Store.get, Store.indexCases, remaining]
                  rw [branch]
                  exact outputTail_run program (base + 123) next (beforeOutputTail r) ps.2.2.2.2
              | cons bit rest =>
                  simp only [outputResult, hs, ho, hi, remaining, readerExit]
                  rw [BitRegister.run_add, source, BitRegister.run_add, first,
                    BitRegister.run_add, second]
                  cases bit <;>
                    simp only [BitRegister.run, BitRegister.step, Registers.state, ps.2.2.2.1,
                      Instruction.execute, Instruction.nextControl, Instruction.update,
                      Registers.store, Store.get, Store.indexCases, remaining]

theorem output_result_bound (r : Registers) :
    (outputResult r).fuel ≤
      256 * (r.input.length + r.inputs.length + r.width.length + r.reversed.length + 1) := by
  have source := (sourceScan_bounds r.inputs r.left r.input).1
  change (outputSource r).fuel ≤ 3 * r.input.length + 1 at source
  have first := (matchScan_bounds LockedNAND.Token.outputsEnd.bits (afterOutputSource r).input).1
  change (outputMarker r).fuel ≤ 8 at first
  have second := (matchScan_bounds LockedNAND.Token.instanceEnd.bits (afterOutputMarker r).input).1
  change (instanceMarker r).fuel ≤ 8 at second
  cases hs : (outputSource r).valid with
  | false => simp only [outputResult, hs]; omega
  | true =>
      have size := (sourceScan_success r.inputs r.left r.input hs).2
      change (outputSource r).value.length ≤ r.inputs.length + r.input.length + 2 at size
      cases ho : (outputMarker r).valid with
      | false => simp only [outputResult, hs, ho]; omega
      | true =>
          cases hi : (instanceMarker r).valid with
          | false => simp only [outputResult, hs, ho, hi]; omega
          | true =>
              cases remaining : (beforeOutputTail r).input with
              | nil =>
                  simp only [outputResult, hs, ho, hi, remaining]
                  rw [outputTailFuel_eq]
                  simp only [beforeOutputTail, afterOutputMarker, afterOutputSource,
                    sourceResultRegisters, Operand.write]
                  omega
              | cons bit rest =>
                  simp only [outputResult, hs, ho, hi, remaining]
                  omega

theorem matchScan_self (expected : BitString) :
    matchScan expected expected = ⟨2 * expected.length, [], true⟩ := by
  simpa only [List.append_nil] using matchScan_prefix expected []

def outputBits (source : LockedNAND.RawSource) : BitString :=
  LockedNAND.encodeTokens (LockedNAND.encodeSourceTokens source) ++
    (LockedNAND.Token.outputsEnd.bits ++ LockedNAND.Token.instanceEnd.bits)

theorem output_result_canonical (inputs : Nat) (source : LockedNAND.RawSource) (r : Registers)
    (original : r.inputs = List.replicate inputs true) :
    outputResult {r with input := outputBits source} =
      ⟨sourceReadFuel source + (8 + (8 + (1 + outputTailFuel
          {r with input := [], left := List.replicate (sourceIndex inputs source) true}))),
        finishedOutput {r with input := [], left := List.replicate (sourceIndex inputs source) true}, true⟩ := by
  simp only [outputResult, outputSource, outputBits, original, sourceScan_canonical,
    outputMarker, afterOutputSource, sourceResultRegisters, Operand.write,
    matchScan_prefix, instanceMarker, afterOutputMarker, matchScan_self, beforeOutputTail,
    LockedNAND.Token.bits, List.length_cons, List.length_nil]

theorem output_result_trailing (inputs : Nat) (source : LockedNAND.RawSource) (r : Registers)
    (bit : Bool) (tail : BitString) (original : r.inputs = List.replicate inputs true) :
    (outputResult {r with input := outputBits source ++ bit :: tail}).valid = false := by
  simp only [outputResult, outputSource, outputBits, List.append_assoc, original,
    sourceScan_canonical, outputMarker, afterOutputSource, sourceResultRegisters, Operand.write,
    matchScan_prefix, instanceMarker, afterOutputMarker, beforeOutputTail]

end PNP.Concrete.NANDFrontend
