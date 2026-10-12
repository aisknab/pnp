/-
Copyright (c) 2026 PNP Labs.

The concrete circuit header reader derives the original input width, enlarged
formula width and initial gate index from the encoded source. It covers invalid
and truncated headers as well as canonical arbitrary-width inputs.
-/

import PNP.Concrete.NANDFrontendPack

namespace PNP.Concrete.NANDFrontend

open BitRegister

def headerSeedCode (base next : Nat) : List (Instruction 9) :=
  [.copy 1 4 (base + 1), .copy 3 4 (base + 2), .push 3 true (base + 3), .push 3 true next]

def headerFinishCode (base next : Nat) : List (Instruction 9) :=
  [.copy 2 3 (base + 1), .copy 3 1 (base + 2), .push 3 true (base + 3), .push 3 true next]

def headerSeed (r : Registers) : Registers :=
  {r with inputs := r.left, gate := true :: true :: r.left}

def headerFinish (r : Registers) : Registers :=
  {r with width := r.gate, gate := true :: true :: r.inputs}

theorem headerSeed_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (headerSeedCode base next)) :
    BitRegister.run program 4 (r.state base) = (headerSeed r).state next := by
  have h0 : BitRegister.lookup program.code base = some (.copy 1 4 (base + 1)) := by
    simpa only [Nat.add_zero, headerSeedCode, BitRegister.lookup] using placed 0 (by change 0 < 4; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.copy 3 4 (base + 2)) := by
    simpa only [Nat.add_zero, headerSeedCode, BitRegister.lookup] using placed 1 (by change 1 < 4; decide)
  have h2 : BitRegister.lookup program.code (base + 2) = some (.push 3 true (base + 3)) := by
    simpa only [Nat.add_zero, headerSeedCode, BitRegister.lookup] using placed 2 (by change 2 < 4; decide)
  have h3 : BitRegister.lookup program.code (base + 3) = some (.push 3 true next) := by
    simpa only [Nat.add_zero, headerSeedCode, BitRegister.lookup] using placed 3 (by change 3 < 4; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1, h2, h3,
    Instruction.execute, Instruction.nextControl, Instruction.update, Registers.store,
    Store.get, Store.set, Store.indexCases, headerSeed]

theorem headerFinish_run (program : Program 9) (base next : Nat) (r : Registers)
    (placed : Segment program base (headerFinishCode base next)) :
    BitRegister.run program 4 (r.state base) = (headerFinish r).state next := by
  have h0 : BitRegister.lookup program.code base = some (.copy 2 3 (base + 1)) := by
    simpa only [Nat.add_zero, headerFinishCode, BitRegister.lookup] using placed 0 (by change 0 < 4; decide)
  have h1 : BitRegister.lookup program.code (base + 1) = some (.copy 3 1 (base + 2)) := by
    simpa only [Nat.add_zero, headerFinishCode, BitRegister.lookup] using placed 1 (by change 1 < 4; decide)
  have h2 : BitRegister.lookup program.code (base + 2) = some (.push 3 true (base + 3)) := by
    simpa only [Nat.add_zero, headerFinishCode, BitRegister.lookup] using placed 2 (by change 2 < 4; decide)
  have h3 : BitRegister.lookup program.code (base + 3) = some (.push 3 true next) := by
    simpa only [Nat.add_zero, headerFinishCode, BitRegister.lookup] using placed 3 (by change 3 < 4; decide)
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0, h1, h2, h3,
    Instruction.execute, Instruction.nextControl, Instruction.update, Registers.store,
    Store.get, Store.set, Store.indexCases, headerFinish]

def headerCode (base next failure : Nat) : List (Instruction 9) :=
  markerCode base .version0 (base + 12) failure ++ [.clear 4 (base + 13)] ++
    unaryCode (base + 13) .left (base + 59) failure ++
    headerSeedCode (base + 59) (base + 63) ++
    unaryCode (base + 63) .gate (base + 109) failure ++ headerFinishCode (base + 109) next

theorem headerCode_length (base next failure : Nat) : (headerCode base next failure).length = 113 := by
  simp only [headerCode, List.length_append, markerCode_length, unaryCode_length]
  rfl

theorem header_segments (program : Program 9) (base next failure : Nat)
    (placed : Segment program base (headerCode base next failure)) :
    Segment program base (markerCode base .version0 (base + 12) failure) ∧
      BitRegister.lookup program.code (base + 12) = some (.clear 4 (base + 13)) ∧
      Segment program (base + 13) (unaryCode (base + 13) .left (base + 59) failure) ∧
      Segment program (base + 59) (headerSeedCode (base + 59) (base + 63)) ∧
      Segment program (base + 63) (unaryCode (base + 63) .gate (base + 109) failure) ∧
      Segment program (base + 109) (headerFinishCode (base + 109) next) := by
  have whole : Segment program base (markerCode base .version0 (base + 12) failure ++
      ([.clear 4 (base + 13)] ++
        (unaryCode (base + 13) .left (base + 59) failure ++
          (headerSeedCode (base + 59) (base + 63) ++
            (unaryCode (base + 63) .gate (base + 109) failure ++ headerFinishCode (base + 109) next))))) := by
    simpa only [headerCode, List.append_assoc] using placed
  have marker := Segment.head _ _ whole
  have rest1 := Segment.tail _ _ whole
  rw [markerCode_length] at rest1
  have clear := Segment.head _ _ rest1
  have hclear := clear 0 (by change 0 < 1; decide)
  simp only [Nat.add_zero, BitRegister.lookup] at hclear
  have rest2 := Segment.tail _ _ rest1
  change Segment program (base + 12 + 1) _ at rest2
  have s13 : base + 12 + 1 = base + 13 := by omega
  rw [s13] at rest2
  have first := Segment.head _ _ rest2
  have rest3 := Segment.tail _ _ rest2
  rw [unaryCode_length] at rest3
  have s59 : base + 13 + 46 = base + 59 := by omega
  rw [s59] at rest3
  have seed := Segment.head _ _ rest3
  have rest4 := Segment.tail _ _ rest3
  change Segment program (base + 59 + 4) _ at rest4
  have s63 : base + 59 + 4 = base + 63 := by omega
  rw [s63] at rest4
  have second := Segment.head _ _ rest4
  have finish := Segment.tail _ _ rest4
  rw [unaryCode_length] at finish
  have s109 : base + 63 + 46 = base + 109 := by omega
  rw [s109] at finish
  exact ⟨marker, hclear, first, seed, second, finish⟩

def headerMarker (r : Registers) : MatchResult :=
  matchScan LockedNAND.Token.version0.bits r.input

def headerBeforeCount (r : Registers) : Registers :=
  {r with input := (headerMarker r).rest, left := []}

def headerCount (r : Registers) : UnaryResult := unaryScan (headerMarker r).rest

def headerAfterCount (r : Registers) : Registers :=
  unaryResultRegisters .left (headerBeforeCount r) (headerCount r)

def headerGateCount (r : Registers) : UnaryResult := unaryScan (headerAfterCount r).input

def headerAfterGates (r : Registers) : Registers :=
  unaryResultRegisters .gate (headerSeed (headerAfterCount r)) (headerGateCount r)

def headerResult (r : Registers) : BlockResult :=
  match (headerMarker r).valid with
  | false => ⟨(headerMarker r).fuel, {r with input := (headerMarker r).rest}, false⟩
  | true =>
      match (headerCount r).valid with
      | false => ⟨(headerMarker r).fuel + (1 + (headerCount r).fuel), headerAfterCount r, false⟩
      | true =>
          match (headerGateCount r).valid with
          | false =>
              ⟨(headerMarker r).fuel + (1 + ((headerCount r).fuel + (4 + (headerGateCount r).fuel))),
                headerAfterGates r, false⟩
          | true =>
              ⟨(headerMarker r).fuel + (1 + ((headerCount r).fuel + (4 + ((headerGateCount r).fuel + 4)))),
                headerFinish (headerAfterGates r), true⟩

theorem header_result_run (program : Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment program base (headerCode base next failure)) :
    BitRegister.run program (headerResult r).fuel (r.state base) =
      (headerResult r).state.state (readerExit (headerResult r).valid next failure) := by
  have ps := header_segments program base next failure placed
  have marker := marker_run program base .version0 (base + 12) failure r r.input ps.1
  change BitRegister.run program (headerMarker r).fuel (r.state base) =
    ({r with input := (headerMarker r).rest}).state
      (readerExit (headerMarker r).valid (base + 12) failure) at marker
  have clear : BitRegister.run program 1 (({r with input := (headerMarker r).rest}).state (base + 12)) =
      (headerBeforeCount r).state (base + 13) := by
    simp only [BitRegister.run, BitRegister.step, Registers.state, ps.2.1,
      Instruction.execute, Instruction.nextControl, Instruction.update]
    rfl
  have first := unary_run program (base + 13) .left (base + 59) failure
    (headerBeforeCount r) (headerBeforeCount r).input ps.2.2.1
  change BitRegister.run program (headerCount r).fuel ((headerBeforeCount r).state (base + 13)) =
    (headerAfterCount r).state (readerExit (headerCount r).valid (base + 59) failure) at first
  have seed := headerSeed_run program (base + 59) (base + 63) (headerAfterCount r) ps.2.2.2.1
  have second := unary_run program (base + 63) .gate (base + 109) failure
    (headerSeed (headerAfterCount r)) (headerSeed (headerAfterCount r)).input ps.2.2.2.2.1
  change BitRegister.run program (headerGateCount r).fuel
      ((headerSeed (headerAfterCount r)).state (base + 63)) =
    (headerAfterGates r).state (readerExit (headerGateCount r).valid (base + 109) failure) at second
  cases hm : (headerMarker r).valid with
  | false => simpa only [headerResult, hm, readerExit] using marker
  | true =>
      simp only [hm, readerExit] at marker
      cases hn : (headerCount r).valid with
      | false =>
          simp only [headerResult, hm, hn, readerExit]
          rw [BitRegister.run_add, marker, BitRegister.run_add, clear]
          simpa only [hn, readerExit] using first
      | true =>
          simp only [hn, readerExit] at first
          cases hg : (headerGateCount r).valid with
          | false =>
              simp only [headerResult, hm, hn, hg, readerExit]
              rw [BitRegister.run_add, marker, BitRegister.run_add, clear,
                BitRegister.run_add, first, BitRegister.run_add, seed]
              simpa only [hg, readerExit] using second
          | true =>
              simp only [hg, readerExit] at second
              simp only [headerResult, hm, hn, hg, readerExit]
              rw [BitRegister.run_add, marker, BitRegister.run_add, clear,
                BitRegister.run_add, first, BitRegister.run_add, seed, BitRegister.run_add, second]
              exact headerFinish_run program (base + 109) next (headerAfterGates r) ps.2.2.2.2.2

theorem header_result_bound (r : Registers) : (headerResult r).fuel ≤ 6 * r.input.length + 19 := by
  have marker := matchScan_bounds LockedNAND.Token.version0.bits r.input
  change (headerMarker r).fuel ≤ 8 ∧ (headerMarker r).rest.length ≤ r.input.length at marker
  have first := unaryScan_bounds (headerMarker r).rest
  change (headerCount r).fuel ≤ 3 * (headerMarker r).rest.length + 1 ∧
    (headerCount r).rest.length + 4 * (headerCount r).added ≤ (headerMarker r).rest.length at first
  have second := unaryScan_bounds (headerAfterCount r).input
  change (headerGateCount r).fuel ≤ 3 * (headerCount r).rest.length + 1 ∧
    (headerGateCount r).rest.length + 4 * (headerGateCount r).added ≤ (headerCount r).rest.length at second
  cases hm : (headerMarker r).valid <;> cases hn : (headerCount r).valid <;>
    cases hg : (headerGateCount r).valid <;> simp only [headerResult, hm, hn, hg] <;> omega

def headerBits (inputs gates : Nat) (suffix : BitString) : BitString :=
  LockedNAND.Token.version0.bits ++
    (LockedNAND.encodeTokens (LockedNAND.encodeNatTokens inputs) ++
      (LockedNAND.encodeTokens (LockedNAND.encodeNatTokens gates) ++ suffix))

def readHeader (inputs gates : Nat) (r : Registers) (suffix : BitString) : Registers :=
  {r with
    input := suffix
    inputs := List.replicate inputs true
    width := List.replicate (inputs + 2 + gates) true
    gate := List.replicate (inputs + 2) true
    left := List.replicate inputs true}

theorem header_result_canonical (inputs gates : Nat) (r : Registers) (suffix : BitString) :
    headerResult {r with input := headerBits inputs gates suffix} =
      ⟨8 + (1 + ((9 * inputs + 8) + (4 + ((9 * gates + 8) + 4)))),
        readHeader inputs gates r suffix, true⟩ := by
  simp only [headerResult, headerMarker, headerBits, matchScan_prefix,
    headerCount, unaryScan_canonical, headerGateCount, headerAfterCount, headerBeforeCount,
    unaryResultRegisters, Operand.write, Operand.value, headerSeed, headerAfterGates,
    headerFinish, List.append_nil, readHeader]
  rw [show inputs + 2 + gates = gates + (inputs + 1 + 1) by omega, unaryWord_add]
  rfl

end PNP.Concrete.NANDFrontend
