/-
Copyright (c) 2026 PNP Labs.

One finite loop reads and emits every gate of an arbitrary encoded circuit
list. The theorem is exact byte equality and exact source-instruction cost.
All-input loop termination and the complete header/output wrapper remain
separate obligations before this becomes a closed polynomial-time frontend.
-/

import PNP.Concrete.NANDFrontendGateRead

namespace PNP.Concrete.NANDFrontend

open BitRegister

def gateLoopCode (base next failure : Nat) : List (Instruction 9) :=
  [.branch 0 failure (base + 1) (base + 303)] ++
    gateReadCode (base + 1) base failure ++
    markerCode (base + 303) .programEnd next failure

theorem gateLoopCode_length (base next failure : Nat) :
    (gateLoopCode base next failure).length = 315 := by
  simp only [gateLoopCode, List.length_append, gateReadCode_length, markerCode_length]
  rfl

theorem gateLoop_segments (program : Program 9) (base next failure : Nat)
    (placed : Segment program base (gateLoopCode base next failure)) :
    BitRegister.lookup program.code base = some (.branch 0 failure (base + 1) (base + 303)) ∧
      Segment program (base + 1) (gateReadCode (base + 1) base failure) ∧
      Segment program (base + 303) (markerCode (base + 303) .programEnd next failure) := by
  have h0 := placed 0 (by rw [gateLoopCode_length]; decide)
  simp only [Nat.add_zero, gateLoopCode, List.cons_append, BitRegister.lookup] at h0
  have body := Segment.slice [.branch 0 failure (base + 1) (base + 303)]
    (gateReadCode (base + 1) base failure) (markerCode (base + 303) .programEnd next failure) placed
  have ending := Segment.tail
    ([.branch 0 failure (base + 1) (base + 303)] ++ gateReadCode (base + 1) base failure)
    (markerCode (base + 303) .programEnd next failure) placed
  rw [List.length_append, gateReadCode_length] at ending
  exact ⟨h0, body, ending⟩

theorem gateLoop_zero (program : Program 9) (base next failure : Nat)
    (r : Registers) (rest : BitString)
    (placed : Segment program base (gateLoopCode base next failure)) :
    BitRegister.run program 1 (({r with input := false :: rest}).state base) =
      ({r with input := false :: rest}).state (base + 1) := by
  have h0 := (gateLoop_segments program base next failure placed).1
  simp only [BitRegister.run, BitRegister.step, Registers.state, h0,
    Instruction.execute, Instruction.nextControl, Instruction.update,
    Registers.store, Store.get, Store.indexCases]

theorem gateLoop_end (program : Program 9) (base next failure : Nat)
    (r : Registers) (suffix : BitString)
    (placed : Segment program base (gateLoopCode base next failure)) :
    BitRegister.run program 9 (({r with input := LockedNAND.Token.programEnd.bits ++ suffix}).state base) =
      ({r with input := suffix}).state next := by
  have segments := gateLoop_segments program base next failure placed
  have start : BitRegister.run program 1
      (({r with input := LockedNAND.Token.programEnd.bits ++ suffix}).state base) =
        ({r with input := LockedNAND.Token.programEnd.bits ++ suffix}).state (base + 303) := by
    simp only [BitRegister.run, BitRegister.step, Registers.state, segments.1,
      Instruction.execute, Instruction.nextControl, Instruction.update,
      Registers.store, Store.get, Store.indexCases, LockedNAND.Token.bits,
      List.cons_append, List.nil_append]
  change BitRegister.run program (1 + 8) _ = _
  rw [BitRegister.run_add, start]
  exact marker_canonical program (base + 303) .programEnd next failure r suffix segments.2.2

def gateListInput (gates : List LockedNAND.RawGate) (suffix : BitString) : BitString :=
  LockedNAND.encodeTokens (LockedNAND.encodeGateListTokens gates) ++
    (LockedNAND.Token.programEnd.bits ++ suffix)

theorem gateListInput_cons (gate : LockedNAND.RawGate) (rest : List LockedNAND.RawGate)
    (suffix : BitString) :
    gateListInput (gate :: rest) suffix =
      LockedNAND.encodeTokens (LockedNAND.encodeGateTokens gate) ++ gateListInput rest suffix := by
  simp only [gateListInput, LockedNAND.encodeGateListTokens, circuitBits_append, List.append_assoc]

theorem encodedGate_starts_zero (gate : LockedNAND.RawGate) (suffix : BitString) :
    ∃ rest, LockedNAND.encodeTokens (LockedNAND.encodeGateTokens gate) ++ suffix = false :: rest := by
  cases gate with
  | mk left right =>
      cases left with
      | input index => exact ⟨_, rfl⟩
      | gate index => exact ⟨_, rfl⟩
      | constant bit => cases bit <;> exact ⟨_, rfl⟩

def gateListFuel (inputs : Nat) : Nat → List LockedNAND.RawGate → Nat
  | _, [] => 9
  | ordinal, gate :: rest => 1 + (gateReadFuel inputs ordinal gate + gateListFuel inputs (ordinal + 1) rest)

def traversalStart (inputs ordinal : Nat) (r : Registers) (input : BitString) : Registers :=
  {r with
    input := input
    inputs := List.replicate inputs true
    gate := List.replicate (inputs + 2 + ordinal) true}

def traversedGates (inputs : Nat) : Nat → List LockedNAND.RawGate → Registers → BitString → Registers
  | ordinal, [], r, suffix => traversalStart inputs ordinal r suffix
  | ordinal, gate :: rest, r, suffix =>
      traversedGates inputs (ordinal + 1) rest
        (emittedGate inputs ordinal gate r (gateListInput rest suffix)) suffix

theorem gateList_canonical (program : Program 9) (base next failure inputs ordinal : Nat)
    (r : Registers) (gates : List LockedNAND.RawGate) (suffix : BitString)
    (placed : Segment program base (gateLoopCode base next failure)) :
    BitRegister.run program (gateListFuel inputs ordinal gates)
        ((traversalStart inputs ordinal r (gateListInput gates suffix)).state base) =
      (traversedGates inputs ordinal gates r suffix).state next := by
  induction gates generalizing ordinal r with
  | nil => exact gateLoop_end program base next failure (traversalStart inputs ordinal r []) suffix placed
  | cons gate rest ih =>
      have segments := gateLoop_segments program base next failure placed
      obtain ⟨tail, inputEq⟩ := encodedGate_starts_zero gate (gateListInput rest suffix)
      have start : BitRegister.run program 1
          ((traversalStart inputs ordinal r (gateListInput (gate :: rest) suffix)).state base) =
            (traversalStart inputs ordinal r (gateListInput (gate :: rest) suffix)).state (base + 1) := by
        simp only [traversalStart, gateListInput_cons, inputEq]
        exact gateLoop_zero program base next failure (traversalStart inputs ordinal r []) tail placed
      have body := gateRead_canonical program (base + 1) base failure inputs ordinal r
        gate (gateListInput rest suffix) segments.2.1
      change BitRegister.run program
        (1 + (gateReadFuel inputs ordinal gate + gateListFuel inputs (ordinal + 1) rest)) _ = _
      rw [BitRegister.run_add, start, BitRegister.run_add]
      have body' : BitRegister.run program (gateReadFuel inputs ordinal gate)
          ((traversalStart inputs ordinal r (gateListInput (gate :: rest) suffix)).state (base + 1)) =
            (emittedGate inputs ordinal gate r (gateListInput rest suffix)).state base := by
        simpa only [traversalStart, gateListInput_cons] using body
      rw [body']
      exact ih (ordinal + 1) (emittedGate inputs ordinal gate r (gateListInput rest suffix))

theorem clauseTokens_append (left right : List (List CNFLiteral)) :
    encodeClauseListTokens (left ++ right) =
      encodeClauseListTokens left ++ encodeClauseListTokens right := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.cons_append, encodeClauseListTokens, ih, List.append_assoc]

theorem traversedGates_reversed (inputs ordinal : Nat) (gates : List LockedNAND.RawGate)
    (r : Registers) (suffix : BitString) :
    (traversedGates inputs ordinal gates r suffix).reversed =
      (encodeTokenPairs (encodeClauseListTokens (gatesClauses inputs ordinal gates))).reverse ++ r.reversed := by
  induction gates generalizing ordinal r with
  | nil => rfl
  | cons gate rest ih =>
      simp only [traversedGates, ih, gatesClauses, clauseTokens_append,
        encodeTokenPairs_append, List.reverse_append, List.append_assoc, emittedGate]

theorem traversedGates_frame (inputs ordinal : Nat) (gates : List LockedNAND.RawGate)
    (r : Registers) (suffix : BitString) :
    (traversedGates inputs ordinal gates r suffix).input = suffix ∧
      (traversedGates inputs ordinal gates r suffix).inputs = List.replicate inputs true ∧
      (traversedGates inputs ordinal gates r suffix).gate = List.replicate (inputs + 2 + ordinal + gates.length) true ∧
      (traversedGates inputs ordinal gates r suffix).width = r.width ∧
      (traversedGates inputs ordinal gates r suffix).output = r.output := by
  induction gates generalizing ordinal r with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | cons gate rest ih =>
      have h := ih (ordinal + 1) (emittedGate inputs ordinal gate r (gateListInput rest suffix))
      have index : inputs + 2 + ordinal + (gate :: rest).length =
          inputs + 2 + (ordinal + 1) + rest.length := by
        simp only [List.length_cons]
        omega
      rw [index]
      exact h

end PNP.Concrete.NANDFrontend
