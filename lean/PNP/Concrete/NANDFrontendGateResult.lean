/-
Copyright (c) 2026 PNP Labs.

All-input execution of the connected gate reader and emitter. No decoded-gate,
well-formedness, termination or source-index premise is supplied by the caller.
-/

import PNP.Concrete.NANDFrontendGateLoop

namespace PNP.Concrete.NANDFrontend

open BitRegister

structure BlockResult where
  fuel : Nat
  state : Registers
  valid : Bool
deriving Repr

def gateLeft (r : Registers) : SourceResult := sourceScan r.inputs r.left r.input

def afterGateLeft (r : Registers) : Registers :=
  sourceResultRegisters .left r (gateLeft r)

def gateRight (r : Registers) : SourceResult :=
  sourceScan (afterGateLeft r).inputs (afterGateLeft r).right (afterGateLeft r).input

def afterGateRight (r : Registers) : Registers :=
  sourceResultRegisters .right (afterGateLeft r) (gateRight r)

def gateMarker (r : Registers) : MatchResult :=
  matchScan LockedNAND.Token.gateEnd.bits (afterGateRight r).input

def beforeGateEmission (r : Registers) : Registers :=
  {afterGateRight r with input := (gateMarker r).rest}

def afterGateEmission (r : Registers) : Registers :=
  {r with gate := true :: r.gate, temp := [], reversed := (gateBits r).reverse ++ r.reversed}

def gateReadResult (r : Registers) : BlockResult :=
  match (gateLeft r).valid with
  | false => ⟨(gateLeft r).fuel, afterGateLeft r, false⟩
  | true =>
      match (gateRight r).valid with
      | false => ⟨(gateLeft r).fuel + (gateRight r).fuel, afterGateRight r, false⟩
      | true =>
          match (gateMarker r).valid with
          | false =>
              ⟨(gateLeft r).fuel + (gateRight r).fuel + (gateMarker r).fuel,
                beforeGateEmission r, false⟩
          | true =>
              ⟨(gateLeft r).fuel + (gateRight r).fuel + (gateMarker r).fuel +
                  gateFuel (beforeGateEmission r) + 1,
                afterGateEmission (beforeGateEmission r), true⟩

theorem gateRead_result_run (program : Program 9) (base next failure : Nat) (r : Registers)
    (placed : Segment program base (gateReadCode base next failure)) :
    BitRegister.run program (gateReadResult r).fuel (r.state base) =
      (gateReadResult r).state.state (readerExit (gateReadResult r).valid next failure) := by
  have ps := gateRead_segments program base next failure placed
  have left := source_run program base .left (base + 98) failure r r.input ps.1
  change BitRegister.run program (gateLeft r).fuel (r.state base) =
    (afterGateLeft r).state (readerExit (gateLeft r).valid (base + 98) failure) at left
  have right := source_run program (base + 98) .right (base + 196) failure
    (afterGateLeft r) (afterGateLeft r).input ps.2.1
  change BitRegister.run program (gateRight r).fuel ((afterGateLeft r).state (base + 98)) =
    (afterGateRight r).state (readerExit (gateRight r).valid (base + 196) failure) at right
  have marker := marker_run program (base + 196) .gateEnd (base + 208) failure
    (afterGateRight r) (afterGateRight r).input ps.2.2.1
  change BitRegister.run program (gateMarker r).fuel ((afterGateRight r).state (base + 196)) =
    (beforeGateEmission r).state (readerExit (gateMarker r).valid (base + 208) failure) at marker
  cases hl : (gateLeft r).valid with
  | false =>
      simpa only [gateReadResult, hl, readerExit] using left
  | true =>
      simp only [hl, readerExit] at left
      cases hr : (gateRight r).valid with
      | false =>
          simp only [gateReadResult, hl, hr, readerExit]
          rw [BitRegister.run_add, left]
          simpa only [hr, readerExit] using right
      | true =>
          simp only [hr, readerExit] at right
          cases hm : (gateMarker r).valid with
          | false =>
              simp only [gateReadResult, hl, hr, hm, readerExit]
              rw [BitRegister.run_add, BitRegister.run_add, left, right]
              simpa only [hm, readerExit] using marker
          | true =>
              simp only [hm, readerExit] at marker
              simp only [gateReadResult, hl, hr, hm, readerExit]
              rw [BitRegister.run_add, BitRegister.run_add, BitRegister.run_add,
                BitRegister.run_add, left, right, marker,
                gate_run program (base + 208) (base + 301) (beforeGateEmission r) ps.2.2.2.1]
              simp only [BitRegister.run, BitRegister.step, Registers.state, ps.2.2.2.2,
                Instruction.execute, Instruction.nextControl, Instruction.update,
                Registers.store, Store.get, Store.set, Store.indexCases, afterGateEmission]

theorem gateRead_result_bound (r : Registers) :
    (gateReadResult r).fuel ≤ 127 * (r.inputs.length + r.gate.length + r.input.length + 1) := by
  have leftBound := sourceScan_bounds r.inputs r.left r.input
  have rightBound := sourceScan_bounds (afterGateLeft r).inputs
    (afterGateLeft r).right (afterGateLeft r).input
  have markerBound := (matchScan_bounds LockedNAND.Token.gateEnd.bits (afterGateRight r).input).1
  change (gateLeft r).fuel ≤ 3 * r.input.length + 1 ∧
    (gateLeft r).rest.length ≤ r.input.length at leftBound
  change (gateRight r).fuel ≤ 3 * (gateLeft r).rest.length + 1 ∧
    (gateRight r).rest.length ≤ (gateLeft r).rest.length at rightBound
  change (gateMarker r).fuel ≤ 8 at markerBound
  cases hl : (gateLeft r).valid with
  | false => simp only [gateReadResult, hl]; omega
  | true =>
      have leftSize := (sourceScan_success r.inputs r.left r.input hl).2
      change (gateLeft r).value.length ≤ r.inputs.length + r.input.length + 2 at leftSize
      cases hr : (gateRight r).valid with
      | false => simp only [gateReadResult, hl, hr]; omega
      | true =>
          have rightSize := (sourceScan_success (afterGateLeft r).inputs
            (afterGateLeft r).right (afterGateLeft r).input hr).2
          change (gateRight r).value.length ≤ r.inputs.length + (gateLeft r).rest.length + 2 at rightSize
          cases hm : (gateMarker r).valid with
          | false => simp only [gateReadResult, hl, hr, hm]; omega
          | true =>
              simp only [gateReadResult, hl, hr, hm, gateFuel, beforeGateEmission,
                afterGateRight, afterGateLeft, sourceResultRegisters, Operand.write]
              omega

theorem gateRead_result_progress (r : Registers) (valid : (gateReadResult r).valid = true) :
    (gateReadResult r).state.input.length < r.input.length ∧
      (gateReadResult r).state.inputs = r.inputs ∧
      (gateReadResult r).state.gate.length = r.gate.length + 1 := by
  cases hl : (gateLeft r).valid with
  | false => simp only [gateReadResult, hl] at valid; cases valid
  | true =>
      cases hr : (gateRight r).valid with
      | false => simp only [gateReadResult, hl, hr] at valid; cases valid
      | true =>
          cases hm : (gateMarker r).valid with
          | false => simp only [gateReadResult, hl, hr, hm] at valid; cases valid
          | true =>
              have leftProgress := (sourceScan_success r.inputs r.left r.input hl).1
              have rightBound := (sourceScan_bounds (afterGateLeft r).inputs
                (afterGateLeft r).right (afterGateLeft r).input).2
              have markerBound := (matchScan_bounds LockedNAND.Token.gateEnd.bits (afterGateRight r).input).2
              change (gateLeft r).rest.length < r.input.length at leftProgress
              change (gateRight r).rest.length ≤ (gateLeft r).rest.length at rightBound
              change (gateMarker r).rest.length ≤ (gateRight r).rest.length at markerBound
              simp only [gateReadResult, hl, hr, hm, afterGateEmission, beforeGateEmission,
                afterGateRight, afterGateLeft, sourceResultRegisters, Operand.write, List.length_cons]
              exact ⟨by omega, True.intro, True.intro⟩

end PNP.Concrete.NANDFrontend
