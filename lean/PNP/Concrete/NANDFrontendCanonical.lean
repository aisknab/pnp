/-
Copyright (c) 2026 PNP Labs.

Exact byte-level semantics of the closed polynomial frontend on every encoded
raw circuit. This is equality to the specified frontend formula and original
width record, not merely equisatisfiability.
-/

import PNP.Concrete.NANDFrontendPolynomial

namespace PNP.Concrete.NANDFrontend

open BitRegister

theorem circuit_header_encoding (circuit : LockedNAND.RawCircuit) :
    LockedNAND.encodeCircuit circuit =
      headerBits circuit.inputCount circuit.gates.length
        (gateListInput circuit.gates (outputBits circuit.output)) := by
  simp only [LockedNAND.encodeCircuit, LockedNAND.encodeCircuitTokens,
    LockedNAND.encodeTokens, circuitBits_append, headerBits, gateListInput, outputBits,
    List.append_assoc, List.append_nil, List.cons_append, List.nil_append]

theorem accepted_store_unique (p : Program 9) (first second : Nat)
    (start : BitRegister.Configuration 9) (left right : Store 9)
    (hl : BitRegister.run p first start = ⟨.accepted, left⟩)
    (hr : BitRegister.run p second start = ⟨.accepted, right⟩) : left = right := by
  cases Nat.le_total first second with
  | inl le =>
      have split : second = first + (second - first) := by omega
      have equal : BitRegister.run p second start = ⟨.accepted, left⟩ := by
        rw [split, BitRegister.run_add, hl, BitRegister.run_accepted]
      exact congrArg BitRegister.Configuration.store (equal.symm.trans hr)
  | inr le =>
      have split : first = second + (first - second) := by omega
      have equal : BitRegister.run p first start = ⟨.accepted, right⟩ := by
        rw [split, BitRegister.run_add, hr, BitRegister.run_accepted]
      exact congrArg BitRegister.Configuration.store (hl.symm.trans equal)

theorem circuit_canonical_execution (circuit : LockedNAND.RawCircuit) :
    ∃ fuel store, BitRegister.run program fuel (BitRegister.initial program (LockedNAND.encodeCircuit circuit)) =
        ⟨.accepted, store⟩ ∧ store.get 8 = circuitData circuit := by
  let n := circuit.inputCount
  let suffix := outputBits circuit.output
  let body := gateListInput circuit.gates suffix
  let r0 := initialRegisters []
  let rh := readHeader n circuit.gates.length r0 body
  let rc := withConstants rh
  let rg := traversedGates n 0 circuit.gates rc suffix
  let ro : Registers := {rg with input := [], left := List.replicate (sourceIndex n circuit.output) true}
  let rf := finishedOutput ro
  let hf := 8 + (1 + ((9 * n + 8) + (4 + ((9 * circuit.gates.length + 8) + 4))))
  let gf := gateListFuel n 0 circuit.gates
  let ofuel := sourceReadFuel circuit.output + (8 + (8 + (1 + outputTailFuel ro)))
  have ps := program_segments
  have hheader : BitRegister.run program hf ((initialRegisters (LockedNAND.encodeCircuit circuit)).state 0) =
      rh.state 113 := by
    have h := header_result_run program 0 113 666
      {r0 with input := headerBits n circuit.gates.length body} ps.1
    rw [header_result_canonical] at h
    rw [circuit_header_encoding]
    exact h
  have hconstants := constants_run program 113 177 rh ps.2.1
  have hgates : BitRegister.run program gf (rc.state 177) = rg.state 492 := by
    have h := gateList_canonical program 177 492 666 n 0 rc circuit.gates suffix ps.2.2.1
    exact h
  have frame := traversedGates_frame n 0 circuit.gates rc suffix
  have original : rg.inputs = List.replicate n true := frame.2.1
  have input : rg.input = suffix := frame.1
  have width : rg.width = List.replicate (n + 2 + circuit.gates.length) true := frame.2.2.2.1
  have reversed : rg.reversed =
      (encodeTokenPairs (encodeClauseListTokens (gatesClauses n 0 circuit.gates))).reverse ++
        (constantBits n).reverse := by
    have h := traversedGates_reversed n 0 circuit.gates rc suffix
    simpa only [rg, rc, rh, withConstants, readHeader, r0, initialRegisters,
      List.length_replicate, List.append_nil] using h
  have houtcome : outputResult rg = ⟨ofuel, rf, true⟩ := by
    have h := output_result_canonical n circuit.output rg original
    have unchanged : {rg with input := outputBits circuit.output} = rg := by
      change {rg with input := suffix} = rg
      rw [← input]
    rw [unchanged] at h
    exact h
  have houtput : BitRegister.run program ofuel (rg.state 492) = rf.state 665 := by
    have h := output_result_run program 492 665 666 rg ps.2.2.2.1
    rw [houtcome] at h
    exact h
  refine ⟨hf + (constantsFuel rh + (gf + (ofuel + 1))), rf.store, ?_, ?_⟩
  · rw [initial_registers, BitRegister.run_add, hheader, BitRegister.run_add, hconstants,
      BitRegister.run_add, hgates, BitRegister.run_add, houtput]
    simp only [BitRegister.run, BitRegister.step, Registers.state, ps.2.2.2.2.1,
      Instruction.execute, Instruction.nextControl, Instruction.update]
  · change (finishedOutput ro).output = circuitData circuit
    rw [finishedOutput_data]
    simp only [ro]
    rw [original, width, reversed]
    simp only [List.length_replicate, List.reverse_append, List.reverse_reverse]
    simp only [circuitData, recordData, CNFRegisterDecoder.formulaData, CNFRegisterDecoder.clausesSuffix,
      formula, clauseTokens_append, encodeTokenPairs_append, encodeClauseListTokens,
      constantBits, encodeTokenPairs, CNFToken.bits, List.append_assoc, List.append_nil,
      List.cons_append, List.nil_append, n]

theorem polynomial_canonical (circuit : LockedNAND.RawCircuit) :
    polynomial.output (LockedNAND.encodeCircuit circuit) = circuitData circuit := by
  obtain ⟨fuel, store, checked, value⟩ := circuit_canonical_execution circuit
  have h := frontend_run (initialRegisters (LockedNAND.encodeCircuit circuit))
  rw [← initial_registers] at h
  have stores := accepted_store_unique program
    (frontendFuel (initialRegisters (LockedNAND.encodeCircuit circuit))) fuel
    (BitRegister.initial program (LockedNAND.encodeCircuit circuit))
    (frontendFinal (initialRegisters (LockedNAND.encodeCircuit circuit))).store store h checked
  rw [polynomial_output]
  change (frontendFinal (initialRegisters (LockedNAND.encodeCircuit circuit))).store.get 8 = _
  rw [stores]
  exact value

end PNP.Concrete.NANDFrontend
