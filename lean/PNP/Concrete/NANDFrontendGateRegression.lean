import PNP.Concrete.NANDFrontendGate

namespace PNP.Concrete.NANDFrontend

private def gateProgram : BitRegister.Program 9 := ⟨gateCode 0 93 ++ [.accept], 0, 0, 8⟩

private theorem gateProgram_segment : Segment gateProgram 0 (gateCode 0 93) := by
  intro offset inside
  simp only [gateProgram, Nat.zero_add]
  exact lookup_append_left _ _ offset inside

example (r : Registers) :
    BitRegister.run gateProgram (gateFuel r) (r.state 0) =
      ({r with temp := [], reversed := (gateBits r).reverse ++ r.reversed}).state 93 :=
  gate_run gateProgram 0 93 r gateProgram_segment
example (r : Registers) :
    gateFuel r = 8 * r.left.length + 8 * r.right.length + 20 * r.gate.length + 66 := rfl
example (r : Registers) :
    (gateBits r).length = 4 * r.left.length + 4 * r.right.length + 10 * r.gate.length + 48 :=
  gateBits_length r
example (r : Registers) : gateFuel r + 30 = 2 * (gateBits r).length := gateFuel_length r
example (inputs ordinal : Nat) (gate : LockedNAND.RawGate) (r : Registers) :
    gateBits {r with
      left := List.replicate (sourceIndex inputs gate.left) true
      right := List.replicate (sourceIndex inputs gate.right) true
      gate := List.replicate (inputs + 2 + ordinal) true} =
        encodeTokenPairs (encodeClauseListTokens (gateClauses inputs ordinal gate)) :=
  gateBits_canonical inputs ordinal gate r
example (r : Registers) : (BitRegister.run gateProgram (gateFuel r) (r.state 0)).store.get 0 = r.input := by
  rw [gate_run gateProgram 0 93 r gateProgram_segment]
  rfl
example (r : Registers) : (BitRegister.run gateProgram (gateFuel r) (r.state 0)).store.get 1 = r.inputs := by
  rw [gate_run gateProgram 0 93 r gateProgram_segment]
  rfl
example (r : Registers) : (BitRegister.run gateProgram (gateFuel r) (r.state 0)).store.get 6 = [] := by
  rw [gate_run gateProgram 0 93 r gateProgram_segment]
  rfl
example (r : Registers) : (BitRegister.run gateProgram (gateFuel r) (r.state 0)).store.get 8 = r.output := by
  rw [gate_run gateProgram 0 93 r gateProgram_segment]
  rfl

#print axioms gate_segments
#print axioms gate_run
#print axioms gateBits_canonical
#print axioms gateBits_length
#print axioms gateFuel_length

end PNP.Concrete.NANDFrontend
