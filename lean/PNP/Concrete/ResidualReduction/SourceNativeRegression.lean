import PNP.Concrete.ResidualReduction.SourceNativeLabel
import Lean

/-! Focused tests for native sparse-label conversion. These run only the newly
added input boundary, not the unchanged history or successor suites. General
kernel contracts establish correctness for arbitrary inputs; finite executions
check truncation, exact suffix preservation, range rejection and complete state.
This is not yet the complete native-system conversion machine. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeRegression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction

private def leftLabel : NativeEquations.Row 2 := (0,false)
private def rightLabel : NativeEquations.Row 2 := (1,true)

example : SourceNativeEncoding.termsWord [leftLabel,leftLabel,rightLabel] true =
    [false,false,false,true,true] := by decide
example : SourceNativeEncoding.termsWord [rightLabel,rightLabel] false =
    [false,false,false,false,false] := by decide
example : SourceNativeEncoding.termsWord ([] : NativeCoefficients.Coefficients 0) true = [true] := rfl
example {c : Nat} (D : NativeSparseSystem.System c) :
    SourceHistoryEncoding.packet (NativeSource.family D) = SourceNativeEncoding.familyPacket D :=
  SourceNativeEncoding.family_packet D
example {c : Nat} (D : NativeSparseSystem.System c) :
    let L := (NativeOutputPacket.encode (.system c D)).length
    (SourceNativeEncoding.familyPacket D).length ≤ 4 * (L * L) + 6 * L + 2 :=
  SourceNativeEncoding.packet_size_bound D
example (input : BitString) :
    Exec SourceNativeRowIndex.block (SourceNativeRowIndex.state input 0 false).store
      (SourceNativeRowIndex.fuel input)
      (SourceNativeRowIndex.state (SourceNativeRowIndex.parse input).rest
        (SourceNativeRowIndex.parse input).index (SourceNativeRowIndex.parse input).valid).store :=
  SourceNativeRowIndex.block_exec input
example (input : BitString) (n : Nat) :
    SourceNativeCoordinate.result input n n = SourceNativeCoordinate.failed input := by
  simp only [SourceNativeCoordinate.result,Nat.lt_irrefl,↓reduceIte]
example (input : BitString) (n j : Nat) :
    Exec SourceNativeCoordinate.block (SourceNativeCoordinate.initial input n j).store
      (SourceNativeCoordinate.fuel n j) (SourceNativeCoordinate.result input n j).store :=
  SourceNativeCoordinate.block_exec input n j
example (input : BitString) (n : Nat) :
    Exec SourceNativeLabel.block (SourceNativeLabel.initial input n)
      (SourceNativeLabel.fuel input n) (SourceNativeLabel.result input n) :=
  SourceNativeLabel.block_exec input n
example (input : BitString) (n : Nat) :
    SourceNativeLabel.fuel input n ≤ 15 * input.length + 3 * n + 31 :=
  SourceNativeLabel.fuel_bound input n

private def check {count : Nat} (counter : IO.Ref Nat) (p : Program count)
    (start expected : Store count) (ticks : Nat) (label : String) : IO Unit := do
  let actual := BitRegister.run p (ticks + 1) ⟨.running 0,start⟩
  if actual.control != .accepted then throw (IO.userError (label ++ ": did not halt at its source bound"))
  for i in List.finRange count do
    if actual.store.get i != expected.get i then
      throw (IO.userError (label ++ ": complete register state differs"))
  counter.modify (· + 1)

#eval (show IO Unit from do
  let counter ← IO.mkRef 0
  let inputs : List BitString := [[],[true],[false],[false,false],[false,true],
    [true,false],[true,true,true],[true,false,false],[true,false,true],
    [false,true,false,true],natural 3 ++ [true,false,true],natural 5 ++ [false],
    List.replicate 9 true,natural 7 ++ [true,true,true,false]]
  for input in inputs do
    let p := SourceNativeRowIndex.parse input
    if SourceNativeRowIndex.fuel input > 7 * input.length + 19 ||
        p.rest.length > input.length || p.index > 2 * input.length + 1 ||
        (p.valid && p.rest.length >= input.length) then
      throw (IO.userError "Native row reader bound differs")
    check counter (SourceNativeRowIndex.block.program 0 8)
      (SourceNativeRowIndex.state input 0 false).store
      (SourceNativeRowIndex.state p.rest p.index p.valid).store
      (SourceNativeRowIndex.fuel input) "Native row reader"
  for n in [0,1,2,5,12] do
    for j in [0,1,n,n + 2,n - 1] do
      for suffix in [[],[true,false]] do
        if SourceNativeCoordinate.fuel n j > 4 * j + 3 * n + 6 then
          throw (IO.userError "Native coordinate bound differs")
        let result := SourceNativeCoordinate.result suffix n j
        if j >= n && (result.sign != [] || result.output != []) then
          throw (IO.userError "Invalid coordinate was not rejected")
        check counter (SourceNativeCoordinate.block.program 0 8)
          (SourceNativeCoordinate.initial suffix n j).store result.store
          (SourceNativeCoordinate.fuel n j) "Checked coordinate"
  for n in [0,1,2,6] do
    for input in inputs do
      if SourceNativeLabel.fuel input n > 15 * input.length + 3 * n + 31 then
        throw (IO.userError "Native label composition bound differs")
      check counter (SourceNativeLabel.block.program 0 8)
        (SourceNativeLabel.initial input n) (SourceNativeLabel.result input n)
        (SourceNativeLabel.fuel input n) "Native label composition"
  for c in [1,3,6] do
    for i in List.finRange c do
      for bit in [false,true] do
        for suffix in [[],[true,false]] do
          let row : NativeEquations.Row c := (i,bit)
          let input := (NativeSystemCodec.rowCodec c).encode row ++ suffix
          let expected := SourceNativeLabel.full
            {SourceNativeRowIndex.state suffix 0 true with output :=
              (SourceNativeEncoding.affineWord
                (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex row))).reverse}
            (List.replicate (2 * c) true)
          check counter (SourceNativeLabel.block.program 0 8)
            (SourceNativeLabel.initial input (2 * c)) expected
            (SourceNativeLabel.fuel input (2 * c)) "Canonical native label"
  IO.println s!"NATIVE_REGRESSIONS_GREEN: {← counter.get} executions")

run_cmd do
  let names := [
    ``SourceNativeEncoding.constant_word,
    ``SourceNativeEncoding.add_word,
    ``SourceNativeEncoding.add_zero_left,
    ``SourceNativeEncoding.add_zero_right,
    ``SourceNativeEncoding.add_comm,
    ``SourceNativeEncoding.add_assoc,
    ``SourceNativeEncoding.coordinate_word,
    ``SourceNativeEncoding.accumulate_exact,
    ``SourceNativeEncoding.accumulate_word,
    ``SourceNativeEncoding.terms_nil,
    ``SourceNativeEncoding.terms_cons,
    ``SourceNativeEncoding.terms_length,
    ``SourceNativeEncoding.terms_false,
    ``SourceNativeEncoding.zeroRow_exact,
    ``SourceNativeEncoding.oneRow_exact,
    ``SourceNativeEncoding.productRow_exact,
    ``SourceNativeEncoding.family_bits,
    ``SourceNativeEncoding.family_packet,
    ``SourceNativeEncoding.input_counts,
    ``SourceNativeEncoding.packet_length,
    ``SourceNativeEncoding.packet_size_bound,
    ``SourceNativeRowIndex.double_exec,
    ``SourceNativeRowIndex.parity_exec,
    ``SourceNativeRowIndex.accepted_exec,
    ``SourceNativeRowIndex.block_exec,
    ``SourceNativeRowIndex.fuel_bound,
    ``SourceNativeRowIndex.parse_bounds,
    ``SourceNativeRowIndex.canonical,
    ``SourceNativeRowIndex.canonical_exec,
    ``SourceNativeCoordinate.prefix_any,
    ``SourceNativeCoordinate.pass_exec,
    ``SourceNativeCoordinate.block_exec,
    ``SourceNativeCoordinate.fuel_bound,
    ``SourceNativeCoordinate.valid_fuel_bound,
    ``SourceNativeCoordinate.coordinate_exec,
    ``SourceNativeLabel.lift_exec,
    ``SourceNativeLabel.expand_exec,
    ``SourceNativeLabel.block_exec,
    ``SourceNativeLabel.fuel_bound,
    ``SourceNativeLabel.canonical_exec,
    ``SourceNativeLabel.canonical_fuel_bound]
  for name in names do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"
  Lean.logInfo m!"NATIVE_AXIOMS_GREEN: {names.length} theorems"

#print axioms PNP.Concrete.ResidualReduction.SourceNativeEncoding.family_packet
#print axioms PNP.Concrete.ResidualReduction.SourceNativeRowIndex.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeCoordinate.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeLabel.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceNativeLabel.canonical_exec

end PNP.Concrete.ResidualReduction.SourceNativeRegression
