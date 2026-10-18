import PNP.Concrete.ResidualReduction.MatrixSolutionInstructions
import PNP.Concrete.ResidualReduction.MatrixSolutionMapRegression

namespace PNP.Concrete.ResidualReduction.MatrixSolutionInstructions.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionHistory
open PNP.Concrete.ResidualReduction.MatrixReconstruction

-- Actual forward histories, not caller-supplied maps, determine every parameter.
example : (fromRows 2 [(false, (true, false))]).encode = [true, false, false] := rfl
example : (computedSpace 2 [(false, (true, false))]).parameters = 1 := rfl
example : mapBits (computedSpace 2 [(false, (true, false))]).forms =
    [true, false, false, false] := rfl
example : (fromRows 2 [(true, (true, true))]).encode = [false, true, true, true] := rfl
example : mapBits (computedSpace 2 [(true, (true, true))]).forms =
    [true, true, true, false] := rfl

example : (result 0 []).core.output = [true, false] := rfl
example : (result 0 [true]).core.output = [false] := rfl
example : (result 1 []).core.output = [true, true, false, true, false] := rfl
example : (result 1 [(true, true)]).core.output = [true, false, true] := rfl
example : (result 1 [(false, true)]).core.output = [false] := rfl
example : (result 1 [(true, false), (true, true)]).core.output = [false] := rfl
example : (result 2 [(false, (true, false))]).core.output =
    [true, true, false, true, false, false, false] := rfl
example : (result 2 [(true, (true, true))]).core.output =
    [true, true, false, true, true, true, false] := rfl

-- Literal execution of the full forward/check/reconstruct/serialize program.
set_option maxRecDepth 4096 in
example : BitRegister.run program (phaseFuel 0 [] + 1) ⟨.running 0, (start 0 []).store⟩ =
    ⟨.accepted, (result 0 []).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run program (phaseFuel 0 [true] + 1) ⟨.running 0, (start 0 [true]).store⟩ =
    ⟨.accepted, (result 0 [true]).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run program (phaseFuel 1 [] + 1) ⟨.running 0, (start 1 []).store⟩ =
    ⟨.accepted, (result 1 []).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run program (phaseFuel 1 [(true, true)] + 1)
    ⟨.running 0, (start 1 [(true, true)]).store⟩ =
    ⟨.accepted, (result 1 [(true, true)]).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run program (phaseFuel 1 [(false, true)] + 1)
    ⟨.running 0, (start 1 [(false, true)]).store⟩ =
    ⟨.accepted, (result 1 [(false, true)]).store⟩ := rfl

example (n : Nat) (rows : System n) :
    Exec phase (start n rows).store (phaseFuel n rows) (result n rows).store := phase_exec n rows
example (n : Nat) (rows : System n) :
    (result n rows).core.output = (solutionCodec n).encode (solve n rows) := result_output n rows
example (n : Nat) (rows : System n) :
    (solutionCodec n).decode (result n rows).core.output = some (solve n rows) := by
  rw [result_output]
  exact solution_roundtrip n (solve n rows)
example (n : Nat) (rows : System n) :
    (BitRegister.run program (phaseFuel n rows + 1)
      ⟨.running 0, (start n rows).store⟩).store.get 8 = (solutionCodec n).encode (solve n rows) :=
  program_output n rows
example (n : Nat) (rows : System n) :
    phaseFuel n rows ≤ 80 * n * n * (rows.length + 1) + 5 * rows.length +
      (50 * (n + 2) * (n + 1) + 1) * n + 3 * n + 20 := phaseFuel_bound n rows
example (n : Nat) (rows : System n) :
    actualFuel n rows ≤ (50 * (n + 2) * (n + 1) + 1) * n + 1 := actualFuel_bound n rows
example (n : Nat) (rows : System n) :
    solve n rows =
      if satisfies (MatrixSweep.residue n rows) () then some (computedSpace n rows) else none :=
  computedSpace_exact n rows

end PNP.Concrete.ResidualReduction.MatrixSolutionInstructions.Regression
