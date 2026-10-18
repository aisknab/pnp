import PNP.Concrete.ResidualReduction.MatrixFeasibilityInstructions
import PNP.Concrete.ResidualReduction.MatrixColumnRegression

namespace PNP.Concrete.ResidualReduction.MatrixSweep.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear

example : residue 0 [false, true] = [false, true] := rfl
example : residue 1 [(false, true)] = [true] := rfl
example : historyBits 1 [(false, true)] [] = [false] := rfl
example : residue 1 [(true, false)] = [false] := rfl
example : historyBits 1 [(true, false)] [] = [true, false] := rfl

-- A leading free column is saved, not silently discarded during reconstruction.
example : residue 2 [(false, (true, false))] = [false] := rfl
example : historyBits 2 [(false, (true, false))] [] = [true, false, false] := rfl
example : (solve 2 [(false, (true, false))]).isSome = true := rfl

-- The loop preserves an inconsistent residue and the exact backward history.
example : residue 2 [(true, (false, false)), (true, (false, true))] = [false, true] := rfl
example : historyBits 2 [(true, (false, false)), (true, (false, true))] [] =
    [false, true, false, false] := rfl
example : (solve 2 [(true, (false, false)), (true, (false, true))]).isSome = false := rfl
example : historyBits 2 [(false, (true, false))] [true, true] =
    [true, false, false, true, true] := rfl

example : BitRegister.run sweepProgram (fuel 0 [true] + 1)
    ⟨.running 0, (start 0 [true] [true, false]).store⟩ =
    ⟨.accepted, (start 0 [true] [true, false]).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run sweepProgram (fuel 1 [] + 1)
    ⟨.running 0, (start 1 [] []).store⟩ =
    ⟨.accepted, (start 0 [] [false]).store⟩ := rfl

example (n : Nat) (rows : System n) (history : BitString) :
    Exec loop (start n rows history).store (fuel n rows)
      (start 0 (residue n rows) (historyBits n rows history)).store := loop_exec n rows history
example (n : Nat) (rows : System n) :
    fuel n rows ≤ 80 * n * n * (rows.length + 1) + 1 := fuel_bound n rows
example (n : Nat) (rows : System n) (history : BitString) :
    (historyBits n rows history).length ≤ history.length + n * (n + 1) :=
  historyBits_bound n rows history
example (n : Nat) (rows : System n) :
    (solve n rows).isSome = satisfies (residue n rows) () := solve_isSome_residue n rows
example (n : Nat) (rows : System n) : (residue n rows).length = rows.length :=
  residue_length n rows

example : MatrixFeasibility.constantResult [false, true, false] true = false := rfl
example : MatrixFeasibility.constantResult [false, false] true = true := rfl
example : MatrixFeasibility.constantResult [] false = false := rfl
example : (MatrixFeasibility.result 1 [(false, true)] []).core.output = [false] := rfl
example : (MatrixFeasibility.result 2 [(false, (true, false))] []).core.output = [true] := rfl
example : (MatrixFeasibility.result 2 [(false, (true, false))] []).history =
    [true, false, false] := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixFeasibility.program (MatrixFeasibility.phaseFuel 0 [true] + 1)
    ⟨.running 0, (start 0 [true] []).store⟩ =
    ⟨.accepted, (MatrixFeasibility.result 0 [true] []).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run MatrixFeasibility.program (MatrixFeasibility.phaseFuel 0 [false] + 1)
    ⟨.running 0, (start 0 [false] []).store⟩ =
    ⟨.accepted, (MatrixFeasibility.result 0 [false] []).store⟩ := rfl
example (n : Nat) (rows : System n) (history : BitString) :
    Exec MatrixFeasibility.phase (start n rows history).store
      (MatrixFeasibility.phaseFuel n rows) (MatrixFeasibility.result n rows history).store :=
  MatrixFeasibility.phase_exec n rows history
example (n : Nat) (rows : System n) :
    MatrixFeasibility.phaseFuel n rows ≤
      80 * n * n * (rows.length + 1) + 5 * rows.length + 4 :=
  MatrixFeasibility.phaseFuel_bound n rows

end PNP.Concrete.ResidualReduction.MatrixSweep.Regression
