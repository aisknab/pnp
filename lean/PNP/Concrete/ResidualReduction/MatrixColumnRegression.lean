import PNP.Concrete.ResidualReduction.MatrixColumnInstructions

/-! General execution contracts and small regression fixtures. Finite fixtures
do not replace the arbitrary-matrix proofs or earn independent progress credit. -/

namespace PNP.Concrete.ResidualReduction.MatrixInstructions.Regression
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear

example : choosePivot (n := 0) [(false, true), (true, false), (true, true)] =
    some false := rfl
example : reducedRows (n := 0) [(false, true), (true, false), (true, true)] =
    [true, false, true] := rfl
example : reducedRows (n := 0) [(true, true), (true, true)] = [false, false] := rfl

-- No pivot is not a satisfiability verdict: the constant contradiction remains.
example : choosePivot (n := 0) [(false, false), (false, true)] = none := rfl
example : reducedRows (n := 0) [(false, false), (false, true)] = [false, true] := rfl
example : satisfies (reducedRows (n := 0) [(false, false), (false, true)]) () = false := rfl

example : reducedRows (n := 1)
    [(false, (true, false)), (true, (false, true)), (true, (true, false))] =
    [(true, false), (false, false), (true, true)] := rfl
example : (columnResult (n := 0) [(false, true), (true, false)]).active = [true] := rfl
example : (columnResult (n := 0) [(false, true)]).active = [] := rfl

-- Execute the literal compiled instruction list, not a host-language solver.
example : BitRegister.run columnProgram (columnFuel (n := 0) [] + 1)
    ⟨.running 0, (columnStart (n := 0) []).store⟩ =
    ⟨.accepted, (columnResult (n := 0) []).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run columnProgram (columnFuel (n := 0) [(true, false)] + 1)
    ⟨.running 0, (columnStart (n := 0) [(true, false)]).store⟩ =
    ⟨.accepted, (columnResult (n := 0) [(true, false)]).store⟩ := rfl
set_option maxRecDepth 4096 in
example : BitRegister.run columnProgram (columnFuel (n := 0) [(false, true)] + 1)
    ⟨.running 0, (columnStart (n := 0) [(false, true)]).store⟩ =
    ⟨.accepted, (columnResult (n := 0) [(false, true)]).store⟩ := rfl

example {n : Nat} (rows : System (n + 1)) :
    Exec column (columnStart rows).store (columnFuel rows) (columnResult rows).store :=
  column_exec rows
example {n : Nat} (rows : System (n + 1)) :
    columnFuel rows ≤ (20 * (n + 1) + 20) * (rows.length + 1) := columnFuel_bound rows
example {n : Nat} (rows : System (n + 1)) :
    (reducedRows rows).length = rows.length := reducedRows_length rows
example {n : Nat} (rows : System (n + 1)) :
    BitRegister.run columnProgram (columnFuel rows + 1)
      ⟨.running 0, (columnStart rows).store⟩ =
      ⟨.accepted, (columnResult rows).store⟩ := column_program_run rows

end PNP.Concrete.ResidualReduction.MatrixInstructions.Regression
