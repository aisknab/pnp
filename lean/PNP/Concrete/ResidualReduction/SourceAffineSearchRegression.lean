import Lean
import PNP.Concrete.ResidualReduction.SourceAffineSearchCorrectness
import PNP.Concrete.ResidualReduction.SourceCandidateSearchRegression

namespace PNP.Concrete.ResidualReduction.SourceAffineSearch.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourcePlane

private def row : Row 2 := ⟨false, (false, (true, false)), (false, (false, true))⟩
private def source : Family 2 := [row]
private def later : AffineMap 1 2 := ((false, (true, false)), ())
private def first : AffineMap 1 2 := ((true, (true, false)), ())
private def constant : AffineMap 1 0 := (true, ())
private def missing : AffineMap 1 2 := ((false, (false, false)), ())
private def cancelled : AffineMap 2 1 := ((true, true), ((true, true), ()))

-- A failed zero candidate and failed first unit candidate must not lose the
-- direction counter: the final unit still succeeds at the final direction.
example : outcome source later = ⟨true, 1, 1, true⟩ := rfl
example : decode source later (outcome source later) = some ((true, ()), (false, (true, ()))) := rfl
example : outcome source first = ⟨true, 0, 1, true⟩ := rfl
example : outcome source constant = ⟨false, 0, 1, true⟩ := rfl
example : outcome source missing = ⟨true, 2, 0, false⟩ := rfl
example : decode source missing (outcome source missing) = none := rfl
example : outcome ([row, row] : Family 2) cancelled = ⟨true, 1, 0, false⟩ := rfl
example : outcome (k := 0) ([] : Family 2) (() : AffineMap 0 0) = ⟨true, 0, 0, false⟩ := rfl
example : outcome ([⟨true, true, true⟩] : Family 0) ((false, ()) : AffineMap 1 0) =
    ⟨true, 0, 0, false⟩ := rfl
-- Neither an exhausted parameter index nor an exhausted direction is a witness.
example : decode source later ⟨true, 2, 1, true⟩ = none := rfl
example : decode source later ⟨true, 1, 2, true⟩ = none := rfl

private def code : Program 22 := block.program 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel source later + 1)
    ⟨.running 0, (ready source later false 0 0 2 0 false).store⟩ =
      ⟨.accepted, (finished source later ⟨true, 1, 1, true⟩).store⟩ :=
  (block_exec source later).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel source missing + 1)
    ⟨.running 0, (ready source missing false 0 0 2 0 false).store⟩ =
      ⟨.accepted, (finished source missing ⟨true, 2, 0, false⟩).store⟩ :=
  (block_exec source missing).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel source constant + 1)
    ⟨.running 0, (ready source constant false 0 0 2 0 false).store⟩ =
      ⟨.accepted, (finished source constant ⟨false, 0, 1, true⟩).store⟩ :=
  (block_exec source constant).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel (k := 0) ([] : Family 0) (() : AffineMap 0 0) + 1)
    ⟨.running 0, (ready (k := 0) ([] : Family 0) (() : AffineMap 0 0) false 0 0 0 0 false).store⟩ =
      ⟨.accepted, (finished (k := 0) ([] : Family 0) (() : AffineMap 0 0) ⟨true, 0, 0, false⟩).store⟩ :=
  (block_exec (k := 0) ([] : Family 0) (() : AffineMap 0 0)).program_run 0 8

-- Exact original query, not only existence of a convenient successful pair.
example {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    decode F s.forms (outcome F s.forms) = SourceClosure.sourceAffineQuery F :=
  computed_query_exact F s computed
example {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    (decode F forms (outcome F forms)).isSome = (outcome F forms).found := outcome_isSome F forms
example {n k : Nat} (F : Family n) (forms : AffineMap F.length k) :
    fuel F forms ≤ (directionBudget n k F.length + 7) * (k + 1) := fuel_bound F forms
example {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) :
    let L := (SourceMatrixEncoding.codec.encode ⟨n, F⟩).length
    fuel F s.forms ≤ (directionBudget L L L + 7) * (L + 1) := original_input_fuel_bound F s computed

run_cmd do
  for name in [``unit_run, ``zero_run, ``advanceUnit_exec, ``zeroAdvance_exec,
    ``unitStep_false, ``unitStep_true, ``unitLoop_exec, ``unitFuel_bound,
    ``block_exec, ``fuel_bound, ``computed_fuel_bound, ``original_input_fuel_bound,
    ``directionWitness_exact, ``directionWitness_isSome, ``unitSearch_exact,
    ``unitPairsBlock_exact, ``allPairs_exact, ``outcome_exact, ``computed_query_exact,
    ``unitSearch_isSome, ``outcome_isSome] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceAffineSearch.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceAffineSearch.computed_query_exact
#print axioms PNP.Concrete.ResidualReduction.SourceAffineSearch.original_input_fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceAffineSearch.outcome_isSome

end PNP.Concrete.ResidualReduction.SourceAffineSearch.Regression
