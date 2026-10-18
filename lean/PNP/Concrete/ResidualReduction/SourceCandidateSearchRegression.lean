import Lean
import PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch

namespace PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.Regression
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

private def later : Row 2 := ⟨true, (false, (true, false)), (false, (false, true))⟩
private def earlier : Row 2 := ⟨false, (true, (false, false)), (false, (false, true))⟩
private def source : Family 2 := [later]
private def forms : AffineMap 1 1 := ((true, true), ())
private def pairForms : AffineMap 2 2 := ((true, (false, true)), ((false, (true, false)), ()))

-- Affine constants affect activity; selected flags do not become coefficients.
example : SourceActivityInstructions.activityBit later 0 = false := rfl
example : SourceActivityInstructions.activityBit later 1 = true := rfl
example : SourceActivityInstructions.activityBit {later with selected := false} 1 = true := rfl
example : SourceActivityInstructions.activityBit (⟨false, (true, (false, true)), (false, (true, false))⟩ : Row 2) 1 = true := rfl
example : weightedActivity ([later, later] : Family 2) (true, (true, ())) (unitPoint 2 1) = false := rfl
example : weightedActivity source (false, ()) (unitPoint 2 1) = false := rfl

-- Each solution-map coordinate retains its own affine constant and byte order.
example : mapBits pairForms = [true, false, true, false, true, false] := rfl
example : (SourceEncoding.pointCodec 2).encode (mapEval pairForms (SourceCandidateMapInstructions.parameter none)) =
    [true, false] := rfl
example : (SourceEncoding.pointCodec 2).encode (mapEval pairForms (SourceCandidateMapInstructions.parameter (some 0))) =
    [false, false] := rfl
example : (SourceEncoding.pointCodec 2).encode (mapEval pairForms (SourceCandidateMapInstructions.parameter (some 1))) =
    [true, true] := rfl
example : (SourceCandidateMapInstructions.schedule 2).map (fun q => (SourceCandidateMapInstructions.marker q, SourceCandidateMapInstructions.cursor q)) =
    [(0, 0), (1, 0), (1, 1)] := rfl

-- Initial success, success only after a failed direction, and complete failure.
example : scan (active source forms none) 2 0 = (1, true) := rfl
example : scan (active ([earlier] : Family 2) forms none) 2 0 = (0, true) := rfl
example : scan (active source forms (some 0)) 2 0 = (2, false) := rfl
example : scan (active (k := 0) ([] : Family 3) (() : AffineMap 0 0) none) 3 0 = (3, false) := rfl
example : scan (active ([⟨true, true, true⟩] : Family 0) ((false, ()) : AffineMap 1 0) none) 0 0 = (0, false) := rfl
example : scan (fun i => i == 2 || i == 3) 4 0 = (2, true) := rfl

-- Execute the literal complete direction-search program, not only its model.
private def code : Program 21 := loop.program 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel source forms none 2 0 + 1)
    ⟨.running 0, (ready source forms none 0 2 false).store⟩ =
      ⟨.accepted, (ready source forms none 1 0 true).store⟩ := by
  exact (complete_exec source forms none).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel source forms (some 0) 2 0 + 1)
    ⟨.running 0, (ready source forms (some 0) 0 2 false).store⟩ =
      ⟨.accepted, (ready source forms (some 0) 2 0 false).store⟩ := by
  exact (complete_exec source forms (some 0)).program_run 0 8
set_option maxRecDepth 8192 in
example : BitRegister.run code (fuel ([earlier] : Family 2) forms none 2 0 + 1)
    ⟨.running 0, (ready ([earlier] : Family 2) forms none 0 2 false).store⟩ =
      ⟨.accepted, (ready ([earlier] : Family 2) forms none 0 0 true).store⟩ := rfl
example : BitRegister.run code 2
    ⟨.running 0, (ready (k := 0) ([] : Family 0) (() : AffineMap 0 0) none 0 0 false).store⟩ =
      ⟨.accepted, (ready (k := 0) ([] : Family 0) (() : AffineMap 0 0) none 0 0 false).store⟩ := rfl

-- Whole-family and whole-map obligations are universal, not fixture coverage.
example {n : Nat} (F : Family n) (w : Point F.length) (j : Fin n) (output : BitString) :
    Exec SourceWeightedActivityInstructions.test
      (SourceWeightedActivityInstructions.ready n j.val (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) output).store
      (SourceWeightedActivityInstructions.fuel n j.val F.length + 1)
      (SourceWeightedActivityInstructions.ready n j.val [] [] (weightedActivity F w (unitPoint n j) :: output)).store :=
  SourceWeightedActivityInstructions.test_exec F w j output
example {m k : Nat} (map : AffineMap m k) (q : Option (Fin k)) :
    Exec SourceCandidateMapInstructions.block
      (SourceCandidateMapInstructions.ready k q [] (mapBits map) [] []).store
      (SourceCandidateMapInstructions.fuel k q m)
      (SourceCandidateMapInstructions.ready k q [] [] []
        ((SourceEncoding.pointCodec m).encode (mapEval map (SourceCandidateMapInstructions.parameter q)))).store :=
  SourceCandidateMapInstructions.block_exec map q
example {n k : Nat} (F : Family n) (map : AffineMap F.length k) (q : Option (Fin k)) :
    Exec loop (ready F map q 0 n false).store (fuel F map q n 0)
      (ready F map q (scan (active F map q) n 0).1 0 (scan (active F map q) n 0).2).store :=
  complete_exec F map q
example {n k : Nat} (F : Family n) (map : AffineMap F.length k) (q : Option (Fin k)) :
    fuel F map q n 0 ≤ ((9 * k + 24 * n + 98) * F.length + 22) * n + 1 :=
  fuel_bound F map q n 0 (by omega)
example {n : Nat} (F : Family n) (s : Space F.length)
    (computed : solve F.length (SourceClosure.affineMaskRows F) = some s) (q : Option (Fin s.parameters)) :
    fuel F s.forms q n 0 ≤ ((9 * F.length + 24 * n + 98) * F.length + 22) * n + 1 :=
  computed_fuel_bound F s computed q
example {n k : Nat} (F : Family n) (map : AffineMap F.length k) (q : Option (Fin k)) :
    (SourcePlane.firstTrue
      (fun j : Fin n => weightedActivity F (mapEval map (SourceCandidateMapInstructions.parameter q)) (unitPoint n j))
      (List.finRange n)).map Fin.val =
        if (scan (active F map q) n 0).2 then some (scan (active F map q) n 0).1 else none :=
  scan_indices_exact F map q

-- No project axiom, admitted result, or classical-choice dependency is allowed.
run_cmd do
  for name in [``PNP.Concrete.ResidualReduction.SourceActivityInstructions.activity_units,
    ``PNP.Concrete.ResidualReduction.SourceActivityInstructions.rowBlock_exec,
    ``PNP.Concrete.ResidualReduction.SourceWeightedActivityInstructions.loop_exec,
    ``PNP.Concrete.ResidualReduction.SourceWeightedActivityInstructions.test_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions.schedule_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateMapInstructions.computed_fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateEvaluation.block_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateEvaluation.computed_fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.step_false,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.step_true,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.loop_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.complete_exec,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.computed_fuel_bound,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.scan_indices_exact,
    ``PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.scan_success] do
    let axioms ← Lean.collectAxioms name
    for axiomName in axioms do
      if axiomName != ``propext && axiomName != ``Quot.sound then
        throwError "Unexpected axiom in {name}: {axiomName}"

#print axioms PNP.Concrete.ResidualReduction.SourceCandidateEvaluation.block_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.complete_exec
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.computed_fuel_bound
#print axioms PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.scan_indices_exact

end PNP.Concrete.ResidualReduction.SourceCandidateDirectionSearch.Regression
