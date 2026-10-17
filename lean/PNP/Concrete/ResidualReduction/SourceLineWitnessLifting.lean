import PNP.Concrete.ResidualReduction.SourceWitnessLiftMachine

/-! Exact original-source lineRawQuery execution through both coordinate lifts.
Every map, matrix, seed and parameter vector is internally computed. This is
a source-instruction refinement; raw tape compilation and the outer contraction
algorithm are still separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceLineWitness
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding

abbrev Selection {n : Nat} (F : Family n) (alpha : Affine n) :=
  SourceMatrixWitness.Pick (SourceLinePullback.leftSpace F alpha).parameters (SourceLinePullback.rightSpace F alpha).parameters
def selection {n : Nat} (F : Family n) (alpha : Affine n) : Option (Selection F alpha) :=
  SourceMatrixWitness.selected (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha)
def leftPoint {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) :
    Point (SourceLinePullback.leftSpace F alpha).parameters :=
  SourceAxisWitness.point p.first.1 p.second.1 p.choice.1
def rightPoint {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) :
    Point (SourceLinePullback.rightSpace F alpha).parameters :=
  SourceAxisWitness.point p.first.2 p.second.2 p.choice.2
def pickCore {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) : Registers :=
  SourceAxisWitness.outputCore
    (SourceWitnessPair.rowCore (SourceMatrixWitness.readyCore (fromPullback F alpha).core
      (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) p)
      p.first.1 p.second.1 p.choice) (rightPoint F alpha p)
def pickFrame {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) : Store 29 :=
  Frame.join (SourceAxisWitness.data p.first.2 p.second.2 [] []).store
    (Frame.join (SourceWitnessPair.data p.first.2 p.second.2 (SourceWitnessPair.rowBytes p.first.1 p.second.1 p.choice)).store
      (Frame.join (SourceLinePullback.emptyFrame 6) (SourceLinePullback.resultData F alpha).store))

theorem parameter_some_state {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha)
    (h : selection F alpha = some p) :
    parameterResult F alpha = SourceWitnessLift.store (pickCore F alpha p) (pickFrame F alpha p) := by
  unfold selection at h
  rw [parameterResult, SourceMatrixWitness.result, h]
  rfl
theorem parameter_none_flag {n : Nat} (F : Family n) (alpha : Affine n)
    (h : selection F alpha = none) : (parameterResult F alpha).get 4 = [] := by
  unfold selection at h
  rw [parameterResult, SourceMatrixWitness.result, h]
  exact (Frame.get_core _ _ (4 : Fin 19)).trans (Store.get_set_same _ _ _)
theorem parameter_some_flag {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha)
    (h : selection F alpha = some p) : (parameterResult F alpha).get 4 = [true] := by
  rw [parameter_some_state F alpha p h]
  exact Frame.get_core _ _ (4 : Fin 9)

def liftedResult {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) : Store 38 :=
  SourceWitnessLift.store
    (SourceWitnessLift.resultCore (SourceLinePullback.rightSpace F alpha).forms (rightPoint F alpha p))
    (SourceWitnessLift.resultData (pickFrame F alpha p)
      (SourceLinePullback.leftSpace F alpha).forms (SourceLinePullback.rightSpace F alpha).forms
      (leftPoint F alpha p) (rightPoint F alpha p))
def liftFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceWitnessLift.fuel (n + F.length) (directionSpace F [alpha]).parameters
    (SourceLinePullback.leftSpace F alpha).parameters (SourceLinePullback.rightSpace F alpha).parameters
theorem lift_exec {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha)
    (h : selection F alpha = some p) :
    Exec SourceWitnessLift.block (parameterResult F alpha) (liftFuel F alpha) (liftedResult F alpha p) := by
  rw [parameter_some_state F alpha p h]
  exact SourceWitnessLift.block_exec (pickCore F alpha p) (pickFrame F alpha p)
    (SourceLinePullback.leftSpace F alpha).forms (SourceLinePullback.rightSpace F alpha).forms
    (leftPoint F alpha p) (rightPoint F alpha p) rfl rfl rfl rfl rfl rfl

def finish : Block 38 := .branch 4 .skip .skip SourceWitnessLift.block
def finishFuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  match selection F alpha with
  | none => 2
  | some _ => 1 + liftFuel F alpha
def result {n : Nat} (F : Family n) (alpha : Affine n) : Store 38 :=
  match selection F alpha with
  | none => parameterResult F alpha
  | some p => liftedResult F alpha p
theorem finish_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec finish (parameterResult F alpha) (finishFuel F alpha) (result F alpha) := by
  cases h : selection F alpha with
  | none =>
    simp only [finishFuel, result, h]
    exact Exec.empty (parameter_none_flag F alpha h) (Exec.skip _)
  | some p =>
    simp only [finishFuel, result, h]
    exact Exec.one (parameter_some_flag F alpha p h) (lift_exec F alpha p h)

def block : Block 38 := .seq parameterBlock finish
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat := parameterFuel F alpha + finishFuel F alpha
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (SourceLinePullback.start F alpha) (fuel F alpha) (result F alpha) :=
  Exec.seq (parameter_exec F alpha) (finish_exec F alpha)

def observed (s : Store 38) : Option (BitString × BitString) :=
  if (s.get 4).isEmpty then none else some (s.get 20, s.get 8)
def liftedBytes {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) : BitString × BitString :=
  ((SourceEncoding.pointCodec (n + F.length)).encode ((SourceLinePullback.leftSpace F alpha).direction (leftPoint F alpha p)),
    (SourceEncoding.pointCodec (directionSpace F [alpha]).parameters).encode
      ((SourceLinePullback.rightSpace F alpha).direction (rightPoint F alpha p)))
theorem lifted_observed {n : Nat} (F : Family n) (alpha : Affine n) (p : Selection F alpha) :
    observed (liftedResult F alpha p) = some (liftedBytes F alpha p) := by
  rw [observed, liftedResult, SourceWitnessLift.result_present,
    SourceWitnessLift.result_left, SourceWitnessLift.result_right]
  rfl
def queryBytes {n : Nat} (F : Family n) (alpha : Affine n) : Option (BitString × BitString) :=
  (SourceLine.lineRawQuery F alpha).map fun w =>
    ((SourceEncoding.pointCodec (n + F.length)).encode w.1,
      (SourceEncoding.pointCodec (directionSpace F [alpha]).parameters).encode w.2)
theorem selection_query {n : Nat} (F : Family n) (alpha : Affine n) :
    (selection F alpha).map (liftedBytes F alpha) = queryBytes F alpha := by
  rw [queryBytes, SourceLinePullback.exact_query_interface, SourceOrderedMatrixSelector.witness_exact]
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds
      (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) with
  | none =>
    simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_none, Option.map_none]
  | some p =>
    rcases p with ⟨e, f⟩
    cases choice : SourceCandidateSelection.choice
        (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) e.1 f.1 e.2 f.2 with
    | none =>
      simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_some, choice, Option.map_none]
    | some c =>
      simp only [selection, SourceMatrixWitness.selected, seeds, Option.bind_some, choice, Option.map_some,
        liftedBytes, leftPoint, rightPoint, SourceAxisWitness.point_exact, SourceCandidateChoice.decode]

theorem result_exact {n : Nat} (F : Family n) (alpha : Affine n) :
    observed (result F alpha) = queryBytes F alpha := by
  rw [← selection_query]
  cases h : selection F alpha with
  | none =>
    simp only [result, h, Option.map_none]
    rw [observed, parameter_none_flag F alpha h]
    rfl
  | some p =>
    simp only [result, h, Option.map_some]
    exact lifted_observed F alpha p

def program : Program 38 := block.program 0 8
theorem program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run program (fuel F alpha + 1) ⟨.running 0, SourceLinePullback.start F alpha⟩ =
      ⟨.accepted, result F alpha⟩ := (block_exec F alpha).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceLineWitness
