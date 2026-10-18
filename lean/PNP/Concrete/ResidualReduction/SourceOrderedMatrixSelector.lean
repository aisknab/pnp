import PNP.Concrete.ResidualReduction.SourceCandidateSelection

/-! Join the exact ordered entry scans to the exact candidate-code machine.
The caller provides matrices and their width, not seed coordinates, corner
values or a success premise. Both failure paths skip candidate evaluation. -/

namespace PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.ConstrainedBilinear
open PNP.Concrete.ResidualReduction.SourceLinePullback (transfers transfers_exec)

def extra : Store 2 := .cons [] (.cons [] .nil)
def extend (r : Store 14) : Store 16 := Frame.join r extra
def start {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 16 :=
  extend (SourceOrderedSelectorPrelude.store r (SourceOrderedSelectorPrelude.data A C))
def afterPrelude {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 16 :=
  extend (SourceOrderedSelectorPrelude.result r A C)

def handoffData (r : Registers) (s : SourceOrderedSelectorPrelude.Saved) : SourceCandidateCorners.Saved :=
  ⟨s.normal, s.activity, s.width, s.firstRow, r.target, s.firstColumn, r.excess⟩
/-- Save the first column before overwriting its old slot with the second row. -/
def handoff : Block 16 := transfers [.copy 14 13, .copy 15 3, .copy 13 1]
theorem handoff_exec (r : Registers) (s : SourceOrderedSelectorPrelude.Saved) :
    Exec handoff (extend (SourceOrderedSelectorPrelude.store r s)) 4
      (SourceCandidateCorners.store r (handoffData r s)) := by
  exact transfers_exec _ _

theorem first_found {m n : Nat} (A C : Matrix m n) (e f : Fin m × Fin n)
    (h : SourceOrderedSelectorPrelude.selectedSeeds A C = some (e, f)) :
    SourceOrderedSelectorPrelude.firstFound A C = true := by
  have pair := SourceOrderedSelectorPrelude.selected_seeds_exact A C
  rw [h] at pair
  cases found : SourceOrderedSelectorPrelude.firstFound A C with
  | true => rfl
  | false =>
    rw [SourceOrderedSelectorPrelude.pair_none_first A C found] at pair
    cases pair

theorem selected_handoff (r : Registers) {m n : Nat} (A C : Matrix m n) (e f : Fin m × Fin n)
    (h : SourceOrderedSelectorPrelude.selectedSeeds A C = some (e, f)) :
    Exec handoff (afterPrelude r A C) 4
      (SourceCandidateCorners.store (SourceOrderedSelectorPrelude.second r A C)
        (SourceCandidateCorners.data A C e.1 f.1 e.2 f.2)) := by
  have pair : SourceOrderedSelectorPrelude.entryPair A C = some ((e.1.val, e.2.val), (f.1.val, f.2.val)) := by
    rw [← SourceOrderedSelectorPrelude.selected_seeds_exact, h]
    rfl
  have found := first_found A C e f h
  have coordinates := SourceOrderedSelectorPrelude.result_coordinates r A C _ _ pair
  rw [SourceOrderedSelectorPrelude.result, found] at coordinates
  change (SourceOrderedSelectorPrelude.first r A C).target = List.replicate e.1.val true ∧
    (SourceOrderedSelectorPrelude.first r A C).excess = List.replicate e.2.val true ∧
    (SourceOrderedSelectorPrelude.second r A C).target = List.replicate f.1.val true ∧
    (SourceOrderedSelectorPrelude.second r A C).excess = List.replicate f.2.val true at coordinates
  have saved : handoffData (SourceOrderedSelectorPrelude.second r A C)
        (SourceOrderedSelectorPrelude.captured (SourceOrderedSelectorPrelude.first r A C) (SourceOrderedSelectorPrelude.data A C)) =
      SourceCandidateCorners.data A C e.1 f.1 e.2 f.2 := by
    simp only [handoffData, SourceOrderedSelectorPrelude.captured, SourceOrderedSelectorPrelude.data,
      SourceCandidateCorners.data, coordinates.1, coordinates.2.1, coordinates.2.2.1, coordinates.2.2.2]
  have checked := handoff_exec (SourceOrderedSelectorPrelude.second r A C)
    (SourceOrderedSelectorPrelude.captured (SourceOrderedSelectorPrelude.first r A C) (SourceOrderedSelectorPrelude.data A C))
  rw [saved] at checked
  simpa only [afterPrelude, SourceOrderedSelectorPrelude.result, found, if_true,
    SourceOrderedSelectorPrelude.afterSecond] using checked

theorem prelude_flag (r : Registers) {m n : Nat} (A C : Matrix m n) :
    (afterPrelude r A C).get 4 = SourceOrderedScan.flag (SourceOrderedSelectorPrelude.selectedSeeds A C).isSome := by
  have core := Frame.get_core (SourceOrderedSelectorPrelude.result r A C) extra (4 : Fin 14)
  change (afterPrelude r A C).get 4 = (SourceOrderedSelectorPrelude.result r A C).get 4 at core
  rw [core, SourceOrderedSelectorPrelude.result_flag, ← SourceOrderedSelectorPrelude.selected_seeds_exact, Option.isSome_map]

def reject : Block 16 := .seq (.action (.clear 8)) (.action (.push 8 false))
def rejectResult (r : Store 16) : Store 16 := (r.set 8 []).set 8 [false]
theorem reject_exec (r : Store 16) : Exec reject r 2 (rejectResult r) := by
  have checked := Exec.seq (Exec.action (.clear (8 : Fin 16)) r)
    (Exec.action (.push (8 : Fin 16) false) ((Action.clear (8 : Fin 16)).update r))
  simpa only [reject, rejectResult, Action.update, Action.instruction, Instruction.update, Store.get_set_same] using checked
theorem reject_output (r : Store 16) : (rejectResult r).get 8 = [false] := Store.get_set_same _ _ _

def continuation : Block 16 := .seq handoff SourceCandidateSelection.block
def finish : Block 16 := .branch 4 reject reject continuation
def block : Block 16 := .seq (Frame.block 2 SourceOrderedSelectorPrelude.block) finish

def code {m n : Nat} (A C : Matrix m n) : Option SourceCandidateChoice.Choice :=
  (SourceOrderedSelectorPrelude.selectedSeeds A C).bind fun p =>
    SourceCandidateSelection.choice A C p.1.1 p.2.1 p.1.2 p.2.2
def finishFuel {m n : Nat} (A C : Matrix m n) : Nat :=
  match SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none => 3
  | some (e, f) => 1 + (4 + SourceCandidateSelection.fuel A C e.1 f.1 e.2 f.2)
def fuel {m n : Nat} (A C : Matrix m n) : Nat := SourceOrderedSelectorPrelude.fuel A C + finishFuel A C
def result {m n : Nat} (r : Registers) (A C : Matrix m n) : Store 16 :=
  match SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none => rejectResult (afterPrelude r A C)
  | some (e, f) => SourceCandidateCorners.store
      (SourceCandidateSelection.result (SourceOrderedSelectorPrelude.second r A C) A C e.1 f.1 e.2 f.2)
      (SourceCandidateCorners.data A C e.1 f.1 e.2 f.2)

theorem finish_exec (r : Registers) {m n : Nat} (A C : Matrix m n) :
    Exec finish (afterPrelude r A C) (finishFuel A C) (result r A C) := by
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none =>
    simp only [finishFuel, result, seeds]
    exact Exec.empty ((prelude_flag r A C).trans (by rw [seeds]; rfl)) (reject_exec _)
  | some p =>
    rcases p with ⟨e, f⟩
    simp only [finishFuel, result, seeds]
    exact Exec.one ((prelude_flag r A C).trans (by rw [seeds]; rfl))
      (Exec.seq (selected_handoff r A C e f seeds)
        (SourceCandidateSelection.block_exec (SourceOrderedSelectorPrelude.second r A C) A C e.1 f.1 e.2 f.2))

theorem block_exec (r : Registers) {m n : Nat} (A C : Matrix m n) :
    Exec block (start r A C) (fuel A C) (result r A C) :=
  Exec.seq (Frame.execution (SourceOrderedSelectorPrelude.block_exec r A C) extra) (finish_exec r A C)

theorem output_exact (r : Registers) {m n : Nat} (A C : Matrix m n) :
    (result r A C).get 8 = SourceCandidateChoice.outputBits (code A C) := by
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none =>
    simp only [result, code, seeds, Option.bind_none, SourceCandidateChoice.outputBits]
    exact reject_output _
  | some p =>
    rcases p with ⟨e, f⟩
    simp only [result, code, seeds, Option.bind_some]
    exact SourceCandidateSelection.output_exact (SourceOrderedSelectorPrelude.second r A C) A C e.1 f.1 e.2 f.2

theorem witness_exact {m n : Nat} (A C : Matrix m n) :
    (BilinearSelection.select A C).witness =
      (SourceOrderedSelectorPrelude.selectedSeeds A C).bind fun p =>
        (SourceCandidateSelection.choice A C p.1.1 p.2.1 p.1.2 p.2.2).map
          (SourceCandidateChoice.decode p.1.1 p.2.1 p.1.2 p.2.2) := by
  rw [SourceOrderedSelectorPrelude.select_from_seeds]
  apply congrArg ((SourceOrderedSelectorPrelude.selectedSeeds A C).bind)
  funext p
  exact (SourceCandidateSelection.choice_exact A C p.1.1 p.2.1 p.1.2 p.2.2).symm

theorem result_coordinates (r : Registers) {m n : Nat} (A C : Matrix m n) (e f : Fin m × Fin n)
    (h : SourceOrderedSelectorPrelude.selectedSeeds A C = some (e, f)) :
    (result r A C).get 12 = List.replicate e.1.val true ∧
      (result r A C).get 13 = List.replicate f.1.val true ∧
      (result r A C).get 14 = List.replicate e.2.val true ∧
      (result r A C).get 15 = List.replicate f.2.val true := by
  rw [result, h]
  exact ⟨Frame.get_frame _ _ (3 : Fin 7), Frame.get_frame _ _ (4 : Fin 7),
    Frame.get_frame _ _ (5 : Fin 7), Frame.get_frame _ _ (6 : Fin 7)⟩

theorem fuel_bound {m n : Nat} (A C : Matrix m n) :
    fuel A C ≤ 26 * (m * n) + (6 + SourceMatrixEntry.budget m n) * 8 + 77 := by
  have scans := SourceOrderedSelectorPrelude.fuel_bound A C
  unfold fuel finishFuel
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds A C with
  | none =>
    dsimp only
    omega
  | some p =>
    rcases p with ⟨e, f⟩
    dsimp only
    have decision := SourceCandidateSelection.fuel_bound A C e.1 f.1 e.2 f.2
    omega

def sourceCostPolynomial : NatPolynomial :=
  .add (.add SourceOrderedSelectorPrelude.sourceCostPolynomial SourceCandidateSelection.sourceCostPolynomial) (.constant 5)
theorem source_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) ≤
      sourceCostPolynomial.eval (SourceDirectionEncoding.codec.encode ⟨n, [alpha], F⟩).length := by
  have scans := SourceOrderedSelectorPrelude.source_bound F alpha
  unfold fuel finishFuel
  cases seeds : SourceOrderedSelectorPrelude.selectedSeeds (SourceLinePullback.normalPull F alpha) (SourceLinePullback.activityPull F alpha) with
  | none =>
    change SourceOrderedSelectorPrelude.fuel _ _ + 3 ≤
      SourceOrderedSelectorPrelude.sourceCostPolynomial.eval _ + SourceCandidateSelection.sourceCostPolynomial.eval _ + 5
    change SourceOrderedSelectorPrelude.fuel _ _ ≤ SourceOrderedSelectorPrelude.sourceCostPolynomial.eval _ at scans
    omega
  | some p =>
    have decision := SourceCandidateSelection.source_bound F alpha p.1.1 p.2.1 p.1.2 p.2.2
    change SourceOrderedSelectorPrelude.fuel _ _ ≤ SourceOrderedSelectorPrelude.sourceCostPolynomial.eval _ at scans
    change SourceOrderedSelectorPrelude.fuel _ _ + (1 + (4 + SourceCandidateSelection.fuel _ _ _ _ _ _)) ≤
      SourceOrderedSelectorPrelude.sourceCostPolynomial.eval _ + SourceCandidateSelection.sourceCostPolynomial.eval _ + 5
    omega

def program : Program 16 := block.program 0 8
theorem program_run (r : Registers) {m n : Nat} (A C : Matrix m n) :
    BitRegister.run program (fuel A C + 1) ⟨.running 0, start r A C⟩ = ⟨.accepted, result r A C⟩ :=
  (block_exec r A C).program_run 0 8

end PNP.Concrete.ResidualReduction.SourceOrderedMatrixSelector
