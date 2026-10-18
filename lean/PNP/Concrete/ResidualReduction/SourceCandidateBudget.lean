import PNP.Concrete.ResidualReduction.SourceCandidateQueries
import PNP.Concrete.ResidualReduction.SourcePolynomialLineQuery
import PNP.Concrete.ResidualReduction.SourcePolynomialPlaneQuery

/-! Original-encoded-input polynomial instruction bounds for both complete
ordered searches. Candidate counts come from the actual source menu. These
prepared-search bounds do not yet account for the outer raw dispatcher,
compiler simulation or the complete contraction/history construction. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateBudget
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceCandidateQueries
open PNP.Concrete.ResidualReduction.SourceCandidateSearch
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (full)
open PNP.Concrete.ResidualReduction.MatrixInstructions (affineWord matrixBits)
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes (pairWord pairBits)

def invocationPolynomial (query packet : NatPolynomial) : NatPolynomial :=
  .add (.add (query.substitute packet) (.mul (.constant 8) packet)) (.constant 109)
def lineQueryPolynomial : NatPolynomial :=
  invocationPolynomial SourcePolynomialLineQuery.sourceFuel (.linear 2 3)
def planeQueryPolynomial : NatPolynomial :=
  invocationPolynomial SourcePolynomialPlaneQuery.sourceFuel (.linear 3 5)
def searchPolynomial (width query count : NatPolynomial) : NatPolynomial :=
  .add (.mul (.add (.add (.add (.mul (.constant 9) width) (.constant 45)) query) (.constant 3)) count)
    (.constant 3)
def lineCostPolynomial : NatPolynomial :=
  searchPolynomial (.linear 1 1) lineQueryPolynomial (.linear 3 0)
def planeCostPolynomial : NatPolynomial :=
  searchPolynomial (.linear 2 2) planeQueryPolynomial (.mul (.linear 3 0) (.linear 3 0))

theorem lineQueryPolynomial_eval (L : Nat) :
    lineQueryPolynomial.eval L = SourcePolynomialLineQuery.sourceFuel.eval (2 * L + 3) +
      8 * (2 * L + 3) + 109 := by
  simp only [lineQueryPolynomial,invocationPolynomial,NatPolynomial.eval_add,
    NatPolynomial.eval_mul,NatPolynomial.eval_constant,NatPolynomial.eval_substitute,
    NatPolynomial.eval_linear]
theorem planeQueryPolynomial_eval (L : Nat) :
    planeQueryPolynomial.eval L = SourcePolynomialPlaneQuery.sourceFuel.eval (3 * L + 5) +
      8 * (3 * L + 5) + 109 := by
  simp only [planeQueryPolynomial,invocationPolynomial,NatPolynomial.eval_add,
    NatPolynomial.eval_mul,NatPolynomial.eval_constant,NatPolynomial.eval_substitute,
    NatPolynomial.eval_linear]
theorem lineCostPolynomial_eval (L : Nat) :
    lineCostPolynomial.eval L =
      (9 * (L + 1) + 45 + lineQueryPolynomial.eval L + 3) * (3 * L) + 3 := by
  simp only [lineCostPolynomial,searchPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,
    NatPolynomial.eval_constant,NatPolynomial.eval_linear,Nat.one_mul,Nat.add_zero]
theorem planeCostPolynomial_eval (L : Nat) :
    planeCostPolynomial.eval L =
      (9 * (2 * L + 2) + 45 + planeQueryPolynomial.eval L + 3) * ((3 * L) * (3 * L)) + 3 := by
  simp only [planeCostPolynomial,searchPolynomial,NatPolynomial.eval_add,NatPolynomial.eval_mul,
    NatPolynomial.eval_constant,NatPolynomial.eval_linear,Nat.add_zero]

theorem line_query_bound {n : Nat} (F : Family n) :
    lineBudget F ≤ lineQueryPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length
  have dim : n ≤ L := SourceMatrixEncoding.dimension_bound n F
  have mono := NatPolynomial.eval_mono SourcePolynomialLineQuery.sourceFuel
    (show L + n + 3 ≤ 2 * L + 3 by omega)
  rw [SourcePolynomialLineQuery.sourceFuel_eval,SourcePolynomialLineQuery.sourceFuel_eval] at mono
  rw [lineQueryPolynomial_eval,SourcePolynomialLineQuery.sourceFuel_eval]
  change SourceLineRaw.sourceBudget (L + n + 3) + 8 * (L + n + 3) + 109 ≤ _
  change _ ≤ SourceLineRaw.sourceBudget (2 * L + 3) + 1 + 8 * (2 * L + 3) + 109
  omega
theorem plane_query_bound {n : Nat} (F : Family n) :
    planeBudget F ≤ planeQueryPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length
  have dim : n ≤ L := SourceMatrixEncoding.dimension_bound n F
  have mono := NatPolynomial.eval_mono SourcePolynomialPlaneQuery.sourceFuel
    (show L + 2 * n + 5 ≤ 3 * L + 5 by omega)
  rw [SourcePolynomialPlaneQuery.sourceFuel_eval,SourcePolynomialPlaneQuery.sourceFuel_eval] at mono
  rw [planeQueryPolynomial_eval,SourcePolynomialPlaneQuery.sourceFuel_eval]
  change SourcePlaneRaw.sourceBudget (L + 2 * n + 5) + 8 * (L + 2 * n + 5) + 109 ≤ _
  change _ ≤ SourcePlaneRaw.sourceBudget (3 * L + 5) + 1 + 8 * (3 * L + 5) + 109
  omega

theorem line_count_bound {n : Nat} (F : Family n) :
    (sourceMenu F).length ≤ 3 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  have count := sourceMenu_length_le F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  omega
theorem plane_count_bound {n : Nat} (F : Family n) :
    (planeMenu (sourceMenu F)).length ≤
      (3 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length) *
      (3 * (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length) :=
  Nat.le_trans (SourcePlaneMenuBytes.rows_length (sourceMenu F) (sourceMenu F))
    (Nat.mul_le_mul (line_count_bound F) (line_count_bound F))

theorem line_original_bound {n : Nat} (F : Family n) :
    2 + loopBound (n + 1) (lineBudget F) (sourceMenu F).length ≤
      lineCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length
  have dim : n ≤ L := SourceMatrixEncoding.dimension_bound n F
  have query := line_query_bound F
  have step : SourceCandidateLoad.fuel (n + 1) + lineBudget F + 3 ≤
      9 * (L + 1) + 45 + lineQueryPolynomial.eval L + 3 := by
    unfold SourceCandidateLoad.fuel
    dsimp only [L] at *
    omega
  have total := Nat.mul_le_mul step (line_count_bound F)
  rw [lineCostPolynomial_eval]
  unfold loopBound
  dsimp only [L] at *
  omega
theorem plane_original_bound {n : Nat} (F : Family n) :
    2 + loopBound (2 * (n + 1)) (planeBudget F) (planeMenu (sourceMenu F)).length ≤
      planeCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  let L := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length
  have dim : n ≤ L := SourceMatrixEncoding.dimension_bound n F
  have query := plane_query_bound F
  have step : SourceCandidateLoad.fuel (2 * (n + 1)) + planeBudget F + 3 ≤
      9 * (2 * L + 2) + 45 + planeQueryPolynomial.eval L + 3 := by
    unfold SourceCandidateLoad.fuel
    dsimp only [L] at *
    omega
  have total := Nat.mul_le_mul step (plane_count_bound F)
  rw [planeCostPolynomial_eval]
  unfold loopBound
  dsimp only [L] at *
  omega

theorem line_menu_exec {n : Nat} (F : Family n) (r : Store 38) (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec SourceCandidateQueries.line (full r (current (base F 1) normal packet oldOutput)
        ⟨matrixBits (sourceMenu F),List.replicate (n + 1) true⟩) used
        (full after d ⟨[],List.replicate (n + 1) true⟩) ∧
      Correct (base F 1) affineWord linePayload (lineHit F (sourceMenu F)) d ∧
      used ≤ lineCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  obtain ⟨used,after,d,checked,correct,budget⟩ := line_exec F (sourceMenu F) r normal packet oldOutput
  exact ⟨used,after,d,checked,correct,Nat.le_trans budget (line_original_bound F)⟩

theorem plane_menu_exec {n : Nat} (F : Family n) (r : Store 38) (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec SourceCandidateQueries.plane (full r (current (base F 2) normal packet oldOutput)
        ⟨pairBits (planeMenu (sourceMenu F)),List.replicate (2 * (n + 1)) true⟩) used
        (full after d ⟨[],List.replicate (2 * (n + 1)) true⟩) ∧
      Correct (base F 2) pairWord planePayload (planeHit F (planeMenu (sourceMenu F))) d ∧
      used ≤ planeCostPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  obtain ⟨used,after,d,checked,correct,budget⟩ :=
    plane_exec F (planeMenu (sourceMenu F)) r normal packet oldOutput
  exact ⟨used,after,d,checked,correct,Nat.le_trans budget (plane_original_bound F)⟩

end PNP.Concrete.ResidualReduction.SourceCandidateBudget
