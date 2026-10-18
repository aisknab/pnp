import PNP.Concrete.ResidualReduction.SourceCandidateSearch
import PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes
import PNP.Concrete.ResidualReduction.SourceWitnessSelection

/-! Closed line and plane candidate-search programs. Their query contracts are
discharged by the existing actual machine execution theorems, not supplied by
a caller. The returned normal record and witness are the first successful pair
in literal list order. Full raw dispatch and successor construction remain
separate obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateQueries
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held full)
open PNP.Concrete.ResidualReduction.SourceCandidateSearch
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourcePlaneMenuBytes (pairWord pairBits)

def base {n : Nat} (F : Family n) (count : Nat) : Data :=
  ⟨natural n,natural count,[],(SourceEncoding.familyCodec n).encode F,[],[]⟩
def linePayload {n m : Nat} (w : LineWitness n m) : BitString :=
  (SourceLineOutput.recordCodec n m).encode w
def planePayload {n m : Nat} (w : Point m × Point n) : BitString :=
  (pairCodec (SourceEncoding.pointCodec m) (SourceEncoding.pointCodec n)).encode w

theorem line_optional {n m : Nat} (w : Option (LineWitness n m)) :
    optional linePayload w = (SourceLineOutput.codec n m).encode w := by cases w <;> rfl
theorem plane_optional {n m : Nat} (w : Option (Point m × Point n)) :
    optional planePayload w = (SourceAffineOutput.witnessCodec m n).encode w := by cases w <;> rfl

theorem line_current {n : Nat} (F : Family n) (a : Affine n) (packet output : BitString) :
    current (base F 1) (affineWord a) packet output =
      SourceSelectionInvocation.initial F [a] packet output := by
  simp only [current,base,SourceSelectionInvocation.initial,matrixBits,List.append_nil,
    List.length_cons,List.length_nil]
theorem plane_current {n : Nat} (F : Family n) (p : Affine n × Affine n) (packet output : BitString) :
    current (base F 2) (pairWord p) packet output =
      SourceSelectionInvocation.initial F [p.1,p.2] packet output := by
  simp only [current,base,SourceSelectionInvocation.initial,matrixBits,pairWord,List.append_nil,
    List.length_cons,List.length_nil]

def lineBudget {n : Nat} (F : Family n) : Nat :=
  let length := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + n + 3
  SourceLineRaw.sourceBudget length + 8 * length + 109
def planeBudget {n : Nat} (F : Family n) : Nat :=
  let length := (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length + 2 * n + 5
  SourcePlaneRaw.sourceBudget length + 8 * length + 109

theorem line_contract {n : Nat} (F : Family n) :
    QueryContract SourceSelectionInvocation.line (base F 1) affineWord
      (sourceLineQuery F) linePayload (lineBudget F) := by
  intro a r packet
  obtain ⟨used,after,checked,bound⟩ := SourceSelectionInvocation.line_family_exec F a r packet [false]
  refine ⟨used,after,?_,?_⟩
  · simpa only [line_current,line_optional] using checked
  · simpa only [lineBudget,SourceSelectionPacket.line_packet_length] using bound
theorem plane_contract {n : Nat} (F : Family n) :
    QueryContract SourceSelectionInvocation.plane (base F 2) pairWord
      (fun p => SourcePlane.sourcePlaneQuery F p.1 p.2) planePayload (planeBudget F) := by
  intro p r packet
  obtain ⟨used,after,checked,bound⟩ :=
    SourceSelectionInvocation.plane_family_exec F p.1 p.2 r packet [false]
  refine ⟨used,after,?_,?_⟩
  · simpa only [plane_current,plane_optional] using checked
  · simpa only [planeBudget,SourceSelectionPacket.plane_packet_length] using bound

theorem line_bytes {n : Nat} (us : List (Affine n)) : words affineWord us = matrixBits us := by
  induction us with
  | nil => rfl
  | cons a us ih => simp only [words,matrixBits,ih]
theorem plane_bytes {n : Nat} (ps : List (Affine n × Affine n)) : words pairWord ps = pairBits ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [words,pairBits,ih]

def line : Block 46 := block SourceSelectionInvocation.line
def plane : Block 46 := block SourceSelectionInvocation.plane
def lineHit {n : Nat} (F : Family n) (us : List (Affine n)) :=
  first (sourceLineQuery F) us
def planeHit {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) :=
  first (fun p => SourcePlane.sourcePlaneQuery F p.1 p.2) ps

theorem line_exec {n : Nat} (F : Family n) (us : List (Affine n)) (r : Store 38)
    (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec line (full r (current (base F 1) normal packet oldOutput)
        ⟨matrixBits us,List.replicate (n + 1) true⟩) used
        (full after d ⟨[],List.replicate (n + 1) true⟩) ∧
      Correct (base F 1) affineWord linePayload (lineHit F us) d ∧
      used ≤ 2 + loopBound (n + 1) (lineBudget F) us.length := by
  have checked := block_exec SourceSelectionInvocation.line (base F 1) affineWord
    (sourceLineQuery F) linePayload (n + 1) (lineBudget F) (by omega) (line_contract F)
    us (fun a _ => affineWord_length a) r normal packet oldOutput
  simpa only [line,line_bytes,lineHit] using checked

theorem plane_exec {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) (r : Store 38)
    (normal packet oldOutput : BitString) :
    ∃ used after d,
      Exec plane (full r (current (base F 2) normal packet oldOutput)
        ⟨pairBits ps,List.replicate (2 * (n + 1)) true⟩) used
        (full after d ⟨[],List.replicate (2 * (n + 1)) true⟩) ∧
      Correct (base F 2) pairWord planePayload (planeHit F ps) d ∧
      used ≤ 2 + loopBound (2 * (n + 1)) (planeBudget F) ps.length := by
  have checked := block_exec SourceSelectionInvocation.plane (base F 2) pairWord
    (fun p => SourcePlane.sourcePlaneQuery F p.1 p.2) planePayload (2 * (n + 1))
    (planeBudget F) (by omega) (plane_contract F)
    ps (fun p _ => SourcePlaneMenuBytes.pairWord_length p) r normal packet oldOutput
  simpa only [plane,plane_bytes,planeHit] using checked

theorem line_selection_exact {n : Nat} (F : Family n) (us : List (Affine n)) :
    (lineHit F us).map (fun p => SourceWitnessSelection.lineChoice p.1 p.2) =
      SourceWitnessSelection.lineSearch F us :=
  first_map (sourceLineQuery F) (fun p => SourceWitnessSelection.lineChoice p.1 p.2) us
theorem plane_selection_exact {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) :
    (planeHit F ps).map (fun p => SourceWitnessSelection.planeChoice p.1 p.2) =
      SourceWitnessSelection.planeSearch F ps :=
  first_map (fun (p : Affine n × Affine n) => SourcePlane.sourcePlaneQuery F p.1 p.2)
    (fun p => SourceWitnessSelection.planeChoice p.1 p.2) ps

def lineProgram : Program 46 := line.program 0 43
def planeProgram : Program 46 := plane.program 0 43

theorem line_program_run {n : Nat} (F : Family n) (us : List (Affine n)) (r : Store 38)
    (normal packet oldOutput : BitString) :
    ∃ used after d,
      BitRegister.run lineProgram (used + 1)
        ⟨.running 0,full r (current (base F 1) normal packet oldOutput)
          ⟨matrixBits us,List.replicate (n + 1) true⟩⟩ =
        ⟨.accepted,full after d ⟨[],List.replicate (n + 1) true⟩⟩ ∧
      Correct (base F 1) affineWord linePayload (lineHit F us) d ∧
      used + 1 ≤ 3 + loopBound (n + 1) (lineBudget F) us.length := by
  obtain ⟨used,after,d,checked,correct,bound⟩ := line_exec F us r normal packet oldOutput
  exact ⟨used,after,d,checked.program_run 0 43,correct,by omega⟩

theorem plane_program_run {n : Nat} (F : Family n) (ps : List (Affine n × Affine n)) (r : Store 38)
    (normal packet oldOutput : BitString) :
    ∃ used after d,
      BitRegister.run planeProgram (used + 1)
        ⟨.running 0,full r (current (base F 2) normal packet oldOutput)
          ⟨pairBits ps,List.replicate (2 * (n + 1)) true⟩⟩ =
        ⟨.accepted,full after d ⟨[],List.replicate (2 * (n + 1)) true⟩⟩ ∧
      Correct (base F 2) pairWord planePayload (planeHit F ps) d ∧
      used + 1 ≤ 3 + loopBound (2 * (n + 1)) (planeBudget F) ps.length := by
  obtain ⟨used,after,d,checked,correct,bound⟩ := plane_exec F ps r normal packet oldOutput
  exact ⟨used,after,d,checked.program_run 0 43,correct,by omega⟩

end PNP.Concrete.ResidualReduction.SourceCandidateQueries
