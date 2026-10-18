import PNP.Concrete.ResidualReduction.SourceSelectorState

/-! The exact affine-first selection result and its interpretation as the
existing contraction choice. An absent result means only that these particular
routes found no reduction; it is not a satisfiability decision or ZeroSlack. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectorResult
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.SourceChain
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)

inductive Result (n m : Nat) where
  | absent
  | affine (witness : Point m × Point n)
  | line (normal : Affine n) (witness : LineWitness n m)
  | plane (normals : Affine n × Affine n) (witness : Point m × Point n)

def fromPlane {n m : Nat} : Option ((Affine n × Affine n) × (Point m × Point n)) → Result n m
  | none => .absent
  | some (normals,witness) => .plane normals witness
def remainder {n : Nat} (F : Family n) : Result n F.length :=
  match SourceCandidateQueries.lineHit F (sourceMenu F) with
  | some (a,w) => .line a w
  | none => fromPlane (SourceCandidateQueries.planeHit F (planeMenu (sourceMenu F)))
def select {n : Nat} (F : Family n) : Result n F.length :=
  match sourceAffineQuery F with
  | some w => .affine w
  | none => remainder F

def choice {n m : Nat} : Result n m → Option (SourceWitnessSelection.Choice n m)
  | .absent => none
  | .affine w => some (SourceWitnessSelection.affineChoice w)
  | .line a w => some (SourceWitnessSelection.lineChoice a w)
  | .plane p w => some (SourceWitnessSelection.planeChoice p w)

theorem fromPlane_choice {n m : Nat}
    (hit : Option ((Affine n × Affine n) × (Point m × Point n))) :
    choice (fromPlane hit) = hit.map (fun p => SourceWitnessSelection.planeChoice p.1 p.2) := by
  cases hit with
  | none => rfl
  | some p => rcases p with ⟨normals,witness⟩; rfl

theorem select_choice {n : Nat} (F : Family n) :
    choice (select F) = SourceWitnessSelection.choose F := by
  cases h : sourceAffineQuery F with
  | some w => simp only [select,SourceWitnessSelection.choose,h,choice]
  | none =>
    unfold select remainder SourceWitnessSelection.choose
    simp only [h]
    rw [← SourceCandidateQueries.line_selection_exact F (sourceMenu F)]
    cases hit : SourceCandidateQueries.lineHit F (sourceMenu F) with
    | none =>
      simp only [Option.map_none]
      exact (fromPlane_choice _).trans
        (SourceCandidateQueries.plane_selection_exact F (planeMenu (sourceMenu F)))
    | some pair =>
      rcases pair with ⟨a,w⟩
      rfl

theorem global_exact {n : Nat} (F : Family (n + 1)) :
    globalStep F = (choice (select F)).bind (SourceWitnessSelection.build F) := by
  rw [select_choice]
  exact SourceWitnessSelection.global_exact F

theorem selected_builds {n : Nat} (F : Family (n + 1))
    (w : SourceWitnessSelection.Choice (n + 1) F.length) (h : choice (select F) = some w) :
    ∃ step, SourceWitnessSelection.build F w = some step :=
  SourceWitnessSelection.choose_total F w (by rw [select_choice] at h; exact h)

def Source {n : Nat} (F : Family n) (d : Data) : Prop :=
  d.dimension = natural n ∧ d.family = (SourceEncoding.familyCodec n).encode F
def Realises {n m : Nat} (result : Result n m) (d : Data) : Prop :=
  match result with
  | .absent => d.output = [false]
  | .affine w => d.count = natural 0 ∧
      d.output = SourceCandidateSearch.optional SourceCandidateQueries.planePayload (some w)
  | .line a w => d.count = natural 1 ∧ d.normals = MatrixInstructions.affineWord a ∧
      d.output = SourceCandidateSearch.optional SourceCandidateQueries.linePayload (some w)
  | .plane p w => d.count = natural 2 ∧ d.normals = SourcePlaneMenuBytes.pairWord p ∧
      d.output = SourceCandidateSearch.optional SourceCandidateQueries.planePayload (some w)
def Correct {n : Nat} (F : Family n) (result : Result n F.length) (d : Data) : Prop :=
  Source F d ∧ Realises result d

end PNP.Concrete.ResidualReduction.SourceSelectorResult
