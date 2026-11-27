import PNP.SignedTernary.Matrix.Basis
import PNP.SignedTernary.Codec

set_option autoImplicit false

namespace PNP.SignedTernary.Encoding
open PNP.SignedTernary.Field PNP.SignedTernary.Linear PNP.SignedTernary.Gate PNP.SignedTernary.Network
open PNP.Concrete (BitString CNFSAT decodeEncodedCNF)

theorem dimension_agrees (raw : BitString) :
    inputWidth (parsedSites (decodeEncodedCNF raw)).length (PNP.SignedTernary.CNF.rawForms raw).length =
      PNP.SignedTernary.Codec.dimension raw := by
  rw [PNP.SignedTernary.Codec.dimension_actual]
  simp only [inputWidth,blockSize_eq,stage_count]
  omega

def castSquare {n m : Nat} (h : n=m) (A : Rows n n) : Rows m m := h ▸ A

def SignedSolution (n : Nat) (A : Rows n n) : Prop :=
  ∃ x : Vec n, Signed x ∧ Signed (applyRows A x)

theorem castSquare_donor {n m : Nat} (h : n=m) (A : Rows n n) :
    SignedSolution m (castSquare h A) ↔ SignedSolution n A := by
  cases h
  exact Iff.rfl

def encodedMatrix (raw : BitString) : Rows (PNP.SignedTernary.Codec.dimension raw) (PNP.SignedTernary.Codec.dimension raw) :=
  castSquare (dimension_agrees raw) (literalMatrix raw)

theorem encodedMatrix_iff_CNFSAT (raw : BitString) :
    SignedSolution (PNP.SignedTernary.Codec.dimension raw) (encodedMatrix raw) ↔ CNFSAT raw :=
  (castSquare_donor (dimension_agrees raw) (literalMatrix raw)).trans (literalMatrix_iff_CNFSAT raw)

/-- A canonical bit-string encoder of the computed literal matrix. -/
def encodeCNFMatrix (raw : BitString) : BitString :=
  PNP.SignedTernary.Codec.pack (PNP.SignedTernary.Codec.dimension raw) (encodedMatrix raw)

/-- Independent target language: parse a canonical square and ask for one common physical donor. -/
def MatrixSAT (bytes : BitString) : Prop :=
  ∃ A : PNP.SignedTernary.Codec.Square, PNP.SignedTernary.Codec.unpack bytes = some A ∧ SignedSolution A.1 A.2

theorem canonical_unpack (raw : BitString) :
    PNP.SignedTernary.Codec.unpack (encodeCNFMatrix raw) =
      some ⟨PNP.SignedTernary.Codec.dimension raw,encodedMatrix raw⟩ :=
  PNP.SignedTernary.Codec.raw_pack_recovers raw (encodedMatrix raw)

/-- All raw strict source inputs, now at the real canonical target bit-string boundary. -/
theorem matrixSAT_encodeCNFMatrix_iff (raw : BitString) : MatrixSAT (encodeCNFMatrix raw) ↔ CNFSAT raw := by
  constructor
  · rintro ⟨A,ha,hd⟩
    rw [canonical_unpack] at ha
    cases ha
    exact (encodedMatrix_iff_CNFSAT raw).1 hd
  · intro h
    exact ⟨⟨PNP.SignedTernary.Codec.dimension raw,encodedMatrix raw⟩,canonical_unpack raw,
      (encodedMatrix_iff_CNFSAT raw).2 h⟩

theorem canonical_length (raw : BitString) :
    (encodeCNFMatrix raw).length =
      PNP.SignedTernary.Codec.dimension raw + 1 + 2*(PNP.SignedTernary.Codec.dimension raw*PNP.SignedTernary.Codec.dimension raw) :=
  PNP.SignedTernary.Codec.pack_length _ _

/-- Structural encoded size; no evaluation-time or search-time assertion. -/
theorem canonical_quadratic_bound (raw : BitString) :
    (encodeCNFMatrix raw).length ≤
      (13*raw.length+30)+1+2*((13*raw.length+30)*(13*raw.length+30)) :=
  PNP.SignedTernary.Codec.raw_pack_bound raw (encodedMatrix raw)

theorem malformed_source_has_no_solution : ¬ MatrixSAT (encodeCNFMatrix []) := by
  intro h
  exact PNP.SignedTernary.CNF.malformed_empty_control
    ((PNP.SignedTernary.CNF.raw_iff_CNFSAT []).2 ((matrixSAT_encodeCNFMatrix_iff []).1 h))

theorem empty_conjunction_has_solution :
    MatrixSAT (encodeCNFMatrix (PNP.Concrete.encodeCNF ⟨0,[]⟩)) :=
  (matrixSAT_encodeCNFMatrix_iff _).2 ((PNP.SignedTernary.CNF.raw_iff_CNFSAT _).1 PNP.SignedTernary.CNF.raw_positive_control)

/-- A deliberately nonlinear map demonstrates why actual additivity was required. -/
def nonlinearProbe (x : Vec 1) : Vec 1 := (mul x.1 x.1,())

theorem basis_samples_alone_fail :
    applyRows (matrixOf 1 nonlinearProbe) (.t,()) = (.t,()) ∧
      nonlinearProbe (.t,()) = (.o,()) := ⟨rfl,rfl⟩

end PNP.SignedTernary.Encoding
