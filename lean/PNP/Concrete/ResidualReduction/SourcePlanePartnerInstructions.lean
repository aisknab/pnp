import PNP.Concrete.ResidualReduction.SourcePlanePartnerBuilder

/-! Exact first-match plane partner construction. Every candidate is generated
from the original normal pair, compared coefficient by coefficient, and tried
in the existing order. A failed search produces the canonical none encoding.
There is no caller-supplied table, partner or correctness certificate. -/

namespace PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourcePlanePartnerSpecification
open PNP.Concrete.ResidualReduction.SourcePlanePartnerBuilder

def result {n : Nat} (a b f : Affine n) : Option (Affine n) → Store 12
  | none => state a b f false []
  | some p => state a b f true (affineWord p)
def search : List Entry → Block 12
  | [] => .skip
  | e :: es => .seq (generate e.1) <| .seq compare
      (.branch 6 .skip (search es) (choose e.2))
def searchFuel {n : Nat} (a b f : Affine n) : List Entry → Nat
  | [] => 1
  | e :: es => generateFuel n e.1 + (compareFuel n +
      (1 + if aEq f (value a b e.1) then 1 else searchFuel a b f es))

theorem search_exec {n : Nat} (a b f : Affine n) (es : List Entry) :
    Exec (search es) (state a b f false []) (searchFuel a b f es)
      (result a b f (lookup a b f es)) := by
  induction es with
  | nil => exact .skip _
  | cons e es ih =>
    have generated := generate_exec a b f false e.1
    have compared := compare_exec a b f false (value a b e.1)
    cases h : aEq f (value a b e.1) with
    | false =>
      rw [h] at compared
      have branch : Exec (.branch (6 : Fin 12) .skip (search es) (choose e.2))
          (state a b f false []) (1 + searchFuel a b f es) (result a b f (lookup a b f es)) :=
        Exec.zero rfl ih
      simpa only [search,searchFuel,SourcePlanePartnerSpecification.lookup,h,Bool.false_eq_true,↓reduceIte] using
        Exec.seq generated (Exec.seq compared branch)
    | true =>
      rw [h] at compared
      have branch : Exec (.branch (6 : Fin 12) .skip (search es) (choose e.2))
          (state a b f true []) (1 + 1) (result a b f (some (output a b e.2))) :=
        Exec.one rfl (choose_exec a b f true e.2)
      simpa only [search,searchFuel,SourcePlanePartnerSpecification.lookup,h,↓reduceIte] using
        Exec.seq generated (Exec.seq compared branch)

theorem searchFuel_bound {n : Nat} (a b f : Affine n) (es : List Entry) :
    searchFuel a b f es ≤ (32 * (n + 1) + 18) * es.length + 1 := by
  induction es with
  | nil => exact Nat.le_refl _
  | cons e es ih =>
    have bound := generateFuel_bound n e.1
    simp only [searchFuel]
    split
    all_goals
      simp only [compareFuel,List.length_cons,Nat.mul_add,Nat.add_mul,Nat.mul_one,
        Nat.mul_assoc] at *
      omega

def codec (n : Nat) : Codec (Option (Affine n)) :=
  MatrixSolutionEncoding.optionCodec (SourceEncoding.affineCodec n)
def encodedResult {n : Nat} (a b f : Affine n) (p : Option (Affine n)) : Store 12 :=
  state a b f p.isSome ((codec n).encode p)
def serialize : Block 12 := .branch 6 .skip (.action (.push 8 false)) (.action (.push 8 true))

theorem serialize_exec {n : Nat} (a b f : Affine n) (p : Option (Affine n)) :
    Exec serialize (result a b f p) 2 (encodedResult a b f p) := by
  cases p with
  | none => exact Exec.zero rfl (.action _ _)
  | some p => exact Exec.one rfl (.action _ _)

def block : Block 12 := .seq setup <| .seq (search entries) serialize
def fuel {n : Nat} (a b f : Affine n) : Nat :=
  (3 * (n + 1) + 6) + (searchFuel a b f entries + 2)
def finished {n : Nat} (a b f : Affine n) : Store 12 :=
  encodedResult a b f (planePartner a b f)

theorem block_exec {n : Nat} (a b f : Affine n) :
    Exec block (SourcePlanePartnerBuilder.initial a b f) (fuel a b f) (finished a b f) := by
  have start := initialize_exec a b f
  have selected := search_exec a b f entries
  rw [lookup_existing] at selected
  exact Exec.seq start (Exec.seq selected (serialize_exec a b f (planePartner a b f)))

theorem fuel_bound {n : Nat} (a b f : Affine n) : fuel a b f ≤ 227 * (n + 1) + 135 := by
  have bound := searchFuel_bound a b f entries
  have count : entries.length = 7 := rfl
  rw [count] at bound
  unfold fuel
  omega

/-- Aggregate operand bytes, not a claim that a raw input loader is present. -/
def operandBytes {n : Nat} (a b f : Affine n) : BitString :=
  affineWord a ++ (affineWord b ++ affineWord f)
theorem fuel_operand_bound {n : Nat} (a b f : Affine n) :
    fuel a b f ≤ 121 * (operandBytes a b f).length := by
  have bound := fuel_bound a b f
  simp only [operandBytes,List.length_append,affineWord_length]
  omega

theorem output_get {n : Nat} (a b f : Affine n) :
    (finished a b f).get 8 = (codec n).encode (planePartner a b f) := rfl
theorem output_decode {n : Nat} (a b f : Affine n) :
    (codec n).decode ((finished a b f).get 8) = some (planePartner a b f) := decode_encode _ _
theorem result_flag {n : Nat} (a b f : Affine n) :
    (finished a b f).get 6 = [(planePartner a b f).isSome] := rfl
theorem output_bound {n : Nat} (a b f : Affine n) :
    ((finished a b f).get 8).length ≤ n + 2 := by
  rw [output_get]
  cases planePartner a b f with
  | none =>
    change 1 ≤ n + 2
    omega
  | some p =>
    change (true :: affineWord p).length ≤ n + 2
    rw [List.length_cons,affineWord_length]
    omega

theorem program_run {n : Nat} (a b f : Affine n) :
    BitRegister.run (block.program 0 8) (fuel a b f + 1)
      ⟨.running 0,SourcePlanePartnerBuilder.initial a b f⟩ =
      ⟨.accepted,finished a b f⟩ := (block_exec a b f).program_run 0 8

end PNP.Concrete.ResidualReduction.SourcePlanePartnerInstructions
