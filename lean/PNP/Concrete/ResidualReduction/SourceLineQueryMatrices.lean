import PNP.Concrete.ResidualReduction.SourceLineQueryMatrixPadding

/-! Construct both exact line-query matrices after computing the source
direction space. Only original source data enters the prepared program:
neither a direction map nor either output matrix is supplied. The result
counts source instructions; raw parsing, constrained pullbacks and the
selected bilinear search remain downstream integration obligations. -/

namespace PNP.Concrete.ResidualReduction.SourceLineQueryMatrices
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceDirections
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourceActivityMapAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixAlgebra
open PNP.Concrete.ResidualReduction.SourceLineQueryMatrixPadding
open PNP.Concrete.ResidualReduction.SourceDirectionEncoding (codec)

structure State where
  core : SourceActivityConstruction.State
  rows : BitString
  normal : BitString
  activity : BitString
def State.frame (r : State) : Store 3 := .cons r.rows (.cons r.normal (.cons r.activity .nil))
def State.store (r : State) : Store 24 := Frame.join r.core.store r.frame
def registers (r : State) : Registers := r.core.core.family.core.core
def setRegisters (r : State) (s : Registers) : State :=
  {r with core := {r.core with core := {r.core.core with family := {r.core.core.family with core := {r.core.core.family.core with core := s}}}}}
def lifted (body : Block 21) : Block 24 := Frame.block 3 body
theorem lifted_exec (body : Block 21) (r : State) (fuel : Nat) (after : SourceActivityConstruction.State)
    (checked : Exec body r.core.store fuel after.store) :
    Exec (lifted body) r.store fuel ({r with core := after}).store :=
  Frame.execution checked r.frame
def small (body : Block 9) : Block 24 :=
  lifted (SourceActivityConstruction.lifted (SourceDirectionInstructions.small body))
theorem small_exec (body : Block 9) (r : State) (fuel : Nat) (after : Registers)
    (checked : Exec body (registers r).store fuel after.store) :
    Exec (small body) r.store fuel (setRegisters r after).store :=
  lifted_exec _ r _ _
    (SourceActivityConstruction.lifted_exec _ r.core _ _
      (SourceDirectionInstructions.small_exec body r.core.core fuel after checked))

def normalBytes {n : Nat} (F : Family n) (alpha : Affine n) : BitString :=
  List.replicate (F.length * (directionSpace F [alpha]).parameters) false ++
    linearBits (directionSpace F [alpha]).forms
def activityBytes {n : Nat} (F : Family n) (alpha : Affine n) : BitString :=
  sourceBits F (directionSpace F [alpha]) ++
    List.replicate (n * (directionSpace F [alpha]).parameters) false
def start {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  ⟨SourceActivityConstruction.start F [alpha], List.replicate F.length true, [], []⟩
def computed {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  ⟨SourceActivityConstruction.result F [alpha], List.replicate F.length true, [], []⟩
def activityReady {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setRegisters (computed F alpha) {base (directionSpace F [alpha]).parameters [] with sign := List.replicate n true, output := sourceBits F (directionSpace F [alpha])}
def activityDone {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setRegisters (computed F alpha) {base (directionSpace F [alpha]).parameters [] with output := activityBytes F alpha}
def activitySaved {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  {setRegisters (computed F alpha) (base (directionSpace F [alpha]).parameters []) with activity := activityBytes F alpha}
def normalReady {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setRegisters (activitySaved F alpha) {base (directionSpace F [alpha]).parameters [] with input := mapBits (directionSpace F [alpha]).forms, sign := List.replicate F.length true}
def normalDone {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  setRegisters (activitySaved F alpha) {base (directionSpace F [alpha]).parameters [] with output := normalBytes F alpha}
def result {n : Nat} (F : Family n) (alpha : Affine n) : State :=
  {normalDone F alpha with normal := normalBytes F alpha}

def prepareActivity : Block 24 := .seq (.action (.copy 4 18)) (.action (.pop 1))
def saveActivity : Block 24 := .seq (.action (.copy 23 8)) (.action (.clear 8))
def prepareNormal : Block 24 := .seq (.action (.copy 0 15)) (.action (.copy 4 21))
theorem compute_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (lifted SourceActivityConstruction.block) (start F alpha).store
      (SourceActivityConstruction.fuel F [alpha]) (computed F alpha).store :=
  lifted_exec _ (start F alpha) _ _ (SourceActivityConstruction.block_exec F [alpha])
theorem prepareActivity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareActivity (computed F alpha).store 2 (activityReady F alpha).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem activity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (small appendBlock) (activityReady F alpha).store
      (appendFuel n (directionSpace F [alpha]).parameters (F.length * (directionSpace F [alpha]).parameters))
      (activityDone F alpha).store := by
  have core : Exec appendBlock (registers (activityReady F alpha)).store
      (appendFuel n (directionSpace F [alpha]).parameters (F.length * (directionSpace F [alpha]).parameters))
      (registers (activityDone F alpha)).store := by
    simpa only [registers, activityReady, activityDone, setRegisters, base, activityBytes, sourceBits_length] using
      append_exec (base (directionSpace F [alpha]).parameters []) n (directionSpace F [alpha]).parameters
        (sourceBits F (directionSpace F [alpha]))
  exact small_exec _ (activityReady F alpha) _ _ core
theorem saveActivity_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec saveActivity (activityDone F alpha).store 2 (activitySaved F alpha).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem prepareNormal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec prepareNormal (activitySaved F alpha).store 2 (normalReady F alpha).store :=
  Exec.seq (.action _ _) (.action _ _)
theorem normal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (small normalBlock) (normalReady F alpha).store
      (normalFuel n F.length (directionSpace F [alpha]).parameters) (normalDone F alpha).store := by
  have core : Exec normalBlock (registers (normalReady F alpha)).store
      (normalFuel n F.length (directionSpace F [alpha]).parameters)
      (registers (normalDone F alpha)).store := by
    exact SourceLineQueryMatrixPadding.normal_exec (base (directionSpace F [alpha]).parameters [])
      (directionSpace F [alpha]).forms F.length
  exact small_exec _ (normalReady F alpha) _ _ core
theorem saveNormal_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec (.action (.copy (22 : Fin 24) 8)) (normalDone F alpha).store 1 (result F alpha).store := .action _ _

def block : Block 24 := .seq (lifted SourceActivityConstruction.block) <|
  .seq prepareActivity <| .seq (small appendBlock) <| .seq saveActivity <|
    .seq prepareNormal <| .seq (small normalBlock) (.action (.copy 22 8))
def fuel {n : Nat} (F : Family n) (alpha : Affine n) : Nat :=
  SourceActivityConstruction.fuel F [alpha] +
    (2 + (appendFuel n (directionSpace F [alpha]).parameters (F.length * (directionSpace F [alpha]).parameters) +
      (2 + (2 + (normalFuel n F.length (directionSpace F [alpha]).parameters + 1)))))
theorem block_exec {n : Nat} (F : Family n) (alpha : Affine n) :
    Exec block (start F alpha).store (fuel F alpha) (result F alpha).store :=
  Exec.seq (compute_exec F alpha) (Exec.seq (prepareActivity_exec F alpha)
    (Exec.seq (activity_exec F alpha) (Exec.seq (saveActivity_exec F alpha)
      (Exec.seq (prepareNormal_exec F alpha) (Exec.seq (normal_exec F alpha) (saveNormal_exec F alpha))))))

theorem normal_output {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 22 = coefficientMatrixBits (SourceLine.normalQueryMatrix F alpha) :=
  (normal_query_bytes F alpha).symm
theorem activity_output {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 23 = coefficientMatrixBits (SourceLine.activityQueryMatrix F alpha) :=
  (activity_query_bytes F alpha).symm
theorem retained_map {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 15 = mapBits (directionSpace F [alpha]).forms := rfl
theorem retained_dimension {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 18 = List.replicate n true := rfl
theorem retained_source_count {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 21 = List.replicate F.length true := rfl
theorem retained_normal {n : Nat} (F : Family n) (alpha : Affine n) :
    (result F alpha).store.get 19 = (matrixBits [alpha]).reverse := rfl

def program : Program 24 := block.program 0 22
theorem program_run {n : Nat} (F : Family n) (alpha : Affine n) :
    BitRegister.run program (fuel F alpha + 1) ⟨.running 0, (start F alpha).store⟩ =
      ⟨.accepted, (result F alpha).store⟩ := (block_exec F alpha).program_run 0 22

theorem normal_output_length {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 22).length = (n + F.length) * (directionSpace F [alpha]).parameters := by
  rw [normal_output, coefficientMatrixBits_length]
theorem activity_output_length {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 23).length = (n + F.length) * (directionSpace F [alpha]).parameters := by
  rw [activity_output, coefficientMatrixBits_length]
theorem parameter_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (directionSpace F [alpha]).parameters ≤ (codec.encode ⟨n, [alpha], F⟩).length :=
  Nat.le_trans (kernelSpace_parameter_bound (directionSystem F [alpha]))
    (SourceDirectionEncoding.dimension_bound n F [alpha])
private theorem matrixSize_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    (n + F.length) * (directionSpace F [alpha]).parameters ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  have bound := Nat.mul_le_mul
    (Nat.add_le_add (SourceDirectionEncoding.dimension_bound n F [alpha])
      (SourceDirectionEncoding.family_bound n F [alpha])) (parameter_bound F alpha)
  simp only [Nat.add_mul] at bound ⊢
  omega
theorem normal_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 22).length ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  rw [normal_output_length]
  exact matrixSize_bound F alpha
theorem activity_output_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ((result F alpha).store.get 23).length ≤
      2 * ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  rw [activity_output_length]
  exact matrixSize_bound F alpha

private theorem zeroFuel_mono {rows k L : Nat} (hr : rows ≤ L) (hk : k ≤ L) :
    zeroFuel rows k ≤ zeroFuel L L :=
  Nat.add_le_add_right
    (Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hk) 4) hr) 1
theorem append_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    appendFuel n (directionSpace F [alpha]).parameters (F.length * (directionSpace F [alpha]).parameters) ≤
      appendFuel (codec.encode ⟨n, [alpha], F⟩).length (codec.encode ⟨n, [alpha], F⟩).length
        ((codec.encode ⟨n, [alpha], F⟩).length * (codec.encode ⟨n, [alpha], F⟩).length) := by
  let L := (codec.encode ⟨n, [alpha], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [alpha]
  have hk : (directionSpace F [alpha]).parameters ≤ L := parameter_bound F alpha
  have hmSize := Nat.mul_le_mul hm hk
  have hnSize := Nat.mul_le_mul hn hk
  have padding := zeroFuel_mono hn hk
  have lengths := Nat.add_le_add hmSize hnSize
  unfold appendFuel
  dsimp only [L] at *
  omega
theorem normal_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    normalFuel n F.length (directionSpace F [alpha]).parameters ≤
      normalFuel (codec.encode ⟨n, [alpha], F⟩).length (codec.encode ⟨n, [alpha], F⟩).length
        (codec.encode ⟨n, [alpha], F⟩).length := by
  let L := (codec.encode ⟨n, [alpha], F⟩).length
  have hn : n ≤ L := SourceDirectionEncoding.dimension_bound n F [alpha]
  have hm : F.length ≤ L := SourceDirectionEncoding.family_bound n F [alpha]
  have hk : (directionSpace F [alpha]).parameters ≤ L := parameter_bound F alpha
  have hmSize := Nat.mul_le_mul hm hk
  have hnSize := Nat.mul_le_mul hn hk
  have padding := zeroFuel_mono hm hk
  have scan := Nat.mul_le_mul (Nat.add_le_add_right (Nat.mul_le_mul_left 5 hk) 4) hn
  have lengths := Nat.add_le_add hmSize hnSize
  unfold normalFuel SourceLineQueryMatrixProjection.fuel
  dsimp only [L] at *
  omega

def squarePolynomial : NatPolynomial := .mul .variable .variable
def zeroPolynomial : NatPolynomial :=
  .add (.mul (.add (.mul (.constant 3) .variable) (.constant 4)) .variable) (.constant 1)
def reversalPolynomial : NatPolynomial :=
  .add (.mul (.constant 4) (.add squarePolynomial squarePolynomial)) (.constant 1)
def appendPolynomial : NatPolynomial :=
  .add (.add (.mul (.constant 4) squarePolynomial) (.constant 3))
    (.add (.constant 1) (.add (.constant 1) (.add zeroPolynomial reversalPolynomial)))
def normalPolynomial : NatPolynomial :=
  .add zeroPolynomial
    (.add (.add (.mul (.add (.mul (.constant 5) .variable) (.constant 4)) .variable) (.constant 1))
      reversalPolynomial)
theorem appendPolynomial_eval (L : Nat) :
    appendPolynomial.eval L = appendFuel L L (L * L) := rfl
theorem normalPolynomial_eval (L : Nat) :
    normalPolynomial.eval L = normalFuel L L L := rfl
def costPolynomial : NatPolynomial :=
  .add SourceActivityConstruction.costPolynomial
    (.add (.add appendPolynomial normalPolynomial) (.constant 7))
theorem original_input_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    fuel F alpha ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length := by
  have computation := SourceActivityConstruction.original_input_bound F [alpha]
  have activity := append_original_bound F alpha
  have normal := normal_original_bound F alpha
  simp only [costPolynomial, NatPolynomial.eval_add, NatPolynomial.eval_constant,
    appendPolynomial_eval, normalPolynomial_eval]
  unfold fuel
  omega
theorem program_original_bound {n : Nat} (F : Family n) (alpha : Affine n) :
    ∃ steps ≤ costPolynomial.eval (codec.encode ⟨n, [alpha], F⟩).length + 1,
      BitRegister.run program steps ⟨.running 0, (start F alpha).store⟩ =
        ⟨.accepted, (result F alpha).store⟩ :=
  ⟨fuel F alpha + 1, Nat.add_le_add_right (original_input_bound F alpha) 1, program_run F alpha⟩

end PNP.Concrete.ResidualReduction.SourceLineQueryMatrices
