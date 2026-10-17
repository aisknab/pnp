import PNP.Concrete.ResidualReduction.SourceCoefficientGateHead
import PNP.Concrete.ResidualReduction.SourceCoefficientGateTail
import PNP.Concrete.ResidualReduction.MatrixStrictHeader

/-! Input-only exact coefficient gates. The dimension, scalar coefficients and
candidate parameters are consumed from a canonical packet, with no hidden
prepared register or assumed successful check. This stage does not yet compose
the source chart and scalar or assert an all-bitstring physical runtime bound. -/

namespace PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data zero)
open PNP.Concrete.ResidualReduction.SourceCoefficientGateState

def packet {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) : BitString :=
  natural n ++ (SourceQuadraticEncoding.word q ++ (SourceComputedTailEncoding.codec n).encode t)
theorem packet_bytes {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) :
    packet q t = natural n ++ (affineWord q.1 ++
      (SourceQuadraticEncoding.word q.2 ++ (SourceComputedTailEncoding.codec n).encode t)) := by
  rcases q with ⟨h,q⟩
  simp only [packet,SourceQuadraticEncoding.word_cons,List.append_assoc]

def initial (input : BitString) : Store 18 :=
  full (work input) SourceScalarState.emptySaved SourceScalarState.emptyData noSaved
def dimension : Block 18 := .seq (core MatrixStrictHeader.block) (.action (.clear 4))

theorem header_fuel (n : Nat) (suffix : BitString) :
    MatrixStrictHeader.blockFuel (natural n ++ suffix) = 4 * n + 9 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold MatrixStrictHeader.blockFuel at ih ⊢
    change 3 + (4 + MatrixStrictHeader.fuel (natural n ++ suffix)) = 4 * (n + 1) + 9
    omega

theorem dimension_exec (n : Nat) (suffix : BitString) :
    Exec dimension (initial (natural n ++ suffix)) (4 * n + 10)
      (Frame.join (SourceScalarState.initial n suffix) noSaved.store) := by
  let before := work (natural n ++ suffix)
  let counted := {work suffix with target := List.replicate n true,sign := [true]}
  have scan : Exec MatrixStrictHeader.block before.store (4 * n + 9) counted.store := by
    simpa only [header_fuel,MatrixStrictHeader.result,MatrixStrictHeader.scan_canonical,if_true,
      before,counted,work,List.append_nil] using
      MatrixStrictHeader.block_exec (natural n ++ suffix) before
  have clear : Exec (.action (.clear (4 : Fin 18)))
      (full counted SourceScalarState.emptySaved SourceScalarState.emptyData noSaved) 1
      (Frame.join (SourceScalarState.initial n suffix) noSaved.store) := .action _ _
  have cost : 4 * n + 10 = (4 * n + 9) + 1 := by omega
  simpa only [dimension,cost,initial,before] using
    Exec.seq (core_exec scan SourceScalarState.emptySaved SourceScalarState.emptyData noSaved) clear

def setup : Block 18 := .seq dimension (scalar SourceScalarInitialization.block)
def setupFuel (n : Nat) : Nat := (4 * n + 10) + SourceScalarInitialization.fuel n

theorem setup_exec (n : Nat) (suffix : BitString) :
    Exec setup (initial (natural n ++ suffix)) (setupFuel n) (prepared n suffix) := by
  have build := scalar_exec (SourceScalarInitialization.block_exec n suffix) noSaved
  simpa only [setup,setupFuel,prepared,state,full,SourceScalarState.state] using
    Exec.seq (dimension_exec n suffix) build

def block : Block 18 := .seq setup <|
  .seq SourceCoefficientGateHead.block SourceCoefficientGateTail.block
def fuel {n : Nat} (t : TailForm n) : Nat :=
  setupFuel n + (SourceCoefficientGateHead.fuel n + SourceCoefficientGateTail.fuel t)

theorem block_exec {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (suffix : BitString) :
    Exec block (initial (packet q t ++ suffix)) (fuel t) (finished q.1 q.2 t suffix) := by
  let rest := SourceQuadraticEncoding.word q.2 ++ ((SourceComputedTailEncoding.codec n).encode t ++ suffix)
  let input := affineWord q.1 ++ rest
  have setupRun := setup_exec n input
  have head := SourceCoefficientGateHead.block_exec q.1 (zero n) rest input noSaved
  have tail := SourceCoefficientGateTail.block_exec q.1 q.2 t suffix
  simpa only [block,fuel,packet_bytes,List.append_assoc,rest,input,prepared,state,noSaved] using
    Exec.seq setupRun (Exec.seq head tail)

theorem program_run {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (suffix : BitString) :
    BitRegister.run (block.program 0 8) (fuel t + 1) ⟨.running 0,initial (packet q t ++ suffix)⟩ =
      ⟨.accepted,finished q.1 q.2 t suffix⟩ := (block_exec q t suffix).program_run 0 8

theorem packet_length {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) :
    (packet q t).length = 2 * (n + 1) + quadraticBits n +
      ((SourceComputedTailEncoding.codec n).encode t).length := by
  rw [packet_bytes]
  simp only [List.length_append,natural_length,affineWord_length,SourceQuadraticEncoding.word_length]
  omega

theorem fuel_bound {n : Nat} (t : TailForm n) :
    fuel t ≤ 71 * quadraticBits n + 82 * n + 168 := by
  have tail := SourceCoefficientGateTail.fuel_bound t
  simp only [fuel,setupFuel,SourceScalarInitialization.fuel_exact,SourceCoefficientGateHead.fuel]
  omega

theorem fuel_encoded_bound {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) :
    fuel t + 1 ≤ 82 * (packet q t).length + 169 := by
  have bound := fuel_bound t
  rw [packet_length]
  omega

theorem output_true_iff {n : Nat} (q : Quadratic (n + 1)) (t : TailForm n) (suffix : BitString) :
    (finished q.1 q.2 t suffix).get 8 = [true] ↔ q.1 = aConst n true ∧ q.2 = t.polynomial := by
  rw [output_get,List.singleton_inj]
  exact checks_true_iff q.1 q.2 t

end PNP.Concrete.ResidualReduction.SourceCoefficientGateRaw
