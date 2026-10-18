import PNP.Concrete.ResidualReduction.SourceRowReductionAffine
import PNP.Concrete.ResidualReduction.SourceRowReductionPlane

/-! One fixed source program consumes an entire row, reads its leading bits,
dispatches on the computed tail kind, and constructs exactly the existing
affine or plane reduction result. Original tail parameters and the remaining
input stream survive the transformation.

The boundary here is a typed tail already placed in protected registers by
the upstream computation. The linear bound counts source instructions, including
one instruction for a register copy; it is not a whole-contraction physical
machine runtime theorem or a raw tail-parameter loader. -/

namespace PNP.Concrete.ResidualReduction.SourceRowReductionInstructions
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceRowReductionState

def dispatch : Block 19 := .branch 18 .skip
  SourceRowReductionAffine.block SourceRowReductionPlane.block
def transformFuel {n : Nat} (t : TailForm n) (r : Row (n + 1)) : Nat :=
  match t with
  | .affine _ => SourceRowReductionAffine.fuel n r.left.1 r.right.1
  | .plane a b _ => SourceRowReductionPlane.fuel a b r.left.2 r.right.2 r.left.1 r.right.1
def block : Block 19 := .seq SourceRowReductionLoad.block dispatch
def fuel {n : Nat} (t : TailForm n) (r : Row (n + 1)) : Nat :=
  SourceRowReductionLoad.fuel n + (1 + transformFuel t r)

theorem dispatch_exec {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    Exec dispatch (loaded t r suffix) (1 + transformFuel t r)
      (finished t suffix (reduceRow t r)) := by
  rcases r with ⟨selected,⟨lh,f⟩,⟨rh,g⟩⟩
  cases t with
  | affine u =>
    exact Exec.zero rfl (SourceRowReductionAffine.block_exec [] [] u f g selected lh rh suffix false)
  | plane a b u =>
    exact Exec.one rfl (SourceRowReductionPlane.block_exec a b u f g selected lh rh suffix)

theorem block_exec {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    Exec block (SourceRowReductionState.initial t r suffix) (fuel t r)
      (finished t suffix (reduceRow t r)) :=
  Exec.seq (SourceRowReductionLoad.block_exec t r suffix) (dispatch_exec t r suffix)

theorem program_run {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    BitRegister.run (block.program 0 8) (fuel t r + 1)
      ⟨.running 0,SourceRowReductionState.initial t r suffix⟩ =
      ⟨.accepted,finished t suffix (reduceRow t r)⟩ := (block_exec t r suffix).program_run 0 8

theorem output_get {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    (finished t suffix (reduceRow t r)).get 8 = (codec n).encode (reduceRow t r) :=
  SourceRowReductionState.output_get _ _ _
theorem suffix_get {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    (finished t suffix (reduceRow t r)).get 0 = suffix :=
  SourceRowReductionState.suffix_get _ _ _
theorem output_decode {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    (codec n).decode ((finished t suffix (reduceRow t r)).get 8) = some (reduceRow t r) :=
  SourceRowReductionState.output_decode _ _ _
theorem output_bound {n : Nat} (t : TailForm n) (r : Row (n + 1)) (suffix : BitString) :
    ((finished t suffix (reduceRow t r)).get 8).length ≤ 2 * n + 4 := bytes_bound _

theorem transformFuel_bound {n : Nat} (t : TailForm n) (r : Row (n + 1)) :
    transformFuel t r ≤ 287 * (n + 1) + 197 := by
  cases t with
  | affine u =>
    have bound := SourceRowReductionAffine.fuel_bound n r.left.1 r.right.1
    change SourceRowReductionAffine.fuel n r.left.1 r.right.1 ≤ 287 * (n + 1) + 197
    omega
  | plane a b u => exact SourceRowReductionPlane.fuel_bound a b r.left.2 r.right.2 r.left.1 r.right.1
theorem fuel_bound {n : Nat} (t : TailForm n) (r : Row (n + 1)) :
    fuel t r ≤ 305 * (n + 1) + 219 := by
  have bound := transformFuel_bound t r
  unfold fuel SourceRowReductionLoad.fuel
  omega
theorem fuel_row_bound {n : Nat} (t : TailForm n) (r : Row (n + 1)) :
    fuel t r + 1 ≤ 153 * (rowWord r).length := by
  have bound := fuel_bound t r
  rw [rowWord_length]
  omega

end PNP.Concrete.ResidualReduction.SourceRowReductionInstructions
