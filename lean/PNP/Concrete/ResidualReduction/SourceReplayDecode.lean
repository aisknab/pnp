import PNP.Concrete.ResidualReduction.SourceReplayEvaluate

/-! One complete reconstruction step from actual encoded stored fields. The
missing bit is computed from source rows, never supplied. Conditional shear
and pivot insertion then implement the exact existing decode function.
Whole-request parsing and the complete history loop remain separate phases. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayDecode
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceReplayState

theorem insert_sheared {n : Nat} (k : Fin (n + 1)) (bit : Bool) (z v : Point n) :
    insert n k (bit,SourceReplayPoint.sheared bit z v) = unchart k v (bit,z) := by
  cases bit <;> rfl

def ready {n : Nat} (bit : Bool) (z v : Point n) : Registers :=
  {blank [] [] with input := (SourceEncoding.pointCodec n).encode z,mode := (SourceEncoding.pointCodec n).encode v,remaining := List.replicate n true,sign := [bit]}
def afterShear {n : Nat} (bit : Bool) (z v : Point n) : Registers :=
  {blank [] [] with sign := [bit],output := (SourceEncoding.pointCodec n).encode (SourceReplayPoint.sheared bit z v)}
def insertReady {n : Nat} (k : Fin (n + 1)) (bit : Bool) (z v : Point n) : Registers :=
  {blank [] [] with input := (SourceEncoding.pointCodec n).encode (SourceReplayPoint.sheared bit z v),remaining := List.replicate k.val true,sign := [bit]}
def inserted {n : Nat} (k : Fin (n + 1)) (bit : Bool) (z v : Point n) : Registers :=
  {blank [] [] with sign := [bit],output := (SourceEncoding.pointCodec (n + 1)).encode (insert n k (bit,SourceReplayPoint.sheared bit z v))}

def setup : Block 16 := .seq (.action (.copy 0 13)) (.seq (.action (.copy 5 12))
  (.seq (.action (.copy 2 14)) (.action (.copy 4 15))))
def insertSetup : Block 16 := .seq (.action (.copy 0 8)) (.seq (.action (.clear 8)) (.action (.copy 2 11)))
def insertDispatch : Block 16 := .branch 15 .skip (core (SourceReplayPoint.splice false)) (core (SourceReplayPoint.splice true))
def reconstruct : Block 16 := .seq setup (.seq (core SourceReplayPoint.shearBlock)
  (.seq insertSetup (.seq insertDispatch (.action (.clear 4)))))
def reconstructFuel (n pivot : Nat) (bit : Bool) : Nat := 9 * pivot + 14 + SourceReplayPoint.shearFuel n bit

theorem reconstruct_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) (bit : Bool) :
    Exec reconstruct (work [] [] (evaluated (data F w k v z) bit)) (reconstructFuel n k.val bit)
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (unchart k v (bit,z))) (evaluated (data F w k v z) bit)) := by
  let saved := evaluated (data F w k v z) bit
  have setup : Exec setup (work [] [] saved) 4 (full (ready bit z v) saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have shear := core_exec (SourceReplayPoint.shear_point (blank [] []) bit z v) saved
  have prepare : Exec insertSetup (full (afterShear bit z v) saved) 3 (full (insertReady k bit z v) saved) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have insertRun : Exec insertDispatch (full (insertReady k bit z v) saved)
      (1 + SourceReplayPoint.spliceFuel k.val) (full (inserted k bit z v) saved) := by
    cases bit with
    | false => exact Exec.zero rfl (core_exec (SourceReplayPoint.splice_point {blank [] [] with sign := [false]} k false z) saved)
    | true => exact Exec.one rfl (core_exec (SourceReplayPoint.splice_point {blank [] [] with sign := [true]} k true (pXor z v)) saved)
  have clear : Exec (.action (.clear (4 : Fin 16))) (full (inserted k bit z v) saved) 1
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (unchart k v (bit,z))) saved) := by
    rw [← insert_sheared]
    exact .action _ _
  have cost : reconstructFuel n k.val bit =
      4 + (SourceReplayPoint.shearFuel n bit + (3 + ((1 + SourceReplayPoint.spliceFuel k.val) + 1))) := by
    unfold reconstructFuel SourceReplayPoint.spliceFuel
    omega
  simpa only [reconstruct,cost,saved,ready,afterShear,blank] using
    Exec.seq setup (Exec.seq shear (Exec.seq prepare (Exec.seq insertRun clear)))

def block : Block 16 := .seq SourceReplayEvaluate.block reconstruct
def fuel (n rows pivot : Nat) (bit : Bool) : Nat :=
  SourceReplayEvaluate.fuel n rows pivot + reconstructFuel n pivot bit

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (v z : Point n) :
    Exec block (work [] [] (data F w k v z)) (fuel n F.length k.val (value F w k z))
      (work [] ((SourceEncoding.pointCodec (n + 1)).encode (decode (markSource F w) k v z))
        (evaluated (data F w k v z) (value F w k z))) := by
  have checked := Exec.seq (SourceReplayEvaluate.block_exec F w k v z)
    (reconstruct_exec F w k v z (value F w k z))
  simpa only [block,fuel,SourceReplayAlgebra.decode_direct,value] using checked

theorem fuel_bound (n rows pivot : Nat) (bit : Bool) (hp : pivot ≤ n) :
    fuel n rows pivot bit ≤ (18 * n + 49) * rows + 29 * n + 45 := by
  have shear := SourceReplayPoint.shearFuel_bound n bit
  simp only [fuel,SourceReplayEvaluate.fuel,reconstructFuel,SourceReplayValue.fuel,
    Nat.mul_add,Nat.add_mul,Nat.mul_one] at *
  omega

def costPolynomial : NatPolynomial :=
  .add (.mul (.linear 18 49) .variable) (.linear 29 45)
theorem costPolynomial_eval (L : Nat) :
    costPolynomial.eval L = (18 * L + 49) * L + 29 * L + 45 := rfl
theorem bounded_cost (n rows pivot L : Nat) (bit : Bool)
    (hn : n ≤ L) (hm : rows ≤ L) (hp : pivot ≤ n) :
    fuel n rows pivot bit ≤ costPolynomial.eval L := by
  have first := fuel_bound n rows pivot bit hp
  have mono := Nat.mul_le_mul (show 18 * n + 49 ≤ 18 * L + 49 by omega) hm
  rw [costPolynomial_eval]
  omega

end PNP.Concrete.ResidualReduction.SourceReplayDecode
