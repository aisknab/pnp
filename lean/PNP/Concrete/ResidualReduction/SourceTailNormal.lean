import PNP.Concrete.ResidualReduction.SourceTailNormalAlgebra

/-! Literal construction of the selected tail normal. The pivot is removed
by the existing counted cutter, the remaining variable coefficients are read
and retained, and the actual original constant is consumed and replaced by
false. Neither a normalized factor nor a tail normal is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceTailNormal
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixPullbackAlgebra
open PNP.Concrete.ResidualReduction.SourceTailNormalAlgebra

def ready {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) : Registers :=
  ⟨affineWord f,List.replicate n true,List.replicate k.val true,[],[],[],[],[],[]⟩
def finished {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) : Registers :=
  ⟨[],List.replicate n true,[],[],[],[],[],[],affineWord (tailNormal k f)⟩
def prepare : Block 9 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 2 1)) (.action (.clear 8))
def replaceConstant : Block 9 := .seq (.action (.pop 0)) (.action (.push 8 false))
def block : Block 9 := .seq SourceChartAffine.cutBlock <| .seq prepare <|
  .seq copyLoop <| .seq replaceConstant <|
  .seq ClauseQuery.reverseLoop (.action (.clear 4))
def fuel (n pivot : Nat) : Nat := 9 * pivot + 9 * n + 14

theorem block_exec {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) :
    Exec block (ready f k).store (fuel n k.val) (finished f k).store := by
  obtain ⟨front,suffix,width,whole,tail⟩ := SourceChartAffine.cut_words bitCodec n k f
  let part := cut n k f
  let cutDone := {ready f k with input := suffix,remaining := [],sign := [part.1],output := affineWord part.2}
  have first : Exec SourceChartAffine.cutBlock (ready f k).store (9 * k.val + 6) cutDone.store := by
    have checked := SourceChartAffine.cut_exec (ready f k) front suffix part.1
    simpa only [ready,cutDone,affineWord,SourceEncoding.affineCodec,whole,tail,width,part] using checked
  let normalReady := {cutDone with input := affineWord part.2,remaining := List.replicate n true,output := []}
  let base := {ready f k with input := [],remaining := [],sign := [part.1],output := []}
  let copied := {base with input := [aConstant part.2],excess := (normalWord part.2).reverse}
  let replaced := {base with excess := (normalWord part.2).reverse,output := [false]}
  let reversed := {base with output := affineWord (tailNormal k f)}
  have prep : Exec prepare cutDone.store 3 normalReady.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have copy : Exec copyLoop normalReady.store (5 * n + 1) copied.store := by
    simpa only [normalReady,cutDone,base,copied,ready,word_split,normalWord_length,List.append_nil] using
      copy_exec base (normalWord part.2) [aConstant part.2]
  have replace : Exec replaceConstant copied.store 2 replaced.store :=
    Exec.seq (.action _ _) (.action _ _)
  have reverse : Exec ClauseQuery.reverseLoop replaced.store (4 * n + 1) reversed.store := by
    simpa only [replaced,reversed,base,ready,part,tailNormal_word,
      List.length_reverse,normalWord_length,List.reverse_reverse] using
      ClauseQuery.reverse_exec {base with output := [false]} (normalWord part.2).reverse
  have clear : Exec (.action (.clear (4 : Fin 9))) reversed.store 1 (finished f k).store := .action _ _
  have cost : fuel n k.val = (9 * k.val + 6) + (3 + ((5 * n + 1) + (2 + ((4 * n + 1) + 1)))) := by
    unfold fuel; omega
  simpa only [block,cost] using Exec.seq first
    (Exec.seq prep (Exec.seq copy (Exec.seq replace (Exec.seq reverse clear))))

theorem fuel_bound {n : Nat} (k : Fin (n + 1)) : fuel n k.val ≤ 18 * n + 14 := by
  have hk := k.isLt
  unfold fuel
  omega
theorem fuel_source_bound {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) :
    fuel n k.val ≤ 18 * (affineWord f).length := by
  have bound := fuel_bound k
  rw [affineWord_length]
  omega

end PNP.Concrete.ResidualReduction.SourceTailNormal
