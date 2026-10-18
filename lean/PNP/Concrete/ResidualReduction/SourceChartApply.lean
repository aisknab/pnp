import PNP.Concrete.ResidualReduction.SourceChartSelection
import PNP.Concrete.ResidualReduction.SourceChartAffine
import PNP.Concrete.NormalizerRegisterFrame

/-! Compose discovery of the first pivot with the actual affine chart
transformation. Only the original direction, factor and dimension are present
initially. The selected pivot and tail are passed by literal register actions,
not by a semantic callback or a supplied correctness certificate. -/

namespace PNP.Concrete.ResidualReduction.SourceChartApply
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions

def saved {n : Nat} (f : Affine (n + 1)) : Store 2 :=
  .cons (affineWord f) (.cons (List.replicate n true) .nil)
def full {n : Nat} (r : Registers) (f : Affine (n + 1)) : Store 11 :=
  Frame.join r.store (saved f)
def initial {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1)) : Store 11 :=
  full (SourceChartSelection.ready ((SourceEncoding.pointCodec (n + 1)).encode v)) f
def answer {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1)) : BitString :=
  match chooseChart v with
  | none => [false]
  | some c => true :: affineWord (aShear c.2 (cut n c.1 f))

def position : Block 9 := .seq (.action (.copy 7 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 3 1))
def loadFactor : Block 11 := .seq (.action (.pop 8)) <|
  .seq (.action (.copy 2 8)) <| .seq (.action (.clear 8)) <|
  .seq (.action (.copy 0 9)) <| .seq (.action (.copy 1 10)) (.action (.clear 4))
def construct : Block 11 := .seq (Frame.block 2 position) <|
  .seq (Frame.block 2 ClauseQuery.reverseLoop) <| .seq loadFactor <|
  .seq (Frame.block 2 SourceChartAffine.block) (.action (.push 8 true))
def dispatch : Block 11 :=
  .branch 4 (.action (.push 8 false)) (.action (.push 8 false)) construct
def block : Block 11 := .seq (Frame.block 2 SourceChartSelection.block) dispatch

def success {n : Nat} (f : Affine (n + 1)) (c : Fin (n + 1) × Point n) : Registers :=
  {SourceChartAffine.finished f c.1 c.2 with output := true :: affineWord (aShear c.2 (cut n c.1 f))}
def chosen {n : Nat} (c : Fin (n + 1) × Point n) : Registers :=
  ⟨[],natural c.1.val,[],[],[true],[],[],[],(SourceEncoding.pointCodec n).encode c.2⟩

theorem construct_exec {n : Nat} (f : Affine (n + 1)) (c : Fin (n + 1) × Point n) :
    Exec construct (full (chosen c) f) (13 * c.1.val + 9 * n + 29) (full (success f c) f) := by
  let positioned := {chosen c with reserved := (SourceEncoding.pointCodec n).encode c.2,output := [],excess := natural c.1.val}
  let reversed := {positioned with excess := [],output := false :: List.replicate c.1.val true}
  have pos : Exec position (chosen c).store 3 positioned.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have rev : Exec ClauseQuery.reverseLoop positioned.store (4 * (c.1.val + 1) + 1) reversed.store := by
    simpa only [positioned,reversed,chosen,natural,List.length_append,
      List.length_replicate,List.length_cons,List.length_nil,List.reverse_append,
      List.reverse_cons,List.reverse_nil,List.reverse_replicate,List.singleton_append,List.append_nil,List.nil_append] using
      ClauseQuery.reverse_exec positioned (natural c.1.val)
  have loaded : Exec loadFactor (full reversed f) 6 (full (SourceChartAffine.ready f c.1 c.2) f) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have transformed := Frame.execution (SourceChartAffine.block_exec f c.1 c.2) (saved f)
  have tagged : Exec (.action (.push (8 : Fin 11) true))
      (full (SourceChartAffine.finished f c.1 c.2) f) 1 (full (success f c) f) := .action _ _
  have cost : 13 * c.1.val + 9 * n + 29 =
      3 + ((4 * (c.1.val + 1) + 1) + (6 + (SourceChartAffine.fuel n c.1.val + 1))) := by
    simp only [SourceChartAffine.fuel]; omega
  simpa only [construct,cost,full] using Exec.seq (Frame.execution pos (saved f))
    (Exec.seq (Frame.execution rev (saved f)) (Exec.seq loaded (Exec.seq transformed tagged)))

theorem chosen_exec {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (h : chooseChart v = some c) :
    Exec block (initial f v) (22 * c.1.val + 9 * n + 39) (full (success f c) f) := by
  have selected := Frame.execution (SourceChartSelection.chosen_exec v c h) (saved f)
  have next : Exec dispatch (full (chosen c) f) (1 + (13 * c.1.val + 9 * n + 29))
      (full (success f c) f) := Exec.one rfl (construct_exec f c)
  have cost : 22 * c.1.val + 9 * n + 39 =
      (9 * c.1.val + 9) + (1 + (13 * c.1.val + 9 * n + 29)) := by omega
  simpa only [block,cost,initial,full,chosen,finCodec] using Exec.seq selected next

theorem absent_exec {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1))
    (h : chooseChart v = none) :
    Exec block (initial f v) (5 * (n + 1) + 6)
      (full {SourceChartSelection.absent (n + 1) with output := [false]} f) := by
  have selected := Frame.execution (SourceChartSelection.absent_exec v h) (saved f)
  have next : Exec dispatch (full (SourceChartSelection.absent (n + 1)) f) 2
      (full {SourceChartSelection.absent (n + 1) with output := [false]} f) :=
    Exec.empty rfl (.action _ _)
  have cost : 5 * (n + 1) + 6 = (5 * (n + 1) + 4) + 2 := by omega
  simpa only [block,cost,initial,full] using Exec.seq selected next

theorem output_get {n : Nat} (r : Registers) (f : Affine (n + 1)) :
    (full r f).get 8 = r.output := Frame.get_core r.store (saved f) 8

theorem block_exec {n : Nat} (f : Affine (n + 1)) (v : Point (n + 1)) :
    ∃ ticks after, Exec block (initial f v) ticks after ∧
      ticks ≤ 31 * n + 39 ∧ after.get 8 = answer f v := by
  cases h : chooseChart v with
  | none =>
    refine ⟨5 * (n + 1) + 6,full {SourceChartSelection.absent (n + 1) with output := [false]} f,
      absent_exec f v h,by omega,?_⟩
    rw [output_get]
    simp only [answer,h]
  | some c =>
    refine ⟨22 * c.1.val + 9 * n + 39,full (success f c) f,chosen_exec f v c h,?_,?_⟩
    · have bound := c.1.isLt
      omega
    · rw [output_get]
      simp only [answer,h,success]

end PNP.Concrete.ResidualReduction.SourceChartApply
