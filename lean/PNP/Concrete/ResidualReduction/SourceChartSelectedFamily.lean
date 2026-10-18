import PNP.Concrete.ResidualReduction.SourceChartFamily
import PNP.Concrete.ResidualReduction.SourceChartSelection

/-! Discover one chart from the actual direction and use it for the entire
marked source family. No caller-supplied pivot or transformed family is used.
The exact canonical family output and an original-source-size polynomial
instruction bound hold for arbitrary dimensions, families and weight vectors. -/

namespace PNP.Concrete.ResidualReduction.SourceChartSelectedFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceChartStream

def saved {n : Nat} (F : Family (n + 1)) (w : Point F.length) : Saved :=
  ⟨familyBits F,[],[],List.replicate (n + 2) true,(SourceEncoding.pointCodec F.length).encode w,[]⟩
def initial {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1)) : Store 15 :=
  full (SourceChartSelection.ready ((SourceEncoding.pointCodec (n + 1)).encode v)) (saved F w)
def chosen {n : Nat} (c : Fin (n + 1) × Point n) : Registers :=
  ⟨[],natural c.1.val,[],[],[true],[],[],[],(SourceEncoding.pointCodec n).encode c.2⟩
def answer {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1)) : BitString :=
  match chooseChart v with
  | none => [false]
  | some c => true :: (SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w c.1 c.2)
def success {n : Nat} (F : Family (n + 1)) (w : Point F.length) (c : Fin (n + 1) × Point n) : Store 15 :=
  SourceChartFamily.finished c.1 c.2
    (true :: (SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w c.1 c.2))

def position : Block 15 := .seq (.action (.copy 11 8)) <|
  .seq (.action (.clear 8)) (.action (.copy 3 1))
def handoff : Block 15 := .seq (.action (.pop 8)) <|
  .seq (.action (.copy 10 8)) <| .seq (.action (.copy 0 9)) <|
  .seq (.action (.copy 1 12)) <| .seq (.action (.pop 1)) <|
  .seq (.action (.pop 1)) <| .seq (.action (.clear 4)) (.action (.clear 8))
def construct : Block 15 := .seq position <|
  .seq (Frame.block 6 ClauseQuery.reverseLoop) <| .seq handoff <|
  .seq SourceChartFamily.block (.action (.push 8 true))
def dispatch : Block 15 := .branch 4 (.action (.push 8 false)) (.action (.push 8 false)) construct
def block : Block 15 := .seq (Frame.block 6 SourceChartSelection.block) dispatch

theorem construct_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (c : Fin (n + 1) × Point n) :
    Exec construct (full (chosen c) (saved F w))
      (4 * c.1.val + 17 + SourceChartFamily.fuel n c.1.val F.length) (success F w c) := by
  let d := {saved F w with tail := (SourceEncoding.pointCodec n).encode c.2}
  let positioned := {chosen c with output := [],excess := natural c.1.val}
  let reversed := {positioned with excess := [],output := false :: List.replicate c.1.val true}
  have pos : Exec position (full (chosen c) (saved F w)) 3 (full positioned d) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have rev : Exec ClauseQuery.reverseLoop positioned.store (4 * (c.1.val + 1) + 1) reversed.store := by
    simpa only [positioned,reversed,chosen,natural,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.reverse_replicate,List.singleton_append,List.append_nil,List.nil_append] using
      ClauseQuery.reverse_exec positioned (natural c.1.val)
  have loaded : Exec handoff (full reversed d) 8 (SourceChartFamily.rowInitial F w c.1 c.2 []) := by
    simp only [reversed,positioned,chosen,d,saved,SourceChartFamily.rowInitial,data,work,List.replicate_succ]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
        (Exec.seq (.action _ _) (.action _ _)))))))
  have family := SourceChartFamily.block_exec F w c.1 c.2
  have tag : Exec (.action (.push (8 : Fin 15) true))
      (SourceChartFamily.finished c.1 c.2 ((SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w c.1 c.2)))
      1 (success F w c) := .action _ _
  have cost : 4 * c.1.val + 17 + SourceChartFamily.fuel n c.1.val F.length =
      3 + ((4 * (c.1.val + 1) + 1) + (8 + (SourceChartFamily.fuel n c.1.val F.length + 1))) := by omega
  simpa only [construct,cost,full] using Exec.seq pos
    (Exec.seq (Frame.execution rev d.store) (Exec.seq loaded (Exec.seq family tag)))

theorem chosen_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1))
    (c : Fin (n + 1) × Point n) (h : chooseChart v = some c) :
    Exec block (initial F w v)
      (13 * c.1.val + 27 + SourceChartFamily.fuel n c.1.val F.length) (success F w c) := by
  have select := Frame.execution (SourceChartSelection.chosen_exec v c h) (saved F w).store
  have next : Exec dispatch (full (chosen c) (saved F w))
      (1 + (4 * c.1.val + 17 + SourceChartFamily.fuel n c.1.val F.length)) (success F w c) :=
    Exec.one rfl (construct_exec F w c)
  have cost : 13 * c.1.val + 27 + SourceChartFamily.fuel n c.1.val F.length =
      (9 * c.1.val + 9) + (1 + (4 * c.1.val + 17 + SourceChartFamily.fuel n c.1.val F.length)) := by omega
  simpa only [block,cost,initial,full,chosen,finCodec] using Exec.seq select next

theorem absent_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1))
    (h : chooseChart v = none) :
    Exec block (initial F w v) (5 * (n + 1) + 6)
      (full {SourceChartSelection.absent (n + 1) with output := [false]} (saved F w)) := by
  have select := Frame.execution (SourceChartSelection.absent_exec v h) (saved F w).store
  have next : Exec dispatch (full (SourceChartSelection.absent (n + 1)) (saved F w)) 2
      (full {SourceChartSelection.absent (n + 1) with output := [false]} (saved F w)) :=
    Exec.empty rfl (.action _ _)
  have cost : 5 * (n + 1) + 6 = (5 * (n + 1) + 4) + 2 := by omega
  simpa only [block,cost,initial,full] using Exec.seq select next

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (v : Point (n + 1)) :
    let L := (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length
    ∃ ticks after, Exec block (initial F w v) ticks after ∧
      ticks ≤ (70 * L + 159) * L + 40 ∧ after.get 8 = answer F w v := by
  dsimp only
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  cases h : chooseChart v with
  | none =>
    refine ⟨5 * (n + 1) + 6,full {SourceChartSelection.absent (n + 1) with output := [false]} (saved F w),
      absent_exec F w v h,?_,?_⟩
    · simp only [Nat.add_mul,Nat.mul_assoc]
      omega
    · change [false] = answer F w v
      simp only [answer,h]
  | some c =>
    refine ⟨13 * c.1.val + 27 + SourceChartFamily.fuel n c.1.val F.length,success F w c,
      chosen_exec F w v c h,?_,?_⟩
    · have pivot := c.1.isLt
      have family := SourceChartFamily.fuel_source_bound F c.1
      dsimp only at family
      simp only [Nat.add_mul,Nat.mul_assoc] at family ⊢
      omega
    · change true :: (SourceEncoding.familyCodec (n + 1)).encode (SourceChartFamily.result F w c.1 c.2) = answer F w v
      simp only [answer,h]

theorem result_models {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t : Point n) (x : Point (n + 1)) :
    models (SourceChartFamily.result F w k t) x = models F (unchart k t x) := by
  rw [SourceChartFamily.result,chartRows_models,markSource_models]

end PNP.Concrete.ResidualReduction.SourceChartSelectedFamily
