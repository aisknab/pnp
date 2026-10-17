import PNP.Concrete.ResidualReduction.SourceChartCoordinates
import PNP.Concrete.ResidualReduction.SourceLinearMapRowInstructions

/-! Literal charting of an arbitrary affine factor. The pivot coefficient is
removed by counted reads, and the new leading coefficient is computed by the
existing literal dot-product loop. No coefficient operation is a machine oracle. -/

namespace PNP.Concrete.ResidualReduction.SourceChartAffine
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions

theorem cut_words {Z : Type} (base : Codec Z) (n : Nat) (k : Fin (n + 1))
    (x : Tuple Z (n + 1)) :
    ∃ front suffix : BitString, front.length = k.val ∧
      (SourceEncoding.tupleCodec base (n + 1)).encode x =
        front ++ (cut n k x).1 :: suffix ∧
      (SourceEncoding.tupleCodec base n).encode (cut n k x).2 = front ++ suffix := by
  induction n with
  | zero =>
    have hk : k = 0 := Fin.ext (by omega)
    subst k
    rcases x with ⟨b,z⟩
    exact ⟨[],base.encode z,rfl,rfl,rfl⟩
  | succ n ih =>
    by_cases hz : k.val = 0
    · have hk : k = 0 := Fin.ext hz
      subst k
      rcases x with ⟨b,x⟩
      refine ⟨[],(SourceEncoding.tupleCodec base (n + 1)).encode x,rfl,?_,?_⟩
      · rw [cut_zero]; rfl
      · rw [cut_zero]; rfl
    · let j : Fin (n + 1) := ⟨k.val - 1,by omega⟩
      have hk : j.succ = k := Fin.ext (by simp only [Fin.val_succ,j]; omega)
      rw [← hk]
      rcases x with ⟨b,x⟩
      obtain ⟨front,suffix,width,whole,tail⟩ := ih j x
      refine ⟨b :: front,suffix,?_,?_,?_⟩
      · simp only [List.length_cons,width,Fin.val_succ]
      · rw [cut_succ]
        change b :: (SourceEncoding.tupleCodec base (n + 1)).encode x =
          b :: (front ++ (cut n j x).1 :: suffix)
        exact congrArg (List.cons b) whole
      · rw [cut_succ]
        change b :: (SourceEncoding.tupleCodec base n).encode (cut n j x).2 =
          b :: (front ++ suffix)
        exact congrArg (List.cons b) tail

def readPivot : Block 9 :=
  MatrixLinearCombinationInstructions.readInput fun b => .action (.push 4 b)
def cutBlock : Block 9 := .seq copyLoop <| .seq readPivot <|
  .seq (.action (.copy 8 0)) ClauseQuery.reverseLoop

theorem readPivot_exec (r : Registers) (bit : Bool) :
    Exec readPivot ({r with input := bit :: r.input}).store 3
      ({r with sign := bit :: r.sign}).store :=
  MatrixLinearCombinationInstructions.readInput_exec r bit _ 1 _ (.action _ _)

theorem cut_exec (r : Registers) (front suffix : BitString) (bit : Bool) :
    Exec cutBlock
      ({r with input := front ++ bit :: suffix,remaining := List.replicate front.length true,excess := [],sign := []}).store
      (9 * front.length + 6)
      ({r with input := suffix,remaining := [],excess := [],sign := [bit],output := front ++ suffix}).store := by
  let before := {r with input := front ++ bit :: suffix,remaining := List.replicate front.length true,excess := [],sign := []}
  let copied := {r with input := bit :: suffix,remaining := [],excess := front.reverse,sign := []}
  let pivotRead := {r with input := suffix,remaining := [],excess := front.reverse,sign := [bit]}
  let reversed := {pivotRead with output := suffix}
  have first : Exec copyLoop before.store (5 * front.length + 1) copied.store := by
    simpa only [before,copied,List.append_nil] using copy_exec {r with excess := [],sign := []} front (bit :: suffix)
  have second : Exec readPivot copied.store 3 pivotRead.store :=
    readPivot_exec {r with input := suffix,remaining := [],excess := front.reverse,sign := []} bit
  have third : Exec (.action (.copy (8 : Fin 9) 0)) pivotRead.store 1 reversed.store := .action _ _
  have last : Exec ClauseQuery.reverseLoop reversed.store (4 * front.length + 1)
      ({r with input := suffix,remaining := [],excess := [],sign := [bit],output := front ++ suffix}).store := by
    simpa only [reversed,pivotRead,List.length_reverse,List.reverse_reverse] using
      ClauseQuery.reverse_exec reversed front.reverse
  have cost : 9 * front.length + 6 = (5 * front.length + 1) + (3 + (1 + (4 * front.length + 1))) := by omega
  simpa only [cutBlock,before,cost] using Exec.seq first (Exec.seq second (Exec.seq third last))

def ready {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) : Registers :=
  ⟨affineWord f,List.replicate n true,List.replicate k.val true,[],[],[],[],
    (SourceEncoding.pointCodec n).encode t,[]⟩
def finished {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) : Registers :=
  ⟨[],List.replicate n true,[],[],[],[],[],
    (SourceEncoding.pointCodec n).encode t,affineWord (aShear t (cut n k f))⟩
def prepareDot : Block 9 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 2 1)) (.action (.copy 5 7))
def block : Block 9 := .seq cutBlock <| .seq prepareDot <|
  .seq SourceLinearMap.dotLoop SourceLinearMap.rowFinish
def fuel (n pivot : Nat) : Nat := 9 * pivot + 9 * n + 14

theorem block_exec {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1)) (t : Point n) :
    Exec block (ready f k t).store (fuel n k.val) (finished f k t).store := by
  obtain ⟨front,suffix,width,whole,tail⟩ := cut_words bitCodec n k f
  let part := cut n k f
  let cutDone := {ready f k t with input := suffix,remaining := [],sign := [part.1],output := affineWord part.2}
  have first : Exec cutBlock (ready f k t).store (9 * k.val + 6) cutDone.store := by
    have checked := cut_exec (ready f k t) front suffix part.1
    simpa only [ready,cutDone,affineWord,SourceEncoding.affineCodec,whole,tail,width,part] using checked
  let dotReady := {cutDone with input := affineWord part.2,remaining := List.replicate n true,mode := (SourceEncoding.pointCodec n).encode t}
  let dotDone := {cutDone with input := [aConstant part.2],mode := [],sign := [Bool.xor (SourceLinearMap.value part.2 t) part.1]}
  have second : Exec prepareDot cutDone.store 3 dotReady.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have third : Exec SourceLinearMap.dotLoop dotReady.store (9 * n + 1) dotDone.store := by
    simpa only [dotReady,dotDone,cutDone,List.append_nil] using
      SourceLinearMap.dotLoop_exec cutDone part.2 t part.1 []
  have head : Bool.xor (SourceLinearMap.value part.2 t) part.1 = (aShear t part).1 :=
    Bool.xor_comm _ _
  have last : Exec SourceLinearMap.rowFinish dotDone.store 4 (finished f k t).store := by
    have checked := SourceLinearMap.rowFinish_exec
      {cutDone with input := [],mode := [],sign := []}
      (aConstant part.2) (Bool.xor (SourceLinearMap.value part.2 t) part.1)
    simpa only [head,finished,dotDone,cutDone,ready,part,affineWord_cons,aShear] using checked
  have cost : fuel n k.val = (9 * k.val + 6) + (3 + ((9 * n + 1) + 4)) := by
    simp only [fuel]; omega
  simpa only [block,cost] using Exec.seq first (Exec.seq second (Exec.seq third last))

theorem fuel_bound {n : Nat} (k : Fin (n + 1)) : fuel n k.val ≤ 18 * n + 14 := by
  have h := k.isLt
  simp only [fuel]
  omega

end PNP.Concrete.ResidualReduction.SourceChartAffine
