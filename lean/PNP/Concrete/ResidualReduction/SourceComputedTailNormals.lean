import PNP.Concrete.ResidualReduction.SourceComputedTailState

/-! Read both original normal words from the stream, delete the selected pivot,
and clear their original constants by literal counted instructions. The stream
suffix and scalar accumulator are preserved; neither derived normal is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceComputedTailNormals
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceClosure
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceScalarState (work data emptySaved Data)
open PNP.Concrete.ResidualReduction.SourceComputedTailState

def wideData {n : Nat} (stream : BitString) (q : Quadratic n) : Data :=
  {data stream q with width := List.replicate (n + 2) true}
def destination (right : Bool) : Fin 19 := if right then 18 else 17
def setNormal (x : Extra) (right : Bool) (word : BitString) : Extra :=
  if right then {x with right := word} else {x with left := word}
def prepare : Block 19 := .seq (.action (.copy 0 8)) <|
  .seq (.action (.copy 1 12)) <| .seq (.action (.copy 2 16)) (.action (.clear 8))
def finish (right : Bool) : Block 19 := .seq (.action (.copy (destination right) 8)) <|
  .seq (.action (.copy 0 11)) <| .seq (.action (.clear 8)) (.action (.clear 1))
def block (right : Bool) : Block 19 := .seq (.action (.copy 2 13)) <|
  .seq (core copyLoop) <| .seq (core ClauseQuery.reverseLoop) <|
  .seq (.action (.copy 11 0)) <| .seq prepare <|
  .seq (core SourceTailNormal.block) (finish right)
def fuel (n pivot : Nat) : Nat := 18 * n + 9 * pivot + 44

theorem block_exec {n : Nat} (f : Affine (n + 1)) (k : Fin (n + 1))
    (q : Quadratic n) (suffix savedStream leftWord rightWord : BitString) (right : Bool) :
    Exec (block right)
      (full (work (affineWord f ++ suffix)) emptySaved (wideData savedStream q) (extras k leftWord rightWord))
      (fuel n k.val)
      (full (work suffix) emptySaved (wideData suffix q)
        (setNormal (extras k leftWord rightWord) right (affineWord (tailNormal k f)))) := by
  let x := extras k leftWord rightWord
  let metadata := wideData savedStream q
  let stored := wideData suffix q
  let before := work (affineWord f ++ suffix)
  let loaded := {before with remaining := List.replicate (n + 2) true}
  let copied := {work suffix with excess := (affineWord f).reverse}
  let reversed := {work suffix with output := affineWord f}
  have load : Exec (.action (.copy (2 : Fin 19) 13))
      (full before emptySaved metadata x) 1 (full loaded emptySaved metadata x) := .action _ _
  have copy : Exec copyLoop loaded.store (5 * (n + 2) + 1) copied.store := by
    simpa only [loaded,before,copied,work,affineWord_length,List.append_nil] using
      copy_exec (work []) (affineWord f) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * (n + 2) + 1) reversed.store := by
    simpa only [copied,reversed,work,affineWord_length,List.length_reverse,
      List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work suffix) (affineWord f).reverse
  have save : Exec (.action (.copy (11 : Fin 19) 0))
      (full reversed emptySaved metadata x) 1 (full reversed emptySaved stored x) := .action _ _
  have prep : Exec prepare (full reversed emptySaved stored x) 4
      (full (SourceTailNormal.ready f k) emptySaved stored x) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have normalize := core_exec (SourceTailNormal.block_exec f k) emptySaved stored x
  have done : Exec (finish right) (full (SourceTailNormal.finished f k) emptySaved stored x) 4
      (full (work suffix) emptySaved stored (setNormal x right (affineWord (tailNormal k f)))) := by
    cases right <;>
      exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have cost : fuel n k.val = 1 + ((5 * (n + 2) + 1) + ((4 * (n + 2) + 1) +
      (1 + (4 + (SourceTailNormal.fuel n k.val + 4))))) := by
    unfold fuel SourceTailNormal.fuel
    omega
  simpa only [block,cost,before,metadata,stored,x] using Exec.seq load
    (Exec.seq (core_exec copy emptySaved metadata x)
      (Exec.seq (core_exec reverse emptySaved metadata x)
        (Exec.seq save (Exec.seq prep (Exec.seq normalize done)))))

def pair : Block 19 := .seq (.action (.push 13 true)) <|
  .seq (block false) <| .seq (block true) (.action (.pop 13))
def pairFuel (n pivot : Nat) : Nat := 2 * fuel n pivot + 2

theorem pair_exec {n : Nat} (a b : Affine (n + 1)) (k : Fin (n + 1))
    (q : Quadratic n) (suffix savedStream leftWord rightWord : BitString) :
    Exec pair
      (full (work (affineWord a ++ (affineWord b ++ suffix))) emptySaved
        (data savedStream q) (extras k leftWord rightWord))
      (pairFuel n k.val)
      (full (work suffix) emptySaved (data suffix q)
        (extras k (affineWord (tailNormal k a)) (affineWord (tailNormal k b)))) := by
  let input := affineWord a ++ (affineWord b ++ suffix)
  let x := extras k leftWord rightWord
  let y := extras k (affineWord (tailNormal k a)) rightWord
  let z := extras k (affineWord (tailNormal k a)) (affineWord (tailNormal k b))
  have widen : Exec (.action (.push (13 : Fin 19) true))
      (full (work input) emptySaved (data savedStream q) x) 1
      (full (work input) emptySaved (wideData savedStream q) x) := .action _ _
  have left : Exec (block false)
      (full (work input) emptySaved (wideData savedStream q) x) (fuel n k.val)
      (full (work (affineWord b ++ suffix)) emptySaved (wideData (affineWord b ++ suffix) q) y) :=
    block_exec a k q (affineWord b ++ suffix) savedStream leftWord rightWord false
  have right : Exec (block true)
      (full (work (affineWord b ++ suffix)) emptySaved (wideData (affineWord b ++ suffix) q) y)
      (fuel n k.val) (full (work suffix) emptySaved (wideData suffix q) z) :=
    block_exec b k q suffix (affineWord b ++ suffix) (affineWord (tailNormal k a)) rightWord true
  have narrow : Exec (.action (.pop (13 : Fin 19)))
      (full (work suffix) emptySaved (wideData suffix q) z) 1
      (full (work suffix) emptySaved (data suffix q) z) := .action _ _
  have cost : pairFuel n k.val = 1 + (fuel n k.val + (fuel n k.val + 1)) := by
    unfold pairFuel
    omega
  simpa only [pair,cost,input,x,y,z] using
    Exec.seq widen (Exec.seq left (Exec.seq right narrow))

theorem pairFuel_bound {n : Nat} (k : Fin (n + 1)) : pairFuel n k.val ≤ 54 * n + 90 := by
  have hk := k.isLt
  unfold pairFuel fuel
  omega

end PNP.Concrete.ResidualReduction.SourceComputedTailNormals
