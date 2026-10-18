import PNP.Concrete.ResidualReduction.SourceChartStream
import PNP.Concrete.ResidualReduction.SourceMatrixEncoding
import PNP.Concrete.ResidualReduction.MatrixSolutionSerialization

/-! Mark and chart every row of an arbitrary source family. Both factors of
every row are read and transformed. The output row-count header is derived
from the actual weight stream, and the complete canonical family encoding is
constructed once. Bounds count literal instructions, not a semantic callback. -/

namespace PNP.Concrete.ResidualReduction.SourceChartFamily
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceBalance
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceChartStream

def mappedRow {n : Nat} (r : Row (n + 1)) (b : Bool) (k : Fin (n + 1)) (t : Point n) : Row (n + 1) :=
  ⟨b,transformed r.left k t,transformed r.right k t⟩
def result {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) : Family (n + 1) :=
  chartRows (markSource F w) k t

theorem result_cons {n : Nat} (r : Row (n + 1)) (F : Family (n + 1)) (b : Bool)
    (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    result (r :: F) (b,w) k t = mappedRow r b k t :: result F w k t := rfl
theorem result_length {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    (result F w k t).length = F.length := by
  simp only [result,chartRows,List.length_map,markSource_length]
theorem output_bytes {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    (SourceEncoding.familyCodec (n + 1)).encode (result F w k t) =
      natural F.length ++ familyBits (result F w k t) := by
  change natural (result F w k t).length ++ encodeSeq (SourceEncoding.rowCodec (n + 1)).encode (result F w k t) = _
  rw [result_length,familyBits_encode]
theorem output_length {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    ((SourceEncoding.familyCodec (n + 1)).encode (result F w k t)).length =
      (2 * n + 6) * F.length + 1 := by
  rw [output_bytes,List.length_append,natural_length,familyBits_length,result_length]
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one]
  omega

def takeWeight : Block 15 := .branch 13 .skip
  (.seq (.action (.pop 13)) (.action (.push 14 false)))
  (.seq (.action (.pop 13)) (.action (.push 14 true)))
def row : Block 15 := .seq takeWeight <| .seq (.action (.pop 0)) <|
  .seq SourceChartStream.block SourceChartStream.block
def rowFuel (n pivot : Nat) : Nat := 44 * n + 18 * pivot + 118

theorem takeWeight_exec {n : Nat} (k : Fin (n + 1)) (t : Point n)
    (input savedStream weights accumulator : BitString) (b : Bool) :
    Exec takeWeight (full (work n input) (data k t savedStream (b :: weights) accumulator)) 3
      (full (work n input) (data k t savedStream weights (b :: accumulator))) := by
  cases b
  · exact Exec.zero rfl (Exec.seq (.action _ _) (.action _ _))
  · exact Exec.one rfl (Exec.seq (.action _ _) (.action _ _))

theorem row_exec {n : Nat} (r : Row (n + 1)) (b : Bool) (k : Fin (n + 1)) (t : Point n)
    (suffix savedStream weights accumulator : BitString) :
    Exec row (full (work n (rowWord r ++ suffix)) (data k t savedStream (b :: weights) accumulator))
      (rowFuel n k.val)
      (full (work n suffix) (data k t suffix weights ((rowWord (mappedRow r b k t)).reverse ++ accumulator))) := by
  have weight := takeWeight_exec k t (rowWord r ++ suffix) savedStream weights accumulator b
  have pop : Exec (.action (.pop (0 : Fin 15)))
      (full (work n (rowWord r ++ suffix)) (data k t savedStream weights (b :: accumulator))) 1
      (full (work n (affineWord r.left ++ (affineWord r.right ++ suffix))) (data k t savedStream weights (b :: accumulator))) := by
    simp only [rowWord,List.cons_append,List.append_assoc]
    exact .action _ _
  have left := SourceChartStream.block_exec r.left k t (affineWord r.right ++ suffix) savedStream weights (b :: accumulator)
  have right := SourceChartStream.block_exec r.right k t suffix (affineWord r.right ++ suffix) weights
    ((affineWord (transformed r.left k t)).reverse ++ b :: accumulator)
  have cost : rowFuel n k.val = 3 + (1 + (SourceChartStream.fuel n k.val + SourceChartStream.fuel n k.val)) := by
    simp only [rowFuel,SourceChartStream.fuel]
    omega
  simpa only [row,cost,rowWord,mappedRow,List.reverse_cons,List.reverse_append,
    List.append_assoc,List.singleton_append] using Exec.seq weight (Exec.seq pop (Exec.seq left right))

def rowInitial {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t : Point n) (accumulator : BitString) : Store 15 :=
  full (work n (familyBits F)) (data k t (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) accumulator)
def terminal {n : Nat} (k : Fin (n + 1)) (t : Point n) (accumulator : BitString) : Store 15 :=
  full (work n []) (data k t [] [] accumulator)
def rowLoop : Block 15 := .loop 0 row

theorem rowLoop_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length)
    (k : Fin (n + 1)) (t : Point n) (accumulator : BitString) :
    Exec rowLoop (rowInitial F w k t accumulator) ((rowFuel n k.val + 1) * F.length + 1)
      (terminal k t ((familyBits (result F w k t)).reverse ++ accumulator)) := by
  induction F generalizing accumulator with
  | nil => cases w; exact Exec.loopStop rfl
  | cons r F ih =>
    rcases w with ⟨b,w⟩
    have head := row_exec r b k t (familyBits F) (familyBits (r :: F))
      ((SourceEncoding.pointCodec F.length).encode w) accumulator
    have rest := ih w ((rowWord (mappedRow r b k t)).reverse ++ accumulator)
    have present : (rowInitial (r :: F) (b,w) k t accumulator).get 0 =
        r.selected :: (affineWord r.left ++ (affineWord r.right ++ familyBits F)) := by
      change rowWord r ++ familyBits F = _
      simp only [rowWord,List.cons_append,List.append_assoc]
    have checked := Exec.loopStep (source := (0 : Fin 15)) present head rest
    have cost : (rowFuel n k.val + 1) * (r :: F).length + 1 =
        1 + (rowFuel n k.val + ((rowFuel n k.val + 1) * F.length + 1)) := by
      simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
    simpa only [rowLoop,cost,result_cons,familyBits,List.reverse_append,List.append_assoc] using checked

private theorem repeat_snoc (n : Nat) (out : BitString) :
    List.replicate n true ++ true :: out = List.replicate (n + 1) true ++ out := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons true) ih

theorem unary_exec (r : Registers) (bits : BitString) :
    Exec MatrixSolutionSerialization.unaryLoop ({r with remaining := bits}).store
      (3 * bits.length + 1) ({r with remaining := [],output := List.replicate bits.length true ++ r.output}).store := by
  induction bits generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons b bits ih =>
    have step : Exec MatrixSolutionSerialization.unaryBody ({r with remaining := b :: bits}).store 2
        ({r with remaining := bits,output := true :: r.output}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl step (ih {r with output := true :: r.output})
    have cost : 3 * (b :: bits).length + 1 = 1 + (2 + (3 * bits.length + 1)) := by
      simp only [List.length_cons]; omega
    rw [cost]
    simpa only [MatrixSolutionSerialization.unaryLoop,List.length_cons,repeat_snoc] using checked

def header : Block 15 := .seq (.action (.copy 2 13)) <|
  .seq (Frame.block 6 MatrixSolutionSerialization.unaryLoop) <|
  .seq (.action (.push 8 false)) <| .seq (.action (.copy 14 8)) (.action (.clear 8))

theorem header_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    Exec header (rowInitial F w k t []) (3 * F.length + 5)
      (rowInitial F w k t (natural F.length).reverse) := by
  let before := work n (familyBits F)
  let d := data k t (familyBits F) ((SourceEncoding.pointCodec F.length).encode w) []
  let loaded := {before with remaining := (SourceEncoding.pointCodec F.length).encode w}
  let scanned := {before with output := List.replicate F.length true}
  have load : Exec (.action (.copy (2 : Fin 15) 13)) (full before d) 1 (full loaded d) := .action _ _
  have scan : Exec MatrixSolutionSerialization.unaryLoop loaded.store (3 * F.length + 1) scanned.store := by
    simpa only [loaded,scanned,before,work,SourceEncoding.point_length,List.append_nil] using
      unary_exec before ((SourceEncoding.pointCodec F.length).encode w)
  have tail : Exec (.seq (.action (.push (8 : Fin 15) false)) (.seq (.action (.copy 14 8)) (.action (.clear 8))))
      (full scanned d) 3 (rowInitial F w k t (natural F.length).reverse) := by
    simp only [natural,List.reverse_append,List.reverse_cons,List.reverse_nil,
      List.reverse_replicate,List.nil_append,List.singleton_append]
    exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have cost : 3 * F.length + 5 = 1 + ((3 * F.length + 1) + 3) := by omega
  simpa only [header,cost,rowInitial,full,before,d] using
    Exec.seq load (Exec.seq (Frame.execution scan d.store) tail)

def finish : Block 15 := .seq (.action (.copy 3 14)) <|
  .seq (Frame.block 6 ClauseQuery.reverseLoop) (.action (.clear 14))
def finished {n : Nat} (k : Fin (n + 1)) (t : Point n) (output : BitString) : Store 15 :=
  full {work n [] with output := output} (data k t [] [] [])

theorem finish_exec {n : Nat} (k : Fin (n + 1)) (t : Point n) (accumulator : BitString) :
    Exec finish (terminal k t accumulator) (4 * accumulator.length + 3)
      (finished k t accumulator.reverse) := by
  let d := data k t [] [] accumulator
  let loaded := {work n [] with excess := accumulator}
  let reversed := {work n [] with output := accumulator.reverse}
  have load : Exec (.action (.copy (3 : Fin 15) 14)) (terminal k t accumulator) 1 (full loaded d) := .action _ _
  have rev : Exec ClauseQuery.reverseLoop loaded.store (4 * accumulator.length + 1) reversed.store := by
    simpa only [loaded,reversed,work,List.append_nil] using ClauseQuery.reverse_exec (work n []) accumulator
  have clear : Exec (.action (.clear (14 : Fin 15))) (full reversed d) 1 (finished k t accumulator.reverse) := .action _ _
  have cost : 4 * accumulator.length + 3 = 1 + ((4 * accumulator.length + 1) + 1) := by omega
  simpa only [finish,cost,full] using Exec.seq load (Exec.seq (Frame.execution rev d.store) clear)

def block : Block 15 := .seq header (.seq rowLoop finish)
def fuel (n pivot rows : Nat) : Nat := (52 * n + 18 * pivot + 146) * rows + 13

theorem block_exec {n : Nat} (F : Family (n + 1)) (w : Point F.length) (k : Fin (n + 1)) (t : Point n) :
    Exec block (rowInitial F w k t []) (fuel n k.val F.length)
      (finished k t ((SourceEncoding.familyCodec (n + 1)).encode (result F w k t))) := by
  have start := header_exec F w k t
  have rows := rowLoop_exec F w k t (natural F.length).reverse
  let acc := (familyBits (result F w k t)).reverse ++ (natural F.length).reverse
  have stop := finish_exec k t acc
  have output : acc.reverse = (SourceEncoding.familyCodec (n + 1)).encode (result F w k t) := by
    rw [output_bytes]
    simp only [acc,List.reverse_append,List.reverse_reverse]
  have size : acc.length = (2 * n + 6) * F.length + 1 := by
    rw [← List.length_reverse,output,output_length]
  have cost : fuel n k.val F.length =
      (3 * F.length + 5) + (((rowFuel n k.val + 1) * F.length + 1) + (4 * acc.length + 3)) := by
    rw [size]
    simp only [fuel,rowFuel,Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.one_mul,Nat.mul_assoc]
    omega
  rw [output] at stop
  simpa only [block,cost,acc] using Exec.seq start (Exec.seq rows stop)

theorem output_get {n : Nat} (k : Fin (n + 1)) (t : Point n) (output : BitString) :
    (finished k t output).get 8 = output := Frame.get_core _ _ 8

theorem fuel_source_bound {n : Nat} (F : Family (n + 1)) (k : Fin (n + 1)) :
    let L := (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length
    fuel n k.val F.length ≤ (70 * L + 146) * L + 13 := by
  dsimp only
  have dimension := SourceMatrixEncoding.dimension_bound (n + 1) F
  have rows := SourceMatrixEncoding.rowCount_bound (n + 1) F
  have pivot := k.isLt
  have coefficient : 52 * n + 18 * k.val + 146 ≤
      70 * (SourceMatrixEncoding.codec.encode ⟨n + 1,F⟩).length + 146 := by omega
  exact Nat.add_le_add_right (Nat.mul_le_mul coefficient rows) 13

end PNP.Concrete.ResidualReduction.SourceChartFamily
