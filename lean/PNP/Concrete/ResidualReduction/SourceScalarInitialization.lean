import PNP.Concrete.ResidualReduction.SourceScalarState

/-! Construct the zero scalar and its width counter from the dimension.
The triangular allocation is an actual nested instruction loop, and the
width counter is then derived by scanning the produced coefficient word. -/

namespace PNP.Concrete.ResidualReduction.SourceScalarInitialization
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceScalarState

private theorem repeat_snoc (n : Nat) (out : BitString) :
    List.replicate n false ++ false :: out = List.replicate (n + 1) false ++ out := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih
private theorem repeat_append (n m : Nat) :
    List.replicate n false ++ List.replicate m false = List.replicate (n + m) false := by
  induction n with
  | zero => simp only [Nat.zero_add,List.replicate_zero,List.nil_append]
  | succ n ih =>
    simpa only [Nat.succ_add,List.replicate_succ,List.cons_append] using congrArg (List.cons false) ih

def zeroBody : Block 9 := .seq (.action (.push 8 false)) (.action (.pop 2))
def zeroLoop : Block 9 := .loop 2 zeroBody
theorem zero_exec (r : Registers) (bits : BitString) :
    Exec zeroLoop ({r with remaining := bits}).store (3 * bits.length + 1)
      ({r with remaining := [],output := List.replicate bits.length false ++ r.output}).store := by
  induction bits generalizing r with
  | nil => exact Exec.loopStop rfl
  | cons b bits ih =>
    have first : Exec zeroBody ({r with remaining := b :: bits}).store 2
        ({r with remaining := bits,output := false :: r.output}).store :=
      Exec.seq (.action _ _) (.action _ _)
    have checked := Exec.loopStep (source := (2 : Fin 9)) rfl first (ih {r with output := false :: r.output})
    have cost : 3 * (b :: bits).length + 1 = 1 + (2 + (3 * bits.length + 1)) := by
      simp only [List.length_cons]; omega
    rw [cost]
    simpa only [zeroLoop,List.length_cons,repeat_snoc] using checked

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + (n + 1)
theorem triangle_bits (n : Nat) : triangle n + 1 = quadraticBits n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [triangle,quadraticBits,affineBits]
    omega

def outerBody : Block 9 := .seq (.action (.copy 2 1)) <| .seq zeroLoop (.action (.pop 1))
def outerLoop : Block 9 := .loop 1 outerBody
def outerFuel : Nat → Nat
  | 0 => 1
  | n + 1 => 1 + ((3 * (n + 1) + 3) + outerFuel n)

theorem outer_exec (r : Registers) (n : Nat) :
    Exec outerLoop ({r with target := List.replicate n true,remaining := []}).store (outerFuel n)
      ({r with target := [],remaining := [],output := List.replicate (triangle n) false ++ r.output}).store := by
  induction n generalizing r with
  | zero => exact Exec.loopStop rfl
  | succ n ih =>
    let before := {r with target := List.replicate (n + 1) true,remaining := []}
    let loaded := {before with remaining := List.replicate (n + 1) true}
    let added := {before with output := List.replicate (n + 1) false ++ r.output}
    let next := {r with output := List.replicate (n + 1) false ++ r.output}
    have load : Exec (.action (.copy (2 : Fin 9) 1)) before.store 1 loaded.store := .action _ _
    have emit : Exec zeroLoop loaded.store (3 * (n + 1) + 1) added.store := by
      simpa only [loaded,added,before,List.length_replicate] using zero_exec before (List.replicate (n + 1) true)
    have pop : Exec (.action (.pop (1 : Fin 9))) added.store 1
        ({next with target := List.replicate n true,remaining := []}).store := .action _ _
    have body : Exec outerBody before.store (3 * (n + 1) + 3)
        ({next with target := List.replicate n true,remaining := []}).store := by
      have cost : 3 * (n + 1) + 3 = 1 + ((3 * (n + 1) + 1) + 1) := by omega
      simpa only [outerBody,cost] using Exec.seq load (Exec.seq emit pop)
    have checked := Exec.loopStep (source := (1 : Fin 9)) rfl body (ih next)
    have combined : List.replicate (triangle n) false ++ (List.replicate (n + 1) false ++ r.output) =
        List.replicate (triangle (n + 1)) false ++ r.output := by
      rw [← List.append_assoc,repeat_append]
      rfl
    simpa only [outerLoop,outerFuel,before,next,combined] using checked

theorem outerFuel_exact (n : Nat) : outerFuel n = 3 * triangle n + 4 * n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [outerFuel,triangle,ih,Nat.mul_add,Nat.mul_one]
    omega

def setup : Block 16 := .seq (.action (.copy 11 0)) <|
  .seq (.action (.copy 12 1)) <| .seq (.action (.copy 13 1)) (.action (.push 13 true))
def recordZero : Block 16 := .seq (.action (.push 8 false)) (.action (.copy 15 8))
def prepareCount : Block 16 := .seq (.action (.copy 2 8)) (.action (.clear 8))
def storeWidth : Block 16 := .seq (.action (.copy 14 8)) (.action (.clear 8))
def block : Block 16 := .seq setup <| .seq (Frame.block 7 outerLoop) <|
  .seq recordZero <| .seq prepareCount <|
  .seq (Frame.block 7 MatrixSolutionSerialization.unaryLoop) storeWidth
def fuel (n : Nat) : Nat := outerFuel n + 3 * quadraticBits n + 11

theorem block_exec (n : Nat) (input : BitString) :
    Exec block (initial n input) (fuel n) (state input (zero n)) := by
  let before := {work input with target := List.replicate n true}
  let metadata : Data := ⟨input,List.replicate n true,List.replicate (n + 1) true,[],[]⟩
  let allocated := {work input with output := List.replicate (triangle n) false}
  let zeroed := {work input with output := SourceQuadraticEncoding.word (zero n)}
  let stored := {metadata with accumulator := SourceQuadraticEncoding.word (zero n)}
  let counting := {work input with remaining := SourceQuadraticEncoding.word (zero n)}
  let counted := {work input with output := List.replicate (quadraticBits n) true}
  have setupRun : Exec setup (initial n input) 4 (full before emptySaved metadata) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have allocation : Exec outerLoop before.store (outerFuel n) allocated.store := by
    simpa only [before,allocated,work,List.append_nil] using outer_exec (work input) n
  have zeroWord : false :: List.replicate (triangle n) false = SourceQuadraticEncoding.word (zero n) := by
    rw [zero,SourceQuadraticEncoding.word_zero,← triangle_bits,List.replicate_succ]
  have storeZero : Exec recordZero (full allocated emptySaved metadata) 2 (full zeroed emptySaved stored) := by
    have checked : Exec recordZero (full allocated emptySaved metadata) 2
        (full {work input with output := false :: List.replicate (triangle n) false}
          emptySaved {metadata with accumulator := false :: List.replicate (triangle n) false}) :=
      Exec.seq (.action _ _) (.action _ _)
    simpa only [zeroed,stored,zeroWord] using checked
  have loadCount : Exec prepareCount (full zeroed emptySaved stored) 2 (full counting emptySaved stored) :=
    Exec.seq (.action _ _) (.action _ _)
  have count : Exec MatrixSolutionSerialization.unaryLoop counting.store (3 * quadraticBits n + 1) counted.store := by
    simpa only [counting,counted,work,SourceQuadraticEncoding.word_length,List.append_nil] using
      SourceChartFamily.unary_exec (work input) (SourceQuadraticEncoding.word (zero n))
  have saveWidth : Exec storeWidth (full counted emptySaved stored) 2 (state input (zero n)) :=
    Exec.seq (.action _ _) (.action _ _)
  have cost : fuel n = 4 + (outerFuel n + (2 + (2 + ((3 * quadraticBits n + 1) + 2)))) := by
    unfold fuel; omega
  simpa only [block,cost] using Exec.seq setupRun (Exec.seq (core_exec allocation emptySaved metadata)
    (Exec.seq storeZero (Exec.seq loadCount (Exec.seq (core_exec count emptySaved stored) saveWidth))))

theorem fuel_exact (n : Nat) : fuel n = 6 * quadraticBits n + 4 * n + 9 := by
  have width := triangle_bits n
  rw [fuel,outerFuel_exact]
  omega
theorem fuel_bound (n : Nat) : fuel n ≤ 6 * ((n + 1) * (n + 1)) + 4 * n + 9 := by
  have width := SourceQuadraticEncoding.word_bound (zero n)
  rw [SourceQuadraticEncoding.word_length] at width
  rw [fuel_exact]
  omega

end PNP.Concrete.ResidualReduction.SourceScalarInitialization
