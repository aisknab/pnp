import PNP.Concrete.ResidualReduction.SourceMenuCandidates

/-! Extract both coefficient words from an encoded source row. The selected
bit and affine constants are consumed from the source, not replaced by
caller-supplied normals. The remaining stream and existing candidate bytes
are preserved for the enclosing family loop. -/

namespace PNP.Concrete.ResidualReduction.SourceMenuRowInput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.CoefficientComparison
open PNP.Concrete.ResidualReduction.MatrixInstructions

theorem affine_payload {n : Nat} (a : Affine n) :
    affineWord a = normalBits a ++ [aConstant a] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rcases a with ⟨b, a⟩
    change b :: affineWord a = b :: (normalBits a ++ [aConstant a])
    rw [ih a]

def work (n : Nat) (r : Registers) (input output : BitString) : Registers :=
  {r with
    input := input, target := List.replicate n true,
    remaining := [], excess := [], output := output}
def coefficient : Block 9 := .seq (.action (.copy 2 1)) <|
  .seq copyLoop <| .seq (.action (.pop 0)) ClauseQuery.reverseLoop

theorem coefficient_exec (r : Registers) {n : Nat} (a : Affine n) (suffix : BitString) :
    Exec coefficient (work n r (affineWord a ++ suffix) []).store (9 * n + 4)
      (work n r suffix (normalBits a)).store := by
  let seed := work n r suffix []
  have prepare : Exec (.action (.copy (2 : Fin 9) 1))
      (work n r (affineWord a ++ suffix) []).store 1
      ({seed with
        input := normalBits a ++ (aConstant a :: suffix),
        remaining := List.replicate n true}).store := by
    rw [affine_payload, List.append_assoc, List.singleton_append]
    exact Exec.action _ _
  have copied : Exec copyLoop
      ({seed with
        input := normalBits a ++ (aConstant a :: suffix),
        remaining := List.replicate n true}).store (5 * n + 1)
      ({seed with input := aConstant a :: suffix, excess := (normalBits a).reverse}).store := by
    simpa only [normalBits_length, seed, work, List.append_nil] using
      copy_exec seed (normalBits a) (aConstant a :: suffix)
  have popped : Exec (.action (.pop (0 : Fin 9)))
      ({seed with input := aConstant a :: suffix, excess := (normalBits a).reverse}).store 1
      ({seed with excess := (normalBits a).reverse}).store := Exec.action _ _
  have reversed : Exec ClauseQuery.reverseLoop
      ({seed with excess := (normalBits a).reverse}).store (4 * n + 1)
      (work n r suffix (normalBits a)).store := by
    simpa only [seed, work, List.length_reverse, normalBits_length, List.reverse_reverse,
      List.append_nil] using ClauseQuery.reverse_exec seed (normalBits a).reverse
  have checked := Exec.seq prepare (Exec.seq copied (Exec.seq popped reversed))
  have count : 9 * n + 4 = 1 + ((5 * n + 1) + (1 + (4 * n + 1))) := by omega
  simpa only [coefficient, count] using checked

def initial (n : Nat) (input accumulator : BitString) : Registers :=
  ⟨input, List.replicate n true, [], [], [], [], [], accumulator, []⟩
def result {n : Nat} (r : Row n) (suffix accumulator : BitString) : Registers :=
  ⟨suffix, List.replicate n true, [], [], normalBits r.left, [], [], accumulator, normalBits r.right⟩

def saveLeft : Block 9 := .seq (.action (.copy 4 8)) (.action (.clear 8))
theorem saveLeft_exec (r : Registers) :
    Exec saveLeft r.store 2 ({r with sign := r.output, output := []}).store :=
  Exec.seq (.action _ _) (.action _ _)

def block : Block 9 := .seq (.action (.pop 0)) <|
  .seq coefficient <| .seq saveLeft coefficient

theorem row_bytes {n : Nat} (r : Row n) :
    (SourceEncoding.rowCodec n).encode r =
      r.selected :: (affineWord r.left ++ affineWord r.right) := rfl

theorem block_exec {n : Nat} (r : Row n) (suffix accumulator : BitString) :
    Exec block (initial n ((SourceEncoding.rowCodec n).encode r ++ suffix) accumulator).store
      (18 * n + 11) (result r suffix accumulator).store := by
  let base := initial n [] accumulator
  have first : Exec (.action (.pop (0 : Fin 9)))
      (initial n ((SourceEncoding.rowCodec n).encode r ++ suffix) accumulator).store 1
      (work n base (affineWord r.left ++ (affineWord r.right ++ suffix)) []).store := by
    rw [row_bytes, List.cons_append, List.append_assoc]
    exact Exec.action _ _
  have left := coefficient_exec base r.left (affineWord r.right ++ suffix)
  have saved := saveLeft_exec (work n base (affineWord r.right ++ suffix) (normalBits r.left))
  let withLeft := {base with sign := normalBits r.left}
  have right := coefficient_exec withLeft r.right suffix
  have checked := Exec.seq first (Exec.seq left (Exec.seq saved right))
  have count : 18 * n + 11 = 1 + ((9 * n + 4) + (2 + (9 * n + 4))) := by omega
  simpa only [block, count, work, withLeft, base, initial, result] using checked

end PNP.Concrete.ResidualReduction.SourceMenuRowInput
