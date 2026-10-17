import PNP.Concrete.ResidualReduction.SourceChartedSuccessorInput

/-! Retain the optional original normal pair by reading its exact coefficient
words. The family packet following it is preserved. Counts come from the parsed
dimension; a normal pair is not supplied as hidden initial register data. -/

namespace PNP.Concrete.ResidualReduction.SourceChartedSuccessorNormals
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceChartedSuccessorState

theorem none_bytes (n : Nat) : (normalsCodec n).encode none = [false] := rfl
theorem some_bytes {n : Nat} (a b : Affine (n + 1)) :
    (normalsCodec n).encode (some (a,b)) = true :: (affineWord a ++ affineWord b) := rfl

def prepareRead : Block 29 := .seq (.action (.copy 2 23)) <|
  .seq (.action (.push 2 true)) (.action (.push 2 true))
def read : Block 29 := .seq prepareRead (core copyLoop)
def readFuel (n : Nat) : Nat := 5 * (n + 2) + 4

theorem read_exec {n : Nat} (a : Affine (n + 1)) (suffix acc : BitString) (s : Saved) :
    Exec read (withCore {SourceScalarState.work (affineWord a ++ suffix) with excess := acc}
      {s with dimension := List.replicate n true}) (readFuel n)
      (withCore {SourceScalarState.work suffix with excess := (affineWord a).reverse ++ acc}
        {s with dimension := List.replicate n true}) := by
  let saved := {s with dimension := List.replicate n true}
  let base := {SourceScalarState.work suffix with excess := acc}
  let loaded := {base with input := affineWord a ++ suffix,remaining := List.replicate (n + 2) true}
  have prepare : Exec prepareRead
      (withCore {SourceScalarState.work (affineWord a ++ suffix) with excess := acc} saved) 3
      (withCore loaded saved) := Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have copy : Exec copyLoop loaded.store (5 * (n + 2) + 1)
      ({SourceScalarState.work suffix with excess := (affineWord a).reverse ++ acc}).store := by
    simpa only [loaded,base,SourceScalarState.work,affineWord_length] using
      copy_exec base (affineWord a) suffix
  have cost : readFuel n = 3 + (5 * (n + 2) + 1) := by unfold readFuel; omega
  simpa only [read,cost,saved] using Exec.seq prepare (core_exec copy saved)

def pair : Block 29 := .seq read <| .seq read (core ClauseQuery.reverseLoop)
def pairFuel (n : Nat) : Nat := 18 * (n + 2) + 9

theorem pair_exec {n : Nat} (a b : Affine (n + 1)) (suffix : BitString) (s : Saved) :
    Exec pair (work (affineWord a ++ (affineWord b ++ suffix)) []
      {s with dimension := List.replicate n true}) (pairFuel n)
      (work suffix (affineWord a ++ affineWord b) {s with dimension := List.replicate n true}) := by
  let saved := {s with dimension := List.replicate n true}
  let reversed := {SourceScalarState.work suffix with excess := (affineWord b).reverse ++ (affineWord a).reverse}
  let emitted := {SourceScalarState.work suffix with output := affineWord a ++ affineWord b}
  have first := read_exec a (affineWord b ++ suffix) [] s
  simp only [List.append_nil] at first
  have second := read_exec b suffix (affineWord a).reverse s
  have reverse : Exec ClauseQuery.reverseLoop reversed.store (8 * (n + 2) + 1) emitted.store := by
    have cost : 8 * (n + 2) + 1 = 4 * ((affineWord a ++ affineWord b).reverse).length + 1 := by
      simp only [List.length_reverse,List.length_append,affineWord_length]
      omega
    rw [cost]
    simpa only [reversed,emitted,SourceScalarState.work,List.reverse_append,List.reverse_reverse,
      List.append_nil] using ClauseQuery.reverse_exec (SourceScalarState.work suffix)
        (affineWord a ++ affineWord b).reverse
  have cost : pairFuel n = readFuel n + (readFuel n + (8 * (n + 2) + 1)) := by
    simp only [pairFuel,readFuel]
    omega
  simpa only [pair,cost,work,SourceScalarState.work,reversed,emitted,saved] using
    Exec.seq first (Exec.seq second (core_exec reverse saved))

def emit : Block 29 := .branch 0 .skip
  (.seq (.action (.pop 0)) (.action (.push 8 false)))
  (.seq (.action (.pop 0)) (.seq pair (.action (.push 8 true))))
def emitFuel (n : Nat) (isPair : Bool) : Nat := if isPair then pairFuel n + 3 else 3

theorem emit_exec {n : Nat} (normals : Option (Affine (n + 1) × Affine (n + 1)))
    (suffix : BitString) (s : Saved) :
    Exec emit (work ((normalsCodec n).encode normals ++ suffix) []
      {s with dimension := List.replicate n true}) (emitFuel n normals.isSome)
      (work suffix ((normalsCodec n).encode normals) {s with dimension := List.replicate n true}) := by
  let saved := {s with dimension := List.replicate n true}
  cases normals with
  | none =>
    have pop : Exec (.action (.pop (0 : Fin 29))) (work (false :: suffix) [] saved) 1
        (work suffix [] saved) := .action _ _
    have tag : Exec (.action (.push (8 : Fin 29) false)) (work suffix [] saved) 1
        (work suffix [false] saved) := .action _ _
    have checked : Exec emit (work (false :: suffix) [] saved) 3 (work suffix [false] saved) :=
      Exec.zero rfl (Exec.seq pop tag)
    simpa only [none_bytes,List.cons_append,List.nil_append,Option.isSome,emitFuel,
      Bool.false_eq_true,↓reduceIte,saved] using checked
  | some p =>
    rcases p with ⟨a,b⟩
    have pop : Exec (.action (.pop (0 : Fin 29)))
        (work (true :: (affineWord a ++ (affineWord b ++ suffix))) [] saved) 1
        (work (affineWord a ++ (affineWord b ++ suffix)) [] saved) := .action _ _
    have tag : Exec (.action (.push (8 : Fin 29) true))
        (work suffix (affineWord a ++ affineWord b) saved) 1
        (work suffix ((normalsCodec n).encode (some (a,b))) saved) := .action _ _
    have checked : Exec emit
        (work (true :: (affineWord a ++ (affineWord b ++ suffix))) [] saved)
        (1 + (1 + (pairFuel n + 1)))
        (work suffix ((normalsCodec n).encode (some (a,b))) saved) :=
      Exec.one rfl (Exec.seq pop (Exec.seq (pair_exec a b suffix s) tag))
    have cost : emitFuel n true = 1 + (1 + (pairFuel n + 1)) := by
      simp only [emitFuel,↓reduceIte]
      omega
    simpa only [some_bytes,List.cons_append,List.append_assoc,Option.isSome,cost,saved] using checked

def save : Block 29 := .seq (.action (.copy 25 8)) (.action (.clear 8))
def block : Block 29 := .seq emit save
def fuel (n : Nat) (isPair : Bool) : Nat := emitFuel n isPair + 2

theorem block_exec {n : Nat} (normals : Option (Affine (n + 1) × Affine (n + 1)))
    (suffix : BitString) (s : Saved) :
    Exec block (work ((normalsCodec n).encode normals ++ suffix) []
      {s with dimension := List.replicate n true}) (fuel n normals.isSome)
      (work suffix [] {s with dimension := List.replicate n true,normals := (normalsCodec n).encode normals}) := by
  have store : Exec save
      (work suffix ((normalsCodec n).encode normals) {s with dimension := List.replicate n true}) 2
      (work suffix [] {s with dimension := List.replicate n true,normals := (normalsCodec n).encode normals}) :=
    Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq (emit_exec normals suffix s) store

theorem fuel_bound (n : Nat) (isPair : Bool) : fuel n isPair ≤ 18 * n + 50 := by
  cases isPair <;> simp only [fuel,emitFuel,pairFuel,Bool.false_eq_true,↓reduceIte] <;> omega

end PNP.Concrete.ResidualReduction.SourceChartedSuccessorNormals
