import PNP.Concrete.ResidualReduction.SourceNativeCoordinate

/-! One fixed literal sparse-label reader and checked dense-coordinate builder.
Register 9 protects the actual unary dimension while the nine-register workspace
reads the label and constructs the affine word. No coordinate object or success
certificate is supplied to the program. The surrounding system parser is still
responsible for deriving the protected dimension from its input header. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeLabel
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization

def full (r : Registers) (dimension : BitString) : Store 10 :=
  Frame.join r.store (.cons dimension .nil)
def lift (b : Block 9) : Block 10 := Frame.block 1 b
theorem lift_exec {b : Block 9} {before after : Registers} {ticks : Nat}
    (checked : Exec b before.store ticks after.store) (dimension : BitString) :
    Exec (lift b) (full before dimension) ticks (full after dimension) :=
  Frame.execution checked (.cons dimension .nil)

def initial (input : BitString) (n : Nat) : Store 10 :=
  full (SourceNativeRowIndex.state input 0 false) (List.replicate n true)
def expand : Block 10 :=
  .seq (.action (.copy 2 9)) (lift SourceNativeCoordinate.block)
theorem expand_exec (input : BitString) (n j : Nat) :
    Exec expand (full (SourceNativeRowIndex.state input j true) (List.replicate n true))
      (1 + SourceNativeCoordinate.fuel n j)
      (full (SourceNativeCoordinate.result input n j) (List.replicate n true)) := by
  have first : Exec (.action (.copy (2 : Fin 10) 9))
      (full (SourceNativeRowIndex.state input j true) (List.replicate n true)) 1
      (full (SourceNativeCoordinate.initial input n j) (List.replicate n true)) := .action _ _
  exact Exec.seq first (lift_exec (SourceNativeCoordinate.block_exec input n j) (List.replicate n true))

def dispatch : Block 10 := .branch 4 .skip expand expand
def block : Block 10 := .seq (lift SourceNativeRowIndex.block) dispatch
def fuel (input : BitString) (n : Nat) : Nat :=
  SourceNativeRowIndex.fuel input +
    (if (SourceNativeRowIndex.parse input).valid then
      2 + SourceNativeCoordinate.fuel n (SourceNativeRowIndex.parse input).index else 2)
def result (input : BitString) (n : Nat) : Store 10 :=
  let p := SourceNativeRowIndex.parse input
  if p.valid then full (SourceNativeCoordinate.result p.rest n p.index) (List.replicate n true)
  else full (SourceNativeRowIndex.state p.rest p.index false) (List.replicate n true)

theorem block_exec (input : BitString) (n : Nat) :
    Exec block (initial input n) (fuel input n) (result input n) := by
  have first := lift_exec (SourceNativeRowIndex.block_exec input) (List.replicate n true)
  cases flag : (SourceNativeRowIndex.parse input).valid with
  | false =>
    have last : Exec dispatch
        (full (SourceNativeRowIndex.state (SourceNativeRowIndex.parse input).rest
          (SourceNativeRowIndex.parse input).index false) (List.replicate n true)) 2
        (full (SourceNativeRowIndex.state (SourceNativeRowIndex.parse input).rest
          (SourceNativeRowIndex.parse input).index false) (List.replicate n true)) :=
      Exec.empty rfl (Exec.skip _)
    rw [flag] at first
    simpa only [block,initial,fuel,result,flag,Bool.false_eq_true,↓reduceIte] using Exec.seq first last
  | true =>
    have last : Exec dispatch
        (full (SourceNativeRowIndex.state (SourceNativeRowIndex.parse input).rest
          (SourceNativeRowIndex.parse input).index true) (List.replicate n true))
        (1 + (1 + SourceNativeCoordinate.fuel n (SourceNativeRowIndex.parse input).index))
        (full (SourceNativeCoordinate.result (SourceNativeRowIndex.parse input).rest n
          (SourceNativeRowIndex.parse input).index) (List.replicate n true)) :=
      Exec.one rfl (expand_exec (SourceNativeRowIndex.parse input).rest n
        (SourceNativeRowIndex.parse input).index)
    rw [flag] at first
    simpa only [block,initial,fuel,result,flag,↓reduceIte,← Nat.add_assoc] using Exec.seq first last

theorem fuel_bound (input : BitString) (n : Nat) :
    fuel input n ≤ 15 * input.length + 3 * n + 31 := by
  have reader := SourceNativeRowIndex.fuel_bound input
  have indexBound := (SourceNativeRowIndex.parse_bounds input).2.1
  have coordinate := SourceNativeCoordinate.fuel_bound n (SourceNativeRowIndex.parse input).index
  unfold fuel
  split <;> omega

theorem canonical_exec {c : Nat} (r : NativeEquations.Row c) (suffix : BitString) :
    Exec block (initial ((NativeSystemCodec.rowCodec c).encode r ++ suffix) (2 * c))
      (fuel ((NativeSystemCodec.rowCodec c).encode r ++ suffix) (2 * c))
      (full ({SourceNativeRowIndex.state suffix 0 true with
        output := (SourceNativeEncoding.affineWord
          (NativeSource.coordinateForm (2 * c) (NativeSource.rowIndex r))).reverse})
        (List.replicate (2 * c) true)) := by
  have checked := block_exec ((NativeSystemCodec.rowCodec c).encode r ++ suffix) (2 * c)
  simpa only [result,SourceNativeRowIndex.canonical,↓reduceIte,SourceNativeCoordinate.result,
    (NativeSource.rowIndex r).isLt,SourceNativeCoordinate.passed,
    SourceNativeEncoding.coordinate_word,SourceUnitDirectionInstructions.unit_bytes] using checked

theorem canonical_fuel_bound {c : Nat} (r : NativeEquations.Row c) (suffix : BitString) :
    fuel ((NativeSystemCodec.rowCodec c).encode r ++ suffix) (2 * c) ≤
      7 * (((NativeSystemCodec.rowCodec c).encode r ++ suffix).length) + 8 * c + 23 := by
  have reader := SourceNativeRowIndex.fuel_bound ((NativeSystemCodec.rowCodec c).encode r ++ suffix)
  have coordinate := SourceNativeCoordinate.valid_fuel_bound (2 * c) (NativeSource.rowIndex r)
  simp only [fuel,SourceNativeRowIndex.canonical,↓reduceIte]
  omega

end PNP.Concrete.ResidualReduction.SourceNativeLabel
