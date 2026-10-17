import PNP.Concrete.ResidualReduction.SourceScalarInitialization

/-! Consume one selected-family row. Unselected rows are skipped by counted
reads. Selected rows are loaded, multiplied by the verified literal product
routine and xor-added to the exact accumulator. All scratch is cleared at the
row boundary and the remaining family stream is preserved. -/

namespace PNP.Concrete.ResidualReduction.SourceScalarRow
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding
open PNP.Concrete.ResidualReduction.SourceScalarState

def factor : Block 16 := .seq (.action (.copy 2 13)) <|
  .seq (Frame.block 7 copyLoop) (Frame.block 7 ClauseQuery.reverseLoop)
def factorFuel (n : Nat) : Nat := 9 * n + 12

theorem factor_exec {n : Nat} (f : Affine n) (q : Quadratic n)
    (suffix savedStream hold : BitString) :
    Exec factor (full {work (affineWord f ++ suffix) with reserved := hold} emptySaved (data savedStream q))
      (factorFuel n) (full {work suffix with reserved := hold,output := affineWord f} emptySaved (data savedStream q)) := by
  let metadata := data savedStream q
  let before := {work (affineWord f ++ suffix) with reserved := hold}
  let loaded := {before with remaining := List.replicate (n + 1) true}
  let copied := {work suffix with reserved := hold,excess := (affineWord f).reverse}
  let after := {work suffix with reserved := hold,output := affineWord f}
  have load : Exec (.action (.copy (2 : Fin 16) 13)) (full before emptySaved metadata) 1 (full loaded emptySaved metadata) := .action _ _
  have copy : Exec copyLoop loaded.store (5 * (n + 1) + 1) copied.store := by
    simpa only [loaded,before,copied,work,affineWord_length,List.append_nil] using
      copy_exec {work suffix with reserved := hold} (affineWord f) suffix
  have reverse : Exec ClauseQuery.reverseLoop copied.store (4 * (n + 1) + 1) after.store := by
    simpa only [copied,after,work,affineWord_length,List.length_reverse,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec {work suffix with reserved := hold} (affineWord f).reverse
  have cost : factorFuel n = 1 + ((5 * (n + 1) + 1) + (4 * (n + 1) + 1)) := by
    unfold factorFuel; omega
  simpa only [factor,cost,before,after,metadata] using
    Exec.seq load (Exec.seq (core_exec copy emptySaved metadata) (core_exec reverse emptySaved metadata))

def saveLeft : Block 16 := .seq (.action (.copy 7 8)) (.action (.clear 8))
def prepareProduct : Block 16 := .seq (.action (.copy 11 0)) <|
  .seq (.action (.copy 5 8)) <| .seq (.action (.copy 0 7)) <|
  .seq (.action (.clear 7)) <| .seq (.action (.clear 8)) (.action (.copy 1 12))
def loadFactors : Block 16 := .seq factor <| .seq saveLeft <| .seq factor prepareProduct
def loadFuel (n : Nat) : Nat := 18 * n + 32

theorem load_exec {n : Nat} (f g : Affine n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec loadFactors (full (work (affineWord f ++ (affineWord g ++ suffix))) emptySaved (data savedStream q))
      (loadFuel n)
      (full (SourceQuadraticProduct.ready (work []) f g) emptySaved (data suffix q)) := by
  let metadata := data savedStream q
  let leftDone := {work (affineWord g ++ suffix) with output := affineWord f}
  let rightReady := {work (affineWord g ++ suffix) with reserved := affineWord f}
  let rightDone := {work suffix with reserved := affineWord f,output := affineWord g}
  have left := factor_exec f q (affineWord g ++ suffix) savedStream []
  have save : Exec saveLeft (full leftDone emptySaved metadata) 2 (full rightReady emptySaved metadata) :=
    Exec.seq (.action _ _) (.action _ _)
  have right := factor_exec g q suffix savedStream (affineWord f)
  have prepare : Exec prepareProduct (full rightDone emptySaved metadata) 6
      (full (SourceQuadraticProduct.ready (work []) f g) emptySaved (data suffix q)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))))
  have cost : loadFuel n = factorFuel n + (2 + (factorFuel n + 6)) := by
    simp only [loadFuel,factorFuel]; omega
  simpa only [loadFactors,cost,leftDone,rightReady,rightDone,metadata,work] using
    Exec.seq left (Exec.seq save (Exec.seq right prepare))

def prepareAdd : Block 16 := .seq (.action (.copy 0 15)) <|
  .seq (.action (.copy 5 8)) <| .seq (.action (.copy 2 14)) (.action (.clear 8))
def storeAdd : Block 16 := .seq (.action (.copy 15 8)) <|
  .seq (.action (.clear 8)) <| .seq (.action (.copy 0 11)) <|
  .seq (.action (.clear 9)) (.action (.clear 10))
def accumulate : Block 16 := .seq prepareAdd <| .seq (Frame.block 7 xorLoop) <|
  .seq (Frame.block 7 ClauseQuery.reverseLoop) storeAdd
def addFuel (n : Nat) : Nat := 11 * quadraticBits n + 11

theorem accumulate_exec {n : Nat} (p q : Quadratic n) (saved : SourceQuadraticProduct.Saved)
    (suffix : BitString) :
    Exec accumulate (full {work [] with output := SourceQuadraticEncoding.word p} saved (data suffix q))
      (addFuel n) (state suffix (qAdd q p)) := by
  let metadata := data suffix q
  let before := {work [] with output := SourceQuadraticEncoding.word p}
  let loaded := {work (SourceQuadraticEncoding.word q) with mode := SourceQuadraticEncoding.word p,remaining := List.replicate (quadraticBits n) true}
  let xored := {work [] with excess := (SourceQuadraticEncoding.word (qAdd q p)).reverse}
  let summed := {work [] with output := SourceQuadraticEncoding.word (qAdd q p)}
  have prepare : Exec prepareAdd (full before saved metadata) 4 (full loaded saved metadata) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  have xor : Exec xorLoop loaded.store (7 * quadraticBits n + 1) xored.store := by
    have same : (SourceQuadraticEncoding.word q).length = (SourceQuadraticEncoding.word p).length := by
      rw [SourceQuadraticEncoding.word_length,SourceQuadraticEncoding.word_length]
    simpa only [loaded,xored,work,SourceQuadraticEncoding.word_length,SourceQuadraticEncoding.word_add,List.append_nil] using
      xor_exec (work []) (SourceQuadraticEncoding.word q) (SourceQuadraticEncoding.word p) [] same
  have reverse : Exec ClauseQuery.reverseLoop xored.store (4 * quadraticBits n + 1) summed.store := by
    simpa only [xored,summed,work,List.length_reverse,SourceQuadraticEncoding.word_length,List.reverse_reverse,List.append_nil] using
      ClauseQuery.reverse_exec (work []) (SourceQuadraticEncoding.word (qAdd q p)).reverse
  have save : Exec storeAdd (full summed saved metadata) 5 (state suffix (qAdd q p)) :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _)
      (Exec.seq (.action _ _) (.action _ _))))
  have cost : addFuel n = 4 + ((7 * quadraticBits n + 1) + ((4 * quadraticBits n + 1) + 5)) := by
    unfold addFuel; omega
  simpa only [accumulate,cost,before,metadata] using Exec.seq prepare
    (Exec.seq (core_exec xor saved metadata) (Exec.seq (core_exec reverse saved metadata) save))

def selected : Block 16 := .seq loadFactors <|
  .seq (Frame.block 5 SourceQuadraticProduct.forwardBlock) accumulate
def selectedFuel (n : Nat) : Nat := loadFuel n + (SourceQuadraticProduct.forwardFuel n + addFuel n)

theorem selected_exec {n : Nat} (f g : Affine n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec selected (full (work (affineWord f ++ (affineWord g ++ suffix))) emptySaved (data savedStream q))
      (selectedFuel n) (state suffix (qAdd q (qProduct f g))) := by
  have load := load_exec f g q suffix savedStream
  obtain ⟨after,product⟩ := SourceQuadraticProduct.forward_exec (work []) emptySaved f g
  have add := accumulate_exec (qProduct f g) q after suffix
  exact Exec.seq load (Exec.seq (product_exec product (data suffix q)) add)

def skipRow : Block 16 := .seq (.action (.copy 2 13)) <| .seq (Frame.block 7 dropLoop) <|
  .seq (.action (.copy 2 13)) <| .seq (Frame.block 7 dropLoop) (.action (.copy 11 0))
def skipFuel (n : Nat) : Nat := 6 * n + 11

theorem skip_exec {n : Nat} (f g : Affine n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec skipRow (full (work (affineWord f ++ (affineWord g ++ suffix))) emptySaved (data savedStream q))
      (skipFuel n) (state suffix q) := by
  let metadata := data savedStream q
  let before := work (affineWord f ++ (affineWord g ++ suffix))
  let leftReady := {before with remaining := List.replicate (n + 1) true}
  let leftDone := work (affineWord g ++ suffix)
  let rightReady := {leftDone with remaining := List.replicate (n + 1) true}
  have loadLeft : Exec (.action (.copy (2 : Fin 16) 13)) (full before emptySaved metadata) 1
      (full leftReady emptySaved metadata) := .action _ _
  have left : Exec dropLoop leftReady.store (3 * (n + 1) + 1) leftDone.store := by
    simpa only [leftReady,before,leftDone,work,affineWord_length] using
      drop_exec (work []) (affineWord f) (affineWord g ++ suffix)
  have loadRight : Exec (.action (.copy (2 : Fin 16) 13)) (full leftDone emptySaved metadata) 1
      (full rightReady emptySaved metadata) := .action _ _
  have right : Exec dropLoop rightReady.store (3 * (n + 1) + 1) (work suffix).store := by
    simpa only [rightReady,leftDone,work,affineWord_length] using
      drop_exec (work []) (affineWord g) suffix
  have finish : Exec (.action (.copy (11 : Fin 16) 0)) (full (work suffix) emptySaved metadata) 1 (state suffix q) := .action _ _
  have cost : skipFuel n = 1 + ((3 * (n + 1) + 1) + (1 + ((3 * (n + 1) + 1) + 1))) := by
    unfold skipFuel; omega
  simpa only [skipRow,cost,before,metadata] using Exec.seq loadLeft
    (Exec.seq (core_exec left emptySaved metadata) (Exec.seq loadRight
      (Exec.seq (core_exec right emptySaved metadata) finish)))

def block : Block 16 := .branch 0 .skip
  (.seq (.action (.pop 0)) skipRow) (.seq (.action (.pop 0)) selected)
def fuel (n : Nat) (b : Bool) : Nat := 2 + if b then selectedFuel n else skipFuel n

theorem block_exec {n : Nat} (r : Row n) (q : Quadratic n) (suffix savedStream : BitString) :
    Exec block (full (work (rowWord r ++ suffix)) emptySaved (data savedStream q))
      (fuel n r.selected) (state suffix (SourceScalarState.step q r)) := by
  rcases r with ⟨b,f,g⟩
  have pop : Exec (.action (.pop (0 : Fin 16)))
      (full (work (rowWord (⟨b,f,g⟩ : Row n) ++ suffix)) emptySaved (data savedStream q)) 1
      (full (work (affineWord f ++ (affineWord g ++ suffix))) emptySaved (data savedStream q)) := by
    simp only [rowWord,List.cons_append,List.append_assoc]
    exact .action _ _
  cases b with
  | false =>
    have checked : Exec block
        (full (work (rowWord (⟨false,f,g⟩ : Row n) ++ suffix)) emptySaved (data savedStream q))
        (1 + (1 + skipFuel n)) (state suffix q) :=
      Exec.zero (source := (0 : Fin 16)) rfl (Exec.seq pop (skip_exec f g q suffix savedStream))
    have cost : fuel n false = 1 + (1 + skipFuel n) := by
      simp only [fuel,Bool.false_eq_true,↓reduceIte]; omega
    simpa only [block,cost,SourceScalarState.step,Bool.false_eq_true,↓reduceIte] using checked
  | true =>
    have checked : Exec block
        (full (work (rowWord (⟨true,f,g⟩ : Row n) ++ suffix)) emptySaved (data savedStream q))
        (1 + (1 + selectedFuel n)) (state suffix (qAdd q (qProduct f g))) :=
      Exec.one (source := (0 : Fin 16)) rfl (Exec.seq pop (selected_exec f g q suffix savedStream))
    have cost : fuel n true = 1 + (1 + selectedFuel n) := by
      simp only [fuel,↓reduceIte]; omega
    simpa only [block,cost,SourceScalarState.step,↓reduceIte] using checked

theorem fuel_le_selected (n : Nat) (b : Bool) : fuel n b ≤ fuel n true := by
  cases b with
  | true => exact Nat.le_refl _
  | false =>
    simp only [fuel,selectedFuel,loadFuel,addFuel,skipFuel,Bool.false_eq_true,↓reduceIte]
    omega

theorem selected_fuel (n : Nat) :
    fuel n true = SourceQuadraticProduct.forwardFuel n + 11 * quadraticBits n + 18 * n + 45 := by
  simp only [fuel,selectedFuel,loadFuel,addFuel,↓reduceIte]
  omega

end PNP.Concrete.ResidualReduction.SourceScalarRow
