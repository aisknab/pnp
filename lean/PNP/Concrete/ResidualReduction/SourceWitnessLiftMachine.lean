import PNP.Concrete.ResidualReduction.SourceLineWitnessSearch

/-! Lift both computed parameter vectors through the two saved homogeneous
maps. The first result and the second parameter vector are protected while
the common literal map program runs. No affine offset is added. -/

namespace PNP.Concrete.ResidualReduction.SourceWitnessLift
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceLinePullback (copy_from_saved copy_to_saved clear_core)

def store (r : Registers) (data : Store 29) : Store 38 := Frame.join r.store data
def leftLoaded (r : Registers) (data : Store 29) : Registers :=
  {r with input := data.get 23, target := data.get 24, reserved := data.get 8}
def saveParameter (data : Store 29) (word : BitString) : Store 29 := data.set 10 word
def loadLeft : Block 38 := .seq (.action (.copy 0 32)) <|
  .seq (.action (.copy 1 33)) <| .seq (.action (.copy 7 17)) (.action (.copy 19 8))
theorem loadLeft_exec (r : Registers) (data : Store 29) :
    Exec loadLeft (store r data) 4 (store (leftLoaded r data) (saveParameter data r.output)) := by
  let a := {r with input := data.get 23}
  let b := {a with target := data.get 24}
  have first : Exec (.action (.copy (0 : Fin 38) 32)) (store r data) 1 (store a data) :=
    copy_from_saved r.store data 0 23
  have second : Exec (.action (.copy (1 : Fin 38) 33)) (store a data) 1 (store b data) :=
    copy_from_saved a.store data 1 24
  have third : Exec (.action (.copy (7 : Fin 38) 17)) (store b data) 1 (store (leftLoaded r data) data) :=
    copy_from_saved b.store data 7 8
  have fourth : Exec (.action (.copy (19 : Fin 38) 8)) (store (leftLoaded r data) data) 1
      (store (leftLoaded r data) (saveParameter data r.output)) :=
    copy_to_saved (leftLoaded r data).store data 10 8
  exact Exec.seq first (Exec.seq second (Exec.seq third fourth))

def clearFirst : Block 9 := .seq (.action (.clear 2)) <| .seq (.action (.clear 3)) (.action (.clear 4))
def firstCleared (r : Registers) : Registers := {r with remaining := [], excess := [], sign := []}
theorem clearFirst_exec (r : Registers) :
    Exec clearFirst r.store 3 (firstCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def clearSecond : Block 9 := .seq (.action (.clear 5)) <| .seq (.action (.clear 6)) (.action (.clear 8))
def secondCleared (r : Registers) : Registers := {r with mode := [], active := [], output := []}
theorem clearSecond_exec (r : Registers) :
    Exec clearSecond r.store 3 (secondCleared r).store :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
def clearWork : Block 9 := .seq clearFirst clearSecond
def leftReady (data : Store 29) : Registers :=
  ⟨data.get 23, data.get 24, [], [], [], [], [], data.get 8, []⟩
theorem clearWork_exec (r : Registers) (data : Store 29) :
    Exec clearWork (leftLoaded r data).store 6 (leftReady data).store :=
  Exec.seq (clearFirst_exec (leftLoaded r data)) (clearSecond_exec (firstCleared (leftLoaded r data)))

def prepareLeft : Block 38 := .seq loadLeft (Frame.block 29 clearWork)
theorem prepareLeft_exec (r : Registers) (data : Store 29) :
    Exec prepareLeft (store r data) 10 (store (leftReady data) (saveParameter data r.output)) :=
  Exec.seq (loadLeft_exec r data) (Frame.execution (clearWork_exec r data) (saveParameter data r.output))

def rightLoaded (r : Registers) (data : Store 29) : Registers :=
  {r with input := data.get 25, target := data.get 26, reserved := data.get 10, output := []}
def saveLeft (data : Store 29) (word : BitString) : Store 29 := data.set 11 word
def prepareRight : Block 38 := .seq (.action (.copy 0 34)) <|
  .seq (.action (.copy 1 35)) <| .seq (.action (.copy 7 19)) <|
  .seq (.action (.copy 20 8)) (.action (.clear 8))
theorem prepareRight_exec (r : Registers) (data : Store 29) :
    Exec prepareRight (store r data) 5 (store (rightLoaded r data) (saveLeft data r.output)) := by
  let a := {r with input := data.get 25}
  let b := {a with target := data.get 26}
  let c := {b with reserved := data.get 10}
  have first : Exec (.action (.copy (0 : Fin 38) 34)) (store r data) 1 (store a data) :=
    copy_from_saved r.store data 0 25
  have second : Exec (.action (.copy (1 : Fin 38) 35)) (store a data) 1 (store b data) :=
    copy_from_saved a.store data 1 26
  have third : Exec (.action (.copy (7 : Fin 38) 19)) (store b data) 1 (store c data) :=
    copy_from_saved b.store data 7 10
  have fourth : Exec (.action (.copy (20 : Fin 38) 8)) (store c data) 1 (store c (saveLeft data r.output)) :=
    copy_to_saved c.store data 11 8
  have fifth : Exec (.action (.clear (8 : Fin 38))) (store c (saveLeft data r.output)) 1
      (store (rightLoaded r data) (saveLeft data r.output)) :=
    clear_core c.store (saveLeft data r.output) 8
  exact Exec.seq first (Exec.seq second (Exec.seq third (Exec.seq fourth fifth)))

theorem saved_other (data : Store 29) (destination source : Fin 29) (word : BitString)
    (h : source ≠ destination) : (data.set destination word).get source = data.get source := by
  rw [Store.get_set, if_neg h]
def block : Block 38 := .seq prepareLeft <| .seq (Frame.block 29 SourceLinearMap.block) <|
  .seq prepareRight <| .seq (Frame.block 29 SourceLinearMap.block) (.action (.push 4 true))
def fuel (m n p q : Nat) : Nat :=
  10 + (SourceLinearMap.fuel m p + (5 + (SourceLinearMap.fuel n q + 1)))
def resultCore {n q : Nat} (forms : AffineMap n q) (y : Point q) : Registers :=
  {SourceLinearMap.ready y [] ((SourceEncoding.pointCodec n).encode (linearMapEval forms y)) with sign := [true]}
def resultData {m n p q : Nat} (data : Store 29) (left : AffineMap m p) (_right : AffineMap n q)
    (x : Point p) (y : Point q) : Store 29 :=
  saveLeft (saveParameter data ((SourceEncoding.pointCodec q).encode y))
    ((SourceEncoding.pointCodec m).encode (linearMapEval left x))

theorem block_exec (r : Registers) (data : Store 29) {m n p q : Nat}
    (left : AffineMap m p) (right : AffineMap n q) (x : Point p) (y : Point q)
    (row : data.get 8 = (SourceEncoding.pointCodec p).encode x)
    (column : r.output = (SourceEncoding.pointCodec q).encode y)
    (leftMap : data.get 23 = mapBits left) (leftWidth : data.get 24 = List.replicate p true)
    (rightMap : data.get 25 = mapBits right) (rightWidth : data.get 26 = List.replicate q true) :
    Exec block (store r data) (fuel m n p q)
      (store (resultCore right y) (resultData data left right x y)) := by
  have prepared := prepareLeft_exec r data
  have readyLeft : leftReady data = SourceLinearMap.ready x (mapBits left) [] := by
    simp only [leftReady, row, leftMap, leftWidth, SourceLinearMap.ready, base]
  rw [readyLeft, column] at prepared
  let saved := saveParameter data ((SourceEncoding.pointCodec q).encode y)
  let afterLeft := SourceLinearMap.ready x [] ((SourceEncoding.pointCodec m).encode (linearMapEval left x))
  have first : Exec (Frame.block 29 SourceLinearMap.block)
      (store (SourceLinearMap.ready x (mapBits left) []) saved)
      (SourceLinearMap.fuel m p) (store afterLeft saved) :=
    Frame.execution (SourceLinearMap.block_exec left x) saved
  have prepare := prepareRight_exec afterLeft saved
  have mapWord : saved.get 25 = mapBits right := by
    dsimp only [saved, saveParameter]
    rw [saved_other data 10 25 _ (by decide), rightMap]
  have widthWord : saved.get 26 = List.replicate q true := by
    dsimp only [saved, saveParameter]
    rw [saved_other data 10 26 _ (by decide), rightWidth]
  have pointWord : saved.get 10 = (SourceEncoding.pointCodec q).encode y := Store.get_set_same _ _ _
  have readyRight : rightLoaded afterLeft saved = SourceLinearMap.ready y (mapBits right) [] := by
    simp only [rightLoaded, mapWord, widthWord, pointWord, afterLeft, SourceLinearMap.ready, base]
  rw [readyRight] at prepare
  have second : Exec (Frame.block 29 SourceLinearMap.block)
      (store (SourceLinearMap.ready y (mapBits right) []) (resultData data left right x y))
      (SourceLinearMap.fuel n q)
      (store (SourceLinearMap.ready y [] ((SourceEncoding.pointCodec n).encode (linearMapEval right y)))
        (resultData data left right x y)) :=
    Frame.execution (SourceLinearMap.block_exec right y) (resultData data left right x y)
  have finish : Exec (.action (.push (4 : Fin 38) true))
      (store (SourceLinearMap.ready y [] ((SourceEncoding.pointCodec n).encode (linearMapEval right y)))
        (resultData data left right x y)) 1
      (store (resultCore right y) (resultData data left right x y)) :=
    Frame.execution (Exec.action (.push (4 : Fin 9) true)
      (SourceLinearMap.ready y [] ((SourceEncoding.pointCodec n).encode (linearMapEval right y))).store)
      (resultData data left right x y)
  exact Exec.seq prepared (Exec.seq first (Exec.seq prepare (Exec.seq second finish)))

theorem result_left {m n p q : Nat} (data : Store 29) (left : AffineMap m p) (right : AffineMap n q)
    (x : Point p) (y : Point q) :
    (store (resultCore right y) (resultData data left right x y)).get 20 =
      (SourceEncoding.pointCodec m).encode (linearMapEval left x) :=
  (Frame.get_frame _ _ (11 : Fin 29)).trans (Store.get_set_same _ _ _)
theorem result_right {m n p q : Nat} (data : Store 29) (left : AffineMap m p) (right : AffineMap n q)
    (x : Point p) (y : Point q) :
    (store (resultCore right y) (resultData data left right x y)).get 8 =
      (SourceEncoding.pointCodec n).encode (linearMapEval right y) := Frame.get_core _ _ (8 : Fin 9)
theorem result_present {m n p q : Nat} (data : Store 29) (left : AffineMap m p) (right : AffineMap n q)
    (x : Point p) (y : Point q) :
    (store (resultCore right y) (resultData data left right x y)).get 4 = [true] := Frame.get_core _ _ (4 : Fin 9)

end PNP.Concrete.ResidualReduction.SourceWitnessLift
