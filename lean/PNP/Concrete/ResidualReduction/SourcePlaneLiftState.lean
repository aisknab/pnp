import PNP.Concrete.ResidualReduction.SourcePlanePipeline
import PNP.Concrete.ResidualReduction.SourceLinearMapInstructions

/-! The output lift can start with arbitrary scratch registers left by the
verified search. The original source data and computed direction map remain
protected. Splitting the store below is a proof view, not a machine operation. -/

namespace PNP.Concrete.ResidualReduction.SourcePlaneLift
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.MatrixSolutionEncoding
open PNP.Concrete.ResidualReduction.SourcePlanePipeline (Saved)

def view : Store 22 → Registers × Store 13
  | .cons input (.cons target (.cons remaining (.cons excess (.cons sign
      (.cons mode (.cons active (.cons reserved (.cons output tail)))))))) =>
    (⟨input, target, remaining, excess, sign, mode, active, reserved, output⟩, tail)
def frame (tail : Store 13) (data : Saved) : Store 20 := Frame.join tail data.store
def store (r : Registers) (tail : Store 13) (data : Saved) : Store 29 := Frame.join r.store (frame tail data)
theorem view_store (after : Store 22) (data : Saved) :
    store (view after).1 (view after).2 data = SourcePlanePipeline.searchStore after data := by
  match after with
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))))))) => rfl
theorem view_output (after : Store 22) : (view after).1.output = after.get 8 := by
  match after with
  | .cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ (.cons _ _)))))))) => rfl
theorem store_output (r : Registers) (tail : Store 13) (data : Saved) : (store r tail data).get 8 = r.output := rfl

def lift (body : Block 9) : Block 29 := Frame.block 20 body
theorem lift_exec (body : Block 9) (r : Registers) (tail : Store 13) (data : Saved)
    (fuel : Nat) (after : Registers) (checked : Exec body r.store fuel after.store) :
    Exec (lift body) (store r tail data) fuel (store after tail data) := Frame.execution checked (frame tail data)
def copySaved (destination : Fin 9) (source : Fin 7) : Block 29 :=
  .action (.copy (Frame.index 20 destination) (Frame.frameIndex 9 (Frame.frameIndex 13 source)))
theorem copySaved_exec (r : Registers) (tail : Store 13) (data : Saved) (destination : Fin 9) (source : Fin 7) :
    Exec (copySaved destination source) (store r tail data) 1
      (Frame.join (r.store.set destination (data.store.get source)) (frame tail data)) := by
  have checked := Exec.action (.copy (Frame.index 20 destination) (Frame.frameIndex 9 (Frame.frameIndex 13 source)))
    (store r tail data)
  simpa only [copySaved, store, frame, Action.update, Action.instruction, Instruction.update,
    Frame.get_frame, Frame.set_core] using checked

def openWitness : Block 9 := .seq (.action (.copy 0 8)) (.action (.pop 0))
def clearOutput : Block 9 := .seq (.action (.clear 3)) (.action (.clear 8))
def seed : Block 29 := .seq (lift openWitness) (.seq (copySaved 2 5) (lift clearOutput))
def seeded (r : Registers) (data : Saved) : Registers :=
  {r with input := r.output.tail, remaining := data.rows, excess := [], output := []}
theorem seed_exec (r : Registers) (tail : Store 13) (data : Saved) :
    Exec seed (store r tail data) 5 (store (seeded r data) tail data) := by
  let opened := {r with input := r.output.tail}
  let counted := {opened with remaining := data.rows}
  have first : Exec openWitness r.store 2 opened.store := Exec.seq (.action _ _) (.action _ _)
  have second : Exec (copySaved 2 5) (store opened tail data) 1 (store counted tail data) :=
    copySaved_exec opened tail data 2 5
  have third : Exec clearOutput counted.store 2 (seeded r data).store := Exec.seq (.action _ _) (.action _ _)
  exact Exec.seq (lift_exec openWitness r tail data 2 opened first)
    (Exec.seq second (lift_exec clearOutput counted tail data 2 (seeded r data) third))

def copiedWeights (r : Registers) {m k : Nat} (w : Point m) (z : Point k) : Registers :=
  {r with input := (SourceEncoding.pointCodec k).encode z, remaining := [], excess := ((SourceEncoding.pointCodec m).encode w).reverse, output := []}
theorem copyWeights_exec (r : Registers) (tail : Store 13) (data : Saved) {m k : Nat}
    (w : Point m) (z : Point k)
    (output : r.output = (SourceAffineOutput.witnessCodec m k).encode (some (w, z)))
    (rows : data.rows = List.replicate m true) :
    Exec (lift copyLoop) (store (seeded r data) tail data) (5 * m + 1) (store (copiedWeights r w z) tail data) := by
  have bytes : r.output.tail = (SourceEncoding.pointCodec m).encode w ++ (SourceEncoding.pointCodec k).encode z := by
    rw [output]
    rfl
  apply lift_exec
  simpa only [seeded, copiedWeights, bytes, rows, SourceEncoding.point_length, List.append_nil] using
    copy_exec {r with excess := [], output := []} ((SourceEncoding.pointCodec m).encode w) ((SourceEncoding.pointCodec k).encode z)

def retainPair : Block 9 := .seq (.action (.copy 7 0)) <|
  .seq (.action (.copy 8 3)) (.action (.clear 3))
def clearFlags : Block 9 := .seq (.action (.clear 4)) <|
  .seq (.action (.clear 5)) (.action (.clear 6))
def prepare : Block 29 := .seq (lift retainPair) <|
  .seq (copySaved 0 3) <| .seq (copySaved 1 4) (lift clearFlags)
def prepared (r : Registers) (data : Saved) : Registers :=
  {r with input := data.directionMap, target := data.directionWidth, excess := [], sign := [], mode := [], active := [], reserved := r.input, output := r.excess}
theorem prepare_exec (r : Registers) (tail : Store 13) (data : Saved) :
    Exec prepare (store r tail data) 8 (store (prepared r data) tail data) := by
  let retained := {r with reserved := r.input, output := r.excess, excess := []}
  let mapped := {retained with input := data.directionMap}
  let counted := {mapped with target := data.directionWidth}
  have first : Exec retainPair r.store 3 retained.store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  have second : Exec (copySaved 0 3) (store retained tail data) 1 (store mapped tail data) :=
    copySaved_exec retained tail data 0 3
  have third : Exec (copySaved 1 4) (store mapped tail data) 1 (store counted tail data) :=
    copySaved_exec mapped tail data 1 4
  have fourth : Exec clearFlags counted.store 3 (prepared r data).store :=
    Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
  exact Exec.seq (lift_exec retainPair r tail data 3 retained first) <|
    Exec.seq second <| Exec.seq third (lift_exec clearFlags counted tail data 3 (prepared r data) fourth)
theorem prepared_weights {m n k : Nat} (r : Registers) (data : Saved)
    (w : Point m) (z : Point k) (forms : AffineMap n k)
    (map : data.directionMap = mapBits forms) (width : data.directionWidth = List.replicate k true) :
    prepared (copiedWeights r w z) data =
      SourceLinearMap.ready z (mapBits forms) ((SourceEncoding.pointCodec m).encode w).reverse := by
  simp only [prepared, copiedWeights, map, width, SourceLinearMap.ready, base]

end PNP.Concrete.ResidualReduction.SourcePlaneLift
