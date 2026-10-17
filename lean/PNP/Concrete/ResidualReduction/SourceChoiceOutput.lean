import PNP.Concrete.ResidualReduction.SourceChoiceLine

/-! Counted serialization of the selector's actual result. The dispatcher tag
chooses only an output conversion; no query is repeated. The line conversion
uses the retained dimension header, not a supplied width or a replacement
witness. All three successful routes share one reversible Choice codec. -/

namespace PNP.Concrete.ResidualReduction.SourceChoiceOutput
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.SourceLine
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)
open PNP.Concrete.ResidualReduction.SourceCandidateLoad (Held)
open PNP.Concrete.ResidualReduction.SourceCandidateSearch (optional)
open PNP.Concrete.ResidualReduction.SourceCandidateQueries (linePayload planePayload)
open PNP.Concrete.ResidualReduction.SourceSelectorState
open PNP.Concrete.ResidualReduction.SourceSelectorResult

def core (r : Registers) : Store 38 := Frame.join r.store (Store.empty 29)
def frame (d : Data) (t : Held) (s : Saved) : Store 39 :=
  Frame.join (Store.empty 29) (dataFrame d t s)
def zero : Registers := ⟨[],[],[],[],[],[],[],[],[]⟩

theorem working_get (r : Store 38) (d : Data) (t : Held) (s : Saved) (i : Fin 38) :
    (full r d t s).get (Frame.index 10 i) = r.get i :=
  (Frame.get_core (SourceCandidateLoad.full r d t) s.store (Frame.index 8 i)).trans
    ((Frame.get_core (SourceSelectionInvocation.full r d) t.store (Frame.index 6 i)).trans
      (Frame.get_core r d.store i))
theorem core_output (r : Registers) (d : Data) (t : Held) (s : Saved) :
    (full (core r) d t s).get 8 = r.output := Frame.get_core r.store (frame d t s) 8
theorem count_get (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    (full r d t s).get 39 = d.count :=
  (Frame.get_core (SourceCandidateLoad.full r d t) s.store (39 : Fin 46)).trans
    ((Frame.get_core (SourceSelectionInvocation.full r d) t.store (39 : Fin 44)).trans
      (Frame.get_frame r d.store 1))
theorem pop_count (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    Exec (.action (.pop 39)) (full r d t s) 1 (full r {d with count := d.count.tail} t s) :=
  Frame.execution (Frame.execution (SourceLinePullback.pop_saved r d.store (1 : Fin 6)) t.store) s.store

def reject : Block 48 := Frame.block 2 (Frame.block 2 (Frame.block 6 SourceLineOutput.reject))
theorem reject_exec (r : Store 38) (d : Data) (t : Held) (s : Saved) :
    ∃ after, Exec reject (full r d t s) 2 after ∧ after.get 8 = [false] := by
  refine ⟨full (SourceLineOutput.rejected r) d t s,
    Frame.execution (Frame.execution (Frame.execution (SourceLineOutput.reject_exec r) d.store) t.store) s.store,?_⟩
  exact (working_get _ _ _ _ 8).trans (SourceLineOutput.rejected_output r)

def affineLoad : Block 48 := .seq (.action (.copy 8 43)) <|
  .seq (.action (.pop 8)) <| .seq (.action (.push 8 false)) (.action (.push 8 true))
def affine : Block 48 := .seq reset affineLoad
theorem affine_exec {n m : Nat} (w : Point m × Point n) (r : Store 38)
    (d : Data) (t : Held) (s : Saved) (answer : d.output = optional planePayload (some w)) :
    ∃ after, Exec affine (full r d t s) 43 after ∧
      after.get 8 = (SourceChoiceEncoding.codec n m).encode (some (SourceWitnessSelection.affineChoice w)) := by
  let result := {zero with output := true :: false :: planePayload w}
  have loaded : Exec affineLoad (full (Store.empty 38) d t s) 4 (full (core result) d t s) := by
    have copied : Exec (.action (.copy (8 : Fin 48) 43)) (full (Store.empty 38) d t s) 1
        (full (core {zero with output := d.output}) d t s) := .action _ _
    rw [answer] at copied
    exact Exec.seq copied (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))
  refine ⟨full (core result) d t s,Exec.seq (reset_exec r d t s) loaded,?_⟩
  rw [core_output,SourceChoiceEncoding.affine_bytes]
  rfl

def planeLoad : Block 48 := .seq (.action (.copy 1 40)) <|
  .seq (.action (.copy 0 43)) (.action (.pop 0))
def tags : Block 9 := .seq (.action (.push 8 true)) (.action (.push 8 true))
def tagged (r : Registers) : Registers := {r with output := true :: true :: r.output}
theorem tags_exec (r : Registers) : Exec tags r.store 2 (tagged r).store :=
  Exec.seq (.action _ _) (.action _ _)

def plane : Block 48 := .seq reset <| .seq planeLoad <|
  .seq (Frame.block 39 SourceSelectionPacket.block) (Frame.block 39 tags)
theorem plane_exec {n m : Nat} (p : Affine n × Affine n) (w : Point m × Point n)
    (r : Store 38) (d : Data) (t : Held) (s : Saved)
    (normals : d.normals = SourcePlaneMenuBytes.pairWord p)
    (answer : d.output = optional planePayload (some w)) :
    ∃ after, Exec plane (full r d t s) (8 * m + 24 * n + 84) after ∧
      after.get 8 = (SourceChoiceEncoding.codec n m).encode (some (SourceWitnessSelection.planeChoice p w)) := by
  let a := SourcePlaneMenuBytes.pairWord p
  let payload := planePayload w
  let result := SourceSelectionPacket.result a [] [] payload
  have loaded : Exec planeLoad (full (Store.empty 38) d t s) 3
      (full (core (SourceSelectionPacket.ready a [] [] payload)) d t s) := by
    have first : Exec (.action (.copy (1 : Fin 48) 40)) (full (Store.empty 38) d t s) 1
        (full (core {zero with target := d.normals}) d t s) := .action _ _
    have second : Exec (.action (.copy (0 : Fin 48) 43))
        (full (core {zero with target := d.normals}) d t s) 1
        (full (core {zero with target := d.normals,input := d.output}) d t s) := .action _ _
    rw [normals] at first second
    rw [answer] at second
    exact Exec.seq first (Exec.seq second (.action _ _))
  have built := Frame.execution (SourceSelectionPacket.block_exec a [] [] payload) (frame d t s)
  have marked := Frame.execution (tags_exec result) (frame d t s)
  have payloadLength : payload.length = m + n := by
    change (((SourceEncoding.pointCodec m).encode w.1) ++ ((SourceEncoding.pointCodec n).encode w.2)).length = _
    simp only [List.length_append,SourceEncoding.point_length]
  have cost : 8 * m + 24 * n + 84 = 39 + (3 + (SourceSelectionPacket.fuel a [] [] payload + 2)) := by
    simp only [SourceSelectionPacket.fuel,SourceSelectionPacket.bytes,a,
      SourcePlaneMenuBytes.pairWord,List.length_append,List.length_nil,affineWord_length,payloadLength]
    omega
  refine ⟨full (core (tagged result)) d t s,?_,?_⟩
  · rw [cost]
    exact Exec.seq (reset_exec r d t s) (Exec.seq loaded (Exec.seq built marked))
  · rw [core_output]
    simp only [tagged,result,SourceSelectionPacket.result_output,SourceSelectionPacket.bytes,
      List.nil_append,SourceChoiceEncoding.plane_bytes]
    change true :: true :: ((affineWord p.1 ++ affineWord p.2) ++
      ((SourceEncoding.pointCodec m).encode w.1 ++ (SourceEncoding.pointCodec n).encode w.2)) = _
    rw [List.append_assoc]

def linePrefix : Block 48 := .seq (.action (.copy 1 40)) (.action (.copy 3 38))
def lineSuffix : Block 48 :=
  .seq (.seq (.action (.copy 6 8)) (.seq (.action (.pop 6)) (.action (.clear 8))))
    (.seq (.action (.copy 3 43)) (.action (.pop 3)))
def lineLoad : Block 48 := .seq linePrefix <| .seq (Frame.block 39 ClauseQuery.reverseLoop) lineSuffix

theorem lineLoad_exec {n m : Nat} (a : Affine n) (w : LineWitness n m)
    (d : Data) (t : Held) (s : Saved)
    (dimension : d.dimension = natural n) (normal : d.normals = affineWord a)
    (answer : d.output = optional linePayload (some w)) :
    Exec lineLoad (full (Store.empty 38) d t s) (4 * n + 12)
      (full (core (SourceChoiceLine.ready n (affineWord a)
        ((SourceEncoding.pointCodec m).encode w.weights) ((SourceEncoding.pointCodec n).encode w.beta)
        ((SourceEncoding.pointCodec n).encode w.direction))) d t s) := by
  let loaded : Registers := {zero with target := affineWord a,excess := natural n}
  let reversed : Registers := {loaded with excess := [],output := (natural n).reverse}
  have first : Exec linePrefix (full (Store.empty 38) d t s) 2 (full (core loaded) d t s) := by
    have one : Exec (.action (.copy (1 : Fin 48) 40)) (full (Store.empty 38) d t s) 1
        (full (core {zero with target := d.normals}) d t s) := .action _ _
    have two : Exec (.action (.copy (3 : Fin 48) 38)) (full (core {zero with target := d.normals}) d t s) 1
        (full (core {zero with target := d.normals,excess := d.dimension}) d t s) := .action _ _
    rw [normal] at one two
    rw [dimension] at two
    exact Exec.seq one two
  have reverse : Exec ClauseQuery.reverseLoop loaded.store (4 * (n + 1) + 1) reversed.store := by
    simpa only [loaded,reversed,zero,natural_length,List.append_nil] using
      ClauseQuery.reverse_exec loaded (natural n)
  have last : Exec lineSuffix (full (core reversed) d t s) 5
      (full (core (SourceChoiceLine.ready n (affineWord a)
        ((SourceEncoding.pointCodec m).encode w.weights) ((SourceEncoding.pointCodec n).encode w.beta)
        ((SourceEncoding.pointCodec n).encode w.direction))) d t s) := by
    have bytes : d.output = true :: (((SourceEncoding.pointCodec m).encode w.weights) ++
        (((SourceEncoding.pointCodec n).encode w.beta) ++ ((SourceEncoding.pointCodec n).encode w.direction))) := by
      rw [answer,SourceCandidateQueries.line_optional,SourceLineOutput.some_bytes]
    have header : (natural n).reverse = false :: List.replicate n true := by
      simp only [natural,List.reverse_append,List.reverse_singleton,List.reverse_replicate,List.singleton_append]
    have moved : Exec (.seq (.action (.copy (6 : Fin 48) 8)) (.seq (.action (.pop 6)) (.action (.clear 8))))
        (full (core reversed) d t s) 3
        (full (core {zero with target := affineWord a,active := List.replicate n true}) d t s) := by
      dsimp only [reversed,loaded]
      rw [header]
      exact Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _))
    have fourth : Exec (.action (.copy (3 : Fin 48) 43))
        (full (core {zero with target := affineWord a,active := List.replicate n true}) d t s) 1
        (full (core {zero with target := affineWord a,active := List.replicate n true,excess := d.output}) d t s) :=
      .action _ _
    rw [bytes] at fourth
    exact Exec.seq moved (Exec.seq fourth (.action _ _))
  have cost : 4 * n + 12 = 2 + ((4 * (n + 1) + 1) + 5) := by omega
  rw [cost]
  exact Exec.seq first (Exec.seq (Frame.execution reverse (frame d t s)) last)

def line : Block 48 := .seq reset <| .seq lineLoad <|
  .seq (Frame.block 39 SourceChoiceLine.block) <|
    .seq (Frame.block 39 SourceSelectionPacket.block) (Frame.block 39 tags)
theorem line_exec {n m : Nat} (a : Affine n) (w : LineWitness n m)
    (r : Store 38) (d : Data) (t : Held) (s : Saved)
    (dimension : d.dimension = natural n) (normal : d.normals = affineWord a)
    (answer : d.output = optional linePayload (some w)) :
    ∃ after, Exec line (full r d t s) (16 * m + 46 * n + 110) after ∧
      after.get 8 = (SourceChoiceEncoding.codec n m).encode (some (SourceWitnessSelection.lineChoice a w)) := by
  let weights := (SourceEncoding.pointCodec m).encode w.weights
  let beta := (SourceEncoding.pointCodec n).encode w.beta
  let direction := (SourceEncoding.pointCodec n).encode w.direction
  let result := SourceSelectionPacket.result (affineWord a) (beta ++ [false]) weights direction
  have loaded := lineLoad_exec a w d t s dimension normal answer
  have reordered := Frame.execution
    (SourceChoiceLine.block_exec n (affineWord a) weights beta direction
      (SourceEncoding.point_length w.beta) (SourceEncoding.point_length w.direction)) (frame d t s)
  have built := Frame.execution (SourceSelectionPacket.block_exec (affineWord a) (beta ++ [false]) weights direction)
    (frame d t s)
  have marked := Frame.execution (tags_exec result) (frame d t s)
  have cost : 16 * m + 46 * n + 110 = 39 + ((4 * n + 12) +
      (SourceChoiceLine.fuel n weights.length +
        (SourceSelectionPacket.fuel (affineWord a) (beta ++ [false]) weights direction + 2))) := by
    simp only [SourceChoiceLine.fuel,SourceSelectionPacket.fuel,SourceSelectionPacket.bytes,
      weights,beta,direction,List.length_append,List.length_cons,List.length_nil,
      affineWord_length,SourceEncoding.point_length]
    omega
  refine ⟨full (core (tagged result)) d t s,?_,?_⟩
  · rw [cost]
    exact Exec.seq (reset_exec r d t s) (Exec.seq loaded (Exec.seq reordered (Exec.seq built marked)))
  · rw [core_output]
    simp only [tagged,result,SourceSelectionPacket.result_output,SourceSelectionPacket.bytes,
      SourceChoiceEncoding.line_bytes,weights,beta,direction,List.append_assoc,List.singleton_append]

def second : Block 48 := .branch 39 reject line plane
def nonAffine : Block 48 := .seq (.action (.pop 39)) second
def present : Block 48 := .branch 39 reject affine nonAffine
def block : Block 48 := .branch 43 reject reject present
def costPolynomial : NatPolynomial := .linear 62 114

theorem block_exec {n : Nat} (F : Family n) (result : Result n F.length)
    (r : Store 38) (d : Data) (t : Held) (s : Saved) (correct : Correct F result d) :
    ∃ used after, Exec block (full r d t s) used after ∧
      after.get 8 = (SourceChoiceEncoding.codec n F.length).encode (choice result) ∧
      used ≤ costPolynomial.eval (SourceMatrixEncoding.codec.encode ⟨n,F⟩).length := by
  have dimension := SourceMatrixEncoding.dimension_bound n F
  have rows := SourceMatrixEncoding.rowCount_bound n F
  cases result with
  | absent =>
    obtain ⟨after,rejected,bytes⟩ := reject_exec r d t s
    refine ⟨3,after,Exec.zero ((output_get r d t s).trans correct.2) rejected,bytes,?_⟩
    simp only [costPolynomial,NatPolynomial.eval_linear]
    omega
  | affine w =>
    obtain ⟨after,encoded,bytes⟩ := affine_exec w r d t s correct.2.2
    refine ⟨45,after,Exec.one ((output_get r d t s).trans correct.2.2)
      (Exec.zero ((count_get r d t s).trans correct.2.1) encoded),bytes,?_⟩
    simp only [costPolynomial,NatPolynomial.eval_linear]
    omega
  | line a w =>
    let popped : Data := {d with count := d.count.tail}
    obtain ⟨after,encoded,bytes⟩ :=
      line_exec a w r popped t s correct.1.1 correct.2.2.1 correct.2.2.2
    have count : popped.count = natural 0 := by change d.count.tail = _; rw [correct.2.1]; rfl
    have first := pop_count r d t s
    refine ⟨16 * F.length + 46 * n + 114,after,?_,bytes,?_⟩
    · have rest : Exec nonAffine (full r d t s) (1 + (1 + (16 * F.length + 46 * n + 110))) after :=
        Exec.seq first (Exec.zero ((count_get r popped t s).trans count) encoded)
      have cost : 16 * F.length + 46 * n + 114 = 1 + (1 + (1 + (1 + (16 * F.length + 46 * n + 110)))) := by omega
      rw [cost]
      exact Exec.one ((output_get r d t s).trans correct.2.2.2)
        (Exec.one ((count_get r d t s).trans correct.2.1) rest)
    · simp only [costPolynomial,NatPolynomial.eval_linear]
      omega
  | plane p w =>
    let popped : Data := {d with count := d.count.tail}
    obtain ⟨after,encoded,bytes⟩ := plane_exec p w r popped t s correct.2.2.1 correct.2.2.2
    have count : popped.count = natural 1 := by change d.count.tail = _; rw [correct.2.1]; rfl
    have first := pop_count r d t s
    refine ⟨8 * F.length + 24 * n + 88,after,?_,bytes,?_⟩
    · have rest : Exec nonAffine (full r d t s) (1 + (1 + (8 * F.length + 24 * n + 84))) after :=
        Exec.seq first (Exec.one ((count_get r popped t s).trans count) encoded)
      have cost : 8 * F.length + 24 * n + 88 = 1 + (1 + (1 + (1 + (8 * F.length + 24 * n + 84)))) := by omega
      rw [cost]
      exact Exec.one ((output_get r d t s).trans correct.2.2.2)
        (Exec.one ((count_get r d t s).trans correct.2.1) rest)
    · simp only [costPolynomial,NatPolynomial.eval_linear]
      omega

end PNP.Concrete.ResidualReduction.SourceChoiceOutput
