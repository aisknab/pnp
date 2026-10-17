import PNP.Concrete.ResidualReduction.SourceSelectionPacket
import PNP.Concrete.ResidualReduction.SourceSelectionQueryCall

/-! A closed prepared invocation constructs the canonical query packet, clears
the query prefix and executes the selected existing query. Source words and
normal records remain protected. The outer candidate loop and complete
contraction are not implemented by this invocation alone. -/

namespace PNP.Concrete.ResidualReduction.SourceSelectionInvocation
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.NativeNormalization.NativeBitCodec
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.BinaryLinear
open PNP.Concrete.ResidualReduction.MatrixInstructions

structure Data where
  dimension : BitString
  count : BitString
  normals : BitString
  family : BitString
  packet : BitString
  output : BitString
deriving Repr
def Data.store (d : Data) : Store 6 :=
  .cons d.dimension (.cons d.count (.cons d.normals (.cons d.family (.cons d.packet (.cons d.output .nil)))))
def full (r : Store 38) (d : Data) : Store 44 := Frame.join r d.store
def packetFrame (d : Data) : Store 35 := Frame.join (Store.empty 29) d.store
def packetCore (r : Registers) : Store 38 := Frame.join r.store (Store.empty 29)
def ready (d : Data) : Registers := SourceSelectionPacket.ready d.dimension d.count d.normals d.family
def packetResult (d : Data) : Registers := SourceSelectionPacket.result d.dimension d.count d.normals d.family
def word (d : Data) : BitString := SourceSelectionPacket.bytes d.dimension d.count d.normals d.family
def assembled (d : Data) : Data := {d with packet := word d}
def returned (d : Data) (answer : BitString) : Data := {assembled d with output := answer}

def loadWords : Block 44 := .seq (.action (.copy 0 41)) <|
  .seq (.action (.copy 1 38)) <| .seq (.action (.copy 4 40)) (.action (.copy 5 39))
theorem loadWords_exec (d : Data) :
    Exec loadWords (full (Store.empty 38) d) 4 (full (packetCore (ready d)) d) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

def prepare : Block 44 := .seq (Frame.block 6 (SourceSelectionFrame.reset 38)) loadWords
theorem prepare_exec (r : Store 38) (d : Data) :
    Exec prepare (full r d) 43 (full (packetCore (ready d)) d) :=
  Exec.seq (SourceSelectionFrame.reset_framed r d.store) (loadWords_exec d)

def capture : Block 44 := .action (.copy 42 8)
theorem capture_exec (d : Data) :
    Exec capture (full (packetCore (packetResult d)) d) 1
      (full (packetCore (packetResult d)) (assembled d)) := by
  have checked := SourceLinePullback.copy_to_saved (packetCore (packetResult d)) d.store 4 8
  have output : (packetCore (packetResult d)).get 8 = word d := by
    exact SourceSelectionPacket.result_output d.dimension d.count d.normals d.family
  rw [output] at checked
  exact checked

def assemble : Block 44 := .seq prepare <|
  .seq (Frame.block 35 SourceSelectionPacket.block) capture
theorem assemble_exec (r : Store 38) (d : Data) :
    Exec assemble (full r d) (8 * (word d).length + 68)
      (full (packetCore (packetResult d)) (assembled d)) := by
  have first := prepare_exec r d
  have second := Frame.execution
    (SourceSelectionPacket.block_exec d.dimension d.count d.normals d.family) (packetFrame d)
  have last := capture_exec d
  have cost : 8 * (word d).length + 68 =
      43 + (SourceSelectionPacket.fuel d.dimension d.count d.normals d.family + 1) := by
    unfold SourceSelectionPacket.fuel word
    omega
  simpa only [assemble,cost] using Exec.seq first (Exec.seq second last)

def line : Block 44 := .seq assemble (SourceSelectionQueryCall.lineCall 4 5)
def plane : Block 44 := .seq assemble (SourceSelectionQueryCall.planeCall 4 5)

theorem line_exec (r : Store 38) (d : Data) :
    ∃ used after, Exec line (full r d) used
      (full after (returned d (SourceLineInput.answer (word d)))) ∧
      used ≤ SourceLineRaw.sourceBudget (word d).length + 8 * (word d).length + 109 := by
  have first := assemble_exec r d
  obtain ⟨used,after,checked,budget⟩ :=
    SourceSelectionQueryCall.line_call_exec (packetCore (packetResult d)) (assembled d).store 4 5
  refine ⟨(8 * (word d).length + 68) + used,after,Exec.seq first checked,?_⟩
  change used ≤ SourceLineRaw.sourceBudget (word d).length + 41 at budget
  omega

theorem plane_exec (r : Store 38) (d : Data) :
    ∃ used after, Exec plane (full r d) used
      (full after (returned d (SourcePlaneInput.answer (word d)))) ∧
      used ≤ SourcePlaneRaw.sourceBudget (word d).length + 8 * (word d).length + 109 := by
  have first := assemble_exec r d
  obtain ⟨used,after,checked,budget⟩ :=
    SourceSelectionQueryCall.plane_call_exec (packetCore (packetResult d)) (assembled d).store 4 5
  refine ⟨(8 * (word d).length + 68) + used,after,Exec.seq first checked,?_⟩
  change used ≤ SourcePlaneRaw.sourceBudget (word d).length + 41 at budget
  omega

def initial {n : Nat} (F : Family n) (U : System n) (oldPacket oldOutput : BitString) : Data :=
  ⟨natural n,natural U.length,matrixBits U,(SourceEncoding.familyCodec n).encode F,oldPacket,oldOutput⟩
theorem initial_word {n : Nat} (F : Family n) (U : System n) (oldPacket oldOutput : BitString) :
    word (initial F U oldPacket oldOutput) = SourceDirectionEncoding.codec.encode ⟨n,U,F⟩ :=
  SourceSelectionPacket.canonical_bytes F U

theorem line_family_exec {n : Nat} (F : Family n) (a : Affine n)
    (r : Store 38) (oldPacket oldOutput : BitString) :
    ∃ used after, Exec line (full r (initial F [a] oldPacket oldOutput)) used
      (full after (returned (initial F [a] oldPacket oldOutput)
        ((SourceLineOutput.codec n F.length).encode (SourceLine.sourceLineQuery F a)))) ∧
      used ≤ SourceLineRaw.sourceBudget (SourceDirectionEncoding.codec.encode ⟨n,[a],F⟩).length +
        8 * (SourceDirectionEncoding.codec.encode ⟨n,[a],F⟩).length + 109 := by
  have checked := line_exec r (initial F [a] oldPacket oldOutput)
  simpa only [initial_word,SourceLineInput.answer_single] using checked

theorem plane_family_exec {n : Nat} (F : Family n) (a b : Affine n)
    (r : Store 38) (oldPacket oldOutput : BitString) :
    ∃ used after, Exec plane (full r (initial F [a,b] oldPacket oldOutput)) used
      (full after (returned (initial F [a,b] oldPacket oldOutput)
        ((SourceAffineOutput.witnessCodec F.length n).encode (SourcePlane.sourcePlaneQuery F a b)))) ∧
      used ≤ SourcePlaneRaw.sourceBudget (SourceDirectionEncoding.codec.encode ⟨n,[a,b],F⟩).length +
        8 * (SourceDirectionEncoding.codec.encode ⟨n,[a,b],F⟩).length + 109 := by
  have checked := plane_exec r (initial F [a,b] oldPacket oldOutput)
  simpa only [initial_word,SourcePlaneInput.answer_pair] using checked

theorem returned_inputs (d : Data) (answer : BitString) :
    (returned d answer).dimension = d.dimension ∧ (returned d answer).count = d.count ∧
    (returned d answer).normals = d.normals ∧ (returned d answer).family = d.family :=
  ⟨rfl,rfl,rfl,rfl⟩

end PNP.Concrete.ResidualReduction.SourceSelectionInvocation
