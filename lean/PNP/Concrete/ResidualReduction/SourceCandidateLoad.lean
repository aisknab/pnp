import PNP.Concrete.ResidualReduction.SourceSelectionInvocation

/-! A counted complete-record loader for the ordered candidate search. The
pending stream and unary record width live outside the query prefix. Loading
clears scratch, reads the entire record and preserves the original source. -/

namespace PNP.Concrete.ResidualReduction.SourceCandidateLoad
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.MatrixInstructions
open PNP.Concrete.ResidualReduction.SourceSelectionInvocation (Data)

structure Held where
  pending : BitString
  width : BitString
deriving Repr
def Held.store (t : Held) : Store 2 := .cons t.pending (.cons t.width .nil)
def full (r : Store 38) (d : Data) (t : Held) : Store 46 :=
  Frame.join (SourceSelectionInvocation.full r d) t.store
def saved (d : Data) (t : Held) : Store 8 := Frame.join d.store t.store
def frame (d : Data) (t : Held) : Store 37 :=
  Frame.join (Store.empty 29) (saved d t)
def core (r : Registers) : Store 38 := Frame.join r.store (Store.empty 29)
def ready (front suffix : BitString) : Registers :=
  ⟨front ++ suffix, [], List.replicate front.length true, [], [], [], [], [], []⟩
def loaded (front suffix : BitString) : Registers :=
  ⟨suffix, [], [], [], [], [], [], [], front⟩

def loadWords : Block 46 := .seq (.action (.copy 0 44)) (.action (.copy 2 45))
theorem loadWords_exec (d : Data) (front suffix : BitString) :
    Exec loadWords (full (Store.empty 38) d ⟨front ++ suffix, List.replicate front.length true⟩) 2
      (full (core (ready front suffix)) d ⟨front ++ suffix, List.replicate front.length true⟩) :=
  Exec.seq (.action _ _) (.action _ _)

def prepare : Block 46 :=
  .seq (Frame.block 2 (Frame.block 6 (SourceSelectionFrame.reset 38))) loadWords
theorem prepare_exec (r : Store 38) (d : Data) (front suffix : BitString) :
    Exec prepare (full r d ⟨front ++ suffix, List.replicate front.length true⟩) 41
      (full (core (ready front suffix)) d ⟨front ++ suffix, List.replicate front.length true⟩) :=
  Exec.seq (Frame.execution (SourceSelectionFrame.reset_framed r d.store)
    (Held.store ⟨front ++ suffix, List.replicate front.length true⟩)) (loadWords_exec d front suffix)

def readRecord : Block 9 := .seq copyLoop ClauseQuery.reverseLoop
theorem readRecord_exec (front suffix : BitString) :
    Exec readRecord (ready front suffix).store (9 * front.length + 2) (loaded front suffix).store := by
  let seed : Registers := ⟨suffix, [], [], [], [], [], [], [], []⟩
  have first : Exec copyLoop (ready front suffix).store (5 * front.length + 1)
      ({seed with excess := front.reverse}).store := by
    simpa only [ready, seed, List.append_nil] using copy_exec seed front suffix
  have second : Exec ClauseQuery.reverseLoop ({seed with excess := front.reverse}).store
      (4 * front.length + 1) (loaded front suffix).store := by
    simpa only [loaded, seed, List.length_reverse, List.reverse_reverse, List.append_nil] using
      ClauseQuery.reverse_exec seed front.reverse
  have count : 9 * front.length + 2 = (5 * front.length + 1) + (4 * front.length + 1) := by omega
  simpa only [readRecord, ready, loaded, seed, List.append_nil, List.length_reverse,
    List.reverse_reverse, count] using Exec.seq first second

def capture : Block 46 := .seq (.action (.copy 40 8)) (.action (.copy 44 0))
theorem capture_exec (d : Data) (front suffix width : BitString) :
    Exec capture (full (core (loaded front suffix)) d ⟨front ++ suffix, width⟩) 2
      (full (core (loaded front suffix)) {d with normals := front} ⟨suffix, width⟩) :=
  Exec.seq (.action _ _) (.action _ _)

def block : Block 46 :=
  .seq prepare <| .seq (Frame.block 37 readRecord) capture
def fuel (width : Nat) : Nat := 9 * width + 45

theorem block_exec (r : Store 38) (d : Data) (front suffix : BitString) :
    Exec block (full r d ⟨front ++ suffix, List.replicate front.length true⟩) (fuel front.length)
      (full (core (loaded front suffix)) {d with normals := front}
        ⟨suffix, List.replicate front.length true⟩) := by
  have first := prepare_exec r d front suffix
  have second := Frame.execution (readRecord_exec front suffix)
    (frame d ⟨front ++ suffix, List.replicate front.length true⟩)
  have last := capture_exec d front suffix (List.replicate front.length true)
  have count : fuel front.length = 41 + ((9 * front.length + 2) + 2) := by unfold fuel; omega
  simpa only [block, count] using Exec.seq first (Exec.seq second last)

theorem preserved_source (d : Data) (front : BitString) :
    ({d with normals := front} : Data).dimension = d.dimension ∧
    ({d with normals := front} : Data).count = d.count ∧
    ({d with normals := front} : Data).family = d.family ∧
    ({d with normals := front} : Data).packet = d.packet ∧
    ({d with normals := front} : Data).output = d.output := ⟨rfl,rfl,rfl,rfl,rfl⟩

end PNP.Concrete.ResidualReduction.SourceCandidateLoad
