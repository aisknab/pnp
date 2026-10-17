import PNP.Concrete.ResidualReduction.SourceReplayRecordFields
import PNP.Concrete.ResidualReduction.SourceChartedSuccessorWords

/-! Protected frame for literal record parsing. Saved fields and cumulative
validity survive workspace resets. The last register is temporary cursor
storage; every completed phase clears it. No parsed record is supplied. -/

namespace PNP.Concrete.ResidualReduction.SourceReplayRecordState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.SourceMatrixPacket

structure Saved where
  dimension : BitString
  rows : BitString
  source : BitString
  weights : BitString
  pivot : BitString
  tail : BitString
  outputRows : BitString
  output : BitString
  valid : BitString
def Saved.store (s : Saved) : Store 9 :=
  .cons s.dimension (.cons s.rows (.cons s.source (.cons s.weights (.cons s.pivot
    (.cons s.tail (.cons s.outputRows (.cons s.output (.cons s.valid .nil))))))))
def emptySaved : Saved := ⟨[],[],[],[],[],[],[],[],[]⟩
def full (r : State) (s : Saved) (backup : BitString := []) : Store 26 :=
  Frame.join r.store (Frame.join s.store (.cons backup .nil))
def blank (input : BitString) : State := SourceReplayFamily.initial 0 input
def work (input : BitString) (s : Saved) : Store 26 := full (blank input) s
def initial (input : BitString) : Store 26 := work input emptySaved
def wide (b : Block 16) : Block 26 := Frame.block 10 b
def core (b : Block 9) : Block 26 := wide (lift9 b)

theorem wide_exec {b : Block 16} {before after : State} {used : Nat}
    (h : Exec b before.store used after.store) (s : Saved) (backup : BitString := []) :
    Exec (wide b) (full before s backup) used (full after s backup) :=
  Frame.execution h (Frame.join s.store (.cons backup .nil))
theorem core_exec {b : Block 9} (r : State) {after : Registers} {used : Nat}
    (h : Exec b r.core.core.core.store used after.store) (s : Saved) (backup : BitString := []) :
    Exec (core b) (full r s backup) used (full (setCore r after) s backup) :=
  wide_exec (lift9_exec b r used after h) s backup

def clearWork : Block 26 := wide (SourceChartedSuccessorWords.clearAll 16)
theorem clearWork_exec (r : State) (s : Saved) (backup : BitString := []) :
    Exec clearWork (full r s backup) 17 (full (blank []) s backup) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r.store)
    (Frame.join s.store (.cons backup .nil))
def reset : Block 26 := .seq (.action (.copy 25 0)) <| .seq clearWork <|
  .seq (.action (.copy 0 25)) (.action (.clear 25))
theorem reset_exec (r : State) (s : Saved) :
    Exec reset (full r s) 20 (work r.core.core.core.input s) := by
  have saved : Exec (.action (.copy (25 : Fin 26) 0)) (full r s) 1
      (full r s r.core.core.core.input) := .action _ _
  have restored : Exec (.action (.copy (0 : Fin 26) 25))
      (full (blank []) s r.core.core.core.input) 1
      (full (blank r.core.core.core.input) s r.core.core.core.input) := .action _ _
  have finished : Exec (.action (.clear (25 : Fin 26)))
      (full (blank r.core.core.core.input) s r.core.core.core.input) 1
      (work r.core.core.core.input s) := .action _ _
  exact Exec.seq saved (Exec.seq (clearWork_exec r s r.core.core.core.input)
    (Exec.seq restored finished))

def flag (good : Bool) : BitString := if good then [true] else []
def restrict (s : Saved) (good : Bool) : Saved := {s with valid := if good then s.valid else []}
def guard (index : Fin 26) : Block 26 :=
  .branch index (.action (.clear 24)) (.action (.clear 24)) .skip
theorem guard_exec (index : Fin 26) (r : State) (s : Saved) (good : Bool)
    (backup : BitString) (read : (full r s backup).get index = flag good) :
    Exec (guard index) (full r s backup) 2 (full r (restrict s good) backup) := by
  cases good with
  | false => exact Exec.empty read (.action _ _)
  | true => exact Exec.one read (.skip _)
theorem restrict_flag (s : Saved) (a b : Bool) :
    restrict {s with valid := flag a} b = {s with valid := flag (a && b)} := by
  cases a <;> cases b <;> rfl

def seeded (input : BitString) : Store 26 := work input {emptySaved with valid := [true]}
theorem seed_exec (input : BitString) :
    Exec (.action (.push (24 : Fin 26) true)) (initial input) 1 (seeded input) := .action _ _

def fromFields (f : SourceReplayRecordFields.Fields) (good : Bool) : Saved :=
  ⟨List.replicate f.dimension true,List.replicate f.rows true,f.source,f.weights,
    List.replicate f.pivot true,f.tail,List.replicate f.outputRows true,f.output,flag good⟩
def capture (input : BitString) : Saved :=
  fromFields (SourceReplayRecordFields.capture input) (SourceReplayRecordFields.valid input)
def result (input : BitString) : Store 26 :=
  work (SourceReplayRecordFields.rest input) (capture input)

end PNP.Concrete.ResidualReduction.SourceReplayRecordState
