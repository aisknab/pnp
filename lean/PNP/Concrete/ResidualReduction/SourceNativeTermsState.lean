import PNP.Concrete.ResidualReduction.SourceNativeTermsSpec

/-! Protected registers for one complete sparse-list converter. The dimension,
affine accumulator, remaining term count, unread suffix and validity flag are
separate from the shared nine-register workspace. -/

namespace PNP.Concrete.ResidualReduction.SourceNativeTermsState
open PNP.Concrete PNP.Concrete.BitRegister
open PNP.Concrete.NormalizerBlocks PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction

structure Saved where
  dimension : BitString
  accumulator : BitString
  pending : BitString
  stream : BitString
  active : BitString

def Saved.tail (s : Saved) : Store 4 :=
  .cons s.accumulator (.cons s.pending (.cons s.stream (.cons s.active .nil)))
def Saved.store (s : Saved) : Store 5 := .cons s.dimension s.tail
def full (r : Registers) (s : Saved) : Store 14 := Frame.join r.store s.store
def work (input : BitString) (s : Saved) : Store 14 :=
  full (SourceScalarState.work input) s
def core (b : Block 9) : Block 14 := Frame.block 5 b
def label (b : Block 10) : Block 14 := Frame.block 4 b

theorem core_exec {b : Block 9} {r out : Registers} {ticks : Nat}
    (checked : Exec b r.store ticks out.store) (s : Saved) :
    Exec (core b) (full r s) ticks (full out s) := Frame.execution checked s.store
theorem label_exec {b : Block 10} {r out : Registers} {ticks : Nat} (s : Saved)
    (checked : Exec b (SourceNativeLabel.full r s.dimension) ticks
      (SourceNativeLabel.full out s.dimension)) :
    Exec (label b) (full r s) ticks (full out s) := Frame.execution checked s.tail

def data {n : Nat} (input : BitString) (a : Affine n) (count : Nat) (valid : Bool) : Saved :=
  ⟨List.replicate n true,SourceNativeEncoding.affineWord a,List.replicate count true,
    input,if valid then [true] else []⟩
def state {n : Nat} (input : BitString) (a : Affine n) (count : Nat) (valid : Bool) : Store 14 :=
  work input (data input a count valid)

def reset : Block 14 := core (SourceChartedSuccessorWords.clearAll 9)
theorem reset_exec (r : Registers) (s : Saved) :
    Exec reset (full r s) 10 (work [] s) :=
  Frame.execution (SourceChartedSuccessorWords.clearAll_exec r.store) s.store

def restore : Block 14 := .action (.copy 0 12)
theorem restore_exec (s : Saved) : Exec restore (work [] s) 1 (work s.stream s) := .action _ _

def retain : Block 14 := .action (.copy 12 0)
theorem retain_exec (r : Registers) (s : Saved) :
    Exec retain (full r s) 1 (full r {s with stream := r.input}) := .action _ _

def reject : Block 14 := .seq (.action (.clear 11))
  (.seq (.action (.clear 13)) (.seq reset restore))
theorem reject_exec (r : Registers) (s : Saved) :
    Exec reject (full r s) 13 (work s.stream {s with pending := [],active := []}) := by
  let done := {s with pending := [],active := []}
  have checked := Exec.seq (.action (.clear (11 : Fin 14)) (full r s))
    (Exec.seq (.action (.clear (13 : Fin 14)) (full r {s with pending := []}))
      (Exec.seq (reset_exec r done) (restore_exec done)))
  simpa only [reject,done] using checked

def advance : Block 14 := .seq (.action (.copy 10 8))
  (.seq (.action (.pop 11)) (.seq reset restore))
theorem advance_exec (r : Registers) (s : Saved) :
    Exec advance (full r s) 13
      (work s.stream {s with accumulator := r.output,pending := s.pending.tail}) := by
  let done := {s with accumulator := r.output,pending := s.pending.tail}
  have checked := Exec.seq (.action (.copy (10 : Fin 14) 8) (full r s))
    (Exec.seq (.action (.pop (11 : Fin 14)) (full r {s with accumulator := r.output}))
      (Exec.seq (reset_exec r done) (restore_exec done)))
  simpa only [advance,done] using checked

end PNP.Concrete.ResidualReduction.SourceNativeTermsState
