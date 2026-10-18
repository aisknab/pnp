import PNP.Concrete.ResidualReduction.SourceFamilyReductionEncoding

/-! Protect the family counter, reversed output, sticky validity flag and
original row count outside the verified single-row register program. -/

namespace PNP.Concrete.ResidualReduction.SourceFamilyReductionState
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.NormalizerBlocks.Occurrence
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceMatrixEncoding (familyBits)
open PNP.Concrete.ResidualReduction.SourceRowReductionState (work parameters emptyData)

structure Saved where
  remaining : BitString
  accumulator : BitString
  valid : BitString
  count : BitString
def Saved.store (s : Saved) : Store 4 :=
  .cons s.remaining (.cons s.accumulator (.cons s.valid (.cons s.count .nil)))
def emptySaved : Saved := ⟨[],[],[],[]⟩
def full (r : Store 19) (s : Saved) : Store 23 := Frame.join r s.store
def row (b : Block 19) : Block 23 := Frame.block 4 b
def core (b : Block 9) : Block 23 := row (SourceRowReductionState.core b)

theorem row_exec {b : Block 19} {before after : Store 19} {ticks : Nat}
    (h : Exec b before ticks after) (s : Saved) :
    Exec (row b) (full before s) ticks (full after s) := Frame.execution h s.store
theorem core_exec {b : Block 9} {before after : Registers} {ticks : Nat}
    (h : Exec b before.store ticks after.store) (p : SourcePlanePartnerBuilder.Saved)
    (d : SourceRowReductionState.Data) (s : Saved) :
    Exec (core b) (full (SourceRowReductionState.full before p d) s) ticks
      (full (SourceRowReductionState.full after p d) s) :=
  row_exec (SourceRowReductionState.core_exec h p d) s

def base {n : Nat} (t : TailForm n) (input : BitString) : Store 19 :=
  SourceRowReductionState.full (work n input) (parameters t) (emptyData t [])
def state {n : Nat} (t : TailForm n) (input remaining accumulator : BitString)
    (valid : Bool) (count : BitString) : Store 23 :=
  full (base t input) ⟨remaining,accumulator,[valid],count⟩
def loopState {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix accumulator : BitString)
    (valid : Bool) (count : BitString) : Store 23 :=
  state t (familyBits F ++ suffix) (List.replicate F.length true) accumulator valid count
def initial {n : Nat} (t : TailForm n) (F : Family (n + 1)) (suffix : BitString) : Store 23 :=
  loopState t F suffix [] true (List.replicate F.length true)
def done {n : Nat} (t : TailForm n) (suffix accumulator : BitString)
    (valid : Bool) (count : BitString) : Store 23 :=
  state t suffix [] accumulator valid count
def finished {n : Nat} (t : TailForm n) (suffix out : BitString) : Store 23 :=
  full (SourceRowReductionState.full {work n suffix with output := out}
    (parameters t) (emptyData t [])) emptySaved

def cleanup : Block 23 := .seq (.action (.clear 19)) <|
  .seq (.action (.clear 20)) <| .seq (.action (.clear 21)) (.action (.clear 22))
theorem cleanup_exec (r : Registers) (p : SourcePlanePartnerBuilder.Saved)
    (d : SourceRowReductionState.Data) (s : Saved) :
    Exec cleanup (full (SourceRowReductionState.full r p d) s) 4
      (full (SourceRowReductionState.full r p d) emptySaved) :=
  Exec.seq (.action _ _) (Exec.seq (.action _ _) (Exec.seq (.action _ _) (.action _ _)))

theorem output_get {n : Nat} (t : TailForm n) (suffix out : BitString) :
    (finished t suffix out).get 8 = out := rfl
theorem suffix_get {n : Nat} (t : TailForm n) (suffix out : BitString) :
    (finished t suffix out).get 0 = suffix := rfl

end PNP.Concrete.ResidualReduction.SourceFamilyReductionState
