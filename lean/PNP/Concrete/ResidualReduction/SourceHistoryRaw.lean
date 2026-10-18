import PNP.Concrete.ResidualReduction.SourceHistoryInput

/-! Closed complete-history execution on every bitstring. Invalid packets have
a distinct rejection tag. Valid packets return the exact terminal family and
linked history of reduce, including valid inputs for which no step is selected. -/

namespace PNP.Concrete.ResidualReduction.SourceHistoryRaw
open PNP.Concrete PNP.Concrete.BitRegister PNP.Concrete.NormalizerBlocks
open PNP.Concrete.ResidualReduction.FactoredContraction
open PNP.Concrete.ResidualReduction.SourceHistoryEncoding
open PNP.Concrete.ResidualReduction.SourceHistoryState

def outputCodec := MatrixSolutionEncoding.optionCodec SourceEncoding.dataCodec
def canonicalAnswer (n : Nat) (F : Family n) : BitString :=
  outputCodec.encode (some (SourceEncoding.toData (SourceChain.reduce n F)))
def answer (input : BitString) : BitString :=
  match SourceMatrixEncoding.codec.decode input with
  | none => [false]
  | some ⟨n,F⟩ => canonicalAnswer n F
theorem answer_canonical (n : Nat) (F : Family n) :
    answer (packet F) = canonicalAnswer n F := by
  simp only [answer,packet,SourceMatrixEncoding.roundtrip]
theorem answer_malformed (input : BitString) (h : SourceMatrixEncoding.codec.decode input = none) :
    answer input = [false] := by simp only [answer,h]

def process : Block 63 := .seq SourceHistoryOutput.complete (.action (.push 8 true))
def dispatch : Block 63 := .branch 62 .skip .skip process
def block : Block 63 := .seq SourceHistoryInput.block dispatch
def budget (L : Nat) : Nat :=
  SourceHistoryInput.budget L + SourceHistoryBounds.totalPolynomial.eval L + 2
def sourceFuel : NatPolynomial := .add SourceHistoryInput.polynomial
  (.add SourceHistoryBounds.totalPolynomial (.constant 3))
theorem sourceFuel_eval (L : Nat) : sourceFuel.eval L = budget L + 1 := by
  simp only [sourceFuel,NatPolynomial.eval_add,NatPolynomial.eval_constant,
    SourceHistoryInput.polynomial_eval,budget]
  omega

theorem valid_exec (n : Nat) (F : Family n) :
    ∃ used after, Exec block (initial (packet F)) used after ∧
      used ≤ budget (packet F).length ∧ after.get 8 = canonicalAnswer n F := by
  obtain ⟨inputUsed,inputRun,inputBound⟩ := SourceHistoryInput.valid_exec n F
  obtain ⟨used,run,bound⟩ := SourceHistoryOutput.complete_exec n F
  have last : Exec (.action (.push (8 : Fin 63) true))
      (work [] (SourceEncoding.dataCodec.encode (SourceEncoding.toData (SourceChain.reduce n F)))
        (SourceHistoryLoop.finished n F [])) 1
      (work [] (canonicalAnswer n F) (SourceHistoryLoop.finished n F [])) := .action _ _
  have checked : Exec dispatch (work [] [] (data F [])) (1 + (used + 1))
      (work [] (canonicalAnswer n F) (SourceHistoryLoop.finished n F [])) :=
    Exec.one rfl (Exec.seq run last)
  have completeBound := SourceHistoryBounds.complete_bound n F
  refine ⟨inputUsed + (1 + (used + 1)),_,Exec.seq inputRun checked,?_,rfl⟩
  unfold budget
  omega

theorem malformed_exec (input : BitString) (invalid : SourceMatrixEncoding.codec.decode input = none) :
    ∃ used after, Exec block (initial input) used after ∧
      used ≤ budget input.length ∧ after.get 8 = answer input := by
  obtain ⟨used,run,bound⟩ := SourceHistoryInput.block_exec input
  rw [SourceHistoryInput.result,invalid] at run
  have checked : Exec dispatch (SourceHistoryInput.failed input) 2 (SourceHistoryInput.failed input) :=
    Exec.empty rfl (Exec.skip _)
  refine ⟨used + 2,_,Exec.seq run checked,?_,?_⟩
  · unfold budget
    omega
  · rw [answer_malformed input invalid]
    rfl

theorem block_exec (input : BitString) :
    ∃ used after, Exec block (initial input) used after ∧
      used ≤ budget input.length ∧ after.get 8 = answer input := by
  cases decoded : SourceMatrixEncoding.codec.decode input with
  | none => exact malformed_exec input decoded
  | some problem =>
    rcases problem with ⟨n,F⟩
    have bytes := (SourceMatrixEncoding.canonical input ⟨n,F⟩).mp decoded
    change packet F = input at bytes
    rw [← bytes,answer_canonical]
    exact valid_exec n F

end PNP.Concrete.ResidualReduction.SourceHistoryRaw
