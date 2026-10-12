/-
Copyright (c) 2026 PNP Labs.

Finite root-query kernel composed from the checked indexed selection,
matching-value decoder and absence projection. This exposes their actual
register execution for tagged graph control without reimplementing lookup.
-/

import PNP.Concrete.NormalizerGraphQuery

namespace PNP.Concrete.NormalizerBlocks.RootKernel

open BitRegister Occurrence

def block : Block 9 :=
  .seq ClauseQuery.block (.seq GraphQuery.handoff
    (.seq MatchingValue.block (.seq GraphQuery.handoff (BooleanHead.block false))))
def decoded (input : BitString) : Registers := MatchingValue.result (ClauseQuery.result input).output
def result (input : BitString) : Registers := BooleanHead.result false (decoded input).output
def sourceSteps (input : BitString) : Nat :=
  ClauseQuery.sourceSteps input + (9 + (MatchingValue.sourceSteps (ClauseQuery.result input).output + (9 + 2)))

theorem block_exec (input : BitString) :
    Exec block (initialRegisters input).store (sourceSteps input) (result input).store :=
  Exec.seq (ClauseQuery.block_exec input) (Exec.seq (GraphQuery.handoff_exec (ClauseQuery.result input))
    (Exec.seq (MatchingValue.block_exec (ClauseQuery.result input).output)
      (Exec.seq (GraphQuery.handoff_exec (decoded input)) (BooleanHead.block_exec false (decoded input).output))))

theorem sourceSteps_bound (input : BitString) : sourceSteps input + 1 ≤ 339 * input.length + 622 := by
  have select := ClauseQuery.sourceSteps_bound input
  have size := ClauseQuery.polynomial_output_length input
  rw [ClauseQuery.polynomial_output] at size
  change (ClauseQuery.result input).output.length ≤ input.length + (84 * input.length + 148) at size
  have decode := MatchingValue.sourceSteps_bound (ClauseQuery.result input).output
  change MatchingValue.sourceSteps (ClauseQuery.result input).output + 1 ≤
    3 * (ClauseQuery.result input).output.length + 11 at decode
  simp only [sourceSteps]
  omega

theorem result_output (input : BitString) : (result input).output = MatchingRoot.polynomial.output input := by
  rw [MatchingRoot.polynomial_output, MatchingRead.polynomial_output, ClauseQuery.polynomial_output,
    MatchingValue.polynomial_output, BooleanHead.polynomial_output]
  rfl

theorem result_canonical (index : Nat) (entries : MatchingTable.Entries) :
    (result (MatchingRead.encodeQuery index entries)).output = [(MatchingTable.read entries index).isNone] := by
  rw [result_output, MatchingRoot.polynomial_canonical]

end PNP.Concrete.NormalizerBlocks.RootKernel
