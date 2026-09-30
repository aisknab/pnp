import PNP

set_option autoImplicit false
set_option Elab.async false

namespace PNP.DirectWire.GrowingWindowUniverseBoundProbe

open Concrete (NatPolynomial)
open Concrete.LockedNAND
open GuardedSpineFamily (candidate)
open GrowingWindowUniverseBound
open PhysicalWindowSearch (Offered Valid candidateUniverse)

/-- These tiny fixtures exercise the existing syntax count, including all
ordered gates. The large guarded search is never executed as a regression. -/
theorem zero_gate_count : (allCandidates 0 0 0).length = 1 := rfl
theorem one_gate_count : (allCandidates 0 1 0).length = 4 := rfl
theorem two_gate_count : (allCandidates 0 2 0).length = 36 := rfl
theorem exact_small_universe : (PhysicalWindowSearch.smallerCandidates 0 0 3).length = 41 := rfl
theorem empty_budget : (PhysicalWindowSearch.smallerCandidates 2 1 0).length = 0 := rfl

theorem query_roundtrip (n : Nat) :
    decodeLockedInstance (query n) =
      some (RawLockedInstance.ofCandidate (candidate (n + 2)) (n + 3)) :=
  decodeLockedInstance_encodeLockedInstance _

theorem query_elaborates (n : Nat) :
    (RawLockedInstance.ofCandidate (candidate (n + 2)) (n + 3)).elaborate =
      some
        { inputCount := n + 3
          gateCount := n + 4
          outputCount := 1
          candidate := candidate (n + 2)
          baseline := n + 3 } :=
  RawLockedInstance.elaborate_ofCandidate _ _

theorem every_polynomial_at_real_bits (polynomial : NatPolynomial) :
    ∃ n : Nat, 0 < residualSlack (candidate (n + 2)).toImplementation ∧
      ∀ (width : Nat)
        (records : List (TerminalPrimitiveRecord (n + 3) (n + 4) 1 width))
        (offered : Offered (candidate (n + 2)) records),
        Valid (candidate (n + 2)) records offered →
          polynomial.eval (query n).length < (candidateUniverse (candidate (n + 2)) records).length :=
  valid_universe_exceeds_encoded_polynomial polynomial

theorem complete_uniform_polynomial_contradiction :
    ¬ ∃ polynomial : NatPolynomial, ∀ n : Nat,
      ∃ (width : Nat)
        (records : List (TerminalPrimitiveRecord (n + 3) (n + 4) 1 width))
        (offered : Offered (candidate (n + 2)) records),
        Valid (candidate (n + 2)) records offered ∧
          (candidateUniverse (candidate (n + 2)) records).length ≤ polynomial.eval (query n).length :=
  no_uniform_polynomial_complete_universe

end PNP.DirectWire.GrowingWindowUniverseBoundProbe

#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.zero_gate_count
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.one_gate_count
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.two_gate_count
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.exact_small_universe
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.empty_budget
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.query_roundtrip
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.query_elaborates
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.every_polynomial_at_real_bits
#print axioms PNP.DirectWire.GrowingWindowUniverseBoundProbe.complete_uniform_polynomial_contradiction
