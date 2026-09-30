import PNP.NANDGuardedSpineBoundedQuiet
import PNP.Concrete.LockedNANDTargetEmitterSpec
import PNP.Concrete.Complexity

set_option autoImplicit false
set_option Elab.async false

/-! The complete materialized candidate universe of the existing physical
window search has no uniform encoded-size polynomial bound on a guarded
nonminimum family. This concerns the list being constructed, not the number
of candidates visited, a machine-runtime lower bound, or all possible solvers. -/

namespace PNP.DirectWire.GrowingWindowUniverseBound

open Concrete (NatPolynomial)
open GuardedSpineFamily (candidate)
open PhysicalWindowSearch (smallerCandidates candidateUniverse Valid Offered)
open Concrete.LockedNAND (encodeLockedInstance RawLockedInstance)

private theorem flatMap_length_eq {α β : Type} (items : List α)
    (mapping : α → List β) (size : Nat)
    (each : ∀ item, item ∈ items → (mapping item).length = size) :
    (items.flatMap mapping).length = items.length * size := by
  induction items with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head tail ih =>
      rw [List.flatMap_cons, List.length_append, each head List.mem_cons_self,
        ih (fun item member => each item (List.mem_cons_of_mem head member))]
      simp only [List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem branch_length_le {α β : Type} (items : List α)
    (mapping : α → List β) (item : α) (member : item ∈ items) :
    (mapping item).length ≤ (items.flatMap mapping).length := by
  induction items with
  | nil => cases member
  | cons head tail ih =>
      rw [List.flatMap_cons, List.length_append]
      rcases List.mem_cons.mp member with same | later
      · subst head
        omega
      · have smaller := ih later
        omega

private theorem allSources_length (inputs gates : Nat) :
    (allSources inputs gates).length = inputs + gates + 2 := by
  simp only [allSources, List.length_append, List.length_map, allFin_length,
    List.length_cons, List.length_nil]
  omega

private theorem allGates_length (inputs gates : Nat) :
    (allGates inputs gates).length = (inputs + gates + 2) ^ 2 := by
  calc
    _ = (allSources inputs gates).length * (allSources inputs gates).length :=
      flatMap_length_eq _ _ _ (fun _ _ => List.length_map _)
    _ = (inputs + gates + 2) ^ 2 := by
      rw [allSources_length, Nat.pow_two]

private theorem programs_length_succ (inputs gates : Nat) :
    (allPrograms inputs (gates + 1)).length =
      (allPrograms inputs gates).length * (inputs + gates + 2) ^ 2 := by
  change ((allPrograms inputs gates).flatMap
    (fun initial => (allGates inputs gates).map (fun gate => Program.snoc initial gate))).length = _
  rw [flatMap_length_eq _ _ _ (fun _ _ => List.length_map _), allGates_length]

private theorem programs_length_positive (inputs gates : Nat) :
    1 ≤ (allPrograms inputs gates).length := by
  induction gates with
  | zero => exact Nat.le_refl 1
  | succ gates ih =>
      rw [programs_length_succ]
      exact Nat.mul_le_mul ih (Nat.one_le_pow 2 _ (by omega))

/-- A tail of the real program enumerator already has this many entries.
Repeated syntax is counted exactly as in the existing list representation. -/
theorem programs_tail_length_le (inputs start steps : Nat) :
    ((inputs + start + 2) ^ 2) ^ steps ≤
      (allPrograms inputs (start + steps)).length := by
  induction steps with
  | zero =>
      simpa only [Nat.pow_zero, Nat.add_zero] using programs_length_positive inputs start
  | succ steps ih =>
      rw [← Nat.add_assoc start steps 1, programs_length_succ, Nat.pow_succ]
      exact Nat.mul_le_mul ih (Nat.pow_le_pow_left (by omega) 2)

private theorem outputWords_length (inputs gates outputs : Nat) :
    (allOutputWords inputs gates outputs).length = (inputs + gates + 2) ^ outputs := by
  induction outputs with
  | zero => rfl
  | succ outputs ih =>
      calc
        _ = (allSources inputs gates).length * (inputs + gates + 2) ^ outputs := by
          apply flatMap_length_eq
          intro _head _member
          rw [List.length_map, ih]
        _ = (inputs + gates + 2) ^ (outputs + 1) := by
          rw [allSources_length, Nat.pow_succ, Nat.mul_comm]

private theorem programs_le_candidates (inputs gates outputs : Nat) :
    (allPrograms inputs gates).length ≤ (allCandidates inputs gates outputs).length := by
  have counted : (allCandidates inputs gates outputs).length =
      (allPrograms inputs gates).length * (inputs + gates + 2) ^ outputs := by
    change ((allPrograms inputs gates).flatMap
      (fun program => (allOutputWords inputs gates outputs).map
        (fun word => Candidate.mk program word))).length = _
    rw [flatMap_length_eq _ _ _ (fun _ _ => List.length_map _), outputWords_length]
  rw [counted]
  have positive := Nat.one_le_pow outputs (inputs + gates + 2) (by omega)
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (allPrograms inputs gates).length positive

private theorem programs_le_smaller (inputs gates outputs budget : Nat)
    (below : gates < budget) :
    (allPrograms inputs gates).length ≤ (smallerCandidates inputs outputs budget).length := by
  have branch := branch_length_le (List.range budget)
    (fun size => (allCandidates inputs size outputs).map Candidate.toImplementation)
    gates (List.mem_range.mpr below)
  rw [List.length_map] at branch
  exact Nat.le_trans (programs_le_candidates inputs gates outputs) branch

private theorem value_le_power (input value : Nat) : value ≤ (input + 2) ^ value := by
  induction value with
  | zero => exact Nat.zero_le _
  | succ value ih =>
      have larger := Nat.pow_lt_pow_succ (a := input + 2) (n := value) (by omega)
      omega

private theorem polynomial_power_bound (polynomial : NatPolynomial) :
    ∃ exponent : Nat, ∀ input : Nat, polynomial.eval input ≤ (input + 2) ^ exponent := by
  induction polynomial with
  | constant value =>
      exact ⟨value, fun input => value_le_power input value⟩
  | «variable» =>
      exact ⟨1, fun input => by simp only [NatPolynomial.eval, Nat.pow_one]; omega⟩
  | add left right leftIH rightIH =>
      obtain ⟨a, leftBound⟩ := leftIH
      obtain ⟨b, rightBound⟩ := rightIH
      refine ⟨a + b + 1, fun input => ?_⟩
      have leftPower := Nat.pow_le_pow_of_le (a := input + 2)
        (by omega) (show a ≤ a + b by omega)
      have rightPower := Nat.pow_le_pow_of_le (a := input + 2)
        (by omega) (show b ≤ a + b by omega)
      have leftAt := leftBound input
      have rightAt := rightBound input
      change left.eval input + right.eval input ≤ _
      calc
        _ ≤ 2 * (input + 2) ^ (a + b) := by omega
        _ ≤ (input + 2) * (input + 2) ^ (a + b) :=
          Nat.mul_le_mul_right _ (by omega)
        _ = (input + 2) ^ (a + b + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  | mul left right leftIH rightIH =>
      obtain ⟨a, leftBound⟩ := leftIH
      obtain ⟨b, rightBound⟩ := rightIH
      refine ⟨a + b, fun input => ?_⟩
      change left.eval input * right.eval input ≤ _
      rw [Nat.pow_add]
      exact Nat.mul_le_mul (leftBound input) (rightBound input)

/-- Even allowing arbitrary boundary and output widths, the actual smaller
candidate list eventually exceeds every polynomial of the source parameter. -/
theorem smallerCandidates_exceeds_polynomial (polynomial : NatPolynomial) :
    ∃ n : Nat, ∀ inputs outputs budget : Nat, n + 4 ≤ budget →
      polynomial.eval n < (smallerCandidates inputs outputs budget).length := by
  obtain ⟨k, bounded⟩ := polynomial_power_bound polynomial
  refine ⟨2 * k, fun inputs outputs budget enough => ?_⟩
  have baseBound : 2 * k + 2 ≤ (inputs + (k + 2) + 2) ^ 2 := by
    have squareBound : 2 * k + 2 ≤ (k + 4) ^ 2 := by
      simp only [Nat.pow_two, Nat.add_mul, Nat.mul_add]
      omega
    exact Nat.le_trans squareBound (Nat.pow_le_pow_left (by omega) 2)
  have tailBound := programs_tail_length_le inputs (k + 2) (k + 1)
  have same : k + 2 + (k + 1) = 2 * k + 3 := by omega
  rw [same] at tailBound
  calc
    polynomial.eval (2 * k) ≤ (2 * k + 2) ^ k := bounded (2 * k)
    _ < (2 * k + 2) ^ (k + 1) := Nat.pow_lt_pow_succ (by omega)
    _ ≤ ((inputs + (k + 2) + 2) ^ 2) ^ (k + 1) :=
      Nat.pow_le_pow_left baseBound (k + 1)
    _ ≤ (allPrograms inputs (2 * k + 3)).length := tailBound
    _ ≤ (smallerCandidates inputs outputs budget).length :=
      programs_le_smaller inputs (2 * k + 3) outputs budget (by omega)

/-- The real unary-header, four-bit-token query encoding, with a threshold
strictly above the explicit equivalent shorter candidate's gate count. -/
def query (n : Nat) : Concrete.BitString :=
  encodeLockedInstance (RawLockedInstance.ofCandidate (candidate (n + 2)) (n + 3))

/-- Exactly the general codec bound specialized to the guarded family. -/
def queryLengthPolynomial : NatPolynomial :=
  let inputs : NatPolynomial := .add .variable (.constant 3)
  let gates : NatPolynomial := .add .variable (.constant 4)
  let sources : NatPolynomial := .add (.add inputs gates) (.constant 1)
  .mul (.constant 4)
    (.add
      (.add
        (.add (.add (.add (.add inputs gates) (.constant 1)) inputs) (.constant 9))
        (.mul gates (.add (.mul (.constant 2) sources) (.constant 1))))
      (.mul (.constant 1) sources))

theorem query_length_le (n : Nat) :
    (query n).length ≤ queryLengthPolynomial.eval n := by
  exact Concrete.LockedNAND.TargetEmitterSpec.encodeLockedInstance_ofCandidate_length_le
    (candidate (n + 2)) (n + 3)

/-- Any accepted strict improvement needs the source's full gate budget.
The previously proved proper-support minimum result supplies this boundary. -/
theorem valid_requires_full_budget (n : Nat) {width : Nat}
    (records : List (TerminalPrimitiveRecord (n + 3) (n + 4) 1 width))
    (offered : Offered (candidate (n + 2)) records)
    (valid : Valid (candidate (n + 2)) records offered) :
    n + 4 ≤ (extractTerminalSupport (candidate (n + 2)) records).gateCount := by
  by_cases enough : n + 4 ≤ (extractTerminalSupport (candidate (n + 2)) records).gateCount
  · exact enough
  · have bounded : (extractTerminalSupport (candidate (n + 2)) records).gateCount ≤ n + 3 := by
      omega
    exact False.elim
      (GuardedSpineBoundedQuiet.bounded_quiet (n + 2) (n + 3) (by omega)
        width records bounded offered valid)

/-- A source-derived, genuinely nonminimum family defeats any polynomial
bound on the complete materialized universe of an accepted physical search.
This is not a lower bound for a different enumeration or a lazy representation. -/
theorem valid_universe_exceeds_encoded_polynomial (polynomial : NatPolynomial) :
    ∃ n : Nat, 0 < residualSlack (candidate (n + 2)).toImplementation ∧
      ∀ (width : Nat)
        (records : List (TerminalPrimitiveRecord (n + 3) (n + 4) 1 width))
        (offered : Offered (candidate (n + 2)) records),
        Valid (candidate (n + 2)) records offered →
          polynomial.eval (query n).length < (candidateUniverse (candidate (n + 2)) records).length := by
  obtain ⟨n, larger⟩ := smallerCandidates_exceeds_polynomial
    (polynomial.substitute queryLengthPolynomial)
  refine ⟨n, GuardedSpineFamily.residual_positive n, fun width records offered valid => ?_⟩
  have exceeds := larger
    (terminalBoundaryPorts (candidate (n + 2)).program records).length
    (terminalInterfacePorts (candidate (n + 2)) records).length
    (extractTerminalSupport (candidate (n + 2)) records).gateCount
    (valid_requires_full_budget n records offered valid)
  rw [NatPolynomial.eval_substitute] at exceeds
  exact Nat.lt_of_le_of_lt (polynomial.eval_mono (query_length_le n)) exceeds

/-- A uniformly complete choice of accepted windows and offers cannot make
the existing full candidate-list construction polynomial in the query bits. -/
theorem no_uniform_polynomial_complete_universe :
    ¬ ∃ polynomial : NatPolynomial, ∀ n : Nat,
      ∃ (width : Nat)
        (records : List (TerminalPrimitiveRecord (n + 3) (n + 4) 1 width))
        (offered : Offered (candidate (n + 2)) records),
        Valid (candidate (n + 2)) records offered ∧
          (candidateUniverse (candidate (n + 2)) records).length ≤ polynomial.eval (query n).length := by
  rintro ⟨polynomial, complete⟩
  obtain ⟨n, _positive, exceeds⟩ := valid_universe_exceeds_encoded_polynomial polynomial
  obtain ⟨width, records, offered, valid, bounded⟩ := complete n
  have larger := exceeds width records offered valid
  omega

end PNP.DirectWire.GrowingWindowUniverseBound
