/-
Copyright (c) 2026 PNP Labs.

Source-derived accounting for the locked-NAND baseline.  Counts are computed
from the intrinsically typed program itself; no externally supplied occurrence
metadata or Boolean certificate can alter them.
-/

import PNP.DirectWireBaseline

namespace PNP
namespace DirectWire

/-- Swap the final two summands without reflection or AC normalization. -/
theorem natAdd_swap_last (a b c : Nat) :
    (a + b) + c = (a + c) + b := by
  rw [Nat.add_assoc, Nat.add_comm b c]
  rw [← Nat.add_assoc]

/-- Regroup six interleaved count fields into two three-field totals. -/
theorem natAdd_six_regroup (a b c d e f : Nat) :
    (a + b) + (c + d) + (e + f) =
      (a + c + e) + (b + d + f) := by
  calc
    (a + b) + (c + d) + (e + f) =
        (((a + b) + c) + d) + (e + f) := by
          exact congrArg (fun value => value + (e + f))
            (Nat.add_assoc (a + b) c d).symm
    _ = ((((a + b) + c) + d) + e) + f := by
          exact (Nat.add_assoc (((a + b) + c) + d) e f).symm
    _ = ((((a + c) + b) + d) + e) + f := by
          exact congrArg (fun value => ((value + d) + e) + f)
            (natAdd_swap_last a b c)
    _ = ((((a + c) + b) + e) + d) + f := by
          exact congrArg (fun value => value + f)
            (natAdd_swap_last ((a + c) + b) d e)
    _ = ((((a + c) + e) + b) + d) + f := by
          exact congrArg (fun value => (value + d) + f)
            (natAdd_swap_last (a + c) b e)
    _ = ((a + c + e) + (b + d)) + f := by
          exact congrArg (fun value => value + f)
            (Nat.add_assoc (a + c + e) b d)
    _ = (a + c + e) + (b + d + f) := by
          exact Nat.add_assoc (a + c + e) (b + d) f

/-- Dependency-free arithmetic form of `n + 2n = 3n`; this direct induction
    keeps the baseline audit within the constructive arithmetic fragment. -/
theorem natAdd_twice_eq_three_mul (value : Nat) :
    value + 2 * value = 3 * value := by
  induction value with
  | zero => rfl
  | succ value ih =>
      calc
        Nat.succ value + 2 * Nat.succ value =
            (value + 1) + (2 * value + 2) := by
              rw [Nat.succ_eq_add_one, Nat.mul_succ]
        _ = ((value + 1) + 2 * value) + 2 := by
              exact (Nat.add_assoc (value + 1) (2 * value) 2).symm
        _ = ((value + 2 * value) + 1) + 2 := by
              exact congrArg (fun result => result + 2)
                (natAdd_swap_last value 1 (2 * value))
        _ = (value + 2 * value) + (1 + 2) := by
              exact Nat.add_assoc (value + 2 * value) 1 2
        _ = 3 * value + 3 := by
              exact congrArg (fun result => result + 3) ih
        _ = 3 * Nat.succ value := by
              exact (Nat.mul_succ 3 value).symm

/-- The three report classes of NAND source occurrences.  Inputs and earlier
    gates use equality checks; Boolean constants use their corresponding
    checked-constant macros. -/
structure SourceOccurrenceCounts where
  equality : Nat
  zero : Nat
  one : Nat
  deriving Repr, DecidableEq

def SourceOccurrenceCounts.empty : SourceOccurrenceCounts :=
  ⟨0, 0, 0⟩

def SourceOccurrenceCounts.add
    (left right : SourceOccurrenceCounts) : SourceOccurrenceCounts :=
  ⟨left.equality + right.equality,
    left.zero + right.zero,
    left.one + right.one⟩

def SourceOccurrenceCounts.total (counts : SourceOccurrenceCounts) : Nat :=
  counts.equality + counts.zero + counts.one

theorem SourceOccurrenceCounts.add_total
    (left right : SourceOccurrenceCounts) :
    (left.add right).total = left.total + right.total := by
  cases left with
  | mk leftEquality leftZero leftOne =>
      cases right with
      | mk rightEquality rightZero rightOne =>
          change
            (leftEquality + rightEquality) + (leftZero + rightZero) +
                (leftOne + rightOne) =
              (leftEquality + leftZero + leftOne) +
                (rightEquality + rightZero + rightOne)
          exact natAdd_six_regroup leftEquality rightEquality
            leftZero rightZero leftOne rightOne

/-- Classify one actual typed source occurrence. -/
def Source.occurrenceCounts {inputs gates : Nat} :
    Source inputs gates → SourceOccurrenceCounts
  | .input _ => ⟨1, 0, 0⟩
  | .constant false => ⟨0, 1, 0⟩
  | .constant true => ⟨0, 0, 1⟩
  | .gate _ => ⟨1, 0, 0⟩

theorem Source.occurrenceCounts_total
    {inputs gates : Nat} (source : Source inputs gates) :
    source.occurrenceCounts.total = 1 := by
  cases source with
  | input _ => rfl
  | constant value => cases value <;> rfl
  | gate _ => rfl

/-- Counts for the two ordered source occurrences of one NAND gate. -/
def Gate.sourceCounts {inputs gates : Nat}
    (gate : Gate inputs gates) : SourceOccurrenceCounts :=
  gate.left.occurrenceCounts.add gate.right.occurrenceCounts

theorem Gate.sourceCounts_total
    {inputs gates : Nat} (gate : Gate inputs gates) :
    gate.sourceCounts.total = 2 := by
  unfold Gate.sourceCounts
  rw [SourceOccurrenceCounts.add_total,
    Source.occurrenceCounts_total, Source.occurrenceCounts_total]

/-- Counts derived recursively from every gate in a typed program. -/
def Program.sourceCounts {inputs : Nat} :
    {gates : Nat} → Program inputs gates → SourceOccurrenceCounts
  | _, .empty => SourceOccurrenceCounts.empty
  | _, .snoc earlier gate =>
      earlier.sourceCounts.add gate.sourceCounts

/-- Every `m`-gate NAND program has exactly `2m` source occurrences. -/
theorem Program.sourceCounts_total
    {inputs gates : Nat} (program : Program inputs gates) :
    program.sourceCounts.total = 2 * gates := by
  induction program with
  | empty => rfl
  | @snoc gates earlier gate ih =>
      simp only [Program.sourceCounts]
      rw [SourceOccurrenceCounts.add_total, ih, Gate.sourceCounts_total]
      rw [Nat.mul_add]

/-- One trace check per gate plus one source check per source occurrence. -/
def distinguishedCheckCount {inputs gates : Nat}
    (program : Program inputs gates) : Nat :=
  gates + program.sourceCounts.total

theorem distinguishedCheckCount_eq_three_mul
    {inputs gates : Nat} (program : Program inputs gates) :
    distinguishedCheckCount program = 3 * gates := by
  unfold distinguishedCheckCount
  rw [Program.sourceCounts_total]
  exact natAdd_twice_eq_three_mul gates

/-- A nonempty list of `3m` checks has `3m - 1` prefix nodes.  Natural
    subtraction also gives the intended zero-gate boundary value. -/
def prefixNodeCount {inputs gates : Nat}
    (program : Program inputs gates) : Nat :=
  distinguishedCheckCount program - 1

theorem prefixNodeCount_eq_three_mul_sub_one
    {inputs gates : Nat} (program : Program inputs gates) :
    prefixNodeCount program = 3 * gates - 1 := by
  unfold prefixNodeCount
  rw [distinguishedCheckCount_eq_three_mul]

/-- The report baseline, computed from the real program and its real source
    occurrence partition. -/
def lockedBaselineCount {inputs gates : Nat}
    (program : Program inputs gates) : Nat :=
  18 * gates +
    10 * program.sourceCounts.equality +
    3 * program.sourceCounts.zero +
    2 * program.sourceCounts.one +
    2 * prefixNodeCount program

/-- Exact source-derived version of the report formula
    `18m + 10w_= + 3w_0 + 2w_1 + 2(3m-1)`. -/
theorem lockedBaselineCount_report_formula
    {inputs gates : Nat} (program : Program inputs gates) :
    lockedBaselineCount program =
      18 * gates +
        10 * program.sourceCounts.equality +
        3 * program.sourceCounts.zero +
        2 * program.sourceCounts.one +
        2 * (3 * gates - 1) := by
  unfold lockedBaselineCount
  rw [prefixNodeCount_eq_three_mul_sub_one]

/-- The displayed construction adds exactly four final gates after the
    baseline.  This is accounting data, not a threshold theorem. -/
def lockedDisplayedGateCount {inputs gates : Nat}
    (program : Program inputs gates) : Nat :=
  lockedBaselineCount program + 4

theorem lockedDisplayedGateCount_eq_baseline_add_four
    {inputs gates : Nat} (program : Program inputs gates) :
    lockedDisplayedGateCount program = lockedBaselineCount program + 4 := rfl

/-- Conditional exactness of an honestly constructed baseline tuple.  The
    premise is a real square candidate plus semantic output conditions; no
    metadata flag or string certificate can inhabit it.  Constructing this
    candidate globally is deliberately left to the locked-NAND builder. -/
theorem lockedBaseline_exact_of_constructed_distinct
    {carrierInputs circuitGates : Nat}
    (circuit : Program carrierInputs circuitGates)
    (baseline : Candidate carrierInputs
      (lockedBaselineCount circuit) (lockedBaselineCount circuit))
    (conditions : BaselineOutputConditions baseline) :
    referenceMinimum
      (Implementation.mk (lockedBaselineCount circuit) baseline) =
        lockedBaselineCount circuit :=
  referenceMinimum_eq_gateCount_of_squareBaseline baseline conditions

end DirectWire
end PNP
