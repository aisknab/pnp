/-
Copyright (c) 2026 PNP Labs.

Concrete semantics for the prefix-conjunction layer in report Section 17.

The report combines all distinguished equality, constant, and NAND trace checks
with two NAND gates per internal conjunction node, exposes both the conjunction
and its negation, and uses the final prefix value in the four-gate output.

This file defines that construction, proves exact conjunction/coverage, proves
the two-gate count, and checks the local exposed-output signatures.
-/

import PNP.LockedNANDMacros

namespace PNP

/-- The report's two-gate conjunction node.  `neg` is the first NAND output and
`out` is the second NAND output.  Both are exposed by the locked construction. -/
structure PrefixAndOutputs where
  neg : Bool
  out : Bool
  deriving Repr, DecidableEq

/-- Two NAND gates computing `a ∧ b` and exposing its negation. -/
def prefixAndMacro (a b : Bool) : PrefixAndOutputs :=
  let neg := boolNand a b
  let out := boolNand neg neg
  { neg, out }


theorem prefixAndMacro_neg_spec (a b : Bool) :
    (prefixAndMacro a b).neg = !(a && b) := by
  cases a <;> cases b <;> decide


theorem prefixAndMacro_out_spec (a b : Bool) :
    (prefixAndMacro a b).out = (a && b) := by
  cases a <;> cases b <;> decide

/-- A left-associated prefix trace.  A nonempty list with `n` checks has exactly
`n - 1` two-gate nodes. -/
def prefixTraceAux (acc : Bool) : List Bool → List PrefixAndOutputs
  | [] => []
  | b :: bs =>
      let node := prefixAndMacro acc b
      node :: prefixTraceAux node.out bs


def prefixTrace : List Bool → List PrefixAndOutputs
  | [] => []
  | x :: xs => prefixTraceAux x xs

/-- Boolean value returned by the report's prefix conjunction.  The empty case
is the neutral element; locked instances use a nonempty check list. -/
def prefixConjunctionAux (acc : Bool) : List Bool → Bool
  | [] => acc
  | b :: bs =>
      prefixConjunctionAux (prefixAndMacro acc b).out bs


def prefixConjunction : List Bool → Bool
  | [] => true
  | x :: xs => prefixConjunctionAux x xs

/-- Specification-level conjunction of all check bits. -/
def allChecks : List Bool → Bool
  | [] => true
  | x :: xs => x && allChecks xs

/-- Accumulator invariant for the concrete NAND prefix construction. -/
theorem prefixConjunctionAux_spec (acc : Bool) (xs : List Bool) :
    prefixConjunctionAux acc xs = (acc && allChecks xs) := by
  induction xs generalizing acc with
  | nil =>
      cases acc <;> decide
  | cons b bs ih =>
      cases acc <;> cases b <;>
        simp [prefixConjunctionAux, allChecks, prefixAndMacro_out_spec, ih]

/-- The concrete NAND prefix computes the conjunction of exactly the supplied
check list. -/
theorem prefixConjunction_spec (checks : List Bool) :
    prefixConjunction checks = allChecks checks := by
  cases checks with
  | nil => rfl
  | cons x xs =>
      simpa [prefixConjunction, allChecks] using
        (prefixConjunctionAux_spec x xs)

/-- The final prefix value is true exactly when every listed check is true. -/
theorem allChecks_eq_true_iff (checks : List Bool) :
    allChecks checks = true ↔ ∀ b ∈ checks, b = true := by
  induction checks with
  | nil => simp [allChecks]
  | cons b bs ih =>
      cases b <;> simp [allChecks, ih]


theorem prefixConjunction_eq_true_iff (checks : List Bool) :
    prefixConjunction checks = true ↔ ∀ b ∈ checks, b = true := by
  rw [prefixConjunction_spec]
  exact allChecks_eq_true_iff checks

/-- The trace has one node for every check after the first. -/
theorem prefixTraceAux_length (acc : Bool) (xs : List Bool) :
    (prefixTraceAux acc xs).length = xs.length := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
      simp [prefixTraceAux, ih]


theorem prefixTrace_length_nonempty (x : Bool) (xs : List Bool) :
    (prefixTrace (x :: xs)).length = xs.length := by
  simp [prefixTrace, prefixTraceAux_length]

/-- NAND gate count for the prefix tree. -/
def prefixGateCount (checks : List Bool) : Nat :=
  2 * (prefixTrace checks).length


theorem prefixGateCount_nonempty (x : Bool) (xs : List Bool) :
    prefixGateCount (x :: xs) = 2 * xs.length := by
  simp [prefixGateCount, prefixTrace, prefixTraceAux_length]


theorem prefixGateCount_eq_two_mul_pred (x : Bool) (xs : List Bool) :
    prefixGateCount (x :: xs) = 2 * ((x :: xs).length - 1) := by
  simp [prefixGateCount_nonempty]

/-- Local truth signatures for the two exposed outputs of one conjunction node. -/
def prefixAndSignatures : List (List Bool) := [
  signature2 (fun a b => (prefixAndMacro a b).neg),
  signature2 (fun a b => (prefixAndMacro a b).out)
]


theorem prefixAndSignatures_nodup : prefixAndSignatures.Nodup := by
  decide


theorem prefixAndSignatures_nonconstant_nonprojection :
    prefixAndSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true := by
  decide

/-- Proof-bearing summary for the concrete prefix layer. -/
structure LockedNANDPrefixCertificate : Prop where
  nodeNegation : ∀ a b,
    (prefixAndMacro a b).neg = !(a && b)
  nodeConjunction : ∀ a b,
    (prefixAndMacro a b).out = (a && b)
  exactCoverage : ∀ checks,
    prefixConjunction checks = allChecks checks
  trueExactlyAllChecks : ∀ checks,
    prefixConjunction checks = true ↔ ∀ b ∈ checks, b = true
  traceLength : ∀ x xs,
    (prefixTrace (x :: xs)).length = xs.length
  gateCount : ∀ x xs,
    prefixGateCount (x :: xs) = 2 * xs.length
  localOutputsDistinct : prefixAndSignatures.Nodup
  localOutputsNonconstantNonprojection :
    prefixAndSignatures.all (fun sig =>
      !(constantSignatures2.contains sig) &&
      !(positiveProjectionSignatures2.contains sig)) = true

/-- The complete local prefix certificate is constructed by Lean. -/
def lockedNANDPrefixCertificate : LockedNANDPrefixCertificate :=
  { nodeNegation := prefixAndMacro_neg_spec
    nodeConjunction := prefixAndMacro_out_spec
    exactCoverage := prefixConjunction_spec
    trueExactlyAllChecks := prefixConjunction_eq_true_iff
    traceLength := prefixTrace_length_nonempty
    gateCount := prefixGateCount_nonempty
    localOutputsDistinct := prefixAndSignatures_nodup
    localOutputsNonconstantNonprojection :=
      prefixAndSignatures_nonconstant_nonprojection }

end PNP
