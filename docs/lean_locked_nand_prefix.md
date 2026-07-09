# Lean locked-NAND prefix conjunction

`lean/PNP/LockedNANDPrefix.lean` formalizes the prefix-conjunction layer used by the locked-NAND SAT embedding.

The report states that every distinguished equality, constant, and NAND trace check is included exactly once in a prefix tree; each internal conjunction node uses two NAND gates and exposes both the conjunction and its negation. The final prefix value is the `Tφ` input to the four-gate final output.

## Two-gate node

The module defines:

```lean
structure PrefixAndOutputs where
  neg : Bool
  out : Bool

def prefixAndMacro (a b : Bool) : PrefixAndOutputs
```

and proves by exhaustive Boolean case analysis:

```lean
theorem prefixAndMacro_neg_spec (a b : Bool) :
    (prefixAndMacro a b).neg = !(a && b)

theorem prefixAndMacro_out_spec (a b : Bool) :
    (prefixAndMacro a b).out = (a && b)
```

## Prefix exactness and coverage

For a list of check bits, Lean defines the concrete NAND trace and its final value:

```lean
def prefixTrace : List Bool → List PrefixAndOutputs

def prefixConjunction : List Bool → Bool
```

It proves:

```lean
theorem prefixConjunction_spec (checks : List Bool) :
    prefixConjunction checks = allChecks checks

theorem prefixConjunction_eq_true_iff (checks : List Bool) :
    prefixConjunction checks = true ↔
      ∀ b ∈ checks, b = true
```

Thus the final prefix is true exactly when every listed distinguished check is true. This discharges the local semantic meaning of the report's `prefix covers all distinguished checks` obligation for the supplied check list.

## Gate count

For a nonempty list whose first check is `x` and remaining checks are `xs`, Lean proves:

```lean
theorem prefixTrace_length_nonempty (x : Bool) (xs : List Bool) :
    (prefixTrace (x :: xs)).length = xs.length

theorem prefixGateCount_nonempty (x : Bool) (xs : List Bool) :
    prefixGateCount (x :: xs) = 2 * xs.length

theorem prefixGateCount_eq_two_mul_pred (x : Bool) (xs : List Bool) :
    prefixGateCount (x :: xs) =
      2 * ((x :: xs).length - 1)
```

This is the report's two-gates-per-internal-node count.

## Local exposed-output checks

The module computes the four-row truth signatures of the two outputs of a prefix node and proves:

```text
the two outputs are distinct
both outputs are nonconstant
neither output is a positive input projection
```

The results are assembled into:

```lean
structure LockedNANDPrefixCertificate : Prop

def lockedNANDPrefixCertificate :
    LockedNANDPrefixCertificate
```

## Remaining global work

This module proves the semantics and gate count of a prefix built from a supplied check list. It does not yet prove the complete locked-NAND builder theorem. Remaining work includes:

```text
constructing the exact global distinguished-check list for a NAND circuit
showing every required macro check appears exactly once
fresh lock and occurrence-slot allocation
cross-instance output distinctness
prefix-node separation from macro outputs and from other prefix nodes
baseline count and direct-wire lower bound
trace equivalence for the complete constructed circuit
locked threshold equivalence and residual-slack bound
```

The locked-NAND trust boundary is therefore narrowed from “local macro and prefix semantics plus the global builder” to the remaining global construction and threshold proof.
