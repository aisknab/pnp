# Lean locked-NAND macro semantics

`lean/PNP/LockedNANDMacros.lean` is the first concrete Boolean-semantics layer in the Lean track.

It formalizes the displayed gates from report Section 17.2 and Appendix A rather than representing their truth laws by a string or trust-field.

## Definitions

The module defines:

```text
boolNand
boolEq
equalityMacro
constantOneMacro
constantZeroMacro
traceMacro
finalConjunction4
```

The macro definitions follow the report gate-by-gate:

```text
M=  : 10 NAND gates
M1  :  2 NAND gates
M0  :  3 NAND gates
MN  : 18 NAND gates
final conjunction : 4 NAND gates
```

## Distinguished-output theorems

Lean proves by exhaustive Boolean case analysis:

```lean
theorem equalityMacro_distinguished_spec (r u s : Bool) :
    (equalityMacro r u s).a8 = (r && boolEq u s)

theorem constantOneMacro_distinguished_spec (r u : Bool) :
    (constantOneMacro r u).b2 = (r && u)

theorem constantZeroMacro_distinguished_spec (r u : Bool) :
    (constantZeroMacro r u).d3 = (r && !u)

theorem traceMacro_distinguished_spec (lock trace u v : Bool) :
    (traceMacro lock trace u v).q16 =
      (lock && boolEq trace (boolNand u v))

theorem finalConjunction4_spec (z traceChecks outputBit : Bool) :
    finalConjunction4 z traceChecks outputBit =
      (z && traceChecks && outputBit)
```

It also proves that the final lock changes the final output when the trace checks and output bit are true.

## Exhaustive signature checks

The module enumerates all Boolean rows in the same lexicographic order used by the report:

```text
2-variable rows: 4
3-variable rows: 8
4-variable rows: 16
```

Lean then computes the truth signatures for every exposed output and checks:

```text
all 10 equality-macro signatures are pairwise distinct
both constant-one signatures are pairwise distinct
all 3 constant-zero signatures are pairwise distinct
all 18 trace-macro signatures are pairwise distinct
all exposed signatures are nonconstant
all exposed signatures differ from every positive input projection
```

These checks are assembled into the proof-bearing proposition:

```lean
structure LockedNANDMacroCertificate : Prop
```

and the repository exports:

```lean
def lockedNANDMacroCertificate : LockedNANDMacroCertificate
```

No external macro truth-table assumption is needed for that certificate.

## Typed direct-wire and local minimum bridge

`lean/PNP/LockedNANDDirect.lean` now realizes the displayed gadgets as typed direct-wire
candidates with gate/output widths `10/10`, `2/2`, `3/3`, `18/18`, `2/2`, and `4/1` for equality,
constant one, constant zero, trace, prefix, and final conjunction respectively. Lean proves their
semantics agree with this module and that none of the six internal programs uses carrier constants.

The general direct-wire baseline theorem maps semantically nonconstant, nonprojection, pairwise
distinct outputs injectively to gates. Finite truth-signature proofs discharge those conditions for
the five square local candidates, giving exact empty-context reference minima of 10, 2, 3, 18, and
2 gates. The four-gate, one-output final conjunction is not claimed to have an exact four-gate
minimum from this argument.

For the global report word, the convention remains multi-output: the baseline coordinates plus one
final coordinate are exposed. See [Lean locked-NAND direct candidates and local
baselines](./lean_locked_nand_baseline.md) for the source-derived count formula, exact proof boundary,
and quarantined legacy `m = 2` fixture.

## What remains outside this module

These local modules do not prove the full locked-NAND threshold theorem. The remaining global work includes:

```text
carrier-slot allocation and G-Sep+
cross-instance freshness and tagging
prefix-tree coverage and exactness
global candidate construction and cross-instance baseline distinctness
trace-equivalence over a complete NAND circuit
unsatisfiable zero-output convention
satisfiable final-lock lower bound
the polynomial SAT-to-locked-NAND builder
the final threshold equivalence and residual-slack bound
```

The Lean bridge therefore narrows the locked-NAND trust boundary to the global builder/threshold
proof beyond the checked local macro, source-accounting, and square-baseline layers. In particular,
it does not prove the global locked builder, threshold, residual-slack-at-most-four bound, or
polynomiality.
