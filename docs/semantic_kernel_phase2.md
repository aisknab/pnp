# Semantic kernel hardening — phase 2 (`Subst`)

## Purpose

Phase 1 implemented semantic checking for the primitive `Eq` family. Phase 2 adds an actual, typed `Subst` rule rather than treating substitution as a rule name attached to an arbitrary conclusion.

The rule operates on an earlier accepted judgment. Semantic variables are schematic variables, so instantiating an accepted derivation requires applying the same sort-preserving substitution throughout its conclusion. The checker computes that transformation itself and compares the complete resulting judgment.

## Implemented rule

A `Subst` proof node has exactly one earlier premise and payload:

```text
op = instantiate
variable = SemanticVar0(name, sort)
replacement = a well-sorted semantic term of the same sort
```

The node accepts only when its conclusion is exactly the capture-avoiding substitution of `replacement` for every free occurrence of `variable` in the premise conclusion.

The checker rejects:

- a replacement of a different sort;
- an unsupported substitution operation;
- zero or multiple premises;
- a result that differs at any term or formula coordinate;
- an unsupported term, formula, or judgment constructor;
- a forward premise or unsupported primitive rule.

## Capture avoidance

The semantic syntax now includes finite universal formulas:

```text
ForallFinite(variable, domain, body)
```

When substitution would insert a replacement containing the quantifier's bound variable, the checker deterministically alpha-renames the binder before descending into the body. Fresh names are chosen as `name$0`, `name$1`, and so on, avoiding every variable name already present in the formula, replacement, or target variable.

For example, substituting `x := y` into

```text
forall y in {false,true}. P(x,y)
```

produces

```text
forall y$0 in {false,true}. P(y,y$0)
```

rather than the capture-producing `forall y. P(y,y)`.

`CheckSemanticSubstitution0` checks this transformation independently. It does not prove the source judgment; the `Subst` proof rule invokes the same transformation only after resolving an earlier accepted proof node.

## Supported semantic rules after phase 2

```text
Eq
Subst
```

The readiness gate remains fail-closed. The still-missing rule families are:

```text
Record
DAGInd
LedgerInd
OblTopoInd
TraceInd
FiniteExhaust
DPInd
Hall
RankInd
MinCounterexample
IntArith
Transport
TruthVec
FiniteRel
```

Therefore phase 2 does **not** make the final `P = NP` theorem ready for emission.

## Verification

Run:

```bash
node --check pcc-kernel-semantic0.mjs
node --test test/pcc-kernel-semantic0.test.mjs
```

The phase-2 test set covers:

- accepted Eq reflexivity, symmetry, transitivity, and congruence;
- accepted typed substitution into an earlier equality derivation;
- rejection of a mutated substitution result;
- rejection of a sort-mismatched replacement;
- deterministic alpha-renaming under a finite universal binder;
- rejection of a capture-producing result;
- fail-closed rejection of unsupported primitive rules;
- a readiness gate that no longer lists `Subst` as missing but still rejects because the remaining rule handlers are absent.

## Next integration step

The next change must connect semantic readiness to the current PCC-K implementation without rewriting the sealed `7072f8d` release:

1. add a semantic-readiness field and checker record to the successor `KImpl` format;
2. make the successor `CheckKImpl0` reject final-theorem readiness unless `CheckSemanticKernelReadiness0` accepts;
3. keep partial semantic proofs runnable for development while preventing them from satisfying a final release gate;
4. migrate the existing conformance nodes from shape-only records to semantic nodes;
5. publish any completed chain under new immutable source/checker and artefact coordinates.
