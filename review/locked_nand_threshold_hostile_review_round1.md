# Hostile Mathematical Review Round 1: Locked NAND Threshold

Status: **open mathematical audit target**.

This note is not a release-engineering patch. The hardened release machinery now gives a coherent reproduction and acceptance story. This note identifies the first theorem block that a hostile complexity-theory reviewer should attack: the locked NAND threshold theorem.

## Release context

Current hardened release identifiers:

```text
source commit:
105af516128fa0f7cc9978e6381bb6d8afdc7058

source tag:
final-pnp-proof-report-hardened-105af51

sealed artifact tag:
final-pnp-proof-report-artifacts-hardened-105af51-sealed

artifact bundle:
proof-artifacts/final-pnp-proof-report-hardened-105af51/

validation:
984 tests, 984 pass, 0 fail
```

Public theorem boundary:

```text
CheckPCCPackexp(GeneratePCCPack())=accept => P = NP
```

The review below concerns the mathematical theorem content behind the checker artefacts, not the release custody.

## Target theorem

For a NAND circuit φ with m gates and source occurrence counts w_=, w_0, w_1, the locked NAND construction claims:

```text
B^NAND_φ = 18m + 10w_= + 3w_0 + 2w_1 + 2(3m - 1)

|W^NAND_φ| = B^NAND_φ + 4
```

and:

```text
φ ∉ SAT  =>  μ(W^NAND_φ) = B^NAND_φ

φ ∈ SAT  =>  B^NAND_φ + 1 ≤ μ(W^NAND_φ) ≤ B^NAND_φ + 4

φ ∈ SAT  <=> μ(W^NAND_φ) > B^NAND_φ

Λ(W^NAND_φ) ≤ 4
```

The proof breaks into six obligations.

## Obligation 1: Macro truth signatures

### Claim

Every exposed output of every equality, constant, NAND-trace, and prefix macro is a pairwise distinct nonconstant nonprojection function in the required local variable set, and depends essentially on its private lock where applicable.

### Current positive evidence

The manuscript gives explicit truth signatures for equality, constant, and NAND trace macros. These can be checked mechanically. For example, the equality macro exposes ten signatures, and the NAND trace macro exposes eighteen signatures.

### Hostile questions

1. Are the signatures compared against all projections in the correct variable order?
2. Are complements of projections also excluded if direct-wire output conventions allow negated projections for free?
3. Are repeated macro instances protected by globally fresh locks, so that two syntactically identical exposed outputs in different macro instances are not the same function over the same carrier variables?
4. Are occurrence slots fresh for duplicate NAND sources?
5. Do prefix-conjunction exposed outputs create any duplicates with macro outputs?

### Required manuscript strengthening

Add a compact lemma:

```text
MacroDistinct:
For every macro instance, every exposed output is nonconstant, nonprojection,
and distinct from every exposed output of every other macro instance after
carrier tagging. The proof is by truth-vector comparison plus fresh lock/slot
tagging.
```

## Obligation 2: Baseline lower bound

### Claim

The baseline tuple contains exactly B^NAND_φ pairwise distinct nonconstant nonprojection output functions. Therefore every direct-wire realization of the baseline tuple has at least B^NAND_φ NAND gates.

### Strong version of the argument

In the direct-wire model, an output wire can be one of:

```text
input/projection
carrier constant
previous NAND gate output
```

If an output function is nonconstant and nonprojection, it cannot be supplied by an input wire or carrier constant. Therefore it must be the output of a NAND gate.

If the baseline tuple contains B pairwise distinct functions, then those B outputs cannot all be supplied by fewer than B NAND gates, because a single gate output wire computes only one Boolean function. Two distinct baseline functions cannot share the same final gate output.

Therefore:

```text
μ(baseline tuple) ≥ B.
```

The constructed baseline word has exactly B exposed NAND gate outputs, so:

```text
μ(baseline tuple) = B.
```

### Hostile questions

1. Does the output convention allow a single gate to feed multiple output positions?  
   If yes, the lower bound still holds for pairwise distinct functions, but the proof must explicitly say so.

2. Can a later gate produce one exposed function while also making an earlier exposed function available internally?  
   This does not reduce count if every exposed noninput function still needs some gate output, but the injection from distinct output functions to distinct gate outputs must be explicit.

3. Does the baseline include any constants or projections?  
   If yes, those outputs do not force gates. The theorem must isolate only nonconstant nonprojection outputs.

4. Are constant-zero and constant-one macros counted correctly?  
   The baseline formula counts exposed macro gates, but the proof must distinguish "constant enforced under lock" from "free carrier constant."

5. Are all prefix-conjunction outputs nonconstant nonprojection?  
   The prefix outputs must not collapse under any legal trace assignment; the functions are over the whole carrier, not under a fixed satisfying assignment.

### Required manuscript strengthening

Add a formal lemma:

```text
DirectWireOutputLowerBound:
Let F = (f_1,...,f_B) be an output tuple of pairwise distinct Boolean functions
over carrier variables. If every f_i is nonconstant and nonprojection, then every
NAND direct-wire realization of F has at least B NAND gates.
```

Then apply `MacroDistinct` and `G-Sep+`.

## Obligation 3: Trace equivalence

### Claim

The distinguished equality, constant, and NAND-trace checks plus prefix conjunction produce a trace predicate T_φ satisfying:

```text
T_φ(t, occurrence slots, locks) = 1
```

if and only if the trace slots encode a coherent NAND evaluation of φ.

The final SAT predicate is:

```text
T_φ ∧ y_out
```

and should be satisfiable if and only if φ is satisfiable.

### Hostile questions

1. Does every source occurrence of every gate have exactly one equality/constant/trace constraint?
2. Do equality macros really force occurrence slots to equal their source values when the private lock is active?
3. Are private locks constrained to the active value, or can an assignment set a lock to deactivate a check?
4. If locks are free carrier variables, why does a check being "distinguished output equals 1" force the intended equality for all assignments?
5. Does the prefix conjunction include every distinguished check exactly once?
6. Does the final output use the original circuit output slot and not an unconstrained occurrence copy?
7. Does topological induction over the NAND circuit explicitly prove both directions:
   - satisfying assignment gives a check assignment;
   - check assignment with y_out=1 gives a satisfying assignment?

### Required manuscript strengthening

Add a theorem:

```text
TraceEquivalence:
For every assignment to primary inputs X, there exists an extension to T,O,R,L
making all distinguished checks one and y_out=1 iff φ(X)=1.
```

The proof should be by topological induction over the NAND circuit and should explicitly handle constants and duplicate source occurrences.

## Obligation 4: Unsatisfiable case

### Claim

If φ is unsatisfiable, then:

```text
μ(W^NAND_φ) = B^NAND_φ.
```

### Intended proof

If φ is unsatisfiable, then:

```text
T_φ ∧ y_out
```

is identically false. Therefore the final output:

```text
F_φ = z ∧ T_φ ∧ y_out
```

is identically zero.

If zero output is free under the direct-wire output convention, or if a zero output is already present in the baseline tuple and may be reused, then adding F_φ adds no irreducible cost beyond the baseline. Thus:

```text
μ(W^NAND_φ) ≤ B^NAND_φ.
```

The baseline lower bound gives:

```text
μ(W^NAND_φ) ≥ B^NAND_φ.
```

So equality follows.

### Hostile questions

1. Is a constant-zero output free in this direct-wire model?
2. If not free, is there an already exposed baseline zero function that the final output may legally share?
3. If constants are enforced by M0/M1 rather than carrier constants, does the unsat final output collapse to a baseline-exposed locked zero or to an external free zero?
4. Does the word output tuple include the final output as an additional coordinate even when it is the zero function?
5. Does the direct-wire minimization model count gates only, or also count output wires / duplicated output coordinates?
6. Is the lower bound still exactly B when the full word includes an extra coordinate equal to constant zero?

### Required manuscript strengthening

This is the first serious possible gap.

Add an explicit convention and lemma:

```text
ZeroOutputConvention:
In μ for a multi-output direct-wire word, output coordinates may be wired to
carrier constants without a NAND gate; repeated output functions do not increase
gate count. Therefore appending an identically zero final coordinate does not
increase μ.
```

If this convention is not intended, then the proof must show that F_φ equals a baseline-exposed zero output in the unsatisfiable case.

## Obligation 5: Satisfiable case upper bound

### Claim

If φ is satisfiable, then:

```text
μ(W^NAND_φ) ≤ B^NAND_φ + 4.
```

### Intended proof

The constructed word already realizes the baseline outputs with B gates. Given the coherent trace predicate and satisfying output, the final output is built by a four-gate ternary conjunction:

```text
F_φ = z ∧ T_φ ∧ y_out.
```

Thus the complete word has size:

```text
B + 4.
```

### Hostile questions

1. Which exact four gates realize the ternary conjunction?
2. Is T_φ already available as a baseline-exposed prefix output?
3. Is y_out already available as a trace/output slot?
4. Does the final lock z appear nowhere else?
5. Does the construction expose only F_φ from the final four gates, not intermediate final gates that would alter the baseline count?

### Required manuscript strengthening

Add a displayed four-gate construction and identify the precise input wires:

```text
final conjunction inputs: z, T_φ, y_out.
```

## Obligation 6: Satisfiable case lower bound

### Claim

If φ is satisfiable, then:

```text
μ(W^NAND_φ) ≥ B^NAND_φ + 1.
```

### Intended proof

The baseline tuple already forces B gates. If φ is satisfiable, then the final output:

```text
F_φ = z ∧ T_φ ∧ y_out
```

is nonconstant and depends essentially on the fresh final lock z. Since z appears nowhere in the baseline outputs, F_φ cannot equal a baseline output, constant, or projection. Therefore at least one additional NAND gate is needed to output F_φ.

### Hostile questions

1. Is F_φ nonconstant over the full carrier when φ is satisfiable?
2. Does F_φ depend essentially on z?
3. Is z guaranteed fresh and absent from every baseline output?
4. Could F_φ be a projection onto z under the satisfying trace?
5. The function is over all carrier variables, not under a fixed satisfying assignment. Is this distinction explicit?
6. Can an already existing baseline gate output be reused to compute F_φ despite z freshness?

### Required manuscript strengthening

Add lemma:

```text
FinalLockSeparation:
If φ is satisfiable, F_φ depends essentially on z, and no baseline output
depends on z. Hence F_φ is distinct from every baseline output and is not a
constant or projection. Therefore at least one additional NAND gate is required.
```

## Residual slack conclusion

Given:

```text
|W^NAND_φ| = B^NAND_φ + 4
```

and the threshold lower bounds:

```text
unsat: μ = B
sat:   μ ≥ B + 1
```

we get:

```text
Λ(W^NAND_φ) = |W| - μ(W) ≤ 4.
```

The satisfiable case is actually:

```text
Λ ≤ 3
```

if μ ≥ B + 1, but the theorem only needs ≤ 4.

## Round 1 verdict

The locked NAND theorem is not obviously false, but the manuscript should be strengthened before external mathematical review.

The highest-risk obligations are:

```text
1. TraceEquivalence.
2. ZeroOutputConvention / unsatisfiable-case equality μ = B.
3. DirectWireOutputLowerBound stated as an explicit lemma.
```

The most urgent prose patch is the unsatisfiable case: a reviewer will ask whether the identically-zero final output is free, shared, or counted.

## Recommended next manuscript patch

Add a short subsection after the locked NAND threshold statement:

```text
Output convention and threshold proof details.
```

It should contain exactly these lemmas:

```text
DirectWireOutputLowerBound
MacroDistinct
TraceEquivalence
ZeroOutputConvention
FinalLockSeparation
```

Then Theorem 17.2 should cite them in order.

## Recommended next code/audit patch

Create a small static checker or test surface that records these theorem obligations explicitly as named fields:

```text
BaselineCert.directWireOutputLowerBound = true
TraceCert.traceEquivalence = true
ThresholdCert.zeroOutputConvention = true
ThresholdCert.finalLockSeparation = true
```

The code already has structured derivation records. The next hardening patch should make these exact mathematical obligations first-class fields, with negative tests for each.
