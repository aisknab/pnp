# Edward Savage Feedback Round 1: Locked NAND Reduction Boundary

Status: **actioned as a manuscript/reviewer-package clarification request**.

## Feedback summary

Edward Savage identified the following concern after the first private review pass:

```text
The proof should explain how the locked NAND construction applies to general NAND gate topologies. The direct-wire and locked-topology restrictions may have restricted the instance family back into a P-time-solvable subclass before the minimizer is applied. The claim would be strengthened by either a NAND generalization route or evidence that the locked problem remains NP-hard/SAT-hard.
```

## Triage

This is the correct attack surface. The intended proof route is not:

```text
solve arbitrary NAND minimization directly
```

The intended route is:

```text
Boolean formula/circuit
-> polynomial-time conversion to NAND circuit phi
-> polynomial-time locked construction (W^NAND_phi, B^NAND_phi)
-> threshold test mu(W^NAND_phi) > B^NAND_phi
-> SAT decision
```

Thus the needed bridge is a named locked-family SAT-hardness theorem:

```text
phi in SAT iff mu(W^NAND_phi) > B^NAND_phi
Lambda(W^NAND_phi) <= 4
```

and the map `phi -> (W^NAND_phi, B^NAND_phi)` must be polynomial-time and must not smuggle in the answer.

## Action

Add an explicit manuscript subsection:

```text
17.5 Locked-family SAT-hardness bridge
```

The new subsection should state that:

1. General NAND circuits enter only as source circuits in the reduction.
2. The locked topology is the reduction target, not an arbitrary post-hoc restriction.
3. The construction is uniform and polynomial-time.
4. The locked invariants hold for every source circuit.
5. The threshold equivalence gives SAT-hardness of the locked threshold family.
6. Residual slack is at most four uniformly.
7. The final SAT decision does not assume a minimizer for arbitrary NAND topologies.

## Follow-up review question

After patching, ask Edward to attack this exact bridge:

```text
Can the locked construction encode arbitrary SAT without accidentally enforcing a P-time-solvable subclass?
```

Concrete subchecks:

```text
1. Is phi -> W^NAND_phi polynomial-time?
2. Are all original input assignments represented?
3. Do trace/occurrence/lock slots preserve satisfiability iff?
4. Do duplicate source occurrences stay distinct before constraints are imposed?
5. Does unsat make the final output zero on the whole carrier, not only coherent traces?
6. Does sat force one extra nonconstant nonprojection final-lock output?
7. Does Lambda(W^NAND_phi) <= 4 hold uniformly?
```
