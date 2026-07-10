# Lean direct-wire NAND enumerator

`lean/PNP/NANDEnumerator.lean` provides a constructive finite enumerator for the typed direct-wire
syntax in `PNP.DirectWire`. It enumerates implementations at one exact triple of natural-number
widths:

```text
(input count, NAND-gate count, output count)
```

The milestone is syntactic. It does not decide semantic equivalence or compute a minimum circuit.

## Enumerated objects

The construction recursively enumerates:

- every index of `Fin n`;
- every source available before a gate: boundary inputs, both Boolean constants, and earlier gates;
- every ordered pair of available sources for one NAND gate;
- every intrinsically topological program of the exact gate count;
- every ordered output tuple of the exact output count; and
- every program/output implementation pair at the requested widths.

Gate inputs are deliberately ordered. Although Boolean NAND is commutative, the foundational syntax
has not been quotiented by commutativity, so both source orders are retained for literal syntactic
completeness.

The output enumerator uses a recursive typed tuple and converts it pointwise to
`DirectWireWord`. At output width zero it contains the unique empty tuple. Later public search or
minimum-size layers may impose a nonempty-output policy, but that policy is not baked into the
semantic foundation or this exact-width enumerator.

## Checked completeness boundary

Membership theorems show that every well-typed finite index, source, gate, program, recursive output
tuple, and candidate at the requested widths appears in the corresponding finite list. Every
existing `Program`/function-backed `DirectWireWord` pair has an enumerated reified candidate with
the same program and each ordered output source equal pointwise, without function extensionality.
The bounded enumerator uses `Fin (gateBound + 1)` and gives the corresponding dependent candidate
for every original implementation whose gate count is at most that inclusive bound.

The enumerator is constructed entirely in Lean 4.31 core. Every explicit declaration is checked
with:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPNANDEnumeratorAxiomAudit.lean
```

The workflow captures this transcript, rejects any `depends on axioms:` line, and requires the
complete expected set of clean audit results.

## Not established here

This enumerator does not claim:

- canonical ordering or duplicate-free enumeration;
- quotienting by NAND commutativity or any other circuit symmetry;
- a decision procedure for semantic equivalence;
- completeness modulo semantic equivalence at a size bound;
- a minimum-equivalent-circuit computation;
- compatible replacement or the global slack law;
- the locked builder, baseline, trace, threshold, or residual-band results;
- correspondence with the historical JavaScript search order; or
- SAT, `P = NP`, or release of a root theorem.

PR 6 can use the exact-width completeness result as the finite search substrate, but must separately
define semantic truth-table comparison, semantic filtering across bounded gate counts, minimum size, compatible
replacement, and the slack inequality.
