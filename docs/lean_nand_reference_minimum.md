# Lean exhaustive direct-wire reference minimum

This milestone makes semantic equivalence and minimum gate count executable for the finite
direct-wire NAND syntax. Every declaration in the four modules is checked by a dedicated
`#print axioms` transcript.

## What is proved

`NANDTruthTable.lean` represents a valuation as a recursive `BoolTuple`, enumerates all tuples, and
checks every output position. The theorem `equivalentBool_eq_true_iff` connects the executable
Boolean result to pointwise `DirectWire.Equivalent` without classical choice or function
extensionality.

`NANDMinimum.lean` packages an implementation with its exact gate count and searches exact sizes
in increasing order from zero through the target size. The target itself makes this bounded search
nonempty. The selected `referenceMinimum` has an equivalent `referenceMinimumWitness`, is no
larger than the target, and is no larger than every semantically equivalent candidate at any gate
count. It is invariant under semantic equivalence. `residualSlack` is target size minus that
minimum, and `residualSlack_eq_zero_iff_minimum` proves zero slack exactly at semantic minimum.

`NANDComposition.lean` constructs serial composition and a concrete `FramedContext`. Its
`compatibleReplacement_framed` theorem says that replacing the support block by a semantically
equivalent implementation preserves the semantics of that concrete composed circuit.
`NANDSlack.lean` specializes the reference minimum to that frame and proves the corresponding
framed additive global-slack identity.

## Scope boundary

The minimum is an exhaustive finite reference definition. The development proves no polynomial,
quasipolynomial, or practical runtime bound for enumeration, truth-table comparison, or minimum
search. It does not implement the report's residual-band minimizer.

The replacement and slack results apply to the explicit serial frame represented by
`FramedContext`. They do not quantify over arbitrary internal support subsets or support profiles,
and they do not establish the historical locked-NAND global replacement claim. The machine status
therefore keeps `leanCompatibleReplacementFormalized` and `leanGlobalSlackLawFormalized` false,
while recording the narrower framed results separately.

## Verification

```sh
node --test audits/lean-nand-reference-minimum0.test.mjs
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPNANDTruthTableAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPNANDMinimumAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPNANDCompositionAxiomAudit.lean
lake env lean -DwarningAsError=true lean-audit/PNPNANDSlackAxiomAudit.lean
```

These checks establish the stated direct-wire results only. They do not establish SAT in P or
`P = NP`.
