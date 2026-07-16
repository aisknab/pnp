# Lean bounded regressions

These files are executable finite regressions, not theorem proofs. They are
kept outside the default `PNP` build and CI path when their exhaustive runtime
would make the main feedback loop impractical.

Run the CNF work-machine differential check with:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFWorkExhaustive.lean
```

The check enumerates all 511 bit strings of length at most eight on both sides
of the formula/certificate pair and compares 261,121 executions of
`cnfWorkDecide` with `checkEncodedCertificate`; every timeout is treated as a
failure. This universe exercises framing and width handling but contains no
encoded clause (the shortest formula containing a clause is nine bits, and a
one-literal formula is fifteen bits). A green guard therefore means only that
no mismatch or timeout was found in that finite universe; it does not replace
the systematic canonical-clause regression or the universal operational-
correctness proof.

Run the composed Cook--Levin first-token prefix regression with:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCookLevinBuilderFirstTokenPrefix.lean
```

Its finite examples exercise empty, one-bit zero/one, odd/even, all-zero, and
all-one source words; exact work and raw-polynomial values; the literal bridge;
the final represented tally workspace containing `T`; disjoint state images;
malformed prefix/appender phases; a stuck prefix reject image; and one-step-short
fuel. The universal behavior is established by the Lean theorems in the main
module, not by this finite case list.

Run the targeted canonical CNF regression with:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteCNFWorkCanonical.lean
```

It checks 620 small canonical formulae against all 15 assignments of length at
most three, for 9,300 pairs. The family reaches clauses, literals, both signs,
in-range and out-of-range indices, empty clauses, and one- and two-clause
formulae. Any timeout is an explicit failure. This remains finite evidence,
not a universal proof.

Run the work-compiler boundary regression with:

```sh
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteWorkCompilerEdges.lean
```

Its ten cases exercise exact six-step compilation for all three head moves,
including implicit blank work symbols at the left and right tape boundaries.
It is a focused executable regression, not the universal compiler-simulation
theorem.

Run the extended canonical sweep with:

```sh
lake env lean -DwarningAsError=true --run \
  lean-regression/PNPConcreteCNFWorkCanonicalExtended.lean
```

This opt-in executable checks 2,668 formulae against 15 assignments, or 40,020
pairs. It adds every one-clause word of length at most three to the systematic
family and exits with an error on either a semantic mismatch or a timeout. It
is still finite regression evidence, not a universal proof.
