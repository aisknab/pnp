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
`cnfWorkDecide` with `checkEncodedCertificate`. A green guard means no mismatch
was found in that finite universe; it does not replace the universal
operational-correctness proof.
