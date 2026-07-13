# Blank-materialization equivalence

`lean/PNP/Concrete/TapeBlankEquivalence.lean` gives a constructive relation
between finite `Tape` values that denote the same infinite blank-extended
tape. Two tapes agree when their focused cells agree and every indexed cell
on both finite side lists agrees after missing cells are read as blank.

The relation is reflexive, symmetric, and transitive. It is preserved by
write, left/right/stay movement, one raw transition, and every bounded raw
run. Blank-delimited `Tape.outputBits` is identical on related tapes. Every
declaration printed by
`lean-audit/PNPConcreteTapeBlankEquivalenceAxiomAudit.lean` has empty axiom
closure.

`rawInputWorkTape` packs arbitrary raw input into two-cell work symbols. For
empty and odd inputs the work representation materializes a blank cell that
is implicit in `Tape.ofInput`; for positive even inputs the representation is
structurally exact. The theorem
`startConfig_compileWorkMachine_blankEquivalent` covers all three cases and
supplies the ordinary-input bridge needed by a future total input framer.

## Verification

```sh
lake build PNP
lake env lean -DwarningAsError=true \
  lean-audit/PNPConcreteTapeBlankEquivalenceAxiomAudit.lean
lake env lean -DwarningAsError=true \
  lean-regression/PNPConcreteTapeBlankEquivalence.lean
node --test audits/lean-concrete-tape-blank-equivalence0.test.mjs
```

## Exact boundary

This module contains no executable framing rules and does not alter the
canonical-pair-only compiler. It does not construct a function or decision
`RawRefinement`, discharge `Formal.ConcreteComplexityMachineLink`, prove
CNF-SAT in P or NP-completeness, or establish P = NP. All seven formal
blockers, four project assumptions, and the false publication gate remain.
