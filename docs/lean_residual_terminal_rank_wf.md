# Residual terminal `RankWF`

`PNP.ResidualTerminalRankWF` reconstructs the fixed residual-rank order named
immediately after `RW-SaturatePositive` in the pinned manuscript. The
manuscript specifies a finite tuple, ordered lexicographically by:

1. witness type;
2. span type;
3. mode;
4. frontier defect;
5. projection defect;
6. saturation defect;
7. anchor count;
8. charge size;
9. profile size; and
10. canonical code.

The Lean type `TerminalResidualRank` is exactly that right-associated
ten-coordinate product of natural numbers. `TerminalResidualRank.mk`, the ten
named accessors, and `TerminalResidualRank.coordinates` expose the order
without allowing a caller to change its arity or priority.

## Checked order and termination

`terminalResidualRankWellFoundedRelation` nests Lean's kernel-checked
`Prod.lex` relation over `Nat.lt_wfRel` nine times. Its public proposition is
`TerminalResidualRank.LexLT`. The module proves:

- `terminalResidualRankLexLT_wellFounded`;
- accessibility of every rank;
- well-founded induction over the exact rank;
- a theorem witnessing strict descent at each of the ten priority positions;
- an executable Boolean comparison with true/false equivalence theorems; and
- `TerminalResidualRankDescent.sound`, so a descent claim must carry the
  proposition for its concrete before and after ranks.

The decision procedure is derived from the same nested `Prod.Lex` relation.
It does not accept a caller-supplied comparison, a Boolean-only termination
flag, or a well-foundedness certificate.

## Exact boundary

This milestone establishes the fixed rank domain, its exact priority order,
and `RankWF`. It does not map the current finite terminal routes into the
manuscript's complete global outcome system, prove that any existing route
strictly decreases this rank, establish route completeness, construct Package
E, remove the explicit positive premise from the finite composition, or prove
full manuscript-wide `SaturatePositive`, `BCELReady`, ZeroSlack, PCCMin,
polynomial runtime, SAT in P, or `P = NP`.

The source anchor is the pinned legacy report's residual routing discussion,
where `RW-SaturatePositive` is followed by the ten coordinates and the
well-founded lexicographic rank claim. The reconstruction intentionally stops
at that named theorem boundary.

## Reproduction

```bash
lake build PNP.ResidualTerminalRankWF
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalRankWFAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalRankWF.lean
node --test audits/lean-residual-terminal-rank-wf0.test.mjs
```
