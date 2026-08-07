# Governed terminal projection square

`lean/PNP/ResidualTerminalProjectionSquare.lean` reconstructs the next
all-finite dependency edge in §3 of the pinned legacy manuscript. The
manuscript requires the completed support square to remain a square after a
forgetful profile projection. Lean now proves that structural law for every
finite direct-wire candidate, every explicit terminal dependency system,
every computed saturated support square, and every forgetful terminal
projection.

This is one theorem over all finite inputs, gates, outputs, profile
widths, candidates, systems, squares, and projections. It is not a sequence
of fixed profile coordinates or a repeatable finite-prefix milestone.

## Exact forgetful projection

`TerminalGovernedFrontier.project` retains the complete physical boundary and
interface of a governed frontier. In each of the ten terminal profile roles,
it filters the finite coordinate list by the projection's Boolean `keep`
function. Lean proves:

- the boundary and interface are unchanged;
- role membership is exactly original membership together with `Keeps`;
- duplicate freedom is preserved; and
- applying the same projection twice is idempotent.

A coordinate satisfying `Forgets` occurs in no projected role at any square
corner. No caller certificate, host lookup, or hard-coded coordinate is used.

## The commutative square

The projected join is compared with
`terminalProjectedGovernedFrontierPushout`. That construction reads only the
completed left and right corners. Its physical fields are the already proved
side-only boundary and interface gluing, while each role profile is the
side-profile union filtered by the projection. It never reads the completed
join corner.

For every computed saturated support square, Lean proves:

- every projected corner keeps its exact computed physical frontier;
- the projected meet role is exactly the overlap of the projected side roles;
- the projected join role is exactly the union of the projected side roles;
- the independently completed and projected join equals the side-only
  projected pushout; and
- the whole statement is packaged by
  `TerminalSaturatedSupportSquare.governed_projection_compatible`.

Thus completion and gluing commute with every explicit forgetful terminal
projection at this structural frontier level.

## Legacy anchor and remaining boundary

This closes the §3 projection-commutation edge immediately after governed
frontier pushout. It keeps the manuscript's carrier conventions and
dependency order: physical ports come from the actual direct-wire program,
profile coordinates retain their computed terminal roles, and the terminal
dependency system remains explicit input.

The result is structural. It does not prove that a square was produced by the
later BN2 construction, that its four local minima are side-tight, that the
square is legitimate for the manuscript's contradiction, or that projection
creates positive slack. In particular, it does not prove BN2 square
legitimacy, `SaturatePositive`, `BCELReady`, complete obstruction routing,
ZeroSlack, PCCMin, polynomial runtime, SAT in P, or P = NP. Those remain
downstream obligations.

## Audit and reproduction

The closed audit covers all 20 public declarations in the module plus 13
reused projection, frontier, completion, and pushout interfaces. The only
permitted closure is the approved Lean-standard set `propext` and
`Quot.sound`. Project axioms, `Classical.choice`, `sorry`, `admit`, native
decision shortcuts, host lookup, and caller certificates are rejected.

```text
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalProjectionSquareAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalProjectionSquare.lean
node --test audits/lean-residual-terminal-projection-square0.test.mjs
```

The generated inventory, publication-map, status, TeX, PDF, size, hash, and
coordinate evidence was recorded only after the compiled source and
expectation chain stabilized:

- inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-07-110`, with
  24,675 declarations, 13,260 theorems, 6,984 assumption-free theorems,
  2,316 reviewed milestone candidates, 226 source-closure modules,
  15,168,239 bytes, and SHA-256
  `2e585d493c1b5364f0bf340b7d141bbb231bef97d609056909f19481c77e45c9`;
- publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-07-110`,
  with 90 milestones, 87 earned milestones, 2,316 exact theorem pins,
  750,275 bytes, canonical-object SHA-256
  `94f46541a5e524e9b4989cf28331c74456c52d41098b5a2634c8cf2a8c11fc17`,
  and file SHA-256
  `20d29d0d85e4edd2ee0ab1cfbe41f403e17b2655ea82651ffeb089c0fe88372b`;
- Lean source-closure SHA-256
  `77155b9e3cd7ba5c931ccd20f587cb5aa0567e1b016b37845d904eec4205426d`;
- status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-07-110`,
  with byte-identical 1,867,836-byte status mirrors and SHA-256
  `a411b2dae18d3869cea0ba236628604e9041f06010553d1e0cfc8b2434cef805`;
- canonical TeX with 195,614 bytes and SHA-256
  `51e174f1cbff5030a905ce6e791741a0f69facb1500acfad3b6b1c72ccdea641`;
  and
- deterministic 77-page A4 PDF with 436,374 bytes and SHA-256
  `ed75cd52e1a5bb6a143838fa7a86f0d9a88ad66e9f1d039413fab5dc671690ad`.

The publication gate remains false, all four project assumptions and six
blockers remain explicit, activation fingerprints remain unset, and
`PNP.Main.p_eq_np` remains absent.
