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

- inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-111`, with
  24,758 declarations, 13,298 theorems, 6,989 assumption-free theorems,
  2,341 reviewed milestone candidates, 227 source-closure modules,
  15,645,082 bytes, and SHA-256
  `ea373cfe65d8c99fab5c3896b7d594f96724a8eab2b3d2b7ddf0abdfee81aabe`;
- publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-111`,
  with 91 milestones, 88 earned milestones, 2,341 exact theorem pins,
  757,472 bytes, canonical-object SHA-256
  `8c208bb3815b2513a3a167dd72adf77903c5a1f1d5c75e590e8064448a309737`,
  and file SHA-256
  `8efcfb683a0aeb7f2b6884bf6374493b3e69c20f6bb5617d2e63252646b384d6`;
- Lean source-closure SHA-256
  `55b94c1f15c1003306e4efcf83469416817e29530e7eae8a25aa4948efa9d370`;
- status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-111`,
  with byte-identical 1,887,604-byte status mirrors and SHA-256
  `72d754abc757743f41696680d14a795d973fe86285fd93aa61ef322d65062a5f`;
- canonical TeX with 196,791 bytes and SHA-256
  `55ffa6aa19ba0c1c3143265d21ac3e481b05556a38f2d9b62591245078b0e492`;
  and
- deterministic 77-page A4 PDF with 436,878 bytes and SHA-256
  `121978e29f6f37caf842fe8ad76c6ce7e8812bc1bbb7c018f068d5247e23e431`.

The publication gate remains false, all four project assumptions and six
blockers remain explicit, activation fingerprints remain unset, and
`PNP.Main.p_eq_np` remains absent.
