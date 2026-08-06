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

- inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-06-108`, with
  24,485 declarations, 13,183 theorems, 6,956 assumption-free theorems,
  2,279 reviewed milestone candidates, 224 source-closure modules,
  14,930,297 bytes, and SHA-256
  `17abf9c431e40fc2775fde868ff9312acf8db37907aa4a5ca64d5aa5c41e75d0`;
- publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-06-108`,
  with 88 milestones, 85 earned milestones, 2,279 exact theorem pins,
  738,472 bytes, canonical-object SHA-256
  `ebfc3498be3d1d4b22c2a2389084869dda23f96a66bf9cf8ffa94aa58cab4d8f`,
  and file SHA-256
  `4b1ba7361fbb2dbbd103a14d848248d1729ad2305a86746021955c183ddc7ccb`;
- Lean source-closure SHA-256
  `54ced1d99c5c88c2580956e2b065101f45cbaef8c41de40f0996a3bf74ca0d3a`;
- status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-06-108`,
  with byte-identical 1,832,643-byte status mirrors and SHA-256
  `8e7e4c01da163413c95ca7bf3b096754bf88b8748f782c72d59ed96c0f7fde6f`;
- canonical TeX with 193,376 bytes and SHA-256
  `422b680daefa772e192eb47fa6fbb826e890b35563a94e05d0bca32da8ad82db`;
  and
- deterministic 76-page A4 PDF with 434,491 bytes and SHA-256
  `edf229a4f5e7c6006fed6bb93774a6ba82de413f288cb6cb0ea5f189aa91d36d`.

The publication gate remains false, all four project assumptions and six
blockers remain explicit, activation fingerprints remain unset, and
`PNP.Main.p_eq_np` remains absent.
