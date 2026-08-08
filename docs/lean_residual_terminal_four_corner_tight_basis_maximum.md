# Complete terminal four-corner tight-basis maximum

## Result

`PNP.ResidualTerminalFourCornerTightBasisMaximum` reconstructs the remaining
local maximum in the `BN2-CoherentOptimum` paragraph of Section 11.1 of the
pinned legacy manuscript. For every finite computed terminal support square,
explicit observer, and selected full or quotient mode, Lean now constructs the
complete finite family of implementations that:

1. attain the exact profile-constrained minimum at every corner;
2. pass the independently recomputed four-corner coherence query; and
3. therefore have the selected signed incidence value.

When the existing exact local coherence route is silent, the family contains
the canonical basis and its signed maximum is exactly the selected delta. The
maximum is an `Option Int`. It has no artificial zero seed, so a nonempty
family whose values are negative retains its true negative maximum.

## Why this is an unbounded mathematical step

The theorem is quantified over every finite support square, observer, mode,
corner, implementation, and bounded candidate enumeration. It does not add
another fixed corner coordinate or one more hard-coded basis. Each corner
enumerates every exact candidate up to the gate count of the existing ambient
implementation, proves that this bound contains every minimum, and filters to
all implementations at the computed minimum. The four complete lists are then
crossed and filtered by the generalized coherence query.

This closes the local manuscript dependency

```text
complete exact corner minima
  -> complete four-corner tight family
  -> signed maximum over that family
  -> selected delta under local route silence
```

The quotient-to-full promotion query remains separate and is not used by the
quotient maximum theorem.

## Main interfaces

The executable data are:

- `TerminalFourCornerImplementationBasis` with named `at` and `sizes`
  projections;
- `TerminalOptimumCoherenceMode.minimumSizes`, `delta`, and
  `profileMatchBool`;
- `TerminalProjectionFourCorners.minimumImplementationsAt` and
  `minimumImplementationBases`;
- `TerminalFourCornerCarrier.tightBasisBool`, `tightBasisFamily`,
  `tightBasisValues`, and `tightBasisMaximum?`;
- `TerminalFourCornerCarrier.firstBasisCoherenceFailure?`, which generalizes
  the earlier canonical query to an arbitrary four-corner implementation
  family without accepting a coherence certificate.

The central exactness theorems are:

- `mem_minimumImplementationsAt_iff`;
- `mem_minimumImplementationBases_iff`;
- `mem_tightBasisFamily_iff`;
- `canonicalImplementationBasis_mem_tightFamily`;
- `tightBasis_incidenceValue_eq_delta`;
- `mem_tightBasisValues_eq_delta`;
- `tightBasisMaximum?_eq_delta`;
- `tightBasisMaximum?_full` and `tightBasisMaximum?_quotient`.

The regression includes a NAND implementation whose two inputs are swapped,
so the family machinery is exercised with an alternative semantic minimum in
addition to the canonical implementation. It also checks
`signedMaximum? [-5, -2, -9] = some (-2)` and the empty-list result `none`.

## Trust and boundary

The dedicated axiom transcript covers every public declaration in the new
module, the generalized coherence interface, and the reused finite-enumerator,
minimum, tightness, and route interfaces. The permitted closure is limited to
Lean's `propext` and `Quot.sound` where required. The audit rejects project
axioms, `Classical.choice`, `sorry`, `admit`, native or SAT shortcuts,
host-side lookup, and caller-supplied certificates.

This result is conditional on the already computed local route being silent.
It does not prove universal route silence, BN2 square legitimacy, the global
no-outcome route system, the terminal dependency extraction theorem,
`SaturatePositive`, Package E, `BCELReady`, ZeroSlack, PCCMin, polynomial
runtime, SAT in P, removal of any project assumption, or P = NP.

## Verification

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFourCornerTightBasisMaximumAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFourCornerTightBasisMaximum.lean
node --test audits/lean-residual-terminal-four-corner-tight-basis-maximum0.test.mjs
npm run formal:inventory:check
npm run formal:publication:check
npm run report:check
```

The root import, durable workflow, generated theorem inventory, formal
publication map, reconstruction status, TeX report, PDF report, and public
mirrors are checked together before publication.
