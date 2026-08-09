# Computed terminal BCEL anchor nucleus and cut-square dichotomy

## Result

`PNP.ResidualTerminalBCELAnchorNucleus` turns one computed governed,
proper-positive terminal support into a finite, deterministic BCEL anchor
problem. The input contains only the existing proof-bearing support, one
explicit forgetful projection, and one executable ambient observer. The
module computes the canonical anchor universe from the saturated support and
enumerates every order-preserving anchor subfamily.

`findTerminalPositiveAnchorNucleus` selects the first minimum-cardinality
subfamily with positive projection defect. Its proof-bearing result records
membership, positivity, and zero defect for every strictly smaller governed
subfamily. The search is total: `none` is equivalent to zero defect on every
enumerated family, and a positive whole family forces a unique returned
nucleus.

## Exact fail-closed boundary

For a computed nucleus, Lean performs three finite scans in a fixed order:

1. every pair of anchor subfamilies and every primitive record is checked for
   exact intersection/meet and union/join membership;
2. every oriented nonempty proper cut is checked for zero meet, left, and
   right projection defects and nucleus defect at the join; and
3. every proper cut is checked for the first local optimum-coherence route,
   with full mode before quotient mode.

Each failing branch retains the exact first query and a soundness proof. The
additional cut-defect branch is deliberately fail-closed: membership algebra
alone does not assume that two extensionally equal seed families produce the
same carrier corner. The carrier defects themselves are recomputed before a
successful result is admitted.

`classifyTerminalBCELAnchorNucleus` therefore returns exactly one of:

- a positive nucleus with fewer than two anchors;
- the first Boolean anchor-algebra mismatch;
- the first proper-cut defect mismatch;
- the first proof-bearing local cut route; or
- `TerminalComputedBCELAnchorNucleus`.

There is no caller-supplied anchor list, algebra certificate, cut certificate,
route-silence flag, or host-side selection.

## Successful cut conclusion

On the successful branch, every oriented nonempty proper cut has a
`TerminalComputedBCELCutConclusion`. It contains computed BN2 square
legitimacy, the three zero side defects, the join defect equal to the nucleus
defect, the exact constant-cut equation, strictly positive projection excess,
and the complete local full-and-quotient BN2 conclusion.

The main public projections state that:

- every strictly smaller governed anchor subfamily has zero defect;
- the nucleus has at least two anchors;
- every proper cut has projection excess equal to the positive nucleus
  defect; and
- every proper cut has the complete local BN2 conclusion.

## Trust and boundary

The dedicated 79-line axiom transcript covers all 68 explicit public
declarations plus the eleven reused finite-enumeration, route, BN2, and
constant-cut dependencies. The hostile audit rejects project axioms,
`Classical.choice`, `sorry`, `admit`, native or SAT shortcuts, host lookup,
caller certificates, noncanonical anchor or cut enumeration, reordered
failure scans, weakened defect identities, and widened global claims.

The regression uses finite NAND fixtures to exercise minimum two-anchor
selection, the insufficient-nucleus branch, a shared-dependency algebra
failure, and a full-mode cut route. All observers are executable functions on
the actual ambient implementation.

This milestone assumes a positive whole-support projection defect. It does
not derive that premise, derive the terminal dependency system from an
arbitrary circuit, identify manuscript activation or charge equivalence
classes absent from the terminal model, connect a local failure to the
complete global no-outcome route system, prove `SaturatePositive`, Package E,
`BCELReady`, later BCEL/BN2--BN6 conclusions, ZeroSlack, PCCMin, polynomial
runtime, SAT in P, remove a project assumption, or prove P = NP.

## Verification

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBCELAnchorNucleusAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBCELAnchorNucleus.lean
node --test audits/lean-residual-terminal-bcel-anchor-nucleus0.test.mjs
npm run formal:inventory:check
npm run formal:publication:check
npm run report:check
```

The root import, workflow, compiled theorem inventory, publication map,
reconstruction status, canonical report, and public mirrors are verified as
one release surface.
