# Computed terminal BN2 square legitimacy

## Result

`PNP.ResidualTerminalBN2SquareLegitimacy` packages the structural and local
quantity boundary needed by the pinned manuscript's BN2 square argument. For
every finite terminal support square computed from two seeds under one
explicit terminal dependency system, one direct-wire candidate, and one
forgetful terminal projection, Lean now constructs a proof of computed BN2
square legitimacy.

The structural proof records, on the same four computed corners:

1. governed and physical compatibility at meet, left, right, and join;
2. exact meet intersection and join union for all ten profile roles;
3. the exact governed frontier pushout, including physical internalization;
4. commutation of the forgetful projection with the square; and
5. one carrier-compatible family of full and quotient minimum quantities.

No caller supplies a corner list, transport certificate, legitimacy flag, or
host-computed quantity. The proof is assembled from the existing executable
saturation, completion, frontier, carrier, optimum, and maximum APIs.

## Local BN2 conclusion

`TerminalComputedBN2SquareQuantities` fixes one observer and retains the
carrier's projection, reference minima, signed projection-transfer identity,
and canonical full and quotient optima on that same carrier.

`TerminalComputedBN2LocalConclusion` then states the exact local no-route
branch. Under `NoOptimumCoherenceRoutes`, it contains:

- the computed legitimacy and shared quantity package;
- a side-tight coherent full optimum tuple;
- a side-tight coherent quotient optimum tuple; and
- the complete tight-family signed maximum equal to the corresponding delta
  in both modes.

The unconditional
`TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute` theorem is
fail-closed. It checks the full coherence query first and the quotient query
second. It returns either the complete local conclusion or the first selected
proof-bearing routed failure. The quotient-promotion firewall remains a
separate later query and is not silently folded into this local dichotomy.

This closes the scoped dependency

```text
computed saturated square
  -> exact governed frontier and projection square
  -> common carrier and shared optimum quantities
  -> local route silence
  -> coherent side-tight tuples and exact tight-family maxima in both modes
```

## Main interfaces

The public proof objects are:

- `TerminalComputedBN2SquareLegitimate`;
- `TerminalComputedBN2SquareQuantities`; and
- `TerminalComputedBN2LocalConclusion`.

Their canonical constructors are:

- `TerminalFourCornerCarrier.computedBN2SquareLegitimate`;
- `TerminalFourCornerCarrier.computedBN2SquareQuantities`;
- `TerminalFourCornerCarrier.computedBN2LocalConclusion`; and
- `TerminalFourCornerCarrier.computedBN2LocalConclusionOrFirstRoute`.

The projection, profile, reference-minimum, and transfer-identity accessors
keep the exact underlying carrier data visible instead of replacing it with a
weaker existential summary.

## Trust and boundary

The dedicated transcript prints the axiom closure of all 15 public
declarations and eight reused dependencies. Every printed declaration closes
using only Lean's `propext` and `Quot.sound` where required. The hostile audit
rejects project axioms, `Classical.choice`, `sorry`, `admit`, native or SAT
shortcuts, host lookup, caller certificates, weakened frontier equations,
mode swaps, and promotion-firewall leakage.

The regression exercises both branches: a coherent finite NAND square gives
the complete full-and-quotient local result, while an open obligation produces
the exact proof-bearing full-mode failure.

This milestone does not derive the terminal dependency system from an
arbitrary circuit, prove universal local route silence, connect a local
failure to the complete global no-outcome route system, identify a BCEL anchor
square, prove `SaturatePositive`, Package E, `BCELReady`, ZeroSlack, PCCMin,
polynomial runtime, SAT in P, remove a project assumption, or prove P = NP.

## Verification

The durable checks are:

```bash
lake build PNP
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalBN2SquareLegitimacyAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalBN2SquareLegitimacy.lean
node --test audits/lean-residual-terminal-bn2-square-legitimacy0.test.mjs
npm run formal:inventory:check
npm run formal:publication:check
npm run report:check
```

The root import, workflow, compiled theorem inventory, publication map,
reconstruction status, canonical report, and public mirrors are verified as
one release surface.
