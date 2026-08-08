# Checked four-corner optimum carrier compatibility

`lean/PNP/ResidualTerminalFourCornerOptimumCompatibility.lean` reconstructs
the legacy report §11.1 dependency named
`fourCornerOptimaCarrierCompatible`. It uses the computed terminal support
square from §3 and the previously checked carrier transport as its only new
import.

The preceding milestone put the meet, left, right, and join corners into one
structural carrier. This milestone puts the independently defined full and
quotient optimum realizers into one reversible common ambient implementation
type. It proves that moving a corner into that type and back preserves its
semantics and exact gate count. It then compares all four corners under one
observer and one quotient projection.

## Canonical ambient coordinates

Each original input and each original gate output has a unique physical wire
coordinate. `TerminalSupportWire.ambientIndex` embeds both kinds of wire into
`Fin (inputs + gates)`, with inputs first and gate outputs second.
`terminalSupportWireAt` is its constructive inverse. Lean proves both inverse
laws and injectivity for arbitrary finite input and gate counts.

Each corner still has its own exact boundary and interface widths. The carrier
therefore exposes fail-closed lookup functions:

- `boundaryIndex?` returns the exact boundary index or `none`;
- `interfaceIndex?` returns the exact interface index or `none`;
- present coordinates are recovered at their unique list position; and
- coordinates outside a corner are never given a fabricated local position.

The proofs use the existing duplicate-free endpoint theorems. They do not use
a caller-provided index map, host-side search result, permutation, or
certificate.

## Faithful ambientization and localization

`ambientizeCandidate` renames one corner boundary into the common ambient
input universe. Outputs at producers in that corner interface retain the exact
local semantics. Every other ambient gate-output position is fixed to
`false`.

`localizeCandidate` runs the inverse operation. It substitutes the corner's
zero-gate boundary adapter for ambient inputs and selects exactly the corner's
interface outputs. The substitution is defined structurally for sources,
gates, programs, and output words. Lean proves its semantics rather than
assuming a substitution law.

For every finite candidate and corner, the checked results include:

- present ambient outputs have the original corner semantics;
- absent outputs are exactly `false`;
- localization after ambientization is semantically equivalent to the
  original candidate;
- both directions preserve the exact gate count; and
- semantic equivalence transports through both operations.

These two directions prove
`ambient_referenceMinimum_eq_corner`: the exhaustive semantic reference
minimum in the ambient type equals the exhaustive reference minimum in the
original corner type. The proof establishes both inequalities. It cannot gain
a cheaper realization by adding unused ambient coordinates, and it cannot
lose a cheaper realization by restricting back to the exact boundary and
interface.

## One observer, one projection, four optima

`ambientProfileSystem` retains the role map from the computed saturation
system. Its observation function is explicit executable data. It is not a
compatibility certificate.

`optimizationCorners` places all four ambient implementations into one
`TerminalProjectionFourCorners` value:

- all four use the same ambient input and output types;
- all four use the same observation function;
- the role map is definitionally the saturation system's role map; and
- all four use the carrier's one forgetful projection.

`canonicalOptimumFamily` invokes the existing exhaustive full and quotient
minimum constructions on that one family. Each resulting realization is then
localized back to its exact extracted corner. Lean checks that all eight local
realizers, full and quotient at meet, left, right, and join, retain the exact
minimum gate counts computed in the shared ambient family.

The universal theorem
`TerminalFourCornerCarrier.fourCornerOptimaCarrierCompatible` packages:

- the previously checked structural carrier compatibility;
- exact ambient-to-corner reference-minimum equality at every corner;
- exact canonical full and quotient size vectors;
- exact localized full and quotient minimum gate counts at every corner; and
- the shared role map and shared projection.

It quantifies over every finite computed saturated terminal support square and
every explicit observer of the required type. It is not a list of selected
coordinates or a fixed four-corner example.

## Proof, regression, and hostile checks

The dedicated axiom transcript audits all 47 new public declarations and ten
reused carrier, minimum, equivalence, and basis interfaces. The approved
compiled closure is limited to Lean's logical infrastructure. The audit
rejects project assumptions, `Classical.choice`, `sorry`, `admit`, native or
SAT shortcuts, host lookup, and caller-supplied certificates.

The regression uses a nonempty one-input, three-gate square whose four corners
have different boundary widths. It checks both wire constructors, successful
and failed boundary and interface queries, present and absent ambient outputs,
the localization round trip, all-corner reference-minimum equality, the
retained and forgotten projection coordinates, both sets of localized
minimum counts, and an empty square at every corner.

The hostile audit alters the physical coordinate embedding, swaps the inverse,
forces absent queries to succeed, changes missing outputs from `false`, changes
localization, removes one inequality, replaces the derived role map or shared
projection, substitutes one corner for another, weakens the compatibility
contract, and removes final proof fields. It also injects assumptions, project
axioms, host lookup, caller certificates, proof shortcuts, private declarations,
and downstream overclaims. Every mutation must be rejected.

The focused commands are:

```bash
lake build PNP.ResidualTerminalFourCornerOptimumCompatibility
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalFourCornerOptimumCompatibilityAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalFourCornerOptimumCompatibility.lean
node --test audits/lean-residual-terminal-four-corner-optimum-compatibility0.test.mjs
```

## Generated publication evidence

Inventory coordinate `PNP-LEAN-THEOREM-INVENTORY-2026-08-08-112` records
24,934 declarations, 13,352 theorem-kind declarations, 7,015 assumption-free
theorems, 14,691 excluded private declarations, 228 source-closure modules,
and 2,352 reviewed milestone candidates. Its 15,824,195 canonical bytes have
SHA-256
`10ca3467d9c899300ac9c76c84ce62f87c8157e73fc39f8af82b203a4be9a8eb`;
the exact Lean source closure has SHA-256
`3161b45bbf5468a66e86fac1cf8dd6bef3ea19b1d472c536a620695085e589d1`.

Publication-map coordinate `PNP-FORMAL-PUBLICATION-MAP-2026-08-08-112`
contains 92 milestones: 89 earned and three deliberately unearned. Its
761,711 bytes pin 2,352 exact kernel theorem types. The canonical object has
SHA-256
`2bab8fea8dbd56ee8594ceb2c5335efa7f8dd935fb11ff00f944c4c252b239c2`
and the file has SHA-256
`8404f2c2b178d87c42f4501b4490286c90da593281dad2708297c22b0fbfa9df`.

Status coordinate `PNP-FORMAL-RECONSTRUCTION-STATUS-2026-08-08-112`, paired
with public-surface coordinate
`PUBLIC-SURFACE-BASELINE-2026-08-08-RESIDUAL-TERMINAL-FOUR-CORNER-OPTIMUM-COHERENCE-111`,
has byte-identical 1,901,511-byte status mirrors with SHA-256
`e0515fe3af9c24f155165f172f2f00c1bbcff21822b5479141183262cf34b8d5`.
Canonical report coordinate
`PNP-CANONICAL-FORMAL-RECONSTRUCTION-REPORT-2026-08-08-112` has a
197,818-byte TeX source with SHA-256
`550fa4769b476b52cae5df3efa912a925b9e4c6d1460fe6a601d060e4a810f72`
and a deterministic 77-page, 437,284-byte A4 PDF with SHA-256
`0e30911e395f6054e968b2ac0de1a27cf9bb2e77a182e6744ac37407dd1de058`.

The concrete publication gate remains false. All four project assumptions,
all six blockers, unset activation fingerprints, and the absence of
`PNP.Main.p_eq_np` remain explicit.

## Boundary still open

This milestone closes the carrier-compatibility dependency named in §11.1. It
does not prove coherent transport of the four optimum realizers along the
square legs. It does not prove `sideTightCompletionExists`, construct the
coherent four-corner optimum required by `BN2-CoherentOptimum`, establish BN2
square legitimacy, or derive the terminal dependency system used by the later
replacement argument.

It also does not prove `SaturatePositive`, Package E, `BCELReady`, complete
obstruction routing, ZeroSlack, PCCMin, polynomial runtime, SAT in P, removal
of a project assumption, or P = NP. Those remain separate downstream proof
obligations.
