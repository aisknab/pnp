# Lean residual terminal Packet selector gain coverage

`PNP.ResidualTerminalPacketSelectorGainCoverage` isolates the exact missing
logical premise between an exhaustive scan of one explicit Packet selector
family and a global ZeroSlack conclusion.

## What is formalized

For arbitrary atom types, finite grouped BN6 families, direct-wire interfaces,
and current implementations, Lean now defines
`TerminalPacketSelectorGainCoverage`. Its `covers` field requires every
`StrictEquivalentGain current next` to be represented by:

- a canonical handle in the supplied family's selector universe;
- an original atom in that handle's exact source cell; and
- an equality identifying the atom payload with `next`.

Given this certificate, family-wide no-gain from the existing exhaustive scan
rules out every strict equivalent gain. The semantic stopping equivalence then
constructs a `ZeroSlackResult`, whose `sound` theorem proves that the current
reference residual slack is zero.

`scanCoveredPacketSelectorGains` retains the executable scan's successful
branch unchanged. Its only other branch carries that proof-bearing ZeroSlack
result. The corresponding residual specification therefore returns either an
original source atom with strict residual descent or a proof that the current
slack is zero.

The composed terminal theorem also retains the encoded pair, positive
balanced-triple, and full-span Packet alternatives literally.

## Fail-closed boundary

The coverage certificate is an explicit theorem premise. Lean does not infer
it from the existence of a finite grouped family or from scan failure. The
regression instantiates an empty selector family around the known positive-
slack redundant identity implementation: its scan is unresolved, but a
coverage certificate would have to produce an inhabitant of the empty handle
type and is therefore impossible.

This distinction matters. The theorem establishes a conditional
gain-or-ZeroSlack interface, not unconditional manuscript selector silence.
The repository still does not construct a faithful compatible selector family
covering every gain, derive the family from terminal data, construct replacement
circuits, bound the certificate or enumeration by encoded circuit size, prove
polynomial generation or runtime, produce the typed blocker and HB/rank
closure, or complete global PkgC, ZeroSlack, or PCCMin. It does not put CNF-SAT
in P, remove a project assumption, or prove `P = NP`.

## Reproduce the focused checks

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorGainCoverageAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorGainCoverage.lean
node --test audits/lean-residual-terminal-packet-selector-gain-coverage0.test.mjs
```
