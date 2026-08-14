# Lean residual terminal Packet charge surplus

`PNP.ResidualTerminalPacketChargeSurplus` formalizes the finite arithmetic
kernel of the pinned manuscript's Section 14 `R-ChargeSurplus` route.

## What is formalized

For arbitrary support- and replacement-charge types, finite ledgers, and
natural-valued weight functions, `TerminalPacketChargeSurplus` records an exact
occurrence pairing. Two list-permutation identities require every replacement
occurrence to appear in one matched pair and partition every support occurrence
between the pairing and an unmatched remainder. Every pair preserves weight,
and the remainder discloses at least one unmatched positive support charge.

Lean derives all of the following rather than accepting them as fields:

- the paired replacement and support totals are equal;
- the unmatched remainder has positive total weight;
- the replacement ledger is strictly shorter than the support ledger;
- replacement total weight is strictly smaller than support total weight; and
- exact NAND gate accounting plus independently proved semantic equivalence
  produces a genuine `StrictEquivalentGain` and strict residual descent.

The occurrence permutations preserve multiplicity. In particular, repeated
charge values do not allow a replacement to reuse a duplicate support
occurrence that is not actually present. The hostile regression checks both
that attack and an attempted ledger with no unmatched occurrence.

## Fail-closed boundary

This theorem is the generic charge-surplus kernel, not the complete Packet
realizer. The support and replacement ledgers, exact pairing, weight function,
gate-count identities, and semantic equivalence remain explicit proof-bearing
inputs. Lean does not yet construct a replacement circuit or charge ledger from
a Packet selector blueprint, establish selector faithfulness or compatibility,
or derive `BotHN`, `BotBUD`, or a lower-rank `BotSeed` when construction fails.

The milestone therefore does not close the HB blocker graph, prove encoded-size
or polynomial-runtime bounds, derive the grouped BN6 family from terminal data,
or complete global PkgC, ZeroSlack, or PCCMin. It is not unconditional
ZeroSlack, does not put CNF-SAT in P, does not remove a project assumption, and
does not prove `P = NP`.

## Reproduce the focused checks

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketChargeSurplusAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketChargeSurplus.lean
node --test audits/lean-residual-terminal-packet-charge-surplus0.test.mjs
```
