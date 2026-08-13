# Lean exhaustive Packet selector-universe gain scan

`lean/PNP/ResidualTerminalPacketSelectorUniverseGainScan.lean` reconstructs the
next bounded selector-oracle edge from pinned manuscript Sections 14 and 15.
For every arbitrary finite explicit grouped BN6 family whose payloads are
direct-wire implementations, Lean enumerates every canonical input-relative
selector handle and runs the existing proof-bearing source-cell candidate scan
at each handle.

The complete scan has exactly two outcomes:

- one canonical handle and an original atom in its exact source cell carrying a
  genuine `StrictEquivalentGain`; or
- proof that no original payload behind any canonical selector in the supplied
  family is a strict equivalent gain.

Every successful gain has a canonical accepted code, retains exact source-cell
and decoded-footprint membership, and strictly decreases residual slack. The
pair, positive balanced-triple, and full-span Packet alternatives are retained
literally alongside the same exhaustive scan.

This is family-wide no-gain for one supplied input-relative selector universe,
not manuscript selector silence. The grouped family and candidate
implementations remain explicit inputs. The unresolved outcome is not a
manuscript `BotHN`, `BotBUD`, or lower-rank `BotSeed`; it does not establish
selector faithfulness or compatibility, global minimality, or ZeroSlack. The
module does not construct replacement candidates, connect payload mass to
charge surplus, derive or group survivors from terminal data, bound the family
by encoded circuit size, prove polynomial enumeration or runtime, complete
PkgC, ZeroSlack, or PCCMin, put SAT in P, remove a project assumption, or prove
`P = NP`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorUniverseGainScanAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorUniverseGainScan.lean
node --test audits/lean-residual-terminal-packet-selector-universe-gain-scan0.test.mjs
```
