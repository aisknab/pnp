# Lean checked Packet selector candidate-gain scan

`lean/PNP/ResidualTerminalPacketSelectorGainScan.lean` reconstructs the
gain-verification side of the next bounded Packet interface. For every
canonical selector code over an arbitrary finite explicit grouped BN6 family
whose payloads are direct-wire implementations, Lean selects the exact
original source cell and scans every candidate payload with the existing
executable strict-equivalent-gain checker.

The proof-bearing scan has exactly two local outcomes:

- an original source-cell payload atom carrying a genuine
  `StrictEquivalentGain`; or
- proof that no payload candidate in that selected cell is a strict equivalent
  gain.

Every successful gain therefore strictly decreases the existing residual-slack
measure. Malformed, trailing, and out-of-range selector codes fail closed
exactly when the canonical decoder rejects; an accepted code always produces a
scan, even when its internal result is local no-gain. Successful scans recover
the exact canonical input, source cell, and decoded footprint. The pair,
positive balanced-triple, and full-span Packet alternatives are preserved, with
one checked local scan at every selected footprint.

This is an input-relative candidate verifier, not the manuscript's complete
gain-or-blocker selector realizer. Candidate implementations and the grouped
family are supplied explicitly. Local no-gain excludes only candidates in one
selected source cell; it is not `BotHN`, `BotBUD`, a lower-rank `BotSeed`,
global minimality, or ZeroSlack. The module does not construct replacement
candidates, establish selector faithfulness or compatibility, connect payload
mass to charge surplus, derive or group survivors, prove an encoded-circuit-size
bound or polynomial generation/runtime, complete PkgC, ZeroSlack, or PCCMin,
put SAT in P, remove a project assumption, or prove `P = NP`.

Run the focused checks with:

```sh
lake env lean -DwarningAsError=true lean-audit/PNPResidualTerminalPacketSelectorGainScanAxiomAudit.lean
lake env lean -DwarningAsError=true lean-regression/PNPResidualTerminalPacketSelectorGainScan.lean
node --test audits/lean-residual-terminal-packet-selector-gain-scan0.test.mjs
```
