# Checker no-circular-authority audit

This directory defines the declared checker-authority graph coordinate:

```text
PNP-CHECKER-AUTHORITY-GRAPH-2026-06-27-01
```

The machine-readable manifest is:

```text
checker-cycles/CHECKER_AUTHORITY_GRAPH.json
```

Run the audit with:

```bash
npm run checker:cycles
```

The audit consumes a freshly generated checker dependency graph and the declared authority graph. Static ES-module dependency edges are implementation evidence, not automatically authority edges. A static cycle becomes a soundness problem only when a checker conclusion is declared as an authority premise that can flow back into itself.

The accepted result proves the declared authority graph is acyclic:

```text
authorityGraphReady = true
noCircularAuthorityProved = true
fullStaticImportCycleFreedomProved = false
```

The audit rejects any authority cycle, unknown node, malformed edge, public-theorem activation, or attempt to claim static import cycle freedom.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
