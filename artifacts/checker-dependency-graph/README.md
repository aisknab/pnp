# Checker dependency graph artifacts

The checker dependency graph generator writes the latest generated graph artifacts here:

```text
artifacts/checker-dependency-graph/checker-dependency-graph.json
artifacts/checker-dependency-graph/checker-dependency-graph.dot
artifacts/checker-dependency-graph/checker-dependency-graph.svg
artifacts/checker-dependency-graph/latest-verdict.json
```

The generated graph files are not committed as stable source artifacts. They are replayed from the current checkout.

Run it with:

```bash
npm run checker:graph
```

The generator scans repository `.mjs` files, inventories exported `Check*0` functions, follows local static ES-module imports, and emits checker-to-checker dependency edges when a checker-bearing module imports another checker-bearing module.

The generated graph is a dependency visualization and audit input. It deliberately does not claim no circular authority yet:

```text
graphCycleAuditRequired = true
noCircularAuthorityProved = false
```

A later cycle audit should consume this graph and reject dependency cycles that allow a checker conclusion to re-enter its own premise chain.

The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
