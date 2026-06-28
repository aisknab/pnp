# Checker no-circular-authority artifacts

The checker cycle audit writes its generated verdict here:

```text
artifacts/checker-cycles/latest-verdict.json
```

It also regenerates the checker dependency graph under:

```text
artifacts/checker-cycles/generated-dependency-graph/
```

The generated verdict and graph files are not committed as stable source artifacts. They are replayed from the current checkout.

Run it with:

```bash
npm run checker:cycles
```

The audit validates `checker-cycles/CHECKER_AUTHORITY_GRAPH.json`, regenerates the static checker dependency graph, and rejects any declared authority cycle where a checker conclusion can re-enter its own premise chain.

The accepted verdict proves acyclicity only for declared authority edges:

```text
noCircularAuthorityProved = true
fullStaticImportCycleFreedomProved = false
```

Static import cycles, if any, remain implementation facts until explicitly declared as authority dependencies. The audit is non-activating: it does not clear the remaining blockers and does not allow public theorem emission.
