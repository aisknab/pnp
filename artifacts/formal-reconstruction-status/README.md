# Formal reconstruction status artifacts

The status checker writes its verdict to:

```text
artifacts/formal-reconstruction-status/latest-verdict.json
```

Run it with:

```bash
node pcc-formal-reconstruction-status0.mjs --json
```

The checker verifies the conservative reconstruction boundary and the exact public mirror. An
`accept` result means the status payload accurately records disabled theorem emission and the listed
formal obligations. It does not establish the target theorem.
