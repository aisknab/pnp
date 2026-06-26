# Canonical proof report public-review documentation revision

- Documentation coordinate: `PNP-DOC-CPR-2026-06-26-01`
- Revision date: `2026-06-26`
- Scope: public-review publication framing, source-access instructions, artefact-access instructions, and sealed-release custody notice
- Public repository: `https://github.com/aisknab/pnp`
- Documentation base commit: `f52e04b9963ea2f10cfccafbf705b9e316ed25a6`
- Frozen source release preserved: `final-pnp-proof-report-hardened-7072f8d` / `7072f8d0bda6d44d240f9bb3fad624fd357e1278`
- Frozen artefact release preserved: `final-pnp-proof-report-artifacts-hardened-7072f8d-sealed`
- Supersedes access-only coordinate: `PNP-DOC-CPR-2026-06-20-01`

This is a documentation-only successor to the sealed report. It does not replace, mutate, or reseal the frozen `7072f8d` source/checker release or its sealed artefact release.

The revision changes the title-page and Section 1 publication framing from direct theorem emission to explicit public-review status. It preserves the sealed report's recorded conditional theorem statement as a historical checker boundary, while stating that independent mathematical and checker-soundness review remains required and that public theorem emission is not activated by this documentation revision.

The revision also carries forward the source- and artefact-access correction: public source, checker code, materialized artefacts, reviewer guidance, and reproduction instructions are available without an access request in the public repository.

`SHA256SUMS` binds the exact revised TeX and PDF payloads. `PATCH_SHA256SUMS` binds the transport files supplied in this directory. `RECONSTRUCT.md` gives exact reconstruction and verification commands. The immutable Git commit coordinate is recorded separately after the payload commit is created.