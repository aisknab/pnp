#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, shutil

R=Path('.')
D=R/'docs-release/public-access-7072f8d'
DT='final-pnp-proof-report-docs-hardened-7072f8d-public-access-sealed'
ST='final-pnp-proof-report-hardened-7072f8d'
SC='7072f8d0bda6d44d240f9bb3fad624fd357e1278'
AT='final-pnp-proof-report-artifacts-hardened-7072f8d-sealed'
AC='9d1de19f827e5cb6880741352eb2349cbbb45994'

def h(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def rep(s,a,b,label):
    n=s.count(a)
    if n!=1: raise RuntimeError(f'{label}: expected 1 occurrence, found {n}')
    return s.replace(a,b)
def update(p,fn):
    q=R/p; q.write_text(fn(q.read_text()))

pdf=R/'canonical_proof_report.pdf'; tex=R/'canonical_proof_report.tex'
ps,ts=h(pdf),h(tex); pb,tb=pdf.stat().st_size,tex.stat().st_size

needle='External-review status is tracked in [EXTERNAL_REVIEW_STATUS.md](./EXTERNAL_REVIEW_STATUS.md). Outreach records are not proof evidence, and silence should not be interpreted as acceptance, rejection, or an assessment of the claim.\n'
block=f'''{needle}\n## Current pinned review release\n\n```text\nsource tag:   {ST}\nartifact tag: {AT}\ndocs tag:     {DT}\n```\n\nThe documentation tag is a public-access revision only. It does not change the source/checker code, theorem statements, mathematical argument, generated package, accepted records, or sealed artefact bundle.\n\nCanonical report identities:\n\n```text\nPDF SHA-256: {ps}\nTeX SHA-256: {ts}\n```\n\nSee [PUBLIC_ACCESS_REVISION.md](./PUBLIC_ACCESS_REVISION.md) and [docs-release/public-access-7072f8d/](./docs-release/public-access-7072f8d/).\n'''
update('README.md',lambda s: rep(s,needle,block,'README release section'))

def current(s):
    s=rep(s,'docs tag:     final-pnp-proof-report-docs-hardened-7072f8d-sealed',f'docs tag:     {DT}','CURRENT docs tag')
    s=rep(s,'bundle path:  proof-artifacts/final-pnp-proof-report-hardened-7072f8d/','artifact path: proof-artifacts/final-pnp-proof-report-hardened-7072f8d/\ndocs path:     docs-release/public-access-7072f8d/','CURRENT paths')
    s=rep(s,'boundary:     CheckPCCPackexp(GeneratePCCPack())=accept => P = NP',f'boundary:     CheckPCCPackexp(GeneratePCCPack())=accept => P = NP\nreport PDF:   {ps}\nreport TeX:   {ts}','CURRENT hashes')
    return s+'\nThe current documentation tag changes public-access and contact instructions only; the source/checker and sealed artefact identities are unchanged.\n'
update('CURRENT_RELEASE.md',current)

old='''### Current canonical manuscript\n\n```text\ncanonical_proof_report.tex\ncanonical_proof_report.pdf\n```\n\nThe manuscript revision is the current `main` commit that contains the 7072f8d residual-hardened release-seal update to `canonical_proof_report.tex` and `canonical_proof_report.pdf`.'''
new=f'''### Canonical documentation revision\n\n```text\ndocs tag: {DT}\ndocs path: docs-release/public-access-7072f8d/\nPDF SHA-256: {ps}\nTeX SHA-256: {ts}\n```\n\nThis is a documentation-only public-access revision. It changes repository and contact instructions, not checker code, theorem statements, mathematical arguments, generated artefacts, accepted records, or artefact digests.'''
old2=f'''To inspect the source/checker revision:\n\n```bash\ngit checkout {ST}\ngit rev-parse HEAD\n```'''
new2=f'''To verify the documentation revision first:\n\n```bash\ngit checkout {DT}\ncd docs-release/public-access-7072f8d\nsha256sum -c SHA256SUMS\ncd ../..\n```\n\nTo inspect the source/checker revision:\n\n```bash\ngit checkout {ST}\ngit rev-parse HEAD\n```'''
def reproduce(s):
    s=rep(s,old,new,'REPRODUCE docs revision')
    return rep(s,old2,new2,'REPRODUCE checkout')
update('REPRODUCE.md',reproduce)

old=f'''sealed artifact tag:\n{AT}\n\nartifact bundle:\nproof-artifacts/final-pnp-proof-report-hardened-7072f8d/\n\nvalidation:\n1121 tests, 1121 pass, 0 fail'''
new=f'''sealed artifact tag:\n{AT}\n\ndocumentation tag:\n{DT}\n\nartifact bundle:\nproof-artifacts/final-pnp-proof-report-hardened-7072f8d/\n\ndocumentation bundle:\ndocs-release/public-access-7072f8d/\n\ncanonical report PDF SHA-256:\n{ps}\n\ncanonical report TeX SHA-256:\n{ts}\n\nvalidation:\n1121 tests, 1121 pass, 0 fail'''
def reviewer(s):
    s=rep(s,old,new,'REVIEWER release facts')
    s=rep(s,'The hardened release seal is:','The hardened artefact release seal is:','REVIEWER seal heading')
    return s+'\n\n## Documentation boundary\n\nThe public-access documentation tag changes repository-access and contact instructions only. It does not change source/checker logic, the theorem boundary, the mathematical argument, generated artefacts, accepted records, or sealed artefact digests.\n'
update('REVIEWER_MAP.md',reviewer)

(R/'PUBLIC_ACCESS_REVISION.md').write_text(f'''# Public-access documentation revision\n\nThe canonical report has a documentation-only public-access revision sealed by:\n\n```text\n{DT}\n```\n\nThe source/checker repository and pinned release tags are public at `https://github.com/aisknab/pnp`; no access request is required.\n\n## New canonical report identities\n\n```text\nPDF SHA-256: {ps}\nTeX SHA-256: {ts}\n```\n\nThe release seal and checksum ledger are under `docs-release/public-access-7072f8d/`.\n\n## Unchanged boundaries\n\nThe source/checker tag and commit, sealed artefact tag and bundle, validation record, theorem statements, mathematical argument, checker implementation, generated package, accepted checker records, and artefact digests are unchanged.\n''')
D.mkdir(parents=True,exist_ok=True)
(D/'README.md').write_text(f'''# Documentation-only public-access revision\n\nThis directory seals the canonical PDF and TeX for the documentation-only public-access revision of the 7072f8d review release.\n\n## Pinned identities\n\n- source/checker tag: `{ST}`\n- source/checker commit: `{SC}`\n- sealed artefact tag: `{AT}`\n- documentation tag: `{DT}`\n\n## Scope\n\nThis revision changes repository-access and review-contact instructions, adds direct public clone and pinned-tag verification commands, restores explicit report attribution and metadata consistently, and seals the PDF and TeX identities.\n\nIt does not change checker code, theorem statements, mathematical arguments, generated packages, accepted checker records, or the sealed artefact bundle.\n\nVerify with `sha256sum -c SHA256SUMS`.\n''')
shutil.copyfile(pdf,D/pdf.name); shutil.copyfile(tex,D/tex.name)
(D/'SHA256SUMS').write_text(f'{ps}  {pdf.name}\n{ts}  {tex.name}\n')
seal={
 'kind':'PNPDocumentationReleaseSeal','version':1,'scope':'documentation-only public-access revision',
 'status':'file identity and documentation provenance only; not theorem validation','docsTag':DT,
 'sourceRepo':'aisknab/pnp','sourceTag':ST,'sourceCommit':SC,'artifactTag':AT,'artifactCommit':AC,
 'previousDocsTag':'final-pnp-proof-report-docs-hardened-7072f8d-sealed','previousDocsCommit':'3ba356c79b545d2c734283bf10d85d0710de2b60',
 'previousPublishedSiteReport':{'pdfSha256':'53437127d4d111562689c093857de86e846c6ad4a8cf0bc0674ff0bc822e603d','texSha256':'414d2a2474291c0cc2bf1098f6c937b0bf13c53243774394516bd8def355d4c7'},
 'previousPnpMainReport':{'pdfSha256':'e134c92d74eb4fdbe4e86814d8c0a86fa49768f2036cb98b5fc9f8da906c44c2','texSha256':'d5559b4d0ca59b9c08d180cd802652159da75e58291aa293e539776207865b21'},
 'changeBoundary':['Replace restricted-access instructions with direct public repository and pinned-tag instructions.','Add a visible documentation-only revision notice and documentation tag.','Add public clone, documentation checksum, artefact checksum, validation, and regeneration commands.','Preserve explicit author and publisher metadata and deterministic PDF metadata controls.'],
 'nonChanges':['No source/checker code change.','No theorem-statement change.','No mathematical-argument change.','No generated-package or checker-record change.','No sealed artefact bundle or artefact digest change.'],
 'build':{'engine':'pdfTeX','sourceDateEpoch':1781740800,'forceSourceDate':True,'timezone':'UTC','deterministicControls':['pdfinfoomitdate','empty pdftrailerid','pdfsuppressptexinfo=15']},
 'files':[{'path':pdf.name,'bytes':pb,'sha256':ps,'role':'canonical documentation-only revised PDF'},{'path':tex.name,'bytes':tb,'sha256':ts,'role':'canonical documentation-only revised TeX source'}]
}
(D/'release-seal.json').write_text(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'status':'finalized','docsTag':DT,'pdfSha256':ps,'pdfBytes':pb,'texSha256':ts,'texBytes':tb},indent=2))
