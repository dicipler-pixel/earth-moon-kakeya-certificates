# Contributing

This repository is the public reproduction supplement for a specific version of
a paper. It is an archival artifact, not an evolving codebase, so the useful
contributions here are different from those of a typical software project.

## Verify before you report

Everything can be checked from a clean clone with the Python standard library:

```sh
python repro/verify_release.py         # hashes, certificates, independent checkers
python repro/verify_release.py --full  # the above plus the full corpus replay
```

Python 3.10 or later. Run without `-O`: the preserved historical aggregate uses
assertions. The full replay takes roughly half a minute. The same command runs
in GitHub Actions on every push, so the badge state on `main` tells you whether
the release verifies as published.

## The payload is hash-pinned

`SHA256SUMS.txt` records the SHA-256 of every file under `manuscript/`,
`repro/`, and `results/`, plus `README.md`. `verify_release.py` checks all of
them before it does anything else.

A pull request that edits any of those files will fail CI. That is intended:
the manifest is what lets a reader confirm they are looking at the same bytes
the paper describes. The certificates are outputs of the producers in `repro/`,
not hand-maintained data, so they are not edited in place.

Repository infrastructure — this file, the license files, `CITATION.cff`, the
workflow, `.gitattributes` — is not hash-pinned and can be improved by pull
request in the normal way.

## What is most valuable

**A mathematical error.** If a certificate asserts something false, or a
checker accepts a configuration it should reject, that is the highest-value
report this repository can receive. Open an issue with the specific
configuration and the reasoning. Do not edit the certificate; the point is
whether the published bytes are wrong.

**A reproduction failure.** If `verify_release.py` fails on your machine while
CI is green, the environment difference is itself worth knowing. Include your
OS, `python --version`, and the complete output.

**An independent re-implementation.** The strongest possible check on a
certificate is a checker written from the paper by someone else. If you write
one, please open an issue describing what it confirmed or contradicted.

## Scope

Claims about the Epoch FrontierMath benchmarks are deliberately narrow: the
results are obstruction, classification, and finite-exclusion theorems, and
neither benchmark is claimed solved. Issues arguing that a stronger claim
follows are welcome as mathematics, but the repository's wording will stay
matched to what the certificates actually establish.
