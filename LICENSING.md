# Licensing

This repository is dual-licensed. The split follows the original release
statement: the written work is CC BY 4.0, the software is MIT.

| Path | Contents | License |
| --- | --- | --- |
| `manuscript/` | Paper (LaTeX, Markdown, PDF) | CC BY 4.0 — `LICENSE-CC-BY-4.0.md` |
| `README.md` | Prose description of the work | CC BY 4.0 — `LICENSE-CC-BY-4.0.md` |
| `repro/` | Producers, independent checkers, preserved corpus code | MIT — `LICENSE` |
| `results/` | Saved certificate outputs and execution logs | MIT — `LICENSE` |
| `SHA256SUMS.txt` | Integrity manifest | MIT — `LICENSE` |

GitHub reports this repository as MIT because `LICENSE` holds the MIT text.
That reflects the code, which is the larger part of the tree by file count. It
does not narrow the manuscript's CC BY 4.0 grant, which stands on its own.

Certificates, search outputs, and the preserved historical corpus under
`repro/legacy_dag/` are released on the same MIT terms as the code that
produced them, so they can be redistributed, re-checked, and built upon
without restriction.

## Integrity note

`SHA256SUMS.txt` pins the SHA-256 of every payload file, and CI re-verifies all
of them on each push. Redistributing the payload unchanged keeps those hashes
valid; modifying a payload file invalidates its hash by design, which is the
point of the manifest rather than a defect.
