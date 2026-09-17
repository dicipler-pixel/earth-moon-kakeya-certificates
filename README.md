# Certified Obstructions and Exact Forcing

**Earth–Moon graph coloring and arithmetic Kakeya — certificates, obstructions, and finite exclusions.**

Jeromie Beasley · Version 2 · 17 September 2026

This repository is the public home of the paper and its complete reproduction supplement. Start with `manuscript/earth_moon_kakeya_epoch_v2_public.pdf`. Neither Epoch FrontierMath benchmark is claimed solved; the results are obstruction, classification, and finite-exclusion theorems with checkable certificates.

Every push re-runs `repro/verify_release.py --full` in GitHub Actions: payload hashes, byte-identical regeneration of both new certificates, the independent integer checkers, the probe/coherence identities, and the complete replay of the older arithmetic and graph corpus.

## What changed

The new written first-escape classification reduces an unrestricted integer generator direction to finitely many exact representatives. The fixed six-vertex Katz–Tao edge core has no completion when two generators are distinct placements from the declared seven-direction pool and a third has any admissible integer direction at any site. There are 861 fixed pairs, 5,166 site-parameter families, 6,112 representative barriers, and 25,498 integer target-dual identities.

A separate exact certificate excludes one initially known vertex and one arbitrary admissible generator: 36 site-parameter families, 38 representatives, and 152 integer target duals. These are overlapping unbounded families, not distinct-configuration counts to add to the old census.

The paper also supplies a probe-sensitive determinant/kernel bridge, exact generator updates, and source-aware Schur coherence. It integrates the earlier connection-energy and restricted Earth–Moon move-space results while keeping their source and test boundaries visible.

The full historical aggregate replay now passes: 231 arithmetic proof bundles, 33 core contexts, 481,712 distinct arithmetic configurations, and a separate 24,976-graph Earth–Moon family. Original corpus bytes and the new output remain separate.

## Public supplement

This is the public reproduction supplement: manuscript, producers, independent checkers, saved outputs, and the complete older arithmetic/graph proof corpus. Private author records are not included.

## Reproduce

Python 3.10 or later; standard library only for these commands. From this extracted folder:

```sh
python repro/verify_release.py
python repro/verify_release.py --full
```

The default verifies payload hashes, regenerates both new parameter certificates, checks their exact byte reproduction, runs the independent integer checkers, and checks the probe/coherence identities. `--full` additionally verifies the complete preserved aggregate in a temporary copy. It took roughly 26 seconds for that aggregate in the first local replay; your environment can differ. Run without Python `-O` because the historical aggregate uses assertions. The new checker scripts use explicit exceptions for failed conditions.

No GitHub connection, private mixer, network, NumPy, SymPy, or Lean installation is needed for the commands above. The separately preserved **historical Atlas-calculus demo** has its own SymPy-based requirements; it is not part of that standard-library claim.

## Contents and boundaries

`repro/` contains the new producers/checkers and complete older arithmetic/graph proof corpus. `results/` contains saved outputs and execution logs. 


The complete 158 MB nineteen-vertex Earth–Moon hard backup remains a separate Library archive; it is not duplicated here. Its archived 8,044-profile Boolean proof census was not newly replayed in this edition. The 100-edge survivor's thickness is still unresolved. No new Lean compilation, remote workflow, merge, publication, official Epoch verification, or accepted competition entry was performed.

Historical formulas are preserved as historical formulas, including rejected or unproved claims. An Atlas card's old grade is not a new certificate. 

## Compile the paper

The single LaTeX source is self-contained and uses standard packages. Run `pdflatex` three times on `manuscript/earth_moon_kakeya_epoch_v2.tex`. The Markdown is a generated editable representation; LaTeX is authoritative for numbered references and typesetting.
