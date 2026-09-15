# Correspondence with Zenodo v1.1.4

The full formalization is published at
[10.5281/zenodo.22739087](https://doi.org/10.5281/zenodo.22739087).
The [GitHub v1.1.4 release](https://github.com/HongruZhao/LogDetBerryEsseen/releases/tag/v1.1.4)
includes the identical file, `LogDetBerryEsseen_Full_Lean_v1.1.4.zip`.

| Artifact | Scope |
|---|---|
| GitHub source tree | Three main results: Theorem 4.2, Theorem 5.2, and Corollary 6.2, with their supporting proofs |
| Full Lean ZIP on Zenodo and GitHub Releases | 243 manuscript inventory entries and 288 audited endpoints, full crosswalk, verification scripts, audit evidence, revised manuscript sources, and original provenance |

The full inventory comprises 73 main-paper equations, 156 supplementary
equations, six main named results, one supplementary lemma, and seven Table 1
regime equivalents. All 38 previously outstanding entries are completed.
The full archive proves the actual covariance and exact general-correlation
variance identities without the historical scalar-limit certificate.

## Exact source relationship

`Challenge.lean`, `LogDetBerryEsseen.lean`, and `Verification.lean` are byte-identical
between the focused repository and the full archive. Their three theorem
statements and proofs agree exactly. The repository also incorporates the
archive's additions to `GeneralRCenterIdentity.lean` and `HardEdgeConstant.lean`.

Of the 131 active GitHub Lean files, 128 match files in the full ZIP byte for byte.
The three focused packaging differences are:

- `LogdetLean.lean` imports the two modules needed for the three main results.
- `KibbleCovarianceBounds.lean` changes one import to the focused helper module;
  its definitions and proof bodies are unchanged.
- `GeneralRVarianceBasics.lean` collects five unchanged definitions and proofs
  from the full archive's covariance and variance modules.

The correspondence receipt and file hashes are in
[audit/2026-09-14-zenodo-sync](../audit/2026-09-14-zenodo-sync).
The Lake package names and default targets differ to reflect the two scopes;
both pin Lean `4.33.0-rc2` and Mathlib commit
`641fbd329d4ffb62bef83c51f54088469056bd36`.

## Archive integrity and verification

The full ZIP has 1,954,690 bytes and SHA-256:

```text
d5172de1e5b338b140485f816950ca638d9b776b5927147a05ce235b5a26769c
```

Its Zenodo MD5 is `20efd3037140c10c2c31f92330527687`.
Checksums identify archive bytes; they are separate from proof verification.
GitHub's automatically generated source ZIP is the focused repository snapshot;
the named **Full Lean** release asset is the archive matching Zenodo.

On September 14, 2026, a fresh extraction of the full ZIP passed all 226 active
project build targets and the separate endpoint audit. Pinned third-party
dependency caches were reused, with no project build artifacts copied into the
fresh extraction. All 288 audited endpoints use only `propext`, `Classical.choice`,
and `Quot.sound`. No new `leanchecker` replay is claimed for that full archive.
The focused GitHub verification is reported separately in
[VERIFICATION.md](VERIFICATION.md).

The included supplement sources mark revisions in blue: the nondegenerate
domain of the joint density, the Gaussian tail bound at the prescribed cutoff,
and updated coverage notes. The main paper and numbered display bodies are
unchanged. Model and domain assumptions remain theorem hypotheses; prose,
bibliographic attribution, novelty, and open problems are outside kernel checking.

## Citation

Cite the full v1.1.4 formalization using `10.5281/zenodo.22739087`.
When reproducing the focused source tree, also identify the GitHub tag `v1.1.4`
or the exact commit. The all-versions DOI is
[10.5281/zenodo.21896818](https://doi.org/10.5281/zenodo.21896818).
