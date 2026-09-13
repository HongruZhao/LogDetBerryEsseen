# Dependency report

## Local source closure

The capsule contains 137 Lean files under `LogdetLean/`:

- 135 modules in the transitive local import closure of the thirteen advertised
  endpoints; and
- two paper-facing audit modules,
  `PaperTable2Endpoints.lean` and `PaperAxiomAudit.lean`.

The top-level `LogdetLean.lean` is a separate narrow root module that imports
only `LogdetLean.PaperTable2Endpoints`.

The public endpoint module has five direct imports:

```lean
import LogdetLean.NullUniformEdgeworthTarget
import LogdetLean.GeneralRPaperExactTranslation
import LogdetLean.NullVUniformAsymptotics
import LogdetLean.NullRefinedAsymptotics
import LogdetLean.NullSharpSupremumDecimal
```

Their recursive imports contain the endpoint modules for Proposition 4.1,
the `A` equivalent, and the supremum theorem, so no broader umbrella import is
needed.

The closure was determined at Lean-module file granularity by recursively
following every local `import LogdetLean...` edge from these four roots. A
generic source module is included only when one of those import paths reaches
it. This is an import closure, not a claim that every declaration inside each
included file is a paper-facing theorem.

## Paper-specific extraction

The general-correlation proof needs four deterministic variance and trace
declarations that had previously lived in a file associated with a broader
project. They are included here, with ordinary readable proofs, in
`LogdetLean/GeneralRVarianceTraceBasics.lean`. The three consuming modules
import this neutral file. The unrelated source module and its unused
declarations are not included.

No compiled `.olean` file is used as a substitute for source.

## External dependencies

The only direct external dependency in `lakefile.toml` is mathlib:

| Dependency | Source | Pinned revision |
|---|---|---|
| Lean | `leanprover/lean4` toolchain | `v4.33.0-rc2` (`d8b18978322de05a8f3dba51ef03cf5461676c17`) |
| mathlib | `leanprover-community/mathlib4` | `641fbd329d4ffb62bef83c51f54088469056bd36` |
| Elan | Lean toolchain manager | `4.2.3` |
| Lake | Lean package manager | `5.0.0-src+d8b1897` |

`lake-manifest.json` records mathlib's public transitive Git dependencies and
their exact revisions. It contains no local path dependency, unpublished
parent workspace, or credentialed URL.

## Excluded material

The capsule intentionally excludes:

- the earlier-paper project and unrelated theorem modules;
- broad project audit modules not needed by the Table 2 boundary;
- qualitative general-correlation CLT and nonfixed-regime collections not
  needed by the thirteen endpoints;
- private prompts, agent workflows, generators, scratch files, and failed or
  alternative proof branches;
- simulations, data, manuscript drafts, and unrelated PDFs;
- `.git`, Git history, `.lake`, `.olean` files, and compiled caches; and
- editor settings, absolute machine paths, credentials, and temporary files.

## Validation status

On 2026-08-12, the complete v1.1.2 capsule passed the source audit, pinned
dependency check, full build, thirteen-endpoint axiom audit, sorry audit, and
eight-root `leanchecker` run from a fresh extraction. The procedure was
repeated after extracting the final ZIP; the generated records are shipped
with the release.
