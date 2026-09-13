# Verified environment

The fresh release verification used:

- Elan `4.2.3` (`elan 4.2.3 (b6cec7e10 2026-06-08)`);
- Lean `4.33.0-rc2`, commit
  `d8b18978322de05a8f3dba51ef03cf5461676c17`;
- Lake `5.0.0-src+d8b1897`;
- mathlib commit `641fbd329d4ffb62bef83c51f54088469056bd36`;
- `lake-manifest.json` SHA-256
  `47e7499d3e7d67f2f3152def1c96126a13aeb23b3c2911deee5ae5bdb640d2ff`.

The build ran on arm64 macOS. The theorem statements and proof terms are not
hardware dependent. `lean-toolchain` and `lake-manifest.json` are the
machine-readable toolchain and dependency pins.
