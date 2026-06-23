# johnson-lindenstrauss-lean

A zero-`sorry` Lean 4 / mathlib formalization of the **Johnson–Lindenstrauss lemma**,
proven end-to-end for an arbitrary finite point set with an explicit bound on the
target dimension.

The probabilistic core is **chi-squared concentration**: the moment generating
function of a sum of squared standard Gaussians, combined with mathlib's Chernoff
bound, yields a two-sided tail bound. **Gaussian rotation invariance** transports this
to the real random projection, and a union bound over pairs upgrades the per-vector
guarantee to a single projection preserving *all* pairwise distances. An inner-product
preservation corollary (via polarization) underpins quantized Johnson–Lindenstrauss
schemes (QJL / TurboQuant).

## Main results

- `JL.sqGaussian_mgf` — `E[exp(t·Z²)] = (1-2t)^(-1/2)` for `Z ~ N(0,1)`, `t < 1/2`.
- `JL.chiSq_mgf`, `JL.chiSq_upper_tail`, `JL.chiSq_lower_tail` — chi-squared MGF and
  two-sided Chernoff tail bounds.
- `JL.jl_norm_preservation` — distributional norm-preservation for the abstract
  chi-squared sum: `P(|S/k - 1| ≥ ε) ≤ 2·exp(-(ε²-ε³)k/4)`.
- `JL.map_dotProduct_gaussianReal` / `JL.gaussianMatrix_map_dotProduct` — Gaussian
  rotation invariance: for a unit vector `u`, the i.i.d. Gaussian matrix pushes forward
  under `A ↦ A.mulVec u` to `gaussianVec k` (the `k` row products are i.i.d. `N(0,1)`).
- `JL.jlMap_concentration` — the norm-preservation bound for the *actual* Gaussian
  projection `jlMap`: `P(|‖f w‖² - ‖w‖²| ≥ ε‖w‖²) ≤ 2·exp(-(ε²-ε³)k/4)`.
- `JL.johnson_lindenstrauss` — the abstract probabilistic-method / union-bound lemma.
- `JL.johnson_lindenstrauss_pointset` — **the end-to-end theorem**: for `m` distinct
  points in `EuclideanSpace ℝ (Fin d)` and `k` with `4·log(2 m²) < (ε²-ε³)·k`, there
  exists a Gaussian projection `A : Fin k → Fin d → ℝ` preserving every pairwise squared
  distance within a factor `1 ± ε`. The dimension bound is *derived* (`JL.card_condition`),
  not assumed.
- `JL.inner_product_preservation` — inner-product preservation via polarization.

## Layout

- `JL/SquaredGaussian.lean` — MGF of a squared standard Gaussian, `(1-2t)^(-1/2)`.
- `JL/ChiSquared.lean` — chi-squared MGF and two-sided tail bounds via Chernoff.
- `JL/Projection.lean` — the Gaussian projection `jlMap` and the deterministic
  row-product reduction `‖f x‖² = (1/k)·∑ᵢ(Aᵢ·x)²` (`jlMap_sq_norm`).
- `JL/NormPreservation.lean` — distributional JL norm-preservation bound (chi-squared form).
- `JL/Rotation.lean` — Gaussian rotation invariance and the projection ↔ chi-squared link,
  transporting the bound to the real projection (`jlMap_concentration`).
- `JL/Lemma.lean` — the abstract `johnson_lindenstrauss` union-bound existence theorem.
- `JL/EndToEnd.lean` — the end-to-end `johnson_lindenstrauss_pointset` with derived `k` bound.
- `JL/InnerProduct.lean` — inner-product preservation corollary.
- `JL/Verify.lean` — sanity instantiations and `#print axioms` audit.

## Building

```bash
lake exe cache get   # fetch prebuilt mathlib oleans
lake build
```
