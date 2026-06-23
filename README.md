# johnson-lindenstrauss-lean

A zero-`sorry` Lean 4 / mathlib formalization of the **Johnson–Lindenstrauss (JL) lemma** —
proven end-to-end for an arbitrary finite point set with an *explicit* bound on the target
dimension — together with the **inner-product correctness guarantee behind quantized
Johnson–Lindenstrauss (QJL / TurboQuant)**: the unbiasedness of the asymmetric 1-bit
sign-sketch estimator and a Chebyshev concentration (distortion) bound for it. The
probabilistic core is chi-squared concentration (the MGF of a sum of squared Gaussians plus
mathlib's Chernoff bound); Gaussian rotation invariance transports it to the real random
projection, and a union bound over pairs upgrades the per-vector guarantee to a single
projection that preserves *all* pairwise distances. The QJL layer adds the
Grothendieck/sign-product identity `E[sign⟨u,g⟩·⟨v,g⟩] = √(2/π)·⟨u,v⟩` and builds the
unbiased estimator and its variance/Chebyshev tail on top of it. Everything reduces to
mathlib's three standard axioms.

## Main results

**End-to-end Johnson–Lindenstrauss** (`JL/EndToEnd.lean`) — for any `m` distinct points and any
target dimension `k` with `4·log(2m²) < (ε²−ε³)·k`, there is a Gaussian projection into `k`
dimensions preserving every pairwise squared distance within a factor `1 ± ε`. The dimension
bound is *derived* (`JL.card_condition`), not assumed.

```lean
theorem johnson_lindenstrauss_pointset {m d k : ℕ} (hk : 0 < k)
    (p : Fin m → EuclideanSpace ℝ (Fin d)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1)
    (hp : ∀ a b, a ≠ b → p a ≠ p b)
    (hdim : 4 * Real.log (2 * (m : ℝ) ^ 2) < (ε ^ 2 - ε ^ 3) * (k : ℝ)) :
    ∃ A : Fin k → Fin d → ℝ, ∀ a b, a ≠ b →
      |(∑ i, (jlMap k d A (fun j => (p a - p b) j) i) ^ 2) - ‖p a - p b‖ ^ 2|
        < ε * ‖p a - p b‖ ^ 2
```

**The Grothendieck / sign-product identity** (`JL/QJL.lean`) — for a standard Gaussian vector
`g` in `ℝ^d`, a unit vector `u` and an arbitrary `v`, the expected product of `sign⟨u,g⟩` with
`⟨v,g⟩` is `√(2/π)·⟨u,v⟩`. This is the heart of QJL's 1-bit correctness.

```lean
theorem sign_product_identity {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∫ g, Real.sign (⟪u, g⟫) * ⟪v, g⟫ ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      = Real.sqrt (2 / π) * ⟪u, v⟫
```

**QJL estimator unbiasedness** (`JL/QJL.lean`) — over an `m × d` i.i.d. standard-Gaussian sketch,
the asymmetric 1-bit estimator is unbiased for the normalized inner product `⟨key/‖key‖, q⟩`
(and, un-normalized, `‖key‖·E[estimator] = ⟨key, q⟩`).

```lean
theorem qjlEstimator_unbiased {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) :
    ∫ S, qjlEstimator key q S
        ∂(Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      = ⟪‖key‖⁻¹ • key, q⟫

theorem qjlEstimator_unbiased_inner {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) :
    ‖key‖ * (∫ S, qjlEstimator key q S
        ∂(Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))))
      = ⟪key, q⟫
```

**QJL distortion / concentration bound** (`JL/QJLDistortion.lean`) — with `m` sign-bits the
estimator deviates from the true normalized inner product by at least `ε` with probability at
most `(π/2)‖q‖²/(m·ε²)`, so `m = O(‖q‖²/(ε²δ))` sign-bits suffice for additive error `ε` with
probability `1 − δ`.

```lean
theorem qjlEstimator_concentration {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ π / 2 * ‖q‖ ^ 2 / (m * ε ^ 2)
```

**QJL exponential distortion bound** (`JL/QJLDistortion.lean`) — the sub-Gaussian / Chernoff
sharpening of the Chebyshev bound: the deviation probability decays *exponentially* in `m`, namely
`2·exp(-m·ε²/(π·‖q‖²))`, so `m = O(‖q‖²·log(1/δ)/ε²)` sign-bits suffice for additive error `ε` with
probability `1 − δ`. This is the one result that depends on a single isolated hypothesis: the
predicate `IsPerRowSubgaussian`, asserting that the centered per-row sign-product term has a
sub-Gaussian MGF with variance proxy `(π/2)‖q‖²` (see "Scope / not yet done").

```lean
theorem qjlEstimator_concentration_exp {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (_hkey : key ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hsub : IsPerRowSubgaussian (‖key‖⁻¹ • key) q) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2))
```

### Supporting results

- `JL.sqGaussian_mgf` — `E[exp(t·Z²)] = (1−2t)^(−1/2)` for `Z ~ N(0,1)`, `t < 1/2`.
- `JL.chiSq_mgf`, `JL.chiSq_upper_tail`, `JL.chiSq_lower_tail`, `JL.chiSq_concentration` —
  chi-squared MGF and two-sided Chernoff tail bounds.
- `JL.jl_norm_preservation` — distributional norm-preservation for the abstract chi-squared sum.
- `JL.map_dotProduct_gaussianReal` / `JL.gaussianMatrix_map_dotProduct` — Gaussian rotation
  invariance: the i.i.d. Gaussian matrix pushes forward under `A ↦ A.mulVec u` (for unit `u`) to
  `gaussianVec k`.
- `JL.jlMap_concentration` — norm preservation for the *actual* Gaussian projection `jlMap`.
- `JL.johnson_lindenstrauss` — the abstract probabilistic-method / union-bound existence lemma.
- `JL.inner_product_preservation` — inner-product preservation via polarization.
- `JL.integral_abs_gaussianReal` — the Gaussian absolute moment `E|Z| = √(2/π)`.
- `JL.qjl_perrow_variance_le` / `JL.qjlEstimator_variance_le` — per-row and `m`-row variance
  bounds (the latter via cross-row independence, `ProbabilityTheory.variance_sum_pi`).
- `JL.qjlEstimator_centered_hasSubgaussianMGF` — the centered estimator is sub-Gaussian with
  variance proxy `(π/2)‖q‖²/m`, assembled from the `m` independent rows (`iIndepFun_pi`,
  `HasSubgaussianMGF.sum_of_iIndepFun`) and the `1/m` rescaling.

## Layout

The dependency chain flows top to bottom:

- `JL/SquaredGaussian.lean` — MGF of a squared standard Gaussian, `(1−2t)^(−1/2)`.
- `JL/ChiSquared.lean` — chi-squared MGF and two-sided tail bounds via Chernoff.
- `JL/Projection.lean` — the Gaussian projection `jlMap` and the deterministic row-product
  reduction `‖f x‖² = (1/k)·∑ᵢ(Aᵢ·x)²` (`jlMap_sq_norm`).
- `JL/NormPreservation.lean` — distributional JL norm-preservation bound (chi-squared form).
- `JL/Rotation.lean` — Gaussian rotation invariance and the projection ↔ chi-squared link
  (`jlMap_concentration`).
- `JL/Lemma.lean` — the abstract `johnson_lindenstrauss` union-bound existence theorem.
- `JL/EndToEnd.lean` — the end-to-end `johnson_lindenstrauss_pointset` with derived `k` bound.
- `JL/InnerProduct.lean` — inner-product preservation corollary (the QJL/TurboQuant tie-in).
- `JL/QJL.lean` — Gaussian absolute moment, the sign-product identity, and QJL estimator
  unbiasedness.
- `JL/QJLDistortion.lean` — per-row and estimator variance, and the Chebyshev distortion bound.
- `JL/Verify.lean` — sanity instantiations and the `#print axioms` audit.
- `JL.lean` — umbrella import of all of the above.

## Building

This is a standalone Lake project pinned to Lean toolchain **`leanprover/lean4:v4.31.0`** with
mathlib pinned to the matching revision (see `lake-manifest.json`).

```bash
lake exe cache get   # fetch prebuilt mathlib oleans (recommended)
lake build
```

## Axioms

Every headline theorem has been audited with `#print axioms` (see `JL/Verify.lean`) and depends
only on mathlib's three standard axioms:

```
[propext, Classical.choice, Quot.sound]
```

There are no uses of `sorry`, `admit`, custom `axiom` declarations, or `native_decide` anywhere
in the development. (The exponential distortion bound takes the per-row sub-Gaussian fact as an
explicit hypothesis `IsPerRowSubgaussian` — see below — so it too reduces to the three axioms.)

## Scope / not yet done

- **The one demoted step: `IsPerRowSubgaussian`.** The exponential QJL tail
  (`qjlEstimator_concentration_exp`) is fully proven *except* for a single isolated, clearly-true
  hypothesis: that the centered per-row term `g ↦ √(π/2)·sign⟪u,g⟫·⟪q,g⟫ − ⟪u,q⟫` has a sub-Gaussian
  MGF with variance proxy `(π/2)‖q‖²`. Everything downstream — coordinate independence under
  `Measure.pi`, additivity of the sub-Gaussian parameter over the `m` independent rows, the `1/m`
  rescaling, and the two-sided Chernoff bound — is discharged unconditionally. A mathlib proof of
  `IsPerRowSubgaussian` itself needs a folded-normal / `erf` sub-Gaussian estimate for `|⟪u,g⟫|`
  that is not yet available (the crude `exp(t|x|) ≤ exp(tx)+exp(−tx)` bound loses a factor `2` per
  row, fatal across `m` rows), so it is left as the remaining analytic gap.
- **PolarQuant stage-1 MSE bound** and **full TurboQuant two-stage near-optimality** are out of
  scope here.
- **Not upstreamed.** This lives as a standalone project, not (yet) part of mathlib. A few helper
  lemmas (`measurable_real_sign`, the `Real.sign`-valued `sign_mul_self`, and
  `integral_abs_gaussianReal`) have no exact mathlib equivalent and would be natural upstream
  candidates; a couple of files still `import Mathlib` wholesale rather than minimal imports.

## License

Apache-2.0 (matching mathlib's license, to ease a future upstream). See `LICENSE`.
