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
asymmetric sign-product identity `E[sign⟨u,g⟩·⟨v,g⟩] = √(2/π)·⟨u,v⟩` (the one-sided one-bit
analogue — *not* the symmetric Grothendieck arcsin law `E[sign⟨u,g⟩·sign⟨v,g⟩] = (2/π)·arcsin⟨u,v⟩`)
and builds the unbiased estimator and its variance/Chebyshev tail on top of it. Both distortion
guarantees — the Chebyshev bound *and* the sharp exponential sub-Gaussian (Chernoff) sharpening —
are proven fully unconditionally; the latter rests on a folded-normal sub-Gaussian estimate built
from scratch in `JL/GaussianTail.lean` (mathlib lacks `erf` / Gaussian-CDF concentration).
Everything reduces to mathlib's three standard axioms.

## How to read this (you don't need to know Lean)

If you are evaluating whether these results match the corresponding statements in the source
papers, you only ever need to read the **theorem statements** — never the proof bodies.

- **You do not need to trust, or even read, the proofs.** Lean's kernel mechanically checks every
  proof step. A theorem that the build accepts is, by construction, a correct derivation from its
  hypotheses; correctness of the proof is not a matter of trust or careful human review.
- **Three checks rule out anything faked**, and this repo performs all three: (1) the project
  *builds cleanly*; (2) there is *zero* `sorry`/`admit` (no proof is left as an unproven hole);
  and (3) `#print axioms` on every headline theorem reports only Lean/mathlib's three standard
  foundational axioms — `propext`, `Classical.choice`, `Quot.sound` — i.e. no extra assumptions or
  escape hatches were smuggled in. The audit lives in `JL/Verify.lean`.
- **So the only thing that needs domain expertise** is the question *"does each Lean statement say
  what the corresponding paper result says?"* The table below answers exactly that: it maps each
  Lean theorem to its plain-math meaning and to the corresponding result in the source papers, so the
  statements can be spot-checked in a couple of minutes.
- You can also read every file directly

## Theorem ↔ paper-lemma map

Each row is a headline result; the statement column is plain math (read the file for the exact Lean
syntax). `g` is a standard Gaussian vector, the sketch is `m × d` i.i.d. standard Gaussian, and
`estimator` is the asymmetric 1-bit QJL estimator `qjlEstimator`.

| Lean name | File | Plain-math statement | Corresponds to |
| --- | --- | --- | --- |
| `qjlEstimator_unbiased` / `qjlEstimator_unbiased_inner` | `JL/QJL.lean` | `E[estimator] = ⟨key/‖key‖, q⟩`; un-normalized, `‖key‖·E[estimator] = ⟨key, q⟩`. Expectation over the `m × d` i.i.d. standard-Gaussian sketch; requires `key ≠ 0`. | **QJL Lemma 2** — unbiasedness of the asymmetric one-bit estimator. |
| `qjlEstimator_concentration` | `JL/QJLDistortion.lean` | `P(\|estimator − ⟨key/‖key‖,q⟩\| ≥ ε) ≤ (π/2)·‖q‖²/(m·ε²)`. | **Chebyshev** (second-moment) distortion bound. |
| `qjlEstimator_concentration_exp` | `JL/QJLDistortion.lean` | `P(\|estimator − ⟨key/‖key‖,q⟩\| ≥ ε) ≤ 2·exp(−m·ε²/(π·‖q‖²))`, fully unconditional (no `key ≠ 0` needed). | **Same FORM as QJL Lemma 3** (exponential, `log(1/δ)` / `ε⁻²` rate) — but with a **looser explicit constant**: `π ≈ 3.14` here in place of the paper's `(4/3)(1+ε) ≈ 1.33–2.67`. The rate matches; the constant is *not* identical (it is looser). |
| `sign_product_identity` | `JL/QJL.lean` | for a **unit** `u` (`‖u‖ = 1`): `E[sign⟨u,g⟩·⟨v,g⟩] = √(2/π)·⟨u,v⟩` — the asymmetric one-bit sign-product identity (distinct from the symmetric Grothendieck arcsin law). | Supporting identity behind Lemma 2. |
| `integral_abs_gaussianReal` | `JL/QJL.lean` | `E\|Z\| = √(2/π)` for `Z ~ N(0,1)`. | Supporting Gaussian moment. |
| `foldedNormal_subgaussian` | `JL/GaussianTail.lean` | `\|Z\| − √(2/π)` is 1-sub-Gaussian for `Z ~ N(0,1)`. | From-scratch infrastructure filling a mathlib gap (no `erf` / Gaussian-CDF concentration); this is what makes the exponential bound unconditional. |
| `johnson_lindenstrauss_pointset` | `JL/EndToEnd.lean` | for `m` distinct points and `0 < ε < 1`, if `4·log(2m²) < (ε²−ε³)·k` then there **exists** one linear map (the `1/√k`-scaled Gaussian projection `jlMap`) preserving **all** pairwise squared distances within relative error `ε`. The dimension condition yields `k = Θ(ε⁻² log m)`, the standard JL target dimension — derived, not assumed. | **The Johnson–Lindenstrauss lemma** (pointset / distance-preservation form). |
| `johnson_lindenstrauss` | `JL/Lemma.lean` | abstract probabilistic-method / union-bound existence theorem that the pointset version is built on. | JL via the probabilistic method. |
| `inner_product_preservation` | `JL/InnerProduct.lean` | **deterministic** polarization corollary: **if** a linear map `f` preserves `‖u±v‖²` within relative error `ε`, **then** `\|⟨f u, f v⟩ − ⟨u, v⟩\| ≤ ε·(‖u‖²+‖v‖²)/2`. This is a deterministic corollary *conditional on* the norm-preservation hypotheses — **not** an assembled probabilistic guarantee about `jlMap`. | JL inner-product preservation. |

**Scope (what is and isn't here).** This formalizes the QJL one-bit inner-product layer plus the JL
foundations only. The PolarQuant stage-1 MSE bound, the full two-stage TurboQuant estimator, and the
information-theoretic lower bound are **not** formalized (see *Scope / not yet done* below).

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

**The asymmetric sign-product identity** (`JL/QJL.lean`) — for a standard Gaussian vector
`g` in `ℝ^d`, a unit vector `u` and an arbitrary `v`, the expected product of `sign⟨u,g⟩` with
`⟨v,g⟩` is `√(2/π)·⟨u,v⟩`. This is the heart of QJL's 1-bit correctness. Note it is the
*asymmetric* one-sided (linear) identity, **not** the symmetric Grothendieck arcsin identity
`E[sign⟨u,g⟩·sign⟨v,g⟩] = (2/π)·arcsin⟨u,v⟩`.

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
sharpening of the Chebyshev bound, now **fully unconditional**: the deviation probability decays
*exponentially* in `m`, namely `2·exp(-m·ε²/(π·‖q‖²))`, so `m = O(‖q‖²·log(1/δ)/ε²)` sign-bits
suffice for additive error `ε` with probability `1 − δ`. This exponential `log(1/δ)` form matches
the QJL paper's published distortion guarantee (Lemma 3 of
[arXiv:2406.03482](https://arxiv.org/abs/2406.03482)). The per-row sub-Gaussian MGF bound it rests
on (formerly an `IsPerRowSubgaussian` hypothesis) is now proven from scratch as
`isPerRowSubgaussian_normalized`, via the folded-normal sub-Gaussian estimate
`foldedNormal_subgaussian` in `JL/GaussianTail.lean`.

```lean
theorem qjlEstimator_concentration_exp {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2))
```

The folded-normal sub-Gaussian estimate is the key new analytic ingredient (`JL/GaussianTail.lean`):
for `Z ~ N(0,1)`, the centered absolute value `|Z| − √(2/π)` is `1`-sub-Gaussian.

```lean
theorem foldedNormal_subgaussian :
    HasSubgaussianMGF (fun z : ℝ => |z| - √(2 / π)) ⟨1, by norm_num⟩ (gaussianReal 0 1)
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
- `JL.foldedNormal_subgaussian` (`JL/GaussianTail.lean`) — the centered folded normal `|Z| − √(2/π)`
  is `1`-sub-Gaussian, with supporting lemmas `JL.gaussian_foldedMGF` (closed-form folded-normal
  MGF), `JL.hasDerivAt_gTail`, and `JL.two_g_le` (the sharp inequality `√(2/π)·gTail t ≤ exp(t√(2/π))`,
  i.e. `2·Φ(t) ≤ exp(t√(2/π))`).
- `JL.isPerRowSubgaussian_of_unit` / `JL.isPerRowSubgaussian_normalized` — the per-row sub-Gaussian
  MGF bound (variance proxy `(π/2)‖q‖²`), proven by orthogonal decomposition `q = ⟪u,q⟫•u + w`,
  pushforward to the independent product law `N(0,1) ⊗ N(0,‖w‖²)`, and Pythagoras.

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
- `JL/GaussianTail.lean` — the folded-normal sub-Gaussian estimate (`foldedNormal_subgaussian`) and
  its analytic supporting lemmas, built from scratch against mathlib.
- `JL/QJLDistortion.lean` — per-row and estimator variance, the Chebyshev distortion bound, and the
  unconditional exponential (sub-Gaussian / Chernoff) distortion bound.
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
in the development. The exponential distortion bound is now unconditional (the former
`IsPerRowSubgaussian` hypothesis is discharged), so it too reduces to the three axioms.

## Scope / not yet done

- **PolarQuant stage-1 MSE bound** and **full TurboQuant two-stage near-optimality** are out of
  scope here.
- **Mathlib-PR candidates.** The folded-normal sub-Gaussian development in `JL/GaussianTail.lean`
  fills a real gap: mathlib has no `erf` / Gaussian-CDF concentration, and these lemmas
  (`gaussian_foldedMGF`, `hasDerivAt_gTail`, `two_g_le`, `foldedNormal_subgaussian`) are natural
  upstream candidates, as are the small helpers `measurable_real_sign`, the `Real.sign`-valued
  `sign_mul_self`, `integral_abs_gaussianReal`, and `gaussianReal_mgf_id`.
- **Not upstreamed.** This lives as a standalone project, not (yet) part of mathlib; a couple of
  files still `import Mathlib` wholesale rather than minimal imports.

## License

Apache-2.0 (matching mathlib's license, to ease a future upstream). See `LICENSE`.
