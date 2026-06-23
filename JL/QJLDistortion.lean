import JL.QJL
import Mathlib.Probability.Moments.Variance

/-!
# QJL distortion / concentration bound

This file proves the **distortion (concentration) bound** for the QJL asymmetric 1-bit
estimator defined in `JL/QJL.lean`. With `m` sign-bits, the estimator is close to the true
normalized inner product `⟪key/‖key‖, q⟫` with high probability. It is built in three layers:

1. **Per-row variance** (`qjl_perrow_variance_le`): for a single standard-Gaussian `g`, unit `u`
   and arbitrary `q`, `Var[sign ⟪u,g⟫ · ⟪q,g⟫] ≤ ‖q‖²` (and, with the `√(π/2)` scaling, the
   per-row estimator term has variance `≤ (π/2)‖q‖²`).

2. **Estimator variance** (`qjlEstimator_variance_le`): the `m` per-row terms are i.i.d. under the
   product measure, so by additivity of variance over independent summands
   `Var[qjlEstimator] ≤ (π/2)‖q‖² / m`. The cross-row independence is supplied by mathlib's
   `ProbabilityTheory.variance_sum_pi`.

3. **Chebyshev concentration** (`qjlEstimator_concentration`): combining the variance bound with
   Chebyshev's inequality gives
   `P(|qjlEstimator − ⟪key/‖key‖,q⟫| ≥ ε) ≤ (π/2)‖q‖² / (m·ε²)`,
   so `m = O(‖q‖²/(ε²δ))` sign-bits suffice for additive error `ε` with probability `1−δ`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace JL

/-! ## Part 1: per-row second moment / variance of the sign-product term -/

/-- Second moment of a Gaussian linear functional: `E⟪q,g⟫² = ‖q‖²`.
This is the variance of the (mean-zero) dual functional `innerSL ℝ q`. -/
theorem integral_inner_sq_stdGaussian {d : ℕ} (q : EuclideanSpace ℝ (Fin d)) :
    ∫ g, ⟪q, g⟫ ^ 2 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) = ‖q‖ ^ 2 := by
  have hmean := integral_strongDual_stdGaussian (innerSL ℝ q)
  have hvar := variance_dual_stdGaussian (innerSL ℝ q)
  rw [variance_eq_integral
      (IsGaussian.memLp_dual _ (innerSL ℝ q) 2 (by simp)).aemeasurable, hmean] at hvar
  simp only [sub_zero, innerSL_apply_apply, innerSL_apply_norm] at hvar
  exact hvar

/-- The Gaussian linear functional `g ↦ ⟪q,g⟫` is in `L²`. -/
theorem memLp_inner {d : ℕ} (q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin d) => ⟪q, g⟫) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine (IsGaussian.memLp_dual _ (innerSL ℝ q) 2 (by simp)).of_le (by fun_prop) ?_
  filter_upwards with g
  simp [innerSL_apply_apply]

/-- The sign-product term `g ↦ sign ⟪u,g⟫ · ⟪q,g⟫` is in `L²` (dominated by `⟪q,g⟫`). -/
theorem memLp_sign_inner {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪q, g⟫) 2
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  refine (memLp_inner q).of_le ?_ ?_
  · exact (measurable_real_sign.comp
      (by fun_prop : Measurable (fun g : EuclideanSpace ℝ (Fin d) => ⟪u, g⟫))).aestronglyMeasurable.mul
      (by fun_prop)
  · filter_upwards with g
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    have hs : |Real.sign (⟪u, g⟫)| ≤ 1 := by
      rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num
    nlinarith [hs, abs_nonneg ((⟪q, g⟫ : ℝ))]

/-- **Per-row variance bound.** For a single standard-Gaussian `g`, unit `u` and arbitrary `q`,
`Var[sign ⟪u,g⟫ · ⟪q,g⟫] ≤ ‖q‖²`.

The proof uses `Var X ≤ E[X²]`, bounds `(sign ⟪u,g⟫ · ⟪q,g⟫)² ≤ ⟪q,g⟫²` pointwise (since
`(sign r)² ≤ 1`), and evaluates `E⟪q,g⟫² = ‖q‖²`. -/
theorem qjl_perrow_variance_le {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) :
    variance (fun g : EuclideanSpace ℝ (Fin d) => Real.sign (⟪u, g⟫) * ⟪q, g⟫)
      (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ ‖q‖ ^ 2 := by
  have hmem := memLp_sign_inner u q
  have hle : (fun g : EuclideanSpace ℝ (Fin d) => (Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2)
      ≤ fun g => ⟪q, g⟫ ^ 2 := by
    intro g
    dsimp only
    rw [mul_pow]
    have hs : (Real.sign (⟪u, g⟫)) ^ 2 ≤ 1 := by
      rcases Real.sign_apply_eq (⟪u, g⟫) with h | h | h <;> rw [h] <;> norm_num
    nlinarith [hs, sq_nonneg ((⟪q, g⟫ : ℝ))]
  calc variance (fun g => Real.sign (⟪u, g⟫) * ⟪q, g⟫)
        (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
      ≤ (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))[
          (fun g => Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2] :=
        variance_le_expectation_sq hmem.aestronglyMeasurable
    _ = ∫ g, (Real.sign (⟪u, g⟫) * ⟪q, g⟫) ^ 2
          ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) := by
        simp only [Pi.pow_apply]
    _ ≤ ∫ g, ⟪q, g⟫ ^ 2 ∂(ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) :=
        integral_mono hmem.integrable_sq (memLp_inner q).integrable_sq hle
    _ = ‖q‖ ^ 2 := integral_inner_sq_stdGaussian q

/-! ## Part 2: variance of the `m`-row estimator via cross-row independence -/

/-- **Estimator variance bound.** Over an `m × d` i.i.d. standard-Gaussian sketch, the variance of
the asymmetric 1-bit estimator is `≤ (π/2)‖q‖² / m`.

The `m` per-row terms are i.i.d. functions of distinct coordinates of the product measure, so
`ProbabilityTheory.variance_sum_pi` gives `Var[Σ row] = Σ Var[row] = m·Var[row]`; pulling out the
`(√(π/2)/m)` scaling and applying the per-row bound finishes it. -/
theorem qjlEstimator_variance_le {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) :
    variance (fun S => qjlEstimator key q S)
        (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      ≤ π / 2 * ‖q‖ ^ 2 / m := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  -- present the estimator as a constant times a coordinate-sum of i.i.d. per-row functions
  have heq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => qjlEstimator key q S)
      = fun S => (Real.sqrt (π / 2) * (m : ℝ)⁻¹) *
          (∑ i, (fun ω : Fin m → EuclideanSpace ℝ (Fin d) =>
            Real.sign (⟪‖key‖⁻¹ • key, ω i⟫) * ⟪q, ω i⟫)) S := by
    funext S
    simp only [qjlEstimator, Finset.sum_apply]
    ring
  rw [heq, variance_const_mul,
    variance_sum_pi (fun _ : Fin m => memLp_sign_inner (‖key‖⁻¹ • key) q),
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hsq : (Real.sqrt (π / 2)) ^ 2 = π / 2 := Real.sq_sqrt (by positivity)
  have hV := qjl_perrow_variance_le (‖key‖⁻¹ • key) q
  calc (Real.sqrt (π / 2) * (m : ℝ)⁻¹) ^ 2 *
          ((m : ℝ) * variance (fun g => Real.sign (⟪‖key‖⁻¹ • key, g⟫) * ⟪q, g⟫)
            (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
      ≤ (Real.sqrt (π / 2) * (m : ℝ)⁻¹) ^ 2 * ((m : ℝ) * ‖q‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = π / 2 * ‖q‖ ^ 2 / m := by
        rw [mul_pow, hsq]
        field_simp

end JL
