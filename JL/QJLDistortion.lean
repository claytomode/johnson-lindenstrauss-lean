import JL.QJL
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Moments.SubGaussian

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

/-! ## Part 3: Chebyshev distortion / concentration bound -/

/-- The estimator is in `L²` under the product measure (a constant times a finite sum of i.i.d.
per-row terms, each `L²`). -/
theorem qjlEstimator_memLp {m d : ℕ} (key q : EuclideanSpace ℝ (Fin d)) :
    MemLp (fun S => qjlEstimator key q S) 2
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  have heq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => qjlEstimator key q S)
      = fun S => (Real.sqrt (π / 2) * (m : ℝ)⁻¹) *
          ∑ i, Real.sign (⟪‖key‖⁻¹ • key, S i⟫) * ⟪q, S i⟫ := by
    funext S
    simp only [qjlEstimator]
    ring
  rw [heq]
  refine MemLp.const_mul ?_ _
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (memLp_sign_inner (‖key‖⁻¹ • key) q).comp_measurePreserving
      (measurePreserving_eval
        (μ := fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i))

/-- **QJL distortion / concentration bound (Chebyshev).** With `m` sign-bits, the asymmetric 1-bit
estimator deviates from the true normalized inner product `⟪key/‖key‖, q⟫` by at least `ε` with
probability at most `(π/2)‖q‖² / (m·ε²)`. Hence `m = O(‖q‖²/(ε²δ))` sign-bits suffice for additive
error `ε` with probability `1 − δ`. -/
theorem qjlEstimator_concentration {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (hkey : key ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ π / 2 * ‖q‖ ^ 2 / (m * ε ^ 2) := by
  have hmean : (Measure.pi
      (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))[
        fun S => qjlEstimator key q S] = ⟪‖key‖⁻¹ • key, q⟫ :=
    qjlEstimator_unbiased hm key q hkey
  have hCheb := meas_ge_le_variance_div_sq (qjlEstimator_memLp (m := m) key q) hε
  rw [hmean] at hCheb
  rw [measureReal_def]
  calc (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}).toReal
      ≤ (ENNReal.ofReal (variance (fun S => qjlEstimator key q S)
          (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
            / ε ^ 2)).toReal := ENNReal.toReal_mono (by finiteness) hCheb
    _ = variance (fun S => qjlEstimator key q S)
          (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))))
            / ε ^ 2 := ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (by positivity))
    _ ≤ (π / 2 * ‖q‖ ^ 2 / m) / ε ^ 2 :=
        (div_le_div_iff_of_pos_right (by positivity)).mpr (qjlEstimator_variance_le hm key q)
    _ = π / 2 * ‖q‖ ^ 2 / (m * ε ^ 2) := by rw [div_div]

/-! ## Part 4: exponential (sub-Gaussian) distortion bound

The Chebyshev bound above decays only polynomially in `m`. The classical QJL guarantee is an
*exponential* tail, obtained by showing the per-row sign-product term is sub-Gaussian and summing
over the `m` independent rows.

The single ingredient that is **not** provable from the current mathlib API is the per-row
sub-Gaussian moment-generating-function bound itself: bounding `E[exp(t·(√(π/2)·sign⟪u,g⟫·⟪q,g⟫))]`
sharply requires a folded-normal / `erf` sub-Gaussian estimate for `|⟪u,g⟫|` (a domination shortcut
is unavailable — the crude `exp(t|x|) ≤ exp(tx)+exp(-tx)` route loses a factor `2` per row, which is
fatal for `m` rows). We therefore isolate exactly this fact as the predicate `IsPerRowSubgaussian`
and discharge **everything else** (coordinate independence under `Measure.pi`, additivity of the
sub-Gaussian parameter over independent rows, the `1/m` rescaling, and the two-sided Chernoff bound)
fully and unconditionally. -/

open scoped RealInnerProductSpace in
/-- **The one remaining analytic gap.** For a (unit) vector `u` and arbitrary `q`, the centered,
`√(π/2)`-scaled per-row sign-product term `g ↦ √(π/2)·sign⟪u,g⟫·⟪q,g⟫ − ⟪u,q⟫` has a sub-Gaussian
moment generating function with variance proxy `(π/2)·‖q‖²` under the standard Gaussian.

This is classically true (with this sharp constant when `‖u‖ = 1`), but a Lean proof needs a
folded-normal sub-Gaussian estimate not yet in mathlib, so it is taken as a hypothesis by the
exponential distortion bound below. It is the *only* demoted step in the entire development. -/
@[reducible] def IsPerRowSubgaussian {d : ℕ} (u q : EuclideanSpace ℝ (Fin d)) : Prop :=
  HasSubgaussianMGF
    (fun g : EuclideanSpace ℝ (Fin d) =>
      Real.sqrt (π / 2) * Real.sign (⟪u, g⟫) * ⟪q, g⟫ - ⟪u, q⟫)
    ⟨π / 2 * ‖q‖ ^ 2, by positivity⟩
    (ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))

/-- **Centered estimator is sub-Gaussian.** Assuming the per-row sub-Gaussian MGF bound
(`IsPerRowSubgaussian`), the centered estimator `qjlEstimator − ⟪key/‖key‖, q⟫` is sub-Gaussian with
variance proxy `(π/2)·‖q‖² / m` under the `m`-fold product Gaussian, by summing the `m` i.i.d.
per-row terms (independent coordinates of `Measure.pi`) and rescaling by `1/m`. -/
theorem qjlEstimator_centered_hasSubgaussianMGF {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d))
    (hsub : IsPerRowSubgaussian (‖key‖⁻¹ • key) q) :
    HasSubgaussianMGF (fun S => qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)
      ⟨π / 2 * ‖q‖ ^ 2 / m, by positivity⟩
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
  set u : EuclideanSpace ℝ (Fin d) := ‖key‖⁻¹ • key with hu_def
  set G : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun g => Real.sqrt (π / 2) * Real.sign (⟪u, g⟫) * ⟪q, g⟫ - ⟪u, q⟫ with hG_def
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hGmeas : Measurable G := by
    refine Measurable.sub ?_ measurable_const
    refine Measurable.mul ?_ (by fun_prop)
    exact measurable_const.mul (measurable_real_sign.comp (by fun_prop))
  -- each coordinate is sub-Gaussian, transported from the single-Gaussian hypothesis
  have hcoord : ∀ i : Fin m,
      HasSubgaussianMGF (fun S : Fin m → EuclideanSpace ℝ (Fin d) => G (S i))
        (⟨π / 2 * ‖q‖ ^ 2, by positivity⟩ : ℝ≥0)
        (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) := by
    intro i
    have hmap : (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).map
          (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)
        = ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)) :=
      (measurePreserving_eval
        (μ := fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) i).map_eq
    have h2 : HasSubgaussianMGF G (⟨π / 2 * ‖q‖ ^ 2, by positivity⟩ : ℝ≥0)
        ((Measure.pi
          (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).map
            (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)) := by
      rw [hmap]; exact hsub
    exact HasSubgaussianMGF.of_map (X := G)
      (Y := fun f : Fin m → EuclideanSpace ℝ (Fin d) => f i)
      (measurable_pi_apply i).aemeasurable h2
  -- coordinates of a product measure are independent
  have hindep : iIndepFun (fun (i : Fin m) (S : Fin m → EuclideanSpace ℝ (Fin d)) => G (S i))
      (Measure.pi (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))) :=
    iIndepFun_pi (fun _ => hGmeas.aemeasurable)
  -- sum the m independent rows
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hindep
    (fun i (_ : i ∈ Finset.univ) => hcoord i)
  -- rescale by 1/m
  have hscale := hsum.const_mul ((m : ℝ)⁻¹)
  -- the rescaled coordinate-sum equals the centered estimator
  have hDeq : (fun S : Fin m → EuclideanSpace ℝ (Fin d) => (m : ℝ)⁻¹ * ∑ i, G (S i))
      = fun S => qjlEstimator key q S - ⟪u, q⟫ := by
    funext S
    simp only [hG_def, qjlEstimator, ← hu_def]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      show (∑ i, Real.sqrt (π / 2) * Real.sign (⟪u, S i⟫) * ⟪q, S i⟫)
          = Real.sqrt (π / 2) * ∑ i, Real.sign (⟪u, S i⟫) * ⟪q, S i⟫ by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp
  rw [hDeq] at hscale
  -- reconcile the variance proxy
  convert hscale using 2
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, NNReal.coe_sum]
  show π / 2 * ‖q‖ ^ 2 / (m : ℝ)
      = ((m : ℝ)⁻¹) ^ 2 * ∑ _i : Fin m, (π / 2 * ‖q‖ ^ 2)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

open scoped RealInnerProductSpace in
/-- **QJL exponential distortion bound (sub-Gaussian / Chernoff).** Assuming the per-row sub-Gaussian
MGF bound (`IsPerRowSubgaussian`), the asymmetric 1-bit estimator deviates from the true normalized
inner product `⟪key/‖key‖, q⟫` by at least `ε` with probability at most
`2 · exp(-m·ε² / (π·‖q‖²))`, an exponential (rather than polynomial) improvement over the Chebyshev
bound `qjlEstimator_concentration`. Hence `m = O(‖q‖²·log(1/δ)/ε²)` sign-bits suffice for additive
error `ε` with probability `1 − δ`. -/
theorem qjlEstimator_concentration_exp {m d : ℕ} (hm : 0 < m)
    (key q : EuclideanSpace ℝ (Fin d)) (_hkey : key ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hsub : IsPerRowSubgaussian (‖key‖⁻¹ • key) q) :
    (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
        {S | ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      ≤ 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := by
  have hDsub := qjlEstimator_centered_hasSubgaussianMGF hm key q hsub
  -- the Chernoff exponent simplifies to the clean constant (`↑⟨a,_⟩` is defeq `a`)
  have hcoe : -ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))
      = -((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2) := by
    rw [show (2 : ℝ) * (π / 2 * ‖q‖ ^ 2 / m) = π * ‖q‖ ^ 2 / m by ring, div_div_eq_mul_div]
    ring
  -- right tail (`↑⟨a,_⟩` is defeq `a`, so `change` rewrites the exponent denominator)
  have hR := hDsub.measure_ge_le hε.le
  change _ ≤ Real.exp (-ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))) at hR
  rw [hcoe] at hR
  -- left tail
  have hL := hDsub.neg.measure_ge_le hε.le
  simp only [Pi.neg_apply] at hL
  change _ ≤ Real.exp (-ε ^ 2 / (2 * (π / 2 * ‖q‖ ^ 2 / (m : ℝ)))) at hL
  rw [hcoe] at hL
  -- split the absolute-value event into the two one-sided events
  have hset : {S : Fin m → EuclideanSpace ℝ (Fin d) |
        ε ≤ |qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫|}
      = {S | ε ≤ qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫}
        ∪ {S | ε ≤ -(qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)} := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hset]
  refine (measureReal_union_le _ _).trans ?_
  calc (Measure.pi
        (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
          {S | ε ≤ qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫}
        + (Measure.pi
            (fun _ : Fin m => ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d)))).real
          {S | ε ≤ -(qjlEstimator key q S - ⟪‖key‖⁻¹ • key, q⟫)}
      ≤ Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2))
          + Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := add_le_add hR hL
    _ = 2 * Real.exp (-((m : ℝ) * ε ^ 2) / (π * ‖q‖ ^ 2)) := by ring

end JL
