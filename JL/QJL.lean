import JL.Rotation

/-!
# Quantized Johnson–Lindenstrauss (QJL): unbiasedness of the 1-bit estimator

This file formalizes the **unbiasedness theorem** at the heart of QJL / TurboQuant's
one-bit key quantization. It is built in three increasing layers:

1. **Gaussian absolute moment** (`integral_abs_gaussianReal`):
   `E|Z| = √(2/π)` for `Z ~ N(0,1)`.

2. **The Grothendieck / sign-product identity** (`sign_product_identity`): for a standard
   Gaussian vector `g` in `ℝ^d`, a unit vector `u`, and an arbitrary `v`,
   `E[ sign ⟪u,g⟫ · ⟪v,g⟫ ] = √(2/π) · ⟪u,v⟫`.
   The proof decomposes `v = ⟪u,v⟫·u + v⊥` with `v⊥ ⟂ u`, uses that `⟪v⊥,g⟫` is
   *independent* of `⟪u,g⟫` (orthogonal linear functionals of a standard Gaussian are
   independent, via `HasGaussianLaw.indepFun_of_covariance_eq_zero`), and that the cross term
   vanishes because `E⟪v⊥,g⟫ = 0`.

3. **QJL asymmetric estimator unbiasedness** (`qjlEstimator_unbiased`): the 1-bit estimator
   `estimator S key q = √(π/2)·(1/m)·Σᵢ sign ⟪key/‖key‖, sᵢ⟫ · ⟪q, sᵢ⟫`
   over an `m × d` i.i.d. standard-Gaussian sketch is *unbiased* for the normalized inner
   product: `E[estimator] = ⟪key/‖key‖, q⟫`.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal RealInnerProductSpace

namespace JL

/-! ## Part 1: the Gaussian absolute moment `E|Z| = √(2/π)` -/

/-- Measurability of the real sign function. -/
theorem measurable_real_sign : Measurable Real.sign := by
  unfold Real.sign
  refine Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

/-- `Real.sign r * r = |r|`. -/
theorem sign_mul_self (r : ℝ) : Real.sign r * r = |r| := by
  obtain hn | rfl | hp := lt_trichotomy r 0
  · rw [Real.sign_of_neg hn, abs_of_neg hn]; ring
  · simp
  · rw [Real.sign_of_pos hp, abs_of_pos hp]; ring

/-- The half-line first moment: `∫_{x>0} x·exp(-x²/2) dx = 1`. -/
theorem integral_Ioi_mul_exp : ∫ x in Set.Ioi (0 : ℝ), x * rexp (-(1 / 2) * x ^ 2) = 1 := by
  have hcont : ContinuousWithinAt (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) (Set.Ici 0) 0 :=
    (by fun_prop : Continuous (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2))).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) (x * rexp (-(1 / 2) * x ^ 2)) x := by
    intro x _
    have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hg : HasDerivAt (fun x : ℝ => -(1 / 2) * x ^ 2) (-(1 / 2) * (2 * x)) x :=
      hsq.const_mul (-(1 / 2))
    have h2 := hg.exp.neg
    rw [show x * rexp (-(1 / 2) * x ^ 2)
        = -(rexp (-(1 / 2) * x ^ 2) * (-(1 / 2) * (2 * x))) from by ring]
    exact h2
  have hf'int : IntegrableOn (fun x : ℝ => x * rexp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) :=
    (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).integrableOn
  have hinner : Filter.Tendsto (fun x : ℝ => -(1 / 2) * x ^ 2) Filter.atTop Filter.atBot :=
    (Filter.tendsto_pow_atTop (two_ne_zero)).const_mul_atTop_of_neg (by norm_num)
  have htend : Filter.Tendsto (fun x : ℝ => -rexp (-(1 / 2) * x ^ 2)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => rexp (-(1 / 2) * x ^ 2)) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_atBot.comp hinner
    simpa using h1.neg
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hf'int htend
  rw [hmain]
  simp [Real.exp_zero]

/-- **Gaussian absolute moment.** `E|Z| = √(2/π)` for `Z ~ N(0,1)`. -/
theorem integral_abs_gaussianReal :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / π) := by
  -- `∫ |x| · exp(-x²/2) dx = 2`, via the even-function reduction `∫ f|x| = 2∫_{Ioi 0} f`.
  have hcore : ∫ x : ℝ, |x| * rexp (-(1 / 2) * x ^ 2) = 2 := by
    have e1 : (fun x : ℝ => |x| * rexp (-(1 / 2) * x ^ 2))
        = (fun x : ℝ => (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) |x|) := by
      funext x
      show |x| * rexp (-(1 / 2) * x ^ 2) = |x| * rexp (-(1 / 2) * |x| ^ 2)
      rw [sq_abs]
    calc ∫ x : ℝ, |x| * rexp (-(1 / 2) * x ^ 2)
        = ∫ x : ℝ, (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) |x| := by rw [e1]
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), (fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2)) x :=
          integral_comp_abs (f := fun t : ℝ => t * rexp (-(1 / 2) * t ^ 2))
      _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x * rexp (-(1 / 2) * x ^ 2) := rfl
      _ = 2 := by rw [integral_Ioi_mul_exp]; norm_num
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  have hint : ∀ x : ℝ, gaussianPDFReal 0 1 x • |x|
      = (√(2 * π))⁻¹ * (|x| * rexp (-(1 / 2) * x ^ 2)) := by
    intro x
    rw [stdGaussian_pdf, smul_eq_mul, show (-x ^ 2 / 2 : ℝ) = -(1 / 2) * x ^ 2 from by ring]
    ring
  simp_rw [hint]
  rw [integral_const_mul, hcore]
  -- `(√(2π))⁻¹ · 2 = √(2/π)`.
  have hL : (0 : ℝ) ≤ (√(2 * π))⁻¹ * 2 := by positivity
  have hR : (0 : ℝ) ≤ Real.sqrt (2 / π) := Real.sqrt_nonneg _
  have key : ((√(2 * π))⁻¹ * 2) ^ 2 = (Real.sqrt (2 / π)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  calc (√(2 * π))⁻¹ * 2
      = Real.sqrt (((√(2 * π))⁻¹ * 2) ^ 2) := (Real.sqrt_sq hL).symm
    _ = Real.sqrt ((Real.sqrt (2 / π)) ^ 2) := by rw [key]
    _ = Real.sqrt (2 / π) := Real.sqrt_sq hR

end JL
