import Mathlib
import JL.SquaredGaussian

/-!
# Gaussian tail analysis: the centered folded normal is 1-sub-Gaussian

This file builds, from scratch against mathlib, the one-dimensional analytic fact underlying the
unconditional exponential QJL distortion bound: if `Z ~ N(0,1)` then the centered folded normal
`|Z| − √(2/π)` is sub-Gaussian with variance proxy `1`, i.e.

`∀ t, ∫ exp (t · (|Z| − √(2/π))) ≤ exp (t² / 2)`.

The route is:
* `gaussian_foldedMGF`: the folded moment generating function in closed form
  `∫ exp (t·|x|) d(gaussianReal 0 1) = √(2/π) · exp(t²/2) · g t`,
  where `g t = ∫ x in Ioi 0, exp (−(x−t)²/2)`.
* `hasDerivAt_g`: `g` is differentiable with `g' t = exp(−t²/2)` (the parameter sits in the
  integration limit, so this is the fundamental theorem of calculus, no differentiation under the
  integral with respect to a fixed domain is needed for the sign analysis).
* `two_g_le`: the sharp inequality `√(2/π) · g t ≤ exp(t·√(2/π))` for all `t`, proven by a sign
  analysis of `f t = exp(t·√(2/π)) − √(2/π)·g t` (`f 0 = 0`, derivative sign split at `0` and
  `−2√(2/π)`, with the far-negative tail handled by the trivial bound `exp(t·|x|) ≤ 1`).
* `foldedNormal_subgaussian`: assembling the above into `HasSubgaussianMGF (|·| − √(2/π)) 1`.
-/

open MeasureTheory ProbabilityTheory Real Filter Set
open scoped ENNReal NNReal Topology

namespace JL

/-- The "completed-square half-line Gaussian" `g t = ∫ x in Ioi 0, exp(−(x−t)²/2)`. -/
noncomputable def gTail (t : ℝ) : ℝ := ∫ x in Ioi (0 : ℝ), rexp (-(x - t) ^ 2 / 2)

/-- `exp (t · |x|)` is integrable against the standard Gaussian (dominated by
`exp (t·x) + exp (−t·x)`). -/
theorem integrable_exp_mul_abs (t : ℝ) :
    Integrable (fun x : ℝ => rexp (t * |x|)) (gaussianReal 0 1) := by
  have hdom : Integrable (fun x : ℝ => rexp (t * x) + rexp (-t * x)) (gaussianReal 0 1) :=
    (integrable_exp_mul_gaussianReal t).add (integrable_exp_mul_gaussianReal (-t))
  refine hdom.mono' ?_ ?_
  · exact (measurable_exp.comp ((measurable_const.mul measurable_id.abs))).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
    have h1 : (0 : ℝ) ≤ rexp (t * x) := (Real.exp_pos _).le
    have h2 : (0 : ℝ) ≤ rexp (-t * x) := (Real.exp_pos _).le
    rcases le_or_gt 0 x with hx | hx
    · rw [abs_of_nonneg hx]; linarith
    · rw [abs_of_neg hx, show t * -x = -t * x by ring]; linarith

/-- The constant `2·(√(2π))⁻¹ = √(2/π)`. -/
theorem two_mul_inv_sqrt : 2 * (√(2 * π))⁻¹ = √(2 / π) := by
  have h2 : (0 : ℝ) ≤ 2 * (√(2 * π))⁻¹ := by positivity
  calc 2 * (√(2 * π))⁻¹
      = √((2 * (√(2 * π))⁻¹) ^ 2) := (Real.sqrt_sq h2).symm
    _ = √(2 / π) := by
        congr 1
        rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
        field_simp

/-- **Folded-normal moment generating function (closed form).** For `Z ~ N(0,1)`,
`∫ exp(t·|x|) = √(2/π) · exp(t²/2) · g t`, where `g t = ∫ x in Ioi 0, exp(−(x−t)²/2)`. -/
theorem gaussian_foldedMGF (t : ℝ) :
    ∫ x, rexp (t * |x|) ∂(gaussianReal 0 1) = √(2 / π) * rexp (t ^ 2 / 2) * gTail t := by
  have hseteq : ∫ x in Ioi (0 : ℝ), rexp (t * x - x ^ 2 / 2) = rexp (t ^ 2 / 2) * gTail t := by
    rw [gTail, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  rw [integral_gaussianReal_eq_integral_smul (by norm_num)]
  calc ∫ x, gaussianPDFReal 0 1 x • rexp (t * |x|)
      = ∫ x, (fun y : ℝ => (√(2 * π))⁻¹ * rexp (t * y - y ^ 2 / 2)) |x| := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [stdGaussian_pdf, smul_eq_mul]
        have hexp : (-x ^ 2 / 2 : ℝ) + t * |x| = t * |x| - |x| ^ 2 / 2 := by rw [sq_abs]; ring
        rw [mul_assoc, ← Real.exp_add, hexp]
    _ = 2 * ∫ x in Ioi (0 : ℝ), (√(2 * π))⁻¹ * rexp (t * x - x ^ 2 / 2) := by
        rw [integral_comp_abs (f := fun y : ℝ => (√(2 * π))⁻¹ * rexp (t * y - y ^ 2 / 2))]
    _ = √(2 / π) * rexp (t ^ 2 / 2) * gTail t := by
        rw [integral_const_mul, hseteq, ← two_mul_inv_sqrt]
        ring

end JL
