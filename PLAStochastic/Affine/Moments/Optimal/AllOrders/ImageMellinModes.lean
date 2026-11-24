import PLAStochastic.Affine.Moments.Optimal.Survival.Image.Convergence
import PLAStochastic.ForMathlib.Analysis.MellinTransform.ExponentialIntegral

/-! # Mellin integrals of the individual optimal image modes

For `t > 0`, the image mode with index `m = n + 1` is a linear combination of
`exp (-a / t)`, `t exp (-a / t)` and `E₁ (a / t)` with `a = 8 m²` and
`a = 8 m (m + 1)`. Each of these has an explicit Mellin integral for
`re q < -1`; this file records the resulting closed form of
`∫ t in Ioi 0, t ^ (q - 1) * mode_n t` before any summation over `n`.
-/
noncomputable section
open MeasureTheory Set Complex
namespace BrownianAffine

/-- The Mellin integrand `t ^ (q - 1) exp (-c / t)`. -/
def mellinInvExp (q : ℂ) (c t : ℝ) : ℂ :=
  (t : ℂ) ^ (q - 1) * ((Real.exp (-c / t) : ℝ) : ℂ)

/-- The Mellin integrand `t ^ q exp (-c / t)`. -/
def mellinInvExpSucc (q : ℂ) (c t : ℝ) : ℂ :=
  (t : ℂ) ^ q * ((Real.exp (-c / t) : ℝ) : ℂ)

/-- The Mellin integrand `t ^ (q - 1) E₁ (c / t)`. -/
def mellinInvE1 (q : ℂ) (c t : ℝ) : ℂ :=
  (t : ℂ) ^ (q - 1) * ((exponentialIntegralE1 (c / t) : ℝ) : ℂ)

/-- The common shape of one image mode, multiplied by `t ^ (q - 1)`. -/
def imageModeShape (q α β γ δ ε ζ : ℂ) (a b t : ℝ) : ℂ :=
  α * mellinInvExp q a t + β * mellinInvExpSucc q a t + γ * mellinInvExp q b t +
    δ * mellinInvExpSucc q b t + ε * mellinInvE1 q a t - ζ * mellinInvE1 q b t

theorem integrableOn_imageModeShape {q : ℂ} (hq : q.re < -1) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (α β γ δ ε ζ : ℂ) :
    IntegrableOn (imageModeShape q α β γ δ ε ζ a b) (Ioi 0) := by
  have hq0 : q.re < 0 := by linarith
  have i1 := (integrableOn_cpow_mul_exp_neg_div hq0 ha).const_mul α
  have i2 := (integrableOn_cpow_mul_exp_neg_div_succ hq ha).const_mul β
  have i3 := (integrableOn_cpow_mul_exp_neg_div hq0 hb).const_mul γ
  have i4 := (integrableOn_cpow_mul_exp_neg_div_succ hq hb).const_mul δ
  have i5 := (integrableOn_cpow_mul_exponentialIntegralE1_div hq0 ha).const_mul ε
  have i6 := (integrableOn_cpow_mul_exponentialIntegralE1_div hq0 hb).const_mul ζ
  exact ((((i1.add i2).add i3).add i4).add i5).sub i6

theorem integral_imageModeShape {q : ℂ} (hq : q.re < -1) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (α β γ δ ε ζ : ℂ) :
    ∫ t in Ioi (0 : ℝ), imageModeShape q α β γ δ ε ζ a b t =
      α * ((a : ℂ) ^ q * Gamma (-q)) + β * ((a : ℂ) ^ (q + 1) * Gamma (-(q + 1))) +
        γ * ((b : ℂ) ^ q * Gamma (-q)) + δ * ((b : ℂ) ^ (q + 1) * Gamma (-(q + 1))) +
        ε * (-((a : ℂ) ^ q * Gamma (-q)) / q) - ζ * (-((b : ℂ) ^ q * Gamma (-q)) / q) := by
  have hq0 : q.re < 0 := by linarith
  have i1 := (integrableOn_cpow_mul_exp_neg_div hq0 ha).const_mul α
  have i2 := (integrableOn_cpow_mul_exp_neg_div_succ hq ha).const_mul β
  have i3 := (integrableOn_cpow_mul_exp_neg_div hq0 hb).const_mul γ
  have i4 := (integrableOn_cpow_mul_exp_neg_div_succ hq hb).const_mul δ
  have i5 := (integrableOn_cpow_mul_exponentialIntegralE1_div hq0 ha).const_mul ε
  have i6 := (integrableOn_cpow_mul_exponentialIntegralE1_div hq0 hb).const_mul ζ
  unfold imageModeShape mellinInvExp mellinInvExpSucc mellinInvE1
  rw [integral_sub ?_ i6, integral_add ?_ i5, integral_add ?_ i4, integral_add ?_ i3,
    integral_add i1 i2]
  · simp only [integral_const_mul]
    rw [integral_cpow_mul_exp_neg_div hq0 ha, integral_cpow_mul_exp_neg_div_succ hq ha,
      integral_cpow_mul_exp_neg_div hq0 hb, integral_cpow_mul_exp_neg_div_succ hq hb,
      integral_cpow_mul_exponentialIntegralE1_div hq0 ha,
      integral_cpow_mul_exponentialIntegralE1_div hq0 hb]
  all_goals first
    | exact i1.add i2
    | exact (i1.add i2).add i3
    | exact ((i1.add i2).add i3).add i4
    | exact (((i1.add i2).add i3).add i4).add i5

/-- The first decay rate `8 m²` of the image mode `n`, with `m = n + 1`. -/
def imageRateA (n : ℕ) : ℝ := 8 * ((n : ℝ) + 1) ^ 2

/-- The second decay rate `8 m (m + 1)` of the image mode `n`, with `m = n + 1`. -/
def imageRateB (n : ℕ) : ℝ := 8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)

theorem imageRateA_pos (n : ℕ) : 0 < imageRateA n := by
  unfold imageRateA
  positivity

theorem imageRateB_pos (n : ℕ) : 0 < imageRateB n := by
  unfold imageRateB
  positivity

/-- The six complex coefficients of the image mode `n`, in terms of `M = n + 1`. -/
def imageModeShapeAt (q : ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  let M : ℂ := (n : ℂ) + 1
  imageModeShape q (-8 * (2 * M ^ 2 + 1) / 3) ((1 - 1 / M ^ 2) / 6)
    ((2 * M + 1) ^ 4 / (3 * M * (M + 1))) ((-2 + 1 / M ^ 2 + 1 / (M + 1) ^ 2) / 12)
    (4 * M ^ 2) (4 * M * (M + 1)) (imageRateA n) (imageRateB n) t

theorem cpow_mellin_optimalImageMode (q : ℂ) (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ) = imageModeShapeAt q n t := by
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hpow : (t : ℂ) ^ q = (t : ℂ) ^ (q - 1) * t := by
    have h := cpow_add (q - 1) 1 ht'
    rw [sub_add_cancel, cpow_one] at h
    exact h
  rw [optimalImageMode_of_pos n ht]
  simp only [imageModeShapeAt, imageModeShape, mellinInvExp, mellinInvExpSucc, mellinInvE1,
    imageRateA, imageRateB, optimalImageCoefficientA, optimalImageCoefficientB, hpow]
  have e1 : Real.exp (-8 * ((n : ℝ) + 1) ^ 2 / t) =
      Real.exp (-(8 * ((n : ℝ) + 1) ^ 2) / t) := by ring_nf
  have e2 : Real.exp (-8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / t) =
      Real.exp (-(8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) / t) := by ring_nf
  rw [e1, e2]
  generalize Real.exp (-(8 * ((n : ℝ) + 1) ^ 2) / t) = X1
  generalize Real.exp (-(8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1)) / t) = X2
  generalize exponentialIntegralE1 (8 * ((n : ℝ) + 1) ^ 2 / t) = Y1
  generalize exponentialIntegralE1 (8 * ((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) / t) = Y2
  generalize (t : ℂ) ^ (q - 1) = T
  push_cast
  ring

theorem integrableOn_mellin_optimalImageMode {q : ℂ} (hq : q.re < -1) (n : ℕ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ))
      (Ioi 0) := by
  refine IntegrableOn.congr_fun (μ := volume)
    (integrableOn_imageModeShape hq (imageRateA_pos n) (imageRateB_pos n) _ _ _ _ _ _)
    (fun t ht => (cpow_mellin_optimalImageMode q n ht).symm) measurableSet_Ioi

theorem integral_mellin_optimalImageMode {q : ℂ} (hq : q.re < -1) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (q - 1) * ((optimalImageMode n t : ℝ) : ℂ) =
      let M : ℂ := (n : ℂ) + 1
      let a : ℂ := (imageRateA n : ℂ)
      let b : ℂ := (imageRateB n : ℂ)
      (-8 * (2 * M ^ 2 + 1) / 3) * (a ^ q * Gamma (-q)) +
        ((1 - 1 / M ^ 2) / 6) * (a ^ (q + 1) * Gamma (-(q + 1))) +
        ((2 * M + 1) ^ 4 / (3 * M * (M + 1))) * (b ^ q * Gamma (-q)) +
        ((-2 + 1 / M ^ 2 + 1 / (M + 1) ^ 2) / 12) * (b ^ (q + 1) * Gamma (-(q + 1))) +
        (4 * M ^ 2) * (-(a ^ q * Gamma (-q)) / q) -
        (4 * M * (M + 1)) * (-(b ^ q * Gamma (-q)) / q) := by
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun t ht => cpow_mellin_optimalImageMode q n ht)]
  exact integral_imageModeShape hq (imageRateA_pos n) (imageRateB_pos n) _ _ _ _ _ _

end BrownianAffine
