import PLAStochastic.ForMathlib.Probability.Distributions.LaplaceDensity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-! # The first and second moments of the actual Laplace smoothing kernel -/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set

theorem laplacePdf_neg (δ x : ℝ) : laplacePdf δ (-x) = laplacePdf δ x := by
  simp only [laplacePdf, abs_neg]

theorem integral_Ioi_sq_laplacePdf {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ in Ioi 0, x ^ 2 * laplacePdf δ x) = δ ^ 2 := by
  have hg := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 3)
    (r := 1 / δ) (by norm_num) (one_div_pos.mpr hδ)
  have he : (∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-x / δ)) = 2 * δ ^ 3 := by
    norm_num only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two,
      one_div_one_div, Real.rpow_ofNat, Real.Gamma_ofNat_eq_factorial,
      Nat.factorial, Nat.cast_ofNat] at hg
    convert hg using 1
    · apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      field_simp
    · ring
  calc
    (∫ x : ℝ in Ioi 0, x ^ 2 * laplacePdf δ x) =
        (1 / (2 * δ)) * ∫ x : ℝ in Ioi 0, x ^ 2 * Real.exp (-x / δ) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [laplacePdf, abs_of_pos hx]
      ring
    _ = δ ^ 2 := by rw [he]; field_simp

theorem sq_laplacePdf_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ => x ^ 2 * laplacePdf δ x) volume := by
  have hp : IntegrableOn (fun x : ℝ => x ^ 2 * laplacePdf δ x) (Ioi 0) volume := by
    by_contra h
    have hz := integral_undef h
    rw [integral_Ioi_sq_laplacePdf hδ] at hz
    exact (pow_pos hδ 2).ne' hz
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun x => x ^ 2 * laplacePdf δ x)
  have hg : Integrable g volume := hp.integrable_indicator measurableSet_Ioi
  refine (hg.add hg.comp_neg).congr (ae_of_all _ fun x => ?_)
  dsimp only [g, Pi.add_apply]
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge hx.le),
      indicator_of_mem (s := Ioi (0 : ℝ)) (neg_pos.mpr hx),
      neg_sq, laplacePdf_neg, zero_add]
  · simp
  · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hx,
      indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge (neg_nonpos.mpr hx.le)), add_zero]

theorem integral_sq_laplacePdf {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : ℝ, x ^ 2 * laplacePdf δ x) = 2 * δ ^ 2 := by
  let g : ℝ → ℝ := (Ioi (0 : ℝ)).indicator (fun x => x ^ 2 * laplacePdf δ x)
  have hg : Integrable g volume :=
    (sq_laplacePdf_integrable hδ).integrableOn.integrable_indicator measurableSet_Ioi
  have he : (fun x : ℝ => x ^ 2 * laplacePdf δ x) = fun x => g x + g (-x) := by
    funext x
    dsimp only [g]
    rcases lt_trichotomy x 0 with hx | rfl | hx
    · rw [indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge hx.le),
        indicator_of_mem (s := Ioi (0 : ℝ)) (neg_pos.mpr hx),
        neg_sq, laplacePdf_neg, zero_add]
    · simp
    · rw [indicator_of_mem (s := Ioi (0 : ℝ)) hx,
        indicator_of_notMem (s := Ioi (0 : ℝ)) (not_lt_of_ge (neg_nonpos.mpr hx.le)), add_zero]
  rw [he, integral_add hg hg.comp_neg, integral_neg_eq_self,
    integral_indicator measurableSet_Ioi, integral_Ioi_sq_laplacePdf hδ]
  ring

theorem id_mul_laplacePdf_integrable {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ => x * laplacePdf δ x) volume := by
  refine ((laplaceDensity δ hδ).integrable.add (sq_laplacePdf_integrable hδ)).mono' ?_ ?_
  · exact (measurable_id.mul (laplaceDensity δ hδ).measurable).aestronglyMeasurable
  · exact ae_of_all _ fun x => by
      change ‖x * laplacePdf δ x‖ ≤ laplacePdf δ x + x ^ 2 * laplacePdf δ x
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (laplacePdf_pos hδ x)]
      have hx : |x| ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (|x| - 1), sq_abs x]
      nlinarith [mul_le_mul_of_nonneg_right hx (laplacePdf_pos hδ x).le]

theorem integral_id_mul_laplacePdf (δ : ℝ) :
    (∫ x : ℝ, x * laplacePdf δ x) = 0 := by
  have he := integral_neg_eq_self (fun x : ℝ => x * laplacePdf δ x) volume
  simp only [laplacePdf_neg, neg_mul, integral_neg] at he
  linarith

end

end ProbabilityTheory
