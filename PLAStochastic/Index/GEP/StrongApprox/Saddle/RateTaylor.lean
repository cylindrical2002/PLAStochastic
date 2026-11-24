import PLAStochastic.Index.GEP.StrongApprox.Saddle.Parameters
import Mathlib.Analysis.Calculus.Taylor

/-!
# WP5: Taylor bounds for the saddle rate function

The estimates are uniform on `saMeanRadius`. They include the symmetric
three-point exponent needed for the conditional density sandwich.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology

def saRateThird (vlo B θ : ℝ) : ℝ := saCumulantThird B θ * (4 / (3 * vlo)) ^ 3

theorem saRateThird_pos {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ) :
    0 < saRateThird vlo B θ := by
  unfold saRateThird
  exact mul_pos (saCumulantThird_pos B hθ) (pow_pos (by positivity) _)

theorem saMeanRadius_lt_full {vlo B θ : ℝ} (hvlo : 0 < vlo) (hθ : 0 < θ) :
    saMeanRadius vlo B θ < 3 / 4 * vlo * saTiltRadius vlo B θ := by
  have hr := saTiltRadius_pos (B := B) hvlo hθ
  unfold saMeanRadius
  nlinarith

variable {vlo vhi κ₃ B θ : ℝ} {ν : ProbabilityMeasure ℝ}

theorem UnivClass.iteratedDeriv_two_saRate_zero (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) :
    iteratedDeriv 2 (saRate vlo B θ ν s) 0 = (lawVar ν + s ^ 2)⁻¹ := by
  have hr := saTiltRadius_pos (B := B) hvlo hθ
  rw [h.iteratedDeriv_two_saRate hvlo hθ s (by simpa using (by positivity :
    (0 : ℝ) < 3 / 4 * vlo * saTiltRadius vlo B θ)), h.saSaddle_zero hvlo hθ s,
    h.iteratedDeriv_two_saSmoothCGF (by simpa using hθ) s,
    h.iteratedDeriv_two_centered_cgf_zero hθ]

theorem UnivClass.iteratedDeriv_two_saRate_lipschitz (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {a b : ℝ}
    (ha : |a| ≤ saMeanRadius vlo B θ) (hb : |b| ≤ saMeanRadius vlo B θ) :
    |iteratedDeriv 2 (saRate vlo B θ ν s) b - iteratedDeriv 2 (saRate vlo B θ ν s) a| ≤
      saRateThird vlo B θ * |b - a| := by
  let R := saMeanRadius vlo B θ
  have hfull : ∀ t ∈ Icc (-R) R, |t| < 3 / 4 * vlo * saTiltRadius vlo B θ :=
    fun t ht => (abs_le.mpr ht).trans_lt (saMeanRadius_lt_full hvlo hθ)
  have hd : ∀ t ∈ Icc (-R) R,
      DifferentiableAt ℝ (iteratedDeriv 2 (saRate vlo B θ ν s)) t :=
    fun t ht => (h.hasDerivAt_iteratedDeriv_two_saRate hvlo hθ s (hfull t ht)).differentiableAt
  have hbd : ∀ t ∈ Icc (-R) R,
      ‖deriv (iteratedDeriv 2 (saRate vlo B θ ν s)) t‖ ≤ saRateThird vlo B θ := by
    intro t ht
    rw [← iteratedDeriv_succ, Real.norm_eq_abs]
    exact h.abs_iteratedDeriv_three_saRate_le hvlo hθ s (hfull t ht)
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (-R) R).norm_image_sub_le_of_norm_deriv_le hd hbd (abs_le.mp ha) (abs_le.mp hb)

theorem UnivClass.iteratedDeriv_two_saRate_sub_zero_le (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {w : ℝ}
    (hw : |w| ≤ saMeanRadius vlo B θ) :
    |iteratedDeriv 2 (saRate vlo B θ ν s) w - (lawVar ν + s ^ 2)⁻¹| ≤
      saRateThird vlo B θ * |w| := by
  have hh := h.iteratedDeriv_two_saRate_lipschitz hvlo hθ s
    (a := 0) (b := w) (by simpa using (saMeanRadius_pos (B := B) hvlo hθ).le) hw
  rwa [h.iteratedDeriv_two_saRate_zero hvlo hθ s, sub_zero] at hh

/-- A third-order remainder valid for increments of either sign. -/
theorem UnivClass.saRate_taylor_two (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {u t : ℝ}
    (hut : |u| + |t| ≤ saMeanRadius vlo B θ) :
    |saRate vlo B θ ν s (u + t) - saRate vlo B θ ν s u -
        deriv (saRate vlo B θ ν s) u * t -
        iteratedDeriv 2 (saRate vlo B θ ν s) u * t ^ 2 / 2| ≤
      saRateThird vlo B θ * |t| ^ 3 / 6 := by
  by_cases ht : t = 0
  · simp [ht]
  let f := saRate vlo B θ ν s
  let R := saMeanRadius vlo B θ
  have hu : |u| ≤ R := by have := abs_nonneg t; linarith
  have hup : |u + t| ≤ R := (abs_add_le u t).trans hut
  have hwin : uIcc u (u + t) ⊆ Icc (-R) R := by
    exact (convex_Icc (-R) R).ordConnected.uIcc_subset (abs_le.mp hu) (abs_le.mp hup)
  have hfull : ∀ z ∈ uIcc u (u + t), |z| < 3 / 4 * vlo * saTiltRadius vlo B θ :=
    fun z hz => (abs_le.mpr (hwin hz)).trans_lt (saMeanRadius_lt_full hvlo hθ)
  have hct (n : ℕ) : ContDiffOn ℝ n f (uIcc u (u + t)) :=
    fun z hz => (h.analyticAt_saRate hvlo hθ s (hfull z hz)).contDiffAt.contDiffWithinAt
  have hne : u ≠ u + t := by intro he; apply ht; linarith
  obtain ⟨z, hz, heq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 2) hne (hct 3)
  have hdiff : UniqueDiffOn ℝ (uIcc u (u + t)) := uniqueDiffOn_uIcc hne
  have hbase : u ∈ uIcc u (u + t) := left_mem_uIcc
  have hder (k : ℕ) : iteratedDerivWithin k f (uIcc u (u + t)) u = iteratedDeriv k f u :=
    iteratedDerivWithin_eq_iteratedDeriv hdiff
      (h.analyticAt_saRate hvlo hθ s (hfull u hbase)).contDiffAt hbase
  simp only [taylorWithinEval_succ, taylor_within_zero_eval, hder,
    iteratedDeriv_one, Nat.factorial, Nat.cast_one, Nat.cast_zero, zero_add,
    Nat.cast_mul, mul_one, smul_eq_mul] at heq
  have hz' : z ∈ uIcc u (u + t) := ⟨hz.1.le, hz.2.le⟩
  have hb := h.abs_iteratedDeriv_three_saRate_le hvlo hθ s (hfull z hz')
  have hre : f (u + t) - f u - deriv f u * t - iteratedDeriv 2 f u * t ^ 2 / 2 =
      iteratedDeriv 3 f z * t ^ 3 / 6 := by
    norm_num at heq
    nlinarith [heq]
  change |f (u + t) - f u - deriv f u * t - iteratedDeriv 2 f u * t ^ 2 / 2| ≤ _
  rw [hre, abs_div, abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity)) (by norm_num)

/-- The symmetric three-point rate exponent is Gaussian up to a uniform cubic error. -/
theorem UnivClass.saRate_three_point (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) (s : ℝ) {u t : ℝ}
    (hut : |u| + |t| ≤ saMeanRadius vlo B θ) :
    |saRate vlo B θ ν s (u + t) + saRate vlo B θ ν s (u - t) -
        2 * saRate vlo B θ ν s u - t ^ 2 / (lawVar ν + s ^ 2)| ≤
      saRateThird vlo B θ * (|u| * t ^ 2 + |t| ^ 3 / 3) := by
  have hp := h.saRate_taylor_two hvlo hθ s hut
  have hn := h.saRate_taylor_two hvlo hθ s (u := u) (t := -t) (by simpa using hut)
  have hu : |u| ≤ saMeanRadius vlo B θ := by have := abs_nonneg t; linarith
  have hv := h.iteratedDeriv_two_saRate_sub_zero_le hvlo hθ s hu
  let f := saRate vlo B θ ν s
  let q := iteratedDeriv 2 f u
  let v := lawVar ν + s ^ 2
  have hid : f (u + t) + f (u - t) - 2 * f u - t ^ 2 / v =
      (f (u + t) - f u - deriv f u * t - q * t ^ 2 / 2) +
      (f (u + -t) - f u - deriv f u * (-t) - q * (-t) ^ 2 / 2) +
      (q - v⁻¹) * t ^ 2 := by
    simp only [sub_eq_add_neg, div_eq_mul_inv]
    ring
  change |f (u + t) + f (u - t) - 2 * f u - t ^ 2 / v| ≤ _
  rw [hid]
  calc
    _ ≤ |f (u + t) - f u - deriv f u * t - q * t ^ 2 / 2| +
        |f (u + -t) - f u - deriv f u * (-t) - q * (-t) ^ 2 / 2| +
        |(q - v⁻¹) * t ^ 2| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ saRateThird vlo B θ * |t| ^ 3 / 6 +
        saRateThird vlo B θ * |t| ^ 3 / 6 + saRateThird vlo B θ * |u| * t ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      exact add_le_add (add_le_add hp (by simpa only [abs_neg] using hn))
        (mul_le_mul_of_nonneg_right hv (sq_nonneg t))
    _ = _ := by ring

end

end PGM
