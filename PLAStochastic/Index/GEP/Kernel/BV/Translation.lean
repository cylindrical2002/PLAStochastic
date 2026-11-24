import PLAStochastic.Index.GEP.Kernel.BV.VariationContraction
import PLAStochastic.Index.GEP.OrbitClosure.Defs
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Translation bounds for integrable BV representatives

The bound uses the variation of the whole zero extension, so endpoint jumps
are included. A final convolution against a bounded density therefore becomes
Lipschitz without differentiating that density.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators ENNReal

theorem kernelVariation_sum_norm {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    {u : ℕ → ℝ} (hu : Monotone u) (n : ℕ) :
    (∑ i ∈ Finset.range n, ‖f (u (i + 1)) - f (u i)‖) ≤ (eVariationOn f univ).toReal := by
  rw [← ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf,
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => norm_nonneg _)]
  have hh := eVariationOn.sum_le (f := f) (s := univ) (n := n) hu (fun _ => mem_univ _)
  simpa only [edist_dist, dist_eq_norm] using hh

theorem kernelTranslation_grid_bound {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (hi : Integrable f) {h : ℝ} (hh : 0 < h) (p : ℝ) (n : ℕ) :
    (∫ x in p..p + n * h, ‖f (x + h) - f x‖) ≤ h * (eVariationOn f univ).toReal := by
  let F := fun x => ‖f (x + h) - f x‖
  have hF : Integrable F := ((hi.comp_add_right h).sub hi).norm
  have hgrid (x : ℝ) :
      (∑ i ∈ Finset.range n, F (x + (p + i * h))) ≤ (eVariationOn f univ).toReal := by
    have hu : Monotone (fun i : ℕ => x + (p + i * h)) := by
      intro i j hij
      exact add_le_add_right (add_le_add_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) hh.le) p) x
    have hb := kernelVariation_sum_norm hf hu n
    convert hb using 1
    apply Finset.sum_congr rfl
    intro i _
    dsimp [F]
    congr 3
    push_cast
    ring
  calc
    (∫ x in p..p + n * h, F x) =
        ∑ i ∈ Finset.range n, ∫ x in (p + i * h)..(p + (i + 1) * h), F x := by
      simpa using (intervalIntegral.sum_integral_adjacent_intervals
        (a := fun i : ℕ => p + i * h) (n := n) (fun i _ => hF.intervalIntegrable)).symm
    _ = ∑ i ∈ Finset.range n, ∫ x in (0 : ℝ)..h, F (x + (p + i * h)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [intervalIntegral.integral_comp_add_right]
      congr 1 <;> ring
    _ = ∫ x in (0 : ℝ)..h, ∑ i ∈ Finset.range n, F (x + (p + i * h)) := by
      rw [intervalIntegral.integral_finsetSum]
      intro i _
      exact (hF.comp_add_right _).intervalIntegrable
    _ ≤ ∫ _x in (0 : ℝ)..h, (eVariationOn f univ).toReal := by
      apply intervalIntegral.integral_mono_on hh.le ?_ intervalIntegrable_const
        (fun x _ => hgrid x)
      exact (integrable_finsetSum (Finset.range n) (fun i _ =>
        hF.comp_add_right (p + i * h))).intervalIntegrable
    _ = h * (eVariationOn f univ).toReal := by simp

/-- Positive shifts have an L¹ modulus bounded by total variation times length. -/
theorem kernelTranslation_pos {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (hi : Integrable f) {h : ℝ} (hh : 0 < h) :
    (∫ x, ‖f (x + h) - f x‖) ≤ h * (eVariationOn f univ).toReal := by
  have hF : Integrable (fun x => ‖f (x + h) - f x‖) := ((hi.comp_add_right h).sub hi).norm
  have hpos : Tendsto (fun n : ℕ => (n : ℝ) * h) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hh
  have hneg : Tendsto (fun n : ℕ => -((n : ℝ) * h)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hpos
  have ht := intervalIntegral_tendsto_integral hF hneg hpos
  apply le_of_tendsto ht
  apply Eventually.of_forall
  intro n
  have hb := kernelTranslation_grid_bound hf hi hh (-((n : ℝ) * h)) (2 * n)
  convert hb using 1
  congr 1
  push_cast
  ring

theorem kernelTranslation_le {f : ℝ → ℂ} (hf : BoundedVariationOn f univ)
    (hi : Integrable f) (h : ℝ) :
    (∫ x, ‖f (x + h) - f x‖) ≤ |h| * (eVariationOn f univ).toReal := by
  rcases lt_trichotomy 0 h with hh | rfl | hh
  · simpa only [abs_of_pos hh] using kernelTranslation_pos hf hi hh
  · simp
  · have hp := kernelTranslation_pos hf hi (neg_pos.mpr hh)
    have he : (∫ x, ‖f (x + h) - f x‖) = ∫ x, ‖f (x + -h) - f x‖ := by
      calc
        _ = ∫ x, ‖f ((x + -h) + h) - f (x + -h)‖ :=
          (integral_add_right_eq_self (fun x => ‖f (x + h) - f x‖) (-h)).symm
        _ = _ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            dsimp only
            rw [show (x + -h) + h = x by ring, norm_sub_rev]
    rw [he, abs_of_neg hh]
    exact hp

/-- The actual convolution of an integrable BV function with a bounded-density
step law is Lipschitz. The density itself is only measurably bounded. -/
theorem kernel_kConv_lip {ρ : Measure ℝ} {D a β : ℝ}
    (hρ : LocBd D ρ) (hD : 0 ≤ D) (ha : a ≠ 0)
    {f : ℝ → ℂ} (hf : BoundedVariationOn f univ) (hi : Integrable f) (x y : ℝ) :
    ‖kConv ρ β a f x - kConv ρ β a f y‖ ≤
      (D / |a| * (eVariationOn f univ).toReal) * |x - y| := by
  have hdom : ρ ≤ ENNReal.ofReal D • (volume : Measure ℝ) := by
    apply Measure.le_iff.mpr
    intro A hA
    simpa only [Measure.smul_apply, smul_eq_mul] using hρ A hA
  have hvol (z : ℝ) : Integrable (fun t => f (z + β - a * t)) := by
    have hh := (hi.comp_add_left (z + β)).comp_mul_left' (neg_ne_zero.mpr ha)
    convert hh using 1
    funext t
    congr 1
    ring
  have hrho (z : ℝ) : Integrable (fun t => f (z + β - a * t)) ρ :=
    ((hvol z).smul_measure ENNReal.ofReal_ne_top).mono_measure hdom
  let F := fun z => ‖f (z + (x - y)) - f z‖
  have hF : Integrable F := ((hi.comp_add_right (x - y)).sub hi).norm
  have hdiff : Integrable (fun t => ‖f (x + β - a * t) - f (y + β - a * t)‖) :=
    ((hvol x).sub (hvol y)).norm
  have hcv : (∫ t, ‖f (x + β - a * t) - f (y + β - a * t)‖) = |a|⁻¹ * ∫ z, F z := by
    have he : (fun t => ‖f (x + β - a * t) - f (y + β - a * t)‖) =
        fun t => F ((y + β) + (-a) * t) := by
      funext t
      dsimp [F]
      congr 2 <;> congr 1 <;> ring
    rw [he, Measure.integral_comp_mul_left (fun z => F ((y + β) + z)) (-a),
      integral_add_left_eq_self, smul_eq_mul, abs_inv, abs_neg]
  unfold kConv
  rw [← integral_sub (hrho x) (hrho y)]
  calc
    _ ≤ ∫ t, ‖f (x + β - a * t) - f (y + β - a * t)‖ ∂ρ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, ‖f (x + β - a * t) - f (y + β - a * t)‖
        ∂(ENNReal.ofReal D • (volume : Measure ℝ)) :=
      integral_mono_measure hdom (Eventually.of_forall fun _ => norm_nonneg _)
        (hdiff.smul_measure ENNReal.ofReal_ne_top)
    _ = D / |a| * ∫ z, F z := by
      rw [integral_smul_measure, ENNReal.toReal_ofReal hD, smul_eq_mul, hcv]
      ring
    _ ≤ (D / |a| * (eVariationOn f univ).toReal) * |x - y| := by
      have hh := mul_le_mul_of_nonneg_left (kernelTranslation_le hf hi (x - y))
        (show 0 ≤ D / |a| by positivity)
      dsimp only [F]
      nlinarith

end
end PGM
