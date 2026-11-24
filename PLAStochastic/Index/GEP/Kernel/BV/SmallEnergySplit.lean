import PLAStochastic.Index.GEP.Kernel.BV.LowPass
import PLAStochastic.ForMathlib.MeasureTheory.Integral.HalfLineTrace
import PLAStochastic.ForMathlib.Topology.EMetricSpace.ZeroExtensionVariation

/-!
# A small-energy state splits into an actual BV function and a small `L²` error

The representative is the zero extension of the actual hard-cutoff inverse
Fourier transform. Both new boundary jumps are controlled by exterior energy.
-/

namespace PGM
noncomputable section
open MeasureTheory FourierTransform Set Filter

/-- The regular part of an interval-supported state. -/
def kBVRegularPart (α w : ℝ) (u : ℝ → ℂ) : ℝ → ℂ :=
  (Icc α (α + w)).indicator (kBVLowPass u)

/-- Exterior low-pass mass is paid for by the cutoff approximation error. -/
theorem kBVLowPass_exterior_normSq_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {s : Set ℝ} (hs : MeasurableSet s) (hu0 : ∀ x ∈ s, u x = 0) :
    (∫ x in s, ‖kBVLowPass u x‖ ^ 2) ≤ kBVEnergy u := by
  have herr2 := h2.sub (kBVLowPass_memLp h1 h2)
  have herrI := (memLp_two_iff_integrable_sq_norm herr2.aestronglyMeasurable).1 herr2
  have he : (∫ x in s, ‖kBVLowPass u x‖ ^ 2) =
      ∫ x in s, ‖u x - kBVLowPass u x‖ ^ 2 := by
    apply setIntegral_congr_fun hs
    intro x hx
    simp only [hu0 x hx, zero_sub, norm_neg]
  rw [he]
  exact (setIntegral_le_integral herrI (Eventually.of_forall fun x => sq_nonneg _)).trans
    (kBVLowPass_error_le h1 h2)

/-- Each boundary trace has the energy scale needed by interval truncation. -/
theorem kBVLowPass_boundary_sq_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {α w : ℝ} (hu0 : ∀ x, x ∉ Icc α (α + w) → u x = 0) :
    ‖kBVLowPass u α‖ ^ 2 ≤ (1 + (2 * Real.pi) ^ 2) * kBVEnergy u ∧
    ‖kBVLowPass u (α + w)‖ ^ 2 ≤ (1 + (2 * Real.pi) ^ 2) * kBVEnergy u := by
  have hd := kBVLowPass_hasDerivAt h1 h2
  have hv2 := kBVLowPass_memLp h1 h2
  have hd2 := kBVLowPassDeriv_memLp h1 h2
  have hdI := (memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).1 hd2
  have hdle (s : Set ℝ) : (∫ x in s, ‖kBVLowPassDeriv u x‖ ^ 2) ≤
      (2 * Real.pi) ^ 2 * kBVEnergy u :=
    (setIntegral_le_integral hdI (Eventually.of_forall fun x => sq_nonneg _)).trans
      (kBVLowPass_deriv_normSq_le h1 h2)
  constructor
  · have htrace := kernelTrace_left hd hv2 hd2 α
    rw [integral_Iic_eq_integral_Iio] at htrace
    have he := kBVLowPass_exterior_normSq_le h1 h2 measurableSet_Iio
      (fun x hx => hu0 x (fun h => not_lt_of_ge h.1 hx))
    have he' := hdle (Iic α)
    nlinarith
  · have htrace := kernelTrace_right hd hv2 hd2 (α + w)
    have he := kBVLowPass_exterior_normSq_le h1 h2 measurableSet_Ioi
      (fun x hx => hu0 x (fun h => not_lt_of_ge h.2 hx))
    have he' := hdle (Ioi (α + w))
    nlinarith

/-- The interior integral of the actual derivative has the sharp `sqrt(w E)` scale. -/
theorem kBVLowPass_deriv_integral_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    (α : ℝ) {w : ℝ} (hw : 0 ≤ w) :
    (∫ x in Icc α (α + w), ‖kBVLowPassDeriv u x‖) ≤
      2 * Real.pi * Real.sqrt w * Real.sqrt (kBVEnergy u) := by
  let μ : Measure ℝ := volume.restrict (Icc α (α + w))
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.2 (by simp)
  have hd2 := kBVLowPassDeriv_memLp h1 h2
  have hi1 : Integrable (fun x => ‖kBVLowPassDeriv u x‖) μ :=
    (hd2.restrict (Icc α (α + w))).norm.integrable (by norm_num)
  have hi2 : Integrable (fun x => ‖kBVLowPassDeriv u x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).1 hd2).integrableOn
  have hcs := kill_sq_integral_le hi1 hi2
  have hvol : μ.real univ = w := by
    rw [measureReal_restrict_apply_univ, Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hvol] at hcs
  have hdi := (memLp_two_iff_integrable_sq_norm hd2.aestronglyMeasurable).1 hd2
  have hder := (setIntegral_le_integral (s := Icc α (α + w)) hdi
    (Eventually.of_forall fun x => sq_nonneg _)).trans (kBVLowPass_deriv_normSq_le h1 h2)
  have hcs' : (∫ x in Icc α (α + w), ‖kBVLowPassDeriv u x‖) ^ 2 ≤
      w * ((2 * Real.pi) ^ 2 * kBVEnergy u) :=
    hcs.trans (mul_le_mul_of_nonneg_left hder hw)
  apply (sq_le_sq₀ (integral_nonneg fun _ => norm_nonneg _) (by positivity)).mp
  calc _ ≤ w * ((2 * Real.pi) ^ 2 * kBVEnergy u) := hcs'
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hw, Real.sq_sqrt (kBVEnergy_nonneg u)]
      ring

/-- Cutting the low-pass representative back to the interval only improves its error. -/
theorem kBVRegularPart_error_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {α w : ℝ} (hu0 : ∀ x, x ∉ Icc α (α + w) → u x = 0) :
    kBVNormSq (fun x => u x - kBVRegularPart α w u x) ≤ kBVEnergy u := by
  have herr2 := h2.sub (kBVLowPass_memLp h1 h2)
  have herrI := (memLp_two_iff_integrable_sq_norm herr2.aestronglyMeasurable).1 herr2
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) herrI
    (Eventually.of_forall fun x => ?_)).trans (kBVLowPass_error_le h1 h2)
  by_cases hx : x ∈ Icc α (α + w)
  · simp only [kBVRegularPart, indicator_of_mem hx, Pi.sub_apply, le_refl]
  · simp only [kBVRegularPart, indicator_of_notMem hx, hu0 x hx, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    positivity

/-- The actual truncated low-frequency representative has bounded variation,
including both endpoint jumps, with the sharp `sqrt(w E(u))` factor. -/
theorem kBVRegularPart_variation_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2)
    {α w : ℝ} (hw : 1 ≤ w) (hu0 : ∀ x, x ∉ Icc α (α + w) → u x = 0) :
    eVariationOn (kBVRegularPart α w u) univ ≤
      ENNReal.ofReal (8 * Real.pi * Real.sqrt w * Real.sqrt (kBVEnergy u)) := by
  have hv := kernelVariation_indicator_le (by linarith : α ≤ α + w)
    (fun x _ => kBVLowPass_hasDerivAt h1 h2 x)
    ((kBVLowPassDeriv_continuous h1 h2).intervalIntegrable α (α + w))
  apply hv.trans
  apply ENNReal.ofReal_le_ofReal
  have hinter : (∫ x in α..α + w, ‖kBVLowPassDeriv u x‖) ≤
      2 * Real.pi * Real.sqrt w * Real.sqrt (kBVEnergy u) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
    exact kBVLowPass_deriv_integral_le h1 h2 α (by linarith)
  obtain ⟨hl, hr⟩ := kBVLowPass_boundary_sq_le h1 h2 hu0
  have hboundary (x : ℝ) (hx : ‖kBVLowPass u x‖ ^ 2 ≤
      (1 + (2 * Real.pi) ^ 2) * kBVEnergy u) :
      ‖kBVLowPass u x‖ ≤ (1 + 2 * Real.pi) * Real.sqrt (kBVEnergy u) := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt (kBVEnergy_nonneg u)]
    nlinarith [Real.pi_pos, kBVEnergy_nonneg u]
  have hl' := hboundary α hl
  have hr' := hboundary (α + w) hr
  have hwroot : 1 ≤ Real.sqrt w := by simpa using Real.sqrt_le_sqrt hw
  have hcoef : 2 * (1 + 2 * Real.pi) ≤ 6 * Real.pi * Real.sqrt w := by
    have hpi := Real.pi_gt_three
    nlinarith
  have hlast := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (kBVEnergy u))
  nlinarith

end
end PGM
