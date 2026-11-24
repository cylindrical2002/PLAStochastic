import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Negative moments from an exponential small-ball bound

If a positive random variable satisfies `μ {X ≤ t} ≤ C exp (-c / t)` for small `t`,
then every negative power of `X` is integrable. The proof applies the layer-cake
formula to `X⁻¹`; no density or distributional identity is assumed.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace BrownianAffine

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

/-- An exponential small-ball bound makes every negative power integrable. -/
theorem integrable_rpow_neg_of_small_ball [IsFiniteMeasure μ] (hX : AEMeasurable X μ)
    (hpos : ∀ᵐ ω ∂μ, 0 < X ω) {C c : ℝ} (hc : 0 < c)
    (hsmall : ∀ t : ℝ, 0 < t → t ≤ 1 →
      μ {ω | X ω ≤ t} ≤ ENNReal.ofReal (C * Real.exp (-c / t)))
    {s : ℝ} (hs : 0 < s) : Integrable (fun ω => X ω ^ (-s)) μ := by
  set K : ℝ := max C 0 + μ.real univ * Real.exp c with hK
  -- The tail of `X⁻¹` decays exponentially at every positive level.
  have htail (t : ℝ) (ht : 0 < t) :
      μ {ω | t < (X ω)⁻¹} ≤ ENNReal.ofReal (K * Real.exp (-(c * t))) := by
    rcases le_or_gt 1 t with ht1 | ht1
    · have hsub : {ω | t < (X ω)⁻¹} ⊆ {ω | X ω ≤ 1 / t} := by
        intro ω hω
        have hω' : t < (X ω)⁻¹ := hω
        have hx : 0 < X ω := inv_pos.mp (ht.trans hω')
        change X ω ≤ 1 / t
        rw [le_div_iff₀ ht]
        have h2 := mul_lt_mul_of_pos_right ((lt_inv_comm₀ ht hx).mp hω') ht
        rw [inv_mul_cancel₀ ht.ne'] at h2
        exact h2.le
      calc
        μ {ω | t < (X ω)⁻¹} ≤ μ {ω | X ω ≤ 1 / t} := measure_mono hsub
        _ ≤ ENNReal.ofReal (C * Real.exp (-c / (1 / t))) :=
          hsmall (1 / t) (by positivity) ((div_le_one ht).mpr ht1)
        _ ≤ ENNReal.ofReal (K * Real.exp (-(c * t))) := by
          apply ENNReal.ofReal_le_ofReal
          rw [one_div, div_inv_eq_mul, neg_mul]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          have : 0 ≤ μ.real univ * Real.exp c := by positivity
          linarith [le_max_left C 0]
    · calc
        μ {ω | t < (X ω)⁻¹} ≤ μ univ := measure_mono (subset_univ _)
        _ = ENNReal.ofReal (μ.real univ) := (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (K * Real.exp (-(c * t))) := by
          apply ENNReal.ofReal_le_ofReal
          have h1 : 1 ≤ Real.exp c * Real.exp (-(c * t)) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          have hm : 0 ≤ μ.real univ := measureReal_nonneg
          have he : 0 ≤ max C 0 * Real.exp (-(c * t)) := by positivity
          rw [hK, add_mul]
          nlinarith
  have hZ : AEMeasurable (fun ω => (X ω)⁻¹) μ := hX.inv
  have hZnn : 0 ≤ᵐ[μ] (fun ω => (X ω)⁻¹) := by
    filter_upwards [hpos] with ω hω
    exact (inv_pos.mpr hω).le
  have hint : IntegrableOn (fun t : ℝ => K * (t ^ (s - 1) * Real.exp (-c * t))) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s - 1) (b := c)
      (by linarith) (by norm_num) hc
    have h' : IntegrableOn (fun t : ℝ => t ^ (s - 1) * Real.exp (-c * t)) (Ioi 0) := by
      simpa only [Real.rpow_one] using h
    exact h'.const_mul K
  have hfin : ∫⁻ ω, ENNReal.ofReal ((X ω)⁻¹ ^ s) ∂μ ≠ ∞ := by
    rw [lintegral_rpow_eq_lintegral_meas_lt_mul μ hZnn hZ hs]
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ne_of_lt
    calc
      ∫⁻ t in Ioi 0, μ {a | t < (X a)⁻¹} * ENNReal.ofReal (t ^ (s - 1)) ≤
          ∫⁻ t in Ioi 0, ENNReal.ofReal (K * (t ^ (s - 1) * Real.exp (-c * t))) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        calc
          μ {a | t < (X a)⁻¹} * ENNReal.ofReal (t ^ (s - 1)) ≤
              ENNReal.ofReal (K * Real.exp (-(c * t))) * ENNReal.ofReal (t ^ (s - 1)) :=
            mul_le_mul_left (htail t ht) _
          _ = ENNReal.ofReal (K * (t ^ (s - 1) * Real.exp (-c * t))) := by
            rw [← ENNReal.ofReal_mul (by positivity)]
            congr 1
            ring_nf
      _ < ∞ := hint.lintegral_lt_top
  have hmeas : AEStronglyMeasurable (fun ω => X ω ^ (-s)) μ :=
    (hX.pow_const (-s)).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[μ] (fun ω => X ω ^ (-s)) := by
    filter_upwards [hpos] with ω hω
    exact Real.rpow_nonneg hω.le _
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas hnn).mp
  convert hfin using 1
  apply lintegral_congr_ae
  filter_upwards [hpos] with ω hω
  rw [Real.inv_rpow hω.le, Real.rpow_neg hω.le]

end BrownianAffine
