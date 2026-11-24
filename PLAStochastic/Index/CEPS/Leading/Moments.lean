import PLAStochastic.Index.CEPS.Leading.Distance
import PLAStochastic.Index.GEP.PointwiseSmall.SegmentFacts

/-!
# The first two actual stopped-sum moments

Exponential integrability permits polynomial tests of the proved weighted
distance estimate. All limits concern the actual one-layer map.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Topology Set
open scoped ENNReal

theorem ceps_rawLaw_nonneg {ν : ProbabilityMeasure ℝ} (hν : (ν : Measure ℝ) (Iic 0) = 0)
    (eps : ℝ) : (rawLaw eps ν : Measure ℝ) (Iio 0) = 0 := by
  change ((iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2)) (Iio 0) = 0
  have hW : Measurable (fun g : ℕ → ℝ => lawVar ν * stopSum eps g / eps ^ 2) :=
    (measurable_const.mul (measurable_stopSum eps)).div_const _
  rw [Measure.map_apply hW measurableSet_Iio]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [ae_pos_iidLaw hν] with g hg
  have hS := rawAsm_stopSum_nonneg (eps := eps) fun j => (hg j).le
  have hv : 0 ≤ lawVar ν := integral_nonneg fun x => sq_nonneg _
  simp only [mem_preimage, mem_Iio, not_lt]
  positivity

theorem cepsTau_exp_integrable : ∃ ζ : ℝ, 0 < ζ ∧
    Integrable (fun x : ℝ => Real.exp (ζ * x)) (cepsTau : Measure ℝ) := by
  obtain ⟨ζ, hζ, hi⟩ := optimalUnitLifetime_exp_neighborhood isBrownianReal_canonicalBrownian
  refine ⟨ζ, hζ, ?_⟩
  change Integrable (fun x : ℝ => Real.exp (ζ * x)) (canonicalPreBrownianMeasure.map
    (optimalUnitLifetime canonicalBrownian))
  apply (integrable_map_measure (by fun_prop)
    (aemeasurable_optimalUnitLifetime isBrownianReal_canonicalBrownian)).mpr
  exact hi ζ (by rw [abs_of_pos hζ])

/-- A uniform positive exponential weight for the actual raw one-layer law. -/
theorem ceps_rawLaw_exp_integrable_on_regular_class {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ eps : ℝ in atTop, ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → Integrable (fun x : ℝ => Real.exp (c * x))
        (rawLaw eps ν : Measure ℝ) := by
  let b := regB vhi
  let β := regBeta D θ vlo
  let vmin := regV vlo
  have hvm : 0 < vmin := regV_pos hvlo
  have hb : 0 < b := hvm.trans_le (regV_le_regB hv)
  obtain ⟨e₂, he₂⟩ := lawPhi_expMom (b := b) (β := β) hvm (half_pos hθ)
    (show 0 < 2 * D / θ by positivity)
  let c := θK * vmin / (cPlus * b)
  have hc : 0 < c := by dsimp [c]; exact div_pos (mul_pos θK_pos hvm) (mul_pos cPlus_pos hb)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop e₂, eventually_ge_atTop (epsZero b β)]
    with eps he₂' hez
  intro ν hν
  have hm := hν.momClass hθ hvlo
  obtain ⟨_, heps1, _, _, _, _, hCm, hCp, _⟩ := momClass_setup hvm hez hm
  have heps : 0 < eps := by linarith
  have hvν : 0 < lawVar ν := hvm.trans_le hm.var_ge
  have hC : 0 < lawC eps ν := (by positivity : 0 < eps ^ 2 / lawVar ν / 128).trans_le hCm
  have hS : ∀ᵐ g ∂(iidLaw ν), 0 ≤ stopSum eps g := by
    filter_upwards [ae_pos_iidLaw hm.pos] with g hg
    exact rawAsm_stopSum_nonneg fun j => (hg j).le
  have hout := he₂ eps he₂' ν hm (hν.expMom hθ)
  have hi : Integrable (fun g => Real.exp (θK * (stopSum eps g / lawC eps ν)))
      (iidLaw ν) := by
    have h := hout.integrable
    change Integrable (fun x : ℝ => Real.exp (θK * x))
      ((iidLaw ν).map (fun g => stopSum eps g / lawC eps ν)) at h
    exact (integrable_map_measure (by fun_prop)
      ((measurable_stopSum eps).div_const _).aemeasurable).mp h
  have hscale : c * lawVar ν * lawC eps ν ≤ θK * eps ^ 2 := by
    calc
      c * lawVar ν * lawC eps ν ≤ c * b * (cPlus * (eps ^ 2 / vmin)) := by
        gcongr
        · exact hm.var_le
        · exact hCp.trans (mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_left (sq_nonneg eps) hvm hm.var_ge) cPlus_pos.le)
      _ = θK * eps ^ 2 := by dsimp [c]; field_simp [hb.ne', hvm.ne', cPlus_pos.ne']
  change Integrable (fun x : ℝ => Real.exp (c * x))
    ((iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2))
  have hW : Measurable (fun g : ℕ → ℝ => lawVar ν * stopSum eps g / eps ^ 2) :=
    (measurable_const.mul (measurable_stopSum eps)).div_const _
  apply (integrable_map_measure (by fun_prop) hW.aemeasurable).mpr
  refine hi.mono' (((measurable_const.mul hW).exp).aestronglyMeasurable) ?_
  filter_upwards [hS] with g hg
  change ‖Real.exp (c * (lawVar ν * stopSum eps g / eps ^ 2))‖ ≤
    Real.exp (θK * (stopSum eps g / lawC eps ν))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  rw [← mul_div_assoc, ← mul_div_assoc, div_le_div_iff₀ (sq_pos_of_pos heps) hC]
  nlinarith [mul_le_mul_of_nonneg_right hscale hg]

private theorem ceps_integrable_mul_exp {μ : Measure ℝ} (hμ : μ (Iio 0) = 0)
    {γ ζ : ℝ} (hγζ : γ < ζ) (hi : Integrable (fun x : ℝ => Real.exp (ζ * x)) μ) :
    Integrable (fun x : ℝ => x * Real.exp (γ * x)) μ := by
  refine (hi.const_mul (1 / (ζ - γ))).mono' (by fun_prop) ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx0 (Real.exp_pos _).le)]
  simpa only [div_eq_mul_inv, mul_comm, mul_one] using mul_exp_le_exp_div (x := x) hγζ

private theorem ceps_integral_testFn_one {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) :
    (∫ x, testFn (fun _ => (1 : ℝ)) x ∂μ) = ∫ x, x ∂μ := by
  apply integral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rcases hx0.eq_or_lt with h | h
  · rw [← h, testFn_nonneg_arg le_rfl]
  · exact testFn_one h

private theorem ceps_integral_testFn_two {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) :
    (∫ x, testFn (fun t => 2 * t) x ∂μ) = ∫ x, x ^ 2 ∂μ := by
  apply integral_congr_ae
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμ] with x hx
  have hx0 : 0 ≤ x := by simpa using hx
  rcases hx0.eq_or_lt with h | h
  · rw [← h, testFn_nonneg_arg le_rfl]; simp
  · exact testFn_two_mul h

/-- The first two actual raw moments have the Brownian limits on every regular law. -/
theorem ceps_raw_moments_tendsto {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    Tendsto (fun eps => ∫ x, x ∂(rawLaw eps ν : Measure ℝ)) atTop (𝓝 optimalMeanConstant) ∧
      Tendsto (fun eps => ∫ x, x ^ 2 ∂(rawLaw eps ν : Measure ℝ)) atTop
        (𝓝 optimalSecondMomentConstant) := by
  obtain ⟨γ₀, K, hγ₀, hK, hdist⟩ := ceps_rawLaw_distance_on_regular_class hD hθ hvlo hv
  obtain ⟨c, hc, hraw⟩ := ceps_rawLaw_exp_integrable_on_regular_class hD hθ hvlo hv
  obtain ⟨ζ, hζ, hτ⟩ := cepsTau_exp_integrable
  let γ := min γ₀ (min (c / 2) (ζ / 2))
  have hγ : 0 < γ := lt_min hγ₀ (lt_min (half_pos hc) (half_pos hζ))
  have hγc : γ < c := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hγζ : γ < ζ := (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hτi := ceps_integrable_mul_exp cepsTau_nonneg hγζ hτ
  have hpos := ceps_rawLaw_nonneg (hν.momClass hθ hvlo).pos
  have hbound : ∀ᶠ eps : ℝ in atTop,
      |(∫ x, x ∂(rawLaw eps ν : Measure ℝ)) - optimalMeanConstant| ≤
        K * eps ^ (-(17 / 32 : ℝ)) ∧
      |(∫ x, x ^ 2 ∂(rawLaw eps ν : Measure ℝ)) - optimalSecondMomentConstant| ≤
        (2 / γ) * K * eps ^ (-(17 / 32 : ℝ)) := by
    filter_upwards [hdist, hraw, eventually_ge_atTop (0 : ℝ)] with eps hd hi heps
    have hd' := (dEtaL_mono (show γ ≤ γ₀ from min_le_left _ _)
      (rawLaw eps ν) cepsTau).trans (hd ν hν)
    have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hd'
    have hri := ceps_integrable_mul_exp (hpos eps) hγc (hi ν hν)
    have ht1 := outTest_one γ hγ.le
    have ht2 := outTest_two_mul hγ
    have h₁ := pw_abs_sub_le_dEtaL (hpos eps) cepsTau_nonneg ht1.1 hγ.le ht1.2 hri hτi hfin
    have h₂ := pw_abs_sub_le_dEtaL (hpos eps) cepsTau_nonneg ht2.1 hγ.le ht2.2 hri hτi hfin
    rw [ceps_integral_testFn_one (hpos eps), ceps_integral_testFn_one cepsTau_nonneg,
      integral_cepsTau, one_mul] at h₁
    rw [ceps_integral_testFn_two (hpos eps), ceps_integral_testFn_two cepsTau_nonneg,
      integral_sq_cepsTau] at h₂
    have hdreal := ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg hK (Real.rpow_nonneg heps _)) hd'
    exact ⟨h₁.trans hdreal, h₂.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdreal
        (show 0 ≤ 2 / γ by positivity))⟩
  have ht : Tendsto (fun eps : ℝ => K * eps ^ (-(17 / 32 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 17 / 32)).const_mul K
  constructor
  · rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq]
    exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hbound.mono fun _ h => h.1) ht
  · rw [tendsto_iff_dist_tendsto_zero]
    simp only [Real.dist_eq]
    exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) (hbound.mono fun _ h => h.2)
      (by simpa only [mul_zero, mul_assoc] using ht.const_mul (2 / γ))

end

end PGM
