import PLAStochastic.Index.CEPS.Leading.Proxy
import PLAStochastic.ForMathlib.Analysis.Asymptotics.InverseExpansion

/-!
# The leading value of the unchanged exact compression constant

The qualitative response coefficient tends to zero. The regular class has
bounded diameter and variance, so the posterior error at depth zero tends to
zero without a fixed-depth expansion hypothesis or a quantitative rate.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Topology Set

/-- Bounded regular residuals suffice for a vanishing depth-zero logarithmic error. -/
theorem ceps_log_proxy_zero_error_tendsto {D θ vlo vhi eOrbit : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ)
    (hν : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] ν))
    (hexp : ∀ eps, eOrbit ≤ eps → ∀ j, RegLaw D θ vlo vhi ((lawPhi eps)^[j] expPM)) :
    Tendsto (fun eps => gepLogC eps - cepsProxyLog eps ν 0) atTop (𝓝 0) := by
  obtain ⟨η, K, eJ, a, hη, hηθ, hK, ha0, haT, hJs⟩ :=
    jointResponse D θ vlo vhi hD hθ hvlo hv
  have hηθ' : η < θ := by linarith
  let B := D / (θ * (θ - η)) + K * (2 * vhi)
  let H := 2 * (1 + vlo⁻¹) * B
  have hs : ∀ᶠ eps in atTop, (2 * K + 2) * a eps ≤ 1 / 2 := by
    have ht := haT.const_mul (2 * K + 2)
    simp only [mul_zero] at ht
    exact ht.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2)
  have he : ∀ᶠ eps : ℝ in atTop,
      |gepLogC eps - cepsProxyLog eps ν 0| ≤ H * a eps := by
    filter_upwards [hs, eventually_ge_atTop eOrbit, eventually_ge_atTop eJ]
      with eps hsmall heOrbit heJ
    have hr := ha0 eps
    have hpost := abs_gepLogC_sub_cepsProxyLog_le hvlo hη.le hηθ' hK (ha0 eps) hsmall
      (hJs eps heJ) ν (hν eps heOrbit) (hexp eps heOrbit) 0
    have hden : 1 / 2 ≤ 1 - (K + 1) * a eps := by nlinarith
    have hc : (1 + vlo⁻¹) * a eps / (1 - (K + 1) * a eps) ≤
        2 * (1 + vlo⁻¹) * a eps := by
      calc
        _ ≤ ((1 + vlo⁻¹) * a eps) / (1 / 2) :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hden
        _ = _ := by ring
    have h0 := hν eps heOrbit 0
    have h1 := hν eps heOrbit 1
    have hd := dEta_le_diam h0 h1 hη.le hηθ'
    have hvar : |lawVar ((lawPhi eps)^[1] ν) - lawVar ((lawPhi eps)^[0] ν)| ≤ 2 * vhi := by
      calc
        _ ≤ |lawVar ((lawPhi eps)^[1] ν)| + |lawVar ((lawPhi eps)^[0] ν)| := abs_sub _ _
        _ = lawVar ((lawPhi eps)^[1] ν) + lawVar ((lawPhi eps)^[0] ν) := by
          rw [abs_of_pos (hvlo.trans_le h1.var_ge), abs_of_pos (hvlo.trans_le h0.var_ge)]
        _ ≤ _ := by linarith [h0.var_le, h1.var_le]
    calc
      _ ≤ _ := hpost
      _ ≤ (2 * (1 + vlo⁻¹) * a eps) *
          (dEta η ((lawPhi eps)^[0] ν) ((lawPhi eps)^[1] ν) +
            K * |lawVar ((lawPhi eps)^[1] ν) - lawVar ((lawPhi eps)^[0] ν)|) := by
        apply mul_le_mul_of_nonneg_right hc
        exact add_nonneg (dEta_nonneg _ _ _) (mul_nonneg hK (abs_nonneg _))
      _ ≤ (2 * (1 + vlo⁻¹) * a eps) * B := by
        apply mul_le_mul_of_nonneg_left
        · dsimp only [B]
          exact add_le_add hd (mul_le_mul_of_nonneg_left hvar hK)
        · positivity
      _ = H * a eps := by dsimp [H]; ring
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq, sub_zero]
  exact squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) he
    (by simpa only [mul_zero] using haT.const_mul H)

/-- The actual compression constant has its Brownian leading limit. -/
theorem gepC_scaled_tendsto_of_regLaw {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν) :
    Tendsto (fun eps => gepC eps / eps ^ 2) atTop
      (𝓝 (optimalMeanConstant / optimalDispersionConstant)) := by
  obtain ⟨Ds, θs, vlos, vhis, e0, hDs, hθs, hvlos, hvs, hνs, hexp⟩ :=
    exists_common_regular_orbits hD hθ hvlo hv ν hν
  have hl := ceps_log_proxy_zero_error_tendsto hDs hθs hvlos hvs ν hνs hexp
  have hp := ceps_scaled_proxy_zero_tendsto hD hθ hvlo hv hν
  have ht := hp.mul hl.rexp
  simp only [Real.exp_zero, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop e0,
    eventually_ge_atTop (epsZero (regB vhis) (regBeta Ds θs vlos))] with eps he0 hez
  have h0 := hνs eps he0 0
  have h1 := hνs eps he0 1
  have hv0 := hvlos.trans_le h0.var_ge
  have hv1 := hvlos.trans_le h1.var_ge
  have hC := h0.lawC_pos hθs hvlos hez
  have he := exp_cepsProxyLog hv0 hv1 hC
  have hproxy : cepsProxy eps ν 0 ≠ 0 := by
    rw [← he]
    exact (Real.exp_pos _).ne'
  change (cepsProxy eps ν 0 / eps ^ 2) *
    Real.exp (gepLogC eps - cepsProxyLog eps ν 0) = gepC eps / eps ^ 2
  rw [Real.exp_sub, he, gepC]
  field_simp [hproxy]

/-- The unchanged exact constant has leading value κ / α, without analytic hypotheses. -/
theorem gepC_scaled_tendsto :
    Tendsto (fun eps => gepC eps / eps ^ 2) atTop
      (𝓝 (optimalMeanConstant / optimalDispersionConstant)) := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  exact gepC_scaled_tendsto_of_regLaw hD hθ optimalDispersionConstant_pos le_rfl cepsLambda hν

/-- Any all-orders coefficient sequence for the actual constant has the prescribed first term. -/
theorem gepC_coeff_zero {a : ℕ → ℝ}
    (ha : HasInverseExpansion (fun eps => gepC eps / eps ^ 2) a) :
    a 0 = optimalMeanConstant / optimalDispersionConstant :=
  tendsto_nhds_unique (ha 0).tendsto_zero_order gepC_scaled_tendsto

end

end PGM
