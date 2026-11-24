import PLAStochastic.Index.CEPS.Leading.Moments
import PLAStochastic.Index.CEPS.FiniteLayer
import PLAStochastic.Index.CEPS.Reference.Density

/-!
# The unconditional leading limit of the actual depth-zero proxy

Wald's identity identifies the first raw moment. The second raw moment gives
the normalized output variance, so the leading value is exactly κ / α.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory BrownianAffine Filter Topology Set
open scoped ENNReal

theorem ceps_integral_rawLaw (eps : ℝ) (ν : ProbabilityMeasure ℝ) :
    (∫ x, x ∂(rawLaw eps ν : Measure ℝ)) = pwM1 eps ν := by
  change (∫ x, x ∂((iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2))) = _
  have hm : Measurable (fun g : ℕ → ℝ => lawVar ν * stopSum eps g / eps ^ 2) :=
    (measurable_const.mul (measurable_stopSum eps)).div_const _
  rw [integral_map (f := fun x : ℝ => x) hm.aemeasurable (by fun_prop)]
  rfl

theorem MomClass.lawVar_eq_second_sub_one {b β vmin : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : MomClass b β vmin ν) : lawVar ν = (∫ x, x ^ 2 ∂(ν : Measure ℝ)) - 1 := by
  have hs : Integrable (fun x : ℝ => x ^ 2) (ν : Measure ℝ) :=
    (hν.memLp3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)).integrable_sq
  have hi : Integrable (fun x : ℝ => x) (ν : Measure ℝ) :=
    hν.memLp3.integrable (by norm_num)
  rw [lawVar, hν.mean]
  have he : (fun x : ℝ => (x - 1) ^ 2) = fun x => (x ^ 2 - 2 * x) + 1 := by
    funext x; ring
  rw [he, integral_add (f := fun x : ℝ => x ^ 2 - 2 * x) (g := fun _ => (1 : ℝ))
      (hs.sub (hi.const_mul 2)) (integrable_const _),
    integral_sub (f := fun x : ℝ => x ^ 2) (g := fun x => 2 * x) hs (hi.const_mul 2), integral_const_mul,
    show (∫ x, x ∂(ν : Measure ℝ)) = 1 from hν.mean,
    integral_const, probReal_univ, smul_eq_mul]
  ring

/-- The normalized variance is a quotient of the actual raw second moment. -/
theorem ceps_lawPhi_var_eq_raw_moments {D θ vlo vhi eps : ℝ}
    (hθ : 0 < θ) (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (heps : epsZero (regB vhi) (regBeta D θ vlo) ≤ eps) :
    lawVar (lawPhi eps ν) =
      (∫ x, x ^ 2 ∂(rawLaw eps ν : Measure ℝ)) /
        (lawVar ν * lawC eps ν / eps ^ 2) ^ 2 - 1 := by
  have hm := hν.momClass hθ hvlo
  have hvm := regV_pos hvlo
  obtain ⟨_, heps1, _, _, _, _, hCm, _⟩ := momClass_setup hvm heps hm
  have hep : 0 < eps := by linarith
  have hv : 0 < lawVar ν := hvm.trans_le hm.var_ge
  have hC : 0 < lawC eps ν := (by positivity : 0 < eps ^ 2 / lawVar ν / 128).trans_le hCm
  have hnext := lawPhi_momClass (bAbs_le_regB vhi) (βAbs_le_regBeta D θ vlo)
    hvm (regV_le_half vlo) heps hm
  rw [hnext.lawVar_eq_second_sub_one]
  congr 1
  have hW : Measurable (fun g : ℕ → ℝ => lawVar ν * stopSum eps g / eps ^ 2) :=
    (measurable_const.mul (measurable_stopSum eps)).div_const _
  have hY : Measurable (fun g : ℕ → ℝ => stopSum eps g / lawC eps ν) :=
    (measurable_stopSum eps).div_const _
  have he : (∫ x, x ^ 2 ∂(rawLaw eps ν : Measure ℝ)) =
      (lawVar ν * lawC eps ν / eps ^ 2) ^ 2 *
        (∫ x, x ^ 2 ∂(lawPhi eps ν : Measure ℝ)) := by
    change (∫ x, x ^ 2 ∂((iidLaw ν).map (fun g => lawVar ν * stopSum eps g / eps ^ 2))) =
      _ * (∫ x, x ^ 2 ∂((iidLaw ν).map (fun g => stopSum eps g / lawC eps ν)))
    rw [integral_map hW.aemeasurable (by fun_prop), integral_map hY.aemeasurable (by fun_prop),
      ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun g => by
      field_simp [hC.ne', hep.ne']
  rw [he]
  field_simp [(mul_pos hv hC).ne', hep.ne']

theorem ceps_scaled_lawC_tendsto {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    Tendsto (fun eps => lawVar ν * lawC eps ν / eps ^ 2) atTop (𝓝 optimalMeanConstant) := by
  apply (ceps_raw_moments_tendsto hD hθ hvlo hv hν).1.congr'
  filter_upwards [eventually_ge_atTop (epsZero (regB vhi) (regBeta D θ vlo))] with eps heps
  rw [ceps_integral_rawLaw, pwM1_eq (regV_pos hvlo) heps (hν.momClass hθ hvlo)]

theorem ceps_lawPhi_var_tendsto {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    Tendsto (fun eps => lawVar (lawPhi eps ν)) atTop (𝓝 optimalDispersionConstant) := by
  have hm₁ := ceps_scaled_lawC_tendsto hD hθ hvlo hv hν
  have hm₂ := (ceps_raw_moments_tendsto hD hθ hvlo hv hν).2
  have hl := (hm₂.div (hm₁.pow 2) (sq_pos_of_pos optimalMeanConstant_pos).ne').sub_const 1
  have he : optimalSecondMomentConstant / optimalMeanConstant ^ 2 - 1 = optimalDispersionConstant := by
    unfold optimalDispersionConstant optimalVarianceConstant
    field_simp [optimalMeanConstant_pos.ne']
  rw [he] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop (epsZero (regB vhi) (regBeta D θ vlo))] with eps heps
  exact (ceps_lawPhi_var_eq_raw_moments hθ hvlo hν heps).symm

/-- The depth-zero proxy has its exact Brownian leading value without expansion inputs. -/
theorem ceps_scaled_proxy_zero_tendsto {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) :
    Tendsto (fun eps => cepsProxy eps ν 0 / eps ^ 2) atTop
      (𝓝 (optimalMeanConstant / optimalDispersionConstant)) := by
  have h := (ceps_scaled_lawC_tendsto hD hθ hvlo hv hν).div
    (ceps_lawPhi_var_tendsto hD hθ hvlo hv hν) optimalDispersionConstant_pos.ne'
  convert h using 1
  funext eps
  simp only [cepsProxy, Function.iterate_zero_apply, Nat.zero_add, Function.iterate_one, Pi.div_apply]
  ring

/-- The particular starting law used by the all-orders construction needs no hypotheses. -/
theorem ceps_scaled_proxy_cepsLambda_zero_tendsto :
    Tendsto (fun eps => cepsProxy eps cepsLambda 0 / eps ^ 2) atTop
      (𝓝 (optimalMeanConstant / optimalDispersionConstant)) := by
  obtain ⟨D, θ, hD, hθ, hν⟩ := exists_regLaw_cepsLambda
  exact ceps_scaled_proxy_zero_tendsto hD hθ optimalDispersionConstant_pos le_rfl hν

end

end PGM
