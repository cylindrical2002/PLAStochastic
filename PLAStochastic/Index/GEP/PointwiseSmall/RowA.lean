import PLAStochastic.Index.GEP.PointwiseSmall.LengthContinuation
import PLAStochastic.Index.GEP.PointwiseSmall.RealAxis
import PLAStochastic.Index.GEP.PointwiseSmall.Interpolation

/-!
# WP4 leaf `PointwiseSmall`, row A: the direction derivative of `log v + log C`

Along `ν_z = (1 - z) ν + z σ` (two mean-one laws), `v_z = (1 - z) v + z v_σ` is affine
(`pw_lawVar_mix`).  With the continuation `f_C` of `C_ε` (`pw_cDisc`) set
`Φ(z) = v_z f_C(z) / ε²`.  On the real segment `Φ(t) = E[v_t S_T/ε²]` (Wald), so (U) gives
`|Φ(t) - Φ(0)| ≤ K ε^{-βU}` (`pw_real_moments`); on the disc `‖Φ‖ ≤ K ε^p`.  Interpolation
(`pw_interp_small`) gives `|Φ'(0)| ≤ K ε^{-βU} (1 + log ε)²`, and algebraically
`Φ'(0) = ((v_σ - v) C + v (∫ J_C dσ - ∫ J_C dν)) / ε²`.  Dividing by `v C/ε² ≍ 1`
(no division by the complex continuation):

`|(∫ J_C dσ - ∫ J_C dν)/C + (v_σ - v)/v| ≤ K ε^{-βU} (1 + log ε)²` (`pw_rowA`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-- The variance of the mixture of a regular law and a direction law. -/
theorem pw_lawVar_mix {A θσ : ℝ} (hθ : 0 < θ) (hvlo : 0 < vlo) (hθσ : 0 < θσ)
    {ν σ : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hσ : SigmaLaw A θσ σ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    lawVar (mixPM ν σ t) = (1 - t) * lawVar ν + t * lawVar σ := by
  obtain ⟨hν3, -⟩ := hν.cube hθ hvlo
  obtain ⟨hσ3, -⟩ := hσ.cube hθσ
  obtain ⟨iν1, iν2, -⟩ := moments_of_cube (hν.pos' hθ hvlo) hν3
  obtain ⟨iσ1, iσ2, -⟩ := moments_of_cube hσ.pos hσ3
  have hmean : lawMean (mixPM ν σ t) = 1 := by
    unfold lawMean
    rw [integral_mixPM ht iν1 iσ1]
    change (1 - t) * lawMean ν + t * lawMean σ = 1
    rw [hν.mean, hσ.mean]; ring
  rw [lawVar_eq_of_mean hmean, integral_mixPM ht iν2 iσ2, lawVar_eq_of_mean hν.mean,
    lawVar_eq_of_mean hσ.mean]

/-- The variance of a direction law is at most `kapSig A θσ`. -/
theorem SigmaLaw.lawVar_le {A θσ : ℝ} {σ : ProbabilityMeasure ℝ} (hσ : SigmaLaw A θσ σ)
    (hθσ : 0 < θσ) : lawVar σ ≤ kapSig A θσ := by
  obtain ⟨hσ3, hle⟩ := hσ.cube hθσ
  obtain ⟨-, -, -, -, h2, -⟩ := moments_of_cube hσ.pos hσ3
  rw [lawVar_eq_of_mean hσ.mean]
  exact h2.trans hle

theorem SigmaLaw.lawVar_nonneg {A θσ : ℝ} {σ : ProbabilityMeasure ℝ} (_hσ : SigmaLaw A θσ σ) :
    0 ≤ lawVar σ := integral_nonneg fun _ => sq_nonneg _

/-- The affine continuation of the variance. -/
def pwVz (v vσ : ℝ) (z : ℂ) : ℂ := (1 - z) * (v : ℂ) + z * (vσ : ℂ)

theorem hasDerivAt_pwVz (v vσ : ℝ) (z : ℂ) :
    HasDerivAt (pwVz v vσ) ((vσ : ℂ) - v) z := by
  have h1 := ((hasDerivAt_id z).const_sub 1).mul_const (v : ℂ)
  have h2 := (hasDerivAt_id z).mul_const (vσ : ℂ)
  refine (h1.add h2).congr_deriv ?_
  ring

theorem differentiable_pwVz (v vσ : ℝ) : Differentiable ℂ (pwVz v vσ) := fun z =>
  (hasDerivAt_pwVz v vσ z).differentiableAt

theorem pwVz_zero (v vσ : ℝ) : pwVz v vσ 0 = v := by simp [pwVz]

theorem pwVz_ofReal (v vσ t : ℝ) : pwVz v vσ t = (((1 - t) * v + t * vσ : ℝ) : ℂ) := by
  simp [pwVz]

theorem norm_pwVz_le {v vσ : ℝ} (hv : 0 ≤ v) (hvσ : 0 ≤ vσ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖pwVz v vσ z‖ ≤ 2 * v + vσ := by
  unfold pwVz
  calc ‖(1 - z) * (v : ℂ) + z * (vσ : ℂ)‖ ≤ ‖1 - z‖ * v + ‖z‖ * vσ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hv, abs_of_nonneg hvσ]
    _ ≤ 2 * v + 1 * vσ := by
        have h1 : ‖1 - z‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
        gcongr
    _ = 2 * v + vσ := by ring

/-- **Row A along one direction**: `|(∫ J_C dσ - ∫ J_C dν)/C + (v_σ - v)/v| ≤ K ε^{-βU} log²`. -/
theorem pw_rowA (hS : SurvivalBound) {βU : ℝ} (hβU : 0 ≤ βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (A θσ : ℝ) (hθσ : 0 < θσ) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        |((∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) /
            lawC eps ν + (lawVar σ - lawVar ν) / lawVar ν| ≤
          K * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by
  obtain ⟨rC, KC, eC, pC, hrC, hrCt, heC, hCD⟩ := pw_cDisc hS hD hθ hvlo hv (A := A) hθσ
  obtain ⟨KM, eM, hKM, heM, hRM⟩ := pw_real_moments hUM hD hθ hvlo hv A θσ hθσ
  have hks := kapSig_nonneg A θσ hθσ
  set K₁ := (2 * vhi + kapSig A θσ) * |KC| with hK₁
  obtain ⟨K₃, hK₃, hint⟩ := pw_interp_small discInterp (R := rC) (K₁ := K₁) (K₂ := KM)
    (b := βU) pC hrC hβU
  have hvhi : 0 < vhi + 1 := by linarith
  refine ⟨K₃ * (128 * (vhi + 1) / vlo), max (max eC eM) (epsZero (vhi + 1) (βMix D θ vlo)),
    by positivity, heC.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro eps heps ν σ hν hσ
  have heC' : eC ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) heps
  have heM' : eM ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) heps
  have hez : epsZero (vhi + 1) (βMix D θ vlo) ≤ eps := le_trans (le_max_right _ _) heps
  have heps1 : 1 ≤ eps := heC.trans heC'
  have heps0 : 0 < eps := by linarith
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  have he2 : (1 : ℝ) ≤ eps ^ 2 := one_le_pow₀ heps1
  obtain ⟨f, hf, hfb, hfr, hfd⟩ := hCD eps heC' ν σ hν hσ
  set v := lawVar ν with hvdef
  set vσ := lawVar σ with hvσdef
  have hv0 : vlo ≤ v := hν.var_ge
  have hvpos : 0 < v := hvlo.trans_le hv0
  have hvσ0 : 0 ≤ vσ := hσ.lawVar_nonneg
  have hvσle : vσ ≤ kapSig A θσ := hσ.lawVar_le hθσ
  set C₀ := lawC eps ν with hC₀
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  have hm0 := momClass_mix hθ hvlo hθσ hν hσ h0t
  rw [mixPM_zero] at hm0
  obtain ⟨-, hCm, -⟩ := momClass_oneLayer (by positivity) hez hm0
  have hC0 : 0 < C₀ := lt_of_lt_of_le (by positivity) hCm
  -- the function `Φ`
  set Φ : ℂ → ℂ := fun z => pwVz v vσ z * f z / (eps ^ 2 : ℝ) with hΦ
  have hΦd : DifferentiableOn ℂ Φ (ball 0 rC) :=
    (((differentiable_pwVz v vσ).differentiableOn).mul hf).div_const _
  have hrC1 : rC ≤ 1 := hrCt.trans ((tMix_le A θσ hθσ).trans (by norm_num))
  have hΦb : ∀ z ∈ ball (0 : ℂ) rC, ‖Φ z‖ ≤ K₁ * eps ^ pC := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le.trans hrC1
    have h1 := norm_pwVz_le hvpos.le hvσ0 hz1
    have h2 := hfb z hz
    have hK : KC * eps ^ pC ≤ |KC| * eps ^ pC := by gcongr; exact le_abs_self _
    rw [hΦ]
    simp only
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps2]
    have hb1 : ‖pwVz v vσ z‖ * ‖f z‖ ≤ (2 * vhi + kapSig A θσ) * (|KC| * eps ^ pC) := by
      have : 2 * v + vσ ≤ 2 * vhi + kapSig A θσ := by linarith [hν.var_le]
      exact mul_le_mul (h1.trans this) (h2.trans hK) (norm_nonneg _) (by linarith)
    calc ‖pwVz v vσ z‖ * ‖f z‖ / eps ^ 2 ≤ ‖pwVz v vσ z‖ * ‖f z‖ := div_le_self (by positivity) he2
      _ ≤ K₁ * eps ^ pC := by rw [hK₁]; linarith
  have hΦr : ∀ t : ℝ, 0 ≤ t → t ≤ rC → Φ t = ((pwM1 eps (mixPM ν σ t) : ℝ) : ℂ) := by
    intro t ht0 htr
    have htm : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, htr.trans hrCt⟩
    have ht1 : t ∈ Icc (0 : ℝ) 1 := ⟨ht0, htr.trans hrC1⟩
    rw [pwM1_eq (by positivity) hez (momClass_mix hθ hvlo hθσ hν hσ htm),
      pw_lawVar_mix hθ hvlo hθσ hν hσ ht1, hΦ]
    simp only
    rw [hfr t ht0 htr, pwVz_ofReal]
    push_cast
    ring
  have hΦ0 : Φ 0 = ((pwM1 eps ν : ℝ) : ℂ) := by
    have h := hΦr 0 le_rfl hrC.le
    rw [mixPM_zero] at h
    simpa using h
  have hΦs : ∀ t : ℝ, 0 ≤ t → t ≤ rC / 8 → ‖Φ t - Φ 0‖ ≤ KM * eps ^ (-βU) := by
    intro t ht0 ht1
    have htr : t ≤ rC := by linarith
    rw [hΦr t ht0 htr, hΦ0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact (hRM eps heM' ν σ hν hσ t ⟨ht0, htr.trans hrCt⟩).1
  have hmain := hint Φ eps heps1 hΦd hΦb hΦs
  -- the derivative of `Φ` at `0`
  set Dj := (∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)
    with hDj
  have hf0 : f 0 = (C₀ : ℂ) := by
    have h := hfr 0 le_rfl hrC.le
    rw [mixPM_zero] at h
    simpa using h
  have hfda : HasDerivAt f (deriv f 0) 0 :=
    (hf.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrC))).hasDerivAt
  have hΦD : HasDerivAt Φ ((((vσ - v) * C₀ + v * Dj) / eps ^ 2 : ℝ) : ℂ) 0 := by
    have h := ((hasDerivAt_pwVz v vσ 0).mul hfda).div_const ((eps ^ 2 : ℝ) : ℂ)
    refine h.congr_deriv ?_
    rw [pwVz_zero, hf0, hfd]
    push_cast
    ring
  rw [hΦD.deriv, Complex.norm_real, Real.norm_eq_abs] at hmain
  -- divide by `v C / ε²`
  have hq : 0 < v * C₀ / eps ^ 2 := by positivity
  have hid : Dj / C₀ + (vσ - v) / v = ((vσ - v) * C₀ + v * Dj) / eps ^ 2 / (v * C₀ / eps ^ 2) := by
    field_simp
    ring
  have hinv : 1 / (v * C₀ / eps ^ 2) ≤ 128 * (vhi + 1) / vlo := by
    rw [one_div_div, div_le_div_iff₀ (by positivity) hvlo]
    rw [div_le_iff₀ (by positivity)] at hCm
    have : eps ^ 2 ≤ 128 * (vhi + 1) * C₀ := by linarith
    nlinarith
  rw [hid, abs_div, abs_of_pos hq, div_eq_mul_one_div]
  have hL0 : 0 ≤ K₃ * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
  calc |((vσ - v) * C₀ + v * Dj) / eps ^ 2| * (1 / (v * C₀ / eps ^ 2))
      ≤ K₃ * eps ^ (-βU) * (1 + Real.log eps) ^ 2 * (128 * (vhi + 1) / vlo) :=
        mul_le_mul hmain hinv (by positivity) hL0
    _ = K₃ * (128 * (vhi + 1) / vlo) * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by ring

end

end PGM
