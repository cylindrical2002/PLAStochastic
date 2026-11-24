import PLAStochastic.Index.CEPS.Scaled.TrueSlopeError
import PLAStochastic.Index.CEPS.Scaled.WeightedErrorCancellation
import PLAStochastic.Index.CEPS.Scaled.SurrogateSlopeInverse

/-! # Frequency-uniform relative error of the actual divided denominator

Spatial derivative errors control the central frequency region. Away from
it, an exact relative divided-difference identity cancels the root gap and
uses the already proved nonzero surrogate delta. The resulting constant
does not grow with scaled drift or frequency.
-/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.highFrequencyDeltaInverseConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) : ℝ :=
  (4 / dom.scaledComplexSector) * (1 + Real.sqrt (8 * v + 8))

def CepsCanonDomain.trueDenominatorRelativeConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  4 * dom.trueSpatialErrorConstant N M 1 * dom.surrogateSlopePolynomialConstant N M +
    2 * dom.trueSpatialErrorConstant N M 0 *
      ((4 / cepsVarLo D) * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))) *
        dom.highFrequencyDeltaInverseConstant

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem highFrequencyDeltaInverseConstant_pos : 0 < dom.highFrequencyDeltaInverseConstant := by
  have := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).2.1
  unfold CepsCanonDomain.highFrequencyDeltaInverseConstant
  positivity

include hW hθ hD in
theorem surrogateDeltaInverseBound_le_high_frequency (lam : ℝ) {z : ℂ}
    (hfreq : 1 ≤ |lam| + Real.sqrt ‖z‖) :
    dom.surrogateDeltaInverseBound lam z ≤ dom.highFrequencyDeltaInverseConstant := by
  let s := Real.sqrt (8 * v + 8)
  let T := dom.scaledCoordinateLower lam z
  have hs : 0 < s := Real.sqrt_pos.mpr (by linarith [CepsCanonDomain.v_pos hW hθ hD])
  have ht : 1 / s ≤ T :=
    (div_le_div_of_nonneg_right hfreq hs.le).trans
      (scaledCoordinateLower_drift_frequency_le dom hW hθ hD lam z)
  have hT : 0 < T := (div_pos (by norm_num) hs).trans_le ht
  have hi : (min 1 T)⁻¹ ≤ 1 + s := by
    by_cases h : T ≤ 1
    · rw [min_eq_right h]
      apply (inv_le_iff_one_le_mul₀ hT).mpr
      have hmul := (div_le_iff₀ hs).mp ht
      nlinarith [mul_nonneg hs.le hT.le]
    · rw [min_eq_left (le_of_not_ge h), inv_one]
      linarith
  have hc := (cepsScaledSurrogate_constants dom hW hθ hD 0 0).2.1
  unfold CepsCanonDomain.surrogateDeltaInverseBound CepsCanonDomain.highFrequencyDeltaInverseConstant
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg (by norm_num) hc.le)

include hW hθ hD in
theorem trueDenominatorRelativeConstant_nonneg {M : ℝ} (hM : 0 ≤ M) (N : ℕ) :
    0 ≤ dom.trueDenominatorRelativeConstant N M := by
  have := trueSpatialErrorConstant_nonneg dom hW hθ hD hM N 0
  have := trueSpatialErrorConstant_nonneg dom hW hθ hD hM N 1
  have := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have := highFrequencyDeltaInverseConstant_pos dom hW hθ hD
  have := cepsVarLo_pos hD
  unfold CepsCanonDomain.trueDenominatorRelativeConstant
  positivity

include hW hθ hD in
theorem cepsScaledTrueDenominator_relative_error_budget {m : ℕ} {η M : ℝ}
    (hf : CepsSobolevClass m η fW) (hη : 2 * dom.c₀ ≤ η)
    (hM : cepsSobolev m η fW ≤ M) (N : ℕ) (hN : N + 2 ≤ m)
    (lam : ℝ) {z : ℂ} (hz : 0 ≤ z.re) {b : ℝ}
    (hb : (b : ℂ) ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖(cepsScaledTrueDenominator dom ρW lam z b - cepsScaledSurrogateDenominator dom ρW N lam z b) /
      cepsScaledSurrogateDenominator dom ρW N lam z b‖ ≤
        dom.trueDenominatorRelativeConstant N M * |b * lam| ^ (N + 1) := by
  let a := cepsScaledSignedRoot D θ ρW lam z (-1) (b : ℂ)
  let p := cepsScaledSignedRoot D θ ρW lam z 1 (b : ℂ)
  let w : ℂ := 1 + (b : ℂ) * lam
  let A := cepsScaledTrueG dom ρW lam z b
  let G := cepsScaledSurrogateG dom ρW N lam z (b : ℂ)
  let S := cepsScaledSurrogateDenominator dom ρW N lam z (b : ℂ)
  let Δ := cepsScaledSurrogateDelta dom ρW N lam z (b : ℂ)
  let e := |b * lam| ^ (N + 1)
  let K := dom.surrogateSlopePolynomialConstant N M
  let I := (4 / cepsVarLo D) * Real.exp (2 * dom.canonDriftTaylorBound N M (dom.μ₀ / 8))
  have hM0 := (cepsSobolev_nonneg m η fW).trans hM
  have hC0 := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 0
  have hC1 := trueSpatialErrorConstant_nonneg dom hW hθ hD hM0 N 1
  have hK : 0 < K := surrogateSlopePolynomialConstant_pos dom hW hθ hD N M
  have hI : 0 ≤ I := by dsimp [I]; have := cepsVarLo_pos hD; positivity
  have hH := (highFrequencyDeltaInverseConstant_pos dom hW hθ hD).le
  have he : 0 ≤ e := pow_nonneg (abs_nonneg _) _
  have hbR := ball_subset_ball (min_le_left _ _) hb
  have hbS := ball_subset_ball (min_le_left _ _) hbR
  have hbC : (b : ℂ) ∈ ball (0 : ℂ) (dom.canonScaleRadius lam z) :=
    ball_subset_ball ((min_le_left _ _).trans
      (half_le_self (canonScaleRadius_pos dom hW hθ hD lam z).le)) hbS
  have horder : 0 ≤ ((p - a) * w).re :=
    (mul_nonneg (cepsScaledSurrogate_constants dom hW hθ hD N M).2.1.le (norm_nonneg _)).trans
      (cepsScaledEffectiveGap_sector dom hW hθ hD N M lam hz hbS)
  have hS0 : S ≠ 0 := cepsScaledSurrogateDenominator_ne_zero dom hW hθ hD hf hη hM N
    (by omega) lam hz hbR
  have hhigh : 0 ≤ 2 * dom.trueSpatialErrorConstant N M 0 * I * dom.highFrequencyDeltaInverseConstant := by positivity
  have hlow : 0 ≤ 4 * dom.trueSpatialErrorConstant N M 1 * K := by positivity
  by_cases hfreq : 1 ≤ |lam| + Real.sqrt ‖z‖
  · have hne : 0 < lam ^ 2 + ‖z‖ := by
      by_contra h
      have hl : lam = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
      have hz0 : ‖z‖ = 0 := by nlinarith [sq_nonneg lam, norm_nonneg z]
      rw [hl, hz0] at hfreq
      norm_num at hfreq
    have hgap : p - a ≠ 0 := cepsScaledRootGap_ne_zero dom hW hθ hD N M lam hz hne hbS
    have hG0 : G a ≠ 0 := cepsScaledSurrogateG_root_ne_zero dom hW hθ hD hf hη hM N
      (by omega) lam hz (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) hbC
    have hid : Δ * G a = -(p - a) * S :=
      cepsScaledSurrogateDelta_mul_rootG dom hW hθ hD hf hη hM N (by omega) lam hz hbC
    have hΔ0 : Δ ≠ 0 := by
      intro h
      rw [h, zero_mul] at hid
      exact mul_ne_zero (neg_ne_zero.mpr hgap) hS0 hid.symm
    have hval : ∀ ξ : ℂ, ‖ξ‖ ≤ dom.entranceSpatialScaleRadius lam z / 2 →
        ‖A ξ - G ξ‖ ≤ dom.trueSpatialErrorConstant N M 0 * e * Real.exp (-(ξ * w).re) := by
      intro ξ hξ
      have h := cepsScaledTrueG_spatial_error_budget dom hW hθ hD hf hη hM N hN lam hz hb 0 hξ
      simpa only [iteratedDeriv_zero, CepsCanonDomain.trueSpatialErrorConstant, mul_assoc,
        mul_comm (Real.exp _) (|b * lam| ^ (N + 1))] using! h
    have hErr : ‖(A a - G a) - (A p - G p)‖ ≤ dom.trueSpatialErrorConstant N M 0 * e *
        (Real.exp (-(a * w).re) + Real.exp (-(p * w).re)) := by
      apply (norm_sub_le _ _).trans
      have hh := add_le_add
        (hval a (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num)))
        (hval p (entranceScaleCurve_root_norm_le_half dom hW hθ hD N M lam hz hb (by norm_num)))
      exact hh.trans_eq (by ring)
    obtain ⟨hμ, hq, hζ⟩ := canonScaleCurve_bounds dom hW hθ hD lam hz (sign := -1) (by norm_num) hbC
    have hF := cepsCanonSurrogateWeight_inverse_bound dom hW hθ hD hf hη hM N
      (by omega) hμ.le hq.le hζ.le
    have hGI : ‖(G a)⁻¹‖ ≤ I * Real.exp ((a * w).re) := by
      dsimp only [G, cepsScaledSurrogateG]
      rw [mul_inv, norm_mul, norm_inv, norm_exp, neg_mul, neg_re, Real.exp_neg, inv_inv]
      exact (mul_le_mul_of_nonneg_left hF (Real.exp_pos _).le).trans_eq (by ring)
    have hEI := cepsNorm_weighted_error_mul_le (mul_nonneg hC0 he) hI horder hErr hGI
    have hDI : ‖Δ⁻¹‖ ≤ dom.highFrequencyDeltaInverseConstant :=
      ((cepsScaledSurrogateDelta_inverse_budget dom hW hθ hD hf hη hM N (by omega)
        lam hz hne).2 b hbS).trans (surrogateDeltaInverseBound_le_high_frequency dom hW hθ hD lam hfreq)
    change ‖(dslope A a p - dslope G a p) / dslope G a p‖ ≤ _
    rw [cepsNormal_dslope_relative_error_identity hG0 hΔ0 hS0 hid, norm_mul]
    calc
      _ ≤ (2 * (dom.trueSpatialErrorConstant N M 0 * e) * I) * dom.highFrequencyDeltaInverseConstant :=
        mul_le_mul hEI hDI (norm_nonneg _) (by positivity)
      _ = (2 * dom.trueSpatialErrorConstant N M 0 * I * dom.highFrequencyDeltaInverseConstant) * e := by ring
      _ ≤ dom.trueDenominatorRelativeConstant N M * e := by
        unfold CepsCanonDomain.trueDenominatorRelativeConstant
        exact mul_le_mul_of_nonneg_right (by change _ ≤ 4 * dom.trueSpatialErrorConstant N M 1 * K + _; linarith) he
  · have hX : 1 + |lam| + Real.sqrt ‖z‖ ≤ 2 := by linarith
    have hErr := cepsScaledTrueDenominator_error_budget dom hW hθ hD hf hη hM N hN lam hz hb
    have hSI := cepsScaledSurrogateDenominator_inverse_weighted_bound dom hW hθ hD hf hη hM N
      (by omega) lam hz hbR
    rw [div_eq_mul_inv]
    have h := cepsNorm_weighted_error_mul_le (mul_nonneg hC1 he)
      (mul_nonneg hK.le (by positivity : 0 ≤ 1 + |lam| + Real.sqrt ‖z‖)) horder hErr hSI
    apply h.trans
    calc
      _ = (2 * dom.trueSpatialErrorConstant N M 1 * K * e) * (1 + |lam| + Real.sqrt ‖z‖) := by ring
      _ ≤ (2 * dom.trueSpatialErrorConstant N M 1 * K * e) * 2 :=
        mul_le_mul_of_nonneg_left hX (by positivity)
      _ = (4 * dom.trueSpatialErrorConstant N M 1 * K) * e := by ring
      _ ≤ dom.trueDenominatorRelativeConstant N M * e := by
        unfold CepsCanonDomain.trueDenominatorRelativeConstant
        exact mul_le_mul_of_nonneg_right (by change _ ≤ _ + 2 * dom.trueSpatialErrorConstant N M 0 * I * dom.highFrequencyDeltaInverseConstant; linarith) he

end PGM
