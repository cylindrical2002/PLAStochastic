import PLAStochastic.Index.CEPS.Scaled.RootBounds
import PLAStochastic.Index.CEPS.Scaled.MorseMinimum
import Mathlib.Analysis.Complex.Schwarz

/-! # A signed complex-drift unit for the actual Morse center -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def cepsMorseCenterUnit (D θ : ℝ) (ρW : Measure ℝ) (μ : ℂ) : ℂ :=
  dslope (cepsMorseCenter D θ ρW) 0 μ

def CepsCanonDomain.centerUnitSectorRadius {D θ v : ℝ} (dom : CepsCanonDomain D θ v) : ℝ :=
  min (dom.μ₀ / 2) (dom.μ₀ * cepsVarLo D / (32 * (v + 1)))

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsMorseCenterUnit_budget :
    DifferentiableOn ℂ (cepsMorseCenterUnit D θ ρW) (ball 0 dom.μ₀) ∧
      ∀ μ ∈ ball (0 : ℂ) dom.μ₀, ‖cepsMorseCenterUnit D θ ρW μ‖ ≤ 2 / cepsVarLo D := by
  have hd : DifferentiableOn ℂ (cepsMorseCenter D θ ρW) (ball 0 dom.μ₀) :=
    (differentiableOn_cepsMorseCenter hW hθ hD).mono fun μ hμ =>
      mem_ball_zero_iff.mpr (dom.μ_lt_chart (mem_ball_zero_iff.mp hμ).le)
  have h0 := cepsMorseCenter_at_zero hW hθ hD
  have hC : 0 ≤ 2 / cepsVarLo D := by have := cepsVarLo_pos hD; positivity
  have hmap : MapsTo (cepsMorseCenter D θ ρW) (ball 0 dom.μ₀)
      (closedBall (cepsMorseCenter D θ ρW 0) (dom.μ₀ * (2 / cepsVarLo D))) := by
    intro μ hμ
    rw [mem_closedBall, h0, dist_zero_right]
    exact (cepsMorseCenter_norm_le_drift dom hW hθ hD (mem_ball_zero_iff.mp hμ).le).trans
      (by nlinarith [mem_ball_zero_iff.mp hμ])
  refine ⟨(differentiableOn_dslope (ball_mem_nhds 0 dom.μ₀_pos)).mpr hd, fun μ hμ => ?_⟩
  simpa only [cepsMorseCenterUnit, mul_div_cancel_left₀ _ dom.μ₀_pos.ne'] using!
    norm_dslope_le_div_of_mapsTo_ball hd hmap hμ

include hW hθ hD in
theorem cepsMorseCenterUnit_zero : cepsMorseCenterUnit D θ ρW 0 = -(cepsStepVar ρW : ℂ)⁻¹ := by
  rw [cepsMorseCenterUnit, dslope_same, deriv_cepsMorseCenter_zero hW hθ hD]

include hW hθ hD in
theorem centerUnitSectorRadius_pos : 0 < dom.centerUnitSectorRadius := by
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  exact lt_min (half_pos dom.μ₀_pos) (div_pos (mul_pos dom.μ₀_pos hvl) (by positivity))

include hW hθ hD in
theorem cepsMorseCenterUnit_relative {μ : ℂ}
    (hμ : μ ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    ‖cepsMorseCenterUnit D θ ρW μ - cepsMorseCenterUnit D θ ρW 0‖ ≤ 1 / (2 * v) := by
  obtain ⟨hd, hm⟩ := cepsMorseCenterUnit_budget dom hW hθ hD
  have hμhalf : μ ∈ ball (0 : ℂ) (dom.μ₀ / 2) := ball_subset_ball (min_le_left _ _) hμ
  have hnorm : ‖μ‖ ≤ dom.μ₀ * cepsVarLo D / (32 * (v + 1)) :=
    (mem_ball_zero_iff.mp hμ).le.trans (min_le_right _ _)
  have he := norm_sub_le_of_ball_half dom.μ₀_pos hd hm hμhalf (mem_ball_self (half_pos dom.μ₀_pos))
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hvl := cepsVarLo_pos hD
  calc
    _ ≤ 4 * (2 / cepsVarLo D) / dom.μ₀ * ‖μ‖ := by simpa only [sub_zero] using he
    _ ≤ 4 * (2 / cepsVarLo D) / dom.μ₀ * (dom.μ₀ * cepsVarLo D / (32 * (v + 1))) :=
      mul_le_mul_of_nonneg_left hnorm (by have := dom.μ₀_pos; positivity)
    _ = 1 / (4 * (v + 1)) := by have := dom.μ₀_pos.ne'; field_simp; norm_num
    _ ≤ 1 / (2 * v) := by apply one_div_le_one_div_of_le (by positivity); linarith

include hW hθ hD in
theorem cepsMorseCenterUnit_complex_sector {μ : ℂ}
    (hμ : μ ∈ ball (0 : ℂ) dom.centerUnitSectorRadius) :
    (cepsMorseCenterUnit D θ ρW μ).re ≤ -1 / (2 * v) ∧
      ‖cepsMorseCenterUnit D θ ρW μ‖ ≤ 3 / (2 * cepsStepVar ρW) := by
  have herr := cepsMorseCenterUnit_relative dom hW hθ hD hμ
  have hV := cepsStepVar_pos hW hθ hD
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hinv : 1 / v ≤ 1 / cepsStepVar ρW := one_div_le_one_div_of_le hV (cepsStepVar_le hW)
  have hreal : (cepsMorseCenterUnit D θ ρW 0).re = -1 / cepsStepVar ρW := by
    rw [cepsMorseCenterUnit_zero hW hθ hD]
    simp only [← ofReal_inv, neg_re, ofReal_re]
    ring
  have hnorm : ‖cepsMorseCenterUnit D θ ρW 0‖ = 1 / cepsStepVar ρW := by
    rw [cepsMorseCenterUnit_zero hW hθ hD, norm_neg, norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hV]
    exact (one_div _).symm
  have hre := (re_le_norm (cepsMorseCenterUnit D θ ρW μ - cepsMorseCenterUnit D θ ρW 0)).trans herr
  rw [sub_re, hreal] at hre
  have ht := norm_sub_norm_le (cepsMorseCenterUnit D θ ρW μ) (cepsMorseCenterUnit D θ ρW 0)
  rw [hnorm] at ht
  have hhalf : 1 / (2 * v) ≤ 1 / (2 * cepsStepVar ρW) := by
    simpa only [one_div, mul_inv_rev, mul_comm] using mul_le_mul_of_nonneg_left hinv (by norm_num : (0 : ℝ) ≤ 1 / 2)
  constructor
  · have he : 1 / v = 2 * (1 / (2 * v)) := by ring
    have heV : -1 / cepsStepVar ρW = -(1 / cepsStepVar ρW) := by ring
    have hev : -1 / (2 * v) = -(1 / (2 * v)) := by ring
    rw [heV] at hre
    rw [hev]
    linarith
  · have he : 3 / (2 * cepsStepVar ρW) = 1 / cepsStepVar ρW + 1 / (2 * cepsStepVar ρW) := by ring
    linarith

end PGM
