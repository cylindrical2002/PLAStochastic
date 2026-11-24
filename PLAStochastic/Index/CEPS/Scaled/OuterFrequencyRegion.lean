import PLAStochastic.Index.CEPS.Scaled.ComplexRootFrequencyBudget
import PLAStochastic.Index.CEPS.Scaled.CentralFrequencyRadius

/-! # Uniform separation outside the central drift-frequency rectangle -/

noncomputable section
open Complex Set Metric MeasureTheory
open PGM.WienerHopf
namespace PGM

def CepsCanonDomain.outerFrequencyThreshold {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  min (dom.centralFrequencyDriftRadius N M) (Real.sqrt (dom.centralFrequencyRadius N M))

def CepsCanonDomain.outerRootFrequencyConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  8 * cepsChartK D * Real.sqrt (4 * v + 4) / dom.outerFrequencyThreshold N M

def CepsCanonDomain.outerRootGapInverseConstant {D θ v : ℝ}
    (dom : CepsCanonDomain D θ v) (N : ℕ) (M : ℝ) : ℝ :=
  4 * Real.sqrt v * Real.sqrt (4 * v + 4) / dom.outerFrequencyThreshold N M

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem outerFrequency_constants (N : ℕ) (M : ℝ) :
    0 < dom.outerFrequencyThreshold N M ∧
      0 < dom.outerRootFrequencyConstant N M ∧ 0 < dom.outerRootGapInverseConstant N M := by
  have hT : 0 < dom.outerFrequencyThreshold N M :=
    lt_min (centralFrequencyDriftRadius_pos dom hW hθ hD N M)
      (Real.sqrt_pos.mpr (centralFrequencyRadius_pos dom hW hθ hD N M))
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hK := cepsChartK_pos hD
  refine ⟨hT, ?_, ?_⟩ <;>
    simp only [CepsCanonDomain.outerRootFrequencyConstant, CepsCanonDomain.outerRootGapInverseConstant] <;>
    positivity

theorem outerFrequency_threshold_le (N : ℕ) (M lam : ℝ) (z : ℂ)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨
      dom.centralFrequencyRadius N M ≤ ‖z‖) :
    dom.outerFrequencyThreshold N M ≤ |lam| + Real.sqrt ‖z‖ := by
  rcases houter with hl | hz
  · exact ((min_le_left _ _).trans hl.le).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _))
  · exact ((min_le_right _ _).trans (Real.sqrt_le_sqrt hz)).trans
      (le_add_of_nonneg_left (abs_nonneg _))

include hW hθ hD in
theorem outerFrequency_ne_origin (N : ℕ) (M lam : ℝ) (z : ℂ)
    (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨
      dom.centralFrequencyRadius N M ≤ ‖z‖) : lam ≠ 0 ∨ z ≠ 0 := by
  by_contra h
  have hl : lam = 0 := by tauto
  have hz : z = 0 := by tauto
  have ht := outerFrequency_threshold_le dom N M lam z houter
  rw [hl, hz, abs_zero, norm_zero, Real.sqrt_zero, zero_add] at ht
  exact (not_le_of_gt (outerFrequency_constants dom hW hθ hD N M).1) ht

include hW hθ hD in
theorem cepsScaledSignedRoot_outer_frequency_budget (N : ℕ) (M lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨
      dom.centralFrequencyRadius N M ≤ ‖z‖) {b sign : ℂ} (hsign : ‖sign‖ ≤ 1)
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    ‖deriv (fun ζ => cepsScaledSignedRoot D θ ρW lam ζ sign b) z‖ ≤
      dom.outerRootFrequencyConstant N M := by
  have hDroot := cepsScaledSignedRoot_complex_frequency_envelope_budget dom hW hθ hD N M lam hz
    (outerFrequency_ne_origin dom hW hθ hD N M lam z houter) hsign hb
  unfold CepsCanonDomain.outerRootFrequencyConstant
  apply (le_div_iff₀ (outerFrequency_constants dom hW hθ hD N M).1).mpr
  exact (mul_le_mul_of_nonneg_left (outerFrequency_threshold_le dom N M lam z houter)
    (norm_nonneg _)).trans hDroot

include hW hθ hD in
theorem cepsScaledRootGap_outer_inverse_budget (N : ℕ) (M lam : ℝ) {z : ℂ}
    (hz : 0 ≤ z.re) (houter : dom.centralFrequencyDriftRadius N M < |lam| ∨
      dom.centralFrequencyRadius N M ≤ ‖z‖) {b : ℂ}
    (hb : b ∈ ball (0 : ℂ) (dom.entranceScaleRadius N M lam z)) :
    cepsScaledSignedRoot D θ ρW lam z 1 b ≠ cepsScaledSignedRoot D θ ρW lam z (-1) b ∧
    ‖(cepsScaledSignedRoot D θ ρW lam z 1 b -
      cepsScaledSignedRoot D θ ρW lam z (-1) b)⁻¹‖ ≤ dom.outerRootGapInverseConstant N M := by
  let gap := cepsScaledSignedRoot D θ ρW lam z 1 b - cepsScaledSignedRoot D θ ρW lam z (-1) b
  let R := ‖cepsScaledRootCoordinate D θ ρW lam z b‖
  let C := 4 * Real.sqrt v * Real.sqrt (4 * v + 4)
  have hv := CepsCanonDomain.v_pos hW hθ hD
  have hC : 0 < C := by dsimp [C]; positivity
  have hT := (outerFrequency_constants dom hW hθ hD N M).1
  have hbC := complexFrequencyCurve_canon_mem dom hW hθ hD N M lam hb
  have hl := cepsScaledRootCoordinate_drift_le dom hW hθ hD lam hz hbC
  have hzB := cepsScaledRootCoordinate_frequency_le dom hW hθ hD lam hz hbC
  have hg := (cepsScaledRootGap_complex_sector dom hW hθ hD lam hz hbC).trans (re_le_norm gap)
  have hR : R ≤ 2 * Real.sqrt v * ‖gap‖ := by
    have hh := (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt v)).mp hg
    simpa only [R, gap, mul_comm] using hh
  have hsep : dom.outerFrequencyThreshold N M ≤ C * ‖gap‖ := by
    apply (outerFrequency_threshold_le dom N M lam z houter).trans
    calc
      _ ≤ 2 * Real.sqrt (4 * v + 4) * R := by dsimp [R]; linarith
      _ ≤ 2 * Real.sqrt (4 * v + 4) * (2 * Real.sqrt v * ‖gap‖) := by gcongr
      _ = C * ‖gap‖ := by dsimp [C]; ring
  have hlo : dom.outerFrequencyThreshold N M / C ≤ ‖gap‖ := (div_le_iff₀ hC).mpr (by nlinarith [hsep])
  have hgap : 0 < ‖gap‖ := (div_pos hT hC).trans_le hlo
  refine ⟨sub_ne_zero.mp (norm_pos_iff.mp hgap), ?_⟩
  change ‖gap⁻¹‖ ≤ C / dom.outerFrequencyThreshold N M
  rw [norm_inv]
  exact ((inv_le_inv₀ hgap (div_pos hT hC)).mpr hlo).trans_eq (by rw [inv_div])

end PGM
