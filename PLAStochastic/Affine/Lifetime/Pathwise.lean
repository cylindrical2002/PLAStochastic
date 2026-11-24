import PLAStochastic.ForMathlib.Probability.FirstExceedance.Time
import PLAStochastic.Affine.Error.TimeProcess
import PLAStochastic.Affine.Error.Attainment

/-!
# Actual approximation lifetimes of continuous paths

The lifetimes are computed from the proved path-error definitions. Closed tails
are equivalent to existence of an actual uniform fit, not to an assumed error
process specification. Infinite lifetimes are retained in the codomain.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

noncomputable section

def anchoredLifetime (f : C(ℝ, ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  firstExceedance (fun t : ℝ≥0 => anchoredTimeError f t) ε

def optimalLifetime (f : C(ℝ, ℝ)) (ε : ℝ) : ℝ≥0∞ :=
  firstExceedance (fun t : ℝ≥0 => optimalTimeError f t) ε

theorem anchoredTimeError_nnreal_monotone (f : C(ℝ, ℝ)) :
    Monotone (fun t : ℝ≥0 => anchoredTimeError f t) := by
  intro s t hst
  exact anchoredTimeError_monotoneOn f s.property t.property hst

theorem optimalTimeError_nnreal_monotone (f : C(ℝ, ℝ)) :
    Monotone (fun t : ℝ≥0 => optimalTimeError f t) := by
  intro s t hst
  exact optimalTimeError_monotoneOn f s.property t.property hst

theorem anchoredLifetime_le_optimalLifetime (f : C(ℝ, ℝ)) (ε : ℝ) :
    anchoredLifetime f ε ≤ optimalLifetime f ε :=
  firstExceedance_antitone_error (fun t => optimalTimeError_le_anchoredTimeError f t)

theorem le_anchoredLifetime_iff (f : C(ℝ, ℝ)) (hf : f 0 = 0) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ anchoredLifetime f ε ↔ anchoredTimeError f t ≤ ε := by
  apply le_firstExceedance_iff (anchoredTimeError_nnreal_monotone f)
    ((continuous_anchoredTimeError f).comp continuous_subtype_val)
  simpa only [NNReal.coe_zero, anchoredTimeError_zero_of_start_zero f hf] using hε

theorem le_optimalLifetime_iff (f : C(ℝ, ℝ)) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ optimalLifetime f ε ↔ optimalTimeError f t ≤ ε := by
  apply le_firstExceedance_iff (optimalTimeError_nnreal_monotone f)
    ((continuous_optimalTimeError f).comp continuous_subtype_val)
  simpa only [NNReal.coe_zero, optimalTimeError_zero f] using hε

/-- The closed lifetime tail is exactly the event of an actual anchored line fit. -/
theorem le_anchoredLifetime_iff_exists_fit (f : C(ℝ, ℝ)) (hf : f 0 = 0) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ anchoredLifetime f ε ↔
      ∃ a : ℝ, ∀ s : Set.Icc (0 : ℝ) (t : ℝ), |f s - a * (s : ℝ)| ≤ ε := by
  rw [le_anchoredLifetime_iff f hf hε t]
  have he : anchoredTimeError f (t : ℝ) = anchoredError (intervalPath f (t : ℝ)) :=
    anchoredTimeError_eq_interval t.property f
  rw [he]
  exact anchoredError_le_iff_exists_fit t.property (intervalPath f t)

theorem le_optimalLifetime_iff_exists_fit (f : C(ℝ, ℝ)) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ optimalLifetime f ε ↔
      ∃ a b : ℝ, ∀ s : Set.Icc (0 : ℝ) (t : ℝ), |f s - a * (s : ℝ) - b| ≤ ε := by
  rw [le_optimalLifetime_iff f hε t]
  have he : optimalTimeError f (t : ℝ) = optimalError (intervalPath f (t : ℝ)) :=
    optimalTimeError_eq_interval t.property f
  rw [he]
  exact optimalError_le_iff_exists_fit t.property (intervalPath f t)

theorem anchoredLifetime_pos (f : C(ℝ, ℝ)) (hf : f 0 = 0) {ε : ℝ} (hε : 0 < ε) :
    0 < anchoredLifetime f ε := by
  apply firstExceedance_pos (anchoredTimeError_nnreal_monotone f)
    ((continuous_anchoredTimeError f).comp continuous_subtype_val)
  simpa only [NNReal.coe_zero, anchoredTimeError_zero_of_start_zero f hf] using hε

theorem optimalLifetime_pos (f : C(ℝ, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    0 < optimalLifetime f ε := by
  apply firstExceedance_pos (optimalTimeError_nnreal_monotone f)
    ((continuous_optimalTimeError f).comp continuous_subtype_val)
  simpa only [NNReal.coe_zero, optimalTimeError_zero f] using hε

theorem anchoredLifetime_dilate (f : C(ℝ, ℝ)) (ε : ℝ) {c : ℝ≥0} (hc : c ≠ 0) :
    anchoredLifetime (dilatePath f c) ε = anchoredLifetime f ε / (c : ℝ≥0∞) := by
  simp only [anchoredLifetime, anchoredTimeError_dilate]
  exact firstExceedance_dilate (fun t : ℝ≥0 => anchoredTimeError f t) ε hc

theorem optimalLifetime_dilate (f : C(ℝ, ℝ)) (ε : ℝ) {c : ℝ≥0} (hc : c ≠ 0) :
    optimalLifetime (dilatePath f c) ε = optimalLifetime f ε / (c : ℝ≥0∞) := by
  simp only [optimalLifetime, optimalTimeError_dilate]
  exact firstExceedance_dilate (fun t : ℝ≥0 => optimalTimeError f t) ε hc

theorem anchoredLifetime_smul_add_drift (f : C(ℝ, ℝ)) (ε a : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    anchoredLifetime (σ • f + affinePath a 0) ε = anchoredLifetime f (ε / σ) := by
  simp only [anchoredLifetime, anchoredTimeError_smul_add_drift, abs_of_pos hσ]
  exact firstExceedance_amplitude (fun t : ℝ≥0 => anchoredTimeError f t) ε hσ

theorem optimalLifetime_smul_add_affine (f : C(ℝ, ℝ)) (ε a b : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    optimalLifetime (σ • f + affinePath a b) ε = optimalLifetime f (ε / σ) := by
  simp only [optimalLifetime, optimalTimeError_smul_add_affine, abs_of_pos hσ]
  exact firstExceedance_amplitude (fun t : ℝ≥0 => optimalTimeError f t) ε hσ

/-- Scalar coordinate measurability suffices for the actual anchored lifetime. -/
theorem aemeasurable_anchoredLifetime {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Ω → C(ℝ, ℝ)} (hF : ∀ t : ℝ≥0, AEMeasurable (fun ω => anchoredTimeError (F ω) t) μ)
    (ε : ℝ) : AEMeasurable (fun ω => anchoredLifetime (F ω) ε) μ :=
  aemeasurable_firstExceedance hF
    (fun ω => (continuous_anchoredTimeError (F ω)).comp continuous_subtype_val) ε

theorem aemeasurable_optimalLifetime {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F : Ω → C(ℝ, ℝ)} (hF : ∀ t : ℝ≥0, AEMeasurable (fun ω => optimalTimeError (F ω) t) μ)
    (ε : ℝ) : AEMeasurable (fun ω => optimalLifetime (F ω) ε) μ :=
  aemeasurable_firstExceedance hF
    (fun ω => (continuous_optimalTimeError (F ω)).comp continuous_subtype_val) ε

end

end BrownianAffine
