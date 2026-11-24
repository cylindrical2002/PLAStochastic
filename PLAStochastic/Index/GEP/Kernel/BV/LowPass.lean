import PLAStochastic.Index.GEP.Kernel.BV.FourierInverse

/-!
# The actual low-frequency representative of a square-integrable state

The cutoff is `1_[-1,1]`. Compact frequency support already gives the differentiable
inverse-transform representative needed by the BV argument. Smoothness of the
cutoff itself is not used. The error estimate is obtained in the unitary `L²`
transform, so no unproved integrability of the smoothed spatial tail is assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory FourierTransform Set Complex

/-- The hard low-frequency truncation of the actual integral Fourier transform. -/
def kBVLowFreq (u : ℝ → ℂ) : ℝ → ℂ := (Icc (-1 : ℝ) 1).indicator (𝓕 u)

/-- Its canonical continuous spatial representative. -/
def kBVLowPass (u : ℝ → ℂ) : ℝ → ℂ := 𝓕⁻ (kBVLowFreq u)

/-- Frequency multiplication used by the spatial derivative. -/
def kBVLowFreqSlope (u : ℝ → ℂ) (ξ : ℝ) : ℂ := (ξ : ℂ) * kBVLowFreq u ξ

/-- The canonical spatial derivative of the low-frequency representative. -/
def kBVLowPassDeriv (u : ℝ → ℂ) : ℝ → ℂ :=
  𝓕⁻ (fun ξ => (2 * Real.pi * I) * kBVLowFreqSlope u ξ)

theorem kBVLowFreq_measurable {u : ℝ → ℂ} (h1 : Integrable u) :
    Measurable (kBVLowFreq u) := (kill_continuous_fourier h1).measurable.indicator measurableSet_Icc

theorem kBVLowFreq_memLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (kBVLowFreq u) 2 := (kill_memLp_two_fourier h1 h2).indicator measurableSet_Icc

theorem kBVLowFreq_integrable {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    Integrable (kBVLowFreq u) :=
  kill_integrable_of_support (by simp : volume (Icc (-1 : ℝ) 1) ≠ ⊤)
    (fun _ h => indicator_of_notMem h _) (kBVLowFreq_memLp h1 h2)

theorem kBVLowFreqSlope_norm_le (u : ℝ → ℂ) (ξ : ℝ) :
    ‖kBVLowFreqSlope u ξ‖ ≤ ‖𝓕 u ξ‖ := by
  by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1
  · have hξ1 : |ξ| ≤ 1 := abs_le.mpr hξ
    simp only [kBVLowFreqSlope, kBVLowFreq, indicator_of_mem hξ, norm_mul, Complex.norm_real]
    simpa only [Real.norm_eq_abs, one_mul] using
      mul_le_mul_of_nonneg_right hξ1 (norm_nonneg (𝓕 u ξ))
  · simp [kBVLowFreqSlope, kBVLowFreq, indicator_of_notMem hξ]

theorem kBVLowFreqSlope_memLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (kBVLowFreqSlope u) 2 := by
  apply (kill_memLp_two_fourier h1 h2).of_le_mul (c := 1) _
    (Filter.Eventually.of_forall fun ξ => by simpa using kBVLowFreqSlope_norm_le u ξ)
  exact ((Complex.measurable_ofReal.comp measurable_id).mul (kBVLowFreq_measurable h1)).aestronglyMeasurable

theorem kBVLowFreqSlope_integrable {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    Integrable (kBVLowFreqSlope u) := by
  apply kill_integrable_of_support (by simp : volume (Icc (-1 : ℝ) 1) ≠ ⊤) _
    (kBVLowFreqSlope_memLp h1 h2)
  intro ξ hξ
  simp [kBVLowFreqSlope, kBVLowFreq, indicator_of_notMem hξ]

theorem kBVLowPass_memLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (kBVLowPass u) 2 :=
  kBV_memLp_two_fourierInv (kBVLowFreq_integrable h1 h2) (kBVLowFreq_memLp h1 h2)

theorem kBVLowPass_continuous {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    Continuous (kBVLowPass u) := kBV_continuous_fourierInv (kBVLowFreq_integrable h1 h2)

/-- The hard cutoff error has squared `L²` norm bounded by the dissipation energy. -/
theorem kBVLowPass_error_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVNormSq (fun x => u x - kBVLowPass u x) ≤ kBVEnergy u := by
  have hF2 := kill_memLp_two_fourier h1 h2
  have hl2 := kBVLowFreq_memLp h1 h2
  have hl1 := kBVLowFreq_integrable h1 h2
  have hv2 := kBVLowPass_memLp h1 h2
  have hhigh2 := hF2.sub hl2
  have herr2 := h2.sub hv2
  have hFLp : 𝓕 (h2.toLp u) = hF2.toLp (𝓕 u) := by
    apply Lp.ext
    exact (kill_fourier_toLp_two_ae_eq h1 h2).trans hF2.coeFn_toLp.symm
  have hvLp : hv2.toLp (kBVLowPass u) = 𝓕⁻ (hl2.toLp (kBVLowFreq u)) := by
    apply Lp.ext
    exact hv2.coeFn_toLp.trans (kBV_fourierInv_toLp_two_ae_eq hl1 hl2).symm
  have heq : kBVNormSq (fun x => u x - kBVLowPass u x) =
      kBVNormSq (fun ξ => 𝓕 u ξ - kBVLowFreq u ξ) := by
    change kBVNormSq (u - kBVLowPass u) = kBVNormSq (𝓕 u - kBVLowFreq u)
    rw [← kBV_toLp_norm_sq herr2, ← kBV_toLp_norm_sq hhigh2,
      MemLp.toLp_sub h2 hv2, MemLp.toLp_sub hF2 hl2, hvLp]
    rw [← Lp.norm_fourier_eq (h2.toLp u - 𝓕⁻ (hl2.toLp (kBVLowFreq u)))]
    have hmap : 𝓕 (h2.toLp u - 𝓕⁻ (hl2.toLp (kBVLowFreq u))) =
        𝓕 (h2.toLp u) - 𝓕 (𝓕⁻ (hl2.toLp (kBVLowFreq u))) :=
      (Lp.fourierTransformₗᵢ ℝ ℂ).map_sub _ _
    rw [hmap, fourier_fourierInv_eq, hFLp]
  rw [heq]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    (kBV_integrable_energy h1 h2)
  apply Filter.Eventually.of_forall
  intro ξ
  by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1
  · simp only [kBVLowFreq, indicator_of_mem hξ, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    positivity
  · have hξ1 : 1 ≤ ξ ^ 2 := by
      have hn : ¬ |ξ| ≤ 1 := by simpa [abs_le] using hξ
      have ht := lt_of_not_ge hn
      nlinarith [sq_abs ξ]
    simp only [kBVLowFreq, indicator_of_notMem hξ, sub_zero, min_eq_right hξ1, one_mul, le_refl]

/-- The Fourier multiplier for the derivative has the exact energy scale. -/
theorem kBVLowFreqSlope_normSq_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVNormSq (kBVLowFreqSlope u) ≤ kBVEnergy u := by
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => sq_nonneg _)
    (kBV_integrable_energy h1 h2)
  apply Filter.Eventually.of_forall
  intro ξ
  by_cases hξ : ξ ∈ Icc (-1 : ℝ) 1
  · have hξ1 : ξ ^ 2 ≤ 1 := by nlinarith [hξ.1, hξ.2]
    simp only [kBVLowFreqSlope, kBVLowFreq, indicator_of_mem hξ, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, min_eq_left hξ1, le_refl]
  · simp only [kBVLowFreqSlope, kBVLowFreq, indicator_of_notMem hξ, mul_zero, norm_zero,
      zero_pow (by decide : 2 ≠ 0)]
    positivity

set_option backward.isDefEq.respectTransparency false in
/-- The low-frequency representative is differentiable everywhere, with the
explicit inverse-transform derivative. -/
theorem kBVLowPass_hasDerivAt {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) (x : ℝ) :
    HasDerivAt (kBVLowPass u) (kBVLowPassDeriv u x) x := by
  have hlow1 := kBVLowFreq_integrable h1 h2
  have hmom : Integrable (fun ξ : ℝ => ξ • kBVLowFreq u ξ) := by
    have hh := kBVLowFreqSlope_integrable h1 h2
    change Integrable (fun ξ : ℝ => (ξ : ℂ) * kBVLowFreq u ξ) at hh
    simpa only [Complex.real_smul] using hh
  have h := (Real.hasDerivAt_fourier hlow1 hmom (-x)).scomp x (hasDerivAt_neg' x)
  have he : (fun ξ : ℝ => (-2 * Real.pi * I * ξ) • kBVLowFreq u ξ) =
      -(fun ξ => (2 * Real.pi * I) * kBVLowFreqSlope u ξ) := by
    funext ξ
    simp only [Pi.neg_apply, smul_eq_mul, kBVLowFreqSlope]
    ring
  have hneg : ∀ t : ℝ, 𝓕 (-(fun ξ => (2 * Real.pi * I) * kBVLowFreqSlope u ξ)) t =
      -𝓕 (fun ξ => (2 * Real.pi * I) * kBVLowFreqSlope u ξ) t := by
    intro t
    simp only [Real.fourier_eq, Pi.neg_apply, smul_neg, integral_neg]
  rw [he, hneg] at h
  have hv : kBVLowPass u = 𝓕 (kBVLowFreq u) ∘ Neg.neg := by
    funext t
    exact Real.fourierInv_eq_fourier_neg _ t
  rw [hv]
  simpa only [kBVLowPassDeriv, Real.fourierInv_eq_fourier_neg,
    neg_smul, one_smul, neg_neg] using h

theorem kBVLowPassDeriv_memLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (kBVLowPassDeriv u) 2 :=
  kBV_memLp_two_fourierInv ((kBVLowFreqSlope_integrable h1 h2).const_mul _)
    ((kBVLowFreqSlope_memLp h1 h2).const_mul _)

theorem kBVLowPassDeriv_continuous {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    Continuous (kBVLowPassDeriv u) :=
  kBV_continuous_fourierInv ((kBVLowFreqSlope_integrable h1 h2).const_mul _)

/-- The actual spatial derivative has the squared-energy scale `4π² E(u)`. -/
theorem kBVLowPass_deriv_normSq_le {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    kBVNormSq (kBVLowPassDeriv u) ≤ (2 * Real.pi) ^ 2 * kBVEnergy u := by
  have hi := (kBVLowFreqSlope_integrable h1 h2).const_mul (2 * Real.pi * I)
  have hm := (kBVLowFreqSlope_memLp h1 h2).const_mul (2 * Real.pi * I)
  have hn : ‖(2 * Real.pi * I : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, norm_I, mul_one]
  unfold kBVNormSq kBVLowPassDeriv
  rw [kBV_plancherelInv hi hm]
  simp only [norm_mul, mul_pow, hn]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (kBVLowFreqSlope_normSq_le h1 h2) (by positivity)

end
end PGM
