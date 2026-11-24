import Mathlib.Analysis.Fourier.LpSpace

/-!
# WP4 `SurvivalBound`: Plancherel for `L¹ ∩ L²` functions on `ℝ`

Mathlib provides the Fourier transform on `L²` only as the abstract isometry
`MeasureTheory.Lp.fourierTransformₗᵢ` (the extension of the Schwartz-space transform).  For the
killed convolution chains we need Plancherel for the *integral* transform
`𝓕 u ξ = ∫ e^{-2πi ξ y} u(y) dy` of `u ∈ L¹ ∩ L²`.

Route (tempered distributions, no approximation argument).  Let `U = u` in `L²` and `W = 𝓕 U`.
For a smooth compactly supported `g`, viewed as a Schwartz function `G`,

`∫ g W = W(G) = (𝓕 U)(G) = U(𝓕 G) = ∫ (𝓕 G) u = ∫ g (𝓕 u)`,

using that the `L²` and `𝓢'` transforms agree (`Lp.fourier_toTemperedDistribution_eq`) and the
self-adjointness of the integral transform on `L¹` (`VectorFourier.integral_fourierIntegral_smul_eq_flip`).
Both `W` and `𝓕 u` are locally integrable, so `W = 𝓕 u` a.e.
(`ae_eq_of_integral_contDiff_smul_eq`); then `‖𝓕 u‖₂ = ‖W‖ = ‖U‖ = ‖u‖₂`.

Main results: `kill_fourier_toLp_two_ae_eq`, `kill_memLp_two_fourier`, `plancherel_integrable_memLp`
(Plancherel), `kill_norm_fourier_le`.
-/

namespace PGM

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ContDiff

/-- For `f ∈ L²(ℝ)`, `‖f‖² = ∫ ‖f x‖²`. -/
theorem kill_Lp_two_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have hmem := Lp.memLp f
  have h := hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hI : 0 ≤ ∫ x, ‖(f : ℝ → ℂ) x‖ ^ (2 : ENNReal).toReal :=
    integral_nonneg fun x => by positivity
  rw [Lp.norm_def, h, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat] at hI ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hI]
  norm_num

/-- The integral Fourier transform of an integrable function is continuous. -/
theorem kill_continuous_fourier {u : ℝ → ℂ} (h1 : Integrable u) : Continuous (𝓕 u) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ h1

/-- `‖𝓕 u ξ‖ ≤ ∫ ‖u‖`. -/
theorem kill_norm_fourier_le (u : ℝ → ℂ) (ξ : ℝ) : ‖𝓕 u ξ‖ ≤ ∫ y, ‖u y‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext y
  rw [Circle.norm_smul]

/-- Self-adjointness of the integral transform on `ℝ`: `∫ (𝓕 f) g = ∫ f (𝓕 g)`. -/
theorem kill_integral_fourier_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕 f ξ * g ξ = ∫ x, f x * 𝓕 g x := by
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
    (L := innerₗ ℝ) Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf hg
  have hflip : ∀ x, VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ ℝ).flip g x =
      𝓕 g x := by
    intro x
    rw [Real.fourier_eq]
    unfold VectorFourier.fourierIntegral
    congr 1
    funext v
    simp only [LinearMap.flip_apply, innerₗ_apply_apply, real_inner_comm]
  simp only [smul_eq_mul, hflip] at h
  exact h

/-- **The `L²` Fourier transform of an `L¹ ∩ L²` function is its integral transform.** -/
theorem kill_fourier_toLp_two_ae_eq {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    ((𝓕 (h2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕 u := by
  set U : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp u with hU
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕 U)).locallyIntegrable (by norm_num)
  · exact (kill_continuous_fourier h1).locallyIntegrable
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hG
  have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
  have key1 : ∫ x, g x • ((𝓕 U : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
      Lp.toTemperedDistribution (𝓕 U) G := by
    rw [Lp.toTemperedDistribution_apply]
    congr 1
  have key2 : Lp.toTemperedDistribution (𝓕 U) G = ∫ x, 𝓕 (G : ℝ → ℂ) x * u x := by
    rw [← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply,
      Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [← hU] at hx
    rw [hx, SchwartzMap.fourier_coe, smul_eq_mul]
  rw [key1, key2]
  have hGi : Integrable (G : ℝ → ℂ) := G.integrable
  rw [kill_integral_fourier_mul_eq hGi h1]
  congr 1

/-- The integral transform of an `L¹ ∩ L²` function is in `L²`. -/
theorem kill_memLp_two_fourier {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (𝓕 u) 2 :=
  (Lp.memLp (𝓕 (h2.toLp u))).ae_eq (kill_fourier_toLp_two_ae_eq h1 h2)

/-- **Plancherel for `L¹ ∩ L²`.**  For `u : ℝ → ℂ` integrable and square integrable,
`∫ ‖𝓕 u ξ‖² dξ = ∫ ‖u y‖² dy`, with Mathlib's normalization
`𝓕 u ξ = ∫ e^{-2πi ξ y} u(y) dy`. -/
theorem plancherel_integrable_memLp {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    ∫ ξ, ‖𝓕 u ξ‖ ^ 2 = ∫ y, ‖u y‖ ^ 2 := by
  set U : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp u with hU
  have hW : ∫ ξ, ‖𝓕 u ξ‖ ^ 2 =
      ∫ ξ, ‖((𝓕 U : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) ξ‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [kill_fourier_toLp_two_ae_eq h1 h2] with ξ hξ
    rw [← hU] at hξ
    rw [hξ]
  have hUu : ∫ y, ‖(U : ℝ → ℂ) y‖ ^ 2 = ∫ y, ‖u y‖ ^ 2 := by
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with y hy
    rw [← hU] at hy
    rw [hy]
  rw [hW, ← kill_Lp_two_norm_sq_eq_integral, Lp.norm_fourier_eq, kill_Lp_two_norm_sq_eq_integral, hUu]

end

end PGM
