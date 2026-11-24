import PLAStochastic.Index.GEP.Kernel.BV.Energy
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Integral and `L²` inverse Fourier transforms

These lemmas connect the actual integral inverse transform used for the smooth
low-frequency representative to the unitary inverse transform on `L²`.
-/

namespace PGM
noncomputable section
open MeasureTheory SchwartzMap FourierTransform
open scoped ContDiff

/-- The integral inverse Fourier transform is continuous on `L¹`. -/
theorem kBV_continuous_fourierInv {u : ℝ → ℂ} (h1 : Integrable u) :
    Continuous (𝓕⁻ u) := by
  have he : 𝓕⁻ u = fun x => 𝓕 u (-x) := funext (Real.fourierInv_eq_fourier_neg u)
  rw [he]
  exact (kill_continuous_fourier h1).comp continuous_neg

/-- Symmetry of the inverse Fourier integral in its two integrable arguments. -/
theorem kBV_integral_fourierInv_mul_eq {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    ∫ ξ, 𝓕⁻ f ξ * g ξ = ∫ x, f x * 𝓕⁻ g x := by
  calc
    (∫ ξ, 𝓕⁻ f ξ * g ξ) = (∫ ξ, 𝓕 f (-ξ) * g ξ) := by
      simp only [Real.fourierInv_eq_fourier_neg]
    _ = ∫ ξ, 𝓕 f ξ * g (-ξ) := by
      simpa only [neg_neg] using (integral_neg_eq_self (fun ξ => 𝓕 f ξ * g (-ξ)) volume)
    _ = ∫ x, f x * 𝓕 (fun ξ => g (-ξ)) x :=
      kill_integral_fourier_mul_eq hf hg.comp_neg
    _ = ∫ x, f x * 𝓕⁻ g x := by rw [Real.fourierInv_eq_fourier_comp_neg]

/-- The integral and unitary inverse transforms agree almost everywhere on `L¹ ∩ L²`. -/
theorem kBV_fourierInv_toLp_two_ae_eq {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    ((𝓕⁻ (h2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) =ᵐ[volume] 𝓕⁻ u := by
  set U : Lp ℂ 2 (volume : Measure ℝ) := h2.toLp u with hU
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (Lp.memLp (𝓕⁻ U)).locallyIntegrable (by norm_num)
  · exact (kBV_continuous_fourierInv h1).locallyIntegrable
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hG
  have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
  have key1 : ∫ x, g x • ((𝓕⁻ U : Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) x =
      Lp.toTemperedDistribution (𝓕⁻ U) G := by
    rw [Lp.toTemperedDistribution_apply]
    congr 1
  have key2 : Lp.toTemperedDistribution (𝓕⁻ U) G = ∫ x, 𝓕⁻ (G : ℝ → ℂ) x * u x := by
    rw [← Lp.fourierInv_toTemperedDistribution_eq, TemperedDistribution.fourierInv_apply,
      Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [h2.coeFn_toLp] with x hx
    rw [← hU] at hx
    rw [hx, SchwartzMap.fourierInv_coe, smul_eq_mul]
  rw [key1, key2]
  have hGi : Integrable (G : ℝ → ℂ) := G.integrable
  rw [kBV_integral_fourierInv_mul_eq hGi h1]
  congr 1

/-- The integral inverse transform preserves square integrability. -/
theorem kBV_memLp_two_fourierInv {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    MemLp (𝓕⁻ u) 2 :=
  (Lp.memLp (𝓕⁻ (h2.toLp u))).ae_eq (kBV_fourierInv_toLp_two_ae_eq h1 h2)

/-- Inverse Plancherel for the integral representative. -/
theorem kBV_plancherelInv {u : ℝ → ℂ} (h1 : Integrable u) (h2 : MemLp u 2) :
    ∫ ξ, ‖𝓕⁻ u ξ‖ ^ 2 = ∫ y, ‖u y‖ ^ 2 := by
  have he : 𝓕⁻ u = fun x => 𝓕 u (-x) := funext (Real.fourierInv_eq_fourier_neg u)
  rw [he]
  calc (∫ ξ, ‖𝓕 u (-ξ)‖ ^ 2) = ∫ ξ, ‖𝓕 u ξ‖ ^ 2 := integral_neg_eq_self (fun ξ : ℝ => ‖𝓕 u ξ‖ ^ 2) volume
    _ = _ := plancherel_integrable_memLp h1 h2

/-- The `L²` norm of an integrable representative agrees with its ordinary integral. -/
theorem kBV_toLp_norm_sq {u : ℝ → ℂ} (h2 : MemLp u 2) :
    ‖h2.toLp u‖ ^ 2 = kBVNormSq u := by
  rw [kill_Lp_two_norm_sq_eq_integral]
  exact integral_congr_ae (h2.coeFn_toLp.fun_comp fun z => ‖z‖ ^ 2)

end
end PGM
