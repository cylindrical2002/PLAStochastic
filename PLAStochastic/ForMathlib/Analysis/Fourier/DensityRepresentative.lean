import PLAStochastic.ForMathlib.Analysis.Fourier.InverseAsymptotics
import PLAStochastic.ForMathlib.Analysis.Fourier.PlancherelIntegrable
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Continuous representatives of densities with integrable characteristic integrals

For an integrable real `f` whose characteristic integral
`φ u = ∫ exp (i u x) f x dx` is integrable, the continuous function `angularRealInverse φ`
agrees with `f` almost everywhere. No continuity of `f` is assumed: with Mathlib's
conventions `u ↦ φ (2π u)` is `𝓕⁻ f`, so `angularInverse φ = 𝓕 (𝓕⁻ f)`, and the identity
`𝓕 (𝓕⁻ f) = f` is tested against smooth compactly supported functions, using
self-adjointness of the integral transform and Schwartz inversion.
-/

noncomputable section

open MeasureTheory SchwartzMap FourierTransform
open scoped ContDiff

namespace PGM

/-- Inverting the Fourier transform of an integrable function with integrable inverse
transform recovers the function almost everywhere. -/
theorem fourier_fourierInv_ae_eq {F : ℝ → ℂ} (hF : Integrable F) (hH : Integrable (𝓕⁻ F)) :
    𝓕 (𝓕⁻ F) =ᵐ[volume] F := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (kill_continuous_fourier hH).locallyIntegrable
  · exact hF.locallyIntegrable
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  set G : 𝓢(ℝ, ℂ) := hg₁.toSchwartzMap hg₂ with hG
  have hGx : ∀ x, G x = (g x : ℂ) := fun x => rfl
  have hGi : Integrable (G : ℝ → ℂ) := G.integrable
  have hFGi : Integrable (𝓕 (G : ℝ → ℂ)) := (𝓕 G).integrable
  have hFF : ∀ x, 𝓕 (𝓕 (G : ℝ → ℂ)) x = G (-x) := by
    intro x
    have hinv : 𝓕⁻ (𝓕 (G : ℝ → ℂ)) = (G : ℝ → ℂ) :=
      G.continuous.fourierInv_fourier_eq hGi hFGi
    rw [← congrFun hinv (-x), Real.fourierInv_eq_fourier_neg, neg_neg]
  have hFneg : Integrable (fun x : ℝ => F (-x)) := hF.comp_neg
  calc
    ∫ x, g x • 𝓕 (𝓕⁻ F) x = ∫ x, 𝓕 (𝓕⁻ F) x * G x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hGx, Complex.real_smul]
      ring
    _ = ∫ x, 𝓕⁻ F x * 𝓕 (G : ℝ → ℂ) x := kill_integral_fourier_mul_eq hH hGi
    _ = ∫ x, 𝓕 (fun y => F (-y)) x * 𝓕 (G : ℝ → ℂ) x := by
      rw [Real.fourierInv_eq_fourier_comp_neg]
    _ = ∫ x, F (-x) * 𝓕 (𝓕 (G : ℝ → ℂ)) x := kill_integral_fourier_mul_eq hFneg hFGi
    _ = ∫ x, F (-x) * G (-x) := by simp only [hFF]
    _ = ∫ x, F x * G x := integral_neg_eq_self (fun x => F x * G x) volume
    _ = ∫ x, g x • F x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [hGx, Complex.real_smul]
      ring

/-- An integrable real function whose characteristic integral is integrable agrees almost
everywhere with the continuous angular inverse of that integral. -/
theorem angularRealInverse_charIntegral_ae_eq {f : ℝ → ℝ} (hf : Integrable f)
    (hi : Integrable (fun u : ℝ =>
      ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ))) :
    (angularRealInverse fun u : ℝ =>
      ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) =ᵐ[volume] f := by
  set F : ℝ → ℂ := fun x => (f x : ℂ) with hFdef
  have hF : Integrable F := hf.ofReal
  have hscale : 𝓕⁻ F = fun u : ℝ => ∫ x : ℝ,
      Complex.exp ((((2 * Real.pi * u) * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ) := by
    funext u
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFdef, smul_eq_mul]
    congr 2
    push_cast
    ring
  have hH : Integrable (𝓕⁻ F) := by
    rw [hscale]
    exact hi.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hang : angularInverse (fun u : ℝ =>
      ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) = 𝓕 (𝓕⁻ F) := by
    rw [angularInverse, hscale]
  filter_upwards [fourier_fourierInv_ae_eq hF hH] with x hx
  change (angularInverse _ x).re = f x
  rw [hang, hx]
  simp only [hFdef, Complex.ofReal_re]

/-- The real angular inverse of an integrable function is continuous. -/
theorem continuous_angularRealInverse {φ : ℝ → ℂ} (hφ : Integrable φ) :
    Continuous (angularRealInverse φ) := by
  have hs : Integrable (fun u : ℝ => φ (2 * Real.pi * u)) :=
    hφ.comp_mul_left' (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  exact Complex.continuous_re.comp (kill_continuous_fourier hs)

/-- A.e. inequality between continuous functions holds everywhere. -/
theorem le_of_ae_le_of_continuous {g k : ℝ → ℝ} (hg : Continuous g) (hk : Continuous k)
    (h : ∀ᵐ x ∂(volume : Measure ℝ), g x ≤ k x) (x : ℝ) : g x ≤ k x := by
  by_contra hx
  have hU : IsOpen {y : ℝ | k y < g y} := isOpen_lt hk hg
  have h0 : volume {y : ℝ | k y < g y} = 0 := by
    rw [ae_iff] at h
    simpa only [not_le] using h
  have hmem : x ∈ {y : ℝ | k y < g y} := lt_of_not_ge hx
  rw [(hU.measure_eq_zero_iff volume).mp h0] at hmem
  exact hmem

/-- Quadratic decay gives integrability. -/
theorem integrable_of_norm_le_div_one_add_sq {φ : ℝ → ℂ} (hm : AEStronglyMeasurable φ) {C : ℝ}
    (hb : ∀ u, ‖φ u‖ ≤ C / (1 + u ^ 2)) : Integrable φ := by
  refine (integrable_inv_one_add_sq.const_mul C).mono' hm (Filter.Eventually.of_forall fun u => ?_)
  rw [← div_eq_mul_inv]
  exact hb u

end PGM
