import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Fourier inversion with angular frequencies

Mathlib uses `exp (-2π i u x)`. `angularInverse` uses the probability convention
`(2π)⁻¹ ∫ exp (-i u x) φ(u) du`. The polynomial moment hypotheses are explicit;
none of the bounds use the convention that a nonintegrable Bochner integral is zero.
-/

noncomputable section

open MeasureTheory Complex FourierTransform
open scoped ContDiff

namespace PGM

def angularInverse (φ : ℝ → ℂ) : ℝ → ℂ :=
  𝓕 (fun u : ℝ => φ (2 * Real.pi * u))

/-- The inverse transform in the probability convention. -/
theorem angularInverse_eq_integral (φ : ℝ → ℂ) (x : ℝ) :
    angularInverse φ x = (1 / (2 * Real.pi) : ℂ) *
      ∫ u : ℝ, Complex.exp (-((u * x : ℝ) : ℂ) * I) * φ u := by
  have h := Measure.integral_comp_mul_left
    (fun u : ℝ => Complex.exp (-((u * x : ℝ) : ℂ) * I) * φ u) (2 * Real.pi)
  rw [abs_of_pos (inv_pos.mpr (by positivity : 0 < 2 * Real.pi)), Complex.real_smul] at h
  rw [angularInverse, Real.fourier_real_eq_integral_exp_smul]
  calc
    _ = ∫ u : ℝ, Complex.exp (-(((2 * Real.pi * u) * x : ℝ) : ℂ) * I) *
        φ (2 * Real.pi * u) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        simp only [smul_eq_mul]
        congr 2
        push_cast
        ring
    _ = _ := by simpa only [one_div, ofReal_inv, ofReal_mul, ofReal_ofNat] using h

theorem angularInverse_const_mul (z : ℂ) (φ : ℝ → ℂ) (x : ℝ) :
    angularInverse (fun u => z * φ u) x = z * angularInverse φ x := by
  rw [angularInverse_eq_integral, angularInverse_eq_integral]
  have heq : (fun u : ℝ => Complex.exp (-((u * x : ℝ) : ℂ) * I) * (z * φ u)) =
      fun u => z * (Complex.exp (-((u * x : ℝ) : ℂ) * I) * φ u) := by funext u; ring
  rw [heq, integral_const_mul]
  ring

/-- Characteristic integrals of integrable densities are continuous. -/
theorem continuous_charIntegral {f : ℝ → ℝ} (hf : Integrable f) :
    Continuous (fun u : ℝ => ∫ x : ℝ,
      Complex.exp (((u * x : ℝ) : ℂ) * I) * (f x : ℂ)) := by
  let F : ℝ → ℂ := fun x => (f x : ℂ)
  have hFc : Continuous (𝓕 F) := VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hf.ofReal
  have heq : (fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * I) * (f x : ℂ)) =
      fun u => 𝓕 F (-u / (2 * Real.pi)) := by
    funext u
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [smul_eq_mul, F]
      congr 2
      push_cast
      field_simp
  rw [heq]
  exact hFc.comp (by fun_prop)

/-- Polynomial moments remain integrable after the angular-frequency rescaling. -/
theorem integrable_angular_rescale_pow {φ : ℝ → ℂ} (hφ : AEStronglyMeasurable φ)
    {r : ℕ} (hr : Integrable (fun u : ℝ => |u| ^ r * ‖φ u‖)) :
    Integrable (fun u : ℝ => u ^ r • φ (2 * Real.pi * u)) := by
  have hi : Integrable (fun u : ℝ => u ^ r • φ u) := by
    apply hr.mono' ((by fun_prop : Continuous fun u : ℝ => u ^ r).aestronglyMeasurable.smul hφ)
    exact Filter.Eventually.of_forall fun u => by simp
  have hc : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have h := (hi.comp_mul_left' hc).smul (((2 * Real.pi : ℝ) ^ r)⁻¹)
  apply h.congr
  exact Filter.Eventually.of_forall fun u => by
    change ((2 * Real.pi : ℝ) ^ r)⁻¹ • ((2 * Real.pi * u) ^ r • φ (2 * Real.pi * u)) = _
    rw [smul_smul, mul_pow (2 * Real.pi) u]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero r hc), one_mul]

/-- Integrable Fourier moments give all derivatives up to the prescribed order. -/
theorem contDiff_angularInverse {φ : ℝ → ℂ} {m : ℕ}
    (hφ : AEStronglyMeasurable φ)
    (hm : ∀ r ≤ m, Integrable (fun u : ℝ => |u| ^ r * ‖φ u‖)) :
    ContDiff ℝ m (angularInverse φ) := by
  apply Real.contDiff_fourier (N := (m : ℕ∞))
  intro r hr
  have hi := integrable_angular_rescale_pow hφ (hm r (by exact_mod_cast hr))
  simpa only [norm_smul, Real.norm_eq_abs, abs_pow] using hi.norm

/-- Derivatives of the inverse transform are inverse transforms of the frequency powers. -/
theorem iteratedDeriv_angularInverse {φ : ℝ → ℂ} {m r : ℕ}
    (hφ : AEStronglyMeasurable φ)
    (hm : ∀ j ≤ m, Integrable (fun u : ℝ => |u| ^ j * ‖φ u‖)) (hr : r ≤ m) :
    iteratedDeriv r (angularInverse φ) =
      𝓕 (fun u : ℝ => (-2 * Real.pi * I * u) ^ r * φ (2 * Real.pi * u)) := by
  apply Real.iteratedDeriv_fourier (N := (m : ℕ∞))
    (fun j hj => integrable_angular_rescale_pow hφ (hm j (by exact_mod_cast hj)))
    (by exact_mod_cast hr)

/-- A uniform derivative bound, stated with the rescaled integrable Fourier moment. -/
theorem norm_iteratedDeriv_angularInverse_le {φ : ℝ → ℂ} {m r : ℕ}
    (hφ : AEStronglyMeasurable φ)
    (hm : ∀ j ≤ m, Integrable (fun u : ℝ => |u| ^ j * ‖φ u‖)) (hr : r ≤ m) (x : ℝ) :
    ‖iteratedDeriv r (angularInverse φ) x‖ ≤
      (2 * Real.pi) ^ r * ∫ u : ℝ, |u| ^ r * ‖φ (2 * Real.pi * u)‖ := by
  rw [iteratedDeriv_angularInverse hφ hm hr, Real.fourier_real_eq]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  simp only [Circle.norm_smul, norm_mul, norm_pow, norm_neg, Complex.norm_two,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
  simp_rw [mul_pow]
  rw [← integral_const_mul]
  congr 1
  funext u
  ring

/-- Angular inversion recovers a continuous integrable density from its characteristic integral. -/
theorem angularInverse_charIntegral {f : ℝ → ℝ} (hf : Integrable f) (hfc : Continuous f)
    (hi : Integrable (fun u : ℝ =>
      ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * I) * (f x : ℂ))) :
    angularInverse (fun u : ℝ =>
      ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * I) * (f x : ℂ)) = fun x => (f x : ℂ) := by
  let F : ℝ → ℂ := fun x => (f x : ℂ)
  have hFT : 𝓕 F = fun u : ℝ =>
      ∫ x : ℝ, Complex.exp ((((-2 * Real.pi * u) * x : ℝ) : ℂ) * I) * (f x : ℂ) := by
    funext u
    rw [Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [F, smul_eq_mul]; congr 2; push_cast; ring
  have hFi : Integrable (𝓕 F) := by
    rw [hFT]
    exact hi.comp_mul_left' (by positivity : (-2 * Real.pi : ℝ) ≠ 0)
  have hrecover : 𝓕⁻ (𝓕 F) = F :=
    (Complex.continuous_ofReal.comp hfc).fourierInv_fourier_eq hf.ofReal hFi
  rw [Real.fourierInv_eq_fourier_comp_neg] at hrecover
  convert hrecover using 1
  unfold angularInverse
  rw [hFT]
  congr 1
  funext u
  simp only [mul_neg, neg_mul, neg_neg]

/-- Linearity of angular inversion on integrable transforms. -/
theorem angularInverse_sub_sum {φ : ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    (hφ : Integrable φ) (s : Finset ℕ) (ha : ∀ k ∈ s, Integrable (a k)) (t : ℕ → ℝ) :
    angularInverse (fun u => φ u - ∑ k ∈ s, t k • a k u) =
      fun x => angularInverse φ x - ∑ k ∈ s, t k • angularInverse (a k) x := by
  funext x
  let c := 2 * Real.pi
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hkernel {ψ : ℝ → ℂ} (hi : Integrable ψ) :
      Integrable (fun u : ℝ => Real.fourierChar (-(u * x)) • ψ (c * u)) := by
    have hkm : Continuous (fun u : ℝ => Real.fourierChar (-(u * x))) := by fun_prop
    apply (hi.comp_mul_left' hc).norm.mono'
      (hkm.aestronglyMeasurable.smul (hi.comp_mul_left' hc).aestronglyMeasurable)
    exact Filter.Eventually.of_forall fun u => by
      change ‖Real.fourierChar (-(u * x)) • ψ (c * u)‖ ≤ ‖ψ (c * u)‖
      simp only [Circle.norm_smul, le_refl]
  have hik : ∀ k ∈ s, Integrable (fun u : ℝ => t k • (Real.fourierChar (-(u * x)) • a k (c * u))) := by
    intro k hk
    change Integrable (fun u : ℝ => (t k : ℂ) * (Real.fourierChar (-(u * x)) • a k (c * u)))
    exact (hkernel (ha k hk)).const_mul (t k : ℂ)
  simp only [angularInverse, Real.fourier_real_eq]
  have heq : (fun v : ℝ => Real.fourierChar (-(v * x)) •
      (φ (c * v) - ∑ k ∈ s, t k • a k (c * v))) =
      fun v => Real.fourierChar (-(v * x)) • φ (c * v) -
        ∑ k ∈ s, t k • (Real.fourierChar (-(v * x)) • a k (c * v)) := by
    funext v
    rw [smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
  rw [heq]
  rw [integral_sub (hkernel hφ) (integrable_finsetSum _ hik), integral_finsetSum _ hik]
  simp only [integral_smul]
  rfl

/-- Real parts commute with finite real derivatives. -/
theorem iteratedDeriv_re {F : ℝ → ℂ} {m r : ℕ} (hf : ContDiff ℝ m F) (hr : r ≤ m) (x : ℝ) :
    iteratedDeriv r (fun y => (F y).re) x = (iteratedDeriv r F x).re := by
  rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv]
  change iteratedFDeriv ℝ r (Complex.reCLM ∘ F) x (fun _ => 1) = _
  rw [Complex.reCLM.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast hr)]
  rfl

end PGM
