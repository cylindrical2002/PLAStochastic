import PLAStochastic.Index.CEPS.Inversion.Sobolev
import PLAStochastic.Index.CEPS.Inversion.Moments
import PLAStochastic.ForMathlib.Analysis.Fourier.RealCoefficients

/-!
# Fourier inversion assembly for the one-layer family

The input contains the three-band estimates and a continuous density representative.
Coefficient measurability is derived from the local expansions. No weighted
coefficient envelopes or real-space expansion estimates are assumed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace PGM

theorem UniformInverseExpansion.congr_eventually {F F' : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (h : UniformInverseExpansion F g) (he : ∀ᶠ eps in atTop, F eps = F' eps) :
    UniformInverseExpansion F' g := by
  intro N
  obtain ⟨K, E, hK⟩ := h N
  obtain ⟨E', hE'⟩ := eventually_atTop.mp he
  refine ⟨K, max E E', fun eps he x => ?_⟩
  rw [← hE' eps ((le_max_right _ _).trans he)]
  exact hK eps ((le_max_left _ _).trans he) x

/-- Recover the continuous actual density as a complex inverse transform. -/
theorem FourierBandEstimates.eventually_complex_inverse_eq_density {φ : ℝ → ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ)) :
    ∀ᶠ eps in atTop, angularInverse (φ eps) = fun x => (F eps x : ℂ) := by
  obtain ⟨B, -, hb⟩ := h.actual_moment_bound 0
  filter_upwards [hb, hφ, hF] with eps he hm hf
  have hi : Integrable (φ eps) := by
    have hn : Integrable (fun u => ‖φ eps u‖) := by
      simpa only [pow_zero, one_mul] using (integrable_fourier_moment_of_bound hm le_rfl he).1
    exact (integrable_norm_iff hm).mp hn
  have hinv := angularInverse_charIntegral hf.1 hf.2.1 (by simpa only [← hf.2.2] using hi)
  rw [← hf.2.2] at hinv
  exact hinv

/-- The real inverse representative equals the given continuous density. -/
theorem FourierBandEstimates.eventually_inverse_eq_density {φ : ℝ → ℝ → ℂ}
    {a : ℕ → ℝ → ℂ} {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ)) :
    ∀ᶠ eps in atTop, angularRealInverse (φ eps) = F eps := by
  filter_upwards [h.eventually_complex_inverse_eq_density hφ hF] with eps he
  funext x
  exact congrArg Complex.re (congrFun he x)

/-- The analytic core of track F: H/M/C/L and the density envelope give every
fixed weighted Sobolev expansion. The weight may depend on the two fixed budgets. -/
theorem cepsFourier_sobolev_expansion {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) (m N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ (∀ k ≤ N, CepsSobolevClass m η (angularRealInverse (a k))) ∧
      (∀ᶠ eps in atTop, CepsSobolevClass m η (F eps)) ∧
      IsInverseOrder (fun eps => cepsSobolev m η
        (cepsInversionRemainder F (fun k => angularRealInverse (a k)) N eps)) (N + 1) := by
  have ha := h.coefficient_aestronglyMeasurable hφ
  have heq := h.eventually_inverse_eq_density hφ hF
  have hcd (j : ℕ) : ∀ᶠ eps in atTop, ContDiff ℝ j (F eps) := by
    obtain ⟨B, -, hb⟩ := h.actual_inverse_bounded hφ j
    filter_upwards [hb, heq] with eps he hre
    rw [hre] at he
    exact he.1
  have hbound (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ eps in atTop,
      ∀ r ≤ j, ∀ x, |iteratedDeriv r (F eps) x| ≤ B := by
    obtain ⟨B, hB, hb⟩ := h.actual_inverse_bounded hφ j
    refine ⟨B, hB, ?_⟩
    filter_upwards [hb, heq] with eps he hre
    rw [hre] at he
    exact he.2
  have hu (r : ℕ) : UniformInverseExpansion (fun eps => iteratedDeriv r (F eps))
      (fun k => iteratedDeriv r (angularRealInverse (a k))) :=
    (h.uniform_inverse_expansion hφ ha r).congr_eventually
      (heq.mono fun eps he => congrArg (iteratedDeriv r) he)
  exact cepsSobolev_expansion_of_uniform hcd (h.coefficient_contDiff ha) hu hbound henv m N

/-- Zero support of the actual density passes to every coefficient. -/
theorem cepsFourier_coefficient_zero {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hφ : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps))
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    {x : ℝ} (hz : ∀ᶠ eps in atTop, F eps x = 0) (k : ℕ) : angularRealInverse (a k) x = 0 := by
  have ha := h.coefficient_aestronglyMeasurable hφ
  have heq := h.eventually_inverse_eq_density hφ hF
  have hu := h.uniform_inverse_expansion hφ ha 0
  simp only [iteratedDeriv_zero] at hu
  apply hu.coefficient_zero
  filter_upwards [heq, hz] with eps he hz
  rw [he, hz]

/-- The density formulation requires no independent measurability assumptions on
either the actual transforms or their asymptotic coefficients. -/
theorem cepsFourier_sobolev_expansion_of_density {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) (m N : ℕ) :
    ∃ η : ℝ, 0 < η ∧ (∀ k ≤ N, CepsSobolevClass m η (angularRealInverse (a k))) ∧
      (∀ᶠ eps in atTop, CepsSobolevClass m η (F eps)) ∧
      IsInverseOrder (fun eps => cepsSobolev m η
        (cepsInversionRemainder F (fun k => angularRealInverse (a k)) N eps)) (N + 1) := by
  have hm : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps) := by
    filter_upwards [hF] with eps he
    rw [he.2.2]
    exact (continuous_charIntegral he.1).aestronglyMeasurable
  exact cepsFourier_sobolev_expansion h hm hF henv m N

/-- The full complex inverse coefficients are real and smooth. -/
theorem cepsFourier_coefficients_real_smooth {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ)) :
    (∀ k x, angularInverse (a k) x = (angularRealInverse (a k) x : ℂ)) ∧
      ∀ k, ContDiff ℝ ∞ (angularRealInverse (a k)) := by
  have hm : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps) := by
    filter_upwards [hF] with eps he
    rw [he.2.2]
    exact (continuous_charIntegral he.1).aestronglyMeasurable
  have heq := h.eventually_complex_inverse_eq_density hm hF
  have hreal : ∀ᶠ eps in atTop, ∀ x, (angularInverse (φ eps) x).im = 0 := by
    filter_upwards [heq] with eps he x
    rw [he]
    exact Complex.ofReal_im _
  refine ⟨h.inverse_coefficients_real hm hreal, fun k => contDiff_infty.mpr ?_⟩
  exact fun m => h.coefficient_contDiff (h.coefficient_aestronglyMeasurable hm) m k

/-- An actual support condition passes to every inverse coefficient. -/
theorem cepsFourier_coefficients_support {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (hsupport : ∀ᶠ eps in atTop, ∀ x ≤ 0, F eps x = 0) :
    ∀ k x, x ≤ 0 → angularRealInverse (a k) x = 0 := by
  have hm : ∀ᶠ eps in atTop, AEStronglyMeasurable (φ eps) := by
    filter_upwards [hF] with eps he
    rw [he.2.2]
    exact (continuous_charIntegral he.1).aestronglyMeasurable
  intro k x hx
  exact cepsFourier_coefficient_zero h hm hF (hsupport.mono fun _ he => he x hx) k

/-- The Sobolev assembly supplies all the weighted expansions used by moment readout. -/
theorem cepsFourier_weighted_expansion {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|)) :
    CepsInversionWeightedExpansion F (fun k => angularRealInverse (a k)) :=
  fun P => cepsFourier_sobolev_expansion_of_density h hF henv 0 P

/-- Probability normalization determines the mass of all coefficient densities. -/
theorem cepsFourier_mass_coefficients {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|))
    (hmass : ∀ᶠ eps in atTop, (∫ x, F eps x) = 1) :
    (∫ x, angularRealInverse (a 0) x) = 1 ∧
      ∀ k : ℕ, 1 ≤ k → (∫ x, angularRealInverse (a k) x) = 0 :=
  (cepsFourier_weighted_expansion h hF henv).mass_coefficients hmass

/-- A constant actual mean gives zero first moments at every positive order. -/
theorem cepsFourier_firstMoment_coefficients {φ : ℝ → ℝ → ℂ} {a : ℕ → ℝ → ℂ}
    {F : ℝ → ℝ → ℝ} (h : FourierBandEstimates φ a)
    (hF : ∀ᶠ eps in atTop, Integrable (F eps) ∧ Continuous (F eps) ∧
      φ eps = fun u : ℝ => ∫ x : ℝ, Complex.exp (((u * x : ℝ) : ℂ) * Complex.I) * (F eps x : ℂ))
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|))
    {q : ℝ} (hmean : ∀ᶠ eps in atTop, (∫ x : ℝ, x * F eps x) = q) :
    (∫ x : ℝ, x * angularRealInverse (a 0) x) = q ∧
      ∀ k : ℕ, 1 ≤ k → (∫ x : ℝ, x * angularRealInverse (a k) x) = 0 :=
  (cepsFourier_weighted_expansion h hF henv).firstMoment_coefficients hmean

/-- For a nonnegative density supported on the positive half-line, the one-sided
input envelope is exactly the symmetric envelope used in the assembly. -/
theorem cepsDensity_symmetric_envelope {F : ℝ → ℝ → ℝ}
    (hnonneg : ∀ᶠ eps in atTop, ∀ x, 0 ≤ F eps x)
    (hsupport : ∀ᶠ eps in atTop, ∀ x ≤ 0, F eps x = 0)
    (henv : ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, 0 < x → F eps x ≤ A * Real.exp (-θ * x)) :
    ∃ A θ : ℝ, 0 ≤ A ∧ 0 < θ ∧ ∀ᶠ eps in atTop,
      ∀ x, |F eps x| ≤ A * Real.exp (-θ * |x|) := by
  obtain ⟨A, θ, hA, hθ, he⟩ := henv
  refine ⟨A, θ, hA, hθ, ?_⟩
  filter_upwards [hnonneg, hsupport, he] with eps hn hs he x
  by_cases hx : x ≤ 0
  · rw [hs x hx, abs_zero]
    positivity
  · rw [abs_of_nonneg (hn x), abs_of_pos (lt_of_not_ge hx)]
    exact he x (lt_of_not_ge hx)

end PGM
