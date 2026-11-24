import PLAStochastic.Index.CEPS.Scaled.ZeroEndpointScale
import PLAStochastic.Index.CEPS.Jets.Consistency

/-! # Finite jet determination of the zero-discount endpoint polynomial

The coefficients read the variance and the spatial-slope drift jets from X8.
Equality with the canonical surrogate uses the already proved line-shift
consistency theorem on its stated neighbourhood of the reference density.
-/

noncomputable section
open Complex Set Metric MeasureTheory Finset
open PGM.WienerHopf
namespace PGM

def cepsZeroEndpointJetPolynomial (p : ℕ → ℝ) (N : ℕ) (b : ℂ) : ℂ :=
  1 - (p (cepsJetCode (.inl 0)) : ℂ) / 2 +
    b * (1 + 2 * ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * b ^ j *
      (p (cepsJetCode (.inr (j, 1, 0))) : ℂ)) - b ^ 2 / 2

theorem cepsZeroEndpointJetPolynomial_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (N + 1) → p i = p' i) :
    cepsZeroEndpointJetPolynomial p N = cepsZeroEndpointJetPolynomial p' N := by
  have hv := hp (cepsJetCode (.inl 0))
    (cepsJetCode_lt_cepsJetDim (show cepsJetWeight (.inl 0) ≤ N + 1 by simp [cepsJetWeight]))
  funext b
  unfold cepsZeroEndpointJetPolynomial
  rw [hv]
  have hs : (∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * b ^ j *
      (p (cepsJetCode (.inr (j, 1, 0))) : ℂ)) =
      ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * b ^ j *
        (p' (cepsJetCode (.inr (j, 1, 0))) : ℂ) := by
    apply sum_congr rfl
    intro j hj
    rw [hp (cepsJetCode (.inr (j, 1, 0)))
      (cepsJetCode_lt_cepsJetDim (by have := mem_range.mp hj; simp only [cepsJetWeight]; omega))]
  rw [hs]

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW f : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)

include hW hθ hD in
theorem cepsStepVar_eq_jet (hfW : ∀ y, fW y = f (1 - y)) :
    cepsStepVar ρW = cepsJet f (cepsJetCode (.inl 0)) := by
  have h := cepsJet_cumulant_eq hW hθ hD hfW 0
  rw [show (0 : ℕ) + 2 = 1 + 1 by omega, iteratedDeriv_succ, iteratedDeriv_one,
    deriv_deriv_cepsCgf_zero hW hθ hD] at h
  exact ofReal_injective h

include hθ hD in
theorem cepsScaledSurrogateZeroEndpoint_eq_jetPolynomial :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m →
        cepsScaledSurrogateZeroEndpoint dom ρW N = cepsZeroEndpointJetPolynomial (cepsJet f) N := by
  obtain ⟨r, hr, he⟩ := cepsJet_contour_eq dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hclose N hN
  have hj : ∀ j ∈ range (N + 1), cepsCanonSpatialDriftCoeff dom ρW j 0 =
      (cepsJet f (cepsJetCode (.inr (j, 1, 0))) : ℂ) := by
    intro j hmem
    have hc := he hW hfW hneg hη hf hclose j 1 0
      (by have := mem_range.mp hmem; omega)
    simpa only [cepsCanonSpatialDriftCoeff, cepsCanonDriftCoeff,
      iteratedDeriv_zero, iteratedDeriv_one] using! hc
  funext b
  unfold cepsScaledSurrogateZeroEndpoint cepsZeroEndpointJetPolynomial
  rw [cepsStepVar_eq_jet hW hθ hD hfW]
  have hs : cepsCanonSpatialDriftTaylor dom ρW N b 0 =
      ∑ j ∈ range (N + 1), (j.factorial : ℂ)⁻¹ * b ^ j *
        (cepsJet f (cepsJetCode (.inr (j, 1, 0))) : ℂ) := by
    unfold cepsCanonSpatialDriftTaylor
    apply sum_congr rfl
    intro j hmem
    rw [hj j hmem]
  rw [hs]

end PGM
