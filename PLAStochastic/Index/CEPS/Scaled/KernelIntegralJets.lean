import PLAStochastic.Index.CEPS.Scaled.KernelSubtractedPairJets
import PLAStochastic.Index.CEPS.Scaled.CutoffPairTaylor

/-! # Genuine Bochner integral coefficients in the explicit finite kernel-jet model -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries
open PGM.WienerHopf
namespace PGM

def cepsKernelPairCoeffJetModel (p : ℕ → ℝ) (N n : ℕ) (z : ℂ) (lam : ℝ) : ℂ :=
  coeff n (complexTaylorSeries (cepsKernelSubtractedPairJetModel p N lam z) 0)

def cepsKernelPairIntegralCoeffJetModel (p : ℕ → ℝ) (N n : ℕ) (z : ℂ) : ℂ :=
  ∫ lam : ℝ, cepsKernelPairCoeffJetModel p N n z lam

theorem cepsKernelPairCoefficients_congr {p p' : ℕ → ℝ} (N : ℕ)
    (hp : ∀ i, i < cepsJetDim (4 * N) → p i = p' i) (n : ℕ) (z : ℂ) :
    cepsKernelPairCoeffJetModel p N n z = cepsKernelPairCoeffJetModel p' N n z ∧
    cepsKernelPairIntegralCoeffJetModel p N n z = cepsKernelPairIntegralCoeffJetModel p' N n z := by
  have hc : cepsKernelPairCoeffJetModel p N n z = cepsKernelPairCoeffJetModel p' N n z := by
    funext lam
    simp only [cepsKernelPairCoeffJetModel, (cepsKernelPairModels_congr N hp lam z).2.2]
  exact ⟨hc, by simp only [cepsKernelPairIntegralCoeffJetModel, hc]⟩

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogatePairCoeff_ae_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ {z : ℂ}, 0 ≤ z.re → ∀ n ≤ N,
        cepsScaledSurrogatePairCoeff dom ρW N n z =ᵐ[volume]
          cepsKernelPairCoeffJetModel (cepsJet f) N n z := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateSubtractedPair_taylorJets_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN z hz n hn
  filter_upwards [(volume : Measure ℝ).ae_ne 0] with lam hlam
  simpa only [cepsScaledSurrogatePairCoeff, cepsKernelPairCoeffJetModel,
    complexTaylorSeries, coeff_mk] using he hW hfW hneg hη hf hfS hηc hclose N hN lam hz (Or.inl hlam) n hn

include hθ hD in
theorem cepsScaledSurrogatePairIntegralCoeff_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ {z : ℂ}, 0 ≤ z.re → ∀ n ≤ N,
        Integrable (cepsKernelPairCoeffJetModel (cepsJet f) N n z) ∧
        cepsScaledSurrogatePairIntegralCoeff dom ρW N n z =
          cepsKernelPairIntegralCoeffJetModel (cepsJet f) N n z := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogatePairCoeff_ae_eq_finite_model dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN z hz n hn
  have hae := he hW hfW hneg hη hf hfS hηc hclose N hN hz n hn
  have hi := cepsScaledSurrogatePairCoeff_integrable dom hW hθ hD hfS hηc le_rfl N hN hz n
  exact ⟨hi.congr hae, integral_congr_ae hae⟩

end PGM
