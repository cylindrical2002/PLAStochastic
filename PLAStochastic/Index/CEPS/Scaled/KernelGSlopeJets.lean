import PLAStochastic.Index.CEPS.Scaled.KernelGJetGeometry
import PLAStochastic.Index.CEPS.Normal.MovingSlopeJetTransfer

/-! # Genuine spatial slope coefficients from finite mixed jets and finite node curves -/

noncomputable section
open Complex Set Metric MeasureTheory Filter Topology PowerSeries Asymptotics
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} (dom : CepsCanonDomain D θ v) (hθ : 0 < θ) (hD : 0 < D)

include hθ hD in
theorem cepsScaledSurrogateG_moving_slopes_taylorJets_eq_finite_model :
    ∃ r : ℝ, 0 < r ∧ ∀ {ρW : Measure ℝ} {fW f : ℝ → ℝ} {m : ℕ} {η : ℝ},
      IsStepLaw ρW fW D θ v → (∀ y, fW y = f (1 - y)) → (∀ x, x < 0 → f x = 0) →
      0 < η → CepsSobolevClass m η f → CepsSobolevClass m η fW → 2 * dom.c₀ ≤ η →
      ∫ x, |f x - cepsLambdaDensity x| ≤ r →
      ∀ N : ℕ, N + 2 ≤ m → ∀ (lam : ℝ) {z : ℂ}, 0 ≤ z.re →
      ∀ {a d t a' d' t' : ℂ → ℂ},
      AnalyticAt ℂ a 0 → AnalyticAt ℂ d 0 → AnalyticAt ℂ t 0 →
      AnalyticAt ℂ a' 0 → AnalyticAt ℂ d' 0 → AnalyticAt ℂ t' 0 →
      (fun b => a b - a' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) →
      (fun b => d b - d' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) →
      (fun b => t b - t' b) =O[𝓝 0] (fun b : ℂ => b ^ (N + 1)) →
      (∀ j ≤ N, coeff j (complexTaylorSeries
        (fun b => dslope (cepsScaledSurrogateG dom ρW N lam z b) (a b) (d b)) 0) =
        coeff j (complexTaylorSeries
          (fun b => dslope (cepsKernelGJetModel (cepsJet f) N lam z b) (a' b) (d' b)) 0)) ∧
      (∀ j ≤ N, coeff j (complexTaylorSeries
        (fun b => dslope (dslope (cepsScaledSurrogateG dom ρW N lam z b) (a b)) (d b) (t b)) 0) =
        coeff j (complexTaylorSeries
          (fun b => dslope (dslope (cepsKernelGJetModel (cepsJet f) N lam z b) (a' b)) (d' b) (t' b)) 0)) := by
  obtain ⟨r, hr, he⟩ := cepsScaledSurrogateG_finite_jet_geometry dom hθ hD
  refine ⟨r, hr, ?_⟩
  intro ρW fW f m η hW hfW hneg hη hf hfS hηc hclose N hN lam z hz a d t a' d' t'
    ha hd ht ha' hd' ht' hae hde hte
  let R : ℝ := 8 * (1 + ‖a 0‖ + ‖d 0‖ + ‖t 0‖ + ‖a' 0‖ + ‖d' 0‖ + ‖t' 0‖)
  have hR : 0 < R := by dsimp [R]; positivity
  have ha0 : a 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  have hd0 : d 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  have ht0 : t 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  have ha'0 : a' 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  have hd'0 : d' 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  have ht'0 : t' 0 ∈ ball (0 : ℂ) (R / 4) := by
    rw [mem_ball_zero_iff]; dsimp [R]
    linarith [norm_nonneg (a 0), norm_nonneg (d 0), norm_nonneg (t 0),
      norm_nonneg (a' 0), norm_nonneg (d' 0), norm_nonneg (t' 0)]
  obtain ⟨C, B, M, _, hB, _, hF, hG, hbound, herror⟩ :=
    he hW hfW hneg hη hf hfS hηc hclose N hN lam hz hR
  have hsmall : ball (0 : ℂ) (R / 4) ⊆ ball 0 (R / 2) := ball_subset_ball (by linarith)
  exact ⟨cepsNormal_moving_dslope_taylorJets_transfer hR hB hF hG hbound N herror
      ha hd ha' hd' (hsmall ha0) (hsmall hd0) (hsmall ha'0) (hsmall hd'0) hae hde,
    cepsNormal_moving_second_dslope_taylorJets_transfer hR hB hF hG hbound N herror
      ha hd ht ha' hd' ht' ha0 hd0 ht0 ha'0 hd'0 ht'0 hae hde hte⟩

end PGM
