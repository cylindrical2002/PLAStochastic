import PLAStochastic.Index.CEPS.Contour.Regularity
import PLAStochastic.Index.CEPS.Scaled.CanonSpatialTaylor

/-! # Contour-independent finite drift and spatial jets of the canonical factor -/

noncomputable section
open Complex Set Metric MeasureTheory Finset Filter Topology
open PGM.WienerHopf
namespace PGM

variable {D θ v : ℝ} {ρW : Measure ℝ} {fW : ℝ → ℝ}
variable (dom : CepsCanonDomain D θ v) (hW : IsStepLaw ρW fW D θ v)
  (hθ : 0 < θ) (hD : 0 < D)
variable {σ : ℝ} (hσ : 0 < σ) (hσc : σ ≤ dom.c₀)

include hW hθ hD in
theorem cepsCanonDriftCoeff_shrink_eq (j : ℕ) {q ζ : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < σ) :
    cepsCanonDriftCoeff (dom.shrink σ hσ hσc) ρW j q ζ =
      cepsCanonDriftCoeff dom ρW j q ζ := by
  have hμ : |(0 : ℝ)| < (dom.shrink σ hσ hσc).μ₀ := by
    simpa using (dom.shrink σ hσ hσc).μ₀_pos
  exact ((dom.canonL_mu_eventuallyEq_shrink hW hθ hD hσ hσc hq hζ hμ).iteratedDeriv_eq j).symm

include hW hθ hD in
theorem cepsCanonDriftTaylor_shrink_eq (N : ℕ) (μ : ℂ) {q ζ : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < σ) :
    cepsCanonDriftTaylor (dom.shrink σ hσ hσc) ρW N μ q ζ =
      cepsCanonDriftTaylor dom ρW N μ q ζ := by
  unfold cepsCanonDriftTaylor
  apply sum_congr rfl
  intro j _
  rw [cepsCanonDriftCoeff_shrink_eq dom hW hθ hD hσ hσc j hq hζ]

include hW hθ hD in
theorem cepsCanonDriftCoeff_spatial_shrink_eq (j l : ℕ) {q ζ : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < σ) :
    iteratedDeriv l (cepsCanonDriftCoeff (dom.shrink σ hσ hσc) ρW j q) ζ =
      iteratedDeriv l (cepsCanonDriftCoeff dom ρW j q) ζ := by
  apply Filter.EventuallyEq.iteratedDeriv_eq l
  exact Filter.eventually_of_mem ((isOpen_lt continuous_re continuous_const).mem_nhds hζ)
    fun _ hζ' => cepsCanonDriftCoeff_shrink_eq dom hW hθ hD hσ hσc j hq hζ'

include hW hθ hD in
theorem cepsCanonDriftCoeff_mixed_shrink_eq (j l k : ℕ) {q ζ : ℂ}
    (hq : ‖q‖ < (dom.shrink σ hσ hσc).q₀) (hζ : ζ.re < σ) :
    iteratedDeriv k (fun q' => iteratedDeriv l
      (cepsCanonDriftCoeff (dom.shrink σ hσ hσc) ρW j q') ζ) q =
    iteratedDeriv k (fun q' => iteratedDeriv l (cepsCanonDriftCoeff dom ρW j q') ζ) q := by
  apply Filter.EventuallyEq.iteratedDeriv_eq k
  exact Filter.eventually_of_mem ((isOpen_lt continuous_norm continuous_const).mem_nhds hq)
    fun _ hq' => cepsCanonDriftCoeff_spatial_shrink_eq dom hW hθ hD hσ hσc j l hq'.le hζ

include hW hθ hD in
theorem cepsCanonSpatialDriftCoeff_shrink_eq (j : ℕ) {q : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) :
    cepsCanonSpatialDriftCoeff (dom.shrink σ hσ hσc) ρW j q =
      cepsCanonSpatialDriftCoeff dom ρW j q := by
  simpa only [cepsCanonSpatialDriftCoeff, iteratedDeriv_one] using
    cepsCanonDriftCoeff_spatial_shrink_eq dom hW hθ hD hσ hσc (ζ := 0) j 1 hq
      (by simpa using hσ)

include hW hθ hD in
theorem cepsCanonSpatialDriftTaylor_shrink_eq (N : ℕ) (μ : ℂ) {q : ℂ}
    (hq : ‖q‖ ≤ (dom.shrink σ hσ hσc).q₀) :
    cepsCanonSpatialDriftTaylor (dom.shrink σ hσ hσc) ρW N μ q =
      cepsCanonSpatialDriftTaylor dom ρW N μ q := by
  unfold cepsCanonSpatialDriftTaylor
  apply sum_congr rfl
  intro j _
  rw [cepsCanonSpatialDriftCoeff_shrink_eq dom hW hθ hD hσ hσc j hq]

end PGM
