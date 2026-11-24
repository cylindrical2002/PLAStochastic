import PLAStochastic.Index.CEPS.Scaled.ComplexJetWeightedRoots
import PLAStochastic.Index.CEPS.BrownianCoeff.Root

/-! # Concrete finite-root directions on a common reference complex variance disc -/

noncomputable section
open Complex
namespace PGM

theorem cepsComplexVariance_reference_cone {v₀ : ℝ} {v : ℂ} (hv₀ : 0 < v₀)
    (hv : ‖v - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀) :
    v₀ / 2 ≤ v.re ∧ ‖v‖ ≤ 2 * v₀ ∧ |v.im| ≤ v.re / 8 := by
  have he := cepsBrownian_variance_bounds hv₀ hv
  refine ⟨he.1, he.2.2.1, ?_⟩
  have hi := (abs_im_le_norm (v - (v₀ : ℂ))).trans hv
  simp only [sub_im, ofReal_im, sub_zero] at hi
  change |v.im| ≤ v₀ / 16 at hi
  linarith [he.1]

/-- A single positive radius is fixed before all finite coordinate vectors, real drifts,
right-half-plane frequencies, and Newton iterations. No realization by a law is needed. -/
theorem cepsComplexCumulantRootModel_reference_sector (N : ℕ) {M v₀ : ℝ}
    (hM : 0 ≤ M) (hv₀ : 0 < v₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (p : ℕ → ℂ),
      (∀ j ≤ N, ‖p (cepsJetCode (.inl j))‖ ≤ M) →
      ‖p (cepsJetCode (.inl 0)) - (v₀ : ℂ)‖ ≤ cepsBrownianRadius v₀ →
      ∀ (lam : ℝ) (z b : ℂ), 0 ≤ z.re → ‖b‖ * (|lam| + Real.sqrt ‖z‖) ≤ δ →
      ∀ k : ℕ,
        (lam ≤ 0 → cepsFiniteRootPhaseLower (v₀ / 2) (2 * v₀) / 2 * (|lam| + Real.sqrt ‖z‖) ≤
          (cepsComplexCumulantRootModel p N lam z 1 k b * (1 + b * lam)).re) ∧
        (0 ≤ lam → (cepsComplexCumulantRootModel p N lam z (-1) k b * (1 + b * lam)).re ≤
          -(cepsFiniteRootPhaseLower (v₀ / 2) (2 * v₀) / 2 * (|lam| + Real.sqrt ‖z‖))) := by
  refine ⟨cepsFiniteWeightedRootRadius N M (v₀ / 2) (2 * v₀),
    cepsFiniteWeightedRootRadius_pos N hM (by positivity) (by positivity), ?_⟩
  intro p hp hv lam z b hz hb k
  obtain ⟨hlo, hhi, him⟩ := cepsComplexVariance_reference_cone hv₀ hv
  exact cepsComplexCumulantRootModel_weighted_individual_sector N hM (by positivity)
    hp hlo hhi him lam hz hb k

end PGM
