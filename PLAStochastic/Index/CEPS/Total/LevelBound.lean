import PLAStochastic.Index.CEPS.Total.LevelClass

/-! # A uniform finite level bound for a Sobolev input class -/

noncomputable section
open MeasureTheory
namespace PGM

/-- Every fixed input class meets only finitely many canonical levels. -/
theorem cepsInputClass_levelIndex_bound {D θ vlo vhi η : ℝ} {m : ℕ}
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hη : 0 < η) (hm : cepsLevelOrder ≤ m) :
    ∃ N : ℕ, ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η 1 ν →
      CepsLevel (cepsLevelIndex ν) ν ∧ cepsLevelIndex ν ≤ N := by
  set X := max (max (max D θ⁻¹) (max vlo⁻¹ vhi))
    (max η⁻¹ (Real.exp η * (cepsSobolev m η cepsLambdaDensity + 1)))
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt X (by norm_num : (1 : ℝ) < 2)
  have hXN : X ≤ cepsLevelScale N := hN.le
  have hrate : ∀ a : ℝ, 0 < a → a⁻¹ ≤ X → cepsLevelRate N ≤ a := by
    intro a ha hax
    have hx := hax.trans hXN
    unfold cepsLevelScale at hx
    unfold cepsLevelRate
    rw [inv_le_comm₀ (by positivity) ha]
    exact hx
  have h1 : D ≤ cepsLevelScale N :=
    ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _))).trans hXN
  have h2 : cepsLevelRate N ≤ θ := hrate θ hθ
    ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have h3 : cepsLevelRate N ≤ vlo := hrate vlo hvlo
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have h4 : vhi ≤ cepsLevelScale N :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))).trans hXN
  have h5 : cepsLevelRate N ≤ η := hrate η hη
    ((le_max_left _ _).trans (le_max_right _ _))
  have h6 : Real.exp η * (cepsSobolev m η cepsLambdaDensity + 1) ≤ cepsLevelScale N :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hXN
  exact ⟨N, fun ν hν => cepsLevelIndex_spec
    (cepsInputClass_level hm hη h1 h2 h3 h4 h5 h6 hν)⟩

end PGM
