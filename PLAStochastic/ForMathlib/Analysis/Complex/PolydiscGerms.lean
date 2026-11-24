import PLAStochastic.ForMathlib.Analysis.Complex.PartialDeriv

/-! # Concrete common polydiscs from genuine neighborhood germs -/

noncomputable section
open Complex Set Metric Filter Topology
namespace PGM

theorem exists_polydisc_of_eventually {b z : ℂ} {P : ℂ × ℂ → Prop}
    (hP : ∀ᶠ x in 𝓝 (b, z), P x) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ ball b B ×ˢ ball z B, P x := by
  obtain ⟨B, hB, hball⟩ := Metric.mem_nhds_iff.mp hP
  refine ⟨B, hB, fun x hx => hball ?_⟩
  simpa only [mem_ball, Prod.dist_eq, max_lt_iff] using
    (show dist x.1 b < B ∧ dist x.2 z < B from hx)

theorem exists_polydisc_of_eventually_le {b z : ℂ} {P : ℂ × ℂ → Prop}
    {B₀ : ℝ} (hB₀ : 0 < B₀) (hP : ∀ᶠ x in 𝓝 (b, z), P x) :
    ∃ B : ℝ, 0 < B ∧ B ≤ B₀ ∧ ∀ x ∈ ball b B ×ˢ ball z B, P x := by
  obtain ⟨C, hC, hrect⟩ := exists_polydisc_of_eventually hP
  exact ⟨min C B₀, lt_min hC hB₀, min_le_right _ _, fun x hx =>
    hrect x ⟨ball_subset_ball (min_le_left _ _) hx.1, ball_subset_ball (min_le_left _ _) hx.2⟩⟩

theorem exists_polydisc_ne_zero {b z : ℂ} {F : ℂ × ℂ → ℂ} {B₀ : ℝ}
    (hB₀ : 0 < B₀) (hF : ContinuousAt F (b, z)) (hF0 : F (b, z) ≠ 0) :
    ∃ B : ℝ, 0 < B ∧ B ≤ B₀ ∧ ∀ x ∈ ball b B ×ˢ ball z B, F x ≠ 0 :=
  exists_polydisc_of_eventually_le hB₀ (hF.eventually_ne hF0)

end PGM
