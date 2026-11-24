import PLAStochastic.Index.CEPS.Final.GlueConstruct
import PLAStochastic.Index.CEPS.Final.ScaleCoeff

/-! # Marked endpoint and marked discount scale coefficients on the strip

The outer strip budgets of the complex marked endpoint and marked discount (package S) are
stated as hypotheses in their proved forms; their scale coefficients are jointly analytic in
`(q, z)` with stretched-exponential, respectively polynomial, frequency bounds.
-/

noncomputable section
open Complex Metric Set Filter Topology
namespace PGM

/-- The strip budget of the complex marked endpoint, as proved in `Strip/`. -/
def CepsStripEndpointBudget (d N : ℕ) : Prop :=
  ∀ M vlo vhi : ℝ, 0 ≤ M → 0 < vlo → vlo ≤ vhi →
    ∃ δ δb K c : ℝ, ∃ e : ℕ, 0 < δ ∧ 0 < δb ∧ 0 < c ∧
      ∀ q : Fin d → ℂ, ‖q‖ ≤ M → vlo ≤ (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re →
        ‖cepsComplexJetPad d q (cepsJetCode (.inl 0))‖ ≤ vhi →
        |(cepsComplexJetPad d q (cepsJetCode (.inl 0))).im| ≤
          (cepsComplexJetPad d q (cepsJetCode (.inl 0))).re / 8 →
        ∀ z b : ℂ, -δ ≤ z.re → ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb →
          AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
              cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d v.1) N v.2.1 v.2.2) (q, z, b) ∧
          ‖cepsComplexKernelMarkedEndpointJetModel (cepsComplexJetPad d q) N z b‖ ≤
            K * (1 + Real.sqrt ‖z‖) ^ e * Real.exp (-c * Real.sqrt ‖z‖)

/-- The budget of the complex marked discount, as proved in `Strip/`. -/
def CepsDiscountBudget (d N : ℕ) : Prop :=
  ∀ M : ℝ, 0 ≤ M → ∃ δb K : ℝ, ∃ e : ℕ, 0 < δb ∧ ∀ q : Fin d → ℂ, ‖q‖ ≤ M → ∀ z b : ℂ,
    ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb →
      AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ =>
          -cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d v.1) N 0 v.2.1 v.2.2
            (v.2.2 * v.2.1)) (q, z, b) ∧
      ‖-cepsComplexCumulantQuotientSpatialUnit (cepsComplexJetPad d q) N 0 z b (b * z)‖ ≤
        K * (1 + ‖z‖) ^ e

theorem one_add_sqrt_le (t : ℝ) (ht : 0 ≤ t) : 1 + Real.sqrt t ≤ 2 * (1 + t) := by
  nlinarith [Real.sq_sqrt ht, Real.sqrt_nonneg t]

/-- Scale coefficients of a family analytic on the frequency-dependent scale disc
`‖b‖ (1 + √‖z‖) ≤ δb`. -/
theorem cepsScaleCoeff_of_sqrt_family {d : ℕ} {F : (Fin d → ℂ) → ℂ → ℂ → ℂ} {q : Fin d → ℂ}
    {z : ℂ} {δb B : ℝ} (hδb : 0 < δb)
    (hF : ∀ b : ℂ, ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb →
      AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ × ℂ => F v.1 v.2.1 v.2.2) (q, z, b) ∧ ‖F q z b‖ ≤ B)
    (n : ℕ) :
    AnalyticAt ℂ (fun v : (Fin d → ℂ) × ℂ => cepsScaleCoeff n (F v.1 v.2)) (q, z) ∧
    ‖cepsScaleCoeff n (F q z)‖ ≤ B * (2 * (1 + Real.sqrt ‖z‖) / δb) ^ n := by
  have hX : 0 < 1 + Real.sqrt ‖z‖ := by positivity
  have hρ : 0 < δb / (1 + Real.sqrt ‖z‖) := div_pos hδb hX
  have hmem : ∀ b : ℂ, ‖b‖ < δb / (1 + Real.sqrt ‖z‖) → ‖b‖ * (1 + Real.sqrt ‖z‖) ≤ δb :=
    fun b hb => ((lt_div_iff₀ hX).mp hb).le
  have h := cepsScaleCoeff_of_family hρ (fun b hb => (hF b (hmem b hb)).1)
    (fun b hb => (hF b (hmem b hb)).2) n
  refine ⟨h.1, h.2.trans_eq ?_⟩
  congr 2
  field_simp

end PGM
