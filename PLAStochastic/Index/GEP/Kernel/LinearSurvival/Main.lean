import PLAStochastic.Index.GEP.Kernel.LinearSurvival.Sharp
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.AffineWalk
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.SurvivalPotential
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.SurvivalSumDensity
import PLAStochastic.Index.GEP.Universality.ClassProperties

/-!
# Class-uniform sharp linear survival for both signs

The actual iid gap law from `RegLaw` supplies every probability input. The
constant is selected before the law, signed slope, drift, starting height, and
horizon. No fluctuation identity or additional survival assumption is used.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Sharp linear survival on the transformed iid probability space. -/
theorem linearSurvival_regLaw_transformed (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ K : ℝ, 0 < K ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, 1 / 2 ≤ |a| → |a| ≤ 2 → ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
        (iidLaw (kernelSurvivalLaw ν a ρ)).real (linearSurvivalStay δ n) ≤
          K * (1 + δ) * ((Real.sqrt n)⁻¹ + ρ) := by
  obtain ⟨C, lam, ρ₀, hC, hlam, hρ₀, hpot⟩ :=
    kernel_survival_class_potential vlo vhi (regBeta D θ vlo * Real.sqrt vhi ^ 3)
      (2 * D / θ) (θ / 2) hvlo (by positivity)
  obtain ⟨L, hL, hconc⟩ := kernel_survival_sum_concentration D θ vlo vhi hD hθ hvlo hv
  obtain ⟨K₀, hK₀, hsharp⟩ := linearSurvival_sharp_of_inputs hC hlam.le hL
    (show 1 ≤ (2 : ℕ) by norm_num)
  let K := max K₀ ρ₀⁻¹
  have hK : 0 < K := hK₀.trans_le (le_max_left _ _)
  refine ⟨K, hK, ?_⟩
  intro ν hν a ha₀ ha ρ hρ δ hδ n hn
  have hfac : 0 ≤ (1 + δ) * ((Real.sqrt n)⁻¹ + ρ) := by positivity
  by_cases hsmall : ρ ≤ ρ₀
  · have hh := hsharp (kernelSurvivalLaw ν a ρ)
      ((hν.univClass hθ hvlo).kernelSurvivalLaw_integrable a ρ) ρ hρ
      (hpot ν (hν.univClass hθ hvlo) a ha₀ ha ρ hρ hsmall)
      (hconc ν hν a ha₀ ρ) δ hδ n hn
    apply hh.trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (le_max_left K₀ ρ₀⁻¹) hfac
  · have hρbig : ρ₀ ≤ ρ := (lt_of_not_ge hsmall).le
    have hKr : 1 ≤ K * ρ := by
      have hh := mul_le_mul_of_nonneg_right (le_max_right K₀ ρ₀⁻¹) hρ
      have hh' := mul_le_mul_of_nonneg_left hρbig (inv_nonneg.2 hρ₀.le)
      rw [inv_mul_cancel₀ hρ₀.ne'] at hh'
      exact hh'.trans hh
    apply (measureReal_le_one : (iidLaw (kernelSurvivalLaw ν a ρ)).real
      (linearSurvivalStay δ n) ≤ 1).trans
    have hroot := inv_nonneg.2 (Real.sqrt_nonneg (n : ℝ))
    have h1 : ρ ≤ (1 + δ) * ((Real.sqrt n)⁻¹ + ρ) := by
      nlinarith [mul_nonneg hδ (add_nonneg hroot hρ)]
    have h2 := mul_le_mul_of_nonneg_left h1 hK.le
    nlinarith

/-- **Sharp linear survival (LS) for the original regular gap class.**
The signed slope includes both centered directions and the full kernel range.
The event includes time zero, which is automatic for `δ ≥ 0`. -/
theorem linearSurvival_regLaw (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ K : ℝ, 0 < K ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ a : ℝ, 1 / 2 ≤ |a| → |a| ≤ 2 → ∀ ρ : ℝ, 0 ≤ ρ →
      ∀ δ : ℝ, 0 ≤ δ → ∀ n : ℕ, 1 ≤ n →
        (iidLaw ν).real {g | ∀ j ≤ n, a * (gapKeys g j - j) ≤ δ + ρ * j} ≤
          K * (1 + δ) * ((Real.sqrt n)⁻¹ + ρ) := by
  obtain ⟨K, hK, hb⟩ := linearSurvival_regLaw_transformed D θ vlo vhi hD hθ hvlo hv
  refine ⟨K, hK, ?_⟩
  intro ν hν a ha₀ ha ρ hρ δ hδ n hn
  rw [← linearSurvival_affine_probability]
  exact hb ν hν a ha₀ ha ρ hρ δ hδ n hn

end
end PGM
