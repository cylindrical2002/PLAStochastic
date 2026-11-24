import PLAStochastic.Index.GEP.Kernel.LinearSurvival.SurvivalMoments
import PLAStochastic.Index.GEP.Kernel.LinearSurvival.KilledPotential

/-!
# A common killed potential for both signs of regular increments

All constants are chosen before the law, the slope, and the small drift.
The result discharges the mgf-tail premise of the potential inequality using
the original exponential-moment and variance class alone.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

theorem kernel_survival_class_potential (vlo vhi κ₃ B θ : ℝ)
    (hvlo : 0 < vlo) (hθ : 0 < θ) :
    ∃ C lam ρ₀ : ℝ, 1 ≤ C ∧ 0 < lam ∧ 0 < ρ₀ ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν →
      ∀ a : ℝ, 1 / 2 ≤ |a| → |a| ≤ 2 → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ ρ₀ →
      ∀ d : ℝ, 0 ≤ d →
        (∫ y, linearSurvivalPotential C lam (d - y) ∂(kernelSurvivalLaw ν a ρ : Measure ℝ)) ≤
          linearSurvivalPotential C lam d + ρ := by
  let lam := min (saTiltRadius vlo B θ / 2) (θ / 16)
  have hl : 0 < lam := lt_min (half_pos (saTiltRadius_pos hvlo hθ)) (by positivity)
  have hlr : lam ≤ saTiltRadius vlo B θ / 2 := min_le_left _ _
  have hlt : lam ≤ θ / 16 := min_le_right _ _
  let ρ₀ := min 1 (3 * vlo * lam / 64)
  have hρ₀ : 0 < ρ₀ := lt_min zero_lt_one (by positivity)
  let g := 3 * vlo * lam ^ 2 / 64
  have hg : 0 < g := by dsimp [g]; positivity
  let B' := Real.exp (θ / 4) * (Real.exp θ * max B 1)
  obtain ⟨R, hR, hRt⟩ := kernel_survival_exists_tail_cutoff
    (B := B') (show 0 < θ / 4 by positivity) hg
  let C := R + Real.exp (lam * R)
  have hC : 1 ≤ C := by
    have he : 1 ≤ Real.exp (lam * R) := Real.one_le_exp (mul_nonneg hl.le hR)
    dsimp [C]
    linarith
  refine ⟨C, lam, ρ₀, hC, hl, hρ₀, ?_⟩
  intro ν hν a ha₀ ha ρ hρ hρu d hd
  have hρ1 : |ρ| ≤ 1 := by
    rw [abs_of_nonneg hρ]
    exact hρu.trans (min_le_left _ _)
  have hρl : ρ ≤ 3 * vlo * lam / 64 := hρu.trans (min_le_right _ _)
  have htilt : |lam * a| ≤ saTiltRadius vlo B θ := by
    rw [abs_mul, abs_of_pos hl]
    have hm := mul_le_mul_of_nonneg_left ha hl.le
    linarith
  obtain ⟨habs, hB⟩ := hν.kernelSurvivalLaw_exp_abs hθ ha hρ1
  obtain ⟨htail, htailbound⟩ := kernel_survival_tail_le
    (show 0 < θ / 4 by positivity) (show lam ≤ θ / 4 / 4 by linarith) hR habs hB
  obtain ⟨he, helo⟩ := hν.kernelSurvivalLaw_mgf_lower (a := a) (ρ := ρ) (lam := lam) hvlo hθ htilt
  have ha2 : 1 / 4 ≤ a ^ 2 := by
    nlinarith [sq_nonneg (|a| - 1 / 2), sq_abs a]
  have hquad : g ≤ 3 / 8 * vlo * (lam * a) ^ 2 - lam * ρ := by
    have h1 := mul_le_mul_of_nonneg_left ha2
      (show 0 ≤ 3 / 8 * vlo * lam ^ 2 by positivity)
    have h2 := mul_le_mul_of_nonneg_left hρl hl.le
    dsimp [g]
    nlinarith
  have hmgf : 1 + g ≤ ∫ y : ℝ, Real.exp (lam * y) ∂(kernelSurvivalLaw ν a ρ : Measure ℝ) :=
    (show 1 + g ≤ Real.exp (3 / 8 * vlo * (lam * a) ^ 2 - lam * ρ) by
      linarith [Real.add_one_le_exp (3 / 8 * vlo * (lam * a) ^ 2 - lam * ρ)]).trans helo
  apply linearSurvivalPotential_step (kernelSurvivalLaw ν a ρ)
    (hν.kernelSurvivalLaw_integrable a ρ) hC hl.le hR (show R + Real.exp (lam * R) ≤ C from le_rfl)
    he htail (hν.kernelSurvivalLaw_mean a ρ) _ hd
  linarith [htailbound.trans hRt]

end
end PGM
