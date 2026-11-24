import PLAStochastic.Index.GEP.Kernel.FarSlope.AnnulusBudget
import PLAStochastic.Index.GEP.Kernel.Marked.Pin.UniformDensity

/-! # The actual scalar bulk on a saddle annulus, uniformly in the input law -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def kernelSaddleAnnulus (δ w A : ℝ) : Set ℝ :=
  {a | |a-1| ≤ δ ∧ A ≤ w*|a-1|}

theorem measurableSet_kernelSaddleAnnulus (δ w A : ℝ) :
    MeasurableSet (kernelSaddleAnnulus δ w A) := by
  exact (measurableSet_le (show Measurable (fun a : ℝ => |a-1|) by fun_prop)
    measurable_const).inter
    (measurableSet_le measurable_const (show Measurable (fun a : ℝ => w*|a-1|) by fun_prop))

theorem kernelSaddleAnnulus_subset {δ w A : ℝ} (hδ : δ ≤ 1/2) :
    kernelSaddleAnnulus δ w A ⊆ Icc (1/2 : ℝ) 2 := by
  intro a ha
  have hh := abs_le.mp ha.1
  constructor <;> linarith

/-- Any legitimate density representative can be used simultaneously in the
annular AL estimate and the global TAIL estimate. -/
theorem kernel_regLaw_bulk_far_annulus (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ q K : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < q ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w x A : ℝ, 1 ≤ w → 0 ≤ x → ∀ y z : ℝ, |z-y|=w →
        (∫⁻ a in kernelSaddleAnnulus δ w A, ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)) ≤
            ENNReal.ofReal (K*w^16*Real.exp (θ/2*x-q*A)) := by
  obtain ⟨δ,q,k,K,hδ,hδhi,hq,hk,hK,hpair⟩ :=
    kernel_regLaw_full_marked_pin_far_window_of_density D θ vlo vhi hD hθ hvlo hv
  obtain ⟨Os,Ol,hOs,hOl,houter⟩ := kernel_regLaw_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  refine ⟨δ,q,2*(Os+Ol)*K*(3*(1+4/k)^4),hδ,hδhi,hq,by positivity,?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w x A hw hx y z hyz
  apply kernel_bulk_saddle_integral ν hf0 hw hk hK.le (show 0 ≤ Os+Ol by positivity)
    (kernelSaddleAnnulus_subset hδhi) ?_ ?_ (measurableSet_kernelSaddleAnnulus δ w A)
  · intro a ha
    have haa := kernelSaddleAnnulus_subset hδhi ha
    have ha0 : 0 < a := by linarith [haa.1]
    have ho := houter ν hν w a hw ha0
    by_cases halo : a ≤ 1/2
    · rw [if_pos halo] at ho
      have hw26 : w^2 ≤ w^6 := pow_le_pow_right₀ hw (by omega)
      have hm := mul_le_mul_of_nonneg_left hw26 hOs.le
      have hOlw : 0 ≤ Ol*w^6 := by positivity
      nlinarith
    · rw [if_neg halo] at ho
      have hOsw : 0 ≤ Os*w^6 := by positivity
      nlinarith
  · intro a ha l r M hlr hM
    exact hpair ν hν f hf hf0 hfD hfz hfe hνf a ha.1 w hw x hx A ha.2 y z hyz l r M hlr hM

end
end PGM
