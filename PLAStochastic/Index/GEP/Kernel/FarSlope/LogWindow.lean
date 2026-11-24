import PLAStochastic.Index.GEP.Kernel.FarSlope.LogCutoff
import PLAStochastic.Index.GEP.Kernel.FarSlope.Infinite
import PLAStochastic.Index.GEP.Kernel.FarSlope.Dirac

/-! # Arbitrarily small actual far-slope errors on logarithmic spatial windows -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

def kernelFarSlopes (w A : ℝ) : Set ℝ := {a | 0 < a ∧ A ≤ w*|a-1|}

theorem kernel_lintegral_far_cover (F : ℝ → ℝ≥0∞) (δ w A : ℝ) :
    (∫⁻ a in kernelFarSlopes w A, F a) ≤
      (∫⁻ a in kernelSaddleAnnulus δ w A, F a) +
      ∫⁻ a in Ioi (0 : ℝ), if δ ≤ |a-1| then F a else 0 := by
  have hS : kernelFarSlopes w A ⊆ kernelSaddleAnnulus δ w A ∪
      (Ioi (0 : ℝ) ∩ {a : ℝ | δ ≤ |a-1|}) := by
    intro a ha
    by_cases hδ : |a-1| ≤ δ
    · exact Or.inl ⟨hδ,ha.2⟩
    · exact Or.inr ⟨ha.1,(not_le.mp hδ).le⟩
  have hm : MeasurableSet {a : ℝ | δ ≤ |a-1|} :=
    measurableSet_le measurable_const (by fun_prop)
  have he : (∫⁻ a in Ioi (0 : ℝ), if δ ≤ |a-1| then F a else 0) =
      ∫⁻ a in Ioi (0 : ℝ) ∩ {a : ℝ | δ ≤ |a-1|}, F a := by
    change (∫⁻ a in Ioi (0 : ℝ), {a : ℝ | δ ≤ |a-1|}.indicator F a) = _
    rw [lintegral_indicator hm,Measure.restrict_restrict hm,inter_comm]
  rw [he]
  exact (lintegral_mono_set hS).trans (lintegral_union_le _ _ _)

theorem kernel_far_bulk_series_eq (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (δ w x y z a : ℝ) :
    (∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelFarBulkTailTerm ν f δ w x y z a p)) =
      if δ ≤ |a-1| then
        (∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)) else 0 := by
  by_cases ha : δ ≤ |a-1| <;> simp [kernelFarBulkTailTerm,ha]

/-- The actual scalar bulk away from a logarithmic near-critical window is
smaller than any chosen inverse width power, uniformly over the law class. -/
theorem kernel_regLaw_bulk_log_far (D θ vlo vhi b : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (hb : 0 < b) (B : ℕ) :
    ∃ α K w0 : ℝ, 0 < α ∧ 0 < K ∧ 1 ≤ w0 ∧
      ∀ w, w0 ≤ w → 1 ≤ α*Real.log w ∧ α*Real.log w ≤ w/2 ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ x, x ∈ Icc (0 : ℝ) (b*Real.log w) →
      ∀ y z : ℝ, ((y=0 ∧ z=w) ∨ (y=w ∧ z=0)) →
        (∫⁻ a in kernelFarSlopes w (α*Real.log w), ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p)) ≤ ENNReal.ofReal (K/w^B) := by
  obtain ⟨δ,q,K1,hδ,hδhi,hq,hK1,ha⟩ := kernel_regLaw_bulk_far_annulus D θ vlo vhi hD hθ hvlo hv
  obtain ⟨lam,c,K2,hlam,hc,hK2,hf⟩ := kernel_regLaw_far_bulk_infinite D θ vlo vhi δ
    hD hθ hvlo hv hδ hδhi
  obtain ⟨α,w1,hα,hw1,hlog⟩ := kernel_log_cutoff_data (show 0 ≤ θ/2 by positivity) hq hb hδ 16 B
  obtain ⟨w2,hw2⟩ := eventually_atTop.mp (kernel_fixed_far_eventually hlam.le hc hb 16 B)
  refine ⟨α,K1+K2,max w1 w2,hα,by positivity,hw1.trans (le_max_left _ _),fun w hw => ?_⟩
  have hw1' := (le_max_left w1 w2).trans hw
  have hw2' := (le_max_right w1 w2).trans hw
  have hww : 1 ≤ w := hw1.trans hw1'
  have hw0 : 0 < w := by linarith
  have hA := hlog w hw1'
  refine ⟨hA.1,?_,fun ν hν f hfm hf0 hfD hfz hfe hνf x hx y z hyz => ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hδhi hw0.le
    linarith [hA.2.1]
  · have hyzw : |z-y|=w := by
      rcases hyz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [abs_of_nonneg hw0.le]
    have h1 := ha ν hν f hfm hf0 hfD hfz hfe hνf w x (α*Real.log w) hww hx.1 y z hyzw
    have h2 := hf ν hν f hfm hf0 hfD hfz hfe hνf w x hww hx.1 y z hyz
    simp_rw [kernel_far_bulk_series_eq] at h2
    have hh := (kernel_lintegral_far_cover
      (fun a => ∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelBulkTailTerm ν f w x y z a p))
      δ w (α*Real.log w)).trans (add_le_add h1 h2)
    apply hh.trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e1 := mul_le_mul_of_nonneg_left (hA.2.2 x hx.2) hK1.le
    have e2 := mul_le_mul_of_nonneg_left ((hw2 w hw2').2 x hx.2) hK2.le
    have he : (K1+K2)/w^B = K1*(1/w^B)+K2*(1/w^B) := by ring
    rw [he]
    nlinarith

end
end PGM
