import PLAStochastic.Index.GEP.Kernel.FarSlope.LogWindow
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedAnnulus
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedInfinite
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedDirac

/-! # Weighted actual far-slope errors with a class-fixed output weight -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem kernel_weighted_far_bulk_series_eq (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (δ w s x y z a : ℝ) :
    (∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelWeightedFarBulkTailTerm ν f δ w s x y z a p)) =
      if δ ≤ |a-1| then
        (∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x y z a p)) else 0 := by
  by_cases ha : δ ≤ |a-1| <;> simp [kernelWeightedFarBulkTailTerm,ha]

/-- The physical output weight is fixed before the growing spatial window
and the requested error order. All far slopes and random times are included. -/
theorem kernel_regLaw_weighted_bulk_log_far (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ b : ℝ, 0 < b → ∀ B : ℕ,
    ∃ α K w0 : ℝ, 0 < α ∧ 0 < K ∧ 1 ≤ w0 ∧
      ∀ w, w0 ≤ w → 1 ≤ α*Real.log w ∧ α*Real.log w ≤ w/2 ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ ρ/w^2 →
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ x, x ∈ Icc (0 : ℝ) (b*Real.log w) →
      ∀ y z : ℝ, ((y=0 ∧ z=w) ∨ (y=w ∧ z=0)) →
        (∫⁻ a in kernelFarSlopes w (α*Real.log w), ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x y z a p)) ≤ ENNReal.ofReal (K/w^B) := by
  obtain ⟨δ,q,ρ1,K1,hδ,hδhi,hq,hρ1,hK1,ha⟩ :=
    kernel_regLaw_weighted_bulk_far_annulus D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρ2,lam,c,K2,hρ2,hlam,hc,hK2,hf⟩ :=
    kernel_regLaw_weighted_far_bulk_infinite D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  refine ⟨min ρ1 ρ2,lt_min hρ1 hρ2,fun b hb B => ?_⟩
  obtain ⟨α,w1,hα,hw1,hlog⟩ := kernel_log_cutoff_data (show 0 ≤ θ/2 by positivity) hq hb hδ 16 B
  obtain ⟨w2,hw2⟩ := eventually_atTop.mp (kernel_fixed_far_eventually hlam.le hc hb 16 B)
  refine ⟨α,K1+K2,max w1 w2,hα,by positivity,hw1.trans (le_max_left _ _),fun w hw => ?_⟩
  have hw1' := (le_max_left w1 w2).trans hw
  have hw2' := (le_max_right w1 w2).trans hw
  have hww : 1 ≤ w := hw1.trans hw1'
  have hw0 : 0 < w := by linarith
  have hA := hlog w hw1'
  refine ⟨hA.1,?_,fun s hs0 hs ν hν f hfm hf0 hfD hfz hfe hνf x hx y z hyz => ?_⟩
  · have hh := mul_le_mul_of_nonneg_right hδhi hw0.le
    linarith [hA.2.1]
  · have hyzw : |z-y|=w := by
      rcases hyz with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [abs_of_nonneg hw0.le]
    have hs1 := hs.trans (div_le_div_of_nonneg_right (min_le_left ρ1 ρ2) (sq_nonneg w))
    have hs2 := hs.trans (div_le_div_of_nonneg_right (min_le_right ρ1 ρ2) (sq_nonneg w))
    have h1 := ha ν hν f hfm hf0 hfD hfz hfe hνf w s x (α*Real.log w) hww hs0 hs1 hx.1 y z hyzw
    have h2 := hf ν hν f hfm hf0 hfD hfz hfe hνf w s x hww hs0 hs2 hx.1 y z hyz
    simp_rw [kernel_weighted_far_bulk_series_eq] at h2
    have hh := (kernel_lintegral_far_cover
      (fun a => ∑' p : ℕ × ℕ × ℕ, ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x y z a p))
      δ w (α*Real.log w)).trans (add_le_add h1 h2)
    apply hh.trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have e1 := mul_le_mul_of_nonneg_left (hA.2.2 x hx.2) hK1.le
    have e2 := mul_le_mul_of_nonneg_left ((hw2 w hw2').2 x hx.2) hK2.le
    have he : (K1+K2)/w^B = K1*(1/w^B)+K2*(1/w^B) := by ring
    rw [he]
    nlinarith

theorem kernel_regLaw_weighted_dirac_log_far (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ b : ℝ, 0 < b → ∀ B : ℕ,
    ∃ K w0 : ℝ, 0 < K ∧ 1 ≤ w0 ∧
      ∀ w, w0 ≤ w → ∀ s : ℝ, 0 ≤ s → s ≤ ρ/w^2 →
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
      ∀ x, x ∈ Ioc (0 : ℝ) (b*Real.log w) →
        Summable (kernelWeightedDiracTailTerm ν f w s x) ∧
        (∑' m, kernelWeightedDiracTailTerm ν f w s x m) ≤ K/w^B := by
  obtain ⟨ρ,c,K,hρ,hc,hK,hdirac⟩ := kernel_regLaw_weighted_dirac_far_infinite D θ vlo vhi hD hθ hvlo hv
  refine ⟨ρ,hρ,fun b hb B => ?_⟩
  obtain ⟨w1,hw1⟩ := eventually_atTop.mp (kernel_fixed_far_eventually (lam := 0) le_rfl hc hb 16 B)
  obtain ⟨w2,hw2⟩ := eventually_atTop.mp (kernel_log_window_eventually hb)
  refine ⟨K,max 1 (max w1 w2),hK,le_max_left _ _,fun w hw s hs0 hs ν hν f hf hf0 hfD hfz hfe x hx => ?_⟩
  have hww : 1 ≤ w := (le_max_left _ _).trans hw
  have h1 := hw1 w ((le_max_left _ _).trans ((le_max_right _ _).trans hw))
  have h2 := hw2 w ((le_max_right _ _).trans ((le_max_right _ _).trans hw))
  have hsmall : 2*x ≤ w+1 := by linarith [hx.2,h2.2]
  obtain ⟨hS,hB⟩ := hdirac ν hν f hf hf0 hfD hfz hfe w s x hww hs0 hs hx.1 hsmall
  refine ⟨hS,hB.trans ?_⟩
  have hh := mul_le_mul_of_nonneg_left (h1.2 x hx.2) hK.le
  simpa only [zero_mul,zero_sub,mul_one_div,mul_assoc,neg_mul] using hh

end
end PGM
