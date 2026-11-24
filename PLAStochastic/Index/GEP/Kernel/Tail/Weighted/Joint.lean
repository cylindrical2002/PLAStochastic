import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Infinite
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.DiracTail

/-! # One density and one fixed output-weight scale for both genuine tail terms -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem kernelPhysicalOuterWeight_zero (ν : ProbabilityMeasure ℝ) (w a : ℝ) :
    kernelPhysicalOuterWeight ν w 0 a = kernelOuterWeight ν w a := by
  simp only [kernelPhysicalOuterWeight, kernelOuterWeight,
    kernelPhysicalSurv_zero_weight measurableSet_Icc]

theorem kernelWeightedPairTailSum_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w a t y z : ℝ) (L R M : ℕ) :
    kernelWeightedPairTailSum ν f w 0 a t y z L R M = kernelPairTailSum ν f w a t y z L R M := by
  simp only [kernelWeightedPairTailSum, kernelPairTailSum, zero_mul, zero_div, Real.exp_zero, one_mul]

theorem kernelWeightedBulkTailTerm_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w t y z a : ℝ) (p : ℕ × ℕ × ℕ) :
    kernelWeightedBulkTailTerm ν f w 0 t y z a p = kernelBulkTailTerm ν f w t y z a p := by
  simp only [kernelWeightedBulkTailTerm, kernelBulkTailTerm, zero_mul, zero_div, Real.exp_zero,
    one_mul, kernelPhysicalOuterWeight_zero]

theorem kernelWeightedDiracTailTerm_zero (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w t : ℝ) (m : ℕ) :
    kernelWeightedDiracTailTerm ν f w 0 t m = kernelDiracTailTerm ν f w t m := by
  simp only [kernelWeightedDiracTailTerm, kernelDiracTailTerm, zero_mul, zero_div, Real.exp_zero,
    one_mul, kernelPhysicalOuterWeight_zero]

/-- The genuine non-Dirac bulk and genuine Dirac contribution share one
pointwise density representative and one physical-output-weight scale. The
fixed exponent 16 and the scale `ρ` precede every arbitrary input exponent;
only the eventual smallness threshold `σ` depends on that input exponent. -/
theorem kernel_regLaw_joint_weighted_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℝ, 0 < ζ → ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → s ≤ σ → 0 < t →
          (∀ y z : ℝ, (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
            ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s t y z a p)) ≤
              ENNReal.ofReal (K * w ^ 16 * Real.exp (ζ * t))) ∧
          Summable (kernelWeightedDiracTailTerm ν f w s t) ∧
          (∑' m, kernelWeightedDiracTailTerm ν f w s t m) ≤ K * w ^ 16 * Real.exp (ζ * t) := by
  obtain ⟨ρb, hρb, hbulk⟩ := kernel_regLaw_weighted_bulk_tail_infinite D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρd, hρd, hdirac⟩ := kernel_regLaw_weighted_dirac_tail_infinite D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρb ρd, lt_min hρb hρd, ?_⟩
  intro ζ hζ
  obtain ⟨σb, Kb, hσb, hKb, hb⟩ := hbulk ζ hζ
  obtain ⟨σd, Kd, hσd, hKd, hd⟩ := hdirac ζ hζ
  refine ⟨min σb σd, Kb + Kd, lt_min hσb hσd, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hb⟩ := hb ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w s t hw hs0 hs hsσ ht
  have hsb : s ≤ ρb / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg w))
  have hsd : s ≤ ρd / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg w))
  have hσb' : s ≤ σb := hsσ.trans (min_le_left _ _)
  have hσd' : s ≤ σd := hsσ.trans (min_le_right _ _)
  obtain ⟨hds, hdb⟩ := hd ν hν f hf hf0 hfD hfz hfe w s t hw hs0 hsd hσd' ht
  refine ⟨?_, hds, ?_⟩
  · intro y z
    apply (hb w s t hw hs0 hsb hσb' ht.le y z).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
    linarith
  · apply hdb.trans
    gcongr
    linarith

end
end PGM
