import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Bulk

/-! # Full positive-slope integrals of the genuine finite scalar IF budgets -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 1400000

/-- Every finite collection of actual marked bridges, including zero random
sides, is absolutely integrable over all positive slopes with the same fixed
width power 16. The arbitrary input weight is chosen only after that power. -/
theorem kernel_regLaw_weighted_bulk_tail_integral (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ζ : ℝ, 0 < ζ → ∃ σ K : ℝ, 0 < σ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x = 0) ∧ (∀ x, f x ≤ D * Real.exp (-θ * x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → s ≤ σ → 0 ≤ t → ∀ y z : ℝ, ∀ L R M : ℕ,
          IntegrableOn (fun a => kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z L R M) (Ioi 0) ∧
          (∫ a in Ioi (0 : ℝ), kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z L R M) ≤
            K * w ^ 16 * Real.exp (ζ * t) := by
  obtain ⟨ρ, hρ, hbudget⟩ := kernel_regLaw_weighted_bulk_tail_budget D θ vlo vhi hD hθ hvlo hv
  refine ⟨ρ, hρ, ?_⟩
  intro ζ hζ
  obtain ⟨σ, Ks, Kl, hσ, hKs, hKl, hdata⟩ := hbudget ζ hζ
  refine ⟨σ, Ks / 2 + 2 * Kl, hσ, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f, hf, hf0, hfD, hfz, hfe, hνf, hb⟩ := hdata ν hν
  refine ⟨f, hf, hf0, hfD, hfz, hfe, hνf, ?_⟩
  intro w s t hw hs0 hs hsσ ht y z L R M
  let F := fun a => kernelPhysicalOuterWeight ν w s a * kernelWeightedPairTailSum ν f w s a t y z L R M
  let Cs := Ks * w ^ 16 * Real.exp (ζ * t)
  let Cl := Kl * w ^ 16
  have hCs : 0 ≤ Cs := by positivity
  have hCl : 0 ≤ Cl := by positivity
  have hF (a : ℝ) : 0 ≤ F a := mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s a)
    (kernelWeightedPairTailSum_nonneg ν hf0 (by linarith) s a t y z L R M)
  have hFm : Measurable F := (measurable_kernelPhysicalOuterWeight ν w s).mul
    (measurable_kernelWeightedPairTailSum ν hf w s t y z L R M)
  have hsmall (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1 / 2)) : F a ≤ Cs := by
    have hh := hb w s t hw hs0 hs hsσ ht y z L R M a ha.1
    simpa only [if_pos ha.2] using hh
  have hlarge (a : ℝ) (ha : a ∈ Ioi (1 / 2 : ℝ)) : F a ≤ Cl * a⁻¹ ^ 2 := by
    have ha' : (1 / 2 : ℝ) < a := ha
    have hh := hb w s t hw hs0 hs hsσ ht y z L R M a (by linarith)
    simpa only [if_neg (not_le.mpr ha')] using hh
  have hIs : IntegrableOn F (Ioc (0 : ℝ) (1 / 2)) := by
    refine (integrableOn_const (s := Ioc (0 : ℝ) (1 / 2)) (C := Cs) (by simp)).mono'
      hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF a)] using hsmall a ha
  have hIl : IntegrableOn F (Ioi (1 / 2 : ℝ)) := by
    refine (kernel_integrable_inverse_square_half.const_mul Cl).mono' hFm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF a)] using hlarge a ha
  have hsplit : Ioc (0 : ℝ) (1 / 2) ∪ Ioi (1 / 2) = Ioi 0 := by
    ext a
    simp only [mem_union, mem_Ioc, mem_Ioi]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro ha
      by_cases hh : a ≤ 1 / 2
      · exact Or.inl ⟨ha, hh⟩
      · exact Or.inr (not_le.mp hh)
  have hdis : Disjoint (Ioc (0 : ℝ) (1 / 2)) (Ioi (1 / 2)) := by
    apply disjoint_left.mpr
    intro a ha hb
    exact (not_lt.mpr ha.2) hb
  have hIf : IntegrableOn F (Ioi (0 : ℝ)) := by rw [← hsplit]; exact hIs.union hIl
  refine ⟨hIf, ?_⟩
  change (∫ a in Ioi (0 : ℝ), F a) ≤ _
  rw [← hsplit, setIntegral_union hdis measurableSet_Ioi hIs hIl]
  have hsi : (∫ a in Ioc (0 : ℝ) (1 / 2), F a) ≤ Cs / 2 := by
    have hh := integral_mono_ae hIs (integrableOn_const (C := Cs) (by simp))
      (show ∀ᵐ a ∂volume.restrict (Ioc (0 : ℝ) (1 / 2)), F a ≤ Cs by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
        exact hsmall a ha)
    apply hh.trans_eq
    simp only [integral_const, smul_eq_mul]
    norm_num
    ring
  have hli : (∫ a in Ioi (1 / 2 : ℝ), F a) ≤ 2 * Cl := by
    have hh := integral_mono_ae hIl (kernel_integrable_inverse_square_half.const_mul Cl)
      (show ∀ᵐ a ∂volume.restrict (Ioi (1 / 2 : ℝ)), F a ≤ Cl * a⁻¹ ^ 2 by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
        exact hlarge a ha)
    apply hh.trans_eq
    rw [integral_const_mul, kernel_integral_inverse_square_half]
    ring
  have he : 1 ≤ Real.exp (ζ * t) := Real.one_le_exp_iff.mpr (mul_nonneg hζ.le ht)
  have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ 2 * Cl by positivity)
  dsimp [Cs, Cl] at hsi hli hh ⊢
  nlinarith

end
end PGM
