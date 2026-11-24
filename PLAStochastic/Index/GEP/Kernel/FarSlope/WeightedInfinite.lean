import PLAStochastic.Index.GEP.Kernel.FarSlope.Infinite
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedFixed
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.Infinite

/-! # Infinite physical-weight IF outside the fixed saddle neighborhood -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option maxHeartbeats 1400000

def kernelWeightedFarPairTailSum (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (δ w s a t y z : ℝ)
    (L R M : ℕ) : ℝ :=
  if δ ≤ |a - 1| then kernelWeightedPairTailSum ν f w s a t y z L R M else 0

theorem kernelWeightedFarPairTailSum_nonneg (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (δ s a t y z : ℝ) (L R M : ℕ) :
    0 ≤ kernelWeightedFarPairTailSum ν f δ w s a t y z L R M := by
  unfold kernelWeightedFarPairTailSum
  split_ifs
  · exact kernelWeightedPairTailSum_nonneg ν hf0 hw s a t y z L R M
  · rfl

theorem measurable_kernelWeightedFarPairTailSum (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf : Measurable f) (δ w s t y z : ℝ) (L R M : ℕ) :
    Measurable (fun a => kernelWeightedFarPairTailSum ν f δ w s a t y z L R M) :=
  Measurable.ite (measurableSet_le measurable_const ((measurable_id.sub measurable_const).abs))
    (measurable_kernelWeightedPairTailSum ν hf w s t y z L R M) measurable_const

/-- Every finite actual random-length rectangle, with both exterior Green
products, is exponentially small outside the fixed saddle neighborhood. -/
theorem kernel_regLaw_weighted_far_bulk_budget (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ ρ lam c K : ℝ, 0 < ρ ∧ 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ L R M : ℕ, ∀ a : ℝ, 0 < a →
        kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M ≤
          (if a ≤ 1 / 2 then K else K * a⁻¹ ^ 2) * w ^ 16 * Real.exp (lam * t - c * w) := by
  obtain ⟨ρp, lam, c, B, hρp, hlam, hc, hB, hpair⟩ :=
    kernel_regLaw_weighted_full_pair_far_width D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  obtain ⟨ρo, Os, Ol, hρo, hOs, hOl, houter⟩ := kernel_regLaw_physical_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  let K := (Os + Ol) * B * (3 * (1 + 1 / c) ^ 4)
  have hK : 0 < K := by positivity
  refine ⟨min ρp ρo, lam, c, K, lt_min hρp hρo, hlam, hc, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz L R M a ha
  have hw0 : 0 ≤ w := by linarith
  have hso : s ≤ ρo / w ^ 2 := hs.trans (div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg w))
  have hsp : s ≤ ρp := by
    have hh := (le_div_iff₀ (show 0 < w ^ 2 by nlinarith)).mp hs
    have hm := min_le_left ρp ρo
    have hw2 := mul_le_mul_of_nonneg_left (show 1 ≤ w ^ 2 by nlinarith) hs0
    nlinarith
  unfold kernelWeightedFarPairTailSum
  by_cases haway : δ ≤ |a - 1|
  · rw [if_pos haway]
    have hp (l r m : ℕ) : Real.exp (s * ((l : ℝ) + r + (m + 1) + 1) / a) *
        (kernelMarkedFullDens (Icc 0 w) ν f 1 a t l r y z *
        krDens (Icc 0 w) ν f 1 a (m + 1) z y) ≤
        ((if a ≤ 1 / 2 then B else B * a⁻¹ ^ 2) * Real.exp (lam * t - c * w)) *
          Real.exp (-c * ((l : ℝ) + r + (m + 1))) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        hpair ν hν f hf hf0 hfD hfz hfe hνf w s a t hw hs0 hsp ha haway ht y z hyz l r (m + 1) (by omega)
    have hcoef : 0 ≤ (if a ≤ 1 / 2 then B else B * a⁻¹ ^ 2) * Real.exp (lam * t - c * w) := by
      split_ifs <;> positivity
    have hh := kernelWeightedPairTailSum_le_of_exp ν f hw0 hc hcoef hp L R M
    have ht' : (2 + w) * (1 + 1 / c) ^ 4 ≤ 3 * (1 + 1 / c) ^ 4 * w := by
      have hh := mul_le_mul_of_nonneg_right (show 2 + w ≤ 3 * w by linarith) (show 0 ≤ (1 + 1 / c) ^ 4 by positivity)
      exact hh.trans_eq (by ring)
    have hh' := hh.trans (mul_le_mul_of_nonneg_left ht' hcoef)
    have ho := houter ν hν w s a hw hs0 hso ha
    by_cases halo : a ≤ 1 / 2
    · rw [if_pos halo] at ho hh' ⊢
      have hh'' := mul_le_mul ho hh' (kernelWeightedPairTailSum_nonneg ν hf0 hw0 s a t y z L R M) (by positivity)
      have hw16 : w ^ 3 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
      have hlast : Os * B * (3 * (1 + 1 / c) ^ 4) * w ^ 3 * Real.exp (lam * t - c * w) ≤
          K * w ^ 16 * Real.exp (lam * t - c * w) := by
        dsimp [K]
        gcongr
        linarith
      apply hh''.trans
      convert hlast using 1 <;> first | rfl | ring
    · rw [if_neg halo] at ho hh' ⊢
      have hh'' := mul_le_mul ho hh' (kernelWeightedPairTailSum_nonneg ν hf0 hw0 s a t y z L R M) (by positivity)
      have hw16 : w ^ 7 ≤ w ^ 16 := pow_le_pow_right₀ hw (by norm_num)
      have hlast : (Ol * B * (3 * (1 + 1 / c) ^ 4)) * a⁻¹ ^ 2 * w ^ 7 * Real.exp (lam * t - c * w) ≤
          (K * a⁻¹ ^ 2) * w ^ 16 * Real.exp (lam * t - c * w) := by
        dsimp [K]
        gcongr
        linarith
      apply hh''.trans
      convert hlast using 1 <;> first | rfl | ring
  · rw [if_neg haway, mul_zero]
    split_ifs <;> positivity

/-- Complete positive-slope integration preserves the far width exponential. -/
theorem kernel_regLaw_weighted_far_bulk_integral (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ ρ lam c K : ℝ, 0 < ρ ∧ 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
      ∀ L R M : ℕ,
        IntegrableOn (fun a => kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M) (Ioi 0) ∧
        (∫ a in Ioi (0 : ℝ), kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M) ≤
          K * w ^ 16 * Real.exp (lam * t - c * w) := by
  obtain ⟨ρ, lam, c, K, hρ, hlam, hc, hK, hb⟩ := kernel_regLaw_weighted_far_bulk_budget D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  refine ⟨ρ, lam, c, 5 * K / 2, hρ, hlam, hc, by positivity, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz L R M
  have hF (a : ℝ) : 0 ≤ kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M :=
    mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s a) (kernelWeightedFarPairTailSum_nonneg ν hf0 (by linarith) δ s a t y z L R M)
  have hFm := (measurable_kernelPhysicalOuterWeight ν w s).mul (measurable_kernelWeightedFarPairTailSum ν hf δ w s t y z L R M)
  let C := K * w ^ 16 * Real.exp (lam * t - c * w)
  have hC : 0 ≤ C := by positivity
  have hsmall (a : ℝ) (ha : a ∈ Ioc (0 : ℝ) (1 / 2)) :
      kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M ≤ C := by
    simpa only [if_pos ha.2] using hb ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz L R M a ha.1
  have hlarge (a : ℝ) (ha : a ∈ Ioi (1 / 2 : ℝ)) :
      kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z L R M ≤ C * a⁻¹ ^ 2 := by
    have ha' : (1 / 2 : ℝ) < a := ha
    have hh := hb ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz L R M a (by linarith)
    rw [if_neg (not_le.mpr ha')] at hh
    exact hh.trans_eq (by dsimp [C]; ring)
  obtain ⟨hi, hh⟩ := kernel_slope_integral_of_two_bounds hFm hF hC hC hsmall hlarge
  exact ⟨hi, hh.trans_eq (by dsimp [C]; ring)⟩

def kernelWeightedFarBulkTailTerm (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (δ w s t y z a : ℝ)
    (p : ℕ × ℕ × ℕ) : ℝ :=
  if δ ≤ |a - 1| then kernelWeightedBulkTailTerm ν f w s t y z a p else 0

theorem kernelWeightedFarBulkTailTerm_cube (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    (hf0 : ∀ x, 0 ≤ f x) {w : ℝ} (hw : 0 ≤ w) (δ s t y z a : ℝ) (N : ℕ) :
    (∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelWeightedFarBulkTailTerm ν f δ w s t y z a p)) =
        ENNReal.ofReal (kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z N N N) := by
  by_cases ha : δ ≤ |a - 1|
  · simpa only [kernelWeightedFarBulkTailTerm, kernelWeightedFarPairTailSum, if_pos ha] using kernelWeightedBulkTailTerm_cube ν hf0 hw s t y z a N
  · simp [kernelWeightedFarBulkTailTerm, kernelWeightedFarPairTailSum, ha]

/-- The actual infinite marked-pair IF at every slope outside a fixed saddle
neighborhood. This includes both extreme slope ends and has a uniform width
exponential before choosing any logarithmic input window. -/
theorem kernel_regLaw_weighted_far_bulk_infinite (D θ vlo vhi δ : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 2) :
    ∃ ρ lam c K : ℝ, 0 < ρ ∧ 0 < lam ∧ 0 < c ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x = 0) → (∀ x, f x ≤ D * Real.exp (-θ * x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w s t : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ / w ^ 2 → 0 ≤ t →
      ∀ y z : ℝ, ((y = 0 ∧ z = w) ∨ (y = w ∧ z = 0)) →
        (∫⁻ a in Ioi (0 : ℝ), ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelWeightedFarBulkTailTerm ν f δ w s t y z a p)) ≤
            ENNReal.ofReal (K * w ^ 16 * Real.exp (lam * t - c * w)) := by
  obtain ⟨ρ, lam, c, K, hρ, hlam, hc, hK, hb⟩ := kernel_regLaw_weighted_far_bulk_integral D θ vlo vhi δ hD hθ hvlo hv hδ hδhi
  refine ⟨ρ, lam, c, K, hρ, hlam, hc, hK, ?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz
  let F : ℕ → ℝ → ℝ≥0∞ := fun N a =>
    ∑ p ∈ (Finset.range N ×ˢ (Finset.range N ×ˢ Finset.range N)),
      ENNReal.ofReal (kernelWeightedFarBulkTailTerm ν f δ w s t y z a p)
  have hw0 : 0 ≤ w := by linarith
  have hFE (N : ℕ) (a : ℝ) : F N a = ENNReal.ofReal
      (kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z N N N) :=
    kernelWeightedFarBulkTailTerm_cube ν hf0 hw0 δ s t y z a N
  have hFm (N : ℕ) : Measurable (F N) := by
    have he : F N = fun a => ENNReal.ofReal
        (kernelPhysicalOuterWeight ν w s a * kernelWeightedFarPairTailSum ν f δ w s a t y z N N N) := funext (hFE N)
    rw [he]
    exact ((measurable_kernelPhysicalOuterWeight ν w s).mul (measurable_kernelWeightedFarPairTailSum ν hf δ w s t y z N N N)).ennreal_ofReal
  have hFmono : Monotone F := by
    intro N M hNM a
    exact Finset.sum_le_sum_of_subset (Finset.product_subset_product (Finset.range_mono hNM)
      (Finset.product_subset_product (Finset.range_mono hNM) (Finset.range_mono hNM)))
  simp_rw [kernel_ennreal_triple_eq_iSup_cube]
  change (∫⁻ a in Ioi (0 : ℝ), ⨆ N : ℕ, F N a) ≤ _
  rw [lintegral_iSup hFm hFmono]
  apply iSup_le
  intro N
  obtain ⟨hI, hB⟩ := hb ν hν f hf hf0 hfD hfz hfe hνf w s t hw hs0 hs ht y z hyz N N N
  simp_rw [hFE]
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun a => mul_nonneg (kernelPhysicalOuterWeight_nonneg ν w s a)
      (kernelWeightedFarPairTailSum_nonneg ν hf0 hw0 δ s a t y z N N N))]
  exact ENNReal.ofReal_le_ofReal hB

end
end PGM
