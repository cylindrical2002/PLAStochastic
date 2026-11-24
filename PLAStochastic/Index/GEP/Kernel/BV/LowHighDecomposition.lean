import PLAStochastic.Index.GEP.Kernel.BV.SmoothStep
import PLAStochastic.ForMathlib.Analysis.Normed.Operator.DuhamelExpansion

/-!
# Actual low/high decomposition of long killed chains

The regular representative is constructed from the actual low-frequency step.
Its variation is propagated by the original killed integral operator. The
remainder is the actual power of the high-frequency continuous linear map.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory FourierTransform Set Filter
open scoped BigOperators

theorem kBV_variation_add_le (f g : ℝ → ℂ) (J : Set ℝ) :
    eVariationOn (f + g) J ≤ eVariationOn f J + eVariationOn g J := by
  apply iSup_le
  rintro ⟨n, u, hu, hJ⟩
  calc
    (∑ i ∈ Finset.range n, edist ((f + g) (u (i + 1))) ((f + g) (u i))) ≤
        ∑ i ∈ Finset.range n,
          (edist (f (u (i + 1))) (f (u i)) + edist (g (u (i + 1))) (g (u i))) := by
      exact Finset.sum_le_sum fun _ _ => edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        ∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i)) := Finset.sum_add_distrib
    _ ≤ eVariationOn f J + eVariationOn g J :=
      add_le_add (eVariationOn.sum_le hu hJ) (eVariationOn.sum_le hu hJ)

/-- An actual measurable BV representative, supported in the killed interval. -/
def kBVHasRep (J : Set ℝ) (b : ℝ) (U : KernelL2) : Prop :=
  ∃ g : ℝ → ℂ, Measurable g ∧ Integrable g ∧ ∃ hg2 : MemLp g 2,
    hg2.toLp g = U ∧ (∀ x, x ∉ J → g x = 0) ∧
      eVariationOn g univ ≤ ENNReal.ofReal b

theorem kBVHasRep_mono {J : Set ℝ} {b c : ℝ} {U : KernelL2}
    (h : kBVHasRep J b U) (hbc : b ≤ c) : kBVHasRep J c U := by
  rcases h with ⟨g, hg, hg1, hg2, heq, hsupp, hvar⟩
  exact ⟨g, hg, hg1, hg2, heq, hsupp, hvar.trans (ENNReal.ofReal_le_ofReal hbc)⟩

theorem kBVHasRep_zero (J : Set ℝ) : kBVHasRep J 0 0 := by
  refine ⟨0, measurable_const, integrable_zero _ _ _, MemLp.zero, ?_, ?_, ?_⟩
  · exact MemLp.toLp_zero _
  · intro x _; rfl
  · simp [eVariationOn]

theorem kBVHasRep_add {J : Set ℝ} {b c : ℝ} {U V : KernelL2}
    (hU : kBVHasRep J b U) (hV : kBVHasRep J c V) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    kBVHasRep J (b + c) (U + V) := by
  rcases hU with ⟨f, hf, hf1, hf2, hfU, hfs, hfv⟩
  rcases hV with ⟨g, hg, hg1, hg2, hgV, hgs, hgv⟩
  refine ⟨f + g, hf.add hg, hf1.add hg1, hf2.add hg2, ?_, ?_, ?_⟩
  · rw [MemLp.toLp_add hf2 hg2, hfU, hgV]
  · intro x hx; simp [hfs x hx, hgs x hx]
  · exact (kBV_variation_add_le f g univ).trans
      ((add_le_add hfv hgv).trans_eq (ENNReal.ofReal_add hb hc).symm)

/-- Propagating an actual BV representative costs no variation constant. -/
theorem kBVKilledL2_preserves_rep (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a α : ℝ)
    {w b : ℝ} (hw : 0 ≤ w) {U : KernelL2}
    (hU : kBVHasRep (Icc α (α + w)) b U) :
    kBVHasRep (Icc α (α + w)) b
      (kBVKilledL2 (Icc α (α + w)) measurableSet_Icc ν β a U) := by
  rcases hU with ⟨g, hg, hg1, hg2, hgU, hgs, hgv⟩
  have hgbv : BoundedVariationOn g univ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgv
  refine ⟨kStep (Icc α (α + w)) ν β a g, measurable_kStep measurableSet_Icc ν hg,
    (integrable_kConv ν hg hg1 β a).indicator measurableSet_Icc,
    ((memLp_two_kConv ν hg hg1 hg2 β a).1).indicator measurableSet_Icc, ?_, ?_, ?_⟩
  · rw [← hgU, kBVKilledL2_toLp measurableSet_Icc ν β a hg hg1 hg2 hgs]
  · intro x hx; exact indicator_of_notMem hx _
  · exact (kBV_variation_kStep_le hg hgbv hg1 (by linarith) β a).trans hgv

theorem kBVLowStepL2_hasRep (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a α : ℝ)
    {w : ℝ} (hw : 1 ≤ w) (U : KernelL2) :
    kBVHasRep (Icc α (α + w)) (8 * Real.pi * Real.sqrt w * ‖U‖)
      (kBVLowStepL2 (Icc α (α + w)) measurableSet_Icc ν β a U) :=
  kBVLowStepL2_regularizes ν β a α hw U

/-- The noncommutative Duhamel sum has an actual BV representative. The only
quantitative hypothesis here is a norm estimate on the explicitly constructed
high-frequency operator; `RegLaw` supplies it below. -/
theorem kBV_long_decomposition (ν : Measure ℝ) [IsProbabilityMeasure ν] (β a α : ℝ)
    {w ρ : ℝ} (hw : 1 ≤ w) (hρ : 0 ≤ ρ)
    (hR : ∀ U : KernelL2,
      ‖kBVHighStepL2 (Icc α (α + w)) measurableSet_Icc ν β a U‖ ≤ ρ * ‖U‖)
    (U : KernelL2) (n : ℕ) :
    kBVHasRep (Icc α (α + w))
      (8 * Real.pi * Real.sqrt w * (∑ j ∈ Finset.range n, ρ ^ j) * ‖U‖)
      (((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc ν β a) ^ n) U -
        ((kBVHighStepL2 (Icc α (α + w)) measurableSet_Icc ν β a) ^ n) U) ∧
      ‖((kBVHighStepL2 (Icc α (α + w)) measurableSet_Icc ν β a) ^ n) U‖ ≤
        ρ ^ n * ‖U‖ := by
  let J := Icc α (α + w)
  let Q := kBVKilledL2 J measurableSet_Icc ν β a
  let S := kBVLowStepL2 J measurableSet_Icc ν β a
  let R := kBVHighStepL2 J measurableSet_Icc ν β a
  have hRn (m : ℕ) : ‖(R ^ m) U‖ ≤ ρ ^ m * ‖U‖ :=
    kBV_duhamel_remainder_bound R (R.opNorm_le_bound hρ hR) m U
  refine ⟨?_, hRn n⟩
  change kBVHasRep J _ ((Q ^ n) U - (R ^ n) U)
  induction n with
  | zero => simpa using kBVHasRep_zero J
  | succ n ih =>
    have hQ := kBVKilledL2_preserves_rep ν β a α (by linarith : 0 ≤ w) ih
    have hS := kBVLowStepL2_hasRep ν β a α hw ((R ^ n) U)
    have hSm := kBVHasRep_mono hS
      (mul_le_mul_of_nonneg_left (hRn n) (by positivity : 0 ≤ 8 * Real.pi * Real.sqrt w))
    have hadd := kBVHasRep_add hQ hSm (by positivity) (by positivity)
    have heq : Q ((Q ^ n) U - (R ^ n) U) + S ((R ^ n) U) =
        (Q ^ (n + 1)) U - (R ^ (n + 1)) U := by
      rw [pow_succ', pow_succ']
      simp only [mul_apply_eq_comp, map_sub]
      change Q ((Q ^ n) U) - Q ((R ^ n) U) + S ((R ^ n) U) =
        Q ((Q ^ n) U) - (Q ((R ^ n) U) - S ((R ^ n) U))
      abel
    have hb : 8 * Real.pi * Real.sqrt w * (∑ j ∈ Finset.range n, ρ ^ j) * ‖U‖ +
        8 * Real.pi * Real.sqrt w * (ρ ^ n * ‖U‖) =
        8 * Real.pi * Real.sqrt w * (∑ j ∈ Finset.range (n + 1), ρ ^ j) * ‖U‖ := by
      rw [Finset.sum_range_succ]
      ring
    simpa only [← heq, ← hb] using hadd

theorem kBV_geometric_sum_le {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, ρ ^ j) ≤ 1 / (1 - ρ) := by
  apply (le_div_iff₀ (by linarith : 0 < 1 - ρ)).mpr
  rw [geom_sum_mul_neg]
  have hp := pow_nonneg hρ n
  linarith

/-- Every real `RegLaw` killed chain splits into an actual BV representative and
its exponentially small pure high-frequency word. -/
theorem kBV_regLaw_long_decomposition {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν)
    (β α : ℝ) {a w : ℝ} (ha : 1 / 2 ≤ |a|) (hw : 1 ≤ w)
    (U : KernelL2) (n : ℕ) :
    kBVHasRep (Icc α (α + w))
      (8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi)) * ‖U‖)
      (((kBVKilledL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n) U -
        ((kBVHighStepL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n) U) ∧
      ‖((kBVHighStepL2 (Icc α (α + w)) measurableSet_Icc (ν : Measure ℝ) β a) ^ n) U‖ ≤
        Real.sqrt (1 - killCnu D vlo vhi) ^ n * ‖U‖ := by
  have hρ1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo (hν.var_ge.trans hν.var_le)
  obtain ⟨hrep, hrem⟩ := kBV_long_decomposition (ν : Measure ℝ) β a α hw
    (Real.sqrt_nonneg _) (kBVHighStepL2_regLaw_bound hD hθ hvlo hν measurableSet_Icc β ha) U n
  refine ⟨kBVHasRep_mono hrep ?_, hrem⟩
  have hsum := kBV_geometric_sum_le (Real.sqrt_nonneg (1 - killCnu D vlo vhi)) hρ1 n
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 8 * Real.pi * Real.sqrt w))
    (norm_nonneg U)

end
end PGM
