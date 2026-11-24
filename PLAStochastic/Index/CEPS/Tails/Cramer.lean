import PLAStochastic.Index.CEPS.Tails.EventComparison
import PLAStochastic.ForMathlib.Probability.RandomWalk.WienerHopf.LargeDeviation
import PLAStochastic.Index.GEP.OrbitClosure.RegularClass

/-!
# Cramér bounds on the actual gap probability space

The W-7 estimates are transported from the Wiener–Hopf increment space to
`iidLaw ν`, with the actual `kWalk` positions. Regular laws supply the step-class
hypotheses; the rate depends only on `D`, `θ`, and the fixed cutoff `δ`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset
open WienerHopf

/-- A `RegLaw` density is a Wiener–Hopf gap-law density with the same envelope. -/
theorem RegLaw.exists_isGapLaw {D θ vlo vhi : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo) :
    ∃ f, IsGapLaw (ν : Measure ℝ) f D θ vhi := by
  obtain ⟨f, hm, hn, hz, he, hd⟩ := hν.density
  have h2 : MemLp id 2 (ν : Measure ℝ) := (hν.momClass hθ hvlo).memLp3.mono_exponent (by norm_num)
  refine ⟨f, inferInstance, hd, hm, hn, hz, fun x _ => he x, ?_, hν.mean, ?_⟩
  · exact (h2.sub (memLp_const 1)).integrable_sq
  · simpa [lawVar, hν.mean] using hν.var_le

/-- The affine increments of an actual gap sequence have the canonical increment law. -/
theorem map_iidLaw_affine (ν : ProbabilityMeasure ℝ) (β a : ℝ) :
    (iidLaw ν).map (fun g n => β - a * g n) = pathLaw ((ν : Measure ℝ).map fun x => β - a * x) := by
  exact Measure.infinitePi_map_pi (fun _ : ℕ => (ν : Measure ℝ))
    (f := fun _ x => β - a * x) (fun _ => by fun_prop)

theorem partialSum_affine (β a : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    WienerHopf.partialSum n (fun i => β - a * g i) = kWalk 0 β a g n := by
  simp only [WienerHopf.partialSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, ← Finset.mul_sum, kWalk, gapKeys]
  ring

/-- Pullback of any measurable event on increments to the actual gap space. -/
theorem measureReal_affine_event (ν : ProbabilityMeasure ℝ) (β a : ℝ)
    {E : Set (ℕ → ℝ)} (hE : MeasurableSet E) :
    (pathLaw ((ν : Measure ℝ).map fun x => β - a * x)).real E =
      (iidLaw ν).real {g | (fun n => β - a * g n) ∈ E} := by
  rw [← map_iidLaw_affine, measureReal_def, Measure.map_apply (by fun_prop) hE]
  rfl

/-- Express the drift of the centred `1-X` law directly as an affine gap law. -/
theorem driftStep_one_sub_eq (ν : ProbabilityMeasure ℝ) (μ : ℝ) :
    driftStep ((ν : Measure ℝ).map fun x => 1 - x) μ =
      (ν : Measure ℝ).map (fun x => (1 + μ) - 1 * x) := by
  unfold driftStep
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

/-- Positive-drift endpoint Cramér bound on actual gap paths. -/
theorem measureReal_cepsWalk_le_neg_of_gapLaw {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D θ v δ μ x : ℝ} (hf : IsGapLaw (ν : Measure ℝ) f D θ v)
    (hθ : 0 < θ) (hD : 0 < D) (hδ : 0 < δ) (hμ : δ ≤ μ) (n : ℕ) (hx : 0 ≤ x) :
    (iidLaw ν).real {g | kWalk 0 (1 + μ) 1 g n ≤ -x} ≤
      Real.exp (-(driftRate (D * Real.exp θ) θ δ * (x + δ * n))) := by
  have hW := hf.toStepLaw hθ.le hD.le
  have h := measureReal_partialSum_le_neg_of_stepLaw hW hθ (by positivity) hδ hμ n hx
  rw [driftStep_one_sub_eq, measureReal_affine_event ν (1 + μ) 1
    (measurableSet_le (measurable_partialSum n) measurable_const)] at h
  simpa only [mem_ofPred_eq, partialSum_affine] using h

/-- Positive-drift Cramér union bound over actual gap-path intervals. -/
theorem measureReal_cepsWalk_exists_le_neg_of_gapLaw {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D θ v δ μ x : ℝ} (hf : IsGapLaw (ν : Measure ℝ) f D θ v)
    (hθ : 0 < θ) (hD : 0 < D) (hδ : 0 < δ) (hμ : δ ≤ μ) (k : ℕ) (hx : 0 ≤ x) :
    (iidLaw ν).real {g | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
      kWalk 0 (1 + μ) 1 g j - kWalk 0 (1 + μ) 1 g i ≤ -x} ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(driftRate (D * Real.exp θ) θ δ * x)) := by
  have hW := hf.toStepLaw hθ.le hD.le
  have h := measureReal_exists_increment_le_of_stepLaw hW hθ (by positivity) hδ hμ k hx
  have hm : MeasurableSet {ω : ℕ → ℝ | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
      WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} := by
    have heq : {ω : ℕ → ℝ | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
        WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} =
        ⋃ i : ℕ, ⋃ j : ℕ, {ω : ℕ → ℝ | (i ≤ k ∧ j ≤ k ∧ i ≤ j) ∧
          WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      aesop
    rw [heq]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
    by_cases h : i ≤ k ∧ j ≤ k ∧ i ≤ j
    · simpa only [h, true_and, Pi.sub_apply] using measurableSet_le
        ((measurable_partialSum j).sub (measurable_partialSum i)) measurable_const
    · simpa only [h, false_and, ofPred_false] using MeasurableSet.empty
  rw [driftStep_one_sub_eq, measureReal_affine_event ν (1 + μ) 1 hm] at h
  simpa only [mem_ofPred_eq, partialSum_affine] using h

/-- The reverse crossing from S-7(a) has an exponential Cramér bound. -/
theorem measureReal_cepsReverseCross_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi eps δ : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (heps : 0 ≤ eps) (k : ℕ) :
    (iidLaw ν).real {g | cepsReverseCross eps δ g k} ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 + δ)))) := by
  obtain ⟨f, hf⟩ := hν.exists_isGapLaw hθ hvlo
  refine (measureReal_mono (fun g h => ?_) (measure_ne_top _ _)).trans
    (measureReal_cepsWalk_exists_le_neg_of_gapLaw hf hθ hD hδ le_rfl k (by positivity))
  obtain ⟨i, hi, j, hj, hij, hlt⟩ := h
  exact ⟨i, hi, j, hj, hij, hlt.le⟩

/-- The reflected drift law, on actual gaps. -/
theorem driftStep_sub_one_eq (ν : ProbabilityMeasure ℝ) (μ : ℝ) :
    driftStep (((ν : Measure ℝ).map fun x => 1 - x).map Neg.neg) (-μ) =
      (ν : Measure ℝ).map (fun x => -(1 + μ) - (-1) * x) := by
  unfold driftStep
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  ring

/-- Negative-drift forward-crossing union bound on actual gap paths. -/
theorem measureReal_cepsWalk_exists_ge_of_gapLaw {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ}
    {D θ v δ μ x : ℝ} (hf : IsGapLaw (ν : Measure ℝ) f D θ v)
    (hθ : 0 < θ) (hD : 0 < D) (hδ : 0 < δ) (hμ : μ ≤ -δ) (k : ℕ) (hx : 0 ≤ x) :
    (iidLaw ν).real {g | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
      x ≤ kWalk 0 (1 + μ) 1 g j - kWalk 0 (1 + μ) 1 g i} ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 * Real.exp (-(driftRate (D * Real.exp θ) θ δ * x)) := by
  have hW := (hf.toStepLaw hθ.le hD.le).neg
  have h := measureReal_exists_increment_le_of_stepLaw hW hθ (by positivity) hδ
    (μ := -μ) (by linarith) k hx
  have hm : MeasurableSet {ω : ℕ → ℝ | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
      WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} := by
    have heq : {ω : ℕ → ℝ | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
        WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} =
        ⋃ i : ℕ, ⋃ j : ℕ, {ω : ℕ → ℝ | (i ≤ k ∧ j ≤ k ∧ i ≤ j) ∧
          WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iUnion]
      aesop
    rw [heq]
    refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
    by_cases h : i ≤ k ∧ j ≤ k ∧ i ≤ j
    · simpa only [h, true_and, Pi.sub_apply] using measurableSet_le
        ((measurable_partialSum j).sub (measurable_partialSum i)) measurable_const
    · simpa only [h, false_and, ofPred_false] using MeasurableSet.empty
  rw [driftStep_sub_one_eq, measureReal_affine_event ν (-(1 + μ)) (-1) hm] at h
  have heq : {g : ℕ → ℝ | (fun n => -(1 + μ) - (-1) * g n) ∈
      {ω | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
        WienerHopf.partialSum j ω - WienerHopf.partialSum i ω ≤ -x}} =
      {g | ∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
        x ≤ kWalk 0 (1 + μ) 1 g j - kWalk 0 (1 + μ) 1 g i} := by
    ext g
    change (∃ i ≤ k, ∃ j ≤ k, i ≤ j ∧
      WienerHopf.partialSum j (fun n => -(1 + μ) - (-1) * g n) -
        WienerHopf.partialSum i (fun n => -(1 + μ) - (-1) * g n) ≤ -x) ↔ _
    simp only [partialSum_affine]
    have hn : ∀ n, kWalk 0 (-(1 + μ)) (-1) g n = -kWalk 0 (1 + μ) 1 g n := by
      intro n
      unfold kWalk
      ring
    simp_rw [hn]
    constructor
    · rintro ⟨i, hi, j, hj, hij, hh⟩
      exact ⟨i, hi, j, hj, hij, by linarith⟩
    · rintro ⟨i, hi, j, hj, hij, hh⟩
      exact ⟨i, hi, j, hj, hij, by linarith⟩
  rw [heq] at h
  exact h

/-- The forward crossing from S-7(b), for regular input laws. -/
theorem measureReal_not_cepsDrawupOK_of_regLaw {ν : ProbabilityMeasure ℝ}
    {D θ vlo vhi eps δ : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hD : 0 < D)
    (hvlo : 0 < vlo) (hδ : 0 < δ) (hδ1 : δ < 1) (heps : 0 ≤ eps) (k : ℕ) :
    (iidLaw ν).real {g | ¬ cepsDrawupOK (1 - δ) 1 (2 * eps * (1 - δ)) g k} ≤
      ((k + 1 : ℕ) : ℝ) ^ 2 *
        Real.exp (-(driftRate (D * Real.exp θ) θ δ * (2 * eps * (1 - δ)))) := by
  obtain ⟨f, hf⟩ := hν.exists_isGapLaw hθ hvlo
  refine (measureReal_mono (fun g h => ?_) (measure_ne_top _ _)).trans
    (measureReal_cepsWalk_exists_ge_of_gapLaw hf hθ hD hδ le_rfl k (by positivity))
  unfold cepsDrawupOK at h
  push Not at h
  obtain ⟨i, j, hij, hj, hlt⟩ := h
  exact ⟨i, by omega, j, hj, hij, hlt.le⟩

end

end PGM
