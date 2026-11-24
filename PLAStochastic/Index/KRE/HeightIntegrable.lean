import PLAStochastic.Index.ModelK.ConstantDensity
import PLAStochastic.Index.Algorithm.MeasurableRankHeight

/-!
# Integrability of the ALG-RE height

The upper halves of H-G-RE and H-K-RE bound a Bochner integral from above.  Such a bound
would be vacuous if the height were not integrable (the integral would then be `0`), so we
record that it is: the height is measurable and deterministically at most `⌊log₂ n⌋ + 1`.
-/

namespace PGM

open MeasureTheory ProbabilityTheory Finset

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The ALG-RE height of a.e.-measurable random keys is integrable. -/
theorem integrable_reHeight [IsFiniteMeasure P] {eps : ℝ} (heps : 1 ≤ eps) {n : ℕ}
    (hn : 1 ≤ n) {keys : Ω → ℕ → ℝ} (hkeys : AEMeasurable keys P) :
    Integrable (fun ω => (reHeight eps (keys ω) n : ℝ)) P := by
  have hm : AEMeasurable (fun ω => (reHeight eps (keys ω) n : ℝ)) P :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp_aemeasurable
      ((measurable_reHeight eps n).comp_aemeasurable hkeys)
  refine Integrable.mono' (integrable_const ((Nat.log 2 n : ℝ) + 1)) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast reHeight_le_log heps hn

/-- Model G: the ALG-RE height is integrable. -/
theorem integrable_reHeight_G [IsFiniteMeasure P] {g : ℕ → Ω → ℝ} (hg : ∀ s, Measurable (g s))
    {x0 : Ω → ℝ} (hx0 : Measurable x0) {eps : ℝ} (heps : 1 ≤ eps) {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun ω => (reHeight eps (fun s => x0 ω + ∑ i ∈ range s, g i ω) n : ℝ)) P :=
  integrable_reHeight heps hn (measurable_partialSumKeys hx0 hg).aemeasurable

/-- Model K: the ALG-RE height of the sorted sample is integrable. -/
theorem integrable_reHeight_K [IsFiniteMeasure P] {f : ℝ → ℝ} {A B : ℝ} {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) {eps : ℝ} (heps : 1 ≤ eps) {n : ℕ}
    (hn : 1 ≤ n) : Integrable (fun ω => (reHeight eps (kKeys X n ω) n : ℝ)) P := by
  refine integrable_reHeight heps hn ?_
  have hv : AEMeasurable (fun ω (i : Fin n) => X i ω) P :=
    aemeasurable_pi_lambda _ fun i => (hX i).aemeasurable
  exact (measurable_extendKeys.comp Renyi.measurable_sortVec).comp_aemeasurable hv

end PGM
