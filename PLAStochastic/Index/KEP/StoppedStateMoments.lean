import PLAStochastic.Index.KEP.Poisson.StateMoments
import PLAStochastic.Index.KEP.IIDPathMoments
import PLAStochastic.Index.KEP.StoppedPrefixMoments
import PLAStochastic.ForMathlib.Probability.Moments.EventFourthMoment

/-!
# Moment payment under the actual absorbing prefix state law

The state law is the original stopped child sequence pushed forward to its
observed prefix. Both integrability and active second moments are paid from
the full path at the same horizon; event dependence is unrestricted.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem stopped_prefix_state_power_budget {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℕ → ℝ} (hX : Measurable X)
    (hpos : ∀ᵐ w ∂P, ∀ i, 0 ≤ X w i) (eps : ℝ) (N p : ℕ)
    (hi : Integrable (fun w => gapKeys (X w) N ^ p) P) {C : ℝ}
    (hbudget : ∫ w, gapKeys (X w) N ^ p ∂P ≤ C) :
    Integrable (fun g => gapKeys g N ^ p)
      (P.map (fun w => kepStoppedPrefix eps N (X w))) ∧
      ∫ g, gapKeys g N ^ p ∂(P.map (fun w => kepStoppedPrefix eps N (X w))) ≤ C := by
  have h := integrable_stopped_gapKeys_power_le P hX hpos eps N p hi
  have hphi : Measurable (fun w => kepStoppedPrefix eps N (X w)) :=
    (measurable_kepStoppedPrefix eps N).comp hX
  have hF : Measurable (fun g : ℕ → ℝ => gapKeys g N ^ p) :=
    ((measurable_pi_apply N).comp measurable_gapKeys).pow_const p
  exact ⟨(integrable_map_measure hF.aestronglyMeasurable hphi.aemeasurable).mpr h.1,
    (by rw [integral_map hphi.aemeasurable hF.aestronglyMeasurable]; exact h.2.trans hbudget)⟩

theorem stopped_prefix_state_active_mass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {X : Ω → ℕ → ℝ} (hX : Measurable X) (eps : ℝ) (N : ℕ) :
    (P.map (fun w => kepStoppedPrefix eps N (X w))).real
      {g | (N : ℕ∞) < gapSegLen eps g} =
        P.real {w | (N : ℕ∞) < gapSegLen eps (X w)} := by
  have hphi : Measurable (fun w => kepStoppedPrefix eps N (X w)) :=
    (measurable_kepStoppedPrefix eps N).comp hX
  rw [map_measureReal_apply hphi
    ((isStoppingRule_gapSegLen eps).measurableSet_lt N)]
  congr 1
  ext w
  exact kepStoppedPrefix_active eps N (X w)

theorem stopped_prefix_state_active_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {X : Ω → ℕ → ℝ} (hX : Measurable X)
    (eps : ℝ) (N : ℕ) (hi : Integrable (fun w => gapKeys (X w) N ^ 4) P) :
    ∫ g, {g | (N : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => gapKeys g N ^ 2) g
      ∂(P.map (fun w => kepStoppedPrefix eps N (X w))) ≤
        Real.sqrt (∫ w, gapKeys (X w) N ^ 4 ∂P) *
          Real.sqrt (P.real {w | (N : ℕ∞) < gapSegLen eps (X w)}) := by
  have hs : MeasurableSet {g : ℕ → ℝ | (N : ℕ∞) < gapSegLen eps g} :=
    (isStoppingRule_gapSegLen eps).measurableSet_lt N
  have hF : Measurable ({g : ℕ → ℝ | (N : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => gapKeys g N ^ 2)) :=
    (((measurable_pi_apply N).comp measurable_gapKeys).pow_const 2).indicator hs
  have hphi : Measurable (fun w => kepStoppedPrefix eps N (X w)) :=
    (measurable_kepStoppedPrefix eps N).comp hX
  rw [integral_map hphi.aemeasurable
    hF.aestronglyMeasurable]
  have he : (fun w => {g | (N : ℕ∞) < gapSegLen eps g}.indicator
      (fun g => gapKeys g N ^ 2) (kepStoppedPrefix eps N (X w))) =
      {w | (N : ℕ∞) < gapSegLen eps (X w)}.indicator
        (fun w => gapKeys (X w) N ^ 2) := by
    funext w
    by_cases hw : (N : ℕ∞) < gapSegLen eps (X w)
    · simp only [indicator_apply, mem_ofPred_eq, kepStoppedPrefix_active, if_pos hw,
        kepStoppedPrefix_gapKeys_of_active hw]
    · simp only [indicator_apply, mem_ofPred_eq, kepStoppedPrefix_active, if_neg hw]
  rw [he]
  exact (integral_event_sq_le_fourth_moment P
    (((measurable_pi_apply N).comp measurable_gapKeys).comp hX) hi
      (hs.preimage hX)).2

theorem kepPoisson_stopped_sequence_state_law {f : ℝ → ℝ} {flo fhi L eps n : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : n ≠ 0) (x : ℝ) (j N : ℕ)
    (hm : kepReferenceSpan eps j ≠ 0)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤) :
    expSeqMeasure.map (fun g => kepStoppedPrefix eps N (kepPoissonLayerSequence hf eps n x j g)) =
      kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
        (Measure.dirac (fun _ => 0)) N := by
  rw [← kepPoissonStoppedPrefixState_law hf hn j hm hfin x N]
  apply Measure.map_congr
  filter_upwards [kepPoissonPivot_all_finite_of_leading hf eps n j hfin x N] with g hg
  exact (kepPoissonStoppedPrefixState_eq_layerSequence hf hg).symm

theorem kepPoisson_stopped_state_power_budget {f : ℝ → ℝ} {flo fhi L eps n theta B : ℝ}
    (hf : KepIntensityProfile f flo fhi L) (hn : 0 < n) (htheta : 0 < theta)
    (hB : 0 ≤ B) (x : ℝ) (j N k : ℕ) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y : ℝ, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hchild : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B) :
    Integrable (fun g => gapKeys g N ^ (k + 1))
      (kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
        (Measure.dirac (fun _ => 0)) N) ∧
      ∫ g, gapKeys g N ^ (k + 1)
        ∂kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
          (Measure.dirac (fun _ => 0)) N ≤
        (N : ℝ) ^ (k + 1) * ((k + 1).factorial / (theta / (fhi / flo)) ^ (k + 1) * B) := by
  have hpos : ∀ᵐ g ∂expSeqMeasure, ∀ i, 0 ≤ kepPoissonLayerSequence hf eps n x j g i := by
    filter_upwards [ae_all_iff.mpr fun a =>
      iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) a] with g hg
    exact kepPoissonLayerSequence_nonneg hf hn x j hm.le (fun a => (hg a).le)
  have h := kepPoissonLayerSequence_power_budget hf hn htheta hB x j N k hm hfin hchild
  rw [← kepPoisson_stopped_sequence_state_law hf hn.ne' x j N hm.ne' hfin]
  exact stopped_prefix_state_power_budget expSeqMeasure
    (measurable_kepPoissonLayerSequence_anchor hf eps n x j) hpos eps N (k + 1) h.1 h.2

theorem iid_stopped_state_power_budget (nu : ProbabilityMeasure ℝ)
    {theta B : ℝ} (htheta : 0 < theta)
    (hpos : ∀ᵐ z ∂(nu : Measure ℝ), 0 ≤ z)
    (hi : Integrable (fun z => Real.exp (theta * z)) (nu : Measure ℝ))
    (hb : ∫ z, Real.exp (theta * z) ∂(nu : Measure ℝ) ≤ B) (eps : ℝ) (N k : ℕ) :
    Integrable (fun g => gapKeys g N ^ (k + 1))
      (kernelIterateLaw (kepReferenceStoppedPrefixKernel nu eps) (Measure.dirac (fun _ => 0)) N) ∧
      ∫ g, gapKeys g N ^ (k + 1)
        ∂kernelIterateLaw (kepReferenceStoppedPrefixKernel nu eps) (Measure.dirac (fun _ => 0)) N ≤
        (N : ℝ) ^ (k + 1) * ((k + 1).factorial / theta ^ (k + 1) * B) := by
  have hpos' : ∀ᵐ g ∂iidLaw nu, ∀ i, 0 ≤ g i := ae_all_iff.mpr fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => (nu : Measure ℝ)) i).quasiMeasurePreserving.ae hpos
  have h := iid_gapKeys_power_budget nu htheta hpos hi hb N k
  rw [← iid_kepStoppedPrefix_law]
  exact stopped_prefix_state_power_budget (iidLaw nu) measurable_id hpos' eps N (k + 1) h.1 h.2

end

end PGM
