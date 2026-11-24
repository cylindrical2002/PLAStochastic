import PLAStochastic.Index.KEP.StoppedPrefixes
import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import PLAStochastic.Index.GEP.LayerLaw.Defs
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Compensated exponentials on the actual absorbing prefix chain

The potential counts only the observed active transitions. Conditional gap
exponential budgets suffice; independence of the nonhomogeneous gaps is not
assumed. Absorbed prefixes have zero future coordinates.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Set Filter
open scoped ENNReal

def kepActiveCount (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) : ℕ :=
  ∑ k ∈ range i, if (k : ℕ∞) < gapSegLen eps g then 1 else 0

theorem measurable_kepActiveCount (eps : ℝ) (i : ℕ) :
    Measurable (kepActiveCount eps i) := by
  unfold kepActiveCount
  exact Finset.measurable_sum _ fun k _ => Measurable.ite
    ((isStoppingRule_gapSegLen eps).measurableSet_lt k) measurable_const measurable_const

theorem kepActiveCount_succ (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    kepActiveCount eps (i + 1) g = kepActiveCount eps i g +
      if (i : ℕ∞) < gapSegLen eps g then 1 else 0 := by
  exact sum_range_succ _ _

theorem kepActiveCount_causal (eps : ℝ) (i : ℕ) {g g' : ℕ → ℝ}
    (hp : ∀ k < i, g k = g' k) : kepActiveCount eps i g = kepActiveCount eps i g' := by
  unfold kepActiveCount
  apply sum_congr rfl
  intro k hk
  have he : (k : ℕ∞) < gapSegLen eps g ↔ (k : ℕ∞) < gapSegLen eps g' :=
    mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps k)
      (fun a ha => hp a (ha.trans (mem_range.mp hk)))
  simp only [he]

theorem kepActiveCount_update (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) (z : ℝ) :
    kepActiveCount eps (i + 1) (Function.update g i z) = kepActiveCount eps (i + 1) g := by
  classical
  rw [kepActiveCount_succ, kepActiveCount_succ,
    kepActiveCount_causal eps i (fun k hk => Function.update_of_ne (Nat.ne_of_lt hk) _ _)]
  have he : (i : ℕ∞) < gapSegLen eps (Function.update g i z) ↔
      (i : ℕ∞) < gapSegLen eps g :=
    mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps i)
      (fun k hk => Function.update_of_ne (Nat.ne_of_lt hk) _ _)
  simp only [he]

theorem kepActiveCount_stoppedPrefix (eps : ℝ) (i : ℕ) (g : ℕ → ℝ) :
    kepActiveCount eps i (kepStoppedPrefix eps i g) = kepActiveCount eps i g := by
  unfold kepActiveCount
  apply sum_congr rfl
  intro k hk
  have hp : ∀ a < k, kepStoppedPrefix eps i g a = kepStoppedPrefix eps k g a := by
    intro a ha
    simp only [kepStoppedPrefix, ha, ha.trans (mem_range.mp hk), true_and]
  have he : (k : ℕ∞) < gapSegLen eps (kepStoppedPrefix eps i g) ↔
      (k : ℕ∞) < gapSegLen eps g :=
    (mem_iff_of_measurableSet_comap_seqPrefix (isStoppingRule_gapSegLen eps k) hp).trans
      (kepStoppedPrefix_active eps k g)
  simp only [he]

theorem kepActiveCount_of_stopped {eps : ℝ} {i t : ℕ} {g : ℕ → ℝ}
    (hT : gapSegLen eps g = (t : ℕ∞)) (hti : t ≤ i) : kepActiveCount eps i g = t := by
  classical
  unfold kepActiveCount
  simp only [hT, ENat.natCast_lt_natCast]
  rw [← sum_range_add_sum_Ico _ hti]
  have ha : (∑ k ∈ range t, if k < t then (1 : ℕ) else 0) = t := by
    simp only [sum_congr rfl (fun k hk => if_pos (mem_range.mp hk)), sum_const,
      card_range, smul_eq_mul, mul_one]
  have hb : (∑ k ∈ Ico t i, if k < t then (1 : ℕ) else 0) = 0 :=
    sum_eq_zero fun k hk => if_neg (not_lt.mpr (mem_Ico.mp hk).1)
  rw [ha, hb, add_zero]

def kepExponentialPotential (eps t d : ℝ) (i : ℕ) (g : ℕ → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (t * gapKeys g i - d * kepActiveCount eps i g))

theorem measurable_kepExponentialPotential (eps t d : ℝ) (i : ℕ) :
    Measurable (kepExponentialPotential eps t d i) := by
  have hc : Measurable (fun g => (kepActiveCount eps i g : ℝ)) :=
    (Measurable.of_discrete (f := fun k : ℕ => (k : ℝ))).comp
      (measurable_kepActiveCount eps i)
  exact (((measurable_pi_apply i).comp measurable_gapKeys).const_mul t |>.sub
    (hc.const_mul d)).exp.ennreal_ofReal

theorem kepGapKeys_succ (g : ℕ → ℝ) (i : ℕ) : gapKeys g (i + 1) = gapKeys g i + g i :=
  sum_range_succ _ _

theorem kepGapKeys_update_succ (i : ℕ) (g : ℕ → ℝ) (z : ℝ) :
    gapKeys (Function.update g i z) (i + 1) = gapKeys g i + z := by
  classical
  rw [kepGapKeys_succ, Function.update_self]
  rw [gapKeys_congr (fun k hk => Function.update_of_ne (Nat.ne_of_lt hk) _ _) i le_rfl]

theorem kepExponentialPotential_update (eps t d : ℝ) (i : ℕ) (g : ℕ → ℝ) (z : ℝ)
    (hi : (i : ℕ∞) < gapSegLen eps g) :
    kepExponentialPotential eps t d (i + 1) (Function.update g i z) =
      kepExponentialPotential eps t d i g * ENNReal.ofReal (Real.exp (t * z - d)) := by
  unfold kepExponentialPotential
  rw [kepGapKeys_update_succ, kepActiveCount_update, kepActiveCount_succ, if_pos hi,
    Nat.cast_add, Nat.cast_one, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  congr 2
  ring

theorem kepExponentialPotential_absorbed (eps t d : ℝ) (i : ℕ) (g : ℕ → ℝ)
    (hi : ¬ (i : ℕ∞) < gapSegLen eps g) (hz : g i = 0) :
    kepExponentialPotential eps t d (i + 1) g = kepExponentialPotential eps t d i g := by
  unfold kepExponentialPotential
  rw [kepGapKeys_succ, hz, add_zero, kepActiveCount_succ, if_neg hi, add_zero]

theorem lintegral_kepExponentialPotential_step
    (eps t d : ℝ) (i : ℕ) (kappa : Kernel (ℕ → ℝ) ℝ) [IsMarkovKernel kappa]
    (hbudget : ∀ g, ∫⁻ z, ENNReal.ofReal (Real.exp (t * z - d)) ∂kappa g ≤ 1)
    (g : ℕ → ℝ) (hz : g i = 0) :
    ∫⁻ g', kepExponentialPotential eps t d (i + 1) g'
      ∂absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
        ((isStoppingRule_gapSegLen eps).measurableSet_lt i) kappa i g ≤
      kepExponentialPotential eps t d i g := by
  classical
  rw [absorbingSequenceKernel_apply]
  simp only [mem_ofPred_eq]
  by_cases hi : (i : ℕ∞) < gapSegLen eps g
  · have hu : Measurable (fun z => Function.update g i z) :=
      (measurable_sequenceUpdate i).comp (measurable_const.prodMk measurable_id)
    rw [if_pos hi, lintegral_map (measurable_kepExponentialPotential eps t d (i + 1)) hu]
    simp_rw [kepExponentialPotential_update eps t d i g _ hi]
    rw [lintegral_const_mul _ (by fun_prop)]
    exact (mul_le_mul_right (hbudget g) _).trans_eq (mul_one _)
  · rw [if_neg hi, lintegral_dirac' _ (measurable_kepExponentialPotential eps t d (i + 1)),
      kepExponentialPotential_absorbed eps t d i g hi hz]

theorem lintegral_kepExponentialPotential_prefix_le_one
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (eps t d : ℝ)
    (kappa : ℕ → Kernel (ℕ → ℝ) ℝ) [∀ i, IsMarkovKernel (kappa i)]
    (htrans : ∀ i, P.map (kepStoppedPrefix eps (i + 1)) =
      absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
        ((isStoppingRule_gapSegLen eps).measurableSet_lt i) (kappa i) i ∘ₘ
          P.map (kepStoppedPrefix eps i))
    (hbudget : ∀ i g, ∫⁻ z, ENNReal.ofReal (Real.exp (t * z - d)) ∂kappa i g ≤ 1)
    (i : ℕ) :
    ∫⁻ g, kepExponentialPotential eps t d i g ∂P.map (kepStoppedPrefix eps i) ≤ 1 := by
  induction i with
  | zero =>
    rw [lintegral_map (measurable_kepExponentialPotential eps t d 0)
      (measurable_kepStoppedPrefix eps 0)]
    simp [kepExponentialPotential, gapKeys, kepActiveCount]
  | succ i hi =>
    rw [htrans i, Measure.lintegral_bind
      (absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
        ((isStoppingRule_gapSegLen eps).measurableSet_lt i) (kappa i) i).aemeasurable
      (measurable_kepExponentialPotential eps t d (i + 1)).aemeasurable]
    refine (lintegral_mono_ae ?_).trans hi
    have hz : ∀ᵐ g ∂P.map (kepStoppedPrefix eps i), g i = 0 := by
      apply (ae_map_iff (measurable_kepStoppedPrefix eps i).aemeasurable
        (measurableSet_eq_fun (measurable_pi_apply i) measurable_const)).mpr
      exact Eventually.of_forall fun g => by
        simp only [kepStoppedPrefix, lt_self_iff_false, false_and, if_false]
    filter_upwards [hz] with g hg
    exact lintegral_kepExponentialPotential_step eps t d i (kappa i) (hbudget i) g hg

theorem lintegral_kepExponentialPotential_stopped_le_one
    (P : Measure (ℕ → ℝ)) [IsProbabilityMeasure P] (eps t d : ℝ)
    (kappa : ℕ → Kernel (ℕ → ℝ) ℝ) [∀ i, IsMarkovKernel (kappa i)]
    (htrans : ∀ i, P.map (kepStoppedPrefix eps (i + 1)) =
      absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
        ((isStoppingRule_gapSegLen eps).measurableSet_lt i) (kappa i) i ∘ₘ
          P.map (kepStoppedPrefix eps i))
    (hbudget : ∀ i g, ∫⁻ z, ENNReal.ofReal (Real.exp (t * z - d)) ∂kappa i g ≤ 1)
    (hfin : ∀ᵐ g ∂P, gapSegLen eps g ≠ ⊤) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (t * stopSum eps g -
      d * ((gapSegLen eps g).toNat : ℝ))) ∂P ≤ 1 := by
  let F : ℕ → (ℕ → ℝ) → ℝ≥0∞ := fun i g =>
    kepExponentialPotential eps t d i (kepStoppedPrefix eps i g)
  have hF (i : ℕ) : Measurable (F i) :=
    (measurable_kepExponentialPotential eps t d i).comp (measurable_kepStoppedPrefix eps i)
  have hl : ∫⁻ g, ENNReal.ofReal (Real.exp (t * stopSum eps g -
      d * ((gapSegLen eps g).toNat : ℝ))) ∂P ≤
        liminf (fun i => ∫⁻ g, F i g ∂P) atTop := by
    calc
      _ = ∫⁻ g, liminf (fun i => F i g) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfin] with g hg
        symm
        apply Filter.Tendsto.liminf_eq
        apply tendsto_atTop_of_eventually_const (i₀ := (gapSegLen eps g).toNat)
        intro i hi
        have ht : gapSegLen eps g = ((gapSegLen eps g).toNat : ℕ∞) :=
          (ENat.natCast_toNat hg).symm
        dsimp only [F, kepExponentialPotential]
        rw [kepActiveCount_stoppedPrefix, kepActiveCount_of_stopped ht hi]
        congr 3
        unfold gapKeys stopSum
        rw [← sum_range_add_sum_Ico _ hi]
        have ha : ∑ k ∈ range (gapSegLen eps g).toNat, kepStoppedPrefix eps i g k =
            ∑ k ∈ range (gapSegLen eps g).toNat, g k := by
          apply sum_congr rfl
          intro k hk
          exact if_pos ⟨(mem_range.mp hk).trans_le hi,
            ht ▸ ENat.natCast_lt_natCast.mpr (mem_range.mp hk)⟩
        have hb : ∑ k ∈ Ico (gapSegLen eps g).toNat i, kepStoppedPrefix eps i g k = 0 := by
          apply sum_eq_zero
          intro k hk
          exact if_neg (fun h => (not_lt.mpr (mem_Ico.mp hk).1)
            (ENat.natCast_lt_natCast.mp (ht ▸ h.2)))
        rw [ha, hb, add_zero]
        rfl
      _ ≤ _ := lintegral_liminf_le hF
  refine hl.trans (Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_))
  have h := lintegral_kepExponentialPotential_prefix_le_one P eps t d kappa htrans hbudget i
  rwa [lintegral_map (measurable_kepExponentialPotential eps t d i)
    (measurable_kepStoppedPrefix eps i)] at h

end

end PGM
