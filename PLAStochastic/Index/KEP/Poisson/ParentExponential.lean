import PLAStochastic.Index.KEP.Poisson.ParentOutput
import PLAStochastic.Index.KEP.Poisson.ConditionalCumulant
import PLAStochastic.Index.KEP.StoppedExponentialMoment

/-!
# A fixed exponential moment of the original Poisson parent output

The true absorbing-prefix law and the conditional child cumulant pay the
compensated stopping potential. The actual geometric stopping tail pays its
compensator. The exact parent normalization transfers the resulting moment
to the original hierarchy, without an iid assumption on its gaps.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

theorem kepPoisson_parent_exponential_moment {f : ℝ → ℝ}
    {flo fhi L eps n theta B : ℝ} (hf : KepIntensityProfile f flo fhi L)
    (hn : 0 < n) (htheta : 0 < theta) (x : ℝ) (j : ℕ)
    (heps : kepReferenceClassicalThreshold ≤ eps) (hm : 0 < kepReferenceSpan eps j)
    (hfin : ∀ y, ∀ᵐ g ∂expSeqMeasure, kepPoissonPivot hf eps n y j 1 g ≠ ⊤)
    (hmean : ∀ y, Integrable (fun z : ℝ => z) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, z ∂kepPoissonLayerMeasure hf eps n y j ≤ 2)
    (hexp : ∀ y, Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n y j) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n y j ≤ B)
    (hC : 0 < lawC eps (kepReferenceLaw eps j))
    (hsmall : 2 * theta / lawC eps (kepReferenceLaw eps j) ≤ (theta / (fhi / flo)) / 2)
    (hcost : 8 * B / (theta / (fhi / flo)) ^ 2 *
      (2 * theta / lawC eps (kepReferenceLaw eps j)) ≤ fhi / flo)
    {M : ℕ} (hM : 1 ≤ M)
    (hscale : (3 * (fhi / flo) * (2 * theta / lawC eps (kepReferenceLaw eps j))) * M ≤ 1 / 144)
    (htail : ∀ k : ℕ, expSeqMeasure.real
      {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} ≤
        (1 / 2 : ℝ) ^ k) :
    Integrable (fun z => Real.exp (theta * z)) (kepPoissonLayerMeasure hf eps n x (j + 1)) ∧
      ∫ z, Real.exp (theta * z) ∂kepPoissonLayerMeasure hf eps n x (j + 1) ≤ 73 := by
  let P := expSeqMeasure.map (kepPoissonLayerSequence hf eps n x j)
  let C := lawC eps (kepReferenceLaw eps j)
  let t := 2 * theta / C
  let d := 3 * (fhi / flo) * t
  have hseq := measurable_kepPoissonLayerSequence_anchor hf eps n x j
  have hT := (isStoppingRule_gapSegLen eps).measurable
  have htailP (k : ℕ) : P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} ≤ (71 / 72 : ℝ) ^ k := by
    have he : P.real {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g} = expSeqMeasure.real
        {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps (kepPoissonLayerSequence hf eps n x j g)} := by
      change (P {g | ((k * M : ℕ) : ℕ∞) < gapSegLen eps g}).toReal = _
      rw [Measure.map_apply hseq (tail_measurableSet_lt hT _)]
      rfl
    rw [he]
    exact (htail k).trans (pow_le_pow_left₀ (by norm_num) (by norm_num) k)
  have hfinite : ∀ᵐ g ∂P, gapSegLen eps g ≠ ⊤ :=
    (ae_lt_top_of_tail hT hM (by norm_num) (by norm_num) htailP).mono fun _ h => h.ne
  have hlaw (i : ℕ) : P.map (kepStoppedPrefix eps i) =
      kernelIterateLaw (kepPoissonStoppedPrefixKernel hf eps n x j)
        (Measure.dirac (fun _ => 0)) i := by
    rw [Measure.map_map (measurable_kepStoppedPrefix eps i) hseq]
    exact kepPoisson_stopped_sequence_state_law hf hn.ne' x j i hm.ne' hfin
  have htrans (i : ℕ) : P.map (kepStoppedPrefix eps (i + 1)) =
      absorbingSequenceKernel {g | (i : ℕ∞) < gapSegLen eps g}
        ((isStoppingRule_gapSegLen eps).measurableSet_lt i)
          (kepPoissonPrefixGapKernel hf eps n x j i) i ∘ₘ P.map (kepStoppedPrefix eps i) := by
    rw [hlaw (i + 1), hlaw i]
    rfl
  have hbudget (i : ℕ) (g : ℕ → ℝ) :
      ∫⁻ z, ENNReal.ofReal (Real.exp (t * z - d)) ∂kepPoissonPrefixGapKernel hf eps n x j i g ≤ 1 := by
    rw [kepPoissonPrefixGapKernel, Kernel.comap_apply, kepPoissonParentStepKernel_apply]
    exact kepPoisson_fixed_scale_compensated_exp hf hn htheta j hm.le hmean hexp
      (div_nonneg (mul_nonneg (by norm_num) htheta.le) hC.le) hsmall hcost le_rfl x _
  have hcomp := lintegral_kepExponentialPotential_stopped_le_one P eps t d
    (kepPoissonPrefixGapKernel hf eps n x j) htrans hbudget hfinite
  have hd : 0 ≤ d := mul_nonneg (mul_nonneg (by norm_num)
    (div_nonneg hf.fhi_pos.le hf.pos.le))
      (div_nonneg (mul_nonneg (by norm_num) htheta.le) hC.le)
  obtain ⟨hi, hb⟩ := integral_normalized_stopSum_exp_le_73 P eps theta C d hM hd hscale hcomp htailP
  have hF : Measurable (fun g => stopSum eps g / C) := (measurable_stopSum eps).div_const C
  rw [kepPoissonLayerMeasure_parent_output hf hn x j heps hm]
  refine ⟨(integrable_map_measure (by fun_prop) hF.aemeasurable).mpr hi, ?_⟩
  rw [integral_map hF.aemeasurable (by fun_prop)]
  exact hb

end

end PGM
