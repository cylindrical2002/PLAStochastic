import PLAStochastic.Index.KEP.Poisson.WindowHeightReadout
import PLAStochastic.Index.KEP.Poisson.LayerArrivalSpan

/-!
# The original Poisson window block event is bracketed by true layer spans

The event of a leading block crossing the actual window is compared with
the same normalized layer-gap law proved in the uniform induction. Density
ratio bounds pay both event inclusions, including every physical anchor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Renyi
open scoped ENNReal unitInterval Nat

theorem kepPoissonWindow_span_event_bounds {f : ℝ → ℝ} {A B flo fhi L eps u : ℝ}
    (hf : DensityK f A B flo fhi L) (heps : 1 / 2 ≤ eps) {ell : ℕ} (hell : 1 ≤ ell)
    (hm : 0 < kepReferenceSpan eps ell) (M : ℕ) (p : I)
    (hM : 0 < (M : ℝ)) (hp : 0 < (p : ℝ)) (hu0 : 0 ≤ u) (hu1 : u < 1)
    (hfin : ∀ᵐ g ∂expSeqMeasure,
      kepPoissonPivot (kepExtendedDensity_profile hf) eps (M / (1 - u))
        (quantK f A B u) ell 1 g ≠ ⊤) :
    (poissonWindow M p).real (tailEvent eps (quantK f A B) u ell) ≤
        (kepPoissonLayerMeasure (kepExtendedDensity_profile hf) eps (M / (1 - u))
          (quantK f A B u) ell).real
            {z | (flo / fhi) * ((M * p) / kepReferenceSpan eps ell) ≤ z} ∧
      (kepPoissonLayerMeasure (kepExtendedDensity_profile hf) eps (M / (1 - u))
        (quantK f A B u) ell).real
          {z | (fhi / flo) * ((M * p) / kepReferenceSpan eps ell) < z} ≤
        (poissonWindow M p).real (tailEvent eps (quantK f A B) u ell) := by
  have hn : 0 < (M : ℝ) / (1 - u) := div_pos hM (sub_pos.mpr hu1)
  have hprofile := kepExtendedDensity_profile hf
  have hR : 0 < fhi / flo := div_pos hprofile.fhi_pos hprofile.pos
  have hRinv : 0 < flo / fhi := div_pos hprofile.pos hprofile.fhi_pos
  have hgAE : ∀ᵐ g ∂expSeqMeasure, ∀ i, 0 ≤ g i := by
    refine ae_all_iff.mpr fun i => ?_
    exact (iidSeq_expCoord.ae_pos_of_expMeasure_one (hasLaw_expCoord 0) i).mono fun g hg => hg.le
  rw [kepPoissonWindow_actual_event M p hM hp
    (measurableSet_tailEvent eps (measurable_quantK hf) u ell)]
  change expSeqMeasure.real _ ≤
      (expSeqMeasure.map (kepPoissonLayerGap hprofile eps (M / (1 - u))
        (quantK f A B u) ell)).real _ ∧
    (expSeqMeasure.map (kepPoissonLayerGap hprofile eps (M / (1 - u))
      (quantK f A B u) ell)).real _ ≤ expSeqMeasure.real _
  have hgapMeas : Measurable (kepPoissonLayerGap hprofile eps (M / (1 - u))
      (quantK f A B u) ell) :=
    (measurable_kepPoissonLayerGap hprofile eps (M / (1 - u)) ell).comp
      (measurable_const.prodMk measurable_id)
  have hupperSet : MeasurableSet
      {z : ℝ | (flo / fhi) * ((M * p) / kepReferenceSpan eps ell) ≤ z} := measurableSet_Ici
  have hlowerSet : MeasurableSet
      {z : ℝ | (fhi / flo) * ((M * p) / kepReferenceSpan eps ell) < z} := measurableSet_Ioi
  rw [map_measureReal_apply hgapMeas hupperSet, map_measureReal_apply hgapMeas hlowerSet]
  constructor
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hgAE, kepArrivalCount_ae_spec (mul_pos hM hp), hfin] with g hg hcount hfinite
    intro hevent
    have ht := (kepPoissonWindow_tailEvent_iff hf hM hu0 hu1 hp p.property.2 heps hell hg hcount).mp hevent
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hr' := hr.symm
    have hNr : kepArrivalCount ((M : ℝ) * p) g < r := by
      rw [hr'] at ht
      exact ENat.natCast_lt_natCast.mp ht
    have hsum : (M : ℝ) * p ≤ gapKeys g r :=
      hcount.2.le.trans (gapKeys_mono hg (Nat.succ_le_of_lt hNr))
    have hb := (kepPoissonLayerGap_arrival_bracket hprofile hn ell hm hg hr').1
    exact le_trans (by gcongr) hb
  · apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono_ae
    filter_upwards [hgAE, kepArrivalCount_ae_spec (mul_pos hM hp), hfin] with g hg hcount hfinite
    intro hspan
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hfinite
    have hr' := hr.symm
    have hb := (kepPoissonLayerGap_arrival_bracket hprofile hn ell hm hg hr').2
    have hsum : (M : ℝ) * p < gapKeys g r := by
      have h := hspan.trans_le hb
      exact (div_lt_div_iff_of_pos_right hm).mp ((mul_lt_mul_iff_right₀ hR).mp h)
    have hNr : kepArrivalCount ((M : ℝ) * p) g < r := by
      by_contra h
      have hrN := not_lt.mp h
      rcases Nat.eq_zero_or_pos r with rfl | hr0
      · simp only [gapKeys, Finset.sum_range_zero] at hsum
        exact (not_lt.mpr (mul_pos hM hp).le) hsum
      · have hle : gapKeys g r ≤ (M : ℝ) * p := by
          simpa only [Nat.sub_add_cancel hr0] using hcount.1 ⟨r - 1, by omega⟩
        exact (not_lt.mpr hle) hsum
    apply (kepPoissonWindow_tailEvent_iff hf hM hu0 hu1 hp p.property.2 heps hell hg hcount).mpr
    rw [hr']
    exact ENat.natCast_lt_natCast.mpr hNr

end

end PGM
