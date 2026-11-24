import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# WP5: measurable quantile transport

The inverse is defined jointly in a distribution parameter and a uniform input.
Values outside `(0,1)` are set to zero; all distributional identities use Lebesgue
measure restricted to `(0,1)`, so this convention has no effect on the coupling.
-/

namespace PGM

noncomputable section

open MeasureTheory Measure ProbabilityTheory Set Filter Topology

/-- The regularity needed for the quantile of an everywhere positive density. -/
structure SACDF (F : ℝ → ℝ) : Prop where
  continuous : Continuous F
  strictMono : StrictMono F
  atBot : Tendsto F Filter.atBot (𝓝 0)
  atTop : Tendsto F Filter.atTop (𝓝 1)

theorem SACDF.mem_range {F : ℝ → ℝ} (hF : SACDF F) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    u ∈ range F := by
  have h := isPreconnected_univ.intermediate_value_Ioo
    (by simp : (Filter.atBot : Filter ℝ) ≤ 𝓟 (univ : Set ℝ))
    (by simp : (Filter.atTop : Filter ℝ) ≤ 𝓟 (univ : Set ℝ))
    hF.continuous.continuousOn hF.atBot hF.atTop hu
  simpa only [image_univ] using h

theorem SACDF.mem_Ioo {F : ℝ → ℝ} (hF : SACDF F) (x : ℝ) : F x ∈ Ioo 0 1 := by
  have hlo : 0 ≤ F (x - 1) := le_of_tendsto hF.atBot
    (eventually_atBot.mpr ⟨x - 1, fun y hy => hF.strictMono.monotone hy⟩)
  have hhi : F (x + 1) ≤ 1 := ge_of_tendsto hF.atTop
    (eventually_atTop.mpr ⟨x + 1, fun y hy => hF.strictMono.monotone hy⟩)
  exact ⟨lt_of_le_of_lt hlo (hF.strictMono (by linarith)),
    lt_of_lt_of_le (hF.strictMono (by linarith)) hhi⟩

/-- A total inverse with a fixed convention off the probability interval. -/
def saQuantile (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  if u ∈ Ioo 0 1 then Function.invFun F u else 0

theorem SACDF.apply_quantile {F : ℝ → ℝ} (hF : SACDF F) {u : ℝ}
    (hu : u ∈ Ioo 0 1) : F (saQuantile F u) = u := by
  rw [saQuantile, if_pos hu]
  exact Function.invFun_eq (hF.mem_range hu)

theorem SACDF.quantile_le_iff {F : ℝ → ℝ} (hF : SACDF F) {u x : ℝ}
    (hu : u ∈ Ioo 0 1) : saQuantile F u ≤ x ↔ u ≤ F x := by
  rw [← hF.apply_quantile hu, hF.strictMono.le_iff_le]
  rw [hF.apply_quantile hu]

theorem SACDF.le_quantile_iff {F : ℝ → ℝ} (hF : SACDF F) {u x : ℝ}
    (hu : u ∈ Ioo 0 1) : x ≤ saQuantile F u ↔ F x ≤ u := by
  rw [← hF.apply_quantile hu, hF.strictMono.le_iff_le]
  rw [hF.apply_quantile hu]

/-- Joint measurability follows from the exact sublevel identity. -/
theorem measurable_saQuantile {A : Type*} [MeasurableSpace A] {F : A → ℝ → ℝ}
    (hF : ∀ a, SACDF (F a)) (hm : ∀ x, Measurable (fun a => F a x)) :
    Measurable (fun p : A × ℝ => saQuantile (F p.1) p.2) := by
  apply measurable_of_Iic
  intro x
  have he : (fun p : A × ℝ => saQuantile (F p.1) p.2) ⁻¹' Iic x =
      {p | p.2 ∈ Ioo 0 1 ∧ p.2 ≤ F p.1 x} ∪
        {p | p.2 ∉ Ioo 0 1 ∧ 0 ≤ x} := by
    ext p
    by_cases hu : p.2 ∈ Ioo 0 1
    · simp only [mem_preimage, mem_Iic, mem_union, mem_ofPred_eq, hu, true_and,
        not_true_eq_false, false_and, or_false]
      exact (hF p.1).quantile_le_iff hu
    · simp only [mem_preimage, mem_Iic, mem_union, mem_ofPred_eq, hu,
        false_and, not_false_eq_true, true_and, false_or, saQuantile, if_false]
  rw [he]
  have hc : MeasurableSet ({p : A × ℝ | (0 : ℝ) ≤ x}) := by
    by_cases hx : (0 : ℝ) ≤ x
    · convert MeasurableSet.univ (α := A × ℝ) using 1
      ext p
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact hx
    · convert MeasurableSet.empty (α := A × ℝ) using 1
      ext p
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact hx
  exact ((measurableSet_Ioo.preimage measurable_snd).inter
    (measurableSet_le measurable_snd ((hm x).comp measurable_fst))).union
      ((measurableSet_Ioo.preimage measurable_snd).compl.inter hc)

theorem SACDF.measurable_quantile {F : ℝ → ℝ} (hF : SACDF F) : Measurable (saQuantile F) := by
  exact (measurable_saQuantile (F := fun _ : Unit => F) (fun _ => hF)
    (fun _ => measurable_const)).comp
      ((measurable_const : Measurable (fun _ : ℝ => ())).prodMk measurable_id)

/-- A deterministic CDF sandwich gives an explicit quantile error bound. -/
theorem SACDF.quantile_error_le {F : ℝ → ℝ} (hF : SACDF F) {u c δ : ℝ}
    (hu : u ∈ Ioo 0 1) (hlo : F (c - δ) ≤ u) (hhi : u ≤ F (c + δ)) :
    |saQuantile F u - c| ≤ δ := by
  have hl := (hF.le_quantile_iff hu).2 hlo
  have hh := (hF.quantile_le_iff hu).2 hhi
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Every atomless distribution with full support has a regular CDF. -/
theorem saCDF_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] [NullSingletonClass μ]
    [IsOpenPosMeasure μ] : SACDF (cdf μ) := by
  refine ⟨?_, ?_, tendsto_cdf_atBot μ, tendsto_cdf_atTop μ⟩
  · apply continuous_iff_continuousAt.mpr
    intro x
    apply (monotone_cdf μ).continuousAt_iff_leftLim_eq_rightLim.mpr
    rw [(cdf μ).rightLim_eq]
    have hs := (cdf μ).measure_singleton x
    rw [measure_cdf, measure_singleton, eq_comm, ENNReal.ofReal_eq_zero] at hs
    have hl := (monotone_cdf μ).leftLim_le (le_refl x)
    linarith
  · intro x y hxy
    have hp : 0 < μ (Ioc x y) :=
      (measure_Ioo_pos μ |>.mpr hxy).trans_le (measure_mono Ioo_subset_Ioc_self)
    rw [← measure_cdf μ, (cdf μ).measure_Ioc, ENNReal.ofReal_pos] at hp
    linarith

/-- Lebesgue measure on the open unit interval, used as the innovation law. -/
def saUniform : Measure ℝ := volume.restrict (Ioo 0 1)

instance : IsProbabilityMeasure saUniform := by
  constructor
  simp [saUniform]

/-- Inverse transform sampling, including exact equality of probability measures. -/
theorem saQuantile_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : SACDF (cdf μ)) : saUniform.map (saQuantile (cdf μ)) = μ := by
  apply Measure.ext_of_Iic
  intro x
  rw [Measure.map_apply hF.measurable_quantile measurableSet_Iic,
    saUniform, Measure.restrict_apply (hF.measurable_quantile measurableSet_Iic)]
  have he : saQuantile (cdf μ) ⁻¹' Iic x ∩ Ioo 0 1 = Ioc 0 (cdf μ x) := by
    ext u
    constructor
    · rintro ⟨hu, hu0⟩
      exact ⟨hu0.1, (hF.quantile_le_iff hu0).mp hu⟩
    · rintro ⟨hu0, hux⟩
      have hu1 : u < 1 := hux.trans_lt (hF.mem_Ioo x).2
      exact ⟨(hF.quantile_le_iff ⟨hu0, hu1⟩).mpr hux, hu0, hu1⟩
  rw [he, Real.volume_Ioc, sub_zero, ofReal_cdf]

/-- The probability integral transform for a continuous strictly increasing CDF. -/
theorem saCDF_map_uniform (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hF : SACDF (cdf μ)) : μ.map (cdf μ) = saUniform := by
  calc
    μ.map (cdf μ) = (saUniform.map (saQuantile (cdf μ))).map (cdf μ) := by
      rw [saQuantile_map_uniform μ hF]
    _ = saUniform.map ((cdf μ) ∘ saQuantile (cdf μ)) :=
      Measure.map_map hF.continuous.measurable hF.measurable_quantile
    _ = saUniform.map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
      exact hF.apply_quantile hu
    _ = saUniform := Measure.map_id

/-- Quantile transport sends one regular distribution exactly to another. -/
theorem saQuantile_transport (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : SACDF (cdf μ)) (hν : SACDF (cdf ν)) :
    ν.map (fun z => saQuantile (cdf μ) (cdf ν z)) = μ := by
  change ν.map (saQuantile (cdf μ) ∘ (cdf ν)) = μ
  rw [← Measure.map_map hμ.measurable_quantile hν.continuous.measurable,
    saCDF_map_uniform ν hν, saQuantile_map_uniform μ hμ]

/-- The monotone pair is an actual coupling with both exact marginals. -/
theorem saQuantile_coupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : SACDF (cdf μ)) (hν : SACDF (cdf ν)) :
    let π := ν.map (fun z => (saQuantile (cdf μ) (cdf ν z), z))
    IsProbabilityMeasure π ∧ π.map Prod.fst = μ ∧ π.map Prod.snd = ν := by
  have hm : Measurable (fun z => (saQuantile (cdf μ) (cdf ν z), z)) :=
    (hμ.measurable_quantile.comp hν.continuous.measurable).prodMk measurable_id
  refine ⟨isProbabilityMeasure_map hm.aemeasurable, ?_, ?_⟩
  · rw [Measure.map_map measurable_fst hm]
    exact saQuantile_transport μ ν hμ hν
  · rw [Measure.map_map measurable_snd hm]
    exact Measure.map_id

end

end PGM
