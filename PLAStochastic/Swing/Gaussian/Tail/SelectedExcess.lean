import PLAStochastic.Swing.Gaussian.StripExit.Walk
import PLAStochastic.Swing.Gaussian.Tail.ExcessMoments

/-! Genuine Gaussian excess bounds at a past-measurable random threshold. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

/-- Exact joint law after restricting to a past event. The fresh increment is not selected yet. -/
theorem past_freshGaussian_restrict_jointLaw [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {Z : Ω → ℝ}
    (hZ : Measurable Z) (hG : μ.map Z = gaussianReal 0 1)
    (hi : Indep (MeasurableSpace.comap Z inferInstance) m μ)
    {α : Type*} [MeasurableSpace α] {Y : Ω → α} (hY : Measurable[m] Y)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    (μ.restrict A).map (fun ω => (Y ω, Z ω)) =
      ((μ.restrict A).map Y).prod (gaussianReal 0 1) := by
  have hYm : Measurable Y := hY.mono hm le_rfl
  apply (Measure.prod_eq fun s t hs ht => ?_).symm
  rw [Measure.map_apply (hYm.prodMk hZ) (hs.prod ht), Measure.map_apply hYm hs,
    Measure.restrict_apply ((hYm.prodMk hZ) (hs.prod ht)), Measure.restrict_apply (hYm hs)]
  have hind := (Indep_iff _ _ μ).mp hi (Z ⁻¹' t) (A ∩ Y ⁻¹' s)
    (show MeasurableSet[MeasurableSpace.comap Z inferInstance] (Z ⁻¹' t) from ⟨t, ht, rfl⟩)
    (hA.inter (hY hs))
  have hz : μ (Z ⁻¹' t) = gaussianReal 0 1 t := by rw [← hG, Measure.map_apply hZ ht]
  rw [hz] at hind
  calc
    _ = μ (Z ⁻¹' t ∩ (A ∩ Y ⁻¹' s)) := by
      congr 1
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_prod]
      tauto
    _ = _ := by rw [hind, inter_comm A, mul_comm]

/-- Undo the actual conditioning normalization in the Gaussian excess law. -/
theorem gaussianExcessLaw_lintegral_restrict (r : ℝ) {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ z in Ioi r, f (z-r) ∂gaussianReal 0 1) =
      gaussianReal 0 1 (Ioi r) * ∫⁻ u, f u ∂gaussianExcessLaw r := by
  rw [gaussianExcessLaw, lintegral_map hf (by fun_prop), ProbabilityTheory.cond,
    lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (gaussianReal_Ioi_pos r).ne' (measure_ne_top _ _), one_mul]

/-- The actual random-threshold excess integral is a mixture of deterministic Gaussian tails. -/
theorem past_freshGaussian_excess_lintegral [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {Z r : Ω → ℝ}
    (hZ : Measurable Z) (hG : μ.map Z = gaussianReal 0 1)
    (hi : Indep (MeasurableSpace.comap Z inferInstance) m μ)
    (hr : Measurable[m] r) {A : Set Ω} (hA : MeasurableSet[m] A)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ ω in A ∩ {ω | r ω < Z ω}, f (Z ω-r ω) ∂μ) =
      ∫⁻ v, ∫⁻ z in Ioi v, f (z-v) ∂gaussianReal 0 1 ∂(μ.restrict A).map r := by
  have hrm : Measurable r := hr.mono hm le_rfl
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => if p.1 < p.2 then f (p.2-p.1) else 0
  have hF : Measurable F :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
      (hf.comp (measurable_snd.sub measurable_fst)) measurable_const
  have he := congrArg (fun ρ : Measure (ℝ × ℝ) => ∫⁻ p, F p ∂ρ)
    (past_freshGaussian_restrict_jointLaw hm hZ hG hi hr hA)
  rw [lintegral_map hF (hrm.prodMk hZ), lintegral_prod _ hF.aemeasurable] at he
  have hl : (∫⁻ ω, F (r ω, Z ω) ∂μ.restrict A) =
      ∫⁻ ω in A ∩ {ω | r ω < Z ω}, f (Z ω-r ω) ∂μ := by
    change (∫⁻ ω, ({ω | r ω < Z ω}).indicator (fun ω => f (Z ω-r ω)) ω ∂μ.restrict A) = _
    rw [lintegral_indicator (measurableSet_lt hrm hZ),
      Measure.restrict_restrict (measurableSet_lt hrm hZ), inter_comm]
  rw [hl] at he
  refine he.trans ?_
  apply lintegral_congr
  intro v
  change (∫⁻ z, (Ioi v).indicator (fun z => f (z-v)) z ∂gaussianReal 0 1) = _
  exact lintegral_indicator measurableSet_Ioi _

/-- A uniform conditional excess bound survives arbitrary measurable selection of the past threshold. -/
theorem past_freshGaussian_excess_lintegral_le [IsProbabilityMeasure μ]
    (hm : m ≤ mΩ) {Z r : Ω → ℝ}
    (hZ : Measurable Z) (hG : μ.map Z = gaussianReal 0 1)
    (hi : Indep (MeasurableSpace.comap Z inferInstance) m μ)
    (hr : Measurable[m] r) {A : Set Ω} (hA : MeasurableSet[m] A)
    (hthreshold : ∀ ω ∈ A, -(1/2 : ℝ) ≤ r ω)
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hb : ∀ v : ℝ, -(1/2 : ℝ) ≤ v → (∫⁻ u, f u ∂gaussianExcessLaw v) ≤ C) :
    (∫⁻ ω in A ∩ {ω | r ω < Z ω}, f (Z ω-r ω) ∂μ) ≤
      C * μ (A ∩ {ω | r ω < Z ω}) := by
  have he := past_freshGaussian_excess_lintegral hm hZ hG hi hr hA hf
  have hone := past_freshGaussian_excess_lintegral hm hZ hG hi hr hA
    (f := fun _ => (1 : ℝ≥0∞)) measurable_const
  simp only [lintegral_one, Measure.restrict_apply_univ] at hone
  rw [he, hone, ← lintegral_const_mul' C _ hC]
  apply lintegral_mono_ae
  have hrm : Measurable r := hr.mono hm le_rfl
  have hth : ∀ᵐ v ∂(μ.restrict A).map r, -(1/2 : ℝ) ≤ v := by
    apply (ae_map_iff hrm.aemeasurable measurableSet_Ici).mpr
    filter_upwards [ae_restrict_mem (hm _ hA)] with ω hω
    exact hthreshold ω hω
  filter_upwards [hth] with v hv
  rw [gaussianExcessLaw_lintegral_restrict v hf, mul_comm C]
  exact mul_le_mul_right (hb v hv) _

end SwingRepair
