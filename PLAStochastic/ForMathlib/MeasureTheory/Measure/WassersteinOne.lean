import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # The Wasserstein-1 distance on the line

For measures `α, β` on `ℝ`, a *coupling* is a measure `π` on `ℝ × ℝ` whose two
marginals are `α` and `β`, and

`W₁(α, β) = inf_π ∫ |x - y| dπ(x, y) ∈ [0, ∞]`.

This file proves the two facts used for observable error bounds:

* `wassersteinOne_lt_top`: two probability measures with first moments are at
  finite `W₁` distance (the product coupling);
* `abs_integral_sub_le_wassersteinOne`: if `α, β` are concentrated on `S`, `W₁(α, β) < ∞`
  and `g` is `L`-Lipschitz on `S` and integrable under both, then
  `|∫ g dα - ∫ g dβ| ≤ L · W₁(α, β)`.

No probability assumption is needed in the second statement: finiteness of `W₁`
already provides a coupling.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace SwingRepair

/-- `π` is a coupling of `α` and `β`: its marginals are `α` and `β`. -/
def IsCoupling (π : Measure (ℝ × ℝ)) (α β : Measure ℝ) : Prop :=
  π.map Prod.fst = α ∧ π.map Prod.snd = β

/-- The Wasserstein-1 distance on `ℝ`, as an infimum over couplings. -/
def wassersteinOne (α β : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (π : Measure (ℝ × ℝ)) (_ : IsCoupling π α β), ∫⁻ p, ‖p.1 - p.2‖ₑ ∂π

variable {α β : Measure ℝ}

theorem wassersteinOne_le_lintegral {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π α β) :
    wassersteinOne α β ≤ ∫⁻ p, ‖p.1 - p.2‖ₑ ∂π :=
  iInf₂_le π hπ

/-- The product of two probability measures is a coupling. -/
theorem isCoupling_prod [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    IsCoupling (α.prod β) α β := by
  constructor
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- A finite `W₁` distance is realised up to finiteness by some coupling. -/
theorem exists_isCoupling_of_wassersteinOne_ne_top (hW : wassersteinOne α β ≠ ⊤) :
    ∃ π : Measure (ℝ × ℝ), IsCoupling π α β ∧ ∫⁻ p, ‖p.1 - p.2‖ₑ ∂π < ⊤ := by
  have h : wassersteinOne α β < ⊤ := lt_top_iff_ne_top.mpr hW
  rw [wassersteinOne, iInf_lt_iff] at h
  obtain ⟨π, hπ⟩ := h
  rw [iInf_lt_iff] at hπ
  obtain ⟨hc, hlt⟩ := hπ
  exact ⟨π, hc, hlt⟩

/-- The product coupling has cost at most the sum of the first absolute moments. -/
theorem lintegral_enorm_sub_prod_le [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    ∫⁻ p, ‖p.1 - p.2‖ₑ ∂(α.prod β) ≤ ∫⁻ x, ‖x‖ₑ ∂α + ∫⁻ y, ‖y‖ₑ ∂β := by
  have hc : IsCoupling (α.prod β) α β := isCoupling_prod
  calc ∫⁻ p, ‖p.1 - p.2‖ₑ ∂(α.prod β) ≤ ∫⁻ p, (‖p.1‖ₑ + ‖p.2‖ₑ) ∂(α.prod β) :=
        lintegral_mono fun p => enorm_sub_le
    _ = ∫⁻ p, ‖p.1‖ₑ ∂(α.prod β) + ∫⁻ p, ‖p.2‖ₑ ∂(α.prod β) :=
        lintegral_add_left measurable_fst.enorm _
    _ = ∫⁻ x, ‖x‖ₑ ∂α + ∫⁻ y, ‖y‖ₑ ∂β := by
        rw [← lintegral_map (f := fun x : ℝ => ‖x‖ₑ) measurable_enorm measurable_fst,
          ← lintegral_map (f := fun x : ℝ => ‖x‖ₑ) measurable_enorm measurable_snd, hc.1, hc.2]

/-- **First moments give a finite `W₁` distance.** -/
theorem wassersteinOne_lt_top [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (hα : Integrable (fun x : ℝ => x) α) (hβ : Integrable (fun x : ℝ => x) β) :
    wassersteinOne α β < ⊤ :=
  (wassersteinOne_le_lintegral isCoupling_prod).trans_lt
    (lintegral_enorm_sub_prod_le.trans_lt
      (ENNReal.add_lt_top.mpr ⟨hα.hasFiniteIntegral, hβ.hasFiniteIntegral⟩))

theorem ae_mem_of_measure_compl_eq_zero {ρ : Measure ℝ} {S : Set ℝ} (h : ρ Sᶜ = 0) :
    ∀ᵐ x ∂ρ, x ∈ S := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp h] with x hx
  simpa using hx

/-- The coupling bound: `‖∫ g dα - ∫ g dβ‖ ≤ L ∫ |x - y| dπ` for one coupling `π`. -/
theorem enorm_integral_sub_le_of_isCoupling {S : Set ℝ} {L : ℝ≥0} {g : ℝ → ℝ}
    {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π α β)
    (hαS : α Sᶜ = 0) (hβS : β Sᶜ = 0) (hg : LipschitzOnWith L g S) (hgm : Measurable g)
    (hgα : Integrable g α) (hgβ : Integrable g β) :
    ‖(∫ x, g x ∂α) - ∫ y, g y ∂β‖ₑ ≤ L * ∫⁻ p, ‖p.1 - p.2‖ₑ ∂π := by
  obtain ⟨h1, h2⟩ := hπ
  have hg1 : Integrable (fun p : ℝ × ℝ => g p.1) π := by
    rw [← h1] at hgα
    exact (integrable_map_measure hgm.aestronglyMeasurable measurable_fst.aemeasurable).mp hgα
  have hg2 : Integrable (fun p : ℝ × ℝ => g p.2) π := by
    rw [← h2] at hgβ
    exact (integrable_map_measure hgm.aestronglyMeasurable measurable_snd.aemeasurable).mp hgβ
  have e1 : ∫ x, g x ∂α = ∫ p, g p.1 ∂π := by
    rw [← h1, integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
  have e2 : ∫ y, g y ∂β = ∫ p, g p.2 ∂π := by
    rw [← h2, integral_map measurable_snd.aemeasurable hgm.aestronglyMeasurable]
  have hS1 : ∀ᵐ p ∂π, p.1 ∈ S := by
    have : ∀ᵐ x ∂(π.map Prod.fst), x ∈ S := by
      rw [h1]; exact ae_mem_of_measure_compl_eq_zero hαS
    exact ae_of_ae_map measurable_fst.aemeasurable this
  have hS2 : ∀ᵐ p ∂π, p.2 ∈ S := by
    have : ∀ᵐ x ∂(π.map Prod.snd), x ∈ S := by
      rw [h2]; exact ae_mem_of_measure_compl_eq_zero hβS
    exact ae_of_ae_map measurable_snd.aemeasurable this
  rw [e1, e2, ← integral_sub hg1 hg2]
  calc ‖∫ p, (g p.1 - g p.2) ∂π‖ₑ ≤ ∫⁻ p, ‖g p.1 - g p.2‖ₑ ∂π :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ p, (L : ℝ≥0∞) * ‖p.1 - p.2‖ₑ ∂π := by
        refine lintegral_mono_ae ?_
        filter_upwards [hS1, hS2] with p hp1 hp2
        have h := hg hp1 hp2
        rwa [edist_eq_enorm_sub, edist_eq_enorm_sub] at h
    _ = L * ∫⁻ p, ‖p.1 - p.2‖ₑ ∂π :=
        lintegral_const_mul _ (measurable_fst.sub measurable_snd).enorm

/-- **The `W₁` bound for Lipschitz observables.**  If `α, β` are concentrated on `S`,
`W₁(α, β) < ∞`, and `g` is measurable, `L`-Lipschitz on `S` and integrable under
both measures, then `|∫ g dα - ∫ g dβ| ≤ L · W₁(α, β)`. -/
theorem abs_integral_sub_le_wassersteinOne {S : Set ℝ} {L : ℝ≥0} {g : ℝ → ℝ}
    (hαS : α Sᶜ = 0) (hβS : β Sᶜ = 0) (hg : LipschitzOnWith L g S) (hgm : Measurable g)
    (hgα : Integrable g α) (hgβ : Integrable g β) (hW : wassersteinOne α β ≠ ⊤) :
    |(∫ x, g x ∂α) - ∫ y, g y ∂β| ≤ L * (wassersteinOne α β).toReal := by
  have hkey : ‖(∫ x, g x ∂α) - ∫ y, g y ∂β‖ₑ ≤ L * wassersteinOne α β := by
    by_cases hL : L = 0
    · obtain ⟨π, hπ, -⟩ := exists_isCoupling_of_wassersteinOne_ne_top hW
      have h := enorm_integral_sub_le_of_isCoupling hπ hαS hβS hg hgm hgα hgβ
      rw [hL, ENNReal.coe_zero, zero_mul] at h
      exact h.trans bot_le
    · have hL' : (L : ℝ≥0∞) ≠ 0 := by exact_mod_cast hL
      rw [wassersteinOne, ENNReal.mul_iInf_of_ne hL' ENNReal.coe_ne_top]
      refine le_iInf fun π => ?_
      rw [ENNReal.mul_iInf_of_ne hL' ENNReal.coe_ne_top]
      exact le_iInf fun hπ => enorm_integral_sub_le_of_isCoupling hπ hαS hβS hg hgm hgα hgβ
  rw [Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_le_iff_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hW)] at hkey
  rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at hkey

end SwingRepair
