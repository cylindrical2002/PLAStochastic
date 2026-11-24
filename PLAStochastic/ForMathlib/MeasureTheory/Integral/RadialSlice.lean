import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Radial slicing of a half-space

The last coordinate is used as a radial variable on `{x : Fin (k + 1) → ℝ | 0 < x (last k)}`:
`x = s • (u, 1)` with `s = x (last k) > 0` and `u = s⁻¹ • init x`. The image of the measure
`s^k ds|_{s > 0} ⊗ du` under `radialMap k (s, u) = s • (u, 1)` is Lebesgue measure on the
half-space (`map_radialMap`). Consequences:

* `lintegral_halfSpace_eq_radial`: `∫⁻_{x_last > 0} F = ∫⁻ u, ∫⁻ s, F (s • (u,1)) ∂(s^k ds)`;
* `integral_eq_radial`: the Bochner version for integrable `G` vanishing off the half-space.

Rays through the origin are the lines `s ↦ s • (u, 1)`, so a cone (a set invariant under
positive dilations) is a union of rays and its indicator does not depend on `s > 0`.
-/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

namespace PGM

variable (k : ℕ)

/-- The radial parametrisation `(s, u) ↦ s • (u, 1) = (s • u, s)`. -/
def radialMap (p : ℝ × (Fin k → ℝ)) : Fin (k + 1) → ℝ := Fin.snoc (p.1 • p.2) p.1

/-- The radial measure `s^k ds` on `(0, ∞)`. -/
def radialMeasure : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ k)

instance : SigmaFinite (radialMeasure k) := by
  unfold radialMeasure; infer_instance

variable {k}

theorem radialMap_eq_smul (s : ℝ) (u : Fin k → ℝ) :
    radialMap k (s, u) = s • (Fin.snoc u 1 : Fin (k + 1) → ℝ) := by
  funext j
  induction j using Fin.lastCases with
  | last => simp [radialMap]
  | cast i => simp [radialMap]

theorem radialMap_last (s : ℝ) (u : Fin k → ℝ) : radialMap k (s, u) (Fin.last k) = s := by
  simp [radialMap]

theorem radial_piFinSuccAbove_symm (s : ℝ) (γ : Fin k → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm (s, γ) =
      Fin.snoc γ s := by
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']

theorem measurable_radialMap : Measurable (radialMap k) := by
  have h := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm.measurable
  have h2 : Measurable fun p : ℝ × (Fin k → ℝ) => (p.1, p.1 • p.2) :=
    measurable_fst.prodMk (measurable_fst.smul measurable_snd)
  have e : radialMap k = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ)
      (Fin.last k)).symm ∘ fun p : ℝ × (Fin k → ℝ) => (p.1, p.1 • p.2) := by
    funext p
    simp only [comp_apply, radial_piFinSuccAbove_symm]
    rfl
  rw [e]
  exact h.comp h2

/-- Lebesgue measure of a set as the integral of the volumes of its slices at fixed last
coordinate. -/
theorem volume_eq_lintegral_slice {B : Set (Fin (k + 1) → ℝ)} (hB : MeasurableSet B) :
    volume B = ∫⁻ s, volume {γ : Fin k → ℝ | (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ B} := by
  let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm
  have hpre : MeasurableSet (eqv.symm ⁻¹' B) := eqv.symm.measurable hB
  rw [← h.measure_preimage hB.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply hpre]
  refine lintegral_congr fun s => ?_
  congr 1
  ext γ
  simp only [mem_preimage, mem_ofPred_eq]
  exact iff_of_eq (congrArg (· ∈ B) (radial_piFinSuccAbove_symm s γ))

/-- **Radial slicing**: `s^k ds|_{s>0} ⊗ du` is carried by `(s, u) ↦ s • (u, 1)` onto
Lebesgue measure on the half-space `{x_last > 0}`. -/
theorem map_radialMap :
    ((radialMeasure k).prod volume).map (radialMap k) =
      volume.restrict {x : Fin (k + 1) → ℝ | 0 < x (Fin.last k)} := by
  have hH : MeasurableSet {x : Fin (k + 1) → ℝ | 0 < x (Fin.last k)} :=
    measurableSet_lt measurable_const (measurable_pi_apply _)
  ext E hE
  have hpre : MeasurableSet (radialMap k ⁻¹' E) := measurable_radialMap hE
  rw [Measure.map_apply measurable_radialMap hE, Measure.prod_apply hpre,
    Measure.restrict_apply hE, volume_eq_lintegral_slice (hE.inter hH)]
  rw [radialMeasure, lintegral_withDensity_eq_lintegral_mul _
    (f := fun s : ℝ => ENNReal.ofReal (s ^ k)) (measurable_id.pow_const k).ennreal_ofReal
    (measurable_measure_prodMk_left hpre)]
  have hz : ∀ s : ℝ, s ≤ 0 →
      volume {γ : Fin k → ℝ | (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ E ∩
        {x | 0 < x (Fin.last k)}} = 0 := by
    intro s hs
    convert measure_empty (μ := (volume : Measure (Fin k → ℝ)))
    ext γ
    simp only [mem_inter_iff, mem_ofPred_eq, Fin.snoc_last, mem_empty_iff_false, iff_false,
      not_and, not_lt]
    exact fun _ => hs
  rw [← lintegral_indicator measurableSet_Ioi]
  have hsplit : (fun s : ℝ => volume {γ : Fin k → ℝ |
      (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ E ∩ {x | 0 < x (Fin.last k)}}) =
      (Ioi (0 : ℝ)).indicator fun s => volume {γ : Fin k → ℝ |
        (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ E} := by
    funext s
    by_cases hs : 0 < s
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
      congr 1
      ext γ
      simp [hs]
    · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs), hz s (not_lt.mp hs)]
  rw [hsplit]
  refine lintegral_congr fun s => ?_
  by_cases hs : 0 < s
  · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs),
      indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs)]
    simp only [Pi.mul_apply]
    have hset : Prod.mk s ⁻¹' (radialMap k ⁻¹' E) =
        (fun u : Fin k → ℝ => s • u) ⁻¹'
          {γ : Fin k → ℝ | (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ E} := by
      ext u
      simp [radialMap]
    have hS : MeasurableSet {γ : Fin k → ℝ | (Fin.snoc γ s : Fin (k + 1) → ℝ) ∈ E} := by
      have h0 := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ)
        (Fin.last k)).symm.measurable.comp (measurable_const.prodMk measurable_id
          (f := fun _ : Fin k → ℝ => s))
      have e : (fun γ : Fin k → ℝ => (Fin.snoc γ s : Fin (k + 1) → ℝ)) =
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm ∘
            fun γ => (s, γ) := by
        funext γ
        exact (radial_piFinSuccAbove_symm s γ).symm
      change MeasurableSet ((fun γ : Fin k → ℝ => (Fin.snoc γ s : Fin (k + 1) → ℝ)) ⁻¹' E)
      rw [e]
      exact h0 hE
    rw [hset, ← Measure.map_apply (measurable_const_smul s) hS,
      Measure.map_addHaar_smul volume hs.ne', Measure.smul_apply, smul_eq_mul,
      Module.finrank_fin_fun, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
      abs_of_pos (inv_pos.mpr (pow_pos hs k)), mul_inv_cancel₀ (pow_pos hs k).ne',
      ENNReal.ofReal_one, one_mul]
  · rw [indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs),
      indicator_of_notMem (show s ∉ Ioi (0 : ℝ) from hs)]

/-- **Radial slicing of lower integrals** over the half-space. -/
theorem lintegral_halfSpace_eq_radial {F : (Fin (k + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x in {x : Fin (k + 1) → ℝ | 0 < x (Fin.last k)}, F x =
      ∫⁻ u : Fin k → ℝ, ∫⁻ s, F (s • (Fin.snoc u 1 : Fin (k + 1) → ℝ)) ∂(radialMeasure k) := by
  rw [← map_radialMap, lintegral_map hF measurable_radialMap,
    lintegral_prod_symm (fun p => F (radialMap k p)) (hF.comp measurable_radialMap).aemeasurable]
  simp_rw [radialMap_eq_smul]

/-- **Radial slicing of integrals**: for `G` integrable and vanishing off the half-space. -/
theorem integral_eq_radial {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : (Fin (k + 1) → ℝ) → E} (hG : Integrable G)
    (h0 : ∀ x : Fin (k + 1) → ℝ, x (Fin.last k) ≤ 0 → G x = 0) :
    ∫ x, G x = ∫ u : Fin k → ℝ, ∫ s, G (s • (Fin.snoc u 1 : Fin (k + 1) → ℝ)) ∂(radialMeasure k) := by
  have hH : MeasurableSet {x : Fin (k + 1) → ℝ | 0 < x (Fin.last k)} :=
    measurableSet_lt measurable_const (measurable_pi_apply _)
  have h1 : ∫ x, G x = ∫ x in {x : Fin (k + 1) → ℝ | 0 < x (Fin.last k)}, G x := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    exact h0 x (not_lt.mp hx)
  have hGr : Integrable G (((radialMeasure k).prod volume).map (radialMap k)) := by
    rw [map_radialMap]; exact hG.restrict
  rw [h1, ← map_radialMap, integral_map measurable_radialMap.aemeasurable hGr.aestronglyMeasurable]
  have hGc : Integrable (fun p => G (radialMap k p)) ((radialMeasure k).prod volume) :=
    (integrable_map_measure hGr.aestronglyMeasurable measurable_radialMap.aemeasurable).mp hGr
  rw [integral_prod_symm (fun p => G (radialMap k p)) hGc]
  simp_rw [radialMap_eq_smul]

end PGM
