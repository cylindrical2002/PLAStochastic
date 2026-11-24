import PLAStochastic.ForMathlib.Probability.OrderStatistics.GammaRatio
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The finite arrival-window density of exponential partial sums

Integrating the first arrival after a fixed positive time leaves the constant
Janossy density exp(-s) on the ordered arrivals before that time. After
normalizing by s the measure is exp(-s) s^k times Lebesgue measure on the closed
ordered simplex. This supplies the actual arrival-process window law.
-/

set_option autoImplicit false

noncomputable section

namespace PGM.Renyi

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

def arrivalWindowCoordinates (k : ℕ) (s : ℝ) (gamma : Fin (k + 1) → ℝ) : Fin k → ℝ :=
  s⁻¹ • fun i => gamma i.castSucc

def arrivalWindowSet (k : ℕ) (s : ℝ) (A : Set (Fin k → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  {gamma | arrivalWindowCoordinates k s gamma ∈ A ∧
    (∀ i : Fin k, gamma i.castSucc ≤ s) ∧ s < gamma (Fin.last k)}

theorem measurable_arrivalWindowCoordinates (k : ℕ) (s : ℝ) :
    Measurable (arrivalWindowCoordinates k s) := by
  exact (measurable_pi_lambda _ fun i : Fin k =>
    (measurable_pi_apply (i.castSucc : Fin (k + 1)))).const_smul s⁻¹

theorem measurableSet_arrivalWindowSet {k : ℕ} (s : ℝ) {A : Set (Fin k → ℝ)}
    (hA : MeasurableSet A) : MeasurableSet (arrivalWindowSet k s A) := by
  have hall : MeasurableSet {gamma : Fin (k + 1) → ℝ | ∀ i : Fin k, gamma i.castSucc ≤ s} := by
    simpa only [Set.ofPred_forall] using
      (MeasurableSet.iInter fun i : Fin k =>
        measurableSet_le (measurable_pi_apply i.castSucc) (measurable_const (a := s)))
  exact ((measurable_arrivalWindowCoordinates k s) hA).inter
    (hall.inter
      (measurableSet_lt measurable_const (measurable_pi_apply (Fin.last k))))

theorem lintegral_exp_neg_Ioi (s : ℝ) :
    ∫⁻ t : ℝ in Ioi s, ENNReal.ofReal (Real.exp (-t)) =
      ENNReal.ofReal (Real.exp (-s)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi s),
    integral_exp_neg_Ioi]
  exact Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le

theorem arrivalWindowSet_snoc_cone {k : ℕ} {s : ℝ} (hs : 0 < s)
    (A : Set (Fin k → ℝ)) (gamma : Fin k → ℝ) (t : ℝ) :
    Fin.snoc gamma t ∈ arrivalWindowSet k s A ∩ cone (k + 1) ↔
      s < t ∧ s⁻¹ • gamma ∈ A ∩ closedSimplex k := by
  simp only [mem_inter_iff, arrivalWindowSet, mem_ofPred_eq, arrivalWindowCoordinates,
    Fin.snoc_castSucc, Fin.snoc_last, snoc_mem_cone_iff,
    inv_smul_mem_closedSimplex_iff hs]
  constructor
  · rintro ⟨⟨hA, hle, hst⟩, hmono, hnn, _, _⟩
    exact ⟨hst, hA, hmono, hnn, hle⟩
  · rintro ⟨hst, hA, hmono, hnn, hle⟩
    exact ⟨⟨hA, hle, hst⟩, hmono, hnn, fun i => (hle i).trans hst.le, hs.le.trans hst.le⟩

theorem coneDensity_arrival_window {k : ℕ} {s : ℝ} (hs : 0 < s)
    {A : Set (Fin k → ℝ)} (hA : MeasurableSet A) :
    (volume.withDensity (coneDensity k)) (arrivalWindowSet k s A) =
      ENNReal.ofReal (Real.exp (-s) * s ^ k) * volume (A ∩ closedSimplex k) := by
  rw [withDensity_apply _ (measurableSet_arrivalWindowSet s hA),
    ← lintegral_indicator (measurableSet_arrivalWindowSet s hA)]
  let F := (arrivalWindowSet k s A).indicator (coneDensity k)
  have hFm : Measurable F :=
    measurable_coneDensity.indicator (measurableSet_arrivalWindowSet s hA)
  let eqv := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) (Fin.last k)).symm
  rw [← h.lintegral_comp_emb eqv.symm.measurableEmbedding F, Measure.volume_eq_prod,
    lintegral_prod (fun p => F (eqv.symm p)) (hFm.comp eqv.symm.measurable).aemeasurable]
  have hsymm (t : ℝ) (gamma : Fin k → ℝ) : eqv.symm (t, gamma) = Fin.snoc gamma t := by
    simp [eqv, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']
  simp_rw [hsymm]
  let B := (fun gamma : Fin k → ℝ => s⁻¹ • gamma) ⁻¹' (A ∩ closedSimplex k)
  have hB : MeasurableSet B :=
    (measurable_const_smul s⁻¹) (hA.inter measurableSet_closedSimplex)
  have hF (t : ℝ) (gamma : Fin k → ℝ) :
      F (Fin.snoc gamma t) =
        (Ioi s).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) t *
          B.indicator (fun _ => (1 : ℝ≥0∞)) gamma := by
    dsimp only [F]
    rw [coneDensity, indicator_indicator]
    by_cases hst : s < t
    · rw [indicator_of_mem (show t ∈ Ioi s from hst)]
      by_cases hg : gamma ∈ B
      · rw [indicator_of_mem hg, mul_one,
          indicator_of_mem ((arrivalWindowSet_snoc_cone hs A gamma t).mpr ⟨hst, hg⟩),
          Fin.snoc_last]
      · rw [indicator_of_notMem hg, mul_zero,
          indicator_of_notMem (fun hmem => hg ((arrivalWindowSet_snoc_cone hs A gamma t).mp hmem).2)]
    · rw [indicator_of_notMem (show t ∉ Ioi s from hst), zero_mul,
        indicator_of_notMem (fun hmem => hst ((arrivalWindowSet_snoc_cone hs A gamma t).mp hmem).1)]
  change (∫⁻ t : ℝ, ∫⁻ gamma : Fin k → ℝ, F (Fin.snoc gamma t)) = _
  have hinner (t : ℝ) :
      (∫⁻ gamma : Fin k → ℝ, F (Fin.snoc gamma t)) =
        (Ioi s).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) t * volume B := by
    simp_rw [hF]
    rw [lintegral_const_mul _ (measurable_const.indicator hB),
      lintegral_indicator_const hB, one_mul]
  simp_rw [hinner]
  have htail : Measurable ((Ioi s).indicator (fun t : ℝ => ENNReal.ofReal (Real.exp (-t)))) := by
    exact (by fun_prop : Measurable (fun t : ℝ => ENNReal.ofReal (Real.exp (-t)))).indicator
      measurableSet_Ioi
  rw [lintegral_mul_const _ htail, lintegral_indicator measurableSet_Ioi, lintegral_exp_neg_Ioi,
    Measure.addHaar_preimage_smul _ (inv_ne_zero hs.ne'), Module.finrank_fin_fun,
    inv_pow, inv_inv, abs_of_pos (pow_pos hs k), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem exponential_arrival_window {k : ℕ} {s : ℝ} (hs : 0 < s)
    {A : Set (Fin k → ℝ)} (hA : MeasurableSet A) :
    (Measure.pi fun _ : Fin (k + 1) => expMeasure 1)
        ((psMap k) ⁻¹' arrivalWindowSet k s A) =
      ENNReal.ofReal (Real.exp (-s) * s ^ k) * volume (A ∩ closedSimplex k) := by
  rw [← Measure.map_apply measurePreserving_psMap.measurable
    (measurableSet_arrivalWindowSet s hA), map_psMap_pi_expMeasure]
  exact coneDensity_arrival_window hs hA

end PGM.Renyi
