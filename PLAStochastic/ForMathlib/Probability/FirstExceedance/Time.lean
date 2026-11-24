import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# First exceedance times of continuous approximation errors

Times take values in the nonnegative extended reals, so a path which never
exceeds the budget has lifetime infinity. No finiteness assumption is hidden
in the definition or the tail identity.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace BrownianAffine

noncomputable section

def firstExceedance (D : ℝ≥0 → ℝ) (ε : ℝ) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if ε < D t then (t : ℝ≥0∞) else ⊤

theorem firstExceedance_le_of_exceeds {D : ℝ≥0 → ℝ} {ε : ℝ} {t : ℝ≥0}
    (ht : ε < D t) : firstExceedance D ε ≤ (t : ℝ≥0∞) := by
  exact (iInf_le _ t).trans_eq (if_pos ht)

theorem le_firstExceedance_of_error_le {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hD : Monotone D) {t : ℝ≥0} (ht : D t ≤ ε) :
    (t : ℝ≥0∞) ≤ firstExceedance D ε := by
  apply le_iInf
  intro s
  split_ifs with hs
  · exact_mod_cast (show t ≤ s by
      by_contra h
      exact (not_lt_of_ge ((hD (le_of_not_ge h)).trans ht)) hs)
  · exact le_top

/-- Continuity prevents an exceedance from first occurring strictly at a positive time. -/
theorem exists_earlier_exceedance {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hD : Continuous D) (hzero : D 0 ≤ ε) {t : ℝ≥0} (ht : ε < D t) :
    ∃ s : ℝ≥0, s < t ∧ ε < D s := by
  have hmid : (ε + D t) / 2 ∈ Icc (D 0) (D t) := by constructor <;> linarith
  obtain ⟨s, hs, heq⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from bot_le)
    hD.continuousOn hmid
  refine ⟨s, lt_of_le_of_ne hs.2 ?_, ?_⟩
  · intro hst
    subst s
    linarith
  · linarith

/-- Exact closed tails, including time zero and paths of infinite lifetime. -/
theorem le_firstExceedance_iff {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hmono : Monotone D) (hcont : Continuous D) (hzero : D 0 ≤ ε) (t : ℝ≥0) :
    (t : ℝ≥0∞) ≤ firstExceedance D ε ↔ D t ≤ ε := by
  constructor
  · intro ht
    by_contra h
    obtain ⟨s, hst, hs⟩ := exists_earlier_exceedance hcont hzero (lt_of_not_ge h)
    have hts : (t : ℝ≥0∞) ≤ s := ht.trans (firstExceedance_le_of_exceeds hs)
    have : t ≤ s := by exact_mod_cast hts
    exact (not_le_of_gt hst) this
  · exact le_firstExceedance_of_error_le hmono

/-- The smaller error process has the later first exceedance. -/
theorem firstExceedance_antitone_error {D E : ℝ≥0 → ℝ} {ε : ℝ}
    (hDE : ∀ t, D t ≤ E t) : firstExceedance E ε ≤ firstExceedance D ε := by
  apply le_iInf
  intro t
  split_ifs with ht
  · exact firstExceedance_le_of_exceeds (ht.trans_le (hDE t))
  · exact le_top

theorem upperSemicontinuous_exceedance_indicator {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hD : Continuous D) :
    UpperSemicontinuous (fun t : ℝ≥0 => if ε < D t then (t : ℝ≥0∞) else ⊤) := by
  rw [upperSemicontinuous_iff_isOpen_preimage]
  intro a
  have heq : {t : ℝ≥0 | (if ε < D t then (t : ℝ≥0∞) else ⊤) < a} =
      {t | ε < D t} ∩ {t | (t : ℝ≥0∞) < a} := by
    ext t
    by_cases ht : ε < D t <;> simp [ht]
  change IsOpen {t : ℝ≥0 | (if ε < D t then (t : ℝ≥0∞) else ⊤) < a}
  rw [heq]
  exact (isOpen_lt continuous_const hD).inter
    (isOpen_lt ENNReal.continuous_coe continuous_const)

/-- Separability of time and continuous paths make the uncountable infimum measurable. -/
theorem measurable_firstExceedance {Ω : Type*} [MeasurableSpace Ω]
    {D : ℝ≥0 → Ω → ℝ} (hD : ∀ t, Measurable (D t))
    (hcont : ∀ ω, Continuous (fun t => D t ω)) (ε : ℝ) :
    Measurable (fun ω => firstExceedance (fun t => D t ω) ε) := by
  have hm : Measurable (⨅ t : ℝ≥0, fun ω => if ε < D t ω then (t : ℝ≥0∞) else ⊤) := by
    apply measurable_iInf_of_upperSemicontinuous
    · intro t
      exact Measurable.ite (measurableSet_lt measurable_const (hD t))
        measurable_const measurable_const
    · intro ω
      exact upperSemicontinuous_exceedance_indicator (hcont ω)
  convert hm using 1
  funext ω
  simp only [iInf_apply, firstExceedance]

/-- A strict initial error margin gives a positive lifetime, without assuming finiteness. -/
theorem firstExceedance_pos {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hmono : Monotone D) (hcont : Continuous D) (hzero : D 0 < ε) :
    0 < firstExceedance D ε := by
  by_cases hone : D 1 ≤ ε
  · exact lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < (1 : ℝ≥0))
      (le_firstExceedance_of_error_le hmono hone)
  · have hmid : (D 0 + ε) / 2 ∈ Icc (D 0) (D 1) := by constructor <;> linarith
    obtain ⟨s, _, hs⟩ := intermediate_value_Icc (show (0 : ℝ≥0) ≤ 1 by norm_num)
      hcont.continuousOn hmid
    have hspos : 0 < s := by
      by_contra h
      have heq : s = 0 := le_antisymm (le_of_not_gt h) bot_le
      rw [heq] at hs
      linarith
    exact lt_of_lt_of_le (by exact_mod_cast hspos)
      (le_firstExceedance_of_error_le hmono (by linarith : D s ≤ ε))

/-- Positive amplitude changes are equivalent to changing the error budget. -/
theorem firstExceedance_amplitude (D : ℝ≥0 → ℝ) (ε : ℝ) {c : ℝ} (hc : 0 < c) :
    firstExceedance (fun t => c * D t) ε = firstExceedance D (ε / c) := by
  simp only [firstExceedance, div_lt_iff₀ hc, mul_comm]

/-- A dense set of observation times computes the exact first exceedance, by continuity. -/
theorem firstExceedance_eq_iInf_dense {D : ℝ≥0 → ℝ} {ε : ℝ}
    (hD : Continuous D) {S : Set ℝ≥0} (hS : Dense S) :
    firstExceedance D ε = ⨅ t : S, if ε < D t then (t.val : ℝ≥0∞) else ⊤ := by
  apply le_antisymm
  · apply le_iInf
    intro t
    exact iInf_le _ t.val
  · apply le_iInf
    intro t
    split_ifs with ht
    · by_contra h
      let L : ℝ≥0∞ := ⨅ s : S, if ε < D s then (s.val : ℝ≥0∞) else ⊤
      have hlt : (t : ℝ≥0∞) < L := lt_of_not_ge h
      have hopen : IsOpen {s : ℝ≥0 | ε < D s ∧ (s : ℝ≥0∞) < L} :=
        (isOpen_lt continuous_const hD).inter
          (isOpen_lt ENNReal.continuous_coe continuous_const)
      obtain ⟨s, hs, hsS⟩ := hS.inter_open_nonempty _ hopen ⟨t, ht, hlt⟩
      have hbound : L ≤ (s : ℝ≥0∞) :=
        (iInf_le _ (⟨s, hsS⟩ : S)).trans_eq (if_pos hs.1)
      exact (not_lt_of_ge hbound) hs.2
    · exact le_top

/-- Coordinatewise a.e. measurability suffices; no measurable path-space map is assumed. -/
theorem aemeasurable_firstExceedance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : ℝ≥0 → Ω → ℝ} (hD : ∀ t, AEMeasurable (D t) μ)
    (hcont : ∀ ω, Continuous (fun t => D t ω)) (ε : ℝ) :
    AEMeasurable (fun ω => firstExceedance (fun t => D t ω) ε) μ := by
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  let : Countable S := hScount.to_subtype
  have hm : AEMeasurable (fun ω => ⨅ t : S,
      if ε < D t ω then (t.val : ℝ≥0∞) else ⊤) μ := by
    apply AEMeasurable.iInf
    intro t
    have hg : Measurable (fun x : ℝ => if ε < x then (t.val : ℝ≥0∞) else ⊤) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_id)
        measurable_const measurable_const
    exact hg.comp_aemeasurable (hD t)
  convert hm using 1
  funext ω
  exact firstExceedance_eq_iInf_dense (hcont ω) hSdense

/-- Rescaling time multiplies the lifetime by the inverse scale, even for infinite lifetimes. -/
theorem firstExceedance_dilate_mul (D : ℝ≥0 → ℝ) (ε : ℝ) {c : ℝ≥0} (hc : c ≠ 0) :
    (c : ℝ≥0∞) * firstExceedance (fun t => D (c * t)) ε = firstExceedance D ε := by
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
  rw [firstExceedance, ENNReal.mul_iInf_of_ne hc' ENNReal.coe_ne_top]
  calc
    (⨅ t : ℝ≥0, (c : ℝ≥0∞) * (if ε < D (c * t) then (t : ℝ≥0∞) else ⊤)) =
        ⨅ t : ℝ≥0, if ε < D (c * t) then ((c * t : ℝ≥0) : ℝ≥0∞) else ⊤ := by
      congr 1
      funext t
      split_ifs <;> simp [ENNReal.coe_mul, hc']
    _ = firstExceedance D ε :=
      (mulLeft_bijective₀ c hc).surjective.iInf_comp
        (fun t : ℝ≥0 => if ε < D t then (t : ℝ≥0∞) else ⊤)

theorem firstExceedance_dilate (D : ℝ≥0 → ℝ) (ε : ℝ) {c : ℝ≥0} (hc : c ≠ 0) :
    firstExceedance (fun t => D (c * t)) ε = firstExceedance D ε / (c : ℝ≥0∞) :=
  (ENNReal.eq_div_iff (by exact_mod_cast hc) ENNReal.coe_ne_top).mpr
    (firstExceedance_dilate_mul D ε hc)

/-- Agreement with the manuscript's infimum over strictly positive exceedance times. -/
theorem firstExceedance_eq_sInf_positive {D : ℝ≥0 → ℝ} {ε : ℝ} (hzero : D 0 ≤ ε) :
    firstExceedance D ε =
      sInf ((fun t : ℝ≥0 => (t : ℝ≥0∞)) '' {t | 0 < t ∧ ε < D t}) := by
  apply le_antisymm
  · apply le_sInf
    rintro _ ⟨t, ht, rfl⟩
    exact firstExceedance_le_of_exceeds ht.2
  · apply le_iInf
    intro t
    split_ifs with ht
    · have htpos : 0 < t := by
        by_contra h
        have heq : t = 0 := le_antisymm (le_of_not_gt h) bot_le
        rw [heq] at ht
        exact (not_lt_of_ge hzero) ht
      exact sInf_le ⟨t, ⟨htpos, ht⟩, rfl⟩
    · exact le_top

end

end BrownianAffine
