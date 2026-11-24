import PLAStochastic.Index.GEP.Kernel.LinearSurvival.PathPotential
import PLAStochastic.Index.GEP.SurvivalBound.WordFunctional

/-! # The independent-block concentration step for linear survival -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

/-- Real-valued prefix Fubini, specialized to one iid law. -/
theorem linearSurvival_integral_cat (μ : ProbabilityMeasure ℝ) (n : ℕ)
    {H : (ℕ → ℝ) → ℝ} (hH : Measurable H) {M : ℝ} (hM : ∀ g, |H g| ≤ M) :
    (∫ g, H g ∂(iidLaw μ)) = ∫ g, ∫ h, H (surv_cat n g h) ∂(iidLaw μ) ∂(iidLaw μ) := by
  have hc := surv_integral_cat μ μ ∅ n (H := fun g => (H g : ℂ))
    (Complex.measurable_ofReal.comp hH) (fun g => by simpa using hM g)
  have hw : wordLaw μ μ ∅ = iidLaw μ := by simp [wordLaw, iidLaw]
  simp only [Finset.preimage_empty, Finset.filter_empty, hw] at hc
  have hL : (∫ g, (H g : ℂ) ∂(iidLaw μ)) = ((∫ g, H g ∂(iidLaw μ) : ℝ) : ℂ) := by
    exact integral_ofReal
  have hI (g : ℕ → ℝ) : (∫ h, (H (surv_cat n g h) : ℂ) ∂(iidLaw μ)) =
      ((∫ h, H (surv_cat n g h) ∂(iidLaw μ) : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hL] at hc
  simp_rw [hI] at hc
  have hO : (∫ g, ((∫ h, H (surv_cat n g h) ∂(iidLaw μ) : ℝ) : ℂ) ∂(iidLaw μ)) =
      ((∫ g, ∫ h, H (surv_cat n g h) ∂(iidLaw μ) ∂(iidLaw μ) : ℝ) : ℂ) := by
    exact integral_ofReal
  rw [hO] at hc
  exact Complex.ofReal_injective hc

theorem linearSurvival_gapKeys_cat_prefix {j n : ℕ} (hj : j ≤ n) (g h : ℕ → ℝ) :
    gapKeys (surv_cat n g h) j = gapKeys g j := by
  apply Finset.sum_congr rfl
  intro i hi
  exact surv_cat_apply_lt (lt_of_lt_of_le (Finset.mem_range.1 hi) hj) g h

theorem linearSurvival_gapKeys_cat (n k : ℕ) (g h : ℕ → ℝ) :
    gapKeys (surv_cat n g h) (n + k) = gapKeys g n + gapKeys h k := by
  rw [gapKeys, Finset.sum_range_add]
  congr 1
  · exact linearSurvival_gapKeys_cat_prefix le_rfl g h
  · exact Finset.sum_congr rfl fun i _ => surv_cat_apply_add n i g h

theorem linearSurvivalStay_cat (δ : ℝ) (n : ℕ) (g h : ℕ → ℝ) :
    surv_cat n g h ∈ linearSurvivalStay δ n ↔ g ∈ linearSurvivalStay δ n := by
  constructor <;> intro hg j hj
  · simpa only [linearSurvival_gapKeys_cat_prefix hj] using hg j hj
  · simpa only [linearSurvival_gapKeys_cat_prefix hj] using hg j hj

/-- The near-boundary endpoint event after an initial surviving block. -/
def linearSurvivalNear (δ r : ℝ) (m k : ℕ) : Set (ℕ → ℝ) :=
  {g | g ∈ linearSurvivalStay δ m ∧ gapKeys g (m + k) ∈ Icc (δ - r) δ}

theorem measurableSet_linearSurvivalNear (δ r : ℝ) (m k : ℕ) :
    MeasurableSet (linearSurvivalNear δ r m k) :=
  (measurableSet_linearSurvivalStay δ m).inter
    ((rawAsm_measurable_gapKeys (m + k)) measurableSet_Icc)

/-- A uniform interval bound for the second block retains the first block's
survival probability. This is the load-bearing factor in the square-root recursion. -/
theorem linearSurvival_near_le (μ : ProbabilityMeasure ℝ) (δ r a : ℝ) (m k : ℕ)
    (hc : ∀ z : ℝ, (iidLaw μ).real {g | gapKeys g k ∈ Icc z (z + r)} ≤ a) :
    (iidLaw μ).real (linearSurvivalNear δ r m k) ≤
      a * (iidLaw μ).real (linearSurvivalStay δ m) := by
  let H := (linearSurvivalNear δ r m k).indicator (fun _ => (1 : ℝ))
  have hH : Measurable H := measurable_const.indicator (measurableSet_linearSurvivalNear δ r m k)
  have hH1 : ∀ g, |H g| ≤ 1 := by
    intro g
    by_cases hg : g ∈ linearSurvivalNear δ r m k <;> simp [H, hg]
  have hreal : (iidLaw μ).real (linearSurvivalNear δ r m k) = ∫ g, H g ∂(iidLaw μ) := by
    simpa only [H, smul_eq_mul, mul_one] using
      (integral_indicator_const (1 : ℝ) (measurableSet_linearSurvivalNear δ r m k)).symm
  rw [hreal, linearSurvival_integral_cat μ m hH hH1]
  have hinner (g : ℕ → ℝ) : (∫ h, H (surv_cat m g h) ∂(iidLaw μ)) =
      (linearSurvivalStay δ m).indicator (fun g => (iidLaw μ).real
        {h | gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)}) g := by
    by_cases hg : g ∈ linearSurvivalStay δ m
    · rw [indicator_of_mem hg]
      have hfun : (fun h => H (surv_cat m g h)) =
          {h : ℕ → ℝ | gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)}.indicator
            (fun _ => (1 : ℝ)) := by
        funext h
        have he : surv_cat m g h ∈ linearSurvivalNear δ r m k ↔
            gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m) := by
          simp only [linearSurvivalNear, mem_ofPred_eq, linearSurvivalStay_cat,
            linearSurvival_gapKeys_cat, hg, true_and, mem_Icc]
          constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
        change (linearSurvivalNear δ r m k).indicator (fun _ => (1 : ℝ)) (surv_cat m g h) = _
        by_cases hh : gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)
        · rw [indicator_of_mem (he.2 hh), indicator_of_mem (show h ∈ {h | gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)} from hh)]
        · rw [indicator_of_notMem (fun hcat => hh (he.1 hcat)),
            indicator_of_notMem (show h ∉ {h | gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)} from hh)]
      rw [hfun]
      simpa only [smul_eq_mul, mul_one] using
        integral_indicator_const (μ := iidLaw μ) (1 : ℝ)
          (show MeasurableSet {h : ℕ → ℝ | gapKeys h k ∈ Icc (δ - r - gapKeys g m) (δ - gapKeys g m)} from
            (rawAsm_measurable_gapKeys k) measurableSet_Icc)
    · rw [indicator_of_notMem hg]
      have hfun : (fun h => H (surv_cat m g h)) = fun _ => (0 : ℝ) := by
        funext h
        apply indicator_of_notMem
        intro hh
        exact hg ((linearSurvivalStay_cat δ m g h).1 hh.1)
      rw [hfun, integral_zero]
  simp_rw [hinner]
  have hright : (∫ g, (linearSurvivalStay δ m).indicator (fun _ => a) g ∂(iidLaw μ)) =
      a * (iidLaw μ).real (linearSurvivalStay δ m) := by
    rw [integral_indicator_const a (measurableSet_linearSurvivalStay δ m)]
    simp [mul_comm]
  rw [← hright]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ fun g => by
      by_cases hg : g ∈ linearSurvivalStay δ m <;> simp [hg, measureReal_nonneg]
  · exact (integrable_const a).indicator (measurableSet_linearSurvivalStay δ m)
  · exact ae_of_all _ fun g => by
      by_cases hg : g ∈ linearSurvivalStay δ m
      · rw [indicator_of_mem hg, indicator_of_mem hg]
        have he : δ - r - gapKeys g m + r = δ - gapKeys g m := by ring
        simpa only [he] using hc (δ - r - gapKeys g m)
      · rw [indicator_of_notMem hg, indicator_of_notMem hg]

/-- Markov's inequality for the surviving endpoint distance. -/
theorem linearSurvival_far_le (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam r : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (hr : 0 < r) (δ : ℝ) (n : ℕ) :
    (iidLaw μ).real {g | g ∈ linearSurvivalStay δ n ∧ r ≤ δ - gapKeys g n} ≤
      (∫ g, linearSurvivalPathPotential C lam δ n g ∂(iidLaw μ)) / r := by
  have hpos : ∀ g, 0 ≤ linearSurvivalPathPotential C lam δ n g := by
    intro g
    by_cases hg : g ∈ linearSurvivalStay δ n
    · rw [linearSurvivalPathPotential, indicator_of_mem hg]
      exact linearSurvivalPotential_nonneg hC hlam _
    · rw [linearSurvivalPathPotential, indicator_of_notMem hg]
  have hb := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ hpos)
    (integrable_linearSurvivalPathPotential μ hi hC hlam δ n) r
  have hsub : {g : ℕ → ℝ | g ∈ linearSurvivalStay δ n ∧ r ≤ δ - gapKeys g n} ⊆
      {g | r ≤ linearSurvivalPathPotential C lam δ n g} := by
    intro g hg
    change r ≤ linearSurvivalPathPotential C lam δ n g
    rw [linearSurvivalPathPotential, indicator_of_mem hg.1]
    exact hg.2.trans (linearSurvivalPotential_ge hC hlam (by linarith [hg.2]))
  rw [le_div_iff₀ hr]
  have := (mul_le_mul_of_nonneg_left (measureReal_mono hsub) hr.le).trans hb
  simpa only [mul_comm] using this

/-- The actual survival recursion, with an explicit drift occupation term. -/
theorem linearSurvival_split_le (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam ρ δ r a : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (hδ : 0 ≤ δ) (hr : 0 < r)
    (hstep : ∀ d : ℝ, 0 ≤ d →
      (∫ y, linearSurvivalPotential C lam (d - y) ∂(μ : Measure ℝ)) ≤
        linearSurvivalPotential C lam d + ρ)
    (m k : ℕ) (hc : ∀ z : ℝ, (iidLaw μ).real {g | gapKeys g k ∈ Icc z (z + r)} ≤ a) :
    (iidLaw μ).real (linearSurvivalStay δ (m + k)) ≤
      a * (iidLaw μ).real (linearSurvivalStay δ m) +
        (linearSurvivalPotential C lam δ +
          ρ * ∑ j ∈ Finset.range (m + k), (iidLaw μ).real (linearSurvivalStay δ j)) / r := by
  have hcover : linearSurvivalStay δ (m + k) ⊆ linearSurvivalNear δ r m k ∪
      {g | g ∈ linearSurvivalStay δ (m + k) ∧ r ≤ δ - gapKeys g (m + k)} := by
    intro g hg
    by_cases hd : r ≤ δ - gapKeys g (m + k)
    · exact Or.inr ⟨hg, hd⟩
    · left
      exact ⟨linearSurvivalStay_antitone δ (Nat.le_add_right m k) hg,
        by have h := hg (m + k) le_rfl; constructor <;> linarith⟩
  calc
    _ ≤ (iidLaw μ).real (linearSurvivalNear δ r m k ∪
        {g | g ∈ linearSurvivalStay δ (m + k) ∧ r ≤ δ - gapKeys g (m + k)}) := measureReal_mono hcover
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add
      (linearSurvival_near_le μ δ r a m k hc)
      ((linearSurvival_far_le μ hi hC hlam hr δ (m + k)).trans
        (div_le_div_of_nonneg_right (linearSurvivalPathPotential_le μ hi hC hlam hstep hδ (m + k)) hr.le)))

end

end PGM
