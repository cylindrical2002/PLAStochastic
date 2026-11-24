import PLAStochastic.Index.GEP.Kernel.LinearSurvival.KilledPotential

/-! # The potential estimate on actual iid surviving paths -/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

/-- Paths staying below the level `δ` through time `n`. -/
def linearSurvivalStay (δ : ℝ) (n : ℕ) : Set (ℕ → ℝ) :=
  {g | ∀ j ≤ n, gapKeys g j ≤ δ}

theorem measurableSet_linearSurvivalStay (δ : ℝ) (n : ℕ) :
    MeasurableSet (linearSurvivalStay δ n) := by
  have he : linearSurvivalStay δ n = ⋂ j, ⋂ (_hj : j ≤ n), {g : ℕ → ℝ | gapKeys g j ≤ δ} := by
    ext g
    simp [linearSurvivalStay]
  rw [he]
  exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
    measurableSet_le (rawAsm_measurable_gapKeys j) measurable_const

theorem linearSurvivalStay_antitone (δ : ℝ) : Antitone (linearSurvivalStay δ) := by
  intro m n hmn g hg j hj
  exact hg j (hj.trans hmn)

/-- The killed potential evaluated on the actual path endpoint. -/
def linearSurvivalPathPotential (C lam δ : ℝ) (n : ℕ) : (ℕ → ℝ) → ℝ :=
  (linearSurvivalStay δ n).indicator (fun g => linearSurvivalPotential C lam (δ - gapKeys g n))

theorem measurable_linearSurvivalPathPotential (C lam δ : ℝ) (n : ℕ) :
    Measurable (linearSurvivalPathPotential C lam δ n) := by
  apply ((measurable_linearSurvivalPotential C lam).comp
    ((rawAsm_measurable_gapKeys n).const_sub δ)).indicator
  exact measurableSet_linearSurvivalStay δ n

theorem linearSurvival_integrable_gapKeys (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ)) (n : ℕ) :
    Integrable (fun g => gapKeys g n) (iidLaw μ) := by
  apply integrable_finsetSum
  intro i _hi
  have hm : (iidLaw μ).map (fun g : ℕ → ℝ => g i) = (μ : Measure ℝ) := Measure.infinitePi_map_eval _ i
  have hmap : Integrable (fun y : ℝ => y) ((iidLaw μ).map (fun g : ℕ → ℝ => g i)) := by rwa [hm]
  exact (integrable_map_measure measurable_id.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 hmap

theorem integrable_linearSurvivalPathPotential (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam) (δ : ℝ) (n : ℕ) :
    Integrable (linearSurvivalPathPotential C lam δ n) (iidLaw μ) := by
  have hs := linearSurvival_integrable_gapKeys μ hi n
  have hp : Integrable (fun g => linearSurvivalPotential C lam (δ - gapKeys g n)) (iidLaw μ) := by
    apply (((integrable_const δ).sub hs).abs.add (integrable_const C)).mono'
      (((measurable_linearSurvivalPotential C lam).comp
        ((rawAsm_measurable_gapKeys n).const_sub δ)).aestronglyMeasurable)
    exact ae_of_all _ fun g => by
      change ‖linearSurvivalPotential C lam (δ - gapKeys g n)‖ ≤ |δ - gapKeys g n| + C
      rw [Real.norm_eq_abs, abs_of_nonneg (linearSurvivalPotential_nonneg hC hlam _)]
      exact linearSurvivalPotential_le (by linarith) _
  exact hp.indicator (measurableSet_linearSurvivalStay δ n)

theorem linearSurvival_gapKeys_update {j n : ℕ} (hjn : j ≤ n) (g : ℕ → ℝ) (y : ℝ) :
    gapKeys (Function.update g n y) j = gapKeys g j := by
  apply Finset.sum_congr rfl
  intro i hi
  exact Function.update_of_ne (by have := Finset.mem_range.1 hi; omega) _ _

theorem linearSurvivalStay_update (δ : ℝ) (n : ℕ) (g : ℕ → ℝ) (y : ℝ) :
    Function.update g n y ∈ linearSurvivalStay δ n ↔ g ∈ linearSurvivalStay δ n := by
  constructor <;> intro h j hj
  · simpa only [linearSurvival_gapKeys_update hj] using h j hj
  · simpa only [linearSurvival_gapKeys_update hj] using h j hj

/-- The last-step survival constraint is already built into the killed potential. -/
theorem linearSurvivalPathPotential_update (C lam δ : ℝ) (n : ℕ) (g : ℕ → ℝ) (y : ℝ) :
    linearSurvivalPathPotential C lam δ (n + 1) (Function.update g n y) =
      (linearSurvivalStay δ n).indicator (fun g =>
        linearSurvivalPotential C lam (δ - gapKeys g n - y)) g := by
  by_cases hg : g ∈ linearSurvivalStay δ n
  · rw [indicator_of_mem hg]
    by_cases hlast : gapKeys g n + y ≤ δ
    · have hstay : Function.update g n y ∈ linearSurvivalStay δ (n + 1) := by
        intro j hj
        by_cases hjn : j ≤ n
        · rw [linearSurvival_gapKeys_update hjn]
          exact hg j hjn
        · have hj' : j = n + 1 := by omega
          rw [hj', gapKeys_update_succ]
          exact hlast
      rw [linearSurvivalPathPotential, indicator_of_mem hstay, gapKeys_update_succ]
      congr 1
      ring
    · have hnStay : Function.update g n y ∉ linearSurvivalStay δ (n + 1) := by
        intro hs
        exact hlast (by simpa only [gapKeys_update_succ] using hs (n + 1) le_rfl)
      rw [linearSurvivalPathPotential, indicator_of_notMem hnStay]
      symm
      exact indicator_of_notMem (show δ - gapKeys g n - y ∉ Set.Ici (0 : ℝ) by simp only [Set.mem_Ici]; linarith) _
  · have hnStay : Function.update g n y ∉ linearSurvivalStay δ (n + 1) := by
      intro hs
      exact hg ((linearSurvivalStay_update δ n g y).1
        (linearSurvivalStay_antitone δ (Nat.le_succ n) hs))
    rw [linearSurvivalPathPotential, indicator_of_notMem hnStay, indicator_of_notMem hg]

/-- A one-step killed-potential inequality iterates on actual iid paths. -/
theorem linearSurvivalPathPotential_succ_le (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam ρ : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam)
    (hstep : ∀ d : ℝ, 0 ≤ d →
      (∫ y, linearSurvivalPotential C lam (d - y) ∂(μ : Measure ℝ)) ≤
        linearSurvivalPotential C lam d + ρ) (δ : ℝ) (n : ℕ) :
    (∫ g, linearSurvivalPathPotential C lam δ (n + 1) g ∂(iidLaw μ)) ≤
      (∫ g, linearSurvivalPathPotential C lam δ n g ∂(iidLaw μ)) +
        ρ * (iidLaw μ).real (linearSurvivalStay δ n) := by
  have hfub : (∫ g, linearSurvivalPathPotential C lam δ (n + 1) g ∂(iidLaw μ)) =
      ∫ g, ∫ y, linearSurvivalPathPotential C lam δ (n + 1) (Function.update g n y)
        ∂(μ : Measure ℝ) ∂(iidLaw μ) :=
    integral_piLaw_insert (fun _ => μ) n (measurable_linearSurvivalPathPotential _ _ _ _)
      (integrable_linearSurvivalPathPotential μ hi hC hlam δ (n + 1))
  rw [hfub]
  simp_rw [linearSurvivalPathPotential_update]
  have heq : (fun g : ℕ → ℝ => ∫ y, (linearSurvivalStay δ n).indicator
      (fun g => linearSurvivalPotential C lam (δ - gapKeys g n - y)) g ∂(μ : Measure ℝ)) =
      (linearSurvivalStay δ n).indicator (fun g =>
        ∫ y, linearSurvivalPotential C lam ((δ - gapKeys g n) - y) ∂(μ : Measure ℝ)) := by
    funext g
    by_cases hg : g ∈ linearSurvivalStay δ n <;> simp [hg]
  rw [heq]
  have hright : (∫ g, (linearSurvivalStay δ n).indicator
      (fun g => linearSurvivalPotential C lam (δ - gapKeys g n) + ρ) g ∂(iidLaw μ)) =
      (∫ g, linearSurvivalPathPotential C lam δ n g ∂(iidLaw μ)) +
        ρ * (iidLaw μ).real (linearSurvivalStay δ n) := by
    rw [Set.indicator_add]
    change (∫ g, linearSurvivalPathPotential C lam δ n g +
      (linearSurvivalStay δ n).indicator (fun _ => ρ) g ∂(iidLaw μ)) = _
    rw [integral_add (integrable_linearSurvivalPathPotential μ hi hC hlam δ n)
      ((integrable_const ρ).indicator (measurableSet_linearSurvivalStay δ n)),
      integral_indicator (measurableSet_linearSurvivalStay δ n), integral_const]
    simp only [measureReal_restrict_apply_univ, smul_eq_mul]
    ring
  rw [← hright]
  apply integral_mono_ae
  · have hip := integrable_prod_update (ρ := fun _ => μ) (i := n) (α := μ)
      (measurable_linearSurvivalPathPotential C lam δ (n + 1))
      (by rw [piLaw_update_self]; exact integrable_linearSurvivalPathPotential μ hi hC hlam δ (n + 1))
    have hm := hip.integral_prod_right
    simp only [linearSurvivalPathPotential_update, heq] at hm
    convert! hm using 1
  · have hm := (integrable_linearSurvivalPathPotential μ hi hC hlam δ n).add
      ((integrable_const ρ).indicator (measurableSet_linearSurvivalStay δ n))
    convert! hm using 1
    exact Set.indicator_add _ _ _
  · filter_upwards [] with g
    by_cases hg : g ∈ linearSurvivalStay δ n
    · rw [indicator_of_mem hg, indicator_of_mem hg]
      exact hstep _ (sub_nonneg.2 (hg n le_rfl))
    · rw [indicator_of_notMem hg, indicator_of_notMem hg]

theorem linearSurvivalPathPotential_le (μ : ProbabilityMeasure ℝ)
    (hi : Integrable (fun y : ℝ => y) (μ : Measure ℝ))
    {C lam ρ : ℝ} (hC : 1 ≤ C) (hlam : 0 ≤ lam)
    (hstep : ∀ d : ℝ, 0 ≤ d →
      (∫ y, linearSurvivalPotential C lam (d - y) ∂(μ : Measure ℝ)) ≤
        linearSurvivalPotential C lam d + ρ) {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    (∫ g, linearSurvivalPathPotential C lam δ n g ∂(iidLaw μ)) ≤
      linearSurvivalPotential C lam δ +
        ρ * ∑ j ∈ range n, (iidLaw μ).real (linearSurvivalStay δ j) := by
  induction n with
  | zero =>
    have hs : linearSurvivalStay δ 0 = univ := by
      ext g
      simp [linearSurvivalStay, gapKeys_zero, hδ]
    simp [linearSurvivalPathPotential, hs, gapKeys_zero]
  | succ n ih =>
    have h := linearSurvivalPathPotential_succ_le μ hi hC hlam hstep δ n
    rw [Finset.sum_range_succ]
    linarith

end

end PGM
