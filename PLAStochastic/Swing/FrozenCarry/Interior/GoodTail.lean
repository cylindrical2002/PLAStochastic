import PLAStochastic.Swing.FrozenCarry.Interior.Sandwich

/-! Actual finite Gaussian-path deviation bounds for the interior-duration sandwich. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem gaussianReal_nonnegative_tail_bound (v : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    (gaussianReal 0 v).real {y | z ≤ y} ≤ Real.exp (-z^2/(2*(v : ℝ))) := by
  have hh := measure_ge_le_exp_mul_mgf (X := id) (μ := gaussianReal 0 v) z
    (show 0 ≤ z/(v : ℝ) by positivity) (integrable_exp_mul_gaussianReal (z/(v : ℝ)))
  rw [congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) (z/(v : ℝ))] at hh
  simp only [zero_mul, zero_add] at hh
  rw [← Real.exp_add] at hh
  have he : -(z/(v : ℝ))*z+(v : ℝ)*(z/(v : ℝ))^2/2 = -z^2/(2*(v : ℝ)) := by
    by_cases hv : (v : ℝ) = 0
    · simp [hv]
    · field_simp
      ring
  simpa only [he, id_eq] using! hh

theorem gaussianReal_absolute_tail_bound (v : ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    (gaussianReal 0 v).real {y | z ≤ |y|} ≤ 2*Real.exp (-z^2/(2*(v : ℝ))) := by
  have hneg : HasLaw (fun y : ℝ => -y) (gaussianReal 0 v) (gaussianReal 0 v) := by
    exact ⟨(measurable_id.neg).aemeasurable, by
      simpa only [neg_zero] using gaussianReal_map_neg (μ := 0) (v := v)⟩
  have hn := hneg.measureReal_eq (p := fun y => z ≤ y) (measurableSet_le measurable_const measurable_id)
  have hs : {y : ℝ | z ≤ |y|} ⊆ {y | z ≤ y} ∪ {y | z ≤ -y} := by
    intro y hy
    change z ≤ |y| at hy
    change z ≤ y ∨ z ≤ -y
    exact le_abs.mp hy
  have hh := (measureReal_mono (μ := gaussianReal 0 v) hs).trans (measureReal_union_le _ _)
  rw [hn] at hh
  linarith [gaussianReal_nonnegative_tail_bound v hz]

theorem cumulativeSamples_abs_tail_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (j : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    μ.real {ω | z ≤ |cumulativeSamples X j ω|} ≤ 2*Real.exp (-z^2/(2*(j : ℝ))) := by
  have hl := gaussianEndpoint_hasLaw hX hi hG j
  rw [hl.measureReal_eq (p := fun y => z ≤ |y|) (measurableSet_le measurable_const measurable_id.abs)]
  exact gaussianReal_absolute_tail_bound _ hz


/-- A finite union bound is already exponentially small on subquadratic horizons. -/
theorem frozenInteriorGood_compl_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w E r : ℝ) {n : ℕ} (_hn : 0 < n) (hz : 0 < r*E-|w|) :
    μ.real (frozenInteriorGood X w E r n)ᶜ ≤
      2*(n : ℝ)*Real.exp (-(r*E-|w|)^2/(2*(n : ℝ))) := by
  have := hi.isProbabilityMeasure
  let z := r*E-|w|
  have hs : (frozenInteriorGood X w E r n)ᶜ ⊆
      ⋃ j ∈ Finset.range n, {ω | z ≤ |cumulativeSamples X j ω|} := by
    intro ω hω
    change ¬ ∀ j < n, |w+cumulativeSamples X j ω| ≤ r*E at hω
    push Not at hω
    obtain ⟨j, hj, hbad⟩ := hω
    refine mem_iUnion.mpr ⟨j, mem_iUnion.mpr ⟨Finset.mem_range.mpr hj, ?_⟩⟩
    have hab := abs_add_le w (cumulativeSamples X j ω)
    dsimp [z]
    linarith
  have hjbound (j : ℕ) (hj : j ∈ Finset.range n) :
      μ.real {ω | z ≤ |cumulativeSamples X j ω|} ≤
        2*Real.exp (-z^2/(2*(n : ℝ))) := by
    by_cases hj0 : j = 0
    · subst j
      have hem : {ω | z ≤ |cumulativeSamples X 0 ω|} = ∅ := by
        ext ω
        simp only [cumulativeSamples_zero, abs_zero, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact not_le.mpr hz
      rw [hem, measureReal_empty]
      positivity
    · have hjp : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_ne_zero hj0
      have hjn : (j : ℝ) ≤ n := by exact_mod_cast (Finset.mem_range.mp hj).le
      refine (cumulativeSamples_abs_tail_bound hX hi hG j hz.le).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div]
      exact neg_le_neg (div_le_div_of_nonneg_left (sq_nonneg z) (by positivity) (by linarith))
  calc
    _ ≤ μ.real (⋃ j ∈ Finset.range n, {ω | z ≤ |cumulativeSamples X j ω|}) := measureReal_mono hs (measure_ne_top μ _)
    _ ≤ ∑ j ∈ Finset.range n, μ.real {ω | z ≤ |cumulativeSamples X j ω|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range n, 2*Real.exp (-z^2/(2*(n : ℝ))) := Finset.sum_le_sum hjbound
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

end SwingRepair
