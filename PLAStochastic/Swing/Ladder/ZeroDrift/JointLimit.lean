import PLAStochastic.Swing.Ladder.ZeroDrift.PairLaw

/-!
# The joint age/residual limit of the zero-drift walk (E15)

Let `X` be i.i.d. standard Gaussian, `W = cumulativeSamples X` the zero-drift walk,
`T_D = inf {j ≥ 1 : W_j > D}`, `O_D = W_{T_D} - D` and `U_D = D - max_{0 ≤ j < T_D} W_j`.
Then, as `D → ∞` along the reals,

`(U_D, O_D) ⇒ equilibriumPairLaw ν₀`,

i.e. `E g(U_D, O_D) → ∫ g d(equilibriumPairLaw ν₀)` for every bounded continuous
`g : ℝ × ℝ → ℝ`.

The proof checks convergence on the π-system of half-open boxes `(a,b] × (c,d]`, which
contains arbitrarily small neighbourhoods of every point, and applies the portmanteau
criterion `IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem`.  The mass of a box is
an alternating sum of four joint survival values; for the walk these converge by the joint
tail limit of `AgeResidualTail`, and for the pair law they are computed in `PairLaw`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical MeasureTheory BoundedContinuousFunction
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-! ### Boxes -/

/-- The half-open boxes `(a,b] × (c,d]`. -/
def halfOpenBoxes : Set (Set (ℝ × ℝ)) := {s | ∃ a b c d : ℝ, s = Ioc a b ×ˢ Ioc c d}

theorem isPiSystem_halfOpenBoxes : IsPiSystem halfOpenBoxes := by
  rintro _ ⟨a, b, c, d, rfl⟩ _ ⟨a', b', c', d', rfl⟩ -
  refine ⟨max a a', min b b', max c c', min d d', ?_⟩
  rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc, Set.Ioc_inter_Ioc]

theorem halfOpenBoxes_measurableSet : ∀ s ∈ halfOpenBoxes, MeasurableSet s := by
  rintro _ ⟨a, b, c, d, rfl⟩
  exact measurableSet_Ioc.prod measurableSet_Ioc

theorem halfOpenBoxes_nhds :
    ∀ u : Set (ℝ × ℝ), IsOpen u → ∀ x ∈ u, ∃ s ∈ halfOpenBoxes, s ∈ 𝓝 x ∧ s ⊆ u := by
  intro u hu x hx
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu x hx
  refine ⟨Ioc (x.1 - ε / 2) (x.1 + ε / 2) ×ˢ Ioc (x.2 - ε / 2) (x.2 + ε / 2),
    ⟨_, _, _, _, rfl⟩, ?_, ?_⟩
  · exact prod_mem_nhds (Ioc_mem_nhds (by linarith) (by linarith))
      (Ioc_mem_nhds (by linarith) (by linarith))
  · intro p hp
    apply hball
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- The mass of a box is the alternating sum of four joint survival values. -/
theorem measureReal_box_eq (ρ : Measure (ℝ × ℝ)) [IsFiniteMeasure ρ] {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ρ.real (Ioc a b ×ˢ Ioc c d) = ρ.real (Ioi a ×ˢ Ioi c) - ρ.real (Ioi b ×ˢ Ioi c) -
      ρ.real (Ioi a ×ˢ Ioi d) + ρ.real (Ioi b ×ˢ Ioi d) := by
  have hdab : Disjoint (Ioc a b) (Ioi b) := Set.disjoint_left.mpr fun x hx hx' => by
    have h1 : x ≤ b := hx.2
    have h2 : b < x := hx'
    linarith
  have hdcd : Disjoint (Ioc c d) (Ioi d) := Set.disjoint_left.mpr fun x hx hx' => by
    have h1 : x ≤ d := hx.2
    have h2 : d < x := hx'
    linarith
  have e1 : Ioi a ×ˢ Ioi c = (Ioc a b ×ˢ Ioi c) ∪ (Ioi b ×ˢ Ioi c) := by
    rw [← Set.union_prod, Set.Ioc_union_Ioi_eq_Ioi hab]
  have e2 : Ioc a b ×ˢ Ioi c = (Ioc a b ×ˢ Ioc c d) ∪ (Ioc a b ×ˢ Ioi d) := by
    rw [← Set.prod_union, Set.Ioc_union_Ioi_eq_Ioi hcd]
  have e3 : Ioi a ×ˢ Ioi d = (Ioc a b ×ˢ Ioi d) ∪ (Ioi b ×ˢ Ioi d) := by
    rw [← Set.union_prod, Set.Ioc_union_Ioi_eq_Ioi hab]
  have r1 : ρ.real (Ioi a ×ˢ Ioi c) = ρ.real (Ioc a b ×ˢ Ioi c) + ρ.real (Ioi b ×ˢ Ioi c) := by
    rw [e1, measureReal_union (Set.disjoint_prod.mpr (Or.inl hdab))
      (measurableSet_Ioi.prod measurableSet_Ioi)]
  have r2 : ρ.real (Ioc a b ×ˢ Ioi c) =
      ρ.real (Ioc a b ×ˢ Ioc c d) + ρ.real (Ioc a b ×ˢ Ioi d) := by
    rw [e2, measureReal_union (Set.disjoint_prod.mpr (Or.inr hdcd))
      (measurableSet_Ioc.prod measurableSet_Ioi)]
  have r3 : ρ.real (Ioi a ×ˢ Ioi d) = ρ.real (Ioc a b ×ˢ Ioi d) + ρ.real (Ioi b ×ˢ Ioi d) := by
    rw [e3, measureReal_union (Set.disjoint_prod.mpr (Or.inl hdab))
      (measurableSet_Ioi.prod measurableSet_Ioi)]
  linarith

/-! ### The laws -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- The joint law of the age and the residual of the zero-drift walk at the level `D`. -/
def zeroDriftAgeResidualLaw (X : ℕ → Ω → ℝ) (μ : Measure Ω) (D : ℝ) : Measure (ℝ × ℝ) :=
  μ.map (fun ω => (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω))

theorem zeroDriftAgeResidual_measurable (hX : ∀ n, Measurable (X n)) (D : ℝ) :
    Measurable (fun ω => (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω)) :=
  (zeroDriftUndershoot_measurable hX D).prodMk (zeroDriftOvershoot_measurable hX D)

theorem zeroDriftAgeResidualLaw_isProbabilityMeasure (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (D : ℝ) : IsProbabilityMeasure (zeroDriftAgeResidualLaw X μ D) := by
  have := hi.isProbabilityMeasure
  exact Measure.isProbabilityMeasure_map (zeroDriftAgeResidual_measurable hX D).aemeasurable

theorem zeroDriftAgeResidualLaw_survival (hX : ∀ n, Measurable (X n)) (D u o : ℝ) :
    (zeroDriftAgeResidualLaw X μ D).real (Ioi u ×ˢ Ioi o) =
      μ.real {ω | u < zeroDriftUndershoot X D ω ∧ o < zeroDriftOvershoot X D ω} := by
  rw [zeroDriftAgeResidualLaw, Measure.real, Measure.map_apply
    (zeroDriftAgeResidual_measurable hX D) (measurableSet_Ioi.prod measurableSet_Ioi)]
  rfl

/-- The joint survival function of the zero-drift equilibrium pair at arbitrary real
arguments. -/
theorem gaussianZeroLadder_pair_survival (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (u o : ℝ) :
    (equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)).real (Ioi u ×ˢ Ioi o) =
      (equilibriumOvershootTail (gaussianAscendingLadderLaw X μ 0) (max u 0 + max o 0)).toReal := by
  have h := gaussianAscendingLadderLaw_zero_spreadOut hX hi hG
  have := h.isProbabilityMeasure
  have hcong : (Ioi u ×ˢ Ioi o : Set (ℝ × ℝ)) =ᵐ[equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)]
      (Ioi (max u 0) ×ˢ Ioi (max o 0) : Set (ℝ × ℝ)) := by
    filter_upwards [equilibriumPairLaw_ae_pos _ h.mean_ne_zero h.mean_ne_top] with p hp
    refine propext ?_
    show p ∈ Ioi u ×ˢ Ioi o ↔ p ∈ Ioi (max u 0) ×ˢ Ioi (max o 0)
    simp only [Set.mem_prod, Set.mem_Ioi, max_lt_iff]
    tauto
  rw [Measure.real, measure_congr hcong,
    equilibriumPairLaw_Ioi_prod_Ioi _ (le_max_right _ _) (le_max_right _ _)]

/-- The survival function of `(U_D, O_D)` converges to that of the equilibrium pair. -/
theorem zeroDriftAgeResidualLaw_survival_tendsto (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (u o : ℝ) :
    Tendsto (fun D : ℝ => (zeroDriftAgeResidualLaw X μ D).real (Ioi u ×ˢ Ioi o)) atTop
      (𝓝 ((equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)).real (Ioi u ×ˢ Ioi o))) := by
  rw [gaussianZeroLadder_pair_survival hX hi hG]
  simp_rw [zeroDriftAgeResidualLaw_survival hX]
  exact zeroDrift_joint_tail_tendsto hX hi hG u o

theorem probabilityMeasure_coe_real {α : Type*} [MeasurableSpace α] (P : ProbabilityMeasure α)
    (s : Set α) : ((P s : ℝ≥0) : ℝ) = (P : Measure α).real s := by
  rw [ProbabilityMeasure.coeFn_def, ENNReal.coe_toNNReal_eq_toReal]
  rfl

/-- **Weak convergence of the zero-drift age/residual pair** to the equilibrium pair law. -/
theorem zeroDriftAgeResidualLaw_tendsto (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Tendsto (β := ProbabilityMeasure (ℝ × ℝ)) (fun D : ℝ => (⟨zeroDriftAgeResidualLaw X μ D,
        zeroDriftAgeResidualLaw_isProbabilityMeasure hX hi D⟩ : ProbabilityMeasure (ℝ × ℝ)))
      atTop (𝓝 (⟨equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0),
        gaussianZeroLadder_pair_isProbabilityMeasure hX hi hG⟩ : ProbabilityMeasure (ℝ × ℝ))) := by
  have hπ := gaussianZeroLadder_pair_isProbabilityMeasure hX hi hG
  refine isPiSystem_halfOpenBoxes.tendsto_probabilityMeasure_of_tendsto_of_mem
    halfOpenBoxes_measurableSet halfOpenBoxes_nhds ?_
  rintro _ ⟨a, b, c, d, rfl⟩
  rw [← NNReal.tendsto_coe]
  simp only [probabilityMeasure_coe_real, ProbabilityMeasure.coe_mk]
  by_cases hbox : a ≤ b ∧ c ≤ d
  · have := zeroDriftAgeResidualLaw_isProbabilityMeasure hX hi
    simp_rw [measureReal_box_eq _ hbox.1 hbox.2]
    exact (((zeroDriftAgeResidualLaw_survival_tendsto hX hi hG a c).sub
      (zeroDriftAgeResidualLaw_survival_tendsto hX hi hG b c)).sub
      (zeroDriftAgeResidualLaw_survival_tendsto hX hi hG a d)).add
      (zeroDriftAgeResidualLaw_survival_tendsto hX hi hG b d)
  · have hempty : Ioc a b ×ˢ Ioc c d = (∅ : Set (ℝ × ℝ)) := by
      rw [Set.prod_eq_empty_iff]
      rcases not_and_or.mp hbox with h | h
      · exact Or.inl (Set.Ioc_eq_empty_of_le (not_le.mp h).le)
      · exact Or.inr (Set.Ioc_eq_empty_of_le (not_le.mp h).le)
    simp only [hempty, measureReal_empty]
    exact tendsto_const_nhds

/-- **The joint age/residual limit (E15).**  For every bounded continuous test function
`g : ℝ × ℝ → ℝ`, `E g(U_D, O_D) → ∫ g d(equilibriumPairLaw ν₀)` as `D → ∞`. -/
theorem zeroDriftAgeResidual_tendsto (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) (g : ℝ × ℝ →ᵇ ℝ) :
    Tendsto (fun D : ℝ => ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ)
      atTop (𝓝 (∫ p, g p ∂(equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)))) := by
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp
    (zeroDriftAgeResidualLaw_tendsto hX hi hG) g
  simp only [ProbabilityMeasure.coe_mk] at h
  refine h.congr fun D => ?_
  rw [zeroDriftAgeResidualLaw, integral_map (zeroDriftAgeResidual_measurable hX D).aemeasurable
    g.continuous.aestronglyMeasurable]

/-- The joint age/residual limit for a continuous function with an explicit bound. -/
theorem zeroDriftAgeResidual_tendsto_of_continuous (hX : ∀ n, Measurable (X n))
    (hi : iIndepFun X μ) (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) {g : ℝ × ℝ → ℝ}
    (hg : Continuous g) {C : ℝ} (hC : ∀ p, |g p| ≤ C) :
    Tendsto (fun D : ℝ => ∫ ω, g (zeroDriftUndershoot X D ω, zeroDriftOvershoot X D ω) ∂μ)
      atTop (𝓝 (∫ p, g p ∂(equilibriumPairLaw (gaussianAscendingLadderLaw X μ 0)))) := by
  let G : ℝ × ℝ →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hg⟩ (2 * C) fun x y => by
    rw [Real.dist_eq]
    have h1 := hC x
    have h2 := hC y
    rw [abs_le] at h1 h2 ⊢
    constructor <;> simp only [ContinuousMap.coe_mk] <;> linarith
  exact zeroDriftAgeResidual_tendsto hX hi hG G

end SwingRepair
