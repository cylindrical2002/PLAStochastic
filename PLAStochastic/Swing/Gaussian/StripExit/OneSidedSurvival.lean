import PLAStochastic.Swing.Gaussian.StripExit.Estimates

/-! # Actual one-sided survival reduced to true strip-exit estimates -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} {X : ℕ → Ω → ℝ}

/-- The paper's actual event Q_n^a(x), testing exactly times 1 through n. -/
def gaussianSurvivalEvent (X : ℕ → Ω → ℝ) (x a : ℝ) (n : ℕ) : Set Ω :=
  {ω | ∀ j ∈ Icc 1 n, 0 ≤ gaussianDriftWalk X x a j ω}

/-- A surviving path either exits at the upper side or has not exited the strip by n. -/
theorem gaussianSurvivalEvent_subset_strip {x a R : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    gaussianSurvivalEvent X x a n ⊆ gaussianStripUpperExit X x a R ∪
      {ω | (n : WithTop ℕ) < gaussianStripExit X x a R ω} := by
  intro ω hω
  by_cases hn : (n : WithTop ℕ) < gaussianStripExit X x a R ω
  · exact Or.inr hn
  · have hle := le_of_not_gt hn
    have ht : gaussianStripExit X x a R ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp ht
    have hkn : k ≤ n := WithTop.coe_le_coe.mp (hk ▸ hle)
    have hp : 0 ≤ gaussianStripExitPosition X x a R ω := by
      rw [gaussianStripExitPosition_of_eq hk.symm]
      by_cases hk0 : k = 0
      · simpa only [hk0, gaussianDriftWalk_zero] using hx
      · exact hω k ⟨by omega, hkn⟩
    exact Or.inl ⟨ht, lt_of_not_ge (fun hu => gaussianStripExitPosition_not_mem ht ⟨hp, hu⟩)⟩

variable [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem gaussianSurvivalEvent_measurable (hX : ∀ n, Measurable (X n)) (x a : ℝ) (n : ℕ) :
    MeasurableSet (gaussianSurvivalEvent X x a n) := by
  unfold gaussianSurvivalEvent
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun j => MeasurableSet.iInter (fun _ =>
    measurableSet_le measurable_const (gaussianDriftWalk_measurable hX x a j)))

/-- Markov's bound is proved directly with the capped time, retaining possible infinite exits. -/
theorem capDiscreteTime_tail_mul_le_integral [IsFiniteMeasure μ] {τ : Ω → WithTop ℕ}
    (hτ : Measurable[mΩ] τ) (n : ℕ) :
    (n : ℝ) * μ.real {ω | (n : WithTop ℕ) < τ ω} ≤
      ∫ ω, (capDiscreteTime (τ ω) n : ℝ) ∂μ := by
  have hs := measurableSet_lt (measurable_const (a := (n : WithTop ℕ))) hτ
  have hi := integral_mono ((integrable_const (n : ℝ)).indicator hs) (capDiscreteTime_integrable (μ := μ) hτ n) ?_
  · rw [integral_indicator hs, setIntegral_const] at hi
    simpa only [smul_eq_mul, mul_comm] using hi
  · intro ω
    dsimp only
    by_cases h : (n : WithTop ℕ) < τ ω
    · rw [indicator_of_mem (show ω ∈ {ω | (n : WithTop ℕ) < τ ω} from h), capDiscreteTime_eq_of_lt h]
    · rw [indicator_of_notMem (show ω ∉ {ω | (n : WithTop ℕ) < τ ω} from h)]
      exact Nat.cast_nonneg _

/-- The survival bound with an arbitrary admissible strip width. -/
theorem gaussianSurvivalEvent_le_strip
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {x a R : ℝ} (hx : x ∈ Icc 0 R) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (ha' : a ≤ 1/2) (haR : a*R ≤ 1/2) {n : ℕ} (hn : 0 < n) :
    μ.real (gaussianSurvivalEvent X x a n) ≤
      gaussianUpperExitConstant * (x+1)/R + gaussianExitMeanConstant * R * (x+1)/(n : ℝ) := by
  have : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have ht := (capDiscreteTime_tail_mul_le_integral
    (gaussianStripExit_isStoppingTime hX x a R).measurable' n).trans
      (gaussianStrip_capped_mean_le hX hi hG hx hR ha ha' haR n)
  have ht' : μ.real {ω | (n : WithTop ℕ) < gaussianStripExit X x a R ω} ≤
      gaussianExitMeanConstant*R*(x+1)/(n : ℝ) := by
    apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
    simpa only [mul_comm] using ht
  exact ((measureReal_mono (gaussianSurvivalEvent_subset_strip hx.1 n)).trans
    (measureReal_union_le _ _)).trans
      (add_le_add (gaussianStrip_upperExit_le hX hi hG hx hR ha ha' haR) ht')

end SwingRepair
