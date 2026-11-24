import PLAStochastic.Swing.StationaryLimit.LeadingCoefficient.ZeroNeighborhood

/-!
# Concrete bounds for the limiting reward

The invariant-law limit is absolutely continuous.  Together with the linear
bound on the Gaussian renewal potential this gives actual integrability of the
limiting reward and an explicit estimate on its contribution from a small
neighbourhood of zero.  These are the limit-law counterparts of the finite
budget cutoff estimates in `LeadingCoefficientConcrete`.
-/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology Classical
namespace SwingRepair
namespace LeadingCoefficient

variable {Ω : Type*} [MeasurableSpace Ω]
variable {X : ℕ → Ω → ℝ} {μ : Measure Ω}

theorem marginLeadingReward_measurable_actual
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1) :
    Measurable (marginLeadingReward X μ) := by
  let V : ℝ → ℝ := fun r => gaussianRenewalPotential X μ (max r 0)
  have hmax : Continuous (fun r : ℝ => max r 0) :=
    continuous_id.max continuous_const
  have hV : Continuous V := by
    have hcomp := (gaussianRenewalPotential_continuousOn hX hi hG).comp_continuous
      hmax (fun r => le_max_right r 0)
    simpa [V, Function.comp_def] using hcomp
  have hVmeas : Measurable V := hV.measurable
  have heq : ∀ r : ℝ, marginLeadingReward X μ r =
      (if 0 < r then 4 * V r else 0) := by
    intro r
    by_cases hr : 0 < r
    · rw [marginLeadingReward, if_pos hr]
      unfold V
      rw [max_eq_left hr.le, if_pos hr]
    · rw [marginLeadingReward, if_neg hr]
      simp [hr]
  rw [show marginLeadingReward X μ =
      (fun r => if 0 < r then 4 * V r else 0) by
    funext r
    exact heq r]
  exact Measurable.ite measurableSet_Ioi (hVmeas.const_mul 4) measurable_const

theorem marginLeadingReward_integrable_of_abs_integrable
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) :
    Integrable (marginLeadingReward X μ) ν := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hmeas : Measurable (marginLeadingReward X μ) :=
    marginLeadingReward_measurable_actual hX hi hG
  have hlin : ∀ r : ℝ, |marginLeadingReward X μ r| ≤
      4 * (gaussianExcessExpMomentBound 2 + |r|) := by
    intro r
    have hnon := marginLeadingReward_nonneg hX hi hG (r := r)
    rw [abs_of_nonneg hnon]
    have hm := marginLeadingReward_le_linear hX hi hG (r := r)
    have hmax : max r 0 ≤ |r| := max_le (le_abs_self r) (abs_nonneg r)
    calc
      marginLeadingReward X μ r ≤
          4 * (max r 0 + gaussianExcessExpMomentBound 2) := hm
      _ ≤ 4 * (|r| + gaussianExcessExpMomentBound 2) := by gcongr
      _ = 4 * (gaussianExcessExpMomentBound 2 + |r|) := by ring
  have hconst : Integrable (fun _ : ℝ =>
      (4 : ℝ) * gaussianExcessExpMomentBound 2) ν := integrable_const _
  have hdom : Integrable (fun r : ℝ =>
      4 * (gaussianExcessExpMomentBound 2 + |r|)) ν := by
    have hsum := hconst.add (hνabs.const_mul 4)
    have heq : (fun r : ℝ =>
        4 * (gaussianExcessExpMomentBound 2 + |r|)) =
        (fun r : ℝ => 4 * gaussianExcessExpMomentBound 2 + 4 * |r|) := by
      funext r
      ring
    rw [heq]
    exact hsum
  exact hdom.mono' hmeas.aestronglyMeasurable (ae_of_all _ (fun r => hlin r))

theorem marginLeadingReward_setIntegral_zero_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν ≤
      4 * (gaussianExcessExpMomentBound 2 + δ) * ν.real (Icc (-δ) δ) := by
  let : IsProbabilityMeasure μ := hi.isProbabilityMeasure
  have hint := marginLeadingReward_integrable_of_abs_integrable hX hi hG hνabs
  have hpoint : ∀ r ∈ Icc (-δ) δ,
      marginLeadingReward X μ r ≤
        4 * (gaussianExcessExpMomentBound 2 + δ) := by
    intro r hr
    have hm := marginLeadingReward_le_linear hX hi hG (r := r)
    have hmax : max r 0 ≤ δ := max_le hr.2 hδ
    calc
      marginLeadingReward X μ r ≤
          4 * (max r 0 + gaussianExcessExpMomentBound 2) := hm
      _ ≤ 4 * (δ + gaussianExcessExpMomentBound 2) := by gcongr
      _ = 4 * (gaussianExcessExpMomentBound 2 + δ) := by ring
  have hsetint : IntegrableOn (marginLeadingReward X μ) (Icc (-δ) δ) ν :=
    hint.integrableOn
  have hconst : IntegrableOn (fun _ : ℝ =>
      4 * (gaussianExcessExpMomentBound 2 + δ)) (Icc (-δ) δ) ν :=
    (integrable_const _).integrableOn
  have hmono := setIntegral_mono_on hsetint hconst measurableSet_Icc hpoint
  calc
    ∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν ≤
        ∫ _r in Icc (-δ) δ,
          4 * (gaussianExcessExpMomentBound 2 + δ) ∂ν := hmono
    _ = 4 * (gaussianExcessExpMomentBound 2 + δ) *
        ν.real (Icc (-δ) δ) := by
      rw [setIntegral_const, smul_eq_mul]
      ring

theorem exists_marginLeadingReward_zero_cutoff
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνac : ν ≪ (volume : Measure ℝ))
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν < ε := by
  let C : ℝ := gaussianExcessExpMomentBound 2
  have hC : 0 ≤ C := (gaussianExcessExpMomentBound_pos 2).le
  let A : ℝ := 4 * (C + 1)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  obtain ⟨δ₀, hδ₀, hmass₀⟩ :=
    exists_measureReal_zeroNeighbourhood_lt hνac (ε := ε / A)
      (by positivity)
  let δ : ℝ := min δ₀ 1
  have hδ : 0 < δ := lt_min hδ₀ zero_lt_one
  have hδle : δ ≤ 1 := min_le_right _ _
  have hδsub : Icc (-δ) δ ⊆ Icc (-δ₀) δ₀ := by
    intro r hr
    exact mem_Icc.mpr ⟨by
      have hneg : -δ₀ ≤ -δ := neg_le_neg (min_le_left _ _)
      exact hneg.trans hr.1, hr.2.trans (min_le_left δ₀ 1)⟩
  have hmass : ν.real (Icc (-δ) δ) < ε / A := by
    exact (lt_of_le_of_lt
      (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hδsub)) hmass₀)
  have hbound := marginLeadingReward_setIntegral_zero_le hX hi hG hνabs hδ.le
  have hcoef : 4 * (C + δ) ≤ A := by
    dsimp [A]
    have : C + δ ≤ C + 1 := by linarith
    linarith
  refine ⟨δ, hδ, ?_⟩
  calc
    ∫ r in Icc (-δ) δ, marginLeadingReward X μ r ∂ν ≤
        4 * (C + δ) * ν.real (Icc (-δ) δ) := by simpa [C] using hbound
    _ ≤ A * ν.real (Icc (-δ) δ) :=
      mul_le_mul_of_nonneg_right hcoef (measureReal_nonneg)
    _ < A * (ε / A) := by
      exact mul_lt_mul_of_pos_left hmass hA
    _ = ε := by field_simp

/-! The same integrability also supplies the limit-law far-tail cutoff. -/

def limitingRewardFarNeighbourhood (n : ℕ) : Set ℝ :=
  {r : ℝ | (n : ℝ) < |r|}

theorem limitingRewardFarNeighbourhood_measureReal_tendsto
    {ν : Measure ℝ} [IsFiniteMeasure ν] :
    Tendsto (fun n : ℕ => ν.real (limitingRewardFarNeighbourhood n))
      atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < |x|}) := by
    intro m n hmn x hx
    change (n : ℝ) < |x| at hx
    change (m : ℝ) < |x|
    exact lt_of_le_of_lt (by exact_mod_cast hmn) hx
  have hiinter : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}) = (∅ : Set ℝ) := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨n, hn⟩ := exists_nat_gt |x|
    have hxn := Set.mem_iInter.mp hx n
    change (n : ℝ) < |x| at hxn
    linarith
  have h := tendsto_measure_iInter_atTop (ι := ℕ) (μ := ν)
    (fun n : ℕ => (KernelLimit.measurableSet_abs_gt (n : ℝ)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  change Tendsto (fun n : ℕ => ν {x : ℝ | (n : ℝ) < |x|}) atTop
      (𝓝 (ν (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}))) at h
  rw [hiinter, measure_empty] at h
  have hreal := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  have hreal' : Tendsto
      (fun n : ℕ => (ν {x : ℝ | (n : ℝ) < |x|}).toReal)
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using hreal
  simpa [limitingRewardFarNeighbourhood, Measure.real] using hreal'

theorem exists_marginLeadingReward_far_cutoff
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν < ε := by
  have hf := marginLeadingReward_integrable_of_abs_integrable
    (X := X) (μ := μ) hX hi hG hνabs
  have hset := hf.tendsto_setIntegral_nhds_zero
    (l := atTop) (s := limitingRewardFarNeighbourhood)
    (by
      have hanti : Antitone (fun n : ℕ => {x : ℝ | (n : ℝ) < |x|}) := by
        intro m n hmn x hx
        change (n : ℝ) < |x| at hx
        change (m : ℝ) < |x|
        exact lt_of_le_of_lt (by exact_mod_cast hmn) hx
      have hiinter : (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}) = (∅ : Set ℝ) := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨n, hn⟩ := exists_nat_gt |x|
        have hxn := Set.mem_iInter.mp hx n
        change (n : ℝ) < |x| at hxn
        linarith
      have hm := tendsto_measure_iInter_atTop (ι := ℕ) (μ := ν)
        (fun n : ℕ => (KernelLimit.measurableSet_abs_gt (n : ℝ)).nullMeasurableSet)
        hanti ⟨0, measure_ne_top _ _⟩
      change Tendsto (fun n : ℕ => ν {x : ℝ | (n : ℝ) < |x|}) atTop
        (𝓝 (ν (⋂ n : ℕ, {x : ℝ | (n : ℝ) < |x|}))) at hm
      rw [hiinter, measure_empty] at hm
      change Tendsto (fun n => ν (limitingRewardFarNeighbourhood n)) atTop (𝓝 0)
      simpa [limitingRewardFarNeighbourhood] using hm)
  obtain ⟨n, hn⟩ := (hset.eventually (eventually_lt_nhds hε)).exists
  refine ⟨n, by positivity, ?_⟩
  simpa [limitingRewardFarNeighbourhood] using hn

theorem marginLeadingReward_farCut_integral_le
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hνabs : Integrable (fun r : ℝ => |r|) ν) {C : ℝ} (_hC : 0 ≤ C) :
    ∫ r, marginLeadingReward X μ r * KernelLimit.farCut C r ∂ν ≤
      ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν := by
  have hf := marginLeadingReward_integrable_of_abs_integrable
    (X := X) (μ := μ) hX hi hG hνabs
  have hfm : Measurable (marginLeadingReward X μ) :=
    marginLeadingReward_measurable_actual hX hi hG
  have hcutm : Measurable (KernelLimit.farCut C) :=
    (KernelLimit.continuous_farCut C).measurable
  have hprod : Integrable
      (fun r => marginLeadingReward X μ r * KernelLimit.farCut C r) ν :=
    hf.mul_bdd (μ := ν) hcutm.aestronglyMeasurable
      (ae_of_all _ (fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (KernelLimit.farCut_nonneg C r)]
        exact KernelLimit.farCut_le_one C r))
  let S : Set ℝ := {r : ℝ | C < |r|}
  have hS : MeasurableSet S := KernelLimit.measurableSet_abs_gt C
  have hset : Integrable (S.indicator (marginLeadingReward X μ)) ν :=
    hf.indicator hS
  have hpoint : ∀ r, marginLeadingReward X μ r * KernelLimit.farCut C r ≤
      S.indicator (marginLeadingReward X μ) r := by
    intro r
    by_cases hr : r ∈ S
    · rw [Set.indicator_of_mem hr]
      have hnon := marginLeadingReward_nonneg hX hi hG (r := r)
      exact mul_le_of_le_one_right hnon (KernelLimit.farCut_le_one C r)
    · rw [Set.indicator_of_notMem hr]
      have hzero : KernelLimit.farCut C r = 0 := by
        apply KernelLimit.farCut_eq_zero
        exact le_of_not_gt hr
      simp [hzero]
  calc
    ∫ r, marginLeadingReward X μ r * KernelLimit.farCut C r ∂ν ≤
        ∫ r, S.indicator (marginLeadingReward X μ) r ∂ν :=
      integral_mono hprod hset hpoint
    _ = ∫ r in S, marginLeadingReward X μ r ∂ν := by
      rw [integral_indicator hS]
    _ = ∫ r in {r : ℝ | C < |r|}, marginLeadingReward X μ r ∂ν := by
      rfl

end LeadingCoefficient
end SwingRepair
