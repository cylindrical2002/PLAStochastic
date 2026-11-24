import PLAStochastic.Swing.Entrance.Brownian.TentDecomposition

/-!
# The signed entrance area vanishes with probability zero (E25)

Fix a scale `r > 0`. The measurable bad event at scale `r` consists of the paths that start at
`0`, pinch after `r`, stay within `1/4` of the line `m_* t` at the rational times of `[0, r]`,
and have signed area `I = 0`. On such a path the tent-bump invariance (E24) makes
`z ↦ I(f + z h_r)` strictly affine near `0`. Hence, along every line `g + z h_r`, the bad
amplitudes `z` are isolated points of their set, so they form a countable set.

Decompose `B = B^⊥ + ξ h_r` with `B^⊥` independent of `ξ` and `ξ` a nondegenerate Gaussian.
Fubini over the product law of `(B^⊥, ξ)` and the absolute continuity of the law of `ξ` show
that the bad event at scale `r` is null. Almost every Brownian path starts at `0`, pinches at a
positive time and is close to `m_* t` near `0`, so every path with `I = 0` lies in the bad event
at some scale `1/(n+1)`. A countable union gives `P(I = 0) = 0`.
-/

open MeasureTheory ProbabilityTheory Set Filter BrownianAffine
open scoped ENNReal NNReal Topology

namespace SwingRepair

noncomputable section

/-- A rational time clipped into `[0, r]`. -/
def clipTime (r : ℝ) (q : ℚ) : ℝ := max 0 (min (q : ℝ) r)

/-- The measurable bad event at scale `r`. -/
def tentBadSet (r : ℝ) : Set C(ℝ, ℝ) :=
  {f | f 0 = 0} ∩ {f | r < pinchM f} ∩
    (⋂ q : ℚ, {f | |f (clipTime r q) - slopeM f * clipTime r q| ≤ 1 / 4}) ∩ {f | areaM f = 0}

theorem measurableSet_tentBadSet (r : ℝ) : MeasurableSet (tentBadSet r) := by
  refine (((measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const).inter
    (measurableSet_lt measurable_const measurable_pinchM)).inter
    (MeasurableSet.iInter fun q => measurableSet_le ?_ measurable_const)).inter
    (measurableSet_eq_fun measurable_areaM measurable_const)
  exact (((continuous_eval_const _).measurable).sub (measurable_slopeM.mul_const _)).abs

/-- The bound at the clipped rational times controls the whole interval `[0, r]`. -/
theorem small_start_of_clip {f : C(ℝ, ℝ)} {m r : ℝ}
    (h : ∀ q : ℚ, |f (clipTime r q) - m * clipTime r q| ≤ 1 / 4) :
    ∀ t ∈ Icc (0 : ℝ) r, |f t - m * t| < 1 / 2 := by
  intro t ht
  have hcl : ∀ x : ℝ, |f (max 0 (min x r)) - m * max 0 (min x r)| ≤ 1 / 4 := by
    intro x
    refine Rat.denseRange_cast.induction_on x ?_ h
    exact isClosed_le (by fun_prop) continuous_const
  have h1 := hcl t
  rw [min_eq_left ht.2, max_eq_right ht.1] at h1
  linarith

/-- Along every line `g + z h_r` the bad amplitudes form a countable set. -/
theorem countable_tentBad_slice {r : ℝ} (hr : 0 < r) (g : C(ℝ, ℝ)) :
    {z : ℝ | g + z • tentBump r ∈ tentBadSet r}.Countable := by
  apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro z₀ hz₀
  have hr1 : 0 < 1 / r := one_div_pos.mpr hr
  refine ⟨Ioo (z₀ - 1 / r) (z₀ + 1 / r), isOpen_Ioo, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_Ioo, mem_ofPred_eq, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hz1, hz2⟩, hz⟩
    set f₀ := g + z₀ • tentBump r with hf₀
    have hsplit : g + z • tentBump r = f₀ + (z - z₀) • tentBump r := by
      ext t
      simp only [hf₀, ContinuousMap.add_apply, ContinuousMap.smul_apply, smul_eq_mul]
      ring
    simp only [tentBadSet, mem_inter_iff, mem_ofPred_eq, mem_iInter] at hz₀ hz
    obtain ⟨⟨⟨h0, hpinch⟩, hclip⟩, harea⟩ := hz₀
    rw [hsplit] at hz
    obtain ⟨⟨⟨h0', -⟩, -⟩, harea'⟩ := hz
    have hf0' : |f₀ 0| < 1 := by rw [h0, abs_zero]; exact one_pos
    have hg0' : |(f₀ + (z - z₀) • tentBump r) 0| < 1 := by rw [h0', abs_zero]; exact one_pos
    have hrσ : r < entrancePinch f₀ := by rwa [entrancePinch_eq_pinchM hf0']
    have hsmall : ∀ t ∈ Icc (0 : ℝ) r, |f₀ t - entranceSlope f₀ * t| < 1 / 2 := by
      rw [entranceSlope_eq_slopeM hf0']
      exact small_start_of_clip hclip
    have hw : |z - z₀| < 1 / r := by
      rw [abs_lt]
      constructor <;> linarith
    obtain ⟨-, -, -, hI⟩ := entrance_tent_invariance h0 hr hrσ hsmall hw
    rw [entranceArea_eq_areaM hg0', harea', entranceArea_eq_areaM hf0', harea, zero_add] at hI
    have hs : entranceSign f₀ ≠ 0 := by
      rcases entranceSign_eq_one_or_neg_one hf0' (hr.trans hrσ) with h | h <;> rw [h] <;> norm_num
    have hc := (tentArea_pos hr).ne'
    have hzero : z - z₀ = 0 := by
      rcases mul_eq_zero.mp hI.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hs
        · exact h'
      · exact absurd h hc
    linarith
  · rintro rfl
    exact ⟨⟨by linarith, by linarith⟩, hz₀⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The bad event at every positive scale is null. -/
theorem measure_tentBadSet_eq_zero (hB : IsBrownianReal B μ) {r : ℝ≥0} (hr : 0 < r) :
    μ {ω | processPath B ω ∈ tentBadSet r} = 0 := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hr' : (0 : ℝ) < r := hr
  set Y := processPath (tentResidual B r) with hYdef
  set ξ := tentCoefficient B r with hξdef
  set S : Set (C(ℝ, ℝ) × ℝ) := {p | p.1 + p.2 • tentBump r ∈ tentBadSet r} with hSdef
  have hcontS : Continuous (fun p : C(ℝ, ℝ) × ℝ => p.1 + p.2 • tentBump r) :=
    continuous_fst.add (continuous_snd.smul continuous_const)
  have hS : MeasurableSet S := hcontS.measurable (measurableSet_tentBadSet r)
  have hY : AEMeasurable Y μ := aemeasurable_tentResidualPath hB r
  have hξ : AEMeasurable ξ μ := aemeasurable_tentCoefficient hB.toIsPreBrownianReal r
  have hset : {ω | processPath B ω ∈ tentBadSet r} =ᵐ[μ] (fun ω => (Y ω, ξ ω)) ⁻¹' S := by
    filter_upwards [hB.cont] with ω hω
    change (processPath B ω ∈ tentBadSet r) = (Y ω + ξ ω • tentBump r ∈ tentBadSet r)
    rw [processPath_eq_tentResidual_add hω r]
  rw [measure_congr hset, ← Measure.map_apply_of_aemeasurable (hY.prodMk hξ) hS,
    (indepFun_iff_map_prod_eq_prod_map_map hY hξ).mp (tentResidualPath_indep hB hr),
    Measure.prod_apply hS]
  have hslice : ∀ g : C(ℝ, ℝ), (μ.map ξ) (Prod.mk g ⁻¹' S) = 0 := fun g =>
    tentCoefficient_map_absolutelyContinuous hB.toIsPreBrownianReal hr
      ((countable_tentBad_slice hr' g).measure_zero volume)
  simp only [hslice, lintegral_zero]

/-- The scales `r_n = 1/(n+1)`. -/
def tentScale (n : ℕ) : ℝ≥0 := ⟨1 / ((n : ℝ) + 1), by positivity⟩

theorem tentScale_pos (n : ℕ) : 0 < tentScale n := by
  rw [← NNReal.coe_pos]
  change (0 : ℝ) < 1 / ((n : ℝ) + 1)
  positivity

/-- **E25.** The signed entrance area of a Brownian path is almost surely nonzero. -/
theorem entranceArea_ne_zero_ae (hB : IsBrownianReal B μ) :
    ∀ᵐ ω ∂μ, entranceArea (processPath B ω) ≠ 0 := by
  have hnull : ∀ᵐ ω ∂μ, ∀ n : ℕ, processPath B ω ∉ tentBadSet (tentScale n) := by
    rw [ae_all_iff]
    intro n
    exact measure_eq_zero_iff_ae_notMem.mp (measure_tentBadSet_eq_zero hB (tentScale_pos n))
  filter_upwards [hnull, processPath_abs_zero_lt_ae hB, processPath_zero_ae hB,
    entrancePinch_pos_ae hB] with ω hω h0' h0 hσ
  intro hI
  set f := processPath B ω with hfdef
  simp only [Pi.zero_apply] at h0
  obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.mp
    (by fun_prop : Continuous (fun t => f t - slopeM f * t)) 0 (1 / 4) (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδ hσ)
  apply hω n
  have hrn : ((tentScale n : ℝ≥0) : ℝ) = 1 / ((n : ℝ) + 1) := rfl
  simp only [tentBadSet, mem_inter_iff, mem_ofPred_eq, mem_iInter]
  refine ⟨⟨⟨h0, ?_⟩, fun q => ?_⟩, ?_⟩
  · rw [hrn, ← entrancePinch_eq_pinchM h0']
    exact hn.trans_le (min_le_right _ _)
  · have hc0 : 0 ≤ clipTime (tentScale n) q := le_max_left _ _
    have hc1 : clipTime (tentScale n) q ≤ 1 / ((n : ℝ) + 1) :=
      (max_le (NNReal.coe_nonneg _) (min_le_right _ _)).trans_eq hrn
    have hd : dist (clipTime (tentScale n) q) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hc0]
      linarith [min_le_left δ (entrancePinch f)]
    have h1 := hball _ hd
    simp only [Real.dist_eq, h0, mul_zero, sub_zero] at h1
    exact h1.le
  · rw [← entranceArea_eq_areaM h0']
    exact hI

/-- Consequently `P(I < 0) = 1 - θ` for every Brownian motion. -/
theorem measureReal_entranceArea_neg (hB : IsBrownianReal B μ) :
    μ.real {ω | entranceArea (processPath B ω) < 0} = 1 - entranceSelectionProb := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have hae : ({ω | entranceArea (processPath B ω) < 0} : Set Ω) =ᵐ[μ]
      ({ω | 0 < entranceArea (processPath B ω)}ᶜ : Set Ω) := by
    filter_upwards [entranceArea_ne_zero_ae hB] with ω hω
    change (entranceArea (processPath B ω) < 0) = ¬ (0 < entranceArea (processPath B ω))
    rw [not_lt]
    exact propext ⟨fun h => h.le, fun h => lt_of_le_of_ne h hω⟩
  have hnm : NullMeasurableSet {ω | 0 < entranceArea (processPath B ω)} μ :=
    (aemeasurable_entranceArea hB).nullMeasurable measurableSet_Ioi
  rw [measureReal_congr hae, probReal_compl_eq_one_sub₀ hnm, measureReal_entranceArea_pos hB]

end

end SwingRepair
