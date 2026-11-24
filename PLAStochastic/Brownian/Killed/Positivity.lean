import PLAStochastic.Brownian.Killed.TimeAnalyticity
import PLAStochastic.Brownian.Killed.LargeTimeAsymptotic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

 theorem continuous_heatKernel_right {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (x : ℝ) :
    Continuous (dirichletHeatKernel r t x) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (hasDerivAt_heatSpatialSeries_right hr ht 0 0 x z).continuousAt

 theorem continuous_heatKernel_left {r t : ℝ} (hr : 0 < r) (ht : 0 < t) (z : ℝ) :
    Continuous (fun x => dirichletHeatKernel r t x z) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_heatSpatialSeries_left hr ht 0 0 x z).continuousAt

 theorem heatFirstSine_pos {r x : ℝ} (hr : 0 < r) (hx : x ∈ Ioo 0 r) :
    0 < Real.sin (heatFrequency r 0 * x) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (heatFrequency_pos hr 0) hx.1
  · have hh := mul_lt_mul_of_pos_left hx.2 (heatFrequency_pos hr 0)
    simpa only [heatFrequency_mul_width hr.ne', Nat.cast_zero, zero_add, one_mul] using hh

 theorem dirichletHeatKernel_diagonal_pos {r t x : ℝ} (hr : 0 < r) (ht : 0 < t)
    (hx : x ∈ Ioo 0 r) : 0 < dirichletHeatKernel r t x x := by
  apply (summable_heatSpatialMode hr ht 0 0 x x).tsum_pos (i := 0)
  · intro n
    unfold heatSpatialMode
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (mul_self_nonneg _)) (Real.exp_nonneg _)
  · unfold heatSpatialMode
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    exact mul_pos (mul_pos (by positivity) (mul_pos (heatFirstSine_pos hr hx)
      (heatFirstSine_pos hr hx))) (Real.exp_pos _)

 variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

 theorem dirichletHeatKernel_nonneg_real (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t x z : ℝ} (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Icc 0 r) (hz : z ∈ Icc 0 r) :
    0 ≤ dirichletHeatKernel r t x z :=
  dirichletHeatKernel_nonneg hB hr hx (T := ⟨t, ht.le⟩) ht hz

/-- A zero at positive time forces zeros at all earlier times, using the semigroup and
strict positivity on the diagonal. -/
 theorem heatKernel_zero_at_earlier_time (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t s x z : ℝ} (hr : 0 < r) (hs : 0 < s) (hst : s < t)
    (hx : x ∈ Icc 0 r) (hz : z ∈ Ioo 0 r) (hzero : dirichletHeatKernel r t x z = 0) :
    dirichletHeatKernel r s x z = 0 := by
  have hts : 0 < t - s := sub_pos.mpr hst
  let f : ℝ → ℝ := fun y => dirichletHeatKernel r s x y * dirichletHeatKernel r (t-s) y z
  have hc : Continuous f := (continuous_heatKernel_right hr hs x).mul
    (continuous_heatKernel_left hr hts z)
  have hi : ∫ y in Icc (0 : ℝ) r, f y = 0 := by
    dsimp only [f]
    rw [integral_dirichletHeatKernel_mul hr hs hts, add_sub_cancel, hzero]
  have hn : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) r)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact mul_nonneg (dirichletHeatKernel_nonneg_real hB hr hs hx hy)
      (dirichletHeatKernel_nonneg_real hB hr hts hy ⟨hz.1.le, hz.2.le⟩)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hn hc.integrableOn_Icc).mp hi
  have hall := Measure.eqOn_Icc_of_ae_eq volume hr.ne hae hc.continuousOn continuousOn_const
  have hp := hall (show z ∈ Icc 0 r from ⟨hz.1.le, hz.2.le⟩)
  change dirichletHeatKernel r s x z * dirichletHeatKernel r (t-s) z z = 0 at hp
  exact (mul_eq_zero.mp hp).resolve_right (dirichletHeatKernel_diagonal_pos hr hts hz).ne'

/-- The actual killed transition density is strictly positive at every interior pair. -/
 theorem dirichletHeatKernel_pos (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t x z : ℝ} (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) (hz : z ∈ Ioo 0 r) :
    0 < dirichletHeatKernel r t x z := by
  by_contra hn
  have hz0 : dirichletHeatKernel r t x z = 0 :=
    le_antisymm (not_lt.mp hn) (dirichletHeatKernel_nonneg_real hB hr ht
      ⟨hx.1.le, hx.2.le⟩ ⟨hz.1.le, hz.2.le⟩)
  have he : (fun s => dirichletHeatKernel r s x z) =ᶠ[𝓝 (t/2)] (fun _ => 0) := by
    filter_upwards [Ioo_mem_nhds (by linarith : (0 : ℝ) < t/2) (by linarith : t/2 < t)] with s hs
    exact heatKernel_zero_at_earlier_time hB hr hs.1 hs.2 ⟨hx.1.le, hx.2.le⟩ hz hz0
  have hall := (analyticOnNhd_dirichletHeatKernel_time hr x z).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const (convex_Ioi (0 : ℝ)).isPreconnected (by change 0 < t/2; linarith) he
  have hlim := tendsto_rescaled_dirichletHeatKernel hr x z
  have hpos : 0 < 2/r * (Real.sin (heatFrequency r 0*x) * Real.sin (heatFrequency r 0*z)) :=
    mul_pos (by positivity) (mul_pos (heatFirstSine_pos hr hx) (heatFirstSine_pos hr hz))
  obtain ⟨s, hp, hs⟩ := ((hlim.eventually (lt_mem_nhds hpos)).and
    (eventually_gt_atTop (0 : ℝ))).exists
  have hh := hall hs
  dsimp only at hh
  rw [hh, mul_zero] at hp
  exact lt_irrefl 0 hp

 theorem continuous_heatBoundaryLeft {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Continuous (heatBoundaryLeft r t) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (hasDerivAt_heatBoundaryLeft hr ht x).continuousAt

 theorem continuous_heatBoundaryRight {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    Continuous (heatBoundaryRight r t) := by
  simp only [funext (heatBoundaryRight_reflection hr.ne' t)]
  exact (continuous_heatBoundaryLeft hr ht).comp (continuous_const.sub continuous_id)

 theorem heatBoundaryLeft_at_zero (r t : ℝ) : heatBoundaryLeft r t 0 = 0 := by
  simp [heatBoundaryLeft_series]

 theorem heatBoundaryLeft_at_width {r : ℝ} (hr : r ≠ 0) (t : ℝ) : heatBoundaryLeft r t r = 0 := by
  rw [heatBoundaryLeft_series]
  have hs (n : ℕ) : Real.sin (heatFrequency r n*r) = 0 := by
    rw [heatFrequency_mul_width hr]
    exact_mod_cast Real.sin_nat_mul_pi (n+1)
  simp only [hs, mul_zero, zero_mul, tsum_zero]

 theorem exists_heatBoundaryLeft_pos (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) :
    ∃ y ∈ Ioo (0 : ℝ) r, 0 < heatBoundaryLeft r t y := by
  by_contra hn
  push Not at hn
  have hz : ∀ y ∈ Icc (0 : ℝ) r, heatBoundaryLeft r t y = 0 := by
    intro y hy
    rcases eq_or_lt_of_le hy.1 with he | he
    · subst y
      exact heatBoundaryLeft_at_zero r t
    rcases eq_or_lt_of_le hy.2 with he' | he'
    · subst y
      exact heatBoundaryLeft_at_width hr.ne' t
    exact le_antisymm (hn y ⟨he, he'⟩) (heatBoundaryLeft_nonneg hB hr (T := ⟨t, ht.le⟩) ht hy)
  have hi : (∫ y in Icc (0 : ℝ) r, heatBoundaryLeft r t y * Real.sin (heatFrequency r 0*y)) = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero (fun y hy => by rw [hz y hy, zero_mul])
  exact (integral_heatBoundaryLeft_sine_pos hr ht 0).ne' hi

 theorem integral_heatKernel_mul_boundaryLeft {r t s : ℝ} (hr : 0 < r)
    (ht : 0 < t) (hs : 0 < s) (x : ℝ) :
    (∫ y in Icc (0 : ℝ) r, dirichletHeatKernel r t x y * heatBoundaryLeft r s y) =
      heatBoundaryLeft r (t+s) x :=
  integral_heatSpatialSeries_mul_heatSpatialSeries hr ht hs 0 1 x 0

 private theorem integral_Icc_pos_of_continuous_nonneg {r : ℝ} (hr : 0 < r)
    {f : ℝ → ℝ} (hc : Continuous f) (hn : ∀ y ∈ Icc 0 r, 0 ≤ f y)
    {x : ℝ} (hx : x ∈ Icc 0 r) (hp : 0 < f x) :
    0 < ∫ y in Icc (0 : ℝ) r, f y := by
  by_contra hi
  have h0 : (∫ y in Icc (0 : ℝ) r, f y) = 0 :=
    le_antisymm (not_lt.mp hi) (setIntegral_nonneg measurableSet_Icc hn)
  have hae : f =ᵐ[volume.restrict (Icc (0 : ℝ) r)] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae _ hc.integrableOn_Icc).mp h0
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy using hn y hy
  have hall := Measure.eqOn_Icc_of_ae_eq volume hr.ne hae hc.continuousOn continuousOn_const
  exact hp.ne' (hall hx)

/-- Strict inward boundary positivity follows from the actual positive heat kernel,
its differentiated semigroup, and its nonzero sine moment. -/
 theorem heatBoundaryLeft_pos (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t x : ℝ} (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) :
    0 < heatBoundaryLeft r t x := by
  have hh : 0 < t/2 := half_pos ht
  have heq : t/2+t/2=t := by ring
  rw [← heq, ← integral_heatKernel_mul_boundaryLeft hr hh hh]
  obtain ⟨y, hy, hp⟩ := exists_heatBoundaryLeft_pos hB hr hh
  apply integral_Icc_pos_of_continuous_nonneg hr
    ((continuous_heatKernel_right hr hh x).mul (continuous_heatBoundaryLeft hr hh))
  · intro z hz
    exact mul_nonneg (dirichletHeatKernel_nonneg_real hB hr hh ⟨hx.1.le,hx.2.le⟩ hz)
      (heatBoundaryLeft_nonneg hB hr (T := ⟨t/2, hh.le⟩) hh hz)
  · exact ⟨hy.1.le, hy.2.le⟩
  · exact mul_pos (dirichletHeatKernel_pos hB hr hh hx hy) hp

 theorem heatBoundaryRight_pos (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t x : ℝ} (hr : 0 < r) (ht : 0 < t) (hx : x ∈ Ioo 0 r) :
    0 < heatBoundaryRight r t x := by
  rw [heatBoundaryRight_reflection hr.ne']
  exact heatBoundaryLeft_pos hB hr ht ⟨sub_pos.mpr hx.2, sub_lt_self _ hx.1⟩

/-- The cross-boundary kernel is strictly positive for every positive width and time. -/
 theorem heatCrossBoundary_pos (hB : ProbabilityTheory.IsBrownianReal B μ)
    {r t : ℝ} (hr : 0 < r) (ht : 0 < t) : 0 < heatCrossBoundary r t := by
  rw [heatCrossBoundary_eq_integral_halves hr ht]
  have hh : 0 < t/2 := half_pos ht
  have hx : r/2 ∈ Ioo (0 : ℝ) r := ⟨half_pos hr, by linarith⟩
  apply integral_Icc_pos_of_continuous_nonneg hr
    ((continuous_heatBoundaryRight hr hh).mul (continuous_heatBoundaryLeft hr hh))
  · intro y hy
    exact mul_nonneg (heatBoundaryRight_nonneg hB hr (T := ⟨t/2,hh.le⟩) hh hy)
      (heatBoundaryLeft_nonneg hB hr (T := ⟨t/2,hh.le⟩) hh hy)
  · exact ⟨hx.1.le,hx.2.le⟩
  · exact mul_pos (heatBoundaryRight_pos hB hr hh hx) (heatBoundaryLeft_pos hB hr hh hx)

end BrownianAffine
