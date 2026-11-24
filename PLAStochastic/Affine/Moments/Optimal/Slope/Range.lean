import PLAStochastic.Affine.Error.Attainment
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Topology

/-!
# The actual slope-range functional on continuous unit-interval paths

The upper and lower residual extrema define the manuscript's range. Fixed-slope
intercept optimization, convexity, a global Lipschitz bound, coercivity, and the
compact interval of minimizing slopes are derived from this definition.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace BrownianAffine

abbrev RangeTime := Set.Icc (0 : ℝ) 1

def rangeTimeZero : RangeTime := ⟨0, by simp⟩
def rangeTimeOne : RangeTime := ⟨1, by simp⟩

/-- Residual before choosing an intercept. -/
def slopeResidual (g : Path 1) (a : ℝ) (t : RangeTime) : ℝ := g t - a * (t : ℝ)

def slopeUpper (g : Path 1) (a : ℝ) : ℝ := sSup (Set.range (slopeResidual g a))
def slopeLower (g : Path 1) (a : ℝ) : ℝ := sInf (Set.range (slopeResidual g a))

def slopeRange (g : Path 1) (a : ℝ) : ℝ := slopeUpper g a - slopeLower g a

def slopeMidpoint (g : Path 1) (a : ℝ) : ℝ := (slopeUpper g a + slopeLower g a) / 2

def slopeMinimum (g : Path 1) : ℝ := sInf (Set.range (slopeRange g))

def slopeMinimizers (g : Path 1) : Set ℝ := {a | slopeRange g a = slopeMinimum g}

theorem continuous_slopeResidual (g : Path 1) (a : ℝ) : Continuous (slopeResidual g a) := by
  unfold slopeResidual
  fun_prop

theorem compact_slopeResidual_range (g : Path 1) (a : ℝ) :
    IsCompact (Set.range (slopeResidual g a)) :=
  isCompact_range (continuous_slopeResidual g a)

private theorem slopeResidual_range_nonempty (g : Path 1) (a : ℝ) :
    (Set.range (slopeResidual g a)).Nonempty := ⟨_, ⟨rangeTimeZero, rfl⟩⟩

theorem slopeUpper_attained (g : Path 1) (a : ℝ) :
    ∃ t : RangeTime, slopeResidual g a t = slopeUpper g a :=
  (compact_slopeResidual_range g a).sSup_mem (slopeResidual_range_nonempty g a)

theorem slopeLower_attained (g : Path 1) (a : ℝ) :
    ∃ t : RangeTime, slopeResidual g a t = slopeLower g a :=
  (compact_slopeResidual_range g a).sInf_mem (slopeResidual_range_nonempty g a)

theorem slopeResidual_le_upper (g : Path 1) (a : ℝ) (t : RangeTime) :
    slopeResidual g a t ≤ slopeUpper g a :=
  le_csSup (compact_slopeResidual_range g a).bddAbove ⟨t, rfl⟩

theorem slopeLower_le_residual (g : Path 1) (a : ℝ) (t : RangeTime) :
    slopeLower g a ≤ slopeResidual g a t :=
  csInf_le (compact_slopeResidual_range g a).bddBelow ⟨t, rfl⟩

theorem slopeResidual_sub_le_range (g : Path 1) (a : ℝ) (s t : RangeTime) :
    slopeResidual g a s - slopeResidual g a t ≤ slopeRange g a :=
  sub_le_sub (slopeResidual_le_upper g a s) (slopeLower_le_residual g a t)

/-- Pairwise residual differences characterize the actual maximum-minus-minimum range. -/
theorem slopeRange_le_iff (g : Path 1) (a r : ℝ) :
    slopeRange g a ≤ r ↔ ∀ s t : RangeTime, slopeResidual g a s - slopeResidual g a t ≤ r := by
  constructor
  · intro h s t
    exact (slopeResidual_sub_le_range g a s t).trans h
  · intro h
    obtain ⟨s, hs⟩ := slopeUpper_attained g a
    obtain ⟨t, ht⟩ := slopeLower_attained g a
    simpa only [slopeRange, hs, ht] using! h s t

theorem slopeRange_nonnegative (g : Path 1) (a : ℝ) : 0 ≤ slopeRange g a := by
  simpa only [sub_self] using slopeResidual_sub_le_range g a rangeTimeZero rangeTimeZero

/-- The midpoint of the attained extrema has uniform residual at most half the range. -/
theorem slopeMidpoint_error (g : Path 1) (a : ℝ) (t : RangeTime) :
    |slopeResidual g a t - slopeMidpoint g a| ≤ slopeRange g a / 2 := by
  have hu := slopeResidual_le_upper g a t
  have hl := slopeLower_le_residual g a t
  unfold slopeMidpoint slopeRange
  rw [abs_le]
  constructor <;> linarith

private theorem slopePoint_error_le_dist (g : Path 1) (a b : ℝ) (t : RangeTime) :
    |slopeResidual g a t - b| ≤ dist g (a • timePath 1 + b • (1 : Path 1)) := by
  simpa [slopeResidual, Real.dist_eq, timePath, sub_sub] using!
    ContinuousMap.dist_apply_le_dist (f := g) (g := a • timePath 1 + b • (1 : Path 1)) t

/-- No intercept can improve on half of the actual residual range. -/
theorem slopeRange_half_le_dist (g : Path 1) (a b : ℝ) :
    slopeRange g a / 2 ≤ dist g (a • timePath 1 + b • (1 : Path 1)) := by
  have h : slopeRange g a ≤ 2 * dist g (a • timePath 1 + b • (1 : Path 1)) := by
    apply (slopeRange_le_iff g a _).mpr
    intro s t
    have hs := (abs_le.mp (slopePoint_error_le_dist g a b s)).2
    have ht := (abs_le.mp (slopePoint_error_le_dist g a b t)).1
    linarith
  linarith

/-- The extrema midpoint is an actual fixed-slope minimizing intercept. -/
theorem dist_slopeMidpoint (g : Path 1) (a : ℝ) :
    dist g (a • timePath 1 + slopeMidpoint g a • (1 : Path 1)) = slopeRange g a / 2 := by
  apply le_antisymm _ (slopeRange_half_le_dist g a (slopeMidpoint g a))
  let : Nonempty RangeTime := ⟨rangeTimeZero⟩
  apply ContinuousMap.dist_le_iff_of_nonempty.mpr
  intro t
  simpa [slopeResidual, Real.dist_eq, timePath, sub_sub] using slopeMidpoint_error g a t

theorem slopeMidpoint_minimizes_intercept (g : Path 1) (a b : ℝ) :
    dist g (a • timePath 1 + slopeMidpoint g a • (1 : Path 1)) ≤
      dist g (a • timePath 1 + b • (1 : Path 1)) := by
  rw [dist_slopeMidpoint]
  exact slopeRange_half_le_dist g a b

theorem optimalError_le_slopeRange_half (g : Path 1) (a : ℝ) :
    optimalError g ≤ slopeRange g a / 2 := by
  apply (optimalError_le_iff_exists_fit (by norm_num : (0 : ℝ) ≤ 1) g).mpr
  exact ⟨a, slopeMidpoint g a, slopeMidpoint_error g a⟩

/-- The infimum over slopes is attained by a slope from an actual optimal affine fit. -/
theorem exists_slopeRange_eq_two_optimal (g : Path 1) :
    ∃ a : ℝ, slopeRange g a = 2 * optimalError g := by
  obtain ⟨a, b, hab⟩ := exists_affine_minimizer g
  have hlo := optimalError_le_slopeRange_half g a
  have hhi := slopeRange_half_le_dist g a b
  exact ⟨a, by linarith⟩

/-- The manuscript's `ρ(g) = 2 F(g)` identifies the actual slope infimum. -/
theorem slopeMinimum_eq_two_optimal (g : Path 1) : slopeMinimum g = 2 * optimalError g := by
  obtain ⟨a, ha⟩ := exists_slopeRange_eq_two_optimal g
  have hglb : IsGLB (Set.range (slopeRange g)) (2 * optimalError g) := by
    constructor
    · rintro r ⟨b, rfl⟩
      have := optimalError_le_slopeRange_half g b
      linarith
    · intro r hr
      exact hr ⟨a, ha⟩
  exact hglb.csInf_eq (Set.range_nonempty _)

theorem slopeMinimum_le (g : Path 1) (a : ℝ) : slopeMinimum g ≤ slopeRange g a := by
  rw [slopeMinimum_eq_two_optimal]
  have := optimalError_le_slopeRange_half g a
  linarith

theorem slopeMinimum_nonnegative (g : Path 1) : 0 ≤ slopeMinimum g := by
  rw [slopeMinimum_eq_two_optimal]
  exact mul_nonneg (by norm_num) (bestError_nonneg _ _)

theorem slopeMinimum_attained (g : Path 1) : ∃ a : ℝ, slopeRange g a = slopeMinimum g := by
  rw [slopeMinimum_eq_two_optimal]
  exact exists_slopeRange_eq_two_optimal g

/-- Convexity comes from affine pairwise residual differences. -/
theorem convexOn_slopeRange (g : Path 1) : ConvexOn ℝ Set.univ (slopeRange g) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ u v hu hv huv
  simp only [smul_eq_mul]
  apply (slopeRange_le_iff g _ _).mpr
  intro s t
  have ha := mul_le_mul_of_nonneg_left (slopeResidual_sub_le_range g a s t) hu
  have hb := mul_le_mul_of_nonneg_left (slopeResidual_sub_le_range g b s t) hv
  unfold slopeResidual at *
  have hc : (u + v) * (g s - g t) = g s - g t := by rw [huv, one_mul]
  nlinarith [hc]

private theorem rangeTime_abs_sub_le_one (s t : RangeTime) : |(s : ℝ) - (t : ℝ)| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [s.property.1, s.property.2, t.property.1, t.property.2]

theorem slopeRange_le_add_abs (g : Path 1) (a b : ℝ) :
    slopeRange g a ≤ slopeRange g b + |a - b| := by
  apply (slopeRange_le_iff g a _).mpr
  intro s t
  have hb := slopeResidual_sub_le_range g b s t
  have he : (b - a) * ((s : ℝ) - (t : ℝ)) ≤ |a - b| := by
    calc
      (b - a) * ((s : ℝ) - (t : ℝ)) ≤ |(b - a) * ((s : ℝ) - (t : ℝ))| := le_abs_self _
      _ = |b - a| * |(s : ℝ) - (t : ℝ)| := abs_mul _ _
      _ ≤ |b - a| * 1 := mul_le_mul_of_nonneg_left (rangeTime_abs_sub_le_one s t) (abs_nonneg _)
      _ = |a - b| := by rw [mul_one, abs_sub_comm]
  unfold slopeResidual at *
  nlinarith

/-- The true range functional is globally 1-Lipschitz in slope on a unit time interval. -/
theorem slopeRange_lipschitz (g : Path 1) : LipschitzWith 1 (slopeRange g) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  simp only [Real.dist_eq, NNReal.coe_one, one_mul]
  rw [abs_le]
  have ha := slopeRange_le_add_abs g a b
  have hb := slopeRange_le_add_abs g b a
  rw [abs_sub_comm b a] at hb
  constructor <;> linarith

theorem continuous_slopeRange (g : Path 1) : Continuous (slopeRange g) :=
  (slopeRange_lipschitz g).continuous

/-- Endpoint residuals force linear growth of the range in either slope direction. -/
theorem slopeRange_endpoint_bound (g : Path 1) (a : ℝ) :
    |g rangeTimeOne - g rangeTimeZero - a| ≤ slopeRange g a := by
  have h₁ := slopeResidual_sub_le_range g a rangeTimeOne rangeTimeZero
  have h₀ := slopeResidual_sub_le_range g a rangeTimeZero rangeTimeOne
  simp only [slopeResidual, rangeTimeOne, rangeTimeZero, mul_one, mul_zero, sub_zero] at h₁ h₀
  dsimp only [rangeTimeOne, rangeTimeZero]
  rw [abs_le]
  constructor <;> linarith

theorem slopeRange_tendsto_atTop (g : Path 1) : Tendsto (slopeRange g) atTop atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [eventually_ge_atTop (g rangeTimeOne - g rangeTimeZero + r)] with a ha
  have hb := (abs_le.mp (slopeRange_endpoint_bound g a)).1
  linarith

theorem slopeRange_tendsto_atBot (g : Path 1) : Tendsto (slopeRange g) atBot atTop := by
  apply tendsto_atTop.mpr
  intro r
  filter_upwards [eventually_le_atBot (g rangeTimeOne - g rangeTimeZero - r)] with a ha
  have hb := (abs_le.mp (slopeRange_endpoint_bound g a)).2
  linarith

/-- A zero minimum would give an exact affine path, so every nonaffine path has positive `ρ`. -/
theorem slopeMinimum_positive_of_not_affine (g : Path 1)
    (hg : ¬ ∃ a b : ℝ, g = a • timePath 1 + b • (1 : Path 1)) : 0 < slopeMinimum g := by
  apply lt_of_le_of_ne (slopeMinimum_nonnegative g)
  intro hz
  obtain ⟨a, b, hab⟩ := exists_affine_minimizer g
  have hρ := slopeMinimum_eq_two_optimal g
  have hd : dist g (a • timePath 1 + b • (1 : Path 1)) = 0 := by linarith
  exact hg ⟨a, b, dist_eq_zero.mp hd⟩

theorem slopeMinimizers_nonempty (g : Path 1) : (slopeMinimizers g).Nonempty :=
  slopeMinimum_attained g

theorem slopeMinimizers_isClosed (g : Path 1) : IsClosed (slopeMinimizers g) :=
  isClosed_eq (continuous_slopeRange g) continuous_const

theorem slopeMinimizers_isCompact (g : Path 1) : IsCompact (slopeMinimizers g) := by
  apply isCompact_Icc.of_isClosed_subset (slopeMinimizers_isClosed g)
    (s := Set.Icc (g rangeTimeOne - g rangeTimeZero - slopeMinimum g)
      (g rangeTimeOne - g rangeTimeZero + slopeMinimum g))
  intro a ha
  have hb := slopeRange_endpoint_bound g a
  change slopeRange g a = slopeMinimum g at ha
  rw [ha, abs_le] at hb
  constructor <;> linarith

theorem slopeMinimizers_convex (g : Path 1) : Convex ℝ (slopeMinimizers g) := by
  have heq : slopeMinimizers g = {a ∈ (Set.univ : Set ℝ) | slopeRange g a ≤ slopeMinimum g} := by
    ext a
    simp only [slopeMinimizers, Set.mem_ofPred_eq, Set.mem_univ, true_and]
    exact ⟨fun h => h.le, fun h => le_antisymm h (slopeMinimum_le g a)⟩
  rw [heq]
  exact (convexOn_slopeRange g).convex_le _

/-- All minimizing slopes form one nonempty compact interval, including the possible singleton case. -/
theorem slopeMinimizers_eq_Icc (g : Path 1) :
    slopeMinimizers g = Set.Icc (sInf (slopeMinimizers g)) (sSup (slopeMinimizers g)) :=
  eq_Icc_of_connected_compact
    ⟨slopeMinimizers_nonempty g, Real.convex_iff_isPreconnected.mp (slopeMinimizers_convex g)⟩
    (slopeMinimizers_isCompact g)

theorem slopeMinimizers_endpoints_ordered (g : Path 1) :
    sInf (slopeMinimizers g) ≤ sSup (slopeMinimizers g) := by
  have h := slopeMinimizers_nonempty g
  rw [slopeMinimizers_eq_Icc] at h
  exact Set.nonempty_Icc.mp h

theorem slopeMinimizers_left_mem (g : Path 1) : sInf (slopeMinimizers g) ∈ slopeMinimizers g :=
  (slopeMinimizers_isCompact g).sInf_mem (slopeMinimizers_nonempty g)

theorem slopeMinimizers_right_mem (g : Path 1) : sSup (slopeMinimizers g) ∈ slopeMinimizers g :=
  (slopeMinimizers_isCompact g).sSup_mem (slopeMinimizers_nonempty g)

end BrownianAffine
