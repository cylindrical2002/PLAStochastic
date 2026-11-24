import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Tactic

/-! Continuous polygonal interpolation on the integer grid. -/

noncomputable section
open Filter Set
open scoped NNReal ENNReal Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Polygonal interpolation of a two-sided sequence on the integer grid. -/
def realPolygon (f : ℤ → ℝ) (t : ℝ) : ℝ :=
  (1 - Int.fract t) * f ⌊t⌋ + Int.fract t * f (⌊t⌋ + 1)

@[simp] theorem realPolygon_int (f : ℤ → ℝ) (k : ℤ) : realPolygon f k = f k := by
  simp [realPolygon]

private theorem tendsto_seq_of_floor {l : Filter ℝ} {k : ℤ}
    (h : Tendsto Int.floor l (pure k)) (f : ℤ → ℝ) :
    Tendsto (fun t => f ⌊t⌋) l (𝓝 (f k)) :=
  ((tendsto_pure_pure f k).comp h).mono_right (pure_le_nhds _)

/-- Polygonal interpolation is continuous even at the grid vertices. -/
theorem continuous_realPolygon (f : ℤ → ℝ) : Continuous (realPolygon f) := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : ∃ k : ℤ, t = k
  · obtain ⟨k, rfl⟩ := ht
    rw [ContinuousAt, ← nhdsLT_sup_nhdsGE (k : ℝ), tendsto_sup]
    constructor
    · rw [realPolygon_int]
      change Tendsto (fun x => (1 - Int.fract x) * f ⌊x⌋ + Int.fract x * f (⌊x⌋ + 1)) _ (𝓝 (f k))
      have hfloor := tendsto_floor_left_pure_sub_one (α := ℝ) k
      have hfrac := tendsto_fract_left' (α := ℝ) k
      have h1 := tendsto_seq_of_floor hfloor f
      have h2 := tendsto_seq_of_floor hfloor (fun j => f (j + 1))
      have h := (((show Tendsto (fun _ : ℝ => (1 : ℝ)) _ (𝓝 1) from tendsto_const_nhds).sub hfrac).mul h1).add (hfrac.mul h2)
      simpa only [sub_self, zero_mul, one_mul, zero_add, sub_add_cancel] using h
    · rw [realPolygon_int]
      change Tendsto (fun x => (1 - Int.fract x) * f ⌊x⌋ + Int.fract x * f (⌊x⌋ + 1)) _ (𝓝 (f k))
      have hfloor := tendsto_floor_right_pure (α := ℝ) k
      have hfrac := tendsto_fract_right' (α := ℝ) k
      have h1 := tendsto_seq_of_floor hfloor f
      have h2 := tendsto_seq_of_floor hfloor (fun j => f (j + 1))
      have h := (((show Tendsto (fun _ : ℝ => (1 : ℝ)) _ (𝓝 1) from tendsto_const_nhds).sub hfrac).mul h1).add (hfrac.mul h2)
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using h
  · have hne : t ≠ (⌊t⌋ : ℤ) := fun h => ht ⟨_, h⟩
    have hfloor : Tendsto Int.floor (𝓝 t) (pure ⌊t⌋) := by
      apply tendsto_pure.mpr
      filter_upwards [Ico_mem_nhds ((Int.floor_le t).lt_of_ne hne.symm) (Int.lt_floor_add_one t)] with s hs
      exact Int.floor_eq_on_Ico _ _ hs
    exact ((continuousAt_const.sub (continuousAt_fract hne)).mul (tendsto_seq_of_floor hfloor f)).add
      ((continuousAt_fract hne).mul (tendsto_seq_of_floor hfloor (fun j => f (j + 1))))

/-- On a closed grid cell the interpolant is the affine combination of its endpoints. -/
theorem realPolygon_eq_affine (f : ℤ → ℝ) {t : ℝ} {k : ℤ}
    (ht : t ∈ Icc (k : ℝ) (k + 1)) :
    realPolygon f t = (1 - (t - k)) * f k + (t - k) * f (k + 1) := by
  rcases ht.2.eq_or_lt with he | he
  · have hte : t = ((k + 1 : ℤ) : ℝ) := by simpa only [Int.cast_add, Int.cast_one] using he
    rw [hte, realPolygon_int]
    simp
  · have hfloor : ⌊t⌋ = k := Int.floor_eq_on_Ico _ _ ⟨ht.1, he⟩
    simp only [realPolygon, Int.fract, hfloor]

/-- Endpoint distance bounds are preserved by the polygonal interpolation. -/
theorem realPolygon_dist_le (f : ℤ → ℝ) (t y a : ℝ)
    (h0 : |f ⌊t⌋ - y| ≤ a) (h1 : |f (⌊t⌋ + 1) - y| ≤ a) :
    |realPolygon f t - y| ≤ a := by
  have hu0 : 0 ≤ Int.fract t := Int.fract_nonneg t
  have hu1 : Int.fract t ≤ 1 := (Int.fract_lt_one t).le
  have he : realPolygon f t - y = (1 - Int.fract t) * (f ⌊t⌋ - y) +
      Int.fract t * (f (⌊t⌋ + 1) - y) := by unfold realPolygon; ring
  rw [he]
  calc
    _ ≤ |(1 - Int.fract t) * (f ⌊t⌋ - y)| + |Int.fract t * (f (⌊t⌋ + 1) - y)| := abs_add_le _ _
    _ = (1 - Int.fract t) * |f ⌊t⌋ - y| + Int.fract t * |f (⌊t⌋ + 1) - y| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hu1), abs_of_nonneg hu0]
    _ ≤ (1 - Int.fract t) * a + Int.fract t * a := by gcongr
    _ = a := by ring

end BrownianAffine
