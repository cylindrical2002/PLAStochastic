import PLAStochastic.ForMathlib.Topology.ContinuousMap.PolygonalInterpolation
import PLAStochastic.Brownian.Construction.DyadicEdges

/-! Deterministic bounds for successive dyadic polygonal interpolants. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

/-- Two fine-grid edges control the distance between consecutive polygonal refinements. -/
theorem realPolygon_refinement_bound (f g : ℤ → ℝ) (t : ℝ) {a : ℝ} (ha : 0 ≤ a)
    (he : ∀ k : ℤ, g (2 * k) = f k)
    (h0 : |g (2 * ⌊t⌋ + 1) - g (2 * ⌊t⌋)| ≤ a)
    (h1 : |g (2 * ⌊t⌋ + 2) - g (2 * ⌊t⌋ + 1)| ≤ a) :
    |realPolygon g (2 * t) - realPolygon f t| ≤ 4 * a := by
  let k : ℤ := ⌊t⌋
  have hlo : 2 * k ≤ ⌊2 * t⌋ := by
    apply Int.le_floor.mpr
    simp only [Int.cast_mul, Int.cast_ofNat]
    exact mul_le_mul_of_nonneg_left (Int.floor_le t) (by norm_num)
  have hhi : ⌊2 * t⌋ < 2 * k + 2 := by
    apply Int.floor_lt.mpr
    have hh := Int.lt_floor_add_one t
    simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
    dsimp only [k]
    linarith
  have hcases : ⌊2 * t⌋ = 2 * k ∨ ⌊2 * t⌋ = 2 * k + 1 := by omega
  have h2 : |g (2 * k + 2) - g (2 * k)| ≤ 2 * a := by
    calc
      _ ≤ |g (2 * k + 2) - g (2 * k + 1)| + |g (2 * k + 1) - g (2 * k)| := abs_sub_le _ _ _
      _ ≤ a + a := add_le_add h1 h0
      _ = _ := by ring
  have hcoarse : |realPolygon f t - g (2 * k)| ≤ 2 * a := by
    apply realPolygon_dist_le
    · rw [he, show k = ⌊t⌋ from rfl, sub_self, abs_zero]
      positivity
    · have hk : 2 * (k + 1) = 2 * k + 2 := by ring
      change |f (k + 1) - g (2 * k)| ≤ 2 * a
      rw [← he (k + 1), hk]
      exact h2
  have hfine : |realPolygon g (2 * t) - g (2 * k)| ≤ 2 * a := by
    apply realPolygon_dist_le
    · rcases hcases with h | h
      · rw [h, sub_self, abs_zero]; positivity
      · rw [h]; exact h0.trans (by linarith)
    · rcases hcases with h | h
      · rw [h]; exact h0.trans (by linarith)
      · simpa only [h, add_assoc, one_add_one_eq_two] using h2
  calc
    _ ≤ |realPolygon g (2 * t) - g (2 * k)| + |g (2 * k) - realPolygon f t| := abs_sub_le _ _ _
    _ = |realPolygon g (2 * t) - g (2 * k)| + |realPolygon f t - g (2 * k)| := by rw [abs_sub_comm (g (2 * k))]
    _ ≤ 2 * a + 2 * a := add_le_add hfine hcoarse
    _ = _ := by ring

theorem dyadicTime_double (n k : ℕ) : dyadicTime (n + 1) (2 * k) = dyadicTime n k := by
  apply NNReal.coe_injective
  simp only [dyadicTime, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_mul,
    NNReal.coe_natCast, NNReal.coe_ofNat, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

/-- Dyadic interpolation of the actual coordinates; negative integer indices are truncated at zero. -/
def dyadicPolygon {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  realPolygon (fun k : ℤ => B (dyadicTime n k.toNat) ω) ((2 : ℝ) ^ n * t)

theorem continuous_dyadicPolygon {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    Continuous (fun t : ℝ≥0 => dyadicPolygon B n t ω) :=
  (continuous_realPolygon _).comp (continuous_const.mul continuous_subtype_val)

theorem dyadicPolygon_at_grid {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (n k : ℕ) (ω : Ω) :
    dyadicPolygon B n (dyadicTime n k) ω = B (dyadicTime n k) ω := by
  unfold dyadicPolygon
  have he : (2 : ℝ) ^ n * (dyadicTime n k : ℝ) = (k : ℤ) := by
    simp only [dyadicTime, NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat,
      Int.cast_natCast]
    field_simp
  rw [he, realPolygon_int, Int.toNat_natCast]

private theorem dyadicSequence_refines {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) (k : ℤ) :
    B (dyadicTime (n + 1) (2 * k).toNat) ω = B (dyadicTime n k.toNat) ω := by
  have hk : (2 * k).toNat = 2 * k.toNat := by omega
  rw [hk, dyadicTime_double]

/-- Uniform fine-edge control gives a uniform bound on one interpolation refinement. -/
theorem dyadicPolygon_step_bound {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (n K : ℕ) (ω : Ω)
    {a : ℝ} (ha : 0 ≤ a)
    (hinc : ∀ j < K * 2 ^ (n + 1),
      |B (dyadicTime (n + 1) (j + 1)) ω - B (dyadicTime (n + 1) j) ω| ≤ a)
    (t : ℝ≥0) (ht : t < K) :
    |dyadicPolygon B (n + 1) t ω - dyadicPolygon B n t ω| ≤ 4 * a := by
  let k : ℤ := ⌊(2 : ℝ) ^ n * t⌋
  have hk : 0 ≤ k := Int.floor_nonneg.mpr (by positivity)
  have hcast : (k.toNat : ℝ) = k := by exact_mod_cast Int.toNat_of_nonneg hk
  have hkK : k.toNat < K * 2 ^ n := by
    have hh : (k.toNat : ℝ) < ((K * 2 ^ n : ℕ) : ℝ) := by
      rw [hcast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      calc
        (k : ℝ) ≤ (2 : ℝ) ^ n * t := Int.floor_le _
        _ < K * (2 : ℝ) ^ n := by exact_mod_cast (mul_lt_mul_of_pos_left ht (by positivity : (0 : ℝ≥0) < 2 ^ n)) |>.trans_eq (mul_comm _ _)
    exact_mod_cast hh
  have hcount : K * 2 ^ (n + 1) = 2 * (K * 2 ^ n) := by rw [pow_succ]; ring
  have he0 : (2 * k).toNat = 2 * k.toNat := by omega
  have he1 : (2 * k + 1).toNat = 2 * k.toNat + 1 := by omega
  have he2 : (2 * k + 2).toNat = 2 * k.toNat + 2 := by omega
  have h0 := hinc (2 * k.toNat) (by rw [hcount]; omega)
  have h1 := hinc (2 * k.toNat + 1) (by rw [hcount]; omega)
  have h0' : |B (dyadicTime (n + 1) (2 * k + 1).toNat) ω -
      B (dyadicTime (n + 1) (2 * k).toNat) ω| ≤ a := by simpa only [he0, he1] using h0
  have h1' : |B (dyadicTime (n + 1) (2 * k + 2).toNat) ω -
      B (dyadicTime (n + 1) (2 * k + 1).toNat) ω| ≤ a := by
    simpa only [he1, he2, add_assoc, one_add_one_eq_two] using h1
  have herr := realPolygon_refinement_bound
    (fun j : ℤ => B (dyadicTime n j.toNat) ω)
    (fun j : ℤ => B (dyadicTime (n + 1) j.toNat) ω)
    ((2 : ℝ) ^ n * t) ha (dyadicSequence_refines B n ω) h0' h1'
  unfold dyadicPolygon
  rw [show (2 : ℝ) ^ (n + 1) * t = 2 * ((2 : ℝ) ^ n * t) by rw [pow_succ]; ring]
  exact herr

end BrownianAffine
