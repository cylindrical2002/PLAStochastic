import Mathlib.NumberTheory.LSeries.HurwitzZeta
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

/-! # Hurwitz-type series at the shift `3/2`

Let `H(w) = ζ(w, 3/2) = ∑_{n ≥ 0} (n + 3/2)^{-w}`, continued from Mathlib's `hurwitzZeta`
at the parameter `1/2` by removing the `n = 0` term. For coefficient functions `a k` with
locally uniform bounds `‖a k z‖ ≤ C * 2 ^ k`, this file studies

`hzSeries a b z = ∑_k a k z * H(2z + b + 2k)`.

* `hasSum_hurwitzZetaThreeHalves`: the Dirichlet series of `H` for `1 < re w`.
* `norm_hurwitzZetaThreeHalves_le`: `‖H w‖ ≤ hzConst * (4/9)^k` once `2 + 2k ≤ re w`.
* `summable_hzSeries`, `differentiableAt_hzSeries`: the series converges everywhere and is
  holomorphic at every `z` with `2z + b + 2k ≠ 1` for all `k`.
* `hasSum_hzSeries`: in the convergence region, `hzSeries` is the sum over `n` of the
  rearranged double series `∑_k a k z (n + 3/2)^{-(2z + b + 2k)}` (absolute Fubini).
-/

noncomputable section

open Complex Filter Topology

namespace BrownianAffine.SpectralZeta

/-- The Hurwitz zeta function `ζ(w, 3/2) = ∑_{n ≥ 0} (n + 3/2)^{-w}`, obtained from Mathlib's
`hurwitzZeta` at `1/2` by removing the `n = 0` term. -/
def hurwitzZetaThreeHalves (w : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) w - 1 / (1 / 2 : ℂ) ^ w

theorem hasSum_hurwitzZetaThreeHalves {w : ℂ} (hw : 1 < w.re) :
    HasSum (fun n : ℕ => ((n : ℂ) + 3 / 2) ^ (-w)) (hurwitzZetaThreeHalves w) := by
  have h := (hasSum_nat_add_iff' 1).2
    (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re (a := 1 / 2) (by norm_num) hw)
  have e1 : (fun n : ℕ => ((n : ℂ) + 3 / 2) ^ (-w)) =
      fun n : ℕ => 1 / (((n + 1 : ℕ) : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ w := by
    funext n
    rw [cpow_neg, ← one_div]
    congr 2
    push_cast
    ring
  have e2 : hurwitzZetaThreeHalves w = HurwitzZeta.hurwitzZeta ((1 / 2 : ℝ) : UnitAddCircle) w -
      ∑ i ∈ Finset.range 1, 1 / ((i : ℂ) + ((1 / 2 : ℝ) : ℂ)) ^ w := by
    rw [hurwitzZetaThreeHalves, Finset.sum_range_one]
    push_cast
    simp
  rw [e1, e2]
  exact h

theorem differentiableAt_hurwitzZetaThreeHalves {w : ℂ} (hw : w ≠ 1) :
    DifferentiableAt ℂ hurwitzZetaThreeHalves w := by
  have h2 : (1 / 2 : ℂ) ^ w ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    norm_num
  exact (HurwitzZeta.differentiableAt_hurwitzZeta _ hw).sub
    ((differentiableAt_const _).div (differentiableAt_id.const_cpow (Or.inl (by norm_num))) h2)

/-- The constant `∑_{n ≥ 0} (n + 3/2)^{-2}` bounding `H` on half-planes. -/
def hzConst : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 3 / 2) ^ 2

theorem summable_one_div_nat_add_three_halves_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 3 / 2) ^ σ) := by
  refine ((Real.summable_one_div_nat_add_rpow (3 / 2) σ).2 hσ).congr fun n => ?_
  rw [abs_of_pos (by positivity)]

theorem summable_hzConst : Summable (fun n : ℕ => 1 / ((n : ℝ) + 3 / 2) ^ 2) := by
  refine (summable_one_div_nat_add_three_halves_rpow (σ := 2) (by norm_num)).congr fun n => ?_
  rw [Real.rpow_two]

theorem one_le_nat_add_three_halves (n : ℕ) : (1 : ℝ) ≤ n + 3 / 2 := by
  have := n.cast_nonneg (α := ℝ)
  linarith

theorem one_div_sq_nat_add_three_halves_le (n : ℕ) : 1 / ((n : ℝ) + 3 / 2) ^ 2 ≤ 4 / 9 := by
  have h : (3 / 2 : ℝ) ≤ n + 3 / 2 := by
    have := n.cast_nonneg (α := ℝ)
    linarith
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

/-- For `x ≥ 1` (here `x = n + 3/2`), `x ^ (-(σ + 2k)) ≤ x ^ (-σ) * (4/9)^k`. -/
theorem rpow_neg_add_two_mul_le (n k : ℕ) (σ : ℝ) :
    ((n : ℝ) + 3 / 2) ^ (-(σ + 2 * k)) ≤ 1 / ((n : ℝ) + 3 / 2) ^ σ * (4 / 9) ^ k := by
  have hu : (0 : ℝ) < n + 3 / 2 := by positivity
  rw [neg_add, Real.rpow_add hu, Real.rpow_neg hu.le, ← one_div,
    show (-(2 * (k : ℝ))) = -((2 * k : ℕ) : ℝ) by push_cast; ring, Real.rpow_neg hu.le,
    Real.rpow_natCast, pow_mul, ← one_div, ← one_div_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (one_div_sq_nat_add_three_halves_le n) k) (by positivity)

theorem norm_hurwitzZetaThreeHalves_le {k : ℕ} {w : ℂ} (hw : 2 + 2 * (k : ℝ) ≤ w.re) :
    ‖hurwitzZetaThreeHalves w‖ ≤ hzConst * (4 / 9) ^ k := by
  have hw1 : 1 < w.re := by linarith [k.cast_nonneg (α := ℝ)]
  refine (hasSum_hurwitzZetaThreeHalves hw1).norm_le_of_bounded
    (summable_hzConst.hasSum.mul_right ((4 / 9 : ℝ) ^ k)) fun n => ?_
  have hu : (0 : ℝ) < n + 3 / 2 := by positivity
  rw [show ((n : ℂ) + 3 / 2) = ((n + 3 / 2 : ℝ) : ℂ) by push_cast; ring,
    norm_cpow_eq_rpow_re_of_pos hu, neg_re]
  calc ((n : ℝ) + 3 / 2) ^ (-w.re) ≤ ((n : ℝ) + 3 / 2) ^ (-(2 + 2 * (k : ℝ))) :=
        Real.rpow_le_rpow_of_exponent_le (one_le_nat_add_three_halves n) (by linarith)
    _ ≤ 1 / ((n : ℝ) + 3 / 2) ^ (2 : ℝ) * (4 / 9) ^ k := rpow_neg_add_two_mul_le n k 2
    _ = 1 / ((n : ℝ) + 3 / 2) ^ 2 * (4 / 9) ^ k := by rw [Real.rpow_two]

/-- A family of coefficient functions bounded by `C * 2 ^ k` on every ball. -/
def GeomBounded (a : ℕ → ℂ → ℂ) : Prop :=
  ∀ R : ℝ, ∃ C : ℝ, ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ‖a k z‖ ≤ C * 2 ^ k

/-- The Hurwitz-type series `∑_k a_k(z) ζ(2z + b + 2k, 3/2)`. -/
def hzSeries (a : ℕ → ℂ → ℂ) (b z : ℂ) : ℂ :=
  ∑' k : ℕ, a k z * hurwitzZetaThreeHalves (2 * z + b + 2 * k)

theorem two_add_two_mul_le_re {b z : ℂ} {R : ℝ} {K : ℕ} (hz : ‖z‖ ≤ R)
    (hK : 2 * R + ‖b‖ + 2 ≤ 2 * K) (k : ℕ) :
    2 + 2 * (k : ℝ) ≤ (2 * z + b + 2 * ((k + K : ℕ) : ℂ)).re := by
  have h1 : -R ≤ z.re := by
    have := abs_re_le_norm z
    have := neg_abs_le z.re
    linarith
  have h2 : -‖b‖ ≤ b.re := by
    have := abs_re_le_norm b
    have := neg_abs_le b.re
    linarith
  simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re, Nat.cast_add]
  linarith

theorem norm_hzSeries_term_le {a : ℕ → ℂ → ℂ} {b z : ℂ} {R C : ℝ} {K : ℕ}
    (hz : ‖z‖ ≤ R) (hC : ∀ k, ‖a k z‖ ≤ C * 2 ^ k) (hK : 2 * R + ‖b‖ + 2 ≤ 2 * K) (k : ℕ) :
    ‖a (k + K) z * hurwitzZetaThreeHalves (2 * z + b + 2 * ((k + K : ℕ) : ℂ))‖ ≤
      C * 2 ^ K * hzConst * (8 / 9) ^ k := by
  have hH := norm_hurwitzZetaThreeHalves_le (two_add_two_mul_le_re hz hK k)
  have hA := hC (k + K)
  rw [norm_mul]
  calc ‖a (k + K) z‖ * ‖hurwitzZetaThreeHalves (2 * z + b + 2 * ((k + K : ℕ) : ℂ))‖
      ≤ (C * 2 ^ (k + K)) * (hzConst * (4 / 9) ^ k) :=
        mul_le_mul hA hH (norm_nonneg _) (le_trans (norm_nonneg _) hA)
    _ = C * 2 ^ K * hzConst * (8 / 9) ^ k := by
        rw [pow_add, show (8 / 9 : ℝ) = 2 * (4 / 9) by norm_num, mul_pow]
        ring

theorem exists_nat_two_mul_ge (R : ℝ) (b : ℂ) : ∃ K : ℕ, 2 * R + ‖b‖ + 2 ≤ 2 * K := by
  refine ⟨⌈|R| + ‖b‖ + 1⌉₊, ?_⟩
  have h := Nat.le_ceil (|R| + ‖b‖ + 1)
  have := le_abs_self R
  have := norm_nonneg b
  linarith

theorem summable_hzSeries {a : ℕ → ℂ → ℂ} (ha : GeomBounded a) (b z : ℂ) :
    Summable (fun k : ℕ => a k z * hurwitzZetaThreeHalves (2 * z + b + 2 * k)) := by
  obtain ⟨C, hC⟩ := ha ‖z‖
  obtain ⟨K, hK⟩ := exists_nat_two_mul_ge ‖z‖ b
  refine (summable_nat_add_iff K).1 ?_
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left (C * 2 ^ K * hzConst))
    (norm_hzSeries_term_le le_rfl (fun k => hC k z le_rfl) hK)

theorem hurwitzZetaThreeHalves_comp_differentiableAt {b z : ℂ} (k : ℕ)
    (hz : 2 * z + b + 2 * (k : ℂ) ≠ 1) :
    DifferentiableAt ℂ (fun z : ℂ => hurwitzZetaThreeHalves (2 * z + b + 2 * (k : ℂ))) z :=
  (differentiableAt_hurwitzZetaThreeHalves hz).comp (f := fun z : ℂ => 2 * z + b + 2 * (k : ℂ)) z
    (by fun_prop)

theorem hzSeries_eq_sum_add_tail {a : ℕ → ℂ → ℂ} (ha : GeomBounded a) (b z : ℂ) (K : ℕ) :
    hzSeries a b z =
      (∑ k ∈ Finset.range K, a k z * hurwitzZetaThreeHalves (2 * z + b + 2 * k)) +
        ∑' k : ℕ, a (k + K) z * hurwitzZetaThreeHalves (2 * z + b + 2 * ((k + K : ℕ) : ℂ)) := by
  have hs := summable_hzSeries ha b z
  rw [← summable_nat_add_iff K] at hs
  exact (hs.sum_add_tsum_nat_add' (f := fun k : ℕ => a k z *
    hurwitzZetaThreeHalves (2 * z + b + 2 * k))).symm

theorem differentiableAt_hzSeries {a : ℕ → ℂ → ℂ} (hd : ∀ k, Differentiable ℂ (a k))
    (ha : GeomBounded a) (b : ℂ) {z₀ : ℂ} (hz₀ : ∀ k : ℕ, 2 * z₀ + b + 2 * k ≠ 1) :
    DifferentiableAt ℂ (hzSeries a b) z₀ := by
  obtain ⟨C, hC⟩ := ha (‖z₀‖ + 1)
  obtain ⟨K, hK⟩ := exists_nat_two_mul_ge (‖z₀‖ + 1) b
  have hsplit : hzSeries a b = fun z =>
      (∑ k ∈ Finset.range K, a k z * hurwitzZetaThreeHalves (2 * z + b + 2 * k)) +
        ∑' k : ℕ, a (k + K) z * hurwitzZetaThreeHalves (2 * z + b + 2 * ((k + K : ℕ) : ℂ)) :=
    funext fun z => hzSeries_eq_sum_add_tail ha b z K
  rw [hsplit]
  refine DifferentiableAt.add ?_ ?_
  · refine DifferentiableAt.fun_sum fun k _ => ?_
    exact ((hd k) z₀).mul (hurwitzZetaThreeHalves_comp_differentiableAt k (hz₀ k))
  · have hdiff : DifferentiableOn ℂ (fun z => ∑' k : ℕ, a (k + K) z *
        hurwitzZetaThreeHalves (2 * z + b + 2 * ((k + K : ℕ) : ℂ))) (Metric.ball 0 (‖z₀‖ + 1)) := by
      refine differentiableOn_tsum_of_summable_norm
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left
          (C * 2 ^ K * hzConst)) (fun k => ?_) Metric.isOpen_ball
        (fun k z hz => norm_hzSeries_term_le (le_of_lt (mem_ball_zero_iff.1 hz))
          (fun k => hC k z (le_of_lt (mem_ball_zero_iff.1 hz))) hK k)
      intro z hz
      have hre := two_add_two_mul_le_re (le_of_lt (mem_ball_zero_iff.1 hz)) hK k
      have hne : 2 * z + b + 2 * ((k + K : ℕ) : ℂ) ≠ 1 := by
        intro h
        rw [h, one_re] at hre
        linarith [k.cast_nonneg (α := ℝ)]
      exact ((hd (k + K)) z).mul
        (hurwitzZetaThreeHalves_comp_differentiableAt (k + K) hne) |>.differentiableWithinAt
    exact hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp))

/-- Absolute Fubini: in the convergence region, `hzSeries` is the sum over `n` of the
expansions `∑_k a_k (n + 3/2)^{-(2z + b + 2k)}`. -/
theorem hasSum_hzSeries {a : ℕ → ℂ → ℂ} {b z : ℂ} {C : ℝ} (hz : 1 < (2 * z + b).re)
    (hC : ∀ k, ‖a k z‖ ≤ C * 2 ^ k) :
    HasSum (fun n : ℕ => ∑' k : ℕ, a k z * ((n : ℂ) + 3 / 2) ^ (-(2 * z + b + 2 * k)))
      (hzSeries a b z) := by
  set σ := (2 * z + b).re with hσ
  set f : ℕ → ℕ → ℂ := fun n k => a k z * ((n : ℂ) + 3 / 2) ^ (-(2 * z + b + 2 * k)) with hf
  have hC0 : 0 ≤ C := by
    have := hC 0
    simp only [pow_zero, mul_one] at this
    exact le_trans (norm_nonneg _) this
  have hbound : ∀ n k, ‖f n k‖ ≤ 1 / ((n : ℝ) + 3 / 2) ^ σ * (C * (8 / 9) ^ k) := by
    intro n k
    have hu : (0 : ℝ) < n + 3 / 2 := by positivity
    simp only [hf]
    rw [norm_mul, show ((n : ℂ) + 3 / 2) = ((n + 3 / 2 : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos hu]
    have hre : (-(2 * z + b + 2 * (k : ℂ))).re = -(σ + 2 * k) := by
      simp [hσ]
    rw [hre]
    have h1 := rpow_neg_add_two_mul_le n k σ
    calc ‖a k z‖ * ((n : ℝ) + 3 / 2) ^ (-(σ + 2 * k))
        ≤ (C * 2 ^ k) * (1 / ((n : ℝ) + 3 / 2) ^ σ * (4 / 9) ^ k) :=
          mul_le_mul (hC k) h1 (by positivity) (by positivity)
      _ = 1 / ((n : ℝ) + 3 / 2) ^ σ * (C * (8 / 9) ^ k) := by
          rw [show (8 / 9 : ℝ) = 2 * (4 / 9) by norm_num, mul_pow]
          ring
  have hsum : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded
      (g := fun p : ℕ × ℕ => 1 / ((p.1 : ℝ) + 3 / 2) ^ σ * (C * (8 / 9) ^ p.2)) ?_ ?_
    · exact Summable.mul_of_nonneg (f := fun n : ℕ => 1 / ((n : ℝ) + 3 / 2) ^ σ)
        (g := fun k : ℕ => C * (8 / 9 : ℝ) ^ k)
        (summable_one_div_nat_add_three_halves_rpow hz)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left C)
        (fun n => by positivity) (fun k => by positivity)
    · rintro ⟨n, k⟩
      exact hbound n k
  have h1 : HasSum (fun n => ∑' k, f n k) (∑' n, ∑' k, f n k) := hsum.prod.hasSum
  convert h1 using 1
  rw [← hsum.tsum_comm]
  unfold hzSeries
  congr 1
  ext k
  simp only [hf]
  rw [tsum_mul_left, (hasSum_hurwitzZetaThreeHalves _).tsum_eq]
  have : (2 * z + b + 2 * (k : ℂ)).re = σ + 2 * k := by simp [hσ]
  rw [this]
  linarith [k.cast_nonneg (α := ℝ)]

end BrownianAffine.SpectralZeta
