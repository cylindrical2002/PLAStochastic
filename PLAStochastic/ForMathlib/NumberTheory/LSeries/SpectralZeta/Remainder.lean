import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.Basic

/-! # The quadratic remainder in the symmetric splitting

Fix `N : ℕ` and `m : ℕ`, and put `u = m + 3/2`, `x = 1/(2u)`, `α = (m+1)^{-z}`,
`β = (m+2)^{-z}` and `P = ((m+1)(m+2))^N`. Then
`((m+1)(m+2))^{-(z-N)} = P α β = P (α² + β²)/2 - P (α - β)²/2`.

The binomial series gives `α - β = u^{-z} 2 z x T(z, x²)` with
`T(z, y) = ∑_i (z+1)_{2i}/(2i+1)! y^i`, so the remainder `P (α - β)²/2` carries the explicit
factor `2 z²`. Expanding `P = ∑_j C(N,j) (-1/4)^j u^{2(N-j)}` and `T²` (Cauchy product),

`∑_m P (α - β)²/2 = 2 z² remSeries N z`   for `re z > N + 1/2`,

where `remSeries N` is a finite combination of Hurwitz-type series, holomorphic wherever
`2z` is not an odd integer (in particular near `z = 0`).
-/

noncomputable section

open Complex Polynomial Finset

namespace BrownianAffine.SpectralZeta

/-- `(z+1)_{2i} / (2i+1)!`, so that `(z)_{2i+1} / (2i+1)! = z * oddCoeff z i`. -/
def oddCoeff (z : ℂ) (i : ℕ) : ℂ :=
  (ascPochhammer ℂ (2 * i)).eval (z + 1) / (2 * i + 1).factorial

theorem pochCoeff_two_mul_add_one (z : ℂ) (i : ℕ) :
    pochCoeff z (2 * i + 1) = z * oddCoeff z i := by
  rw [pochCoeff, oddCoeff, ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add,
    eval_X, eval_one, mul_div_assoc]

theorem norm_oddCoeff_le (z : ℂ) (i : ℕ) : ‖oddCoeff z i‖ ≤ 2 ^ (‖z‖ + 1) * 4 ^ i := by
  have h1 : ‖oddCoeff z i‖ ≤ ‖pochCoeff (z + 1) (2 * i)‖ := by
    rw [oddCoeff, pochCoeff, norm_div, norm_div, Complex.norm_natCast, Complex.norm_natCast]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by exact_mod_cast Nat.factorial_le (by omega))
  refine h1.trans ((norm_pochCoeff_le_of_norm_le (R := ‖z‖ + 1)
    ((norm_add_le _ _).trans (by simp)) (2 * i)).trans ?_)
  rw [pow_mul]
  norm_num

theorem differentiable_oddCoeff (i : ℕ) : Differentiable ℂ (fun z => oddCoeff z i) := by
  have h : Differentiable ℂ (fun z : ℂ => (ascPochhammer ℂ (2 * i)).eval (z + 1)) :=
    (Polynomial.differentiable _).comp (differentiable_id.add_const (1 : ℂ))
  exact h.div_const _

theorem norm_oddCoeff_mul_pow_le (z : ℂ) {y : ℂ} (hy : ‖y‖ ≤ 1 / 9) (i : ℕ) :
    ‖oddCoeff z i * y ^ i‖ ≤ 2 ^ (‖z‖ + 1) * (4 / 9) ^ i := by
  rw [norm_mul, norm_pow]
  calc ‖oddCoeff z i‖ * ‖y‖ ^ i ≤ (2 ^ (‖z‖ + 1) * 4 ^ i) * (1 / 9) ^ i :=
        mul_le_mul (norm_oddCoeff_le z i) (pow_le_pow_left₀ (norm_nonneg _) hy i)
          (by positivity) (by positivity)
    _ = 2 ^ (‖z‖ + 1) * (4 / 9) ^ i := by
        rw [mul_assoc, ← mul_pow]
        norm_num

theorem summable_norm_oddCoeff_mul_pow (z : ℂ) {y : ℂ} (hy : ‖y‖ ≤ 1 / 9) :
    Summable (fun i => ‖oddCoeff z i * y ^ i‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_oddCoeff_mul_pow_le z hy)
    ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)

/-- The odd part of the binomial series:
`(1 - x)^{-z} - (1 + x)^{-z} = 2 z x ∑_i (z+1)_{2i}/(2i+1)! x^{2i}`. -/
theorem one_sub_cpow_neg_sub_one_add_cpow_neg (z : ℂ) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (1 - (x : ℂ)) ^ (-z) - (1 + (x : ℂ)) ^ (-z) =
      2 * z * x * ∑' i : ℕ, oddCoeff z i * ((x : ℂ) ^ 2) ^ i := by
  have hxn : ‖(x : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
  have h1 := hasSum_pochCoeff_mul_pow z hxn
  have h2 := hasSum_pochCoeff_mul_pow z (y := -(x : ℂ)) (by rwa [norm_neg])
  rw [sub_neg_eq_add] at h2
  have h := h1.sub h2
  have hinj : Function.Injective (fun i : ℕ => 2 * i + 1) := fun a b hab => by
    simp only at hab
    omega
  have hzero : ∀ k ∉ Set.range (fun i : ℕ => 2 * i + 1),
      pochCoeff z k * (x : ℂ) ^ k - pochCoeff z k * (-(x : ℂ)) ^ k = 0 := by
    intro k hk
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show j + j = 2 * j by ring, pow_mul, pow_mul, neg_sq, sub_self]
    · exact absurd ⟨j, rfl⟩ hk
  have hodd := (hinj.hasSum_iff hzero).2 h
  have hodd' : HasSum (fun i : ℕ => 2 * z * x * (oddCoeff z i * ((x : ℂ) ^ 2) ^ i))
      ((1 - (x : ℂ)) ^ (-z) - (1 + (x : ℂ)) ^ (-z)) := by
    convert hodd using 1
    funext i
    simp only [Function.comp_apply]
    rw [pochCoeff_two_mul_add_one, Odd.neg_pow ⟨i, rfl⟩]
    ring
  rw [← hodd'.tsum_eq, tsum_mul_left]

/-- The coefficient of `y^l` in `T(z, y)²`. -/
def oddSq (z : ℂ) (l : ℕ) : ℂ := ∑ p ∈ antidiagonal l, oddCoeff z p.1 * oddCoeff z p.2

theorem oddSeries_sq (z : ℂ) {y : ℂ} (hy : ‖y‖ ≤ 1 / 9) :
    (∑' i : ℕ, oddCoeff z i * y ^ i) ^ 2 = ∑' l : ℕ, oddSq z l * y ^ l := by
  rw [sq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_oddCoeff_mul_pow z hy) (summable_norm_oddCoeff_mul_pow z hy)]
  congr 1
  funext l
  rw [oddSq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

theorem norm_oddSq_le (z : ℂ) (l : ℕ) :
    ‖oddSq z l‖ ≤ (l + 1) * ((2 ^ (‖z‖ + 1)) ^ 2 * 4 ^ l) := by
  rw [oddSq]
  calc ‖∑ p ∈ antidiagonal l, oddCoeff z p.1 * oddCoeff z p.2‖
      ≤ ∑ p ∈ antidiagonal l, ‖oddCoeff z p.1 * oddCoeff z p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ antidiagonal l, (2 ^ (‖z‖ + 1)) ^ 2 * 4 ^ l := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [mem_antidiagonal] at hp
        rw [norm_mul, ← hp, pow_add]
        calc ‖oddCoeff z p.1‖ * ‖oddCoeff z p.2‖
            ≤ (2 ^ (‖z‖ + 1) * 4 ^ p.1) * (2 ^ (‖z‖ + 1) * 4 ^ p.2) :=
              mul_le_mul (norm_oddCoeff_le z _) (norm_oddCoeff_le z _) (norm_nonneg _)
                (by positivity)
          _ = (2 ^ (‖z‖ + 1)) ^ 2 * (4 ^ p.1 * 4 ^ p.2) := by ring
    _ = (l + 1) * ((2 ^ (‖z‖ + 1)) ^ 2 * 4 ^ l) := by
        rw [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
        push_cast
        ring

/-- The coefficients of the remainder series, `oddSq z l / 4^{l+1}`. -/
def remCoeff (l : ℕ) (z : ℂ) : ℂ := oddSq z l / 4 ^ (l + 1)

theorem norm_remCoeff_le {z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (l : ℕ) :
    ‖remCoeff l z‖ ≤ (2 ^ (R + 1)) ^ 2 * 2 ^ l := by
  rw [remCoeff, norm_div, norm_pow, Complex.norm_ofNat]
  have hl : ((l : ℝ) + 1) ≤ 2 ^ l := by
    have := Nat.lt_two_pow_self (n := l)
    exact_mod_cast this
  have hR : (2 : ℝ) ^ (‖z‖ + 1) ≤ 2 ^ (R + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc ‖oddSq z l‖ / 4 ^ (l + 1) ≤ (l + 1) * ((2 ^ (‖z‖ + 1)) ^ 2 * 4 ^ l) / 4 ^ (l + 1) :=
        div_le_div_of_nonneg_right (norm_oddSq_le z l) (by positivity)
    _ = (l + 1) * (2 ^ (‖z‖ + 1)) ^ 2 / 4 := by
        rw [show (4 : ℝ) ^ (l + 1) = 4 ^ l * 4 from pow_succ 4 l]
        field_simp
    _ ≤ 2 ^ l * (2 ^ (R + 1)) ^ 2 / 1 := by
        gcongr
        norm_num
    _ = (2 ^ (R + 1)) ^ 2 * 2 ^ l := by ring

theorem geomBounded_remCoeff : GeomBounded remCoeff :=
  fun R => ⟨(2 ^ (R + 1)) ^ 2, fun l _ hz => norm_remCoeff_le hz l⟩

theorem differentiable_remCoeff (l : ℕ) : Differentiable ℂ (remCoeff l) := by
  show Differentiable ℂ (fun z => oddSq z l / 4 ^ (l + 1))
  refine Differentiable.div_const ?_ _
  show Differentiable ℂ (fun z => ∑ p ∈ antidiagonal l, oddCoeff z p.1 * oddCoeff z p.2)
  exact Differentiable.fun_sum fun p _ =>
    (differentiable_oddCoeff p.1).mul (differentiable_oddCoeff p.2)

/-- The remainder series `∑_j C(N,j) (-1/4)^j ∑_l remCoeff l z ζ(2z + 2 - 2N + 2j + 2l, 3/2)`. -/
def remSeries (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range (N + 1), (N.choose j : ℂ) * (-1 / 4) ^ j *
    hzSeries remCoeff (2 - 2 * N + 2 * j) z

theorem differentiableAt_remSeries (N : ℕ) {z : ℂ} (hz : ∀ n : ℤ, 2 * z + 2 * n ≠ 1) :
    DifferentiableAt ℂ (remSeries N) z := by
  show DifferentiableAt ℂ (fun z => ∑ j ∈ range (N + 1), (N.choose j : ℂ) * (-1 / 4) ^ j *
    hzSeries remCoeff (2 - 2 * N + 2 * j) z) z
  refine DifferentiableAt.fun_sum fun j _ => (differentiableAt_const _).mul ?_
  refine differentiableAt_hzSeries differentiable_remCoeff geomBounded_remCoeff _ fun k hk => ?_
  refine hz (1 - N + j + k) ?_
  rw [← hk]
  push_cast
  ring

/-- `u^{-(w + 2 - 2N + 2j + 2l)} = u^{-w} u^{2(N-j)} / u^{2l+2}` for `u > 0`, `j ≤ N`. -/
theorem ofReal_cpow_neg_add_shift {u : ℝ} (hu : 0 < u) (w : ℂ) {N j : ℕ} (hj : j ≤ N)
    (l : ℕ) :
    (u : ℂ) ^ (-(w + (2 - 2 * N + 2 * j) + 2 * l)) =
      (u : ℂ) ^ (-w) * (u : ℂ) ^ (2 * (N - j)) / (u : ℂ) ^ (2 * l + 2) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  have e : -(w + (2 - 2 * N + 2 * j) + 2 * l) =
      -w + ((2 * (N - j) : ℕ) : ℂ) - ((2 * l + 2 : ℕ) : ℂ) := by
    push_cast [Nat.cast_sub hj]
    ring
  rw [e, cpow_sub _ _ hu0, cpow_add _ _ hu0, cpow_natCast, cpow_natCast]

/-- `((m+1)(m+2))^N = ∑_j C(N,j) (-1/4)^j u^{2(N-j)}` with `u = m + 3/2`. -/
theorem natCast_mul_pow_eq_sum (N m : ℕ) {u : ℝ} (hu : u = m + 3 / 2) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N =
      ∑ j ∈ range (N + 1), (N.choose j : ℂ) * (-1 / 4) ^ j * (u : ℂ) ^ (2 * (N - j)) := by
  have h : ((((m + 1) * (m + 2) : ℕ) : ℂ)) = (-1 / 4) + (u : ℂ) ^ 2 := by
    rw [hu]
    push_cast
    ring
  rw [h, add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_mul]
  ring

/-- The difference `(m+1)^{-z} - (m+2)^{-z} = u^{-z} 2 z x T(z, x²)`, `u = m + 3/2`,
`x = 1/(2u)`. -/
theorem natCast_cpow_neg_sub (z : ℂ) (m : ℕ) {u : ℝ} (hu : u = m + 3 / 2) :
    (((m + 1 : ℕ) : ℂ)) ^ (-z) - (((m + 2 : ℕ) : ℂ)) ^ (-z) =
      (u : ℂ) ^ (-z) * (2 * z * ((1 / (2 * u) : ℝ) : ℂ) *
        ∑' i : ℕ, oddCoeff z i * ((((1 / (2 * u) : ℝ) : ℂ)) ^ 2) ^ i) := by
  have hu0 : 0 < u := by rw [hu]; positivity
  have hu32 : (3 / 2 : ℝ) ≤ u := by rw [hu]; linarith [m.cast_nonneg (α := ℝ)]
  have hx0 : 0 ≤ 1 / (2 * u) := by positivity
  have hx1 : 1 / (2 * u) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have h1 : (((m + 1 : ℕ) : ℂ)) = (u : ℂ) * ((1 - 1 / (2 * u) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, show u * (1 - 1 / (2 * u)) = u - 1 / 2 by field_simp, hu]
    push_cast
    ring
  have h2 : (((m + 2 : ℕ) : ℂ)) = (u : ℂ) * ((1 + 1 / (2 * u) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, show u * (1 + 1 / (2 * u)) = u + 1 / 2 by field_simp, hu]
    push_cast
    ring
  rw [h1, h2, mul_cpow_ofReal_nonneg hu0.le (by linarith),
    mul_cpow_ofReal_nonneg hu0.le (by linarith), ← mul_sub,
    ← one_sub_cpow_neg_sub_one_add_cpow_neg z hx0 hx1]
  push_cast
  ring

/-- Per-term expansion of the quadratic remainder `P (α - β)² / 2`. -/
theorem remainder_term_eq (N : ℕ) (z : ℂ) (m : ℕ) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
        ((((m + 1 : ℕ) : ℂ)) ^ (-z) - (((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2 / 2 =
      2 * z ^ 2 * ∑ j ∈ range (N + 1), (N.choose j : ℂ) * (-1 / 4) ^ j *
        ∑' l : ℕ, remCoeff l z * ((m : ℂ) + 3 / 2) ^ (-(2 * z + (2 - 2 * N + 2 * j) + 2 * l)) := by
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = m + 3 / 2 := ⟨_, rfl⟩
  have hu : 0 < u := by rw [hu_def]; positivity
  have hu32 : (3 / 2 : ℝ) ≤ u := by rw [hu_def]; linarith [m.cast_nonneg (α := ℝ)]
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
  have hmu : ((m : ℂ) + 3 / 2) = (u : ℂ) := by rw [hu_def]; push_cast; ring
  set x : ℂ := ((1 / (2 * u) : ℝ) : ℂ) with hx_def
  set T : ℂ := ∑' i : ℕ, oddCoeff z i * (x ^ 2) ^ i with hT_def
  have hy : ‖x ^ 2‖ ≤ 1 / 9 := by
    rw [hx_def, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hT2 := oddSeries_sq z hy
  have hx2 : x ^ 2 = 1 / (4 * (u : ℂ) ^ 2) := by
    rw [hx_def]
    push_cast
    field_simp
    ring
  have hterm : ∀ j ∈ range (N + 1), ∑' l : ℕ, remCoeff l z *
      ((m : ℂ) + 3 / 2) ^ (-(2 * z + (2 - 2 * N + 2 * j) + 2 * l)) =
      ((u : ℂ) ^ (-z) * (u : ℂ) ^ (-z) * (u : ℂ) ^ (2 * (N - j)) * x ^ 2) * T ^ 2 := by
    intro j hj
    have hjN : j ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hj)
    rw [hT_def, hT2, ← tsum_mul_left]
    congr 1
    funext l
    rw [hmu, ofReal_cpow_neg_add_shift hu (2 * z) hjN l, ofReal_cpow_neg_two_mul hu z, remCoeff,
      hx2, div_pow, one_pow, mul_pow]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun j hj => by rw [hterm j hj], natCast_cpow_neg_sub z m hu_def,
    natCast_mul_pow_eq_sum N m hu_def, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hx_def, ← hT_def]
  ring

/-- Summing the remainder: `∑_m P (α - β)²/2 = 2 z² remSeries N z` for `re z > N + 1/2`. -/
theorem hasSum_remainder (N : ℕ) {z : ℂ} (hz : (N : ℝ) + 1 / 2 < z.re) :
    HasSum (fun m : ℕ => ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
        ((((m + 1 : ℕ) : ℂ)) ^ (-z) - (((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2 / 2)
      (2 * z ^ 2 * remSeries N z) := by
  simp_rw [remainder_term_eq N z]
  refine HasSum.mul_left _ ?_
  refine hasSum_sum fun j _ => HasSum.mul_left _ ?_
  refine hasSum_hzSeries (C := (2 ^ (‖z‖ + 1)) ^ 2) ?_ (fun k => norm_remCoeff_le le_rfl k)
  simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, sub_re, natCast_re,
    natCast_im, mul_zero]
  linarith [j.cast_nonneg (α := ℝ)]

end BrownianAffine.SpectralZeta
