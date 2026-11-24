import PLAStochastic.ForMathlib.NumberTheory.LSeries.SpectralZeta.SymmetricPart
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.PathConnected

/-! # The spectral zeta function at non-positive integers (T6)

For every `N : ℕ`,

`D(-N) = -1_{N = 0}`,   `D'(-N) = 2 ∑_{r ≤ N/2} C(N, 2r) ζ'(-2N + 2r)`.

**Proof.** For `re z > N + 1/2`, termwise
`((m+1)(m+2))^{-(z-N)} = P α β = P (α² + β²)/2 - P (α - β)²/2`, so

`D(z - N) = symZeta N z - 2 z² remSeries N z`

(`hasSum_symmetric`, `hasSum_remainder`). All three functions are holomorphic on the
star-shaped open set `offHalfLine = {im z ≠ 0} ∪ {|re z| < 1/2}`, which meets the half-plane
`re z > N + 1/2`; the identity theorem extends the equality to `offHalfLine ∋ 0`. The remainder
term `2 z² remSeries N z` vanishes to second order at `0`, so `D(-N)` and `D'(-N)` are the value
and derivative of `symZeta N` at `0`. These follow from `ζ(0) = -1/2`, the trivial zeros
`ζ(-2k) = 0`, and the parity identity `∑_{i ≤ N} (1 + (-1)^i) g(i) = 2 ∑_{r ≤ N/2} g(2r)`.
-/

noncomputable section

open Complex Filter Topology Finset

namespace BrownianAffine.SpectralZeta

/-- The open star-shaped set `{im z ≠ 0} ∪ {|re z| < 1/2}`; it avoids every real `c` with
`|c| ≥ 1/2`. -/
def offHalfLine : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1 / 2}

theorem isOpen_offHalfLine : IsOpen offHalfLine :=
  (isOpen_ne_fun continuous_im continuous_const).union
    (isOpen_lt (continuous_abs.comp continuous_re) continuous_const)

theorem zero_mem_offHalfLine : (0 : ℂ) ∈ offHalfLine := Or.inr (by norm_num)

theorem starConvex_offHalfLine : StarConvex ℝ 0 offHalfLine := by
  intro y hy a b _ hb hab
  rw [smul_zero, zero_add]
  rcases eq_or_lt_of_le hb with rfl | hbpos
  · rw [zero_smul]
    exact zero_mem_offHalfLine
  · have hb1 : b ≤ 1 := by linarith
    rcases hy with h | h
    · left
      rw [Complex.smul_im, smul_eq_mul]
      exact mul_ne_zero hbpos.ne' h
    · right
      rw [Complex.smul_re, smul_eq_mul, abs_mul, abs_of_pos hbpos]
      calc b * |y.re| ≤ 1 * |y.re| := mul_le_mul_of_nonneg_right hb1 (abs_nonneg _)
        _ < 1 / 2 := by linarith

theorem isPreconnected_offHalfLine : IsPreconnected offHalfLine :=
  (starConvex_offHalfLine.isPathConnected zero_mem_offHalfLine).isConnected.isPreconnected

theorem ne_ofReal_of_mem_offHalfLine {z : ℂ} (hz : z ∈ offHalfLine) {c : ℝ}
    (hc : 1 / 2 ≤ |c|) : z ≠ c := by
  rintro rfl
  rcases hz with h | h
  · exact h (ofReal_im c)
  · rw [ofReal_re] at h
    linarith

theorem two_mul_add_intCast_ne_one {z : ℂ} (hz : z ∈ offHalfLine) (n : ℤ) :
    2 * z + 2 * n ≠ 1 := by
  intro h
  have hzc : z = ((((1 - 2 * n : ℤ) : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination h / 2
  refine ne_ofReal_of_mem_offHalfLine hz ?_ hzc
  have h1 : (1 - 2 * n : ℤ) ≠ 0 := by omega
  have h2 : (1 : ℝ) ≤ |(((1 - 2 * n : ℤ)) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h1
  rw [abs_div, abs_two]
  linarith

theorem sym_arg_ne_one {z : ℂ} (hz : z ∈ offHalfLine) (N : ℕ) :
    ∀ i ∈ range (N + 1), 2 * z - 2 * N + i ≠ 1 := by
  intro i hi h
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hzc : z = (((1 + 2 * N - i) / 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination h / 2
  refine ne_ofReal_of_mem_offHalfLine hz ?_ hzc
  have hN : (0 : ℝ) ≤ N := N.cast_nonneg
  rw [abs_of_nonneg (by linarith)]
  linarith

/-- Termwise splitting `P α β = P (α² + β²)/2 - P (α - β)²/2`. -/
theorem natCast_mul_cpow_neg_sub_nat (N : ℕ) (z : ℂ) (m : ℕ) :
    ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ (-(z - N)) =
      ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
          (((((m + 1 : ℕ) : ℂ)) ^ (-z)) ^ 2 + ((((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2) / 2 -
        ((((m + 1) * (m + 2) : ℕ) : ℂ)) ^ N *
          ((((m + 1 : ℕ) : ℂ)) ^ (-z) - (((m + 2 : ℕ) : ℂ)) ^ (-z)) ^ 2 / 2 := by
  have hQ : ((((m + 1) * (m + 2) : ℕ) : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero m) (Nat.succ_ne_zero (m + 1))
  rw [show -(z - N) = (N : ℂ) + -z by ring, cpow_add _ _ hQ, cpow_natCast, Nat.cast_mul,
    natCast_mul_natCast_cpow]
  ring

/-- The splitting identity `D(z - N) = symZeta N z - 2 z² remSeries N z`, valid on
`offHalfLine` by analytic continuation from `re z > N + 1/2`. -/
theorem spectralZeta_sub_nat_eq (N : ℕ) {z : ℂ} (hz : z ∈ offHalfLine) :
    spectralZeta (z - N) = symZeta N z - 2 * z ^ 2 * remSeries N z := by
  set F : ℂ → ℂ := fun w => spectralZeta (w - N) - (symZeta N w - 2 * w ^ 2 * remSeries N w)
    with hF_def
  have hFd : DifferentiableOn ℂ F offHalfLine := by
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun w : ℂ => spectralZeta (w - N)) w := by
      refine (differentiableAt_spectralZeta fun r hr =>
        two_mul_add_intCast_ne_one hw ((r : ℤ) - N) ?_).comp (f := fun w : ℂ => w - N) w
          (by fun_prop)
      push_cast
      linear_combination 2 * hr
    have h2 := differentiableAt_symZeta N (sym_arg_ne_one hw N)
    have h3 := differentiableAt_remSeries N (two_mul_add_intCast_ne_one hw)
    exact h1.sub (h2.sub ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => 2 * w ^ 2) w).mul h3))
  have hz₀ : ((N : ℂ) + 1 + I) ∈ offHalfLine := Or.inl (by simp)
  have hev : F =ᶠ[𝓝 ((N : ℂ) + 1 + I)] fun _ => 0 := by
    have hopen : IsOpen {w : ℂ | (N : ℝ) + 1 / 2 < w.re} :=
      isOpen_lt continuous_const continuous_re
    have hmem : ((N : ℂ) + 1 + I) ∈ {w : ℂ | (N : ℝ) + 1 / 2 < w.re} := by
      show (N : ℝ) + 1 / 2 < ((N : ℂ) + 1 + I).re
      simp only [add_re, natCast_re, one_re, I_re, add_zero]
      linarith
    filter_upwards [hopen.mem_nhds hmem] with w hw
    have hw' : (N : ℝ) + 1 / 2 < w.re := hw
    have h1 := hasSum_spectralZeta (s := w - N) (by
      simp only [sub_re, natCast_re]
      linarith)
    simp_rw [natCast_mul_cpow_neg_sub_nat N w] at h1
    have h2 := (hasSum_symmetric N hw').sub (hasSum_remainder N hw')
    have := h1.unique h2
    simp only [hF_def]
    rw [this]
    ring
  have hEq := (hFd.analyticOnNhd isOpen_offHalfLine).eqOn_of_preconnected_of_eventuallyEq
    analyticOnNhd_const isPreconnected_offHalfLine hz₀ hev
  have := hEq hz
  simp only [hF_def] at this
  linear_combination this

theorem spectralZeta_sub_nat_eventuallyEq (N : ℕ) :
    (fun z : ℂ => spectralZeta (z - N)) =ᶠ[𝓝 0]
      fun z => symZeta N z - 2 * z ^ 2 * remSeries N z := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  refine spectralZeta_sub_nat_eq N (Or.inr ?_)
  rw [mem_ball_zero_iff] at hz
  exact lt_of_le_of_lt (abs_re_le_norm z) hz

theorem spectralZeta_neg_nat_eq_symZeta (N : ℕ) : spectralZeta (-N) = symZeta N 0 := by
  have := spectralZeta_sub_nat_eq N zero_mem_offHalfLine
  rw [zero_sub] at this
  rw [this]
  ring

theorem symZeta_zero (N : ℕ) : symZeta N 0 = if N = 0 then -1 else 0 := by
  unfold symZeta
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [riemannZeta_zero]
    norm_num
  · rw [if_neg hN.ne']
    have halt : ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (-1) ^ i = 0 := by
      have h := add_pow (-1 : ℂ) 1 N
      rw [neg_add_cancel, zero_pow hN.ne'] at h
      rw [h]
      exact Finset.sum_congr rfl fun i _ => by rw [one_pow]; ring
    have hterm : ∀ i ∈ range (N + 1),
        (N.choose i : ℂ) * (1 + (-1) ^ i) * riemannZeta (2 * 0 - 2 * N + i) = 0 := by
      intro i hi
      have hiN : i ≤ N := Nat.lt_succ_iff.1 (mem_range.1 hi)
      rcases Nat.even_or_odd i with ⟨t, rfl⟩ | ⟨t, rfl⟩
      · have e : (N : ℂ) = t + ((N - t - 1 : ℕ) : ℂ) + 1 := by
          have : t + (N - t - 1) + 1 = N := by omega
          exact_mod_cast this.symm
        have hz : (2 * (0 : ℂ) - 2 * N + ((t + t : ℕ) : ℂ)) =
            -2 * (((N - t - 1 : ℕ) : ℂ) + 1) := by
          push_cast
          linear_combination (-2 : ℂ) * e
        rw [hz, riemannZeta_neg_two_mul_nat_add_one, mul_zero]
      · rw [Odd.neg_one_pow ⟨t, rfl⟩]
        ring
    rw [Finset.sum_eq_zero hterm, halt]
    simp

/-- The parity identity `∑_{i ≤ N} (1 + (-1)^i) g(i) = 2 ∑_{r ≤ N/2} g(2r)`. -/
theorem sum_range_one_add_neg_one_pow_mul (g : ℕ → ℂ) : ∀ N : ℕ,
    ∑ i ∈ range (N + 1), (1 + (-1) ^ i) * g i = 2 * ∑ r ∈ range (N / 2 + 1), g (2 * r)
  | 0 => by
    rw [Finset.sum_range_one, Nat.zero_div, Finset.sum_range_one, pow_zero, mul_zero]
    ring
  | 1 => by
    rw [Finset.sum_range_succ, Finset.sum_range_one, show 1 / 2 = 0 from rfl,
      Finset.sum_range_one, pow_zero, pow_one, mul_zero]
    ring
  | N + 2 => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, sum_range_one_add_neg_one_pow_mul g N,
      show (N + 2) / 2 + 1 = (N / 2 + 1) + 1 by omega,
      Finset.sum_range_succ (fun r => g (2 * r)) (N / 2 + 1)]
    rcases Nat.even_or_odd N with ⟨k, hk⟩ | ⟨k, hk⟩
    · have h1 : (-1 : ℂ) ^ (N + 1) = -1 := Odd.neg_one_pow ⟨k, by omega⟩
      have h2 : (-1 : ℂ) ^ (N + 2) = 1 := Even.neg_one_pow ⟨k + 1, by omega⟩
      have h3 : 2 * (N / 2 + 1) = N + 2 := by omega
      rw [h1, h2, h3]
      ring
    · have h1 : (-1 : ℂ) ^ (N + 1) = 1 := Even.neg_one_pow ⟨k + 1, by omega⟩
      have h2 : (-1 : ℂ) ^ (N + 2) = -1 := Odd.neg_one_pow ⟨k + 1, by omega⟩
      have h3 : 2 * (N / 2 + 1) = N + 1 := by omega
      rw [h1, h2, h3]
      ring

theorem deriv_spectralZeta_neg_nat_eq_sum (N : ℕ) :
    deriv spectralZeta (-N) = ∑ i ∈ range (N + 1),
      (N.choose i : ℂ) * (1 + (-1) ^ i) * deriv riemannZeta (-2 * N + i) := by
  have h1 : deriv spectralZeta (-N) = deriv (fun z : ℂ => spectralZeta (z - N)) 0 := by
    rw [deriv_comp_sub_const, zero_sub]
  have hrem : HasDerivAt (fun z : ℂ => 2 * z ^ 2 * remSeries N z) 0 0 := by
    have hd := (differentiableAt_remSeries N
      (two_mul_add_intCast_ne_one zero_mem_offHalfLine)).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => 2 * z ^ 2) 0 0 := by
      simpa using (hasDerivAt_pow 2 (0 : ℂ)).const_mul (2 : ℂ)
    exact (hp.mul hd).congr_deriv (by simp)
  have hsum : HasDerivAt (fun z => symZeta N z - 2 * z ^ 2 * remSeries N z)
      ((∑ i ∈ range (N + 1), (N.choose i : ℂ) * (1 + (-1) ^ i) *
        deriv riemannZeta (-2 * N + i)) - 0) 0 :=
    (hasDerivAt_symZeta_zero N).sub hrem
  rw [h1, (spectralZeta_sub_nat_eventuallyEq N).deriv_eq, hsum.deriv, sub_zero]

end BrownianAffine.SpectralZeta

namespace BrownianAffine

open SpectralZeta

/-- **Values (T6).** `D(-N) = -1` if `N = 0` and `0` otherwise. -/
theorem spectralZeta_neg_nat (N : ℕ) : spectralZeta (-N) = if N = 0 then -1 else 0 := by
  rw [spectralZeta_neg_nat_eq_symZeta, symZeta_zero]

/-- **Derivatives (T6).** `D'(-N) = 2 ∑_{r ≤ N/2} C(N, 2r) ζ'(-2N + 2r)`. -/
theorem deriv_spectralZeta_neg_nat (N : ℕ) :
    deriv spectralZeta (-N) = 2 * ∑ r ∈ Finset.range (N / 2 + 1),
      (N.choose (2 * r) : ℂ) * deriv riemannZeta (-2 * N + 2 * r) := by
  rw [deriv_spectralZeta_neg_nat_eq_sum]
  calc ∑ i ∈ range (N + 1), (N.choose i : ℂ) * (1 + (-1) ^ i) * deriv riemannZeta (-2 * N + i)
      = ∑ i ∈ range (N + 1), (1 + (-1) ^ i) *
          ((N.choose i : ℂ) * deriv riemannZeta (-2 * N + i)) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = 2 * ∑ r ∈ range (N / 2 + 1), (N.choose (2 * r) : ℂ) *
          deriv riemannZeta (-2 * N + ((2 * r : ℕ) : ℂ)) :=
        sum_range_one_add_neg_one_pow_mul
          (fun i => (N.choose i : ℂ) * deriv riemannZeta (-2 * N + i)) N
    _ = 2 * ∑ r ∈ Finset.range (N / 2 + 1),
          (N.choose (2 * r) : ℂ) * deriv riemannZeta (-2 * N + 2 * r) := by
        push_cast
        rfl

end BrownianAffine
