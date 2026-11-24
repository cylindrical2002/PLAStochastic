import PLAStochastic.ForMathlib.NumberTheory.Harmonic.IcoLogBounds

/-! # Summing a scaled tail over a range

If `(n/E) * p n` is within `ε` of a constant `V` throughout a range of indices,
then the sum of `p` over that range is `V * E` times the logarithm of the index
ratio, with an error that is `E` times an absolute constant plus `E * ε` times
the logarithm. This is the arithmetic core of the interior summation. -/
noncomputable section
open Finset
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

theorem sum_of_scaled_range {E V ε : ℝ} (hE : 0 < E) (hε : 0 ≤ ε) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {p : ℕ → ℝ}
    (hp : ∀ n ∈ Finset.Ico a b, |(n : ℝ)/E*p n-V| ≤ ε) :
    |(∑ n ∈ Finset.Ico a b, p n)-V*E*(Real.log b-Real.log a)| ≤
      E*(ε*(|Real.log b-Real.log a|+1)+|V|) := by
  have hsum : ∑ n ∈ Finset.Ico a b, p n =
      E*∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n)*(n : ℝ)⁻¹ := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := le_trans ha (Finset.mem_Ico.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    field_simp
  set H : ℝ := ∑ n ∈ Finset.Ico a b, (n : ℝ)⁻¹ with hHdef
  have hHlog := abs_sum_inv_Ico_sub_log_le_one a b ha hab
  have hHnn : 0 ≤ H := Finset.sum_nonneg fun n _ => by positivity
  have hHub : H ≤ |Real.log b-Real.log a|+1 := by
    have := abs_le.mp hHlog
    have habs := le_abs_self (Real.log b-Real.log a)
    linarith [this.2]
  -- compare the weighted sum with V * H
  have hcmp : |(∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n)*(n : ℝ)⁻¹)-V*H| ≤ ε*H := by
    have he : (∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n)*(n : ℝ)⁻¹)-V*H =
        ∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n-V)*(n : ℝ)⁻¹ := by
      rw [hHdef, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [he]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hHdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : 1 ≤ n := le_trans ha (Finset.mem_Ico.mp hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)⁻¹)]
    exact mul_le_mul_of_nonneg_right (hp n hn) (by positivity)
  -- assemble
  have hVH : |V*H-V*(Real.log b-Real.log a)| ≤ |V| := by
    rw [← mul_sub, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg V) hHlog
  have hkey : |(∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n)*(n : ℝ)⁻¹)-
      V*(Real.log b-Real.log a)| ≤ ε*H+|V| := by
    calc _ ≤ |(∑ n ∈ Finset.Ico a b, ((n : ℝ)/E*p n)*(n : ℝ)⁻¹)-V*H|+
            |V*H-V*(Real.log b-Real.log a)| := abs_sub_le _ _ _
      _ ≤ ε*H+|V| := add_le_add hcmp hVH
  rw [hsum, show V*E*(Real.log b-Real.log a) =
      E*(V*(Real.log b-Real.log a)) by ring, ← mul_sub, abs_mul,
    abs_of_nonneg hE.le]
  refine mul_le_mul_of_nonneg_left (hkey.trans ?_) hE.le
  have : ε*H ≤ ε*(|Real.log b-Real.log a|+1) := mul_le_mul_of_nonneg_left hHub hε
  linarith

/-- A range sum dominated by `M * E / n` is at most `M * E` times the logarithm
of the index ratio, up to an absolute constant. -/
theorem sum_of_dominated_range {E M : ℝ} (hE : 0 < E) (hM : 0 ≤ M) {a b : ℕ}
    (ha : 1 ≤ a) (hab : a ≤ b) {p : ℕ → ℝ}
    (hp : ∀ n ∈ Finset.Ico a b, p n ≤ M*E*(n : ℝ)⁻¹) :
    (∑ n ∈ Finset.Ico a b, p n) ≤ M*E*(|Real.log b-Real.log a|+1) := by
  have hHlog := abs_sum_inv_Ico_sub_log_le_one a b ha hab
  have hHub : (∑ n ∈ Finset.Ico a b, (n : ℝ)⁻¹) ≤ |Real.log b-Real.log a|+1 := by
    have h := (abs_le.mp hHlog).2
    have habs := le_abs_self (Real.log b-Real.log a)
    linarith
  calc (∑ n ∈ Finset.Ico a b, p n)
      ≤ ∑ n ∈ Finset.Ico a b, M*E*(n : ℝ)⁻¹ := Finset.sum_le_sum hp
    _ = M*E*∑ n ∈ Finset.Ico a b, (n : ℝ)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ M*E*(|Real.log b-Real.log a|+1) :=
        mul_le_mul_of_nonneg_left hHub (by positivity)

end SwingRepair
