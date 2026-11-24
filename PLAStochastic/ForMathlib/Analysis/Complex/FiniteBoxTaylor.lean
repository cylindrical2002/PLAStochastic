import PLAStochastic.ForMathlib.Analysis.Complex.FiniteBasisTaylor
import Mathlib.Analysis.Analytic.Basic

/-! # Total-degree and rectangular truncations of genuine finite-coordinate Taylor series -/

noncomputable section
open Complex Finset Filter Topology Asymptotics
namespace PGM

theorem mem_finiteCoordinateTaylorBox {d N : ℕ} {α : Fin d → ℕ} :
    α ∈ finiteCoordinateTaylorBox d N ↔ ∀ i, α i ≤ N := by
  simp [finiteCoordinateTaylorBox, Fintype.mem_piFinset]

theorem finiteCoordinateTaylorBox_mono {d n N : ℕ} (hn : n ≤ N) :
    finiteCoordinateTaylorBox d n ⊆ finiteCoordinateTaylorBox d N := by
  intro α hα
  exact mem_finiteCoordinateTaylorBox.mpr fun i =>
    (mem_finiteCoordinateTaylorBox.mp hα i).trans hn

/-- The homogeneous coordinate expansion can use any larger rectangular support. -/
theorem multilinear_diagonal_eq_coordinate_box_of_le {d : ℕ}
    (p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ) (n N : ℕ) (hn : n ≤ N) (x : Fin d → ℂ) :
    p n (fun _ => x) = ∑ α ∈ finiteCoordinateTaylorBox d N,
      if (∑ i, α i) = n then finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i) else 0 := by
  rw [multilinear_diagonal_eq_coordinate_box]
  apply sum_subset (finiteCoordinateTaylorBox_mono hn)
  intro α _ hnot
  have hne : (∑ i, α i) ≠ n := by
    intro he
    apply hnot
    apply mem_finiteCoordinateTaylorBox.mpr
    intro i
    have hi : α i ≤ ∑ j, α j := single_le_sum (fun j _ => Nat.zero_le (α j)) (mem_univ i)
    exact he ▸ hi
  simp only [if_neg hne]

/-- The total-degree Taylor polynomial is the rectangular polynomial restricted to
monomials of total degree at most the requested order. -/
theorem partialSum_eq_coordinate_box_total_degree {d : ℕ}
    (p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ) (N : ℕ) (x : Fin d → ℂ) :
    p.partialSum (N + 1) x = ∑ α ∈ finiteCoordinateTaylorBox d N,
      if (∑ i, α i) ≤ N then finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i) else 0 := by
  unfold FormalMultilinearSeries.partialSum
  calc
    ∑ n ∈ range (N + 1), p n (fun _ => x) =
        ∑ n ∈ range (N + 1), ∑ α ∈ finiteCoordinateTaylorBox d N,
          if (∑ i, α i) = n then finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i) else 0 := by
      apply sum_congr rfl
      intro n hn
      exact multilinear_diagonal_eq_coordinate_box_of_le p n N
        (by have := mem_range.mp hn; omega) x
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro α _
      simp [mem_range]

/-- Monomials above total degree `N` are bounded by the `(N+1)`st power of the coordinate norm
sum, on its unit ball. -/
theorem norm_coordinate_monomial_le_of_degree_gt {d N : ℕ} {x : Fin d → ℂ}
    (hx : (∑ i, ‖x i‖) ≤ 1) {α : Fin d → ℕ} (hα : N < ∑ i, α i) :
    ‖∏ i, x i ^ α i‖ ≤ (∑ i, ‖x i‖) ^ (N + 1) := by
  have hs : 0 ≤ ∑ i, ‖x i‖ := sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ = ∏ i, ‖x i‖ ^ α i := by simp only [norm_prod, norm_pow]
    _ ≤ ∏ i : Fin d, (∑ j, ‖x j‖) ^ α i := by
      apply prod_le_prod (fun _ _ => by positivity)
      intro i _
      exact pow_le_pow_left₀ (norm_nonneg _) (single_le_sum
        (fun j _ => norm_nonneg (x j)) (mem_univ i)) _
    _ = (∑ i, ‖x i‖) ^ (∑ i, α i) := prod_pow_eq_pow_sum univ α _
    _ ≤ _ := pow_le_pow_of_le_one hs hx hα

/-- Rectangular and total-degree truncations differ only by controlled higher-degree terms. -/
theorem norm_partialSum_sub_coordinate_box_le {d : ℕ}
    (p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ) (N : ℕ) {x : Fin d → ℂ}
    (hx : (∑ i, ‖x i‖) ≤ 1) :
    ‖p.partialSum (N + 1) x - ∑ α ∈ finiteCoordinateTaylorBox d N,
        finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i)‖ ≤
      (∑ α ∈ finiteCoordinateTaylorBox d N, ‖finiteCoordinateTaylorCoeff p α‖) *
        (∑ i, ‖x i‖) ^ (N + 1) := by
  classical
  rw [partialSum_eq_coordinate_box_total_degree, ← sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ α ∈ finiteCoordinateTaylorBox d N,
        ‖finiteCoordinateTaylorCoeff p α‖ * (∑ i, ‖x i‖) ^ (N + 1) := by
      apply sum_le_sum
      intro α _
      by_cases hα : (∑ i, α i) ≤ N
      · simp only [if_pos hα, sub_self, norm_zero]
        exact mul_nonneg (norm_nonneg _) (pow_nonneg (sum_nonneg fun _ _ => norm_nonneg _) _)
      · simp only [if_neg hα, zero_sub, norm_neg, norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_coordinate_monomial_le_of_degree_gt hx (lt_of_not_ge hα)) (norm_nonneg _)
    _ = _ := (sum_mul _ _ _).symm

/-- A genuine analytic Taylor series gives a rectangular expansion with one fixed family of
coordinate coefficients and an arbitrary-order norm-sum remainder. -/
theorem HasFPowerSeriesAt.exists_coordinate_box_remainder {d : ℕ}
    {f : (Fin d → ℂ) → ℂ} {p : FormalMultilinearSeries ℂ (Fin d → ℂ) ℂ}
    {a : Fin d → ℂ} (hf : HasFPowerSeriesAt f p a) (N : ℕ) :
    ∃ ρ K : ℝ, 0 < ρ ∧ ∀ x : Fin d → ℂ, (∑ i, ‖x i‖) ≤ ρ →
      ‖f (a + x) - ∑ α ∈ finiteCoordinateTaylorBox d N,
          finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i)‖ ≤
        K * (∑ i, ‖x i‖) ^ (N + 1) := by
  obtain ⟨C, hC, H⟩ := (hf.isBigO_sub_partialSum_pow (N + 1)).exists_nonneg
  obtain ⟨r, hr, Hr⟩ := Metric.eventually_nhds_iff.mp H.bound
  refine ⟨min 1 (r / 2),
    C + ∑ α ∈ finiteCoordinateTaylorBox d N, ‖finiteCoordinateTaylorCoeff p α‖,
    lt_min one_pos (half_pos hr),
    fun x hx => ?_⟩
  have hs : 0 ≤ ∑ i, ‖x i‖ := sum_nonneg fun _ _ => norm_nonneg _
  have hnorm : ‖x‖ ≤ ∑ i, ‖x i‖ := (pi_norm_le_iff_of_nonneg hs).mpr fun i =>
    single_le_sum (fun j _ => norm_nonneg (x j)) (mem_univ i)
  have hxr : dist x 0 < r := by
    rw [dist_zero_right]
    have := hx.trans (min_le_right _ _)
    linarith
  have hmain := Hr hxr
  simp only [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg x)] at hmain
  have hbox := norm_partialSum_sub_coordinate_box_le p N (hx.trans (min_le_left _ _))
  have htri := norm_add_le
    (f (a + x) - p.partialSum (N + 1) x)
    (p.partialSum (N + 1) x - ∑ α ∈ finiteCoordinateTaylorBox d N,
      finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i))
  rw [sub_add_sub_cancel] at htri
  calc
    _ ≤ ‖f (a + x) - p.partialSum (N + 1) x‖ +
        ‖p.partialSum (N + 1) x - ∑ α ∈ finiteCoordinateTaylorBox d N,
          finiteCoordinateTaylorCoeff p α * (∏ i, x i ^ α i)‖ := htri
    _ ≤ C * (∑ i, ‖x i‖) ^ (N + 1) +
        (∑ α ∈ finiteCoordinateTaylorBox d N, ‖finiteCoordinateTaylorCoeff p α‖) *
          (∑ i, ‖x i‖) ^ (N + 1) :=
      add_le_add (hmain.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg x) hnorm _) hC)) hbox
    _ = _ := by ring

end PGM
