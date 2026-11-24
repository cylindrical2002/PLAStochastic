import PLAStochastic.Index.GEP.StrongApprox.Endgame.PowerOfSixteenCoupling
import PLAStochastic.Index.GEP.StrongApprox.Tree.Endpoint

/-! # Class-uniform strong approximation on the original smooth-part class

This closes the frozen `StrongApproxClass` interface.  Constants are chosen
before the source law.  The coupling has the exact infinite iid marginals,
error `K n^(1/8) sqrt(log n)`, and failure probability at most `n^(-2)`.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Filter

/-- The strong approximation of WP5, under the original class parameters only. -/
theorem strongApproxClass (vlo vhi κ₃ B θ D c₀ : ℝ)
    (hvlo : 0 < vlo) (hvv : vlo ≤ vhi) (hθ : 0 < θ) (hc₀ : 0 < c₀) :
    StrongApproxClass vlo vhi κ₃ B θ D c₀ := by
  classical
  by_cases hnonempty : ∃ ν : ProbabilityMeasure ℝ,
      UnivClass vlo vhi κ₃ B θ ν ∧ SmoothPart D c₀ ν
  · obtain ⟨ν₀, hν₀, hsm₀⟩ := hnonempty
    have hvhi : 0 < vhi := hvlo.trans_le hvv
    have hB : 0 < B := hν₀.B_pos
    have hD : 0 < D := hsm₀.D_pos hc₀
    obtain ⟨C, H₀, hC, _, htree⟩ := exists_uniform_saDyadicLeafCoupling_bound
      vlo vhi κ₃ B θ D c₀ hvlo hvhi hB hθ hD hc₀
    let w := max 20 (10 / bernsteinRate θ B)
    let A := 3 * C * (3 / Real.log 16 + 1)
    have hrate : 0 < bernsteinRate θ B := bernsteinRate_pos hθ hB
    have hw : 20 ≤ w := le_max_left _ _
    have hcw : 10 ≤ bernsteinRate θ B * w := by
      have he := (div_le_iff₀ hrate).1 (le_max_right 20 (10 / bernsteinRate θ B))
      simpa only [mul_comm] using he
    have hA : 0 ≤ A := by
      dsimp [A]
      positivity
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.1 (sa_eventually_final_scales w H₀)
    apply strongApproxClass_of_pow_sixteen
    refine ⟨A + Real.sqrt w * (1 + Real.sqrt (vhi + 1)) + 1 + 1 / (2 * Real.sqrt vlo),
      k₀, by positivity, ?_⟩
    intro ν hν hsm k hk
    obtain ⟨hN, hH₀, hH, hlarge, hlog, hnoise⟩ := hk₀ k hk
    apply sa_coupling_pow_sixteen_of_leaf hvlo hθ hA hw hcw ν hν k hN hH hlarge hlog hnoise
    intro hs hV
    let N : ℝ := (16 ^ k : ℕ)
    let H : ℝ := Real.log N
    have hNpos : 0 < N := by positivity
    have hN1 : 1 ≤ N := by dsimp [N]; linarith
    have hs1 : 1 / N ^ 2 ≤ 1 := (sa_smoothing_scale_bounds hN1).2.1
    have hlo : Real.exp (H / 4) ≤ ((2 ^ k : ℕ) : ℝ) := by
      simpa only [H, N, Nat.cast_pow, Nat.cast_ofNat] using (sa_pow_sixteen_window k).le
    have hhi : ((2 ^ k * 2 ^ (3 * k) : ℕ) : ℝ) ≤ Real.exp H := by
      rw [Nat.mul_comm, sa_pow_sixteen_partition]
      exact (Real.exp_log hNpos).symm.le
    have hscale : 1 / (1 / N ^ 2) ≤ (((2 ^ k : ℕ) : ℝ) ^ 8) := by
      simpa only [one_div, inv_inv, Nat.cast_pow, Nat.cast_ofNat, N] using
        (sa_pow_sixteen_square k).le
    have he := htree ν hν hsm H hH₀ (1 / N ^ 2) hs hs1
      (2 ^ k) (by positivity) (3 * k) hlo hhi hscale hV
    have herror : (((3 * k : ℕ) : ℝ) + 1) * (3 * C * H * Real.sqrt H) ≤
        A * H ^ 2 * Real.sqrt H := by
      have hd := sa_pow_sixteen_depth k hH
      have hHpos : 0 ≤ H := by dsimp [H, N]; linarith
      have hm := mul_le_mul_of_nonneg_right hd
        (show 0 ≤ 3 * C * H * Real.sqrt H by positivity)
      push_cast at hm ⊢
      dsimp only [A, H, N] at hm ⊢
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hm ⊢
      nlinarith only [hm]
    have hLle : (2 : ℝ) ^ (3 * k) ≤ N := by
      have hp : (2 : ℝ) ^ (3 * k) * (2 : ℝ) ^ k = N := by
        dsimp only [N]
        exact_mod_cast sa_pow_sixteen_partition k
      have hm : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
      nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (3 * k)]
    obtain ⟨hπ, _, _⟩ := saDyadicLeafCoupling_laws ν hs (show 0 < 2 ^ k by positivity) hV (3 * k)
    let := hπ
    apply le_trans (measureReal_mono (μ := saDyadicLeafCoupling ν hs (show 0 < 2 ^ k by positivity) hV (3 * k))
      (show saLeafBad (2 ^ (3 * k)) (A * H ^ 2 * Real.sqrt H) ⊆
        saLeafBad (2 ^ (3 * k)) ((((3 * k : ℕ) : ℝ) + 1) * (3 * C * H * Real.sqrt H)) from ?_))
    · exact he.trans (sa_tree_failure_budget (by dsimp [N]; linarith) hLle)
    · rintro q ⟨j, hj, herr⟩
      exact ⟨j, hj, herror.trans_lt herr⟩
  · refine ⟨0, 16, le_rfl, le_rfl, ?_⟩
    intro ν hν hsm
    exact False.elim (hnonempty ⟨ν, hν, hsm⟩)

end
end PGM
