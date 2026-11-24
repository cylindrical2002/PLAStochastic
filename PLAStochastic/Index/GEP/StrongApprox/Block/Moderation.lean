import PLAStochastic.Index.GEP.StrongApprox.Block.NodeNumerics

/-! # WP5: uniform moderation of the actual smoothed block sums -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- Two CDF tails control the probability of exceeding a symmetric cutoff. -/
theorem sa_real_abs_gt_le_cdf_tails (μ : ProbabilityMeasure ℝ) (a : ℝ) :
    (μ : Measure ℝ).real {x | a < |x|} ≤ cdf (μ : Measure ℝ) (-a) +
      (1 - cdf (μ : Measure ℝ) a) := by
  have hsub : {x : ℝ | a < |x|} ⊆ Iic (-a) ∪ Ioi a := by
    intro x hx
    change a < |x| at hx
    rcases (lt_abs.mp hx) with hx | hx
    · exact Or.inr hx
    · exact Or.inl (show x ≤ -a by linarith)
  apply (measureReal_mono hsub).trans
  apply (measureReal_union_le _ _).trans
  rw [cdf_eq_real, cdf_eq_real, ← compl_Iic,
    probReal_compl_eq_one_sub measurableSet_Iic]

/-- A single class-uniform cutoff constant makes every actual block moderation
failure at most `exp(-5H)` throughout the logarithmic range of block sizes. -/
theorem exists_uniform_saCenteredSum_moderation
    (vlo vhi κ₃ B θ D c : ℝ) (hvlo : 0 < vlo) (hvhi : 0 < vhi)
    (hB : 0 < B) (hθ : 0 < θ) (hD : 0 < D) (hc : 0 < c) :
    ∃ A₀ H₀ : ℝ, 0 < A₀ ∧ 1 ≤ H₀ ∧
      ∀ ν : ProbabilityMeasure ℝ, UnivClass vlo vhi κ₃ B θ ν → SmoothPart D c ν →
      ∀ H : ℝ, H₀ ≤ H → ∀ s : ℝ, ∀ hs : 0 < s, s ≤ 1 →
      ∀ l : ℕ, ∀ hl : 2 ≤ l,
      Real.exp (H / 4) ≤ (l : ℝ) → (l : ℝ) ≤ Real.exp H → 1 / s ≤ (l : ℝ) ^ 8 →
      ((saDensity_centeredSum ν hs (show 0 < l by omega)).law : Measure ℝ).real
        {a | A₀ * Real.sqrt ((l : ℝ) * H) < |a|} ≤ Real.exp (-(5 * H)) := by
  obtain ⟨K, hK, htail⟩ := exists_uniform_saCenteredSumDensity_block_tails
    vlo vhi κ₃ B θ D c hvlo hvhi hB hθ hD hc
  let r := saMeanRadius vlo B θ
  let b := 2 / (5 * (vhi + 1))
  have hr : 0 < r := saMeanRadius_pos hvlo hθ
  have hb : 0 < b := by dsimp [b]; positivity
  obtain ⟨A₀, hA₀, hwindow, hrate, hgauss⟩ := exists_saNodeWindow hb (by norm_num : (0 : ℝ) < 1)
  obtain ⟨H₀, hH₀, hnum⟩ := exists_saBlockWindowInputs
    (C := 1) (K := K) (r := r) (b := b) (S := 1) (A₀ := 0) (Y₀ := A₀) (E := 2)
    (by norm_num) hK hr hb (by norm_num) (by norm_num) hA₀
    (by norm_num) (by norm_num) hwindow hrate hgauss
  refine ⟨A₀, H₀, hA₀, hH₀, ?_⟩
  intro ν hν hsm H hH s hs hs1 l hl hlo hhi hscale
  have hH1 : 1 ≤ H := hH₀.trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH1
  have hl0 : 0 < l := by omega
  have hd : 0 < Real.sqrt (l : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hl0)
  obtain ⟨hdlo, hdhi⟩ := sa_sqrt_block_range hl hlo hhi
  have hn := hnum H hH (Real.sqrt l) hdlo hdhi
  have hY : 0 < A₀ * Real.sqrt H := by positivity
  have hYR : A₀ * Real.sqrt H ≤ r * Real.sqrt l := by
    simpa only [zero_add] using hn.local_window
  have ht := htail ν hν hsm s hs hs1 l hl hscale (A₀ * Real.sqrt H) hY hYR
  have hbnd := hn.density_tail b le_rfl
  have hgauss : saGaussianTail (Real.sqrt (10 * H)) ≤ Real.exp (-(5 * H)) := by
    have hg := saGaussianTail_le_exp (Real.sqrt_nonneg (10 * H))
    rw [Real.sq_sqrt (by positivity)] at hg
    convert hg using 1
    congr 1
    ring
  have hsmall : (2 * H * Real.sqrt H / Real.sqrt l) * saGaussianTail (Real.sqrt (10 * H)) ≤
      (1 / 32) * Real.exp (-(5 * H)) :=
    mul_le_mul hn.error_small hgauss (saGaussianTail_pos _).le (by norm_num)
  have hleft := ht.1.trans (hbnd.trans hsmall)
  have hright := ht.2.trans (hbnd.trans hsmall)
  have hcoord : A₀ * Real.sqrt ((l : ℝ) * H) = Real.sqrt l * (A₀ * Real.sqrt H) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg l)]
    ring
  rw [hcoord]
  apply (sa_real_abs_gt_le_cdf_tails (saDensity_centeredSum ν hs hl0).law _).trans
  have he := add_le_add hleft hright
  simp only [neg_mul] at he
  exact he.trans (by nlinarith [Real.exp_pos (-(5 * H))])

end
end PGM
