import PLAStochastic.Index.KEP.AsymptoticUpper

/-!
# H-K-EP: the Model K ALG-PGM height

Let `X 0, X 1, …` be iid with a Model K law (`DensityK f A B fmin fmax Lf`) and let the keys for
sample size `n` be the sorted first `n` samples (`kKeys X n`).  Along any sequence with
`n → ∞`, `ε → ∞` and `log ε = o(log n)`, `E H_EP / (log n / (2 log ε)) → 1` (`H_K_EP`).

The lower bound `(1 - ν)² log n / (2 log ε) ≤ E H_EP` is `integral_epHeight_kKeys_ge_asymp`
with the local-count bound `refK_expCoord_le`; the upper bound
`E H_EP ≤ (1 + 3ν) log n / (2 log ε)` is `integral_epHeight_kKeys_le_asymp`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- **H-K-EP.**  For sorted iid Model K keys, along any sequence with `n → ∞`, `ε → ∞` and
`log ε = o(log n)`, `E H_EP / (log n / (2 log ε)) → 1`. -/
theorem H_K_EP (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    Tendsto (fun k => (∫ ω, (epHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P) /
      (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hpos : ∀ᶠ k in atTop, 0 < Real.log (n k) / (2 * Real.log (ε k)) := by
    filter_upwards [hL.eventually_gt_atTop 0, hε.eventually_ge_atTop (Real.exp 1)] with k h1 h2
    have : 1 ≤ Real.log (ε k) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) h2
    positivity
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set ν := min (1 / 8) ((1 - a) / 4) with hν
    have hν0 : 0 < ν := lt_min (by norm_num) (by linarith)
    have hν1 : ν < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hνa : ν ≤ (1 - a) / 4 := min_le_right _ _
    have hlt : a < (1 - ν) * (1 - ν) := by nlinarith [sq_nonneg ν]
    filter_upwards [integral_epHeight_kKeys_ge_asymp hf hX hind refK_expCoord_le hn hε hεn
      hν0 hν1, hpos] with k h1 h2
    rw [lt_div_iff₀ h2]
    exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hlt h2) h1
  · set ν := min (1 / 8) ((b - 1) / 6) with hν
    have hν0 : 0 < ν := lt_min (by norm_num) (by linarith)
    have hν1 : ν < 1 / 4 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    have hνb : ν ≤ (b - 1) / 6 := min_le_right _ _
    have hlt : 1 + 3 * ν < b := by linarith
    filter_upwards [integral_epHeight_kKeys_le_asymp hf hX hind hn hε hεn hν0 hν1, hpos]
      with k h1 h2
    rw [div_lt_iff₀ h2]
    exact lt_of_le_of_lt h1 (mul_lt_mul_of_pos_right hlt h2)

end

end PGM
