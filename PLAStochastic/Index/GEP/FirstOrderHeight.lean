import PLAStochastic.Index.Endpoint.LayerInduction

/-!
# H-G-EP: the expected endpoint height under Model G

**Theorem (`H_G_EP`).**  Let the gaps `g 0, g 1, …` be iid with mean `μ₀ > 0`,
variance `σ₀² > 0` and finite centred absolute third moment (`GapLaw`), and let the
keys be `x₀ + g 0 + ⋯ + g (t-1)` for an arbitrary (possibly random) offset `x₀`.
Run ALG-PGM (ALG-OPT at every layer, endpoint promotion) on the first `n` keys with
error `ε`.  Along any sequence with `n → ∞`, `ε → ∞` and `log ε = o(log n)`,

`E H / (log n / (2 log ε)) → 1`.

Since `log C∞ = 2 log ε + O(1)` for the fixed ratio `C∞ / ε²`, this is the claim
`E H ∼ log n / log C∞ ∼ log n / (2 log ε)` of `MAIN_RESULTS.md` (H-G-EP).  No
positivity of the gaps is used.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem meanSpan_zero (P : Measure Ω) [IsProbabilityMeasure P] (eps : ℝ) (g : ℕ → Ω → ℝ) :
    meanSpan P eps g 0 = 1 := by
  simp [meanSpan, lcount, epLayerSeq, inputPairs]

theorem one_le_cBr {b vmin : ℝ} (hb : bAbs ≤ b) : 1 ≤ cBr b vmin := by
  have : 1 ≤ 128 * b := by
    have := bAbs_pos
    have h2 : 1 ≤ bAbs := by unfold bAbs K2; norm_num
    linarith
  exact le_trans this (le_max_left _ _)

/-- **H-G-EP.** -/
theorem H_G_EP [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) (x0 : Ω → ℝ) {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    Tendsto (fun k =>
        (∫ ω, (epHeight (ε k) (fun t => x0 ω + gapKeys (seq g ω) t) (n k) : ℝ) ∂P) /
          (Real.log (n k) / (2 * Real.log (ε k)))) atTop (𝓝 1) := by
  set b := bIn μ₀ σ₀
  set β := βIn σ₀ (lkap P (inputPairs g))
  set vmin := vIn μ₀ σ₀
  set c := cBr b vmin
  set e₀ := epsZero b β
  have hc : 1 ≤ c := one_le_cBr (bAbs_le_bIn μ₀ σ₀)
  have hvmin0 : 0 < vmin := vIn_pos hg.mu_pos hg.sigma_pos
  have hbpos : 0 < b := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  -- the good parameters
  let good : ℕ → Prop := fun k => e₀ ≤ ε k ∧ 2 * c ≤ ε k ^ 2
  classical
  let m : ℕ → ℕ → ℝ := fun k => if good k then meanSpan P (ε k) g else fun ℓ => (ε k ^ 2) ^ ℓ
  have hm0 : ∀ k, m k 0 = 1 := by
    intro k; by_cases hk : good k
    · simp only [m, if_pos hk]; exact meanSpan_zero P _ g
    · simp only [m, if_neg hk, pow_zero]
  -- the bracket, valid for every k
  have hbr : ∀ k ℓ, ε k ^ 2 / c ≤ m k (ℓ + 1) / m k ℓ ∧ m k (ℓ + 1) / m k ℓ ≤ c * ε k ^ 2 := by
    intro k ℓ
    by_cases hk : good k
    · simp only [m, if_pos hk]
      have hall := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀) (βAbs_le_βIn _ _) hvmin0
        (vIn_le μ₀ σ₀) KcAbs_le_KcIn hk.1 ℓ
      have hpos : 0 < meanSpan P (ε k) g ℓ := hall.1.cnt_pos
      have hq : meanSpan P (ε k) g (ℓ + 1) / meanSpan P (ε k) g ℓ =
          segMean P (ε k) (epLayerSeq (ε k) g ℓ) := by
        have e1 : meanSpan P (ε k) g (ℓ + 1) =
            meanSpan P (ε k) g ℓ * segMean P (ε k) (epLayerSeq (ε k) g ℓ) := hall.2.2.1
        rw [e1, mul_div_cancel_left₀ _ hpos.ne']
      rw [hq]
      have hlo := hall.2.2.2.1
      have hhi := hall.2.2.2.2
      have hc1 : 128 * b ≤ c := le_max_left _ _
      have hc2 : cPlus / vmin ≤ c := le_max_right _ _
      constructor
      · calc ε k ^ 2 / c ≤ ε k ^ 2 / (128 * b) := by gcongr
          _ ≤ _ := hlo
      · calc segMean P (ε k) (epLayerSeq (ε k) g ℓ) ≤ cPlus * ε k ^ 2 / vmin := hhi
          _ = cPlus / vmin * ε k ^ 2 := by ring
          _ ≤ c * ε k ^ 2 := by gcongr
    · simp only [m, if_neg hk]
      by_cases he : ε k = 0
      · simp [he]
      · have hpow : (ε k ^ 2) ^ (ℓ + 1) / (ε k ^ 2) ^ ℓ = ε k ^ 2 := by
          rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ he))]
        rw [hpow]
        have he2 : 0 ≤ ε k ^ 2 := sq_nonneg _
        constructor
        · exact div_le_self he2 hc
        · exact le_mul_of_one_le_left he2 hc
  -- eventually the parameters are good and n ≥ 1
  have hgood : ∀ᶠ k in atTop, good k ∧ 1 ≤ n k := by
    have h1 : ∀ᶠ k in atTop, max e₀ (2 * c) ≤ ε k := hε.eventually_ge_atTop _
    have h2 : ∀ᶠ k in atTop, (1 : ℝ) ≤ n k := hn.eventually_ge_atTop 1
    filter_upwards [h1, h2] with k hk hnk
    have he0 : e₀ ≤ ε k := le_trans (le_max_left _ _) hk
    have hc2 : 2 * c ≤ ε k := le_trans (le_max_right _ _) hk
    have hε1 : 1 ≤ ε k := by linarith
    refine ⟨⟨he0, ?_⟩, by exact_mod_cast hnk⟩
    calc 2 * c ≤ ε k := hc2
      _ ≤ ε k ^ 2 := by nlinarith
  have hbounds : ∀ᶠ k in atTop,
      (firstPassage (m k) (n k) : ℝ) - (4 * KcIn + 2) ≤
          ∫ ω, (epHeight (ε k) (fun t => x0 ω + gapKeys (seq g ω) t) (n k) : ℝ) ∂P ∧
        ∫ ω, (epHeight (ε k) (fun t => x0 ω + gapKeys (seq g ω) t) (n k) : ℝ) ∂P ≤
          (firstPassage (m k) (2 * n k) : ℝ) + (4 * KcIn + 2) := by
    filter_upwards [hgood] with k ⟨hk, hnk⟩
    have hmk : m k = meanSpan P (ε k) g := by simp only [m, if_pos hk]
    rw [hmk]
    obtain ⟨hlo, hhi⟩ := integral_epHeight_bounds hg x0 hk.1 hk.2 hnk
    have hK : 0 ≤ 4 * KcIn := by have := one_le_KcIn; linarith
    constructor <;> linarith
  obtain ⟨hx1, hx⟩ := level_self hn
  obtain ⟨hy1, hy⟩ := level_two_mul hn
  exact div_scale_tendsto_of_squeeze hc hm0 (fun k ℓ => (hbr k ℓ).1) (fun k ℓ => (hbr k ℓ).2)
    hε hn hεn (4 * KcIn + 2) hx1 hx hy1 hy (hbounds.mono fun k h => h.1)
    (hbounds.mono fun k h => h.2)

end

end PGM
