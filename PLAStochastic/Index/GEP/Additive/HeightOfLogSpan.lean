import PLAStochastic.Index.GEP.FirstOrderHeight

/-!
# From `log m_ℓ = ℓ c + O(1)` to the additive height formula

`closure-assembly.md` §4.  If the mean hyper-segment counts satisfy
`|log m_ℓ - ℓ c| ≤ B` for every `ℓ`, the first-passage level of `n` is
`log n / c + O(1)`; with `integral_epHeight_bounds` this gives
`|E H - log n / c| ≤ B / c + log 2 / c + 4 KcIn + 3` for every `n ≥ 2`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- The first passage of an approximately geometric sequence. -/
theorem firstPassage_log_bound {m : ℕ → ℝ} (hm0 : m 0 = 1) (hpos : ∀ ℓ, 0 < m ℓ)
    (hex : ∀ x : ℝ, ∃ ℓ, x ≤ m ℓ) {c B : ℝ} (hc : 0 < c)
    (hlog : ∀ ℓ : ℕ, |Real.log (m ℓ) - ℓ * c| ≤ B) {x : ℝ} (hx : 1 ≤ x) :
    |(firstPassage m x : ℝ) - Real.log x / c| ≤ 1 + B / c := by
  have hB : 0 ≤ B := by simpa [hm0] using hlog 0
  have hx0 : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  obtain ⟨j, hj⟩ : ∃ j, firstPassage m x = j := ⟨_, rfl⟩
  have hhit : x ≤ m j := hj ▸ firstPassage_hit (hex x)
  have h1 : Real.log x ≤ j * c + B := by
    have := Real.log_le_log hx0 hhit
    have := (abs_le.1 (hlog j)).2
    linarith
  have h2 : (j : ℝ) * c ≤ Real.log x + c + B := by
    rcases Nat.eq_zero_or_pos j with h0 | hj0
    · rw [h0, Nat.cast_zero, zero_mul]; linarith
    · obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hmk : m k < x := lt_of_lt_firstPassage (by rw [hj]; omega)
      have := Real.log_lt_log (hpos k) hmk
      have := (abs_le.1 (hlog k)).1
      rw [hk, Nat.cast_succ, add_mul, one_mul]
      linarith
  have hBc : 0 ≤ B / c := div_nonneg hB hc.le
  have e1 : (j * c + B) / c = j + B / c := by
    rw [add_div, mul_div_cancel_right₀ _ hc.ne']
  have e2 : (Real.log x + c + B) / c = Real.log x / c + 1 + B / c := by
    rw [add_div, add_div, div_self hc.ne']
  have h1' : Real.log x / c ≤ j + B / c := by
    rw [← e1]; exact div_le_div_of_nonneg_right h1 hc.le
  have h2' : (j : ℝ) ≤ Real.log x / c + 1 + B / c := by
    rw [← e2, le_div_iff₀ hc]; exact h2
  rw [hj, abs_le]
  constructor <;> linarith

/-- The layer facts used below, specialised to the input class constants. -/
private theorem meanSpan_step [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    0 < meanSpan P eps g ℓ ∧
      meanSpan P eps g (ℓ + 1) = meanSpan P eps g ℓ * segMean P eps (epLayerSeq eps g ℓ) ∧
      eps ^ 2 / (128 * bIn μ₀ σ₀) ≤ segMean P eps (epLayerSeq eps g ℓ) ∧
      segMean P eps (epLayerSeq eps g ℓ) ≤ cPlus * eps ^ 2 / vIn μ₀ σ₀ := by
  obtain ⟨hL, -, h1, h2, h3⟩ := layerOK_all (layerOK_input hg) (bAbs_le_bIn μ₀ σ₀)
    (βAbs_le_βIn _ _) (vIn_pos hg.mu_pos hg.sigma_pos) (vIn_le μ₀ σ₀) KcAbs_le_KcIn heps ℓ
  exact ⟨hL.cnt_pos, h1, h2, h3⟩

/-- The mean counts are the partial products of the per-layer compression ratios. -/
theorem log_meanSpan_eq_sum [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    Real.log (meanSpan P eps g ℓ) =
      ∑ j ∈ range ℓ, Real.log (segMean P eps (epLayerSeq eps g j)) := by
  have heps1 : 1 ≤ eps := le_trans (one_le_epsZero _ _) heps
  have hepspos : 0 < eps := by linarith
  have hbpos : 0 < bIn μ₀ σ₀ := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  induction ℓ with
  | zero => simp [meanSpan_zero]
  | succ ℓ ih =>
    obtain ⟨hm, hstep, hlo, -⟩ := meanSpan_step hg heps ℓ
    have hs : 0 < segMean P eps (epLayerSeq eps g ℓ) := lt_of_lt_of_le (by positivity) hlo
    rw [hstep, Real.log_mul hm.ne' hs.ne', ih, sum_range_succ]

/-- The per-layer bracket `eps²/c ≤ C_ℓ ≤ c eps²` with `c = cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀)`. -/
theorem segMean_bracket [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ} {μ₀ σ₀ κ₀ : ℝ}
    (hg : GapLaw P g μ₀ σ₀ κ₀) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps) (ℓ : ℕ) :
    eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ segMean P eps (epLayerSeq eps g ℓ) ∧
      segMean P eps (epLayerSeq eps g ℓ) ≤ cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * eps ^ 2 := by
  have hbpos : 0 < bIn μ₀ σ₀ := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  obtain ⟨-, -, hlo, hhi⟩ := meanSpan_step hg heps ℓ
  have hc1 : 128 * bIn μ₀ σ₀ ≤ cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := le_max_left _ _
  have hc2 : cPlus / vIn μ₀ σ₀ ≤ cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := le_max_right _ _
  constructor
  · calc eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2 / (128 * bIn μ₀ σ₀) := by gcongr
      _ ≤ _ := hlo
  · calc segMean P eps (epLayerSeq eps g ℓ) ≤ cPlus * eps ^ 2 / vIn μ₀ σ₀ := hhi
      _ = cPlus / vIn μ₀ σ₀ * eps ^ 2 := by ring
      _ ≤ cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) * eps ^ 2 := by gcongr

/-- The additive height formula from `|log m_ℓ - ℓ c| ≤ B`. -/
theorem integral_epHeight_additive_of_logSpan [IsProbabilityMeasure P] {g : ℕ → Ω → ℝ}
    {μ₀ σ₀ κ₀ : ℝ} (hg : GapLaw P g μ₀ σ₀ κ₀) (x0 : Ω → ℝ) {eps : ℝ}
    (heps : epsZero (bIn μ₀ σ₀) (βIn σ₀ (lkap P (inputPairs g))) ≤ eps)
    (hbig : 2 * cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤ eps ^ 2) {c B : ℝ} (hc : 0 < c)
    (hlog : ∀ ℓ : ℕ, |Real.log (meanSpan P eps g ℓ) - ℓ * c| ≤ B) {n : ℕ} (hn : 2 ≤ n) :
    |∫ ω, (epHeight eps (fun t => x0 ω + gapKeys (seq g ω) t) n : ℝ) ∂P - Real.log n / c| ≤
      B / c + Real.log 2 / c + 4 * KcIn + 3 := by
  have hbpos : 0 < bIn μ₀ σ₀ := lt_of_lt_of_le bAbs_pos (bAbs_le_bIn μ₀ σ₀)
  have hm0 : meanSpan P eps g 0 = 1 := meanSpan_zero P eps g
  have hmpos : ∀ ℓ, 0 < meanSpan P eps g ℓ := fun ℓ => (meanSpan_step hg heps ℓ).1
  have hc1 : 128 * bIn μ₀ σ₀ ≤ cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := le_max_left _ _
  have hccpos : 0 < cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := lt_of_lt_of_le (by positivity) hc1
  have hratio : ∀ ℓ, eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) ≤
      meanSpan P eps g (ℓ + 1) / meanSpan P eps g ℓ := by
    intro ℓ
    rw [(meanSpan_step hg heps ℓ).2.1, mul_div_cancel_left₀ _ (hmpos ℓ).ne']
    exact (segMean_bracket hg heps ℓ).1
  have hq : 1 < eps ^ 2 / cBr (bIn μ₀ σ₀) (vIn μ₀ σ₀) := by
    rw [lt_div_iff₀ hccpos]; linarith
  have hex : ∀ x : ℝ, ∃ ℓ, x ≤ meanSpan P eps g ℓ := fun x =>
    geometric_exists_ge hq hm0 hratio x
  obtain ⟨hlo, hhi⟩ := integral_epHeight_bounds hg x0 heps hbig (n := n) (by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hA := firstPassage_log_bound hm0 hmpos hex hc hlog hn1
  have hB := firstPassage_log_bound hm0 hmpos hex hc hlog (x := 2 * n) (by linarith)
  have hlog2 : Real.log (2 * n) = Real.log 2 + Real.log n :=
    Real.log_mul (by norm_num) (by positivity)
  rw [hlog2, add_div] at hB
  have hK : 1 ≤ KcIn := one_le_KcIn
  have hl2 : 0 ≤ Real.log 2 / c := div_nonneg (Real.log_nonneg (by norm_num)) hc.le
  rw [abs_le] at hA hB ⊢
  constructor <;> linarith

end

end PGM
