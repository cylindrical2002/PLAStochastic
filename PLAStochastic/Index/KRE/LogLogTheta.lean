import PLAStochastic.Index.KRE.FixedParameter
import PLAStochastic.Index.KRE.EventualConditions

/-!
# H-K-RE: the expected rank-equispaced height under Model K

Let `X 0, X 1, …` be iid with a Model K density `f` on `[A, B]` (`DensityK`: bounded above and
below by positive constants, Lipschitz, total mass one), and let the keys for sample size `n`
be the sorted first `n` samples (`kKeys X n`).  Along `n → ∞`, `ε → ∞`, `log ε = o(log n)`,
the expected height of the actual ALG-RE run is `O(log log n)` (`H_K_RE_upper`); under RE-LOWER
`log ε ≤ D (log n)^(1-η)` it is also `Ω(log log n)` (`H_K_RE_lower`), hence `Θ(log log n)`
(`H_K_RE_theta`).

The fixed-parameter bounds of `PLAStochastic.Index.KRE.FixedParameter` are used with the concentration levels
`t = tRE n`, `j = jK n` and the regime threshold `Dn = DnK Λ n ε`; their side conditions hold
eventually by `PLAStochastic.Index.KRE.EventualConditions`, and the bad event has mass at most `63 / n²`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset Filter Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : ℝ → ℝ} {A B fmin fmax Lf : ℝ}

/-- The constant `Λ = L / (2 δ) · 80` of the quantile `Q`, with `L = Lf / f₋³ + 1`, `δ = 1 / f₊`. -/
def kreLamK (Lf fmin fmax : ℝ) : ℝ := kreLam (Lf / fmin ^ 3 + 1) (1 / fmax)

theorem kreLamK_pos (hf : DensityK f A B fmin fmax Lf) : 0 < kreLamK Lf fmin fmax := by
  have hL := kre_quantK_lip_pos hf
  have hδ := kre_quantK_delta_pos hf
  unfold kreLamK kreLam
  positivity

/-- Total mass of the bad event at the levels `tRE n`, `jK n`. -/
theorem kreBadMass_le {n : ℕ} (hn : 1 ≤ n) :
    18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE n)) +
        ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ jK n ≤ 63 / (n : ℝ) ^ 2 := by
  have h1 := badMass_tRE_le hn
  have h2 := windowMass_jK_le hn
  have e : (63 : ℝ) / (n : ℝ) ^ 2 = 18 / (n : ℝ) ^ 2 + 2 * (18 / (n : ℝ) ^ 2) + 9 / (n : ℝ) ^ 2 := by
    ring
  linarith

theorem kreBadMass_nonneg (n t j : ℕ) :
    0 ≤ 18 / (n : ℝ) ^ 2 + 2 * (((2 * n + 1 : ℕ) : ℝ) ^ 2 * pairFail t) +
        ((2 * n + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ j := by
  have := pairFail_nonneg t
  positivity

/-- `63 / n² ≤ 1 / 2` and `(⌊log₂ n⌋ + 1) · 63 / n² ≤ 1` for `n ≥ 160000`. -/
theorem kreBadMass_small {n : ℕ} (hn : 160000 ≤ n) :
    63 / (n : ℝ) ^ 2 ≤ 1 / 2 ∧ ((Nat.log 2 n : ℝ) + 1) * (63 / (n : ℝ) ^ 2) ≤ 1 := by
  have hN : (160000 : ℝ) ≤ n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < n := by linarith
  have hlog : ((Nat.log 2 n : ℕ) : ℝ) + 1 ≤ n := by
    have := Nat.log_lt_self 2 (by omega : n ≠ 0)
    have : Nat.log 2 n + 1 ≤ n := this
    exact_mod_cast this
  have h63 : 63 / (n : ℝ) ^ 2 ≤ 63 / (n : ℝ) := by
    apply div_le_div_of_nonneg_left (by norm_num) hN0
    nlinarith
  have h63' : 63 / (n : ℝ) ≤ 1 / 2 := by
    rw [div_le_iff₀ hN0]; linarith
  refine ⟨h63.trans h63', ?_⟩
  calc ((Nat.log 2 n : ℝ) + 1) * (63 / (n : ℝ) ^ 2) ≤ (n : ℝ) * (63 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_right hlog (by positivity)
    _ = 63 / (n : ℝ) := by field_simp
    _ ≤ 1 := by rw [div_le_iff₀ hN0]; linarith

/-- **H-K-RE, upper half.**  Along `n → ∞`, `ε → ∞`, `log ε = o(log n)`, the expected height of
ALG-RE on the sorted Model K sample of size `n` is `O(log log n)`. -/
theorem H_K_RE_upper (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0)) :
    ∃ C : ℝ, ∀ᶠ k in atTop,
      ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ≤ C * Real.log (Real.log (n k)) := by
  have hΛ := kreLamK_pos hf
  obtain ⟨C, hC⟩ := KRE_UK_le_loglog hΛ hn hε
  refine ⟨C + 1, ?_⟩
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [KRE_eventually hΛ hn hε hεn, hC, hLL.eventually_ge_atTop 1]
    with k hk hCk hLLk
  obtain ⟨h160, heps, -, -, hN1, -, hC1, hC2, hR1, hR2, hq, hqn⟩ := hk
  have hint := integral_reHeight_K_le hf hX hind h160 heps (tRE (n k)) (jK (n k))
    (Dn := DnK (kreLamK Lf fmin fmax) (n k) (ε k)) hN1 hC1 hC2 hR1 hR2 hq hqn
  have hU : kreUpper (n k) (ε k) (Lf / fmin ^ 3 + 1) (1 / fmax) (tRE (n k)) =
      UK (kreLamK Lf fmin fmax) (n k) (ε k) (tRE (n k)) := rfl
  have hn1 : 1 ≤ n k := by omega
  have hmass := kreBadMass_le hn1
  obtain ⟨-, hsmall⟩ := kreBadMass_small h160
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 (n k) : ℝ) + 1 := by positivity
  have hbad : ((Nat.log 2 (n k) : ℝ) + 1) *
      (18 / (n k : ℝ) ^ 2 + 2 * (((2 * n k + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE (n k))) +
        ((2 * n k + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ jK (n k)) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hmass hlog0).trans hsmall
  rw [hU] at hint
  calc ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P
      ≤ UK (kreLamK Lf fmin fmax) (n k) (ε k) (tRE (n k)) + 1 := by linarith
    _ ≤ C * Real.log (Real.log (n k)) + Real.log (Real.log (n k)) := by linarith
    _ = (C + 1) * Real.log (Real.log (n k)) := by ring

/-- **H-K-RE, lower half.**  Along `n → ∞`, `ε → ∞` with RE-LOWER
`log ε ≤ D (log n)^(1-η)`, the expected height of ALG-RE on the sorted Model K sample is
`Ω(log log n)`. -/
theorem H_K_RE_lower (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤ ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P := by
  have hΛ := kreLamK_pos hf
  have hεn := tendsto_logRatio_of_RE hn hε hη0 hRE
  obtain ⟨c, hc, hcK⟩ := KRE_LoK_ge_loglog hn hε hη0 hη1 hD hRE
  refine ⟨c / 2, by positivity, ?_⟩
  have hL : Tendsto (fun k => Real.log (n k)) atTop atTop := Real.tendsto_log_atTop.comp hn
  have hLL : Tendsto (fun k => Real.log (Real.log (n k))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards [KRE_eventually hΛ hn hε hεn, KRE_lower_eventually hΛ hn hε hη0 hRE, hcK,
    hLL.eventually_ge_atTop 1, hL.eventually_gt_atTop 0] with k hk hlo hcKk hLLk hLk
  obtain ⟨h160, heps, hj, -, -, hN2, -, -, -, -, -, -⟩ := hk
  obtain ⟨hDn, hsqrt⟩ := hlo
  have ht : 1 ≤ tRE (n k) := by
    unfold tRE
    rw [Nat.one_le_ceil_iff]
    have := cRE_pos
    positivity
  have hLo : kreLower (n k) (ε k) = LoK (n k) (ε k) := rfl
  have hL0 : 0 ≤ kreLower (n k) (ε k) := by
    rw [hLo]
    have : 0 ≤ c * Real.log (Real.log (n k)) := by positivity
    linarith
  have hint := integral_reHeight_K_ge hf hX hind h160 heps ht hj
    (Dn := DnK (kreLamK Lf fmin fmax) (n k) (ε k)) hN2 hDn hsqrt hL0
  have hn1 : 1 ≤ n k := by omega
  have hmass := kreBadMass_le hn1
  obtain ⟨hhalf, -⟩ := kreBadMass_small h160
  have hfac : 1 / 2 ≤ 1 - (18 / (n k : ℝ) ^ 2 +
      2 * (((2 * n k + 1 : ℕ) : ℝ) ^ 2 * pairFail (tRE (n k))) +
        ((2 * n k + 1 : ℕ) : ℝ) ^ 2 * (71 / 72 : ℝ) ^ jK (n k)) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hfac hL0
  rw [hLo] at hmul hint
  calc c / 2 * Real.log (Real.log (n k)) = (c * Real.log (Real.log (n k))) * (1 / 2) := by ring
    _ ≤ LoK (n k) (ε k) * (1 / 2) := by
        apply mul_le_mul_of_nonneg_right hcKk (by norm_num)
    _ ≤ _ := hmul.trans hint

/-- **H-K-RE.**  Under `n → ∞`, `ε → ∞`, `log ε = o(log n)` and RE-LOWER, the expected height of
ALG-RE on the sorted Model K sample is `Θ(log log n)`. -/
theorem H_K_RE_theta (hf : DensityK f A B fmin fmax Lf) {X : ℕ → Ω → ℝ}
    (hX : ∀ i, HasLaw (X i) (densityLaw f A B) P) (hind : iIndepFun X P)
    {n : ℕ → ℕ} {ε : ℕ → ℝ}
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop) (hε : Tendsto ε atTop atTop)
    (hεn : Tendsto (fun k => Real.log (ε k) / Real.log (n k)) atTop (𝓝 0))
    {η D : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hD : 0 < D)
    (hRE : ∀ᶠ k in atTop, Real.log (ε k) ≤ D * Real.log (n k) ^ (1 - η)) :
    ∃ c > 0, ∃ C : ℝ, ∀ᶠ k in atTop,
      c * Real.log (Real.log (n k)) ≤ ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ∧
        ∫ ω, (reHeight (ε k) (kKeys X (n k) ω) (n k) : ℝ) ∂P ≤ C * Real.log (Real.log (n k)) := by
  obtain ⟨C, hC⟩ := H_K_RE_upper hf hX hind hn hε hεn
  obtain ⟨c, hc, hc'⟩ := H_K_RE_lower hf hX hind hn hε hη0 hη1 hD hRE
  exact ⟨c, hc, C, hc'.and hC⟩

end

end PGM
