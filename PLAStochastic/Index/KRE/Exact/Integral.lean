import PLAStochastic.Index.KRE.Exact.Transfer

/-! # The window-excluded expectation error is O(N⁻² log N) -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
universe u

theorem kre_integral_exact_of_event {f : ℝ → ℝ} {fmin fmax Lf eps : ℝ} {n h : ℕ}
    (hf : DensityK f 0 1 fmin fmax Lf) (he : 1 ≤ eps) (hn : 16 ≤ n)
    (hY : 1 ≤ Real.log n) {E : Set (ℕ → ℝ)} (hEm : MeasurableSet E)
    (hbad : expSeqMeasure.real Eᶜ ≤ 63 / (n : ℝ) ^ 2)
    (hgood : ∀ ω ∈ E, reHeight eps (renyiKeys f n ω) n = h) :
    |∫ ω, (reHeight eps (renyiKeys f n ω) n : ℝ) ∂expSeqMeasure - h| ≤
      200 * Real.log n / (n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hnr : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsmall : 63 / (n : ℝ) ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith
  have hEpos : 0 < expSeqMeasure.real E := by
    rw [probReal_compl_eq_one_sub hEm] at hbad
    linarith
  obtain ⟨ω₀, hω₀⟩ := nonempty_of_measureReal_ne_zero hEpos.ne'
  let H : (ℕ → ℝ) → ℝ := fun ω => (reHeight eps (renyiKeys f n ω) n : ℝ)
  let B : ℝ := (Nat.log 2 n : ℝ) + 1
  have hHB : ∀ ω, H ω ≤ B := fun ω => by
    dsimp [H, B]
    exact_mod_cast (reHeight_le_log (p := renyiKeys f n ω) he hn1)
  have hhB : (h : ℝ) ≤ B := by
    have := hHB ω₀
    dsimp only [H] at this
    rw [hgood ω₀ hω₀] at this
    exact this
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hBY : B ≤ 3 * Real.log n := by
    have hlog := Real.natLog_le_logb n 2
    norm_num only [Nat.cast_ofNat] at hlog
    have h2 : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
    have h2p : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hY0 : 0 ≤ Real.log n := by linarith
    have hdiv : Real.log n / Real.log 2 ≤ 2 * Real.log n := by
      rw [div_le_iff₀ h2p]
      nlinarith
    change (Nat.log 2 n : ℝ) + 1 ≤ 3 * Real.log n
    rw [Real.logb] at hlog
    linarith
  have hpt : ∀ ω, |H ω - h| ≤ Eᶜ.indicator (fun _ => B) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [Set.indicator_of_notMem (by simpa using hω)]
      dsimp only [H]
      rw [hgood ω hω]
      simp
    · rw [Set.indicator_of_mem (by simpa using hω), abs_le]
      have := hHB ω
      have hH0 : 0 ≤ H ω := Nat.cast_nonneg _
      have hh0 : (0 : ℝ) ≤ h := Nat.cast_nonneg _
      constructor <;> linarith
  have hHi : Integrable H expSeqMeasure :=
    integrable_reHeight he hn1 (measurable_kreKeys hf n).aemeasurable
  have hdi : Integrable (fun ω => |H ω - h|) expSeqMeasure :=
    (hHi.sub (integrable_const (h : ℝ))).abs
  have hbi : Integrable (Eᶜ.indicator (fun _ => B)) expSeqMeasure :=
    (integrable_const B).indicator hEm.compl
  have hm := integral_mono hdi hbi hpt
  rw [integral_indicator hEm.compl, setIntegral_const, smul_eq_mul] at hm
  have heq : (∫ ω, H ω ∂expSeqMeasure) - h = ∫ ω, (H ω - h) ∂expSeqMeasure := by
    rw [integral_sub hHi (integrable_const (h : ℝ)), integral_const, probReal_univ, one_smul]
  change |(∫ ω, H ω ∂expSeqMeasure) - h| ≤ _
  rw [heq]
  calc
    _ ≤ ∫ ω, |H ω - h| ∂expSeqMeasure := abs_integral_le_integral_abs
    _ ≤ expSeqMeasure.real Eᶜ * B := hm
    _ ≤ (63 / (n : ℝ) ^ 2) * (3 * Real.log n) :=
      mul_le_mul hbad hBY hB0 (by positivity)
    _ ≤ 200 * Real.log n / (n : ℝ) ^ 2 := by
      have hY0 : 0 ≤ Real.log n := by linarith
      have heq' : (63 / (n : ℝ) ^ 2) * (3 * Real.log n) =
          189 * Real.log n / (n : ℝ) ^ 2 := by ring
      rw [heq']
      gcongr
      norm_num

/-- `thm:KRE` (a), expectation on the actual sorted iid sample. -/
theorem K_RE_exact_integral {f : ℝ → ℝ} {fmin fmax Lf : ℝ}
    (hf : DensityK f 0 1 fmin fmax Lf)
    (hnc : ∃ x ∈ Set.Icc (0 : ℝ) 1, ∃ y ∈ Set.Icc (0 : ℝ) 1, f x ≠ f y) :
    ∃ K : ℝ, 0 < K ∧ ∀ {N : ℕ → ℕ} {ε : ℕ → ℝ},
      Tendsto (fun k => (N k : ℝ)) atTop atTop → Tendsto ε atTop atTop →
      Tendsto (fun k => Real.log (ε k) / Real.log (N k)) atTop (𝓝 0) →
      ∀ᶠ k in atTop, ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ),
        (∀ i, HasLaw (X i) (densityLaw f 0 1) P) → iIndepFun X P →
        KREOutside (kreZ (N k) (ε k)) (greW K (N k) (ε k)) →
        |∫ ω, (reHeight (ε k) (kKeys X (N k) ω) (N k) : ℝ) ∂P -
          kreExactHeight (kreZ (N k) (ε k))| ≤ 200 * Real.log (N k) / (N k : ℝ) ^ 2 := by
  obtain ⟨K, hK, h⟩ := K_RE_exact hf hnc
  refine ⟨K, hK, fun {N ε} hN hε hεN => ?_⟩
  have hL := Real.tendsto_log_atTop.comp hN
  filter_upwards [h hN hε hεN, hN.eventually_ge_atTop 16, hε.eventually_ge_atTop 1,
    hL.eventually_ge_atTop 1] with k hk hn he hY
  intro Ω _ P _ X hX hind hwin
  obtain ⟨E, hEm, hbad, hgood⟩ := hk
  rw [integral_reHeight_kKeys hf hX hind (ε k) (N k)]
  exact kre_integral_exact_of_event hf he (by exact_mod_cast hn) hY hEm hbad
    (fun ω hω => hgood ω hω hwin)

end
end PGM
