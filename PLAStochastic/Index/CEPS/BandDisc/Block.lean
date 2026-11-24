import PLAStochastic.Index.CEPS.BandDisc.Actual

/-!
# Uniform diffusive block contraction and relative entrance time budgets

Free-sum density bounds give a common contraction block of length `O(w²)`.
This removes the extra width amplitude in the coarse Fourier survival budget
when a sharp time scale is required for the small-discount entrance argument.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset

lemma cepsBandDisc_survival_le_free_density {ν : ProbabilityMeasure ℝ}
    {f : ℝ → ℝ} {D : ℝ} (hf : CepsGapDensity ν f D) {l : ℝ} (hl : 0 ≤ l)
    (β : ℝ) {a L : ℝ} (ha : a ≠ 0) (hL : 0 ≤ L) {n : ℕ}
    (hfree : LocBd L (convPow (ν : Measure ℝ) n)) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) β a (n + 1) y ≤ L / |a| * l := by
  have hfin : volume (Icc 0 l) ≠ ⊤ := by simp
  have hint := kr_integrable_krDens_right ν measurableSet_Icc hfin
    hf.measurable hf.nonneg hf.le (β := β) (a := a) (n + 1) y
  have hc : Integrable ((Icc 0 l).indicator (fun _ : ℝ => L / |a|)) := by
    rw [integrable_indicator_iff measurableSet_Icc]
    exact integrableOn_const hfin
  rw [← integral_krDens ν measurableSet_Icc hfin hf.measurable hf.nonneg hf.le hf.eq ha n y]
  calc
    _ ≤ ∫ z, (Icc 0 l).indicator (fun _ : ℝ => L / |a|) z := by
      apply integral_mono hint hc
      intro z
      by_cases hz : z ∈ Icc 0 l
      · rw [indicator_of_mem hz]
        exact krDens_le_of_locBd ν hL measurableSet_Icc hf.measurable hf.nonneg hf.le
          hf.eq ha hfree y z
      · dsimp only
        rw [krDens_eq_zero_of_right_notMem ν (f := f) (β := β) (a := a) hz (n + 1) y, indicator_of_notMem hz]
    _ = L / |a| * l := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const]
      simp [hl, smul_eq_mul, mul_comm]

/-- The constant is chosen before the gap law, drift and width. -/
theorem cepsBandDisc_uniform_block {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w : ℝ, 2 ≤ w → ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ C * w ^ 2 ∧
        ∀ l : ℝ, w / 2 ≤ l → l ≤ 2 * w → ∀ β a : ℝ, 1 / 2 ≤ |a| →
          ∀ y : ℝ, krSurv (Icc 0 l) (ν : Measure ℝ) β a N y ≤ 1 / 2 := by
  obtain ⟨L, hL, hfree⟩ := kr_free_sum_density D θ vlo vhi hD hθ hvlo hvhi
  refine ⟨64 * L ^ 2 + 4, by positivity, ?_⟩
  intro ν hν w hw
  let n : ℕ := ⌈(8 * L * w) ^ 2⌉₊ + 2
  refine ⟨n + 1, by omega, ?_, ?_⟩
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ (8 * L * w) ^ 2 by positivity)
    have hw2 : 1 ≤ w ^ 2 := by nlinarith
    dsimp [n]
    push_cast
    nlinarith
  · intro l hl hlw β a ha y
    have ha0 : a ≠ 0 := by intro he; simp only [he, abs_zero] at ha; linarith
    have hn : 2 ≤ n := by dsimp [n]; omega
    have hs : 8 * L * w ≤ Real.sqrt n := by
      apply Real.le_sqrt_of_sq_le
      have hc := Nat.le_ceil ((8 * L * w) ^ 2)
      dsimp [n]
      push_cast
      linarith
    have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    have hbound := cepsBandDisc_survival_le_free_density
      (hν.exists_cepsGapDensity hθ.le).choose_spec (by linarith : 0 ≤ l) β ha0
      (show 0 ≤ L / Real.sqrt n by positivity) (hfree ν hν n hn) y
    refine hbound.trans ?_
    rw [show L / Real.sqrt n / |a| * l = (L * l) / (Real.sqrt n * |a|) by ring]
    apply (div_le_iff₀ (mul_pos hs0 (abs_pos.mpr ha0))).mpr
    have hsL : 4 * L * w ≤ Real.sqrt n * |a| := by
      calc 4 * L * w = (8 * L * w) * (1 / 2) := by ring
        _ ≤ Real.sqrt n * |a| := mul_le_mul hs ha (by norm_num) hs0.le
    nlinarith

/-- A one-half contraction every `N` steps bounds the first moment relative to the total
entrance mass. No lower bound on that mass is used in the time estimate. -/
theorem cepsBandDisc_relative_time_moment {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n))
    {N : ℕ} (_hN : 0 < N) (hblock : ∀ n, s (n + N) ≤ (1 / 2) * s n) :
    (∑' n : ℕ, (n + 1 : ℝ) * s n) ≤ 2 * (N : ℝ) * ∑' n : ℕ, s n := by
  let M := ∑' n : ℕ, s n
  let J := ∑' n : ℕ, (n + 1 : ℝ) * s n
  have ht0 : Summable (fun n => s (n + N)) := (summable_nat_add_iff N).2 hs
  have ht1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s (n + N)) :=
    (hs1.mul_left (1 / 2)).of_nonneg_of_le (fun n => mul_nonneg (by positivity) (hs0 _))
      (fun n => by simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left (hblock n) (by positivity : 0 ≤ (n + 1 : ℝ)))
  have htail : (∑' n : ℕ, (n + 1 : ℝ) * s (n + N)) ≤ (1 / 2) * J := by
    calc _ ≤ ∑' n : ℕ, (1 / 2) * ((n + 1 : ℝ) * s n) :=
        ht1.tsum_le_tsum (fun n => by
          simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left (hblock n)
            (by positivity : 0 ≤ (n + 1 : ℝ))) (hs1.mul_left (1 / 2))
      _ = _ := tsum_mul_left
  have hprefix : (∑ n ∈ range N, (n + 1 : ℝ) * s n) ≤
      (N : ℝ) * ∑ n ∈ range N, s n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn' : n + 1 ≤ N := by simpa using mem_range.mp hn
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn') (hs0 n)
  have hsplit : J = (∑ n ∈ range N, (n + 1 : ℝ) * s n) +
      (∑' n : ℕ, (n + 1 : ℝ) * s (n + N)) + (N : ℝ) * ∑' n : ℕ, s (n + N) := by
    dsimp only [J]
    rw [← hs1.sum_add_tsum_nat_add N]
    simp only [Nat.cast_add]
    rw [show (fun n : ℕ => ((n : ℝ) + N + 1) * s (n + N)) =
      (fun n : ℕ => (n + 1 : ℝ) * s (n + N) + (N : ℝ) * s (n + N)) by
        funext n; ring, ht1.tsum_add (ht0.mul_left (N : ℝ)), tsum_mul_left]
    ring
  have hineq : J ≤ (N : ℝ) * M + (1 / 2) * J := by
    calc J = _ := hsplit
      _ ≤ (N : ℝ) * (∑ n ∈ range N, s n) + (1 / 2) * J +
        (N : ℝ) * ∑' n : ℕ, s (n + N) := by gcongr
      _ = (N : ℝ) * M + (1 / 2) * J := by
        dsimp [M]
        rw [← hs.sum_add_tsum_nat_add N]
        ring
  dsimp [J, M] at hineq
  linarith

end
end PGM
