import PLAStochastic.Index.CEPS.BandDisc.LowerSmall

/-! # The exit-atom lower bound for a survival generating function

The global estimate uses `|1-z|` with `|z|≤1`; the linear bound in `|q|`
is then proved only on the small disc `|q|≤1/2`, with `z=exp(-q)`.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Finset

/-- Absolute convergence of a survival generating function on the closed unit disc. -/
lemma cepsBandDisc_summable_generating {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ => z ^ n * (s n : ℂ)) := by
  apply Summable.of_norm_bounded hs
  intro n
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 n)]
  exact mul_le_of_le_one_left (hs0 n) (pow_le_one₀ (norm_nonneg z) hz)

/-- The survival-to-exit telescoping identity, including the entire boundary `|z|=1`. -/
theorem cepsBandDisc_generating_telescope {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hmono : ∀ n, s (n + 1) ≤ s n) (hzero : s 0 = 1)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (1 - z) * (∑' n : ℕ, z ^ n * (s n : ℂ)) =
      ∑' n : ℕ, ((s n - s (n + 1) : ℝ) : ℂ) * (1 - z ^ (n + 1)) := by
  let d : ℕ → ℝ := fun n => s n - s (n + 1)
  have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hmono n)
  have hshift := (summable_nat_add_iff 1).2 hs
  have hd : Summable d := hs.sub hshift
  have hmass : (∑' n : ℕ, d n) = 1 := by
    change (∑' n : ℕ, (s n - s (n + 1))) = 1
    rw [hs.tsum_sub hshift]
    have h := hs.sum_add_tsum_nat_add 1
    simp only [sum_range_one, hzero] at h
    linarith
  have hsz := cepsBandDisc_summable_generating hs0 hs hz
  have hdz := cepsBandDisc_summable_generating hd0 hd hz
  have hszshift : Summable (fun n : ℕ => z ^ (n + 1) * (s (n + 1) : ℂ)) :=
    (summable_nat_add_iff 1).2 hsz
  have hdz1 : Summable (fun n : ℕ => z ^ (n + 1) * (d n : ℂ)) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdz.mul_left z
  have hdiff : (∑' n : ℕ, z ^ (n + 1) * (d n : ℂ)) =
      1 - (1 - z) * ∑' n : ℕ, z ^ n * (s n : ℂ) := by
    have hleft : (∑' n : ℕ, z ^ (n + 1) * (s n : ℂ)) =
        z * ∑' n : ℕ, z ^ n * (s n : ℂ) := by
      simp only [pow_succ, mul_left_comm, mul_comm, tsum_mul_left]
    have hright : (∑' n : ℕ, z ^ (n + 1) * (s (n + 1) : ℂ)) =
        (∑' n : ℕ, z ^ n * (s n : ℂ)) - 1 := by
      have h := hsz.sum_add_tsum_nat_add 1
      simp only [sum_range_one, pow_zero, one_mul, hzero, Complex.ofReal_one] at h
      linear_combination h
    simp only [d, Complex.ofReal_sub, mul_sub]
    have hsz1 : Summable (fun n : ℕ => z ^ (n + 1) * (s n : ℂ)) := by
      simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hsz.mul_left z
    rw [hsz1.tsum_sub hszshift, hleft, hright]
    ring
  calc
    _ = 1 - (∑' n : ℕ, z ^ (n + 1) * (d n : ℂ)) := by rw [hdiff]; ring
    _ = ∑' n : ℕ, ((d n : ℂ) - z ^ (n + 1) * (d n : ℂ)) := by
      rw [Complex.summable_ofReal.mpr hd |>.tsum_sub hdz1, ← Complex.ofReal_tsum, hmass]
      simp
    _ = _ := by
      apply tsum_congr
      intro n
      dsimp [d]
      ring

/-- A positive first exit atom rules out a zero on the closed unit disc away from `z=1`.
The bound is globally periodic after substitution `z=exp(-q)`. -/
theorem cepsBandDisc_generating_atom_lower {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hmono : ∀ n, s (n + 1) ≤ s n) (hzero : s 0 = 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 - s 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    (p / 2) * ‖1 - z‖ ≤ ‖∑' n : ℕ, z ^ n * (s n : ℂ)‖ := by
  let d : ℕ → ℝ := fun n => s n - s (n + 1)
  let H : ℂ := ∑' n : ℕ, z ^ n * (s n : ℂ)
  have hd0 : ∀ n, 0 ≤ d n := fun n => sub_nonneg.mpr (hmono n)
  have hd : Summable d := hs.sub ((summable_nat_add_iff 1).2 hs)
  have hdz := cepsBandDisc_summable_generating hd0 hd hz
  have hdz1 : Summable (fun n : ℕ => (d n : ℂ) * z ^ (n + 1)) := by
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdz.mul_left z
  have he : Summable (fun n : ℕ => (d n : ℂ) * (1 - z ^ (n + 1))) := by
    simpa only [mul_sub, mul_one] using (Complex.summable_ofReal.mpr hd).sub hdz1
  have hR : Summable (fun n : ℕ => d n * (1 - (z ^ (n + 1)).re)) := by
    simpa [Complex.mul_re] using Complex.reCLM.summable he
  have hR0 : ∀ n, 0 ≤ d n * (1 - (z ^ (n + 1)).re) := by
    intro n
    apply mul_nonneg (hd0 n)
    have hb : (z ^ (n + 1)).re ≤ 1 :=
      (Complex.re_le_norm _).trans (by simpa using pow_le_one₀ (norm_nonneg z) hz)
    linarith
  have hRe : p * (1 - z.re) ≤ ((1 - z) * H).re := by
    have hzRe : z.re ≤ 1 := (Complex.re_le_norm z).trans hz
    calc
      _ ≤ d 0 * (1 - z.re) := by
        dsimp [d]
        rw [hzero]
        exact mul_le_mul_of_nonneg_right hp1 (by linarith)
      _ ≤ ∑' n : ℕ, d n * (1 - (z ^ (n + 1)).re) := by
        simpa using hR.le_tsum 0 (fun n _ => hR0 n)
      _ = ((1 - z) * H).re := by
        rw [cepsBandDisc_generating_telescope hs0 hs hmono hzero hz]
        symm
        simpa [Complex.mul_re, d] using Complex.reCLM.map_tsum he
  have hnormsq : ‖1 - z‖ ^ 2 ≤ 2 * (1 - z.re) := by
    have hzsq : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hzsq ⊢
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im] at *
    nlinarith
  have hh : (p / 2) * ‖1 - z‖ ^ 2 ≤ ‖1 - z‖ * ‖H‖ := by
    calc _ ≤ p * (1 - z.re) := by nlinarith [mul_le_mul_of_nonneg_left hnormsq hp]
      _ ≤ ((1 - z) * H).re := hRe
      _ ≤ ‖(1 - z) * H‖ := Complex.re_le_norm _
      _ = _ := norm_mul _ _
  by_cases hn : ‖1 - z‖ = 0
  · rw [hn, mul_zero]
    exact norm_nonneg _
  · have hn0 : 0 < ‖1 - z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
    dsimp [H] at hh
    nlinarith

lemma cepsBandDisc_norm_exp_sub_one_lower {q : ℂ} (hq : ‖q‖ ≤ 1 / 2) :
    ‖q‖ / 2 ≤ ‖1 - Complex.exp (-q)‖ := by
  have hb := Complex.norm_exp_sub_one_sub_id_le (x := -q) (by simpa using hq.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  simp only [norm_neg, sub_neg_eq_add] at hb
  have ht := norm_sub_le (Complex.exp (-q) - 1 + q) (Complex.exp (-q) - 1)
  rw [show Complex.exp (-q) - 1 + q - (Complex.exp (-q) - 1) = q by ring] at ht
  rw [norm_sub_rev] at ht
  nlinarith [norm_nonneg q]

/-- The linear-in-discount estimate is local; no unbounded-half-plane claim is made. -/
theorem cepsBandDisc_discount_atom_lower {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hmono : ∀ n, s (n + 1) ≤ s n) (hzero : s 0 = 1)
    {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1 - s 1) {q : ℂ}
    (hqr : 0 ≤ q.re) (hq : ‖q‖ ≤ 1 / 2) :
    (p / 4) * ‖q‖ ≤ ‖∑' n : ℕ, Complex.exp (-q * n) * (s n : ℂ)‖ := by
  have hz : ‖Complex.exp (-q)‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hqr)
  have h := cepsBandDisc_generating_atom_lower hs0 hs hmono hzero hp hp1 hz
  have he : ∀ n : ℕ, Complex.exp (-q) ^ n = Complex.exp (-q * n) := by
    intro n
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [he] at h
  have hl := cepsBandDisc_norm_exp_sub_one_lower hq
  nlinarith [mul_le_mul_of_nonneg_left hl hp]

end
end PGM
