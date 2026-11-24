import PLAStochastic.Index.CEPS.BandDisc.Block

/-! # A nonvanishing entrance in a diffusive small-discount disc

This proves the small-discount part of the original right-half-plane target.
The relative time moment, rather than an absolute moment of size `w⁵`, pays the
radius `a₀/w²`. No extension to negative real parts is asserted here.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

lemma cepsBandDisc_norm_exp_sub_one_le {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_hx : x ∈ {z : ℂ | z.re ≤ 0}) =>
      (Complex.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x (hx : x ∈ {z : ℂ | z.re ≤ 0}) => by
      rw [Complex.norm_exp]
      exact Real.exp_le_one_iff.mpr hx)
    (convex_halfSpace_re_le 0) (show (0 : ℂ) ∈ {z : ℂ | z.re ≤ 0} by simp)
    hz
  simpa using h

/-- The relative time budget controls the distance to the positive zero-discount value. -/
theorem cepsBandDisc_entrance_sub_zero_le {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n))
    {q : ℂ} (hq : 0 ≤ q.re) :
    ‖(∑' n : ℕ, Complex.exp (-q * n) * (s n : ℂ)) -
      ((∑' n : ℕ, s n : ℝ) : ℂ)‖ ≤
      ‖q‖ * ∑' n : ℕ, (n + 1 : ℝ) * s n := by
  have he : ∀ n : ℕ, ‖Complex.exp (-q * n) * (s n : ℂ)‖ ≤ s n := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs0 n)]
    apply mul_le_of_le_one_left (hs0 n)
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im, mul_zero, sub_zero]
    simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hq (Nat.cast_nonneg n))
  have hsq : Summable (fun n : ℕ => Complex.exp (-q * n) * (s n : ℂ)) :=
    Summable.of_norm_bounded hs he
  have hsr : Summable (fun n : ℕ => (s n : ℂ)) := Complex.summable_ofReal.mpr hs
  have hp : ∀ n : ℕ, ‖Complex.exp (-q * n) * (s n : ℂ) - (s n : ℂ)‖ ≤
      ‖q‖ * ((n + 1 : ℝ) * s n) := by
    intro n
    rw [← sub_one_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hs0 n)]
    have hz : (-q * (n : ℂ)).re ≤ 0 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
        Complex.natCast_im, mul_zero, sub_zero]
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg hq (Nat.cast_nonneg n))
    calc _ ≤ ‖-q * (n : ℂ)‖ * s n :=
        mul_le_mul_of_nonneg_right (cepsBandDisc_norm_exp_sub_one_le hz) (hs0 n)
      _ ≤ ‖q‖ * ((n + 1 : ℝ) * s n) := by
        rw [norm_mul, norm_neg, Complex.norm_natCast]
        have hn : (n : ℝ) ≤ n + 1 := by linarith
        nlinarith [mul_nonneg (norm_nonneg q) (hs0 n)]
  rw [Complex.ofReal_tsum, ← hsq.tsum_sub hsr]
  have hss := (hs1.mul_left ‖q‖).of_nonneg_of_le (fun _ => norm_nonneg _) hp
  exact (norm_tsum_le_tsum_norm hss).trans
    ((hss.tsum_le_tsum hp (hs1.mul_left ‖q‖)).trans_eq tsum_mul_left)

/-- The small-discount entrance is bounded below by one-half of its mass at zero. -/
theorem cepsBandDisc_entrance_small_lower {s : ℕ → ℝ} (hs0 : ∀ n, 0 ≤ s n)
    (hs : Summable s) (hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n))
    (hzero : s 0 = 1) {N : ℕ} (hN : 0 < N)
    (hblock : ∀ n, s (n + N) ≤ (1 / 2) * s n)
    {q : ℂ} (hq : 0 ≤ q.re) (hqN : 4 * (N : ℝ) * ‖q‖ ≤ 1) :
    1 / 2 ≤ ‖∑' n : ℕ, Complex.exp (-q * n) * (s n : ℂ)‖ := by
  let M : ℝ := ∑' n : ℕ, s n
  let H : ℂ := ∑' n : ℕ, Complex.exp (-q * n) * (s n : ℂ)
  have hM : 1 ≤ M := by
    rw [← hzero]
    exact hs.le_tsum 0 (fun n _ => hs0 n)
  have hJ := cepsBandDisc_relative_time_moment hs0 hs hs1 hN hblock
  have hdiff : ‖H - (M : ℂ)‖ ≤ M / 2 := by
    calc _ ≤ ‖q‖ * ∑' n : ℕ, (n + 1 : ℝ) * s n :=
        cepsBandDisc_entrance_sub_zero_le hs0 hs hs1 hq
      _ ≤ ‖q‖ * (2 * (N : ℝ) * M) := mul_le_mul_of_nonneg_left hJ (norm_nonneg _)
      _ ≤ M / 2 := by nlinarith [mul_le_mul_of_nonneg_right hqN (show 0 ≤ M by linarith)]
  have hnorm : ‖(M : ℂ)‖ = M := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have htri := norm_le_norm_add_norm_sub H (M : ℂ)
  rw [hnorm] at htri
  dsimp [H] at htri hdiff
  linarith

/-- A class-uniform diffusive disc gives the genuine actual entrance lower bound.
Both boundary starts (and every other start in the band) are covered. -/
theorem cepsBandDisc_survival_small_lower {D θ vlo vhi : ℝ}
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ w : ℝ, 2 ≤ w → ∀ l : ℝ, w / 2 ≤ l → l ≤ 2 * w →
        ∀ β a : ℝ, 1 / 2 ≤ |a| → ∀ y : ℝ, y ∈ Icc 0 l → ∀ q : ℂ,
          0 ≤ q.re → ‖q‖ ≤ a₀ / w ^ 2 →
            1 / 2 ≤ ‖∑' n : ℕ, Complex.exp (-q * n) *
              (krSurv (Icc 0 l) (ν : Measure ℝ) β a n y : ℂ)‖ := by
  obtain ⟨C, hC, hblock⟩ := cepsBandDisc_uniform_block hD hθ hvlo hvhi
  refine ⟨1 / (4 * C), by positivity, ?_⟩
  intro ν hν w hw l hl hlw β a ha y hy q hq hqnorm
  obtain ⟨N, hN, hNC, hb⟩ := hblock ν hν w hw
  let s : ℕ → ℝ := fun n => krSurv (Icc 0 l) (ν : Measure ℝ) β a n y
  have hs0 : ∀ n, 0 ≤ s n := fun n => krSurv_nonneg measurableSet_Icc ν β a n y
  have hq0 : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ (0 : ℂ).re := by
    simp only [Complex.zero_re]
    exact neg_nonpos.mpr (div_nonneg (krKappa_pos hD hvlo hvhi).le (by positivity))
  have hs : Summable s := by
    simpa [s] using (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha hq0 0 y).1
  have hs1 : Summable (fun n : ℕ => (n + 1 : ℝ) * s n) := by
    simpa [s] using (cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha hq0 1 y).1
  have hzero : s 0 = 1 := by
    simp [s, krSurv, krRow_zero, hy]
  have hstep : ∀ n, s (n + N) ≤ (1 / 2) * s n := fun n =>
    krSurv_add_le ν (hb l hl hlw β a ha) n y
  have hw2 : 0 < w ^ 2 := sq_pos_of_pos (by linarith)
  have hmul : ‖q‖ * w ^ 2 ≤ 1 / (4 * C) := (le_div_iff₀ hw2).mp hqnorm
  have hqN : 4 * (N : ℝ) * ‖q‖ ≤ 1 := by
    have hcq : 4 * C * (‖q‖ * w ^ 2) ≤ 1 := by
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hmul
    have hnq := mul_le_mul_of_nonneg_right hNC (norm_nonneg q)
    nlinarith
  exact cepsBandDisc_entrance_small_lower hs0 hs hs1 hzero hN hstep hq hqN

end
end PGM
