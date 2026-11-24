import PLAStochastic.Index.GEP.Kernel.Row.LargeTime
import PLAStochastic.Index.CEPS.Actual.KilledDecay

/-!
# Class-uniform killed decay with arbitrary drift

The killed Fourier gap is independent of the real translation `β`. Thus a fixed
drift window needs no near-critical slope estimate: the bounds below hold for
every `β` and both signs of the gap coefficient. The width `l` lies in `[w/2,2w]`.
All constants are fixed before the gap law, width, drift and starting point.
-/

namespace PGM

noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- A class constant paying the short-time survival bound and the shift by one. -/
def cepsBandDecayConst (D vlo vhi : ℝ) : ℝ :=
  1 + 3 * (1 + 4 * D) * Real.exp (krKappa D vlo vhi / 2)

/-- Uniform killed survival from the existing Fourier gap; the shift is arbitrary. -/
theorem cepsBand_survival_decay {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) (n : ℕ) (y : ℝ) :
    krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤
      cepsBandDecayConst D vlo vhi * w *
        Real.exp (-(krKappa D vlo vhi / (8 * w ^ 2)) * n) := by
  have hw0 : 0 < w := by linarith
  have hl1 : 1 ≤ l := by linarith
  have hl0 : 0 < l := by linarith
  have hκ := krKappa_pos hD hvlo hvhi
  have hc := killCnu_pos hD hvlo hvhi
  have hc1 : killCnu D vlo vhi ≤ 1 := by
    have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) 1
    simp only [one_pow, min_self, mul_one] at h
    linarith [sq_nonneg (‖charFun (ν : Measure ℝ) 1‖)]
  have hB : 1 ≤ cepsBandDecayConst D vlo vhi := by
    unfold cepsBandDecayConst
    have : 0 ≤ 3 * (1 + 4 * D) * Real.exp (krKappa D vlo vhi / 2) := by positivity
    linarith
  by_cases hn : n = 0
  · subst n
    simpa using (krSurv_le_one measurableSet_Icc ν β a 0 y).trans
      (show 1 ≤ cepsBandDecayConst D vlo vhi * w by nlinarith)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
  obtain ⟨f, hf, hf0, hfD, hνf⟩ := hν.kill_density_le hθ
  have hgap : ∀ t : ℝ, ‖(1 - (0 : ℂ)) * charFun (ν : Measure ℝ) t +
      0 * charFun (ν : Measure ℝ) t‖ ^ 2 ≤
      1 - killCnu D vlo vhi * min (t ^ 2) 1 := by
    intro t
    have h := kill_regLaw_charFun_gap hD hθ hvlo hν (a := 1) (by norm_num) t
    simp only [one_mul] at h
    simp only [sub_zero, one_mul, zero_mul, add_zero]
    linarith
  have hrow := norm_kRow_le_gap_exp (ν := (ν : Measure ℝ)) (σ := (ν : Measure ℝ))
    (α := 0) (β := β) (a := a) (a₀ := 1 / 2) hl1 hf hf0 hfD hνf
    (by norm_num) ha hc hc1 hgap (by norm_num : ‖(0 : ℂ)‖ ≤ 1 / 3)
    (φ := fun _ => (1 : ℂ)) measurable_const (fun _ => by simp) hn1 y
  simp only [zero_add] at hrow
  have heq := congrFun (kRow_zero_eq_krRow (J := Icc 0 l) (β := β) (a := a)
    (ν : Measure ℝ) (ν : Measure ℝ) n (fun _ => 1)) y
  simp only [Complex.ofReal_one] at heq
  rw [heq] at hrow
  simp only [show D * l / (1 / 2) = 2 * D * l by ring,
    Complex.norm_real, Real.norm_eq_abs, norm_zero, zero_pow hn, add_zero] at hrow
  change |krSurv (Icc 0 l) (ν : Measure ℝ) β a n y| ≤
    3 * Real.sqrt (2 * D * l) *
      Real.exp (-(krKappa D vlo vhi * ((n : ℝ) - 1) / (2 * l ^ 2))) at hrow
  rw [abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a n y)] at hrow
  have hs : Real.sqrt (2 * D * l) ≤ (1 + 4 * D) * w := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · have hw1 : 1 ≤ w := by linarith
      have hww : w ≤ w ^ 2 := by nlinarith
      have hdl : 2 * D * l ≤ 4 * D * w := by nlinarith
      have hDw : 4 * D * w ≤ 4 * D * w ^ 2 := by nlinarith
      have he : ((1 + 4 * D) * w) ^ 2 = (1 + 8 * D + 16 * D ^ 2) * w ^ 2 := by ring
      rw [he]
      nlinarith [mul_nonneg (sq_nonneg D) (sq_nonneg w)]
  have hexp : -(krKappa D vlo vhi * ((n : ℝ) - 1) / (2 * l ^ 2)) ≤
      krKappa D vlo vhi / 2 - (krKappa D vlo vhi / (8 * w ^ 2)) * n := by
    have hl2 : 1 ≤ l ^ 2 := one_le_pow₀ hl1
    have hln : (n : ℝ) - 1 ≥ 0 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have hlsq : l ^ 2 ≤ 4 * w ^ 2 := by nlinarith
    have hrate : krKappa D vlo vhi / (8 * w ^ 2) ≤
        krKappa D vlo vhi / (2 * l ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    have hrhalf : krKappa D vlo vhi / (8 * w ^ 2) ≤ krKappa D vlo vhi / 2 := by
      apply div_le_div_of_nonneg_left hκ.le (by norm_num)
      nlinarith
    calc
      _ = -(krKappa D vlo vhi / (2 * l ^ 2) * ((n : ℝ) - 1)) := by ring
      _ ≤ -(krKappa D vlo vhi / (8 * w ^ 2) * ((n : ℝ) - 1)) :=
        neg_le_neg (mul_le_mul_of_nonneg_right hrate hln)
      _ = krKappa D vlo vhi / (8 * w ^ 2) -
          (krKappa D vlo vhi / (8 * w ^ 2)) * n := by ring
      _ ≤ _ := by linarith
  calc
    _ ≤ 3 * Real.sqrt (2 * D * l) *
        Real.exp (-(krKappa D vlo vhi * ((n : ℝ) - 1) / (2 * l ^ 2))) := hrow
    _ ≤ 3 * ((1 + 4 * D) * w) *
        Real.exp (krKappa D vlo vhi / 2 - (krKappa D vlo vhi / (8 * w ^ 2)) * n) := by
      gcongr
    _ ≤ _ := by
      rw [show krKappa D vlo vhi / 2 - (krKappa D vlo vhi / (8 * w ^ 2)) * n =
        krKappa D vlo vhi / 2 + (-(krKappa D vlo vhi / (8 * w ^ 2)) * n) by ring,
        Real.exp_add]
      unfold cepsBandDecayConst
      nlinarith [mul_nonneg hw0.le
        (Real.exp_pos (-(krKappa D vlo vhi / (8 * w ^ 2)) * n)).le]

/-- Complex discount may grow at a fixed fraction of the killed gap. -/
theorem cepsBand_discount_survival_decay {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (n : ℕ) (y : ℝ) :
    ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n y ≤
      cepsBandDecayConst D vlo vhi * w *
        Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * n) := by
  have h := cepsBand_survival_decay hD hθ hvlo hvhi hν hw hl hlw β ha n y
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]
  calc
    _ ≤ Real.exp ((krKappa D vlo vhi / (16 * w ^ 2)) * n) *
        (cepsBandDecayConst D vlo vhi * w *
          Real.exp (-(krKappa D vlo vhi / (8 * w ^ 2)) * n)) :=
      mul_le_mul (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])) h
        (krSurv_nonneg measurableSet_Icc ν β a n y) (Real.exp_pos _).le
    _ = _ := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 1
      congr 1
      ring

end
end PGM
