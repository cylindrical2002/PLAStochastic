import PLAStochastic.Index.CEPS.Band.WidthLipschitz

/-! # A polynomial bandwidth modulus for the actual opposite-side Green pin -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

def cepsBandPinWidthConst (D vlo vhi K : ℝ) : ℝ :=
  Real.exp (krKappa D vlo vhi / 16) *
    (2 * D * cepsBandFirstWidthConst D vlo vhi +
      4 * K * cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0)

theorem cepsBandPinWidthConst_nonneg {D vlo vhi K : ℝ} (hD : 0 < D)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hK : 0 ≤ K) :
    0 ≤ cepsBandPinWidthConst D vlo vhi K := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hC := cepsBandFirstWidthConst_nonneg hD hvlo hvhi
  unfold cepsBandPinWidthConst cepsBandMomentConst cepsBandDecayConst
  positivity

/-- Absolute pin width increments, including the endpoint-motion contribution. -/
theorem cepsBand_pin_width_sum_le {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re)
    {x y : ℝ} (hx : w / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * w) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
      |krDens (Icc 0 y) ν f β a (n + 1) 0 y - krDens (Icc 0 x) ν f β a (n + 1) 0 x|) ∧
    (∑' n : ℕ, ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
      |krDens (Icc 0 y) ν f β a (n + 1) 0 y - krDens (Icc 0 x) ν f β a (n + 1) 0 x|) ≤
      cepsBandPinWidthConst D vlo vhi K * w ^ 6 * (y - x) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hw2 : 2 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hδ : 0 ≤ y - x := sub_nonneg.mpr hxy
  have habs : 0 < |a| := by linarith
  have ha0 : a ≠ 0 := abs_pos.mp habs
  have hq' : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  let E := Real.exp (krKappa D vlo vhi / 16)
  let S := fun n : ℕ => ‖Complex.exp (-q * n)‖ *
    krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0
  let T := fun n : ℕ => ‖Complex.exp (-q * n)‖ *
    (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)
  obtain ⟨hTs, hTb⟩ := cepsBand_survival_width_sum_le hD hθ hvlo hvhi hν hf hLip hw β ha hq hx hxy hy
  obtain ⟨hSs, hSb⟩ := cepsBand_survival_moments hD hθ hvlo hvhi hν hw2 hx
    (hxy.trans hy) β ha hq' 0 0
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] at hSs hSb
  have hnorm : ‖Complex.exp (-q)‖ ≤ E := by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp]
    have hb : krKappa D vlo vhi / (16 * w ^ 2) ≤ krKappa D vlo vhi / 16 := by
      apply div_le_div_of_nonneg_left hκ.le (by norm_num)
      nlinarith
    linarith
  have hdiv : D / |a| ≤ 2 * D := by rw [div_le_iff₀ habs]; nlinarith
  have hdivK : (K : ℝ) / |a| ^ 2 ≤ 4 * K := by
    rw [div_le_iff₀ (sq_pos_of_pos habs)]
    have hsq : 1 / 4 ≤ |a| ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left hsq K.coe_nonneg
    nlinarith
  let F := fun n : ℕ => ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
    |krDens (Icc 0 y) ν f β a (n + 1) 0 y - krDens (Icc 0 x) ν f β a (n + 1) 0 x|
  have hpoint : ∀ n, F n ≤ E * (2 * D * T n + 4 * K * (y - x) * S n) := by
    intro n
    have hdiff := hf.cepsBand_pin_width_le hLip ha0 β hx0 hxy n
    have hdiff' : |krDens (Icc 0 y) ν f β a (n + 1) 0 y -
        krDens (Icc 0 x) ν f β a (n + 1) 0 x| ≤
        2 * D * (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 -
          krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) +
          4 * K * (y - x) * krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0 :=
      hdiff.trans (add_le_add (mul_le_mul_of_nonneg_right hdiv
        (hf.cepsBand_survival_width_le ha0 β hx0 hxy n).1)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdivK hδ)
          (krSurv_nonneg measurableSet_Icc ν β a n 0)))
    have hweight : ‖Complex.exp (-q * ((n : ℂ) + 1))‖ ≤ E * ‖Complex.exp (-q * n)‖ := by
      rw [show -q * ((n : ℂ) + 1) = -q + (-q * n) by ring, Complex.exp_add, norm_mul]
      exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
    exact (mul_le_mul hweight hdiff' (abs_nonneg _) (by positivity)).trans_eq (by dsimp [S, T]; ring)
  have hmajor : Summable (fun n => E * (2 * D * T n + 4 * K * (y - x) * S n)) :=
    ((hTs.mul_left (2 * D)).add (hSs.mul_left (4 * K * (y - x)))).mul_left E
  have hFs : Summable F := hmajor.of_nonneg_of_le (fun _ => by dsimp [F]; positivity) hpoint
  refine ⟨hFs, ?_⟩
  calc
    _ ≤ ∑' n, E * (2 * D * T n + 4 * K * (y - x) * S n) := hFs.tsum_le_tsum hpoint hmajor
    _ = E * (2 * D * ∑' n, T n + 4 * K * (y - x) * ∑' n, S n) := by
      rw [tsum_mul_left, (hTs.mul_left (2 * D)).tsum_add (hSs.mul_left (4 * K * (y - x))),
        tsum_mul_left, tsum_mul_left]
    _ ≤ E * (2 * D * (cepsBandFirstWidthConst D vlo vhi * w ^ 6 * (y - x)) +
        4 * K * (y - x) * (cepsBandMomentConst (cepsBandDecayConst D vlo vhi)
          (krKappa D vlo vhi) 0 * w ^ 3)) := by
      gcongr
    _ ≤ E * (2 * D * (cepsBandFirstWidthConst D vlo vhi * w ^ 6 * (y - x)) +
        4 * K * (y - x) * (cepsBandMomentConst (cepsBandDecayConst D vlo vhi)
          (krKappa D vlo vhi) 0 * w ^ 6)) := by
      have hp : w ^ 3 ≤ w ^ 6 := pow_le_pow_right₀ hw1 (by norm_num)
      have hC : 0 ≤ cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 := by
        unfold cepsBandMomentConst cepsBandDecayConst
        positivity
      have hcoef : 0 ≤ 4 * (K : ℝ) * (y - x) := mul_nonneg (by positivity) hδ
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp hC) hcoef))
        (Real.exp_pos _).le
    _ = _ := by unfold cepsBandPinWidthConst; dsimp [E]; ring

/-- The actual pin resolvent is Lipschitz with a polynomial, uniform bandwidth budget. -/
theorem cepsBand_bridgeSeries_lipschitz {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    LipschitzOnWith ⟨cepsBandPinWidthConst D vlo vhi K * w ^ 6,
      mul_nonneg (cepsBandPinWidthConst_nonneg hD hvlo hvhi K.coe_nonneg) (pow_nonneg (by linarith) _)⟩
      (cepsBridgeSeries ν f β a q) (Icc (w / 2) (2 * w)) := by
  have hκ := krKappa_pos hD hvlo hvhi
  have hq' : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re := by
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have hb : ∀ {x y}, w / 2 ≤ x → x ≤ y → y ≤ 2 * w →
      ‖cepsBridgeSeries ν f β a q y - cepsBridgeSeries ν f β a q x‖ ≤
        cepsBandPinWidthConst D vlo vhi K * w ^ 6 * (y - x) := by
    intro x y hx hxy hy
    obtain ⟨hs, hsum⟩ := cepsBand_pin_width_sum_le hD hθ hvlo hvhi hν hf hLip hw β ha hq hx hxy hy
    have hx' := (cepsBand_summable_density_norm hD hθ hvlo hvhi hν hf (show 2 ≤ w by linarith)
      hx (hxy.trans hy) β ha hq' 0 x).of_norm
    have hy' := (cepsBand_summable_density_norm hD hθ hvlo hvhi hν hf (show 2 ≤ w by linarith)
      (hx.trans hxy) hy β ha hq' 0 y).of_norm
    have he : ∀ n : ℕ, ‖Complex.exp (-q * ((n : ℂ) + 1)) *
        (krDens (Icc 0 y) ν f β a (n + 1) 0 y : ℂ) -
        Complex.exp (-q * ((n : ℂ) + 1)) * (krDens (Icc 0 x) ν f β a (n + 1) 0 x : ℂ)‖ =
        ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
          |krDens (Icc 0 y) ν f β a (n + 1) 0 y - krDens (Icc 0 x) ν f β a (n + 1) 0 x| := by
      intro n
      rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    unfold cepsBridgeSeries
    rw [← hy'.tsum_sub hx']
    exact (norm_tsum_le_tsum_norm (by simpa only [he] using hs)).trans (by simpa only [he] using hsum)
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  change dist (cepsBridgeSeries ν f β a q x) (cepsBridgeSeries ν f β a q y) ≤
    cepsBandPinWidthConst D vlo vhi K * w ^ 6 * dist x y
  rcases le_total y x with h | h
  · simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)] using hb hy.1 h hx.2
  · rw [dist_comm, dist_comm x y]
    simpa only [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr h)] using hb hx.1 h hy.2

end
end PGM
