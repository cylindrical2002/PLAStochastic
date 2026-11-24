import PLAStochastic.Index.CEPS.Band.WidthFinite

/-! # Width continuity and genuine first derivatives of the bottom survival resolvent -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

/-- The bottom survival resolvent has a polynomial bound at arbitrary translation. -/
theorem cepsBand_bottomSurv_le {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    ‖cepsBottomSurv ν β a q l‖ ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3 := by
  obtain ⟨hs, hb⟩ := cepsBand_survival_moments hD hθ hvlo hvhi hν hw hl hlw β ha hq 0 0
  have he : ∀ n : ℕ, ‖Complex.exp (-q * n) *
      (krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 : ℂ)‖ =
      ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a n 0)]
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] at hs hb
  unfold cepsBottomSurv
  exact (norm_tsum_le_tsum_norm (by simpa only [he] using hs)).trans (by simpa only [he] using hb)

/-- Reflection identifies the top survival series with bottom survival for the reverse walk. -/
theorem cepsBand_topSurv_eq_reverse (ν : ProbabilityMeasure ℝ) (β a : ℝ) (q : ℂ) (l : ℝ) :
    cepsTopSurv ν β a q l = cepsBottomSurv ν (-β) (-a) q l := by
  unfold cepsTopSurv cepsBottomSurv
  congr 1
  funext n
  rw [← krSurv_reflect ν l β a n l, sub_self]

/-- The full pointwise bridge resolvent has a polynomial bound at arbitrary translation. -/
theorem cepsBand_bridgeSeries_le {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    ‖cepsBridgeSeries ν f β a q l‖ ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) 0 * w ^ 3 := by
  obtain ⟨hs, hb⟩ := cepsBand_density_moments hD hθ hvlo hvhi hν hf hw hl hlw β ha hq 0 0 l
  have he : ∀ n : ℕ, ‖Complex.exp (-q * ((n : ℂ) + 1)) *
      (krDens (Icc 0 l) ν f β a (n + 1) 0 l : ℂ)‖ =
      ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * krDens (Icc 0 l) ν f β a (n + 1) 0 l := by
    intro n
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)]
  simp only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] at hs hb
  unfold cepsBridgeSeries
  exact (norm_tsum_le_tsum_norm (by simpa only [he] using hs)).trans (by simpa only [he] using hb)

/-- Uniformly convergent survival series are continuous in the bandwidth, even with growing
discount. No regularity of the density is required for this statement. -/
theorem cepsBand_bottomSurv_continuousOn {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w : ℝ} (hw : 2 ≤ w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    ContinuousOn (cepsBottomSurv ν β a q) (Icc (w / 2) (2 * w)) := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, abs_zero] at ha; linarith
  let r := krKappa D vlo vhi / (16 * w ^ 2)
  have hr : 0 < r := by dsimp [r]; exact div_pos (krKappa_pos hD hvlo hvhi) (by positivity)
  have hs : Summable (fun n : ℕ => cepsBandDecayConst D vlo vhi * w * Real.exp (-r * n)) := by
    simp_rw [mul_comm (-r), Real.exp_nat_mul]
    exact (summable_geometric_of_lt_one (Real.exp_pos (-r)).le
      (Real.exp_lt_one_iff.mpr (by linarith : -r < 0))).mul_left
        (cepsBandDecayConst D vlo vhi * w)
  unfold cepsBottomSurv
  apply continuousOn_tsum (u := fun n : ℕ =>
    cepsBandDecayConst D vlo vhi * w * Real.exp (-r * n)) ?_ hs ?_
  · intro n
    have hc := (hf.cepsBand_survival_lipschitz ha0 β n).continuousOn.mono
      (show Icc (w / 2) (2 * w) ⊆ Ici 0 from fun _ h => by simp only [mem_Ici]; linarith [h.1])
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)
  · intro n l hl
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a n 0)]
    exact cepsBand_discount_survival_decay hD hθ hvlo hvhi hν hw hl.1 hl.2 β ha hq n 0

/-- Width continuity of the pointwise bridge is derived from a Lipschitz density representative. -/
theorem cepsBand_bridgeSeries_continuousOn {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 2 ≤ w) (β : ℝ)
    {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) :
    ContinuousOn (cepsBridgeSeries ν f β a q) (Icc (w / 2) (2 * w)) := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, abs_zero] at ha; linarith
  let r := krKappa D vlo vhi / (16 * w ^ 2)
  have hr : 0 < r := by dsimp [r]; exact div_pos (krKappa_pos hD hvlo hvhi) (by positivity)
  have hs : Summable (fun n : ℕ => cepsBandPinDecayConst D vlo vhi * w * Real.exp (-r * n)) := by
    simp_rw [mul_comm (-r), Real.exp_nat_mul]
    exact (summable_geometric_of_lt_one (Real.exp_pos (-r)).le
      (Real.exp_lt_one_iff.mpr (by linarith : -r < 0))).mul_left
        (cepsBandPinDecayConst D vlo vhi * w)
  unfold cepsBridgeSeries
  apply continuousOn_tsum (u := fun n : ℕ =>
    cepsBandPinDecayConst D vlo vhi * w * Real.exp (-r * n)) ?_ hs ?_
  · intro n
    have hc := (hf.cepsBand_pin_lipschitz hLip ha0 β n).continuousOn.mono
      (show Icc (w / 2) (2 * w) ⊆ Ici 0 from fun _ h => by simp only [mem_Ici]; linarith [h.1])
    exact continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hc)
  · intro n l hl
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)]
    exact cepsBand_discount_density_decay hD hθ hvlo hvhi hν hf hw hl.1 hl.2 β ha hq n 0 l

end
end PGM
