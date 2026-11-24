import PLAStochastic.Index.CEPS.Band.WidthDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-! # Polynomial width moduli for the actual survival and pin resolvents -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

theorem cepsBandFirstWidthConst_nonneg {D vlo vhi : ℝ} (hD : 0 < D)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) : 0 ≤ cepsBandFirstWidthConst D vlo vhi := by
  have hκ := krKappa_pos hD hvlo hvhi
  unfold cepsBandFirstWidthConst cepsBandMomentConst cepsBandPinDecayConst cepsBandDecayConst
  positivity

/-- A bounded derivative of the density gives the density modulus used throughout this chain. -/
theorem cepsBand_density_lipschitz_of_deriv {f : ℝ → ℝ} {K : ℝ≥0}
    (hf : Differentiable ℝ f) (hK : ∀ x, |deriv f x| ≤ K) : LipschitzWith K f := by
  apply lipschitzWith_of_nnnorm_deriv_le hf
  intro x
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact hK x

/-- A class polynomial controls the bandwidth modulus of the actual bottom resolvent. -/
theorem cepsBand_bottomSurv_lipschitz {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re) :
    LipschitzOnWith ⟨cepsBandFirstWidthConst D vlo vhi * w ^ 6,
      mul_nonneg (cepsBandFirstWidthConst_nonneg hD hvlo hvhi) (pow_nonneg (by linarith) _)⟩
      (cepsBottomSurv ν β a q) (Icc (w / 2) (2 * w)) := by
  apply (convex_Icc (w / 2) (2 * w)).lipschitzOnWith_of_nnnorm_deriv_le
  · intro l hl
    exact (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hl.1 hl.2 β ha hq).1.differentiableAt
  · intro l hl
    change ‖deriv (cepsBottomSurv ν β a q) l‖ ≤ cepsBandFirstWidthConst D vlo vhi * w ^ 6
    exact (cepsBand_bottomSurv_first_width hD hθ hvlo hvhi hν hf hLip hw hl.1 hl.2 β ha hq).2

theorem cepsBand_norm_discount (q : ℂ) (n : ℕ) :
    ‖Complex.exp (-q * n)‖ = Real.exp (-q.re * n) := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, sub_zero]

/-- At real discount the resolvent is the real nonnegative survival series. -/
theorem cepsBand_real_bottomSurv (ν : ProbabilityMeasure ℝ) (β a r l : ℝ) :
    cepsBottomSurv ν β a (r : ℂ) l =
      ((∑' n : ℕ, Real.exp (-r * n) * krSurv (Icc 0 l) (ν : Measure ℝ) β a n 0 : ℝ) : ℂ) := by
  unfold cepsBottomSurv
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  push_cast
  rfl

/-- A modulus for the absolute time sum of survival width increments follows by using the real
part of the discount. No cancellation between complex terms is used. -/
theorem cepsBand_survival_width_sum_le {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {K : ℝ≥0} (hLip : LipschitzWith K f) {w : ℝ} (hw : 4 ≤ w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (64 * w ^ 2)) ≤ q.re)
    {x y : ℝ} (hx : w / 2 ≤ x) (hxy : x ≤ y) (hy : y ≤ 2 * w) :
    Summable (fun n : ℕ => ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)) ∧
    (∑' n : ℕ, ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)) ≤
      cepsBandFirstWidthConst D vlo vhi * w ^ 6 * (y - x) := by
  have ha0 : a ≠ 0 := by intro h; simp only [h, abs_zero] at ha; linarith
  have hxy₀ : 0 ≤ x := by linarith
  have hq' : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re := by
    have hκ := krKappa_pos hD hvlo hvhi
    have hb : krKappa D vlo vhi / (64 * w ^ 2) ≤ krKappa D vlo vhi / (16 * w ^ 2) := by
      apply div_le_div_of_nonneg_left hκ.le (by positivity)
      nlinarith
    linarith
  have hsx := (cepsBand_survival_moments hD hθ hvlo hvhi hν (show 2 ≤ w by linarith)
    hx (hxy.trans hy) β ha hq' 0 0).1
  have hsy := (cepsBand_survival_moments hD hθ hvlo hvhi hν (show 2 ≤ w by linarith)
    (hx.trans hxy) hy β ha hq' 0 0).1
  simp only [pow_zero, one_mul] at hsx hsy
  have he : ∀ n : ℕ, ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) =
      ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 -
        ‖Complex.exp (-q * n)‖ * krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0 := fun _ => by ring
  have hs : Summable (fun n : ℕ => ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0)) := by
    simpa only [he] using hsy.sub hsx
  refine ⟨hs, ?_⟩
  have hsum0 : 0 ≤ ∑' n : ℕ, ‖Complex.exp (-q * n)‖ *
      (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) :=
    tsum_nonneg fun n => mul_nonneg (norm_nonneg _) (hf.cepsBand_survival_width_le ha0 β hxy₀ hxy n).1
  have hid : cepsBottomSurv ν β a (q.re : ℂ) y - cepsBottomSurv ν β a (q.re : ℂ) x =
      ((∑' n : ℕ, ‖Complex.exp (-q * n)‖ *
        (krSurv (Icc 0 y) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 x) (ν : Measure ℝ) β a n 0) : ℝ) : ℂ) := by
    rw [cepsBand_real_bottomSurv, cepsBand_real_bottomSurv]
    simp_rw [cepsBand_norm_discount] at hsx hsy ⊢
    rw [← Complex.ofReal_sub, ← hsy.tsum_sub hsx]
    congr 1
    exact tsum_congr fun _ => by ring
  have hb := (cepsBand_bottomSurv_lipschitz hD hθ hvlo hvhi hν hf hLip hw β ha
    (q := (q.re : ℂ)) (by simpa using hq)).dist_le_mul y ⟨hx.trans hxy, hy⟩ x ⟨hx, hxy.trans hy⟩
  rw [dist_eq_norm, hid, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum0,
    Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hb
  exact hb

end
end PGM
