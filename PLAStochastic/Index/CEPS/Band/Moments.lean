import PLAStochastic.Index.CEPS.Band.Decay
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.PolynomialExponentialSeries

/-!
# Polynomial killed-band time budgets with complex discount

These are quantitative bounds on the actual absolutely convergent series.
The degree `2*j+3` is deliberately coarse and uniform in all drift translations.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

/-- The constant for a moment budget with decay amplitude `B` and killed gap `κ`. -/
def cepsBandMomentConst (B κ : ℝ) (j : ℕ) : ℝ :=
  B * (j.factorial : ℝ) * Real.exp 1 * (1 + 32 / κ) ^ (j + 1)

/-- A killed-scale exponential envelope gives an explicit polynomial time budget. -/
theorem cepsBand_moment_budget {F : ℕ → ℝ} {B κ w : ℝ}
    (hF : ∀ n, 0 ≤ F n) (hB : 0 ≤ B) (hκ : 0 < κ) (hw : 1 ≤ w)
    (hbound : ∀ n, F n ≤ B * w * Real.exp (-(κ / (16 * w ^ 2)) * n)) (j : ℕ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * F n) ∧
      (∑' n : ℕ, (n + 1 : ℝ) ^ j * F n) ≤
        cepsBandMomentConst B κ j * w ^ (2 * j + 3) := by
  let r := κ / (16 * w ^ 2)
  have hr : 0 < r := by dsimp [r]; positivity
  let C := (j.factorial : ℝ) * Real.exp 1 * (1 + 2 / r) ^ j
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hgeom : Summable (fun n : ℕ => Real.exp (-(r / 2) * n)) := by
    simp_rw [mul_comm (-(r / 2)), Real.exp_nat_mul]
    exact summable_geometric_of_norm_lt_one (by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith))
  have hmajor : Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * Real.exp (-r * n)) :=
    (hgeom.mul_left C).of_nonneg_of_le (fun _ => by positivity)
      (Real.polynomial_mul_exp_neg_le hr j)
  have hpoint : ∀ n : ℕ, (n + 1 : ℝ) ^ j * F n ≤
      B * w * ((n + 1 : ℝ) ^ j * Real.exp (-r * n)) := by
    intro n
    exact (mul_le_mul_of_nonneg_left (hbound n) (by positivity)).trans_eq (by ring)
  have hs := (hmajor.mul_left (B * w)).of_nonneg_of_le
    (fun n => mul_nonneg (by positivity) (hF n)) hpoint
  refine ⟨hs, ?_⟩
  have hbase : 1 + 2 / r ≤ (1 + 32 / κ) * w ^ 2 := by
    have he : 2 / r = (32 / κ) * w ^ 2 := by dsimp [r]; field_simp; ring
    rw [he]
    nlinarith [one_le_pow₀ (n := 2) hw]
  calc
    _ ≤ ∑' n : ℕ, B * w * ((n + 1 : ℝ) ^ j * Real.exp (-r * n)) :=
      hs.tsum_le_tsum hpoint (hmajor.mul_left (B * w))
    _ = B * w * ∑' n : ℕ, (n + 1 : ℝ) ^ j * Real.exp (-r * n) := tsum_mul_left
    _ ≤ B * w * ((j.factorial : ℝ) * Real.exp 1 * (1 + 2 / r) ^ (j + 1)) :=
      mul_le_mul_of_nonneg_left (Real.tsum_polynomial_mul_exp_neg_le hr j) (by positivity)
    _ ≤ B * w * ((j.factorial : ℝ) * Real.exp 1 *
        ((1 + 32 / κ) * w ^ 2) ^ (j + 1)) := by gcongr
    _ = _ := by
      unfold cepsBandMomentConst
      rw [mul_pow, ← pow_mul]
      have he : 2 * (j + 1) + 1 = 2 * j + 3 := by omega
      rw [← he, pow_succ]
      ring

/-- The actual survival series, including time zero, has every polynomial time moment. -/
theorem cepsBand_survival_moments {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l)
    (hlw : l ≤ 2 * w) (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (j : ℕ) (y : ℝ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * ‖Complex.exp (-q * n)‖ *
      krSurv (Icc 0 l) (ν : Measure ℝ) β a n y) ∧
    (∑' n : ℕ, (n + 1 : ℝ) ^ j * ‖Complex.exp (-q * n)‖ *
      krSurv (Icc 0 l) (ν : Measure ℝ) β a n y) ≤
      cepsBandMomentConst (cepsBandDecayConst D vlo vhi) (krKappa D vlo vhi) j *
        w ^ (2 * j + 3) := by
  have hB : 0 ≤ cepsBandDecayConst D vlo vhi := by unfold cepsBandDecayConst; positivity
  simpa only [mul_assoc] using cepsBand_moment_budget
    (fun n => mul_nonneg (norm_nonneg _) (krSurv_nonneg measurableSet_Icc ν β a n y)) hB
    (krKappa_pos hD hvlo hvhi) (show 1 ≤ w by linarith)
    (fun n => cepsBand_discount_survival_decay hD hθ hvlo hvhi hν hw hl hlw β ha hq n y) j

/-- A class constant for the last-step smoothing of a survival row into a density. -/
def cepsBandPinDecayConst (D vlo vhi : ℝ) : ℝ :=
  2 * D * Real.exp (krKappa D vlo vhi / 16) * cepsBandDecayConst D vlo vhi

/-- Discounted pointwise killed densities inherit the survival decay, uniformly in both ends. -/
theorem cepsBand_discount_density_decay {D θ vlo vhi : ℝ} (hD : 0 < D)
    (hθ : 0 < θ) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (n : ℕ) (y z : ℝ) :
    ‖Complex.exp (-q * ((n : ℂ) + 1))‖ * krDens (Icc 0 l) ν f β a (n + 1) y z ≤
      cepsBandPinDecayConst D vlo vhi * w *
        Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * n) := by
  have habs : 0 < |a| := by linarith
  have hdiv : D / |a| ≤ 2 * D := by rw [div_le_iff₀ habs]; nlinarith
  have hdens := krDens_le_div_mul_krSurv (J := Icc 0 l) ν measurableSet_Icc
    hf.measurable hf.nonneg hf.le (β := β) (a := a) n y z
  have hsurv := cepsBand_discount_survival_decay hD hθ hvlo hvhi hν hw hl hlw β ha hq n y
  have hnorm : ‖Complex.exp (-q)‖ ≤ Real.exp (krKappa D vlo vhi / 16) := by
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp]
    have hκ := krKappa_pos hD hvlo hvhi
    have he : krKappa D vlo vhi / (16 * w ^ 2) ≤ krKappa D vlo vhi / 16 := by
      apply div_le_div_of_nonneg_left hκ.le (by norm_num)
      nlinarith
    linarith
  have he : -q * ((n : ℂ) + 1) = -q + (-q * n) := by ring
  rw [he, Complex.exp_add, norm_mul]
  calc
    _ ≤ Real.exp (krKappa D vlo vhi / 16) * ‖Complex.exp (-q * n)‖ *
        (2 * D * krSurv (Icc 0 l) (ν : Measure ℝ) β a n y) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hnorm (norm_nonneg _))
        (hdens.trans (mul_le_mul_of_nonneg_right hdiv
          (krSurv_nonneg measurableSet_Icc ν β a n y)))
        (krDens_nonneg ν hf.nonneg _ _ _) (by positivity)
    _ = (2 * D * Real.exp (krKappa D vlo vhi / 16)) *
        (‖Complex.exp (-q * n)‖ * krSurv (Icc 0 l) (ν : Measure ℝ) β a n y) := by ring
    _ ≤ (2 * D * Real.exp (krKappa D vlo vhi / 16)) *
        (cepsBandDecayConst D vlo vhi * w *
          Real.exp (-(krKappa D vlo vhi / (16 * w ^ 2)) * n)) :=
      mul_le_mul_of_nonneg_left hsurv (by positivity)
    _ = _ := by unfold cepsBandPinDecayConst; ring

/-- Actual pointwise killed Green densities have every time moment, with explicit width degree. -/
theorem cepsBand_density_moments {D θ vlo vhi : ℝ} (hD : 0 < D) (hθ : 0 < θ)
    (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) {f : ℝ → ℝ} (hf : CepsGapDensity ν f D)
    {w l : ℝ} (hw : 2 ≤ w) (hl : w / 2 ≤ l) (hlw : l ≤ 2 * w)
    (β : ℝ) {a : ℝ} (ha : 1 / 2 ≤ |a|) {q : ℂ}
    (hq : -(krKappa D vlo vhi / (16 * w ^ 2)) ≤ q.re) (j : ℕ) (y z : ℝ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ j * ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
      krDens (Icc 0 l) ν f β a (n + 1) y z) ∧
    (∑' n : ℕ, (n + 1 : ℝ) ^ j * ‖Complex.exp (-q * ((n : ℂ) + 1))‖ *
      krDens (Icc 0 l) ν f β a (n + 1) y z) ≤
      cepsBandMomentConst (cepsBandPinDecayConst D vlo vhi) (krKappa D vlo vhi) j *
        w ^ (2 * j + 3) := by
  have hB : 0 ≤ cepsBandPinDecayConst D vlo vhi := by
    unfold cepsBandPinDecayConst cepsBandDecayConst
    positivity
  simpa only [mul_assoc] using cepsBand_moment_budget
    (fun n => mul_nonneg (norm_nonneg _) (krDens_nonneg ν hf.nonneg _ _ _)) hB
    (krKappa_pos hD hvlo hvhi) (show 1 ≤ w by linarith)
    (fun n => cepsBand_discount_density_decay hD hθ hvlo hvhi hν hf hw hl hlw β ha hq n y z) j

end
end PGM
