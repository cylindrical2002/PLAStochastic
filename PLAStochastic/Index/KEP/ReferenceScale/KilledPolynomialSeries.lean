import PLAStochastic.Index.KEP.ReferenceScale.KernelFirstDecay
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.PolynomialExponentialSeries

/-!
# Quantitative polynomial series for the killed spectral factor

These estimates also apply before a law is selected. Truncating the positive
class gap by one handles a negative formal lambda without adding a regular-law
premise. Each polynomial length sum costs a polynomial in the band width.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

def kepTruncatedKappa (D vlo vhi : ℝ) : ℝ := min (krKappa D vlo vhi) 1

theorem kepTruncatedKappa_pos {D vlo vhi : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    0 < kepTruncatedKappa D vlo vhi :=
  lt_min (krKappa_pos hD hvlo hvhi) one_pos

theorem sqrt_krLam_le_exp_truncated_gap {D vlo vhi w : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 1 ≤ w) :
    Real.sqrt (krLam D vlo vhi w) ≤
      Real.exp (-kepTruncatedKappa D vlo vhi / (2 * w ^ 2)) := by
  let k := kepTruncatedKappa D vlo vhi
  let x := k / w ^ 2
  have hk : 0 < k := kepTruncatedKappa_pos hD hvlo hvhi
  have hk1 : k ≤ 1 := min_le_right _ _
  have hkk : k ≤ krKappa D vlo vhi := min_le_left _ _
  have hw0 : 0 < w := by linarith
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_one (by positivity : 0 < w ^ 2)).mpr
    nlinarith only [hk1, hw, sq_nonneg (w - 1)]
  have hlam : krLam D vlo vhi w ≤ 1 - x := by
    dsimp [krLam, x]
    have h := div_le_div_of_nonneg_right hkk (by positivity : 0 ≤ w ^ 2)
    linarith only [h]
  have hs : Real.sqrt (1 - x) ≤ 1 - x / 2 := by
    rw [Real.sqrt_le_left (by linarith)]
    nlinarith only [hx, hx1, sq_nonneg x]
  calc
    _ ≤ Real.sqrt (1 - x) := Real.sqrt_le_sqrt hlam
    _ ≤ 1 - x / 2 := hs
    _ ≤ Real.exp (-x / 2) := by
      simpa only [neg_div, sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-x / 2)
    _ = _ := by congr 1; dsimp [x]; ring

/-- The weight leaves half the killed rate for the length sum. -/
theorem summable_polynomial_weighted_sqrt_krLam
    {D vlo vhi w eta : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hw : 1 ≤ w) (heta : eta ≤ kepTruncatedKappa D vlo vhi / (4 * w ^ 2)) (p : ℕ) :
    Summable (fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (eta * n) *
      Real.sqrt (krLam D vlo vhi w) ^ n) := by
  let r := kepTruncatedKappa D vlo vhi / (4 * w ^ 2)
  have hr : 0 < r := by
    have := kepTruncatedKappa_pos hD hvlo hvhi
    dsimp [r]
    positivity
  have hs : Summable (fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (-r * n)) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
    convert h.mul_left (Real.exp r) using 1 <;> first
    | rfl
    | (funext n
       rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
       congr 2
       ring)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (n + 1 : ℝ) ^ p)
  calc
    _ ≤ Real.exp (eta * n) *
        Real.exp (-kepTruncatedKappa D vlo vhi / (2 * w ^ 2)) ^ n := by
      gcongr
      exact sqrt_krLam_le_exp_truncated_gap hD hvlo hvhi hw
    _ = Real.exp ((eta - 2 * r) * n) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      dsimp [r]
      ring
    _ ≤ Real.exp (-r * n) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
      linarith only [heta]

theorem tsum_polynomial_weighted_sqrt_krLam_le
    {D vlo vhi w eta : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hw : 1 ≤ w) (heta : eta ≤ kepTruncatedKappa D vlo vhi / (4 * w ^ 2)) (p : ℕ) :
    (∑' n : ℕ, (n + 1 : ℝ) ^ p * Real.exp (eta * n) *
      Real.sqrt (krLam D vlo vhi w) ^ n) ≤
      ((p.factorial : ℝ) * Real.exp 1 *
        (1 + 8 / kepTruncatedKappa D vlo vhi) ^ (p + 1)) * w ^ (2 * (p + 1)) := by
  let r := kepTruncatedKappa D vlo vhi / (4 * w ^ 2)
  have hk := kepTruncatedKappa_pos hD hvlo hvhi
  have hr : 0 < r := by dsimp [r]; positivity
  have hs := summable_polynomial_weighted_sqrt_krLam hD hvlo hvhi hw heta p
  have hsR : Summable (fun n : ℕ => (n + 1 : ℝ) ^ p * Real.exp (-r * n)) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
    convert h.mul_left (Real.exp r) using 1 <;> first
    | rfl
    | (funext n
       rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
       congr 2
       ring)
  have hb (n : ℕ) : (n + 1 : ℝ) ^ p * Real.exp (eta * n) *
      Real.sqrt (krLam D vlo vhi w) ^ n ≤ (n + 1 : ℝ) ^ p * Real.exp (-r * n) := by
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (n + 1 : ℝ) ^ p)
    calc
      _ ≤ Real.exp (eta * n) *
          Real.exp (-kepTruncatedKappa D vlo vhi / (2 * w ^ 2)) ^ n := by
        gcongr
        exact sqrt_krLam_le_exp_truncated_gap hD hvlo hvhi hw
      _ = Real.exp ((eta - 2 * r) * n) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        dsimp [r]
        ring
      _ ≤ Real.exp (-r * n) := by
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg n)
        linarith only [heta]
  have hscale : 1 + 2 / r ≤ (1 + 8 / kepTruncatedKappa D vlo vhi) * w ^ 2 := by
    have heq : 2 / r = 8 / kepTruncatedKappa D vlo vhi * w ^ 2 := by
      dsimp [r]
      field_simp
      ring
    rw [heq]
    nlinarith only [hw, sq_nonneg (w - 1)]
  calc
    _ ≤ ∑' n : ℕ, (n + 1 : ℝ) ^ p * Real.exp (-r * n) := hs.tsum_le_tsum hb hsR
    _ ≤ (p.factorial : ℝ) * Real.exp 1 * (1 + 2 / r) ^ (p + 1) :=
      Real.tsum_polynomial_mul_exp_neg_le hr p
    _ ≤ (p.factorial : ℝ) * Real.exp 1 *
        ((1 + 8 / kepTruncatedKappa D vlo vhi) * w ^ 2) ^ (p + 1) := by gcongr
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

end

end PGM
