import PLAStochastic.Affine.Moments.Optimal.Survival.Image.ThetaDerivative
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.ExponentialIntegral

/-! # Positive half-integer Gaussian images and their derivatives -/
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace BrownianAffine
set_option backward.isDefEq.respectTransparency false

def oddHeatImageRate (n : ℕ) : ℝ := (2*(n : ℝ)+1)^2/2
def oddHeatImageTerm (n : ℕ) (t : ℝ) : ℝ := expNegInvGlue (t/oddHeatImageRate n)

theorem oddHeatImageRate_pos (n : ℕ) : 0 < oddHeatImageRate n := by
  unfold oddHeatImageRate
  positivity

theorem oddHeatImageRate_bounds (n : ℕ) :
    ((n : ℝ)+1)/2 ≤ oddHeatImageRate n ∧ oddHeatImageRate n ≤ 2*((n : ℝ)+1)^2 := by
  unfold oddHeatImageRate
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n, sq_nonneg (n : ℝ)]

theorem oddHeatImageTerm_of_pos (n : ℕ) {t : ℝ} (ht : 0 < t) :
    oddHeatImageTerm n t = Real.exp (-oddHeatImageRate n/t) :=
  expNegInvGlue_div (oddHeatImageRate_pos n) ht

theorem oddHeatImageTerm_bound (n : ℕ) {T t : ℝ} (hT : 0 < T) (ht : t ≤ T) :
    ‖oddHeatImageTerm n t‖ ≤ Real.exp (-((n : ℝ)+1)/(2*T)) := by
  rw [oddHeatImageTerm, Real.norm_eq_abs, abs_of_nonneg (expNegInvGlue.nonneg _)]
  have hh := expNegInvGlue.monotone (div_le_div_of_nonneg_right ht (oddHeatImageRate_pos n).le)
  rw [expNegInvGlue_div (oddHeatImageRate_pos n) hT] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hi := div_le_div_of_nonneg_right (oddHeatImageRate_bounds n).1 hT.le
  convert! neg_le_neg hi using 1 <;> ring

theorem summable_oddHeatImageBound {T : ℝ} (hT : 0 < T) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ)+1)^k * Real.exp (-((n : ℝ)+1)/(2*T))) := by
  have hh := (summable_nat_add_iff 1).mpr
    (Real.summable_pow_mul_exp_neg_nat_mul k (by positivity : 0 < 1/(2*T)))
  convert! hh using 1
  funext n
  simp only [Nat.cast_add, Nat.cast_one]
  congr 1
  congr 1
  ring

theorem summable_oddHeatImageTerm (t : ℝ) : Summable (fun n => oddHeatImageTerm n t) := by
  let T := max t 1
  have hT : 0 < T := zero_lt_one.trans_le (le_max_right _ _)
  have hh : Summable (fun n : ℕ => Real.exp (-((n : ℝ)+1)/(2*T))) := by
    simpa only [pow_zero, one_mul] using summable_oddHeatImageBound hT 0
  exact hh.of_norm_bounded (fun n => oddHeatImageTerm_bound n hT (le_max_left _ _))

theorem alternatingHeatTheta_image_nat {t : ℝ} (ht : 0 < t) :
    alternatingHeatTheta t = 2 / (Real.pi*t/2)^(1/2 : ℝ) *
      ∑' n : ℕ, oddHeatImageTerm n t := by
  let f : ℤ → ℝ := fun n => Real.exp (-2*((n : ℝ)+1/2)^2/t)
  have hn (n : ℕ) : f n = oddHeatImageTerm n t := by
    rw [oddHeatImageTerm_of_pos n ht]
    unfold f oddHeatImageRate
    simp only [Int.cast_natCast]
    congr 1
    ring
  have hneg (n : ℕ) : f (-(n+1 : ℤ)) = oddHeatImageTerm n t := by
    rw [oddHeatImageTerm_of_pos n ht]
    unfold f oddHeatImageRate
    push_cast
    congr 1
    ring
  have hs : Summable f := (show Summable (fun n : ℕ => f n) by
    simpa only [hn] using summable_oddHeatImageTerm t).of_nat_of_neg_add_one
      (by simpa only [hneg] using summable_oddHeatImageTerm t)
  have hsum := tsum_nat_add_neg_add_one hs
  simp only [hn, hneg] at hsum
  rw [(summable_oddHeatImageTerm t).tsum_add (summable_oddHeatImageTerm t)] at hsum
  have he : (∑' n : ℤ, Real.exp (-2*((n : ℝ)-1/2)^2/t)) = ∑' n : ℤ, f n := by
    have hh := (Equiv.neg ℤ).tsum_eq f
    convert! hh using 1
    apply tsum_congr
    intro n
    unfold f
    simp only [Equiv.neg_apply, Int.cast_neg]
    congr 1
    ring
  rw [alternatingHeatTheta_image ht, he, ← hsum]
  ring

theorem hasDerivAt_oddHeatImageTerm (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (oddHeatImageTerm n)
      (oddHeatImageRate n/t^2 * Real.exp (-oddHeatImageRate n/t)) t :=
  hasDerivAt_inverseExp (oddHeatImageRate_pos n) ht

theorem oddHeatImageDerivative_bound (n : ℕ) {δ T t : ℝ}
    (hδ : 0 < δ) (htδ : δ ≤ t) (htT : t ≤ T) :
    ‖oddHeatImageRate n/t^2 * Real.exp (-oddHeatImageRate n/t)‖ ≤
      (2/δ^2) * (((n : ℝ)+1)^2 * Real.exp (-((n : ℝ)+1)/(2*T))) := by
  have ht : 0 < t := hδ.trans_le htδ
  have hT : 0 < T := ht.trans_le htT
  have he := oddHeatImageTerm_bound n hT htT
  rw [oddHeatImageTerm_of_pos n ht, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at he
  have hc : oddHeatImageRate n/t^2 ≤ 2*((n : ℝ)+1)^2/δ^2 := by
    calc
      _ ≤ 2*((n : ℝ)+1)^2/t^2 := div_le_div_of_nonneg_right (oddHeatImageRate_bounds n).2 (sq_nonneg t)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hδ) (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (div_nonneg (oddHeatImageRate_pos n).le (sq_nonneg t)) (Real.exp_nonneg _))]
  have hh := mul_le_mul hc he (Real.exp_nonneg _) (by positivity)
  convert! hh using 1
  ring

theorem hasDerivAt_tsum_oddHeatImageTerm {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ∑' n, oddHeatImageTerm n s)
      (∑' n, oddHeatImageRate n/t^2 * Real.exp (-oddHeatImageRate n/t)) t := by
  let δ := t/2
  let T := 2*t
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hT : 0 < T := by dsimp [T]; positivity
  have hmem : t ∈ Ioo δ T := by change t/2 < t ∧ t < 2*t; constructor <;> linarith
  have hb := (summable_oddHeatImageBound hT 2).mul_left (2/δ^2)
  exact hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioo isPreconnected_Ioo
    (fun n s hs => hasDerivAt_oddHeatImageTerm n (hδ.trans hs.1))
    (fun n s hs => oddHeatImageDerivative_bound n hδ hs.1.le hs.2.le)
    hmem (summable_oddHeatImageTerm t) hmem

end BrownianAffine
