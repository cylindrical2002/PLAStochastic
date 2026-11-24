import PLAStochastic.Index.KEP.ReferenceScale.KilledPolynomialSeries

/-!
# Killed exponential envelopes including the short endpoint steps

Fixed losses of steps are paid by fixed constants, including a zero spectral
factor. The first rough convolution estimate also covers the true two-step
bridge. This permits pin sums to keep their entire original length decay.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepKilledRate (D vlo vhi w : ℝ) : ℝ := kepTruncatedKappa D vlo vhi / (2 * w ^ 2)

theorem kepKilledRate_bounds {D vlo vhi w : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 1 ≤ w) :
    0 < kepKilledRate D vlo vhi w ∧ kepKilledRate D vlo vhi w ≤ 1 / 2 := by
  have hk := kepTruncatedKappa_pos hD hvlo hvhi
  have hk1 : kepTruncatedKappa D vlo vhi ≤ 1 := min_le_right _ _
  constructor
  · unfold kepKilledRate
    positivity
  · unfold kepKilledRate
    apply (div_le_iff₀ (by positivity : 0 < 2 * w ^ 2)).mpr
    nlinarith only [hk1, hw, sq_nonneg (w - 1)]

theorem kep_shifted_geometric_le_exp {q r : ℝ} (hq : 0 ≤ q)
    (hr : 0 ≤ r) (hr2 : r ≤ 1 / 2) (hqr : q ≤ Real.exp (-r)) (n c : ℕ) :
    q ^ (n - c) ≤ Real.exp ((c : ℝ) / 2) * Real.exp (-r * n) := by
  have hnat : (n : ℝ) ≤ (n - c : ℕ) + (c : ℝ) := by
    exact_mod_cast (show n ≤ n - c + c by omega)
  calc
    _ ≤ Real.exp (-r) ^ (n - c) := pow_le_pow_left₀ hq hqr _
    _ = Real.exp (-r * (n - c : ℕ)) := by rw [mul_comm, Real.exp_nat_mul]
    _ ≤ Real.exp ((c : ℝ) / 2 - r * n) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hnat),
        mul_le_mul_of_nonneg_right hr2 (Nat.cast_nonneg c)]
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add, neg_mul]

theorem sqrt_krLam_shifted_le_exp {D vlo vhi w : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hw : 1 ≤ w) (n c : ℕ) :
    Real.sqrt (krLam D vlo vhi w) ^ (n - c) ≤
      Real.exp ((c : ℝ) / 2) * Real.exp (-kepKilledRate D vlo vhi w * n) :=
  kep_shifted_geometric_le_exp (Real.sqrt_nonneg _)
    (kepKilledRate_bounds hD hvlo hvhi hw).1.le
    (kepKilledRate_bounds hD hvlo hvhi hw).2
    (by simpa only [kepKilledRate, neg_div] using
      sqrt_krLam_le_exp_truncated_gap hD hvlo hvhi hw) n c

theorem krDens_le_exp_full_length (ν : ProbabilityMeasure ℝ)
    {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (n : ℕ) (x y : ℝ) :
    |krDens (Icc 0 w) ν f β a' (n + 1) x y| ≤
      2 * D * Real.exp 1 * Real.exp (-kepKilledRate D vlo vhi w * (n + 1 : ℕ)) := by
  have hD := H.hD
  rw [abs_of_nonneg (krDens_nonneg ν H.hf0 (n + 1) x y)]
  cases n with
  | zero =>
    have hr := (kepKilledRate_bounds H.hD H.hvlo H.hvhi H.hw).2
    have he : 1 ≤ Real.exp 1 * Real.exp (-kepKilledRate D vlo vhi w * (0 + 1 : ℕ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      norm_num only [Nat.reduceAdd, Nat.cast_one, mul_one]
      linarith
    exact (H.krDens_le_two_D 1 x y).trans
      (by simpa only [mul_assoc, mul_one] using
        mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * D))
  | succ n =>
    have hh := sqrt_krLam_shifted_le_exp H.hD H.hvlo H.hvhi H.hw (n + 2) 2
    simp only [Nat.add_sub_cancel, Nat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0)] at hh
    exact (krDens_le_spectral_two_steps ν H n x y).trans
      (by simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc] using
        mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2 * D))

theorem krDens_first_rough_bound (ν : ProbabilityMeasure ℝ)
    {f f' : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hpi' : Integrable f' volume)
    (n : ℕ) (x y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialFirst f' β a')
      (fun z => krDens (Icc 0 w) ν f β a' (n + 1) x z) y| ≤ 4 * D * ∫ t, |f' t| := by
  have hD := H.hD
  have hJ : 0 ≤ ∫ t, |f' t| := integral_nonneg fun _ => abs_nonneg _
  have ha : 0 < |a'| := lt_of_lt_of_le (by norm_num) H.ha₁'
  have hscale : (∫ t, |f' t|) / |a'| ≤ 2 * ∫ t, |f' t| :=
    (div_le_iff₀ ha).mpr (by nlinarith [H.ha₁'])
  have hb := abs_truncatedConvolution_le_input_bound (a := 0) (b := w)
    (integrable_kepStepSpatialFirst hpi' H.ha' β)
    (measurable_krDens_right ν H.hJ H.hf β a' (n + 1) x)
    (by positivity : 0 ≤ 2 * D)
    (fun z _ => by
      rw [abs_of_nonneg (krDens_nonneg ν H.hf0 (n + 1) x z)]
      exact H.krDens_le_two_D (n + 1) x z) y
  rw [integral_abs_kepStepSpatialFirst f' β H.ha'] at hb
  have hm := mul_le_mul_of_nonneg_left hscale (by positivity : 0 ≤ 2 * D)
  exact hb.trans (by nlinarith [hm])

end

end PGM
