import PLAStochastic.Index.GEP.StrongApprox.Endgame.Asymptotics
import PLAStochastic.Index.GEP.StrongApprox.Coupling.Desmoothing

/-! # Scalar error estimates after lifting the block coupling -/

namespace PGM

open Filter Topology

/-- At the Bernstein cutoff, the quadratic part is the smaller part. -/
theorem sa_bernstein_cutoff {w m H : ℝ} (hw : 0 ≤ w) (hm : 0 < m) (hH : 0 ≤ H)
    (hlarge : w * H ≤ m) :
    min ((Real.sqrt (w * m * H)) ^ 2 / m) (Real.sqrt (w * m * H)) = w * H := by
  have hs : 0 ≤ w * m * H := by positivity
  have he : Real.sqrt (w * m * H) ^ 2 / m = w * H := by
    rw [Real.sq_sqrt hs]
    field_simp
  rw [he, min_eq_left]
  apply (Real.le_sqrt (by positivity) hs).2
  nlinarith [mul_le_mul_of_nonneg_left hlarge (show 0 ≤ w * H by positivity)]

/-- The fourth-root leaf scale absorbs the tree logarithms and both smoothing corrections. -/
theorem sa_final_error_bound {vlo vhi v s N m H A w : ℝ}
    (hvlo : 0 < vlo) (hv : vlo ≤ v) (hvhi : v ≤ vhi)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hm : 1 ≤ m) (hH : 1 ≤ H)
    (hA : 0 ≤ A) (hw : 0 ≤ w)
    (hnoise : s * N ≤ 1) (hvariance : s ^ 2 * N ≤ 1)
    (hlog : H ^ 2 ≤ Real.sqrt m) :
    A * H ^ 2 * Real.sqrt H + |s| * N + Real.sqrt (w * m * H) +
        Real.sqrt (v + s ^ 2) * Real.sqrt (w * m * H) + s ^ 2 / (2 * Real.sqrt v) * N ≤
      (A + Real.sqrt w * (1 + Real.sqrt (vhi + 1)) + 1 + 1 / (2 * Real.sqrt vlo)) *
        (Real.sqrt m * Real.sqrt H) := by
  have hm0 : 0 ≤ m := by linarith
  have hH0 : 0 ≤ H := by linarith
  have hv0 : 0 < v := hvlo.trans_le hv
  have hvhi0 : 0 ≤ vhi + 1 := by linarith
  have hrootlo : 0 < Real.sqrt vlo := Real.sqrt_pos.2 hvlo
  have hroot : 0 < Real.sqrt v := Real.sqrt_pos.2 hv0
  have hrootle : Real.sqrt vlo ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
  have hV : Real.sqrt (v + s ^ 2) ≤ Real.sqrt (vhi + 1) := by
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (1 - s)]
  have hM : 1 ≤ Real.sqrt m * Real.sqrt H := by
    have hm' : 1 ≤ Real.sqrt m := (Real.le_sqrt (by norm_num) hm0).2 (by simpa using hm)
    have hH' : 1 ≤ Real.sqrt H := (Real.le_sqrt (by norm_num) hH0).2 (by simpa using hH)
    nlinarith
  have hb : Real.sqrt (w * m * H) = Real.sqrt w * (Real.sqrt m * Real.sqrt H) := by
    rw [Real.sqrt_mul (mul_nonneg hw hm0), Real.sqrt_mul hw]
    ring
  have htree : A * H ^ 2 * Real.sqrt H ≤ A * (Real.sqrt m * Real.sqrt H) := by
    have := mul_le_mul_of_nonneg_left hlog hA
    nlinarith [mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg H)]
  have hcorr : s ^ 2 / (2 * Real.sqrt v) * N ≤ 1 / (2 * Real.sqrt vlo) := by
    calc
      _ = (s ^ 2 * N) / (2 * Real.sqrt v) := by ring
      _ ≤ 1 / (2 * Real.sqrt v) := div_le_div_of_nonneg_right hvariance (by positivity)
      _ ≤ _ := one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [abs_of_nonneg hs, hb]
  have hscaled := mul_le_mul_of_nonneg_right hV
    (show 0 ≤ Real.sqrt w * (Real.sqrt m * Real.sqrt H) by positivity)
  have hconst := mul_le_mul_of_nonneg_left hM
    (show 0 ≤ 1 + 1 / (2 * Real.sqrt vlo) by positivity)
  nlinarith

/-- Summing the source blocks, Gaussian blocks, and two desmoothing walk budgets
still gives the frozen failure probability. -/
theorem sa_final_probability_bound {N m L w c : ℝ}
    (hN : 16 ≤ N) (hm : 1 ≤ m) (hL : 1 ≤ L) (hNm : N = L * m)
    (hw : 20 ≤ w) (_hc : 0 ≤ c) (hcw : 10 ≤ c * w)
    (hlarge : w * Real.log N ≤ m)
    (hnoise : 8 * N * Real.exp (-(N / 2)) ≤ N ^ (-(3 : ℝ))) :
    N ^ (-(3 : ℝ)) +
        (L + 1) * (2 * Real.exp (-(c * min (Real.sqrt (w * m * Real.log N) ^ 2 / m)
          (Real.sqrt (w * m * Real.log N))))) +
        (L + 1) * (2 * (m + 1) * Real.exp (-(Real.sqrt (w * m * Real.log N) ^ 2 / (2 * m)))) +
        2 * (2 * (N + 1) * Real.exp (-(N ^ 2 / (2 * N)))) ≤ N ^ (-(2 : ℝ)) := by
  have hN0 : 0 < N := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hH : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hcut := sa_bernstein_cutoff hw0 hm0 hH hlarge
  have hexp : Real.exp (-(10 * Real.log N)) = N ^ (-(10 : ℝ)) := by
    rw [Real.rpow_def_of_pos hN0]
    congr 1
    ring
  have hsrc : Real.exp (-(c * min (Real.sqrt (w * m * Real.log N) ^ 2 / m)
      (Real.sqrt (w * m * Real.log N)))) ≤ N ^ (-(10 : ℝ)) := by
    rw [hcut, ← hexp]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hcw hH]
  have hgauss : Real.exp (-(Real.sqrt (w * m * Real.log N) ^ 2 / (2 * m))) ≤
      N ^ (-(10 : ℝ)) := by
    have he : Real.sqrt (w * m * Real.log N) ^ 2 / (2 * m) = w / 2 * Real.log N := by
      rw [Real.sq_sqrt (by positivity)]
      field_simp
    rw [he, ← hexp]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hw hH]
  have hLle : L ≤ N := by nlinarith
  have hprod : (L + 1) * (m + 1) ≤ 4 * N := by
    have hx := mul_le_mul (show L + 1 ≤ 2 * L by linarith)
      (show m + 1 ≤ 2 * m by linarith) (by positivity) (by positivity)
    nlinarith
  have hp : N * N ^ (-(10 : ℝ)) ≤ N ^ (-(3 : ℝ)) := by
    calc
      _ ≤ N * N ^ (-(4 : ℝ)) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)) hN0.le
      _ = _ := by
        conv_lhs => lhs; rw [← Real.rpow_one N]
        rw [← Real.rpow_add hN0]
        norm_num
  have hsrc' : (L + 1) * (2 * Real.exp (-(c * min (Real.sqrt (w * m * Real.log N) ^ 2 / m)
        (Real.sqrt (w * m * Real.log N))))) ≤ 4 * N ^ (-(3 : ℝ)) := by
    have hb := mul_le_mul_of_nonneg_left hsrc (show 0 ≤ (L + 1) * 2 by positivity)
    have hcoef : (L + 1) * 2 ≤ 4 * N := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hN0.le (-(10 : ℝ)))]
  have hgauss' : (L + 1) * (2 * (m + 1) *
      Real.exp (-(Real.sqrt (w * m * Real.log N) ^ 2 / (2 * m)))) ≤
        8 * N ^ (-(3 : ℝ)) := by
    have hb := mul_le_mul_of_nonneg_left hgauss (show 0 ≤ (L + 1) * (2 * (m + 1)) by positivity)
    have hcoef : (L + 1) * (2 * (m + 1)) ≤ 8 * N := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hN0.le (-(10 : ℝ)))]
  have hnoise' : 2 * (2 * (N + 1) * Real.exp (-(N ^ 2 / (2 * N)))) ≤ N ^ (-(3 : ℝ)) := by
    have he : N ^ 2 / (2 * N) = N / 2 := by field_simp
    rw [he]
    have hcoef : 4 * (N + 1) ≤ 8 * N := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef (Real.exp_pos (-(N / 2))).le]
  have hfinal : 14 * N ^ (-(3 : ℝ)) ≤ N ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hN0.le, Real.rpow_neg hN0.le]
    norm_num only [Real.rpow_ofNat]
    field_simp
    nlinarith
  linarith

end PGM
