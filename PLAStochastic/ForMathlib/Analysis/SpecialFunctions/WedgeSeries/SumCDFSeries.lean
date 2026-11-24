import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.TriangleIntegral
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# The derivative of the integrated wedge series

The derivative series is locally dominated by a polynomial times a geometric
sequence. Reindexing its two summable pieces gives the explicit sum CDF series.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def sumCDFSeries (s : ℝ) : ℝ := 1 + ∑' n : ℕ,
  (-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1) *
    Real.exp (-((n : ℝ) + 1) * ((n : ℝ) + 2) * s)

private def spectralBase (n : ℕ) (s : ℝ) : ℝ := Real.exp (-(n : ℝ) * ((n : ℝ) + 1) * s)
private def spectralLeft (n : ℕ) (s : ℝ) : ℝ := (-1 : ℝ) ^ n * (n : ℝ) * spectralBase n s
private def spectralRight (n : ℕ) (s : ℝ) : ℝ := (-1 : ℝ) ^ n * ((n : ℝ) + 1) * spectralBase n s

def integratedWedgeDeriv (n : ℕ) (s : ℝ) : ℝ := spectralLeft n s + spectralRight (n + 1) s

private theorem spectralBase_bound {r x : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (n : ℕ) :
    spectralBase n x ≤ Real.exp (-(n : ℝ) * r) := by
  apply Real.exp_le_exp.mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h₁ := mul_le_mul_of_nonneg_left hx (mul_nonneg hn (by positivity : 0 ≤ (n : ℝ) + 1))
  have h₂ := mul_nonneg (sq_nonneg (n : ℝ)) hr
  nlinarith

private theorem spectralLeft_bound {r x : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (n : ℕ) :
    ‖spectralLeft n x‖ ≤ ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r) := by
  simp only [spectralLeft, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), spectralBase, abs_of_pos (Real.exp_pos _)]
  apply (mul_le_mul_of_nonneg_left (spectralBase_bound hr hx n) (Nat.cast_nonneg n)).trans
  exact mul_le_mul_of_nonneg_right ((lt_add_one _).le) (Real.exp_nonneg _)

private theorem spectralRight_bound {r x : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (n : ℕ) :
    ‖spectralRight n x‖ ≤ ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r) := by
  simp only [spectralRight, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1), spectralBase,
    abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (spectralBase_bound hr hx n) (by positivity)

private theorem summable_polynomial_wedgeBound {r : ℝ} (hr : 0 < r) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r)) := by
  have h₁ := Real.summable_pow_mul_exp_neg_nat_mul 1 hr
  have h₀ := Real.summable_pow_mul_exp_neg_nat_mul 0 hr
  convert! h₁.add h₀ using 1
  funext n
  simp only [pow_one, pow_zero, one_mul, neg_mul]
  ring_nf

private theorem summable_spectralLeft {s : ℝ} (hs : 0 < s) :
    Summable (fun n => spectralLeft n s) :=
  (summable_polynomial_wedgeBound hs).of_norm_bounded (fun n => spectralLeft_bound hs.le le_rfl n)

private theorem summable_spectralRight {s : ℝ} (hs : 0 < s) :
    Summable (fun n => spectralRight n s) :=
  (summable_polynomial_wedgeBound hs).of_norm_bounded (fun n => spectralRight_bound hs.le le_rfl n)

theorem integratedWedgeDeriv_bound {r x : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (n : ℕ) :
    ‖integratedWedgeDeriv n x‖ ≤ 4 * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r) := by
  have hp := spectralLeft_bound hr hx n
  have hq := spectralRight_bound hr hx (n + 1)
  have he : Real.exp (-((n : ℝ) + 1) * r) ≤ Real.exp (-(n : ℝ) * r) := by
    apply Real.exp_le_exp.mpr
    linarith
  simp only [Nat.cast_add, Nat.cast_one] at hq
  have hq' := hq.trans (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (n : ℝ) + 1 + 1))
  apply (norm_add_le (spectralLeft n x) (spectralRight (n + 1) x)).trans
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he0 := Real.exp_nonneg (-(n : ℝ) * r)
  nlinarith

theorem hasDerivAt_integratedWedgeTerm (n : ℕ) (s : ℝ) :
    HasDerivAt (integratedWedgeTerm n) (integratedWedgeDeriv n s) s := by
  have hm : (n : ℝ) + 1 ≠ 0 := by positivity
  have heq : integratedWedgeTerm n = fun x => (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
      (spectralBase n x - spectralBase (n + 1) x) := by
    funext x
    unfold integratedWedgeTerm spectralBase
    congr 1
    congr 1 <;> congr 1 <;> push_cast <;> ring
  have hp := ((hasDerivAt_id s).const_mul (-(n : ℝ) * ((n : ℝ) + 1))).exp
  have hq := ((hasDerivAt_id s).const_mul (-((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1))).exp
  rw [heq]
  convert! (hp.sub hq).const_mul ((-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1)) using 1
  simp only [integratedWedgeDeriv, spectralLeft, spectralRight, spectralBase,
    Nat.cast_add, Nat.cast_one, pow_succ (-1 : ℝ), mul_one, id_eq]
  field_simp
  ring

theorem summable_integratedWedgeTerm {s : ℝ} (hs : 0 < s) :
    Summable (fun n => integratedWedgeTerm n s) := by
  apply ((summable_wedgeBound hs).mul_right s).of_norm_bounded
  intro n
  rw [← integral_wedgeTerm_triangle n s]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := s)
    (f := fun x => wedgeTerm n x (s - x))
    (C := 2 * Real.exp (-(n : ℝ) * s)) (fun x hx => ?_)
  · simpa only [sub_zero, abs_of_pos hs] using h
  · rw [uIoc_of_le hs.le] at hx
    exact wedgeTerm_bound hs.le hx.1.le (sub_nonneg.mpr hx.2) (by linarith) n

theorem summable_integratedWedgeDeriv {s : ℝ} (hs : 0 < s) :
    Summable (fun n => integratedWedgeDeriv n s) :=
  (summable_spectralLeft hs).add ((summable_nat_add_iff 1).mpr (summable_spectralRight hs))

theorem integratedWedgeDeriv_tsum {s : ℝ} (hs : 0 < s) :
    1 + ∑' n, integratedWedgeDeriv n s = sumCDFSeries s := by
  have hp := summable_spectralLeft hs
  have hq := summable_spectralRight hs
  have hps : Summable (fun n => spectralLeft (n + 1) s) := (summable_nat_add_iff 1).mpr hp
  have hqs : Summable (fun n => spectralRight (n + 1) s) := (summable_nat_add_iff 1).mpr hq
  have hp0 : spectralLeft 0 s = 0 := by simp [spectralLeft]
  simp only [integratedWedgeDeriv, hp.tsum_add hqs]
  rw [hp.tsum_eq_zero_add, hp0, zero_add, ← hps.tsum_add hqs]
  unfold sumCDFSeries
  congr 1
  apply tsum_congr
  intro n
  simp only [spectralLeft, spectralRight, spectralBase, Nat.cast_add, Nat.cast_one]
  ring_nf

/-- The integrated wedge has the explicit spectral CDF series as its ordinary
derivative at every strictly positive argument. -/
theorem hasDerivAt_wedgeIntegrated {s : ℝ} (hs : 0 < s) :
    HasDerivAt wedgeIntegrated (sumCDFSeries s) s := by
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hsr : s ∈ Ioi r := by change s / 2 < s; linarith
  have hb : Summable (fun n : ℕ => 4 * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r)) := by
    convert! (summable_polynomial_wedgeBound hr).mul_left 4 using 1
    funext n
    ring
  have hd := hasDerivAt_tsum_of_isPreconnected hb isOpen_Ioi isPreconnected_Ioi
    (fun n x _ => hasDerivAt_integratedWedgeTerm n x)
    (fun n x hx => integratedWedgeDeriv_bound hr.le hx.le n)
    hsr (summable_integratedWedgeTerm hs) hsr
  have hh := (hasDerivAt_id s).add hd
  rw [integratedWedgeDeriv_tsum hs] at hh
  apply hh.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with x hx
  exact wedgeIntegrated_eq_tsum hx

private theorem sumCDFTerm_bound {r x : ℝ} (hr : 0 ≤ r) (hx : r ≤ x) (n : ℕ) :
    ‖(-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1) *
      Real.exp (-((n : ℝ) + 1) * ((n : ℝ) + 2) * x)‖ ≤
      4 * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r) := by
  have heq : (-1 : ℝ) ^ (n + 1) * (2 * ((n : ℝ) + 1) + 1) *
      Real.exp (-((n : ℝ) + 1) * ((n : ℝ) + 2) * x) =
      spectralLeft (n + 1) x + spectralRight (n + 1) x := by
    simp only [spectralLeft, spectralRight, spectralBase, Nat.cast_add, Nat.cast_one]
    ring_nf
  rw [heq]
  have hp := spectralLeft_bound hr hx (n + 1)
  have hq := spectralRight_bound hr hx (n + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hp hq
  have he : Real.exp (-((n : ℝ) + 1) * r) ≤ Real.exp (-(n : ℝ) * r) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hmul := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ (n : ℝ) + 1 + 1)
  have hp' := hp.trans hmul
  have hq' := hq.trans hmul
  apply (norm_add_le (spectralLeft (n + 1) x) (spectralRight (n + 1) x)).trans
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have he0 := Real.exp_nonneg (-(n : ℝ) * r)
  nlinarith

theorem continuousAt_sumCDFSeries {s : ℝ} (hs : 0 < s) : ContinuousAt sumCDFSeries s := by
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hsr : r < s := by dsimp only [r]; linarith
  have hb : Summable (fun n : ℕ => 4 * ((n : ℝ) + 1) * Real.exp (-(n : ℝ) * r)) := by
    convert! (summable_polynomial_wedgeBound hr).mul_left 4 using 1
    funext n
    ring
  have hc : ContinuousOn sumCDFSeries (Ioi r) := by
    unfold sumCDFSeries
    apply continuousOn_const.add
    apply continuousOn_tsum (fun n => ?_) hb (fun n x hx => sumCDFTerm_bound hr.le hx.le n)
    fun_prop
  exact hc.continuousAt (Ioi_mem_nhds hsr)

theorem continuousOn_sumCDFSeries : ContinuousOn sumCDFSeries (Ioi 0) :=
  fun _ hs => (continuousAt_sumCDFSeries hs).continuousWithinAt

end BrownianAffine
