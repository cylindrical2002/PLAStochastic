import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# The analytic series for the expanding Brownian wedge

Absolute summability and exact cancellation on either boundary are proved
before this function is used at a stopping time.
-/

noncomputable section
open Filter
open scoped Topology

namespace BrownianAffine

def wedgeTerm (n : ℕ) (u v : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) *
    (Real.exp (-((n : ℝ) + 1) ^ 2 * (u + v) + ((n : ℝ) + 1) * (u - v)) +
      Real.exp (-((n : ℝ) + 1) ^ 2 * (u + v) - ((n : ℝ) + 1) * (u - v)))

def wedgeSeries (u v : ℝ) : ℝ := 1 + ∑' n : ℕ, wedgeTerm n u v

theorem wedgeTerm_symm (n : ℕ) (u v : ℝ) : wedgeTerm n u v = wedgeTerm n v u := by
  unfold wedgeTerm
  congr 1
  rw [add_comm (Real.exp _) (Real.exp _)]
  congr 1 <;> congr 1 <;> ring

theorem wedgeTerm_bound {s u v : ℝ} (hs : 0 ≤ s) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsuv : s ≤ u + v) (n : ℕ) : ‖wedgeTerm n u v‖ ≤ 2 * Real.exp (-(n : ℝ) * s) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hkn : (n : ℝ) ≤ ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1) := by nlinarith
  have hk : 0 ≤ ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1) := hn.trans hkn
  have hb : (n : ℝ) * s ≤ (((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1)) * (u + v) :=
    (mul_le_mul_of_nonneg_right hkn hs).trans (mul_le_mul_of_nonneg_left hsuv hk)
  have hp : ((n : ℝ) + 1) * (u - v) ≤ ((n : ℝ) + 1) * (u + v) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hm : -(((n : ℝ) + 1) * (u - v)) ≤ ((n : ℝ) + 1) * (u + v) := by
    nlinarith [mul_nonneg (show 0 ≤ (n : ℝ) + 1 by positivity) hu]
  have he₁ := Real.exp_le_exp.mpr (show
      -((n : ℝ) + 1) ^ 2 * (u + v) + ((n : ℝ) + 1) * (u - v) ≤ -(n : ℝ) * s by
    nlinarith)
  have he₂ := Real.exp_le_exp.mpr (show
      -((n : ℝ) + 1) ^ 2 * (u + v) - ((n : ℝ) + 1) * (u - v) ≤ -(n : ℝ) * s by
    nlinarith)
  simp only [wedgeTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_pos (add_pos (Real.exp_pos _) (Real.exp_pos _))]
  linarith

theorem summable_wedgeBound {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => 2 * Real.exp (-(n : ℝ) * s)) := by
  simpa only [mul_neg, neg_mul] using
    (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hs)).mul_left 2

theorem summable_wedgeTerm {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hs : 0 < u + v) :
    Summable (fun n => wedgeTerm n u v) :=
  (summable_wedgeBound hs).of_norm_bounded (fun n => wedgeTerm_bound hs.le hu hv le_rfl n)

private def boundaryTerm (n : ℕ) (v : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (-(n : ℝ) * ((n : ℝ) + 1) * v)

private theorem summable_boundaryTerm {v : ℝ} (hv : 0 < v) :
    Summable (fun n => boundaryTerm n v) := by
  apply (Real.summable_exp_nat_mul_iff.mpr (neg_neg_of_pos hv)).of_norm_bounded
  intro n
  simp only [boundaryTerm, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg (sq_nonneg (n : ℝ)) hv.le]

private theorem wedgeTerm_zero_left (n : ℕ) (v : ℝ) :
    wedgeTerm n 0 v = boundaryTerm (n + 1) v - boundaryTerm n v := by
  unfold wedgeTerm boundaryTerm
  simp only [Nat.cast_add, Nat.cast_one, pow_succ (-1 : ℝ)]
  have h₁ : -((n : ℝ) + 1) ^ 2 * (0 + v) + ((n : ℝ) + 1) * (0 - v) =
      -((n : ℝ) + 1) * ((n : ℝ) + 1 + 1) * v := by ring
  have h₂ : -((n : ℝ) + 1) ^ 2 * (0 + v) - ((n : ℝ) + 1) * (0 - v) =
      -(n : ℝ) * ((n : ℝ) + 1) * v := by ring
  rw [h₁, h₂]
  ring

theorem wedgeSeries_zero_left {v : ℝ} (hv : 0 < v) : wedgeSeries 0 v = 0 := by
  have hs := summable_boundaryTerm hv
  have hsucc : Summable (fun n => boundaryTerm (n + 1) v) := (summable_nat_add_iff 1).mpr hs
  have he := hs.tsum_eq_zero_add
  have hz : boundaryTerm 0 v = 1 := by simp [boundaryTerm]
  rw [hz] at he
  simp only [wedgeSeries, wedgeTerm_zero_left]
  rw [hsucc.tsum_sub hs]
  linarith

theorem wedgeSeries_symm (u v : ℝ) : wedgeSeries u v = wedgeSeries v u := by
  simp only [wedgeSeries, wedgeTerm_symm (u := u) (v := v)]

theorem wedgeSeries_zero_right {u : ℝ} (hu : 0 < u) : wedgeSeries u 0 = 0 := by
  rw [wedgeSeries_symm]
  exact wedgeSeries_zero_left hu

theorem wedgeSeries_bound {s u v : ℝ} (hs : 0 < s) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hsuv : s ≤ u + v) :
    ‖wedgeSeries u v‖ ≤ 1 + ∑' n : ℕ, 2 * Real.exp (-(n : ℝ) * s) := by
  apply (norm_add_le 1 _).trans
  rw [norm_one]
  exact add_le_add_right (tsum_of_norm_bounded (summable_wedgeBound hs).hasSum
    (fun n => wedgeTerm_bound hs.le hu hv hsuv n)) 1

theorem continuousOn_wedgeSeries {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun x : ℝ × ℝ => wedgeSeries x.1 x.2)
      {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ s ≤ x.1 + x.2} := by
  apply continuousOn_const.add
  apply continuousOn_tsum (fun n => ?_) (summable_wedgeBound hs)
    (fun n x hx => wedgeTerm_bound hs.le hx.1 hx.2.1 hx.2.2 n)
  unfold wedgeTerm
  fun_prop

private theorem wedgeExponent_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (n : ℕ) :
    -((n : ℝ) + 1) ^ 2 * (u + v) + ((n : ℝ) + 1) * (u - v) ≤ -2 * v := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hk : 0 ≤ ((n : ℝ) + 1) ^ 2 - ((n : ℝ) + 1) := by nlinarith
  have h₁ := mul_nonneg hk (add_nonneg hu hv)
  have h₂ := mul_nonneg hn hv
  nlinarith

theorem tendsto_wedgeTerm_of_atTop {α : Type*} {l : Filter α} {u v : α → ℝ}
    (hu : Tendsto u l atTop) (hv : Tendsto v l atTop) (n : ℕ) :
    Tendsto (fun x => wedgeTerm n (u x) (v x)) l (𝓝 0) := by
  have he (f : α → ℝ) (hf : Tendsto f l atTop) :
      Tendsto (fun x => Real.exp (-2 * f x)) l (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul, Function.comp_def] using tendsto_neg_atTop_atBot.comp (hf.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have h₁ : Tendsto (fun x => Real.exp (-((n : ℝ) + 1) ^ 2 * (u x + v x) +
      ((n : ℝ) + 1) * (u x - v x))) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) ?_ (he v hv)
    filter_upwards [hu.eventually_ge_atTop 0, hv.eventually_ge_atTop 0] with x hux hvx
    exact Real.exp_le_exp.mpr (wedgeExponent_le hux hvx n)
  have h₂ : Tendsto (fun x => Real.exp (-((n : ℝ) + 1) ^ 2 * (u x + v x) -
      ((n : ℝ) + 1) * (u x - v x))) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) ?_ (he u hu)
    filter_upwards [hu.eventually_ge_atTop 0, hv.eventually_ge_atTop 0] with x hux hvx
    apply Real.exp_le_exp.mpr
    convert wedgeExponent_le hvx hux n using 1
    ring
  simpa only [wedgeTerm, add_zero, mul_zero] using (h₁.add h₂).const_mul ((-1 : ℝ) ^ (n + 1))

/-- Both distances to the moving wedge boundaries diverge along a surviving path. -/
theorem tendsto_wedgeSeries_of_atTop {α : Type*} {l : Filter α} {u v : α → ℝ}
    (hu : Tendsto u l atTop) (hv : Tendsto v l atTop) :
    Tendsto (fun x => wedgeSeries (u x) (v x)) l (𝓝 1) := by
  have hb : ∀ᶠ x in l, ∀ n, ‖wedgeTerm n (u x) (v x)‖ ≤
      2 * Real.exp (-(n : ℝ) * 1) := by
    filter_upwards [hu.eventually_ge_atTop 1, hv.eventually_ge_atTop 0] with x hux hvx n
    exact wedgeTerm_bound (by norm_num) (by linarith) hvx (by linarith) n
  have h := tendsto_tsum_of_dominated_convergence (summable_wedgeBound (by norm_num : (0 : ℝ) < 1))
    (fun n => tendsto_wedgeTerm_of_atTop hu hv n) hb
  simpa only [wedgeSeries, tsum_zero, add_zero] using h.const_add 1

end BrownianAffine
