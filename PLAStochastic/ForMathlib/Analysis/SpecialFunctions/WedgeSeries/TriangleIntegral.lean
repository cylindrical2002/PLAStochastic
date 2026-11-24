import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.WedgeSeries.Summability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Integrating the wedge series along a triangle boundary
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace BrownianAffine

set_option backward.isDefEq.respectTransparency false

def wedgeIntegrated (s : ℝ) : ℝ := ∫ a in 0..s, wedgeSeries a (s - a)

def integratedWedgeTerm (n : ℕ) (s : ℝ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) *
    (Real.exp (-((n : ℝ) + 1) * (n : ℝ) * s) -
      Real.exp (-((n : ℝ) + 1) * ((n : ℝ) + 2) * s))

private def triangleModePrimitive (m s x : ℝ) : ℝ :=
  (Real.exp (-(m ^ 2) * s + m * (2 * x - s)) -
    Real.exp (-(m ^ 2) * s - m * (2 * x - s))) / (2 * m)

private theorem hasDerivAt_triangleModePrimitive {m : ℝ} (hm : m ≠ 0) (s x : ℝ) :
    HasDerivAt (triangleModePrimitive m s)
      (Real.exp (-(m ^ 2) * s + m * (2 * x - s)) +
        Real.exp (-(m ^ 2) * s - m * (2 * x - s))) x := by
  have hp : HasDerivAt (fun x : ℝ => -(m ^ 2) * s + m * (2 * x - s)) (2 * m) x := by
    convert! ((((hasDerivAt_id x).const_mul 2).sub_const s).const_mul m).const_add (-(m ^ 2) * s) using 1
    ring
  have hn : HasDerivAt (fun x : ℝ => -(m ^ 2) * s - m * (2 * x - s)) (-2 * m) x := by
    convert! ((((hasDerivAt_id x).const_mul 2).sub_const s).const_mul m).const_sub (-(m ^ 2) * s) using 1
    ring
  convert! (hp.exp.sub hn.exp).div_const (2 * m) using 1
  field_simp
  ring

theorem integral_wedgeTerm_triangle (n : ℕ) (s : ℝ) :
    (∫ x in 0..s, wedgeTerm n x (s - x)) = integratedWedgeTerm n s := by
  let m : ℝ := (n : ℝ) + 1
  have hm : m ≠ 0 := by dsimp only [m]; positivity
  let F : ℝ → ℝ := fun x => Real.exp (-(m ^ 2) * s + m * (2 * x - s)) +
    Real.exp (-(m ^ 2) * s - m * (2 * x - s))
  have heq : (fun x => wedgeTerm n x (s - x)) = fun x => (-1 : ℝ) ^ (n + 1) * F x := by
    funext x
    unfold wedgeTerm F m
    congr 1
    congr 1 <;> congr 1 <;> ring
  have hi : (∫ x in 0..s, F x) = triangleModePrimitive m s s - triangleModePrimitive m s 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => hasDerivAt_triangleModePrimitive hm s x)
      ((show Continuous F by unfold F; fun_prop).intervalIntegrable 0 s)
  rw [heq, intervalIntegral.integral_const_mul, hi]
  have h₁ : -(m ^ 2) * s + m * (2 * s - s) = -m * (m - 1) * s := by ring
  have h₂ : -(m ^ 2) * s - m * (2 * s - s) = -m * (m + 1) * s := by ring
  have h₃ : -(m ^ 2) * s + m * (2 * 0 - s) = -m * (m + 1) * s := by ring
  have h₄ : -(m ^ 2) * s - m * (2 * 0 - s) = -m * (m - 1) * s := by ring
  simp only [triangleModePrimitive, h₁, h₂, h₃, h₄]
  have hn : (n : ℝ) = m - 1 := by dsimp only [m]; ring
  have hn2 : (n : ℝ) + 2 = m + 1 := by dsimp only [m]; ring
  change _ = (-1 : ℝ) ^ (n + 1) / m *
    (Real.exp (-m * (n : ℝ) * s) - Real.exp (-m * ((n : ℝ) + 2) * s))
  rw [hn2, hn]
  field_simp
  ring

theorem continuousOn_wedgeTriangle {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun a => wedgeSeries a (s - a)) (Icc 0 s) := by
  apply (continuousOn_wedgeSeries hs).comp
    (show Continuous (fun a : ℝ => (a, s - a)) by fun_prop).continuousOn
  intro a ha
  exact ⟨ha.1, sub_nonneg.mpr ha.2, by linarith⟩

/-- Uniform geometric domination justifies integrating the actual wedge series
term by term on the closed triangle boundary. -/
theorem wedgeIntegrated_eq_tsum {s : ℝ} (hs : 0 < s) :
    wedgeIntegrated s = s + ∑' n : ℕ, integratedWedgeTerm n s := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 s)
  let F : ℕ → ℝ → ℝ := fun n x => wedgeTerm n x (s - x)
  let C : ℕ → ℝ := fun n => 2 * Real.exp (-(n : ℝ) * s)
  have hF (n : ℕ) : Integrable (F n) μ :=
    ((show Continuous (F n) by unfold F wedgeTerm; fun_prop).intervalIntegrable 0 s).1
  have hbound : ∀ᵐ x ∂μ, ∀ n, ‖F n x‖ ≤ C n := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx n
    exact wedgeTerm_bound hs.le hx.1.le (sub_nonneg.mpr hx.2) (by linarith) n
  have hnorm : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _)) ?_
      ((summable_wedgeBound hs).mul_left (μ.real univ))
    intro n
    calc
      (∫ x, ‖F n x‖ ∂μ) ≤ ∫ _ : ℝ, C n ∂μ :=
        integral_mono_ae (hF n).norm (integrable_const _) (hbound.mono (fun _ h => h n))
      _ = μ.real univ * C n := by rw [integral_const, smul_eq_mul]
  have hG : Integrable (fun x => wedgeSeries x (s - x)) μ :=
    ((continuousOn_wedgeTriangle hs).intervalIntegrable_of_Icc hs.le).1
  have hsum : Integrable (fun x => ∑' n, F n x) μ := by
    convert! hG.sub (integrable_const 1) using 1
    funext x
    simp only [Pi.sub_apply, wedgeSeries, F, add_sub_cancel_left]
  change (∫ x in 0..s, wedgeSeries x (s - x)) = _
  rw [intervalIntegral.integral_of_le hs.le]
  change (∫ x, 1 + ∑' n, F n x ∂μ) = _
  rw [integral_add (integrable_const 1) hsum,
    ← integral_tsum_of_summable_integral_norm hF hnorm]
  have hconst : (∫ _ : ℝ, (1 : ℝ) ∂μ) = s := by
    change (∫ _ in Ioc (0 : ℝ) s, (1 : ℝ)) = s
    simp [hs.le]
  rw [hconst]
  congr 1
  apply tsum_congr
  intro n
  change (∫ x in Ioc (0 : ℝ) s, wedgeTerm n x (s - x)) = _
  rw [← intervalIntegral.integral_of_le hs.le]
  exact integral_wedgeTerm_triangle n s

end BrownianAffine
