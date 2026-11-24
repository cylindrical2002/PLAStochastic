import Mathlib.Probability.Distributions.Gamma
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Piecewise

/-!
# Classical derivatives of the zero-extended integer Gamma density

The shape is `n + 4` in the twice differentiable statements. The zero endpoint
is checked on both closed half-lines, rather than ignoring its possible jump.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory Set Filter

/-- The existing rate-one Gamma density with positive integer shape. -/
def gammaNatDensity (n : ℕ) : ℝ → ℝ := gammaPDFReal ((n + 1 : ℕ) : ℝ) 1

theorem gammaNatDensity_of_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    gammaNatDensity n x = x ^ n * Real.exp (-x) / n.factorial := by
  unfold gammaNatDensity gammaPDFReal
  rw [if_pos hx]
  push_cast
  rw [Real.Gamma_nat_eq_factorial, add_sub_cancel_right, Real.rpow_natCast,
    Real.one_rpow, one_mul]
  ring

theorem gammaNatDensity_of_neg (n : ℕ) {x : ℝ} (hx : x < 0) :
    gammaNatDensity n x = 0 := by
  simp only [gammaNatDensity, gammaPDFReal, if_neg (not_le.mpr hx)]

theorem gammaNatDensity_succ_of_nonpos (n : ℕ) {x : ℝ} (hx : x ≤ 0) :
    gammaNatDensity (n + 1) x = 0 := by
  rcases lt_or_eq_of_le hx with hx | rfl
  · exact gammaNatDensity_of_neg (n + 1) hx
  · rw [gammaNatDensity_of_nonneg (n + 1) le_rfl]
    simp

theorem gammaNatDensity_nonneg (n : ℕ) (x : ℝ) : 0 ≤ gammaNatDensity n x :=
  gammaPDFReal_nonneg (by positivity) one_pos x

theorem gammaNatDensity_le_one (n : ℕ) (x : ℝ) : gammaNatDensity n x ≤ 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · rw [gammaNatDensity_of_neg n hx]
    exact zero_le_one
  · rw [gammaNatDensity_of_nonneg n hx]
    have hsum : (∑' k : ℕ, x ^ k / (k.factorial : ℝ)) = Real.exp x := by
      rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
    have hb : x ^ n / (n.factorial : ℝ) ≤ Real.exp x := by
      rw [← hsum]
      exact (Real.summable_pow_div_factorial x).le_tsum n (fun k _ => by positivity)
    calc
      x ^ n * Real.exp (-x) / n.factorial =
          (x ^ n / n.factorial) * Real.exp (-x) := by ring
      _ ≤ Real.exp x * Real.exp (-x) :=
        mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp

theorem integrable_gammaNatDensity (n : ℕ) : Integrable (gammaNatDensity n) volume := by
  refine ⟨(measurable_gammaPDFReal _ _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (gammaNatDensity_nonneg n))]
  change (∫⁻ x, gammaPDF ((n + 1 : ℕ) : ℝ) 1 x) < ⊤
  rw [lintegral_gammaPDF_eq_one (by positivity) one_pos]
  exact ENNReal.one_lt_top

theorem integral_gammaNatDensity (n : ℕ) : (∫ x, gammaNatDensity n x) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaNatDensity_nonneg n))
    (measurable_gammaPDFReal _ _).aestronglyMeasurable]
  change (∫⁻ x, gammaPDF ((n + 1 : ℕ) : ℝ) 1 x).toReal = 1
  rw [lintegral_gammaPDF_eq_one (by positivity) one_pos, ENNReal.toReal_one]

theorem continuous_gammaNatDensity (n : ℕ) : Continuous (gammaNatDensity (n + 1)) := by
  classical
  have hc : Continuous (fun x : ℝ => x ^ (n + 1) * Real.exp (-x) / (n + 1).factorial) := by
    fun_prop
  have he : (Ici (0 : ℝ)).piecewise
      (fun x : ℝ => x ^ (n + 1) * Real.exp (-x) / (n + 1).factorial) (fun _ => 0) =
      gammaNatDensity (n + 1) := by
    funext x
    by_cases hx : 0 ≤ x
    · simp only [Set.piecewise, mem_Ici, if_pos hx]
      exact (gammaNatDensity_of_nonneg (n + 1) hx).symm
    · simp only [Set.piecewise, mem_Ici, if_neg hx]
      exact (gammaNatDensity_of_neg (n + 1) (not_le.mp hx)).symm
  rw [← he]
  apply Continuous.piecewise ?_ hc continuous_const
  intro x hx
  rw [frontier_Ici] at hx
  rcases mem_singleton_iff.mp hx with rfl
  simp

set_option backward.isDefEq.respectTransparency.types false in
theorem hasDerivAt_gammaNatDensity (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaNatDensity (n + 2))
      (gammaNatDensity (n + 1) x - gammaNatDensity (n + 2) x) x := by
  have hpoly (z : ℝ) : HasDerivAt
      (fun t : ℝ => t ^ (n + 2) * Real.exp (-t) / (n + 2).factorial)
      (((n + 2 : ℕ) : ℝ) * z ^ (n + 1) * Real.exp (-z) /
        (n + 2).factorial - z ^ (n + 2) * Real.exp (-z) / (n + 2).factorial) z := by
    convert (((hasDerivAt_id z).pow (n + 2)).mul
      ((Real.hasDerivAt_exp (-z)).comp z (hasDerivAt_id z).neg)).div_const
      ((n + 2).factorial : ℝ) using 1 <;>
        first | rfl | (simp only [id_eq, Pi.pow_apply, Function.comp_apply,
          show n + 2 - 1 = n + 1 by omega]; ring)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [gammaNatDensity_of_neg (n + 1) hx, gammaNatDensity_of_neg (n + 2) hx, sub_self]
    apply (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hx] with z hz
    exact gammaNatDensity_of_neg (n + 2) hz
  · have hright : HasDerivWithinAt (gammaNatDensity (n + 2)) 0 (Ici 0) 0 := by
      have h := (hpoly 0).hasDerivWithinAt (s := Ici 0)
      simp only [zero_pow (by omega : n + 1 ≠ 0), zero_pow (by omega : n + 2 ≠ 0),
        mul_zero, zero_mul, zero_div, sub_zero] at h
      exact h.congr (fun z hz => gammaNatDensity_of_nonneg (n + 2) hz)
        (gammaNatDensity_of_nonneg (n + 2) le_rfl)
    have hleft : HasDerivWithinAt (gammaNatDensity (n + 2)) 0 (Iic 0) 0 := by
      apply (hasDerivAt_const 0 (0 : ℝ)).hasDerivWithinAt.congr
      · intro z hz
        rcases lt_or_eq_of_le (show z ≤ 0 from hz) with hz | rfl
        · exact gammaNatDensity_of_neg (n + 2) hz
        · rw [gammaNatDensity_of_nonneg (n + 2) le_rfl]; simp
      · rw [gammaNatDensity_of_nonneg (n + 2) le_rfl]; simp
    have h := hleft.union hright
    rw [Iic_union_Ici, hasDerivWithinAt_univ] at h
    simpa [gammaNatDensity_of_nonneg, show n + 1 ≠ 0 by omega,
      show n + 2 ≠ 0 by omega] using h
  · have hd := hpoly x
    have he : ((n + 2 : ℕ) : ℝ) * x ^ (n + 1) * Real.exp (-x) /
        (n + 2).factorial = gammaNatDensity (n + 1) x := by
      rw [gammaNatDensity_of_nonneg (n + 1) hx.le, Nat.factorial_succ]
      push_cast
      field_simp
      ring
    rw [he, ← gammaNatDensity_of_nonneg (n + 2) hx.le] at hd
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact gammaNatDensity_of_nonneg (n + 2) hz.le

def gammaNatFirst (n : ℕ) (x : ℝ) : ℝ :=
  gammaNatDensity (n + 2) x - gammaNatDensity (n + 3) x

def gammaNatSecond (n : ℕ) (x : ℝ) : ℝ :=
  gammaNatDensity (n + 1) x - 2 * gammaNatDensity (n + 2) x + gammaNatDensity (n + 3) x

theorem hasDerivAt_gammaNatFirst (n : ℕ) (x : ℝ) :
    HasDerivAt (gammaNatFirst n) (gammaNatSecond n x) x := by
  convert (hasDerivAt_gammaNatDensity n x).sub (hasDerivAt_gammaNatDensity (n + 1) x)
    using 1 <;> first | rfl | (dsimp [gammaNatSecond]; ring)

theorem abs_gammaNatFirst_le (n : ℕ) (x : ℝ) : |gammaNatFirst n x| ≤ 2 := by
  have h1 := gammaNatDensity_nonneg (n + 2) x
  have h2 := gammaNatDensity_nonneg (n + 3) x
  have h3 := gammaNatDensity_le_one (n + 2) x
  have h4 := gammaNatDensity_le_one (n + 3) x
  rw [gammaNatFirst, abs_le]
  constructor <;> linarith

theorem abs_gammaNatSecond_le (n : ℕ) (x : ℝ) : |gammaNatSecond n x| ≤ 4 := by
  have h1 := gammaNatDensity_nonneg (n + 1) x
  have h2 := gammaNatDensity_nonneg (n + 2) x
  have h3 := gammaNatDensity_nonneg (n + 3) x
  have h4 := gammaNatDensity_le_one (n + 1) x
  have h5 := gammaNatDensity_le_one (n + 2) x
  have h6 := gammaNatDensity_le_one (n + 3) x
  rw [gammaNatSecond, abs_le]
  constructor <;> linarith

theorem integrable_gammaNatFirst (n : ℕ) : Integrable (gammaNatFirst n) volume :=
  (integrable_gammaNatDensity (n + 2)).sub (integrable_gammaNatDensity (n + 3))

theorem integrable_gammaNatSecond (n : ℕ) : Integrable (gammaNatSecond n) volume :=
  ((integrable_gammaNatDensity (n + 1)).sub
    ((integrable_gammaNatDensity (n + 2)).const_mul 2)).add
    (integrable_gammaNatDensity (n + 3))

theorem integral_abs_gammaNatFirst_le (n : ℕ) : (∫ x, |gammaNatFirst n x|) ≤ 2 := by
  calc
    (∫ x, |gammaNatFirst n x|) ≤
        ∫ x, gammaNatDensity (n + 2) x + gammaNatDensity (n + 3) x := by
      apply integral_mono (integrable_gammaNatFirst n).abs
        ((integrable_gammaNatDensity _).add (integrable_gammaNatDensity _))
      intro x
      dsimp [gammaNatFirst]
      simpa only [abs_of_nonneg (gammaNatDensity_nonneg _ _)] using abs_sub
        (gammaNatDensity (n + 2) x) (gammaNatDensity (n + 3) x)
    _ = 2 := by
      rw [integral_add (integrable_gammaNatDensity _) (integrable_gammaNatDensity _)]
      simp only [integral_gammaNatDensity]
      norm_num

theorem integral_abs_gammaNatSecond_le (n : ℕ) : (∫ x, |gammaNatSecond n x|) ≤ 4 := by
  calc
    (∫ x, |gammaNatSecond n x|) ≤
        ∫ x, gammaNatDensity (n + 1) x + 2 * gammaNatDensity (n + 2) x +
          gammaNatDensity (n + 3) x := by
      apply integral_mono (integrable_gammaNatSecond n).abs
        (((integrable_gammaNatDensity _).add
          ((integrable_gammaNatDensity _).const_mul 2)).add (integrable_gammaNatDensity _))
      intro x
      dsimp [gammaNatSecond]
      have ha := abs_add_le (gammaNatDensity (n + 1) x - 2 * gammaNatDensity (n + 2) x)
        (gammaNatDensity (n + 3) x)
      have hb := abs_sub (gammaNatDensity (n + 1) x) (2 * gammaNatDensity (n + 2) x)
      simp only [abs_of_nonneg (gammaNatDensity_nonneg _ _), abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at ha hb
      linarith
    _ = 4 := by
      rw [integral_add (f := fun x => gammaNatDensity (n + 1) x + 2 * gammaNatDensity (n + 2) x)
          (g := gammaNatDensity (n + 3))
          ((integrable_gammaNatDensity _).add ((integrable_gammaNatDensity _).const_mul 2))
          (integrable_gammaNatDensity _),
        integral_add (f := gammaNatDensity (n + 1)) (g := fun x => 2 * gammaNatDensity (n + 2) x)
          (integrable_gammaNatDensity _) ((integrable_gammaNatDensity _).const_mul 2),
        integral_const_mul]
      simp only [integral_gammaNatDensity]
      norm_num

end

end ProbabilityTheory
