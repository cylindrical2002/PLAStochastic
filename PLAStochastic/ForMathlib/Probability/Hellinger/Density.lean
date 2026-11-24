import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Hellinger distance for probability densities

The reference measure is explicit. A density is a nonnegative measurable real
function with integral one. Its square root is a unit vector in `L²`; Hellinger
distance is the distance between those vectors, without a factor `1 / sqrt 2`.
All integral formulas below refer to these actual densities.
-/

set_option autoImplicit false

namespace ProbabilityTheory

noncomputable section

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A probability density relative to an explicitly specified measure. -/
structure HellingerDensity (μ : Measure α) where
  density : α → ℝ
  measurable : Measurable density
  nonneg : ∀ x, 0 ≤ density x
  integrable : Integrable density μ
  integral_eq_one : ∫ x, density x ∂μ = 1

namespace HellingerDensity

@[ext] theorem ext (p q : HellingerDensity μ) (h : ∀ x, p.density x = q.density x) : p = q := by
  cases p
  cases q
  cases funext h
  rfl

theorem sqrt_memLp (p : HellingerDensity μ) :
    MemLp (fun x => Real.sqrt (p.density x)) 2 μ := by
  apply (memLp_two_iff_integrable_sq p.measurable.sqrt.aestronglyMeasurable).2
  simpa only [Real.sq_sqrt (p.nonneg _)] using p.integrable

/-- The square-root density as an actual `L²` vector. -/
def root (p : HellingerDensity μ) : Lp ℝ 2 μ :=
  p.sqrt_memLp.toLp (fun x => Real.sqrt (p.density x))

theorem root_ae (p : HellingerDensity μ) :
    p.root =ᵐ[μ] fun x => Real.sqrt (p.density x) :=
  MemLp.coeFn_toLp _

/-- Hellinger distance with the unnormalised convention `H² = ∫ (sqrt p - sqrt q)²`. -/
def hellinger (p q : HellingerDensity μ) : ℝ := dist p.root q.root

@[simp] theorem hellinger_self (p : HellingerDensity μ) : p.hellinger p = 0 :=
  dist_self _

theorem hellinger_nonneg (p q : HellingerDensity μ) : 0 ≤ p.hellinger q :=
  dist_nonneg

theorem hellinger_comm (p q : HellingerDensity μ) : p.hellinger q = q.hellinger p :=
  dist_comm _ _

theorem hellinger_triangle (p q r : HellingerDensity μ) :
    p.hellinger r ≤ p.hellinger q + q.hellinger r := dist_triangle _ _ _

theorem norm_root_sq (p : HellingerDensity μ) : ‖p.root‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  calc
    (∫ x, inner ℝ (p.root x) (p.root x) ∂μ) = ∫ x, p.density x ∂μ := by
      apply integral_congr_ae
      filter_upwards [p.root_ae] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial]
      exact Real.mul_self_sqrt (p.nonneg x)
    _ = 1 := p.integral_eq_one

@[simp] theorem norm_root (p : HellingerDensity μ) : ‖p.root‖ = 1 := by
  have h := p.norm_root_sq
  nlinarith [norm_nonneg p.root]

theorem hellinger_sq (p q : HellingerDensity μ) :
    p.hellinger q ^ 2 =
      ∫ x, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ := by
  rw [hellinger, dist_eq_norm, ← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub p.root q.root, p.root_ae, q.root_ae] with x hsub hp hq
  simp only [hsub, Pi.sub_apply, hp, hq, RCLike.inner_apply, conj_trivial, pow_two]

theorem hellinger_le_two (p q : HellingerDensity μ) : p.hellinger q ≤ 2 := by
  calc
    p.hellinger q ≤ ‖p.root‖ + ‖q.root‖ := by
      simpa only [hellinger, dist_eq_norm] using norm_sub_le p.root q.root
    _ = 2 := by rw [norm_root, norm_root]; norm_num

theorem hellinger_sq_le_two (p q : HellingerDensity μ) : p.hellinger q ^ 2 ≤ 2 := by
  rw [hellinger_sq]
  calc
    (∫ x, (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ∂μ) ≤
        ∫ x, p.density x + q.density x ∂μ := by
      apply integral_mono (p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq
        (p.integrable.add q.integrable)
      intro x
      change (Real.sqrt (p.density x) - Real.sqrt (q.density x)) ^ 2 ≤
        p.density x + q.density x
      have hp := Real.sq_sqrt (p.nonneg x)
      have hq := Real.sq_sqrt (q.nonneg x)
      nlinarith [mul_nonneg (Real.sqrt_nonneg (p.density x))
        (Real.sqrt_nonneg (q.density x))]
    _ = 2 := by rw [integral_add p.integrable q.integrable,
        p.integral_eq_one, q.integral_eq_one]; norm_num

theorem hellinger_eq_zero_iff (p q : HellingerDensity μ) :
    p.hellinger q = 0 ↔ p.density =ᵐ[μ] q.density := by
  constructor
  · intro h
    have he : p.root = q.root := dist_eq_zero.mp h
    filter_upwards [p.root_ae, q.root_ae] with x hp hq
    have hs : Real.sqrt (p.density x) = Real.sqrt (q.density x) := by
      rw [← hp, ← hq, he]
    have := congrArg (fun y : ℝ => y ^ 2) hs
    simpa only [Real.sq_sqrt (p.nonneg x), Real.sq_sqrt (q.nonneg x)] using this
  · intro h
    apply dist_eq_zero.mpr
    apply Lp.ext
    filter_upwards [p.root_ae, q.root_ae, h] with x hp hq hx
    rw [hp, hq, hx]

theorem sqrt_sub_sq_le_abs_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have hpa := Real.sqrt_nonneg a
  have hpb := Real.sqrt_nonneg b
  rcases le_total a b with hab | hba
  · rw [abs_of_nonpos (sub_nonpos.mpr hab)]
    have hs := Real.sqrt_le_sqrt hab
    nlinarith [mul_nonneg hpa (sub_nonneg.mpr hs)]
  · rw [abs_of_nonneg (sub_nonneg.mpr hba)]
    have hs := Real.sqrt_le_sqrt hba
    nlinarith [mul_nonneg hpb (sub_nonneg.mpr hs)]

/-- The square Hellinger distance is at most the `L¹` difference of the densities. -/
theorem hellinger_sq_le_integral_abs (p q : HellingerDensity μ) :
    p.hellinger q ^ 2 ≤ ∫ x, |p.density x - q.density x| ∂μ := by
  rw [hellinger_sq]
  apply integral_mono
    ((p.sqrt_memLp.sub q.sqrt_memLp).integrable_sq)
    ((p.integrable.sub q.integrable).abs)
  intro x
  exact sqrt_sub_sq_le_abs_sub (p.nonneg x) (q.nonneg x)

end HellingerDensity

end

end ProbabilityTheory
