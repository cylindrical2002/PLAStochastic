import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.HittingTime
import Mathlib.Tactic

/-! # An explicit exponential-moment majorant from genuine Gaussian tails -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

/-- A finite constant independent of the law or exit threshold. -/
def subGaussianTailExpBound (θ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (θ + 2*(θ+1)^2)) / (1 - ENNReal.ofReal (Real.exp (-1)))

theorem subGaussianTailExpBound_lt_top (θ : ℝ) : subGaussianTailExpBound θ < ⊤ := by
  apply ENNReal.div_lt_top (by simp)
  apply (tsub_pos_of_lt _).ne'
  exact (ENNReal.ofReal_lt_one).mpr (by simpa only [Real.exp_lt_one_iff] using (by norm_num : (-1 : ℝ) < 0))

/-- A binwise proof gives a common moment bound before integrability is known. -/
theorem lintegral_exp_le_subGaussianTailExpBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (θ * X ω)) ∂μ) ≤ subGaussianTailExpBound θ := by
  let S : ℕ → Set Ω := fun n => {ω | (n : ℝ) ≤ X ω}
  let F : ℕ → Ω → ℝ≥0∞ := fun n => (S n).indicator
    (fun _ => ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1))))
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hX
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hS n)
  have hpoint : (fun ω => ENNReal.ofReal (Real.exp (θ*X ω))) ≤ᵐ[μ]
      (fun ω => ∑' n, F n ω) := by
    filter_upwards [hn] with ω hω
    let n := ⌊X ω⌋₊
    have hlo : (n : ℝ) ≤ X ω := Nat.floor_le hω
    have hhi : X ω ≤ (n : ℝ)+1 := (Nat.lt_floor_add_one _).le
    calc
      _ ≤ ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1))) :=
        ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hhi hθ))
      _ = F n ω := by simp only [F, Set.indicator_of_mem (show ω ∈ S n from hlo)]
      _ ≤ ∑' n, F n ω := ENNReal.le_tsum n
  calc
    _ ≤ ∫⁻ ω, ∑' n, F n ω ∂μ := lintegral_mono_ae hpoint
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1))) * μ (S n) := by
      rw [lintegral_tsum (fun n => (hF n).aemeasurable)]
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (hS n) _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ*((n : ℝ)+1))) *
        ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)) :=
      ENNReal.tsum_le_tsum (fun n => mul_le_mul_right (htail n) _)
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Real.exp (θ+2*(θ+1)^2)) *
        ENNReal.ofReal (Real.exp (-1)) ^ n := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
        ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_add]
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg ((n : ℝ)-4*(θ+1))]
    _ = subGaussianTailExpBound θ := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      rfl

/-- Integrability is a consequence of the finite tail sum, not an input hypothesis. -/
theorem integrable_exp_of_subGaussianTail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)))
    {θ : ℝ} (hθ : 0 ≤ θ) : Integrable (fun ω => Real.exp (θ * X ω)) μ := by
  apply (lintegral_ofReal_ne_top_iff_integrable
    (hX.const_mul θ |>.exp |>.aestronglyMeasurable)
    (Eventually.of_forall fun _ => Real.exp_pos _ |>.le)).mp
  exact (lt_of_le_of_lt (lintegral_exp_le_subGaussianTailExpBound hX hn htail hθ)
    (subGaussianTailExpBound_lt_top θ)).ne

/-- The actual Bochner expectation has the same common finite upper bound. -/
theorem integral_exp_le_subGaussianTailExpBound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) (hn : ∀ᵐ ω ∂μ, 0 ≤ X ω)
    (htail : ∀ n : ℕ, μ {ω | (n : ℝ) ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(n : ℝ)^2/8)))
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∫ ω, Real.exp (θ * X ω) ∂μ) ≤ (subGaussianTailExpBound θ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ => Real.exp_pos _ |>.le)
    (hX.const_mul θ |>.exp |>.aestronglyMeasurable)]
  exact ENNReal.toReal_mono (subGaussianTailExpBound_lt_top θ).ne
    (lintegral_exp_le_subGaussianTailExpBound hX hn htail hθ)

end SwingRepair
