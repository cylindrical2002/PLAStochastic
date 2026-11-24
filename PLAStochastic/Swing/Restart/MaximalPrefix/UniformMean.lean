import PLAStochastic.Swing.Restart.MaximalPrefix.Length
import PLAStochastic.ForMathlib.Probability.Moments.NatGeometricBlockTail

/-! # Uniform mean of the actual maximal native prefix with arbitrary carried value -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set
open scoped NNReal ENNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

/-- Finite real-valued representative of the actual maximal prefix.
The zero default on infinite paths is removed almost surely by the proved block bound. -/
def nativePrefixLengthNat (D : ℕ → Ω → ℝ) (Q : Ω → ℝ) (E : ℝ) (ω : Ω) : ℕ :=
  (nativePrefixLength D Q E ω).untopD 0

theorem nativePrefixLengthNat_measurable (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable (D k)) (hQ : Measurable Q) (E : ℝ) :
    Measurable (nativePrefixLengthNat D Q E) :=
  (nativePrefixLength_measurable D Q hD hQ E).untopD 0

theorem nativePrefixLengthNat_block_tail
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r b : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    μ {ω | (2 * r) * b < nativePrefixLengthNat D Q E ω} ≤ gaussianBlockPass ^ b := by
  apply le_trans _ (nativePrefixLength_three_point_tail hX hi hG D Q hshift hE r b hr)
  apply measure_mono
  intro ω hω
  change ((1 + 2 * r * b : ℕ) : WithTop ℕ) ≤ nativePrefixLength D Q E ω
  change (2 * r) * b < (nativePrefixLength D Q E ω).untopD 0 at hω
  cases hN : nativePrefixLength D Q E ω using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    simp only [hN, WithTop.untopD_coe] at hω
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using!
      (WithTop.coe_le_coe.mpr (show 1 + 2 * r * b ≤ k by omega) :
        ((1 + 2 * r * b : ℕ) : WithTop ℕ) ≤ (k : WithTop ℕ))

/-- Every arbitrary carried native segment has finite mean under actual iid Gaussian increments. -/
theorem nativePrefixLengthNat_integrable
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable (D k)) (hQ : Measurable Q)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    Integrable (fun ω => (nativePrefixLengthNat D Q E ω : ℝ)) μ := by
  have hrpos : 0 < r := by
    have h : 0 < (r : ℝ) := lt_of_lt_of_le (by positivity) hr
    exact_mod_cast h
  exact integrable_natCast_of_geometric_block_tail
    (nativePrefixLengthNat_measurable D Q hD hQ E) (Nat.mul_pos (by decide) hrpos)
    gaussianBlockPass_lt_one (nativePrefixLengthNat_block_tail hX hi hG D Q hshift hE r · hr)

/-- The precise uniform mean bound in the three-point-block lemma. -/
theorem nativePrefixLengthNat_mean_le
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable (D k)) (hQ : Measurable Q)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) (r : ℕ) (hr : 8 * E ^ 2 ≤ (r : ℝ)) :
    (∫ ω, (nativePrefixLengthNat D Q E ω : ℝ) ∂μ) ≤
      2 * (r : ℝ) / (1 - gaussianBlockPass.toReal) := by
  have hrpos : 0 < r := by
    have h : 0 < (r : ℝ) := lt_of_lt_of_le (by positivity) hr
    exact_mod_cast h
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    integral_natCast_le_geometric_block_tail
      (nativePrefixLengthNat_measurable D Q hD hQ E) (Nat.mul_pos (by decide) hrpos)
      gaussianBlockPass_lt_one (nativePrefixLengthNat_block_tail hX hi hG D Q hshift hE r · hr)

/-- Paper convention r_E = ceil(8 E^2), with no free block-size hypothesis remaining. -/
theorem nativePrefixLengthNat_mean_le_ceil
    (hX : ∀ k, Measurable (X k)) (hi : iIndepFun X μ)
    (hG : ∀ k, μ.map (X k) = gaussianReal 0 1)
    (D : ℕ → Ω → ℝ) (Q : Ω → ℝ)
    (hD : ∀ k, Measurable (D k)) (hQ : Measurable Q)
    (hshift : ∀ ω k, D (1 + k) ω = D 1 ω + cumulativeSamples X k ω)
    {E : ℝ} (hE : 0 < E) :
    (∫ ω, (nativePrefixLengthNat D Q E ω : ℝ) ∂μ) ≤
      2 * (⌈8 * E ^ 2⌉₊ : ℝ) / (1 - gaussianBlockPass.toReal) :=
  nativePrefixLengthNat_mean_le hX hi hG D Q hD hQ hshift hE _ (Nat.le_ceil _)

end SwingRepair
