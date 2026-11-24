import PLAStochastic.Index.CEPS.Inversion.Sobolev
import PLAStochastic.Index.CEPS.Family.Projection

/-! # Mass and moment readout from a weighted density expansion -/

noncomputable section

open MeasureTheory Filter Topology Finset

namespace PGM

/-- The order-zero Sobolev information needed for integrating fixed tests. -/
def CepsInversionWeightedExpansion (F : ℝ → ℝ → ℝ) (g : ℕ → ℝ → ℝ) : Prop :=
  ∀ P : ℕ, ∃ η : ℝ, 0 < η ∧ (∀ k ≤ P, CepsSobolevClass 0 η (g k)) ∧
    (∀ᶠ eps in atTop, CepsSobolevClass 0 η (F eps)) ∧
    IsInverseOrder (fun eps => cepsSobolev 0 η (cepsInversionRemainder F g P eps)) (P + 1)

/-- Every measurable test absorbed by each positive exponential weight can be integrated
against the expansion. In particular, the mass and the first moment are valid tests. -/
theorem CepsInversionWeightedExpansion.test_hasInverseExpansion {F : ℝ → ℝ → ℝ}
    {g : ℕ → ℝ → ℝ} (h : CepsInversionWeightedExpansion F g) {T : ℝ → ℝ}
    (hT : AEStronglyMeasurable T)
    (hbound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |T x| ≤ C * Real.exp (η * |x|)) :
    HasInverseExpansion (fun eps => ∫ x, T x * F eps x) (fun k => ∫ x, T x * g k x) := by
  intro P
  obtain ⟨η, hη, hg, hF, hrem⟩ := h P
  obtain ⟨C, hC, hCbound⟩ := hbound η hη
  obtain ⟨K, E, hK⟩ := hrem
  obtain ⟨Ef, hEf⟩ := eventually_atTop.mp hF
  refine ⟨C * K, max E Ef, fun eps heps => ?_⟩
  have hef := hEf eps ((le_max_right _ _).trans heps)
  have htest {f : ℝ → ℝ} (hf : CepsSobolevClass 0 η f) : Integrable (fun x => T x * f x) :=
    integrable_mul_of_abs_le_expWeight hT hf.continuous.aestronglyMeasurable hCbound hf.integrable_zero
  have hiF := htest hef
  have hig : ∀ k ∈ range (P + 1), Integrable (fun x => T x * g k x) :=
    fun k hk => htest (hg k (by have := mem_range.mp hk; omega))
  let R := cepsInversionRemainder F g P eps
  have hRweight : Integrable (fun x => Real.exp (η * |x|) * R x) := by
    have hsplit : (fun x => Real.exp (η * |x|) * R x) = fun x => Real.exp (η * |x|) * F eps x -
        ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * (Real.exp (η * |x|) * g k x) := by
      funext x
      dsimp [R, cepsInversionRemainder]
      rw [mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun _ _ => by ring
    rw [hsplit]
    exact hef.integrable_zero.sub (integrable_finsetSum _ fun k hk =>
      ((hg k (by have := mem_range.mp hk; omega)).integrable_zero).const_mul _)
  have hsplit : ∫ x, T x * R x = (∫ x, T x * F eps x) -
      inversePolynomial (fun k => ∫ x, T x * g k x) P eps := by
    have heq : (fun x => T x * R x) = fun x => T x * F eps x -
        ∑ k ∈ range (P + 1), (eps⁻¹) ^ k * (T x * g k x) := by
      funext x
      dsimp [R, cepsInversionRemainder]
      rw [mul_sub, mul_sum]
      congr 1
      exact sum_congr rfl fun _ _ => by ring
    rw [heq, integral_sub hiF (integrable_finsetSum _ fun k hk => (hig k hk).const_mul _),
      integral_finsetSum _ (fun k hk => (hig k hk).const_mul _)]
    simp only [integral_const_mul, inversePolynomial]
    congr 1
    exact sum_congr rfl fun _ _ => mul_comm _ _
  have hb := abs_integral_mul_le_expWeighted hCbound hRweight
  have hl := integral_expWeighted_abs_le_cepsSobolev 0 η R
  have hk := hK eps ((le_max_left _ _).trans heps)
  rw [abs_of_nonneg (cepsSobolev_nonneg _ _ _)] at hk
  rw [← hsplit]
  exact hb.trans ((mul_le_mul_of_nonneg_left hl hC).trans
    ((mul_le_mul_of_nonneg_left hk hC).trans_eq (by ring)))

/-- A test with constant value along the actual family has no positive-order coefficients. -/
theorem CepsInversionWeightedExpansion.test_coefficients_of_constant {F : ℝ → ℝ → ℝ}
    {g : ℕ → ℝ → ℝ} (h : CepsInversionWeightedExpansion F g) {T : ℝ → ℝ}
    (hT : AEStronglyMeasurable T)
    (hbound : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |T x| ≤ C * Real.exp (η * |x|))
    {q : ℝ} (hq : ∀ᶠ eps in atTop, (∫ x, T x * F eps x) = q) :
    (∫ x, T x * g 0 x) = q ∧ ∀ k : ℕ, 1 ≤ k → (∫ x, T x * g k x) = 0 := by
  have ha := h.test_hasInverseExpansion hT hbound
  obtain ⟨E, hE⟩ := eventually_atTop.mp hq
  have hb : HasInverseExpansion (fun eps => ∫ x, T x * F eps x) (fun k => if k = 0 then q else 0) := by
    intro P
    refine ⟨0, E, fun eps he => ?_⟩
    simp [hE eps he, inversePolynomial]
  have heq := ha.unique hb
  refine ⟨by simpa using congrFun heq 0, fun k hk => ?_⟩
  simpa only [if_neg (show k ≠ 0 by omega)] using congrFun heq k

/-- Probability normalization forces zero mass in every positive-order coefficient. -/
theorem CepsInversionWeightedExpansion.mass_coefficients {F : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (h : CepsInversionWeightedExpansion F g) (hmass : ∀ᶠ eps in atTop, (∫ x, F eps x) = 1) :
    (∫ x, g 0 x) = 1 ∧ ∀ k : ℕ, 1 ≤ k → (∫ x, g k x) = 0 := by
  have htest : ∀ η : ℝ, 0 < η → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |(1 : ℝ)| ≤ C * Real.exp (η * |x|) := by
    intro η hη
    exact ⟨1, by norm_num, fun x => by simpa only [abs_one, one_mul] using Real.one_le_exp (by positivity : 0 ≤ η * |x|)⟩
  simpa only [one_mul] using h.test_coefficients_of_constant (T := fun _ => 1) (by fun_prop) htest
    (by simpa only [one_mul] using hmass)

/-- Constant first moment is a separate hypothesis, independent of probability normalization. -/
theorem CepsInversionWeightedExpansion.firstMoment_coefficients {F : ℝ → ℝ → ℝ} {g : ℕ → ℝ → ℝ}
    (h : CepsInversionWeightedExpansion F g) {q : ℝ}
    (hmean : ∀ᶠ eps in atTop, (∫ x : ℝ, x * F eps x) = q) :
    (∫ x : ℝ, x * g 0 x) = q ∧ ∀ k : ℕ, 1 ≤ k → (∫ x : ℝ, x * g k x) = 0 := by
  apply h.test_coefficients_of_constant (by fun_prop) _ hmean
  intro η hη
  refine ⟨η⁻¹, (inv_pos.mpr hη).le, fun x => ?_⟩
  simpa only [pow_one, Nat.factorial_one, Nat.cast_one, one_div] using
    Real.pow_le_factorial_inv_mul_exp 1 hη (abs_nonneg x)

end PGM
