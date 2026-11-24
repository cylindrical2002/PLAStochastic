import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSecond

/-!
# Class-uniform budgets for the actual long killed row

The energy input in the long-row decomposition is bounded by the probability
mass of the actual row. This retains the killed spectral decay and the extra
geometric decay of the rough remainder, uniformly over the compact slope band.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

def kepLongUniformEnergy (D vlo vhi w : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
    (2 * D) / (killCnu D vlo vhi * (k / 4 : ℕ)))

def kepLongUniformVariation (D vlo vhi w : ℝ) (k : ℕ) : ℝ :=
  (8 * Real.pi * Real.sqrt w +
    8 * Real.pi * Real.sqrt w / (1 - Real.sqrt (1 - killCnu D vlo vhi))) *
      kepLongUniformEnergy D vlo vhi w k

def kepLongUniformRemainder (D vlo vhi w : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (1 - killCnu D vlo vhi) ^ (k / 2) *
    kepLongUniformEnergy D vlo vhi w k

theorem integral_sq_krDens_le_two_D
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (n : ℕ) (x : ℝ) :
    (∫ y, krDens (Icc 0 w) ν f β a' (n + 1) x y ^ 2) ≤ 2 * D := by
  have hD : 0 < D := H.hD
  have hi := kr_integrable_krDens_right ν (β := β) (a := a')
    H.hJ H.hJfin H.hf H.hf0 H.hfD (n + 1) x
  have hi2 := kr_integrable_sq_of_bdd H.hJ H.hJfin
    (measurable_krDens_right ν H.hJ H.hf β a' (n + 1) x)
    (fun y hy => krDens_eq_zero_of_right_notMem ν hy (n + 1) x)
    (abs_krDens_le ν H.hf0 H.hfD (n + 1) x)
  calc
    _ ≤ ∫ y, (2 * D) * krDens (Icc 0 w) ν f β a' (n + 1) x y := by
      apply integral_mono hi2 (hi.const_mul (2 * D))
      intro y
      have h0 := krDens_nonneg ν (J := Icc 0 w) (β := β) (a := a') H.hf0 (n + 1) x y
      have hB := H.krDens_le_two_D (n + 1) x y
      nlinarith
    _ = (2 * D) * krSurv (Icc 0 w) (ν : Measure ℝ) β a' (n + 1) x := by
      rw [integral_const_mul, integral_krDens ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha']
    _ ≤ 2 * D := by
      have h := mul_le_mul_of_nonneg_left
        (krSurv_le_one H.hJ ν β a' (n + 1) x) (by positivity : 0 ≤ 2 * D)
      simpa only [mul_one] using h

theorem kepLongRowEnergy_le_uniform
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (x : ℝ) :
    kepLongRowEnergy ν f D vlo vhi w β a' m k x ≤ kepLongUniformEnergy D vlo vhi w k := by
  unfold kepLongRowEnergy kepLongUniformEnergy
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (mul_nonneg
    (killCnu_pos H.hD H.hvlo H.hvhi).le (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_left (integral_sq_krDens_le_two_D ν H m x)
    (Real.exp_pos _).le

theorem kepLongUniformVariation_nonneg {D vlo vhi w : ℝ} (k : ℕ)
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) :
    0 ≤ kepLongUniformVariation D vlo vhi w k := by
  have hρ := kBVHighStepL2_regLaw_factor_lt_one hD hvlo hvhi
  unfold kepLongUniformVariation
  exact mul_nonneg (add_nonneg (by positivity)
    (div_nonneg (by positivity) (by linarith))) (Real.sqrt_nonneg _)

theorem kepLongUniformRemainder_nonneg (D vlo vhi w : ℝ) (k : ℕ) :
    0 ≤ kepLongUniformRemainder D vlo vhi w k := by
  unfold kepLongUniformRemainder kepLongUniformEnergy
  positivity

theorem kepLongRowVarBudget_le_uniform
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (x : ℝ) :
    kepLongRowVarBudget ν f D vlo vhi w β a' m k x ≤
      kepLongUniformVariation D vlo vhi w k := by
  have hρ := kBVHighStepL2_regLaw_factor_lt_one H.hD H.hvlo H.hvhi
  unfold kepLongRowVarBudget kepLongUniformVariation
  apply mul_le_mul_of_nonneg_left (kepLongRowEnergy_le_uniform ν H m k x)
  exact add_nonneg (by positivity) (div_nonneg (by positivity) (by linarith))

theorem kepLongRowRemBudget_le_uniform
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (m k : ℕ) (x : ℝ) :
    kepLongRowRemBudget ν f D vlo vhi w β a' m k x ≤
      kepLongUniformRemainder D vlo vhi w k := by
  unfold kepLongRowRemBudget kepLongUniformRemainder
  exact mul_le_mul_of_nonneg_left (kepLongRowEnergy_le_uniform ν H m k x) (by positivity)

/-- A simpler exponential envelope keeps both sources of decay. -/
theorem kepLongUniformEnergy_le_exp {D vlo vhi w : ℝ} {k : ℕ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (hk : 4 ≤ k) :
    kepLongUniformEnergy D vlo vhi w k ≤
      Real.sqrt (2 * D / killCnu D vlo vhi) *
        Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / (2 * w ^ 2))) := by
  have hc := killCnu_pos hD hvlo hvhi
  have hk1 : (1 : ℝ) ≤ (k / 4 : ℕ) := by exact_mod_cast (by omega : 1 ≤ k / 4)
  have he : -(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2) =
      -(krKappa D vlo vhi * (k / 4 : ℕ) / (2 * w ^ 2)) * 2 := by ring
  unfold kepLongUniformEnergy
  calc
    _ ≤ Real.sqrt (Real.exp (-(krKappa D vlo vhi * (k / 4 : ℕ) / w ^ 2)) *
        (2 * D / killCnu D vlo vhi)) := by
      apply Real.sqrt_le_sqrt
      rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact div_le_div_of_nonneg_left (by positivity) hc (by nlinarith)
    _ = _ := by
      rw [Real.sqrt_mul (Real.exp_pos _).le, he, Real.exp_mul, Real.rpow_two, Real.sqrt_sq_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_comm]

end

end PGM
