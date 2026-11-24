import PLAStochastic.Index.KEP.ReferenceScale.LongKernelSummability
import PLAStochastic.ForMathlib.Analysis.SpecialFunctions.PolynomialExponentialSeries

/-!
# Quantitative long-kernel series budgets

The killed rate is of order `w⁻²`. Summing a polynomial length weight therefore
costs a polynomial in the band width, with constants selected before the width,
the slope weight, and the truncation index. The rough second-derivative term
retains its geometric factor at that truncation index.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

def kepLongPolynomialEnergyConstant (D vlo vhi : ℝ) (p : ℕ) : ℝ :=
  (Real.sqrt (2 * D / killCnu D vlo vhi) * Real.exp (krKappa D vlo vhi / 2)) *
    ((p.factorial : ℝ) * Real.exp 1 * (1 + 32 / krKappa D vlo vhi) ^ (p + 1))

theorem kepLongPolynomialEnergyConstant_pos {D vlo vhi : ℝ}
    (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (p : ℕ) :
    0 < kepLongPolynomialEnergyConstant D vlo vhi p := by
  have hc := killCnu_pos hD hvlo hvhi
  have hk := krKappa_pos hD hvlo hvhi
  unfold kepLongPolynomialEnergyConstant
  positivity

/-- A fixed polynomial in the length costs `w^(2p+2)`. -/
theorem tsum_polynomial_weighted_kepLongUniformEnergy_le
    {D vlo vhi w eta : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi)
    (hw : 1 ≤ w) (heta : eta ≤ krKappa D vlo vhi / (16 * w ^ 2)) (p : ℕ) :
    (∑' k : ℕ, (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
      kepLongUniformEnergy D vlo vhi w k) ≤
        kepLongPolynomialEnergyConstant D vlo vhi p * w ^ (2 * (p + 1)) := by
  let κ := krKappa D vlo vhi
  let r := κ / (16 * w ^ 2)
  let B := Real.sqrt (2 * D / killCnu D vlo vhi) * Real.exp (κ / 2)
  have hκ : 0 < κ := krKappa_pos hD hvlo hvhi
  have hw0 : 0 < w := by linarith
  have hr : 0 < r := by dsimp [r]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have heta' : eta < κ / (8 * w ^ 2) := by
    apply heta.trans_lt
    apply div_lt_div_of_pos_left hκ (by positivity)
    nlinarith
  have hs := summable_polynomial_weighted_kepLongUniformEnergy hD hvlo hvhi hw heta' p
  have hsR : Summable (fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (-r * k)) := by
    have h := (summable_nat_add_iff 1).2 (Real.summable_pow_mul_exp_neg_nat_mul p hr)
    convert h.mul_left (Real.exp r) using 1 <;> first
    | rfl
    | (funext k
       rw [Nat.cast_add, Nat.cast_one, mul_left_comm, ← Real.exp_add]
       congr 2
       ring)
  have hb (k : ℕ) :
      (k + 1 : ℝ) ^ p * Real.exp (eta * k) * kepLongUniformEnergy D vlo vhi w k ≤
        B * ((k + 1 : ℝ) ^ p * Real.exp (-r * k)) := by
    calc
      _ ≤ (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
          (B * Real.exp (-(κ / (8 * w ^ 2)) * k)) :=
        mul_le_mul_of_nonneg_left (kepLongUniformEnergy_le_full_exp k hD hvlo hvhi hw)
          (by positivity)
      _ = B * ((k + 1 : ℝ) ^ p * Real.exp ((eta - κ / (8 * w ^ 2)) * k)) := by
        rw [show (eta - κ / (8 * w ^ 2)) * (k : ℝ) =
          eta * k + (-(κ / (8 * w ^ 2))) * k by ring, Real.exp_add]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
        dsimp [r]
        have heq : κ / (8 * w ^ 2) = 2 * (κ / (16 * w ^ 2)) := by ring
        rw [heq]
        linarith
  have hscale : 1 + 2 / r ≤ (1 + 32 / κ) * w ^ 2 := by
    have heq : 2 / r = 32 / κ * w ^ 2 := by
      dsimp [r]
      field_simp
      ring
    rw [heq]
    nlinarith
  calc
    _ ≤ ∑' k : ℕ, B * ((k + 1 : ℝ) ^ p * Real.exp (-r * k)) :=
      hs.tsum_le_tsum hb (hsR.mul_left B)
    _ = B * ∑' k : ℕ, (k + 1 : ℝ) ^ p * Real.exp (-r * k) := tsum_mul_left
    _ ≤ B * ((p.factorial : ℝ) * Real.exp 1 * (1 + 2 / r) ^ (p + 1)) :=
      mul_le_mul_of_nonneg_left (Real.tsum_polynomial_mul_exp_neg_le hr p) hB
    _ ≤ B * ((p.factorial : ℝ) * Real.exp 1 *
        ((1 + 32 / κ) * w ^ 2) ^ (p + 1)) := by
      gcongr
    _ = _ := by
      dsimp [B, κ, kepLongPolynomialEnergyConstant]
      rw [mul_pow, ← pow_mul]
      ring

/-- The long second-derivative budget is polynomial in the width, while its
linear dependence on the input second norm retains the cutoff decay. -/
theorem tsum_polynomial_weighted_kepLongSecondSlopeBudget_tail_le
    {D vlo vhi : ℝ} (hD : 0 < D) (hvlo : 0 < vlo) (hvhi : vlo ≤ vhi) (p : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ w eta : ℝ, 1 ≤ w →
      eta ≤ krKappa D vlo vhi / (16 * w ^ 2) → ∀ N : ℕ, ∀ J1 J2 : ℝ,
      0 ≤ J1 → 0 ≤ J2 →
      (∑' k : ℕ, (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
        kepLongSecondSlopeBudget D vlo vhi w (k + N) J1 J2) ≤
      K * w ^ (2 * p + 4) *
        (J1 + Real.sqrt (1 - killCnu D vlo vhi) ^ (N / 2) * J2) := by
  let ρ := Real.sqrt (1 - killCnu D vlo vhi)
  let V := 8 * Real.pi + 8 * Real.pi / (1 - ρ)
  let A := 10 * D * V
  let B := 6 * Real.sqrt (2 * D)
  let E := kepLongPolynomialEnergyConstant D vlo vhi p
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hρ1 : ρ < 1 := kBVHighStepL2_regLaw_factor_lt_one hD hvlo hvhi
  have hV : 0 < V := by dsimp [V]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hE : 0 < E := kepLongPolynomialEnergyConstant_pos hD hvlo hvhi p
  refine ⟨E * (A + B), by positivity, ?_⟩
  intro w eta hw heta N J1 J2 hJ1 hJ2
  have hκ := krKappa_pos hD hvlo hvhi
  have heta' : eta < krKappa D vlo vhi / (8 * w ^ 2) := by
    apply heta.trans_lt
    apply div_lt_div_of_pos_left hκ (by positivity)
    nlinarith
  let F := fun k : ℕ => (k + 1 : ℝ) ^ p * Real.exp (eta * k) *
    kepLongUniformEnergy D vlo vhi w k
  have hsF : Summable F :=
    summable_polynomial_weighted_kepLongUniformEnergy hD hvlo hvhi hw heta' p
  have hsT : Summable (fun k : ℕ => (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
      kepLongSecondSlopeBudget D vlo vhi w (k + N) J1 J2) := by
    convert (summable_nat_add_iff N).2
      (summable_polynomial_weighted_kepLongSecondSlopeBudget (J1 := J1) (J2 := J2)
        hD hvlo hvhi hw heta' p) using 1 <;> first
    | rfl
    | (funext k; simp only [Nat.cast_add])
  have hsFN : Summable (fun k : ℕ => F (k + N)) := (summable_nat_add_iff N).2 hsF
  have hFN : (∑' k : ℕ, F (k + N)) ≤ E * w ^ (2 * (p + 1)) := by
    apply (tsum_comp_le_tsum_of_inj hsF (fun k => by dsimp [F, kepLongUniformEnergy]; positivity)
      (i := fun k : ℕ => k + N) (fun _ _ h => Nat.add_right_cancel h)).trans
    exact tsum_polynomial_weighted_kepLongUniformEnergy_le hD hvlo hvhi hw heta p
  have hvw : (8 * Real.pi * Real.sqrt w + 8 * Real.pi * Real.sqrt w / (1 - ρ)) *
      (3 + 2 * w) ≤ 5 * V * w ^ 2 := by
    have hsqrt : Real.sqrt w ≤ w := by
      apply Real.sqrt_le_iff.mpr
      constructor <;> nlinarith
    calc
      _ = V * Real.sqrt w * (3 + 2 * w) := by dsimp [V]; ring
      _ ≤ V * w * (5 * w) := by gcongr; linarith
      _ = _ := by ring
  have hb (k : ℕ) : (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
      kepLongSecondSlopeBudget D vlo vhi w (k + N) J1 J2 ≤
        (A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) * F (k + N) := by
    have hpow : ρ ^ ((k + N) / 2) ≤ ρ ^ (N / 2) :=
      pow_le_pow_of_le_one hρ0 hρ1.le (by omega)
    have hbudget : kepLongSecondSlopeBudget D vlo vhi w (k + N) J1 J2 ≤
        (A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) *
          kepLongUniformEnergy D vlo vhi w (k + N) := by
      unfold kepLongSecondSlopeBudget kepLongUniformVariation kepLongUniformRemainder
      dsimp only [A, B]
      have he := Real.sqrt_nonneg
        (Real.exp (-(krKappa D vlo vhi * ((k + N) / 4 : ℕ) / w ^ 2)) *
          (2 * D) / (killCnu D vlo vhi * ((k + N) / 4 : ℕ)))
      change _ ≤ _
      calc
        _ = (2 * D *
          (8 * Real.pi * Real.sqrt w + 8 * Real.pi * Real.sqrt w / (1 - ρ)) *
          (3 + 2 * w) * J1 + 6 * Real.sqrt (2 * D) * ρ ^ ((k + N) / 2) * J2) *
            kepLongUniformEnergy D vlo vhi w (k + N) := by
          dsimp [kepLongUniformEnergy, ρ]
          ring
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ he
          apply add_le_add
          · calc
              _ = 2 * D * ((8 * Real.pi * Real.sqrt w +
                  8 * Real.pi * Real.sqrt w / (1 - ρ)) * (3 + 2 * w)) * J1 := by ring
              _ ≤ 2 * D * (5 * V * w ^ 2) * J1 := by gcongr
              _ = _ := by ring
          · gcongr
    calc
      _ ≤ (k + N + 1 : ℝ) ^ p * Real.exp (eta * (k + N)) *
          ((A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) *
            kepLongUniformEnergy D vlo vhi w (k + N)) := by
        exact mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = _ := by dsimp [F]; simp only [Nat.cast_add]; ring
  calc
    _ ≤ ∑' k : ℕ, (A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) * F (k + N) :=
      hsT.tsum_le_tsum hb (hsFN.mul_left _)
    _ = (A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) * ∑' k : ℕ, F (k + N) := tsum_mul_left
    _ ≤ (A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2) * (E * w ^ (2 * (p + 1))) :=
      mul_le_mul_of_nonneg_left hFN (by positivity)
    _ ≤ _ := by
      have hw2 : 1 ≤ w ^ 2 := by nlinarith
      have hC : A * w ^ 2 * J1 + B * ρ ^ (N / 2) * J2 ≤
          (A + B) * w ^ 2 * (J1 + ρ ^ (N / 2) * J2) := by
        have hR : 0 ≤ ρ ^ (N / 2) * J2 := mul_nonneg (pow_nonneg hρ0 _) hJ2
        have hBW : B * ρ ^ (N / 2) * J2 ≤ B * w ^ 2 * (ρ ^ (N / 2) * J2) := by
          calc
            _ = B * (ρ ^ (N / 2) * J2) * 1 := by ring
            _ ≤ B * (ρ ^ (N / 2) * J2) * w ^ 2 :=
              mul_le_mul_of_nonneg_left hw2 (mul_nonneg hB.le hR)
            _ = _ := by ring
        calc
          _ ≤ A * w ^ 2 * J1 + B * w ^ 2 * (ρ ^ (N / 2) * J2) :=
            add_le_add le_rfl hBW
          _ ≤ (A + B) * w ^ 2 * J1 + (A + B) * w ^ 2 * (ρ ^ (N / 2) * J2) := by
            apply add_le_add
            · gcongr; linarith
            · gcongr; linarith
          _ = _ := by ring
      calc
        _ ≤ ((A + B) * w ^ 2 * (J1 + ρ ^ (N / 2) * J2)) *
            (E * w ^ (2 * (p + 1))) := by gcongr
        _ = _ := by
          rw [show 2 * p + 4 = 2 + 2 * (p + 1) by omega, pow_add]
          ring

end

end PGM
