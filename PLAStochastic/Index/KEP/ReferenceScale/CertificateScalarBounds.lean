import PLAStochastic.Index.KEP.ReferenceScale.BridgeBudgetData
import PLAStochastic.Index.KEP.ReferenceScale.CertificateCutoffBounds

/-!
# Absolute budgets of the original compact certificate scalar

The second scalar budget has precisely one original second spatial kernel.
Its remaining coefficient is polynomial in the original length and linear in
the first input budget. Cutoff bounds are independent of all layer data.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepCertificateScalar_pointwise_bound {p : ℝ → ℝ → ℝ} {w C r A d s : ℝ}
    (hd : 0 ≤ d) (hA : 0 ≤ A) (_hC : 0 ≤ C) (n : ℕ) {κ : ℝ → ℝ}
    (hκ : |κ s| ≤ A)
    (hK : |kepFixedBridge p w s n 0 w| ≤ C * Real.exp (-r * (n + 1 : ℕ))) :
    |kepCertificateScalar p w d n κ s| ≤ d * A * C * Real.exp (-r * (n + 1 : ℕ)) := by
  unfold kepCertificateScalar
  rw [abs_mul, abs_mul, abs_of_nonneg hd]
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left hκ hd) hK (abs_nonneg _) (by positivity)
  simpa only [mul_assoc] using hh

theorem kepCertificateScalar_norm_bound {p p' q : ℝ → ℝ → ℝ} {w C J r A d : ℝ}
    (H : KepKilledBridgeBudget 1 p p' q w C J r) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (n : ℕ) {κ : ℝ → ℝ}
    (hκ : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ s| ≤ A) :
    kepLogSlopeNorm (kepCertificateScalar p w d n κ) ≤
      2 * d * A * C * Real.exp (-r * (n + 1 : ℕ)) := by
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, H.width_nonneg⟩
  have hw : w ∈ Icc 0 w := ⟨H.width_nonneg, le_rfl⟩
  have hh := kepLogSlopeNorm_uniform (by positivity :
    0 ≤ d * A * C * Real.exp (-r * (n + 1 : ℕ)))
    (fun s hs => kepCertificateScalar_pointwise_bound hd hA hC n (hκ s hs)
      (H.pointwise s hs n 0 h0 w hw))
  simpa only [mul_assoc] using hh

theorem kepCertificateScalarFirst_norm_bound {p p' q : ℝ → ℝ → ℝ} {w C J r A d : ℝ}
    (H : KepKilledBridgeBudget 1 p p' q w C J r) (hd : 0 ≤ d) (hA : 0 ≤ A)
    (n : ℕ) {κ κ' : ℝ → ℝ} (hcκ : Continuous κ) (hcκ' : Continuous κ')
    (hκ : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ s| ≤ A)
    (hκ' : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ' s| ≤ A) :
    kepLogSlopeNorm (kepCertificateScalarFirst p q w d n κ κ') ≤
      d * A * (2 * C + 8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J) *
        Real.exp (-r * (n + 1 : ℕ)) := by
  let K := fun s => kepFixedBridge p w s n 0 w
  let Ds := fun s => kepFixedBridgeSlope p q w s n 0 w
  let E := Real.exp (-r * (n + 1 : ℕ))
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, H.width_nonneg⟩
  have hw : w ∈ Icc 0 w := ⟨H.width_nonneg, le_rfl⟩
  have hKc : Continuous K := (continuous_kepFixedBridge H.continuous_step w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDsc : Continuous Ds := (continuous_kepFixedBridgeSlope H.continuous_step H.continuous_slope w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hKn : kepLogSlopeNorm K ≤ 2 * (C * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs => H.pointwise s hs n 0 h0 w hw)
  have hDsn := H.slope n (Or.inl rfl) (Or.inr rfl)
  have hF := (kepLogSlopeNorm_mul_bound hcκ' hKc hκ').trans
    (mul_le_mul_of_nonneg_left hKn hA)
  have hG := (kepLogSlopeNorm_mul_bound hcκ hDsc hκ).trans
    (mul_le_mul_of_nonneg_left hDsn hA)
  have hs := kepLogSlopeNorm_add_le (F := fun s => κ' s * K s) (G := fun s => κ s * Ds s)
    (hcκ'.mul hKc) (hcκ.mul hDsc)
  change kepLogSlopeNorm (fun s => d * (κ' s * K s + κ s * Ds s)) ≤ _
  rw [kepLogSlopeNorm_const_mul, abs_of_nonneg hd]
  apply (mul_le_mul_of_nonneg_left hs hd).trans
  have hh := mul_le_mul_of_nonneg_left (show
    kepLogSlopeNorm (fun s => κ' s * K s) + kepLogSlopeNorm (fun s => κ s * Ds s) ≤
      A * (2 * (C * E)) + A * (8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J * E) by
        linarith) hd
  convert hh using 1
  dsimp [E]
  ring

theorem kepCertificateScalarSecond_norm_bound {p p' p'' q : ℝ → ℝ → ℝ} {w C J r A d : ℝ}
    (H : KepKilledBridgeBudget 1 p p' q w C J r) (hp'' : Continuous (Function.uncurry p''))
    (hd : 0 ≤ d) (hA : 0 ≤ A) (n : ℕ) {κ κ' κ'' : ℝ → ℝ}
    (hcκ : Continuous κ) (hcκ' : Continuous κ') (hcκ'' : Continuous κ'')
    (hκ : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ s| ≤ A)
    (hκ' : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ' s| ≤ A)
    (hκ'' : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |κ'' s| ≤ A) :
    kepLogSlopeNorm (kepCertificateScalarSecond p p' p'' q w d n κ κ' κ'') ≤
      d * A * (w + (n + 1 : ℕ)) ^ 2 *
        kepLogSlopeNorm (fun s => kepFixedBridgeRight p p'' w s n 0 w) +
      d * A * (2 * C + 16 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J +
        kepBridgeSecondRemainderBudget C J w n) * Real.exp (-r * (n + 1 : ℕ)) := by
  let K := fun s => kepFixedBridge p w s n 0 w
  let Ds := fun s => kepFixedBridgeSlope p q w s n 0 w
  let DDs := fun s => kepFixedBridgeSlopeSecondWard p p' p'' q w 1 s n 0 w
  let DD := fun s => kepFixedBridgeRight p p'' w s n 0 w
  let E := Real.exp (-r * (n + 1 : ℕ))
  let S := w + (n + 1 : ℕ)
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, H.width_nonneg⟩
  have hw : w ∈ Icc 0 w := ⟨H.width_nonneg, le_rfl⟩
  have hKc : Continuous K := (continuous_kepFixedBridge H.continuous_step w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDsc : Continuous Ds := (continuous_kepFixedBridgeSlope H.continuous_step H.continuous_slope w n).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDDsc : Continuous DDs := continuous_kepFixedBridgeSlopeSecondWard H.continuous_step
    H.continuous_spatial hp'' H.continuous_slope w 1 n 0 w
  have hKn : kepLogSlopeNorm K ≤ 2 * (C * E) :=
    kepLogSlopeNorm_uniform (by positivity) (fun s hs => H.pointwise s hs n 0 h0 w hw)
  have hDsn := H.slope n (Or.inl rfl) (Or.inr rfl)
  have hDDsn := H.second hp'' n (Or.inl rfl) (Or.inr rfl)
  have hF := (kepLogSlopeNorm_mul_bound hcκ'' hKc hκ'').trans
    (mul_le_mul_of_nonneg_left hKn hA)
  have hG : kepLogSlopeNorm (fun s => 2 * κ' s * Ds s) ≤
      2 * (A * (8 * C ^ 2 * S ^ 2 * J * E)) := by
    have he : (fun s => 2 * κ' s * Ds s) = fun s => 2 * (κ' s * Ds s) := by funext s; ring
    rw [he, kepLogSlopeNorm_const_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left ((kepLogSlopeNorm_mul_bound hcκ' hDsc hκ').trans
      (mul_le_mul_of_nonneg_left hDsn hA)) (by norm_num)
  have hH := (kepLogSlopeNorm_mul_bound hcκ hDDsc hκ).trans
    (mul_le_mul_of_nonneg_left hDDsn hA)
  have hs := kepLogSlopeNorm_add_six (F₁ := fun s => κ'' s * K s)
    (F₂ := fun s => 2 * κ' s * Ds s) (F₃ := fun s => κ s * DDs s)
    (F₄ := fun _ => 0) (F₅ := fun _ => 0) (F₆ := fun _ => 0)
    (hcκ''.mul hKc) ((hcκ'.const_mul 2).mul hDsc) (hcκ.mul hDDsc)
    continuous_const continuous_const continuous_const
  simp only [add_zero, kepLogSlopeNorm, abs_zero, integral_zero] at hs
  change kepLogSlopeNorm (fun s => d * (κ'' s * K s + 2 * κ' s * Ds s + κ s * DDs s)) ≤ _
  rw [kepLogSlopeNorm_const_mul, abs_of_nonneg hd]
  apply (mul_le_mul_of_nonneg_left hs hd).trans
  have hh := mul_le_mul_of_nonneg_left (show
      kepLogSlopeNorm (fun s => κ'' s * K s) + kepLogSlopeNorm (fun s => 2 * κ' s * Ds s) +
        kepLogSlopeNorm (fun s => κ s * DDs s) ≤ A * (2 * (C * E)) +
        2 * (A * (8 * C ^ 2 * S ^ 2 * J * E)) +
        A * (S ^ 2 * kepLogSlopeNorm DD + kepBridgeSecondRemainderBudget C J w n * E) by
      linarith) hd
  convert hh using 1 <;> first | rfl | (dsimp [S, E, DD]; ring)

end

end PGM
