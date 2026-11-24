import PLAStochastic.Index.KEP.ReferenceScale.CertificateScalarBounds
import PLAStochastic.Index.KEP.ReferenceScale.CertificateGraphWeight
import PLAStochastic.Index.KEP.ReferenceScale.GraphSecondTransfer

/-!
# Budgets for the true exterior pin scalar and its first derivative

The differentiated pin scalar uses a differentiated original scalar with an
undifferentiated pin, or an undifferentiated original scalar with a first pin
derivative. There is no product of input derivative norms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kep_length_exp_product (r : ℝ) (L M : ℕ) :
    Real.exp (-r * (L : ℝ)) * Real.exp (-r * (M : ℝ)) = Real.exp (-r * (L + M : ℕ)) := by
  rw [← Real.exp_add, ← mul_add, ← Nat.cast_add]

theorem kep_pin_ratio_bound {D d S : ℝ} (hD : 1 ≤ D) (hd : 0 ≤ d) (hS : d ≤ S) :
    0 ≤ d / D ∧ d / D ≤ S := by
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ d := by rw [div_eq_mul_inv]; simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hD) hd
    _ ≤ S := hS

theorem kepLogSlopeNorm_exp_mul {G : ℝ → ℝ} (hG : Continuous G) :
    kepLogSlopeNorm (fun s => Real.exp s * G s) ≤ 2 * kepLogSlopeNorm G := by
  apply kepLogSlopeNorm_mul_bound Real.continuous_exp hG
  intro s hs
  rw [abs_of_pos (Real.exp_pos s)]
  exact (kep_logSlope_exp_bounds hs).2.1

theorem kepGraphPinScalar_pointwise_bound {σ w C J r D d S A s : ℝ}
    {p p' q : ℝ → ℝ → ℝ} (H : KepKilledBridgeBudget σ p p' q w C J r)
    (hD : 1 ≤ D) (hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A)
    (L l : ℕ) {x b : ℝ} (hx : x ∈ Icc 0 w) (hb : b ∈ Icc 0 w)
    {R : ℝ → ℝ} (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))
    (hR : |R s| ≤ A * Real.exp (-r * (L : ℝ))) :
    |kepGraphPinScalar p w D d l x b R s| ≤
      2 * S * A * C * Real.exp (-r * (L + (l + 1) : ℕ)) := by
  have hr := kep_pin_ratio_bound hD hd hdS
  have hS : 0 ≤ S := hd.trans hdS
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  unfold kepGraphPinScalar
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hr.1, abs_of_pos (Real.exp_pos s)]
  calc
    _ ≤ S * 2 * (A * Real.exp (-r * (L : ℝ))) *
        (C * Real.exp (-r * (l + 1 : ℕ))) := by
      gcongr
      exact hr.2
      exact (kep_logSlope_exp_bounds hs).2.1
      exact H.pointwise s hs l x hx b hb
    _ = 2 * S * A * C *
        (Real.exp (-r * (L : ℝ)) * Real.exp (-r * (l + 1 : ℕ))) := by ring
    _ = _ := by rw [kep_length_exp_product]

theorem kepGraphPinScalar_norm_bound {σ w C J r D d S A : ℝ}
    {p p' q : ℝ → ℝ → ℝ} (H : KepKilledBridgeBudget σ p p' q w C J r)
    (hD : 1 ≤ D) (hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A)
    (L l : ℕ) {x b : ℝ} (hx : x ∈ Icc 0 w) (hb : b ∈ Icc 0 w)
    {R : ℝ → ℝ}
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |R s| ≤ A * Real.exp (-r * (L : ℝ))) :
    kepLogSlopeNorm (kepGraphPinScalar p w D d l x b R) ≤
      4 * S * A * C * Real.exp (-r * (L + (l + 1) : ℕ)) := by
  have hS : 0 ≤ S := hd.trans hdS
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have hh := kepLogSlopeNorm_uniform (by positivity : 0 ≤
    2 * S * A * C * Real.exp (-r * (L + (l + 1) : ℕ)))
    (fun s hs => kepGraphPinScalar_pointwise_bound H hD hd hdS hA L l hx hb hs (hR s hs))
  exact hh.trans_eq (by ring)

theorem kepGraphPinScalarFirst_norm_bound {σ w C J r D d S A A' : ℝ}
    {p p' q : ℝ → ℝ → ℝ} (H : KepKilledBridgeBudget σ p p' q w C J r)
    (hD : 1 ≤ D) (hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A) (_hA' : 0 ≤ A')
    (L l : ℕ) {x b : ℝ} (hx : x = 0 ∨ x = w) (hb : b = 0 ∨ b = w)
    {R R' : ℝ → ℝ} (hcR : Continuous R) (hcR' : Continuous R')
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |R s| ≤ A * Real.exp (-r * (L : ℝ)))
    (hR' : kepLogSlopeNorm R' ≤ A' * Real.exp (-r * (L : ℝ))) :
    kepLogSlopeNorm (kepGraphPinScalarFirst p q w D d l x b R R') ≤
      2 * S * ((2 * A + A') * C + A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J) *
        Real.exp (-r * (L + (l + 1) : ℕ)) := by
  have hS : 0 ≤ S := hd.trans hdS
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have hJ : 0 ≤ J := by have := H.first_ge_one; linarith
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> exact ⟨by first | rfl | exact H.width_nonneg,
      by first | rfl | exact H.width_nonneg⟩
  have hbband : b ∈ Icc 0 w := by
    rcases hb with rfl | rfl <;> exact ⟨by first | rfl | exact H.width_nonneg,
      by first | rfl | exact H.width_nonneg⟩
  let K := fun s => kepFixedBridge p w s l x b
  let Ds := fun s => kepFixedBridgeSlope p q w s l x b
  let F := fun s => (R s + R' s) * K s
  let G := fun s => R s * Ds s
  let E := Real.exp (-r * (L + (l + 1) : ℕ))
  have hKc : Continuous K := (continuous_kepFixedBridge H.continuous_step w l).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hDsc : Continuous Ds := (continuous_kepFixedBridgeSlope H.continuous_step H.continuous_slope w l).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
  have hFc : Continuous F := (hcR.add hcR').mul hKc
  have hGc : Continuous G := hcR.mul hDsc
  have hRn : kepLogSlopeNorm R ≤ 2 * (A * Real.exp (-r * (L : ℝ))) :=
    kepLogSlopeNorm_uniform (by positivity) hR
  have hsum : kepLogSlopeNorm (fun s => R s + R' s) ≤
      (2 * A + A') * Real.exp (-r * (L : ℝ)) := by
    apply (kepLogSlopeNorm_add_le hcR hcR').trans
    nlinarith only [hRn, hR']
  have hFn : kepLogSlopeNorm F ≤ (2 * A + A') * C * E := by
    have he : F = fun s => K s * (R s + R' s) := by funext s; dsimp [F]; ring
    rw [he]
    have hh := (kepLogSlopeNorm_mul_bound hKc (hcR.add hcR')
      (fun s hs => H.pointwise s hs l x hxband b hbband)).trans
      (mul_le_mul_of_nonneg_left hsum (by positivity :
        0 ≤ C * Real.exp (-r * (l + 1 : ℕ))))
    apply hh.trans_eq
    calc
      _ = (2 * A + A') * C * (Real.exp (-r * (L : ℝ)) *
          Real.exp (-r * (l + 1 : ℕ))) := by ring
      _ = _ := by rw [kep_length_exp_product]
  have hGn : kepLogSlopeNorm G ≤ A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J * E := by
    have hh := (kepLogSlopeNorm_mul_bound hcR hDsc hR).trans
      (mul_le_mul_of_nonneg_left (H.slope l hx hb) (by positivity :
        0 ≤ A * Real.exp (-r * (L : ℝ))))
    apply hh.trans_eq
    calc
      _ = A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J *
          (Real.exp (-r * (L : ℝ)) * Real.exp (-r * (l + 1 : ℕ))) := by ring
      _ = _ := by rw [kep_length_exp_product]
  have hFG : kepLogSlopeNorm (fun s => F s + G s) ≤
      ((2 * A + A') * C + A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J) * E := by
    apply (kepLogSlopeNorm_add_le hFc hGc).trans
    nlinarith only [hFn, hGn]
  have he : kepGraphPinScalarFirst p q w D d l x b R R' =
      fun s => (d / D) * (Real.exp s * (F s + G s)) := by
    funext s
    dsimp [kepGraphPinScalarFirst, F, G]
    ring
  have hr := kep_pin_ratio_bound hD hd hdS
  rw [he, kepLogSlopeNorm_const_mul, abs_of_nonneg hr.1]
  calc
    _ ≤ S * kepLogSlopeNorm (fun s => Real.exp s * (F s + G s)) :=
      mul_le_mul_of_nonneg_right hr.2 (kepLogSlopeNorm_nonneg _)
    _ ≤ S * (2 * kepLogSlopeNorm (fun s => F s + G s)) :=
      mul_le_mul_of_nonneg_left (kepLogSlopeNorm_exp_mul (hFc.add hGc)) hS
    _ ≤ S * (2 * (((2 * A + A') * C + A * 8 * C ^ 2 *
        (w + (l + 1 : ℕ)) ^ 2 * J) * E)) := by gcongr
    _ = _ := by ring

end

end PGM
