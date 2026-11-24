import PLAStochastic.Index.KEP.ReferenceScale.GraphPinScalarBounds
import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphSecondTransfer

/-!
# The complete remainder of one exterior pin has one first input budget

Both the transferred pin scalar and its further exterior flux keep the exact
combined bridge and tail length. The latter contains all second exterior pins
through the proved two-tail flux bound, including their Dirac suffixes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

theorem kepLogSlopeNorm_exp_div {G : ℝ → ℝ} (hG : Continuous G) {D : ℝ} (hD : 1 ≤ D) :
    kepLogSlopeNorm (fun s => Real.exp s * G s / D) ≤ 2 * kepLogSlopeNorm G := by
  have hD0 : 0 < D := by linarith
  have he : (fun s => Real.exp s * G s / D) = fun s => (Real.exp s / D) * G s := by
    funext s
    ring
  rw [he]
  apply kepLogSlopeNorm_mul_bound (Real.continuous_exp.div_const D) hG
  intro s hs
  rw [abs_of_pos (div_pos (Real.exp_pos _) hD0)]
  apply (div_le_iff₀ hD0).mpr
  have hh := (kep_logSlope_exp_bounds hs).2.1
  linarith

def kepGraphPinRemainderBudget (C J w S A A' : ℝ) (l i r : ℕ) : ℝ :=
  8 * S * A * C +
    4 * S * ((2 * A + A') * C + A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J) +
    16 * (i + r : ℕ) * (w + (i + r : ℕ)) * S * A * C ^ 2

theorem kepGraphPinRemainder_killed_bound {σ w C J r D d S A A' B : ℝ}
    {pA pA' qA pB pB' qB p p' q : ℝ → ℝ → ℝ}
    (HA : KepKilledBridgeBudget (-1) pA pA' qA w C J r)
    (HB : KepKilledBridgeBudget 1 pB pB' qB w C J r)
    (H : KepKilledBridgeBudget σ p p' q w C J r)
    (hD : 1 ≤ D) (hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A) (hA' : 0 ≤ A') (hB : 0 ≤ B)
    (L l i k : ℕ) {x b xA xB : ℝ}
    (hx : x = 0 ∨ x = w) (hb : b = 0 ∨ b = w)
    (hxA : xA ∈ Icc 0 w) (hxB : xB ∈ Icc 0 w)
    {R R' φ : ℝ → ℝ} (hcR : Continuous R) (hcR' : Continuous R') (hφ : Continuous φ)
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |R s| ≤ A * Real.exp (-r * (L : ℝ)))
    (hR' : kepLogSlopeNorm R' ≤ A' * Real.exp (-r * (L : ℝ)))
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput (D + d) i k xA xB s u v)| ≤ B) :
    let U := kepGraphPinScalar p w D d l x b R
    let U' := kepGraphPinScalarFirst p q w D d l x b R R'
    |kepLogGraphIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) (D + d) i k xA xB
        (fun s => Real.exp s * (U s + U' s) / (D + d)) φ +
      kepLogGraphFluxIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) (D + d) i k xA xB U φ| ≤
      (1 + C * w) ^ 2 * B * kepGraphPinRemainderBudget C J w S A A' l i k *
        Real.exp (-r * (L + (l + 1) + (i + k) : ℕ)) := by
  dsimp only
  let U := kepGraphPinScalar p w D d l x b R
  let U' := kepGraphPinScalarFirst p q w D d l x b R R'
  let E := Real.exp (-r * (L + (l + 1) : ℕ))
  let F := Real.exp (-r * (i + k : ℕ))
  let T := (1 + C * w) ^ 2 * B
  let Q := (2 * A + A') * C + A * 8 * C ^ 2 * (w + (l + 1 : ℕ)) ^ 2 * J
  have hw := H.width_nonneg
  have hC : 0 ≤ C := by have := H.constant_ge_one; linarith
  have hJ : 0 ≤ J := by have := H.first_ge_one; linarith
  have hS : 0 ≤ S := hd.trans hdS
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDd : 1 ≤ D + d := by linarith
  have hxband : x ∈ Icc 0 w := by
    rcases hx with rfl | rfl <;> constructor <;> first | rfl | exact hw
  have hbband : b ∈ Icc 0 w := by
    rcases hb with rfl | rfl <;> constructor <;> first | rfl | exact hw
  have hKc := (continuous_kepFixedBridge H.continuous_step w l).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    (f := fun s : ℝ => (s, x, b))
  have hDsc := (continuous_kepFixedBridgeSlope H.continuous_step H.continuous_slope w l).comp
    (continuous_id.prodMk (continuous_const.prodMk continuous_const))
    (f := fun s : ℝ => (s, x, b))
  have hUc : Continuous U := by
    change Continuous (fun s => (d / D) * Real.exp s * R s * kepFixedBridge p w s l x b)
    fun_prop
  have hU'c : Continuous U' := by
    change Continuous (fun s => (d / D) * Real.exp s *
      ((R s + R' s) * kepFixedBridge p w s l x b + R s * kepFixedBridgeSlope p q w s l x b))
    fun_prop
  have hUn : kepLogSlopeNorm U ≤ 4 * S * A * C * E :=
    kepGraphPinScalar_norm_bound H hD hd hdS hA L l hxband hbband hR
  have hU'n : kepLogSlopeNorm U' ≤ 2 * S * Q * E :=
    kepGraphPinScalarFirst_norm_bound H hD hd hdS hA hA' L l hx hb hcR hcR' hR hR'
  have hVn : kepLogSlopeNorm (fun s => Real.exp s * (U s + U' s) / (D + d)) ≤
      2 * (4 * S * A * C + 2 * S * Q) * E := by
    have hs := kepLogSlopeNorm_add_le hUc hU'c
    have hh := kepLogSlopeNorm_exp_div (G := fun s => U s + U' s) (hUc.add hU'c) hDd
    have hm := mul_le_mul_of_nonneg_left (show
        kepLogSlopeNorm (fun s => U s + U' s) ≤ (4 * S * A * C + 2 * S * Q) * E by
      nlinarith only [hs, hUn, hU'n]) (by norm_num : (0 : ℝ) ≤ 2)
    exact hh.trans (by nlinarith only [hm])
  have hI := kepLogGraphIntegral_killed_bound HA.continuous_step HB.continuous_step
    hw hC hB HA.pointwise HB.pointwise i k hxA hxB
    ((Real.continuous_exp.mul (hUc.add hU'c)).div_const (D + d)) hφ hTest
  have hFlux := kepLogGraphFluxIntegral_killed_bound HA.continuous_step HB.continuous_step
    hw hC hB hDd HA.pointwise HB.pointwise i k hxA hxB hUc hφ hTest
  apply (abs_add_le _ _).trans
  calc
    _ ≤ T * F * (2 * (4 * S * A * C + 2 * S * Q) * E) +
        (4 * (i + k : ℕ) * (w + (i + k : ℕ)) * T * C * F) * (4 * S * A * C * E) := by
      apply add_le_add
      · exact hI.trans (mul_le_mul_of_nonneg_left hVn (by positivity))
      · have hm := mul_le_mul_of_nonneg_left hUn (by positivity : 0 ≤
          4 * (i + k : ℕ) * (w + (i + k : ℕ)) * (1 + C * w) ^ 2 * C * B *
            Real.exp (-r * (i + k : ℕ)))
        exact (hFlux.trans hm).trans_eq (by dsimp [T, F]; ring)
    _ = T * kepGraphPinRemainderBudget C J w S A A' l i k * (E * F) := by
      dsimp [kepGraphPinRemainderBudget, Q]
      ring
    _ = _ := by rw [kep_length_exp_product]

end

end PGM
