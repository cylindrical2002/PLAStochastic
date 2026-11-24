import PLAStochastic.Index.KEP.ReferenceScale.GraphBoundaryBudget

/-!
# The entire finite second graph is paid by one original second kernel

The bulk, both exterior fluxes and every first and second exterior pin are
included. All first-derivative costs are in the explicit polynomial coefficient;
the original second-kernel term alone keeps its separate exterior factor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepGraphSecondBudget (C J w S A A' A'' : ℝ) (i r : ℕ) : ℝ :=
  4 * (4 * A + 3 * A' + A'') +
    8 * (i + r : ℕ) * (w + (i + r : ℕ)) * C * (2 * A + A') +
    2 * (i + r : ℕ) * kepGraphUniformPinBudget C J S A A'

theorem kepFiniteGraphSecond_killed_bound {w C J rate D S A A' A'' K I B : ℝ}
    {pA pA' qA pB pB' qB : ℝ → ℝ → ℝ}
    (HA : KepKilledBridgeBudget (-1) pA pA' qA w C J rate)
    (HB : KepKilledBridgeBudget 1 pB pB' qB w C J rate)
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hA' : 0 ≤ A') (_hA'' : 0 ≤ A'')
    (_hK : 0 ≤ K) (_hI : 0 ≤ I) (hB : 0 ≤ B)
    (L i r : ℕ) (hSlen : w + (i + r + 1 : ℕ) ≤ S)
    {R R' R'' φ : ℝ → ℝ} (hcR : Continuous R) (hcR' : Continuous R')
    (hcR'' : Continuous R'') (hφ : Continuous φ)
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2), |R s| ≤ A * Real.exp (-rate * (L : ℝ)))
    (hR' : kepLogSlopeNorm R' ≤ A' * Real.exp (-rate * (L : ℝ)))
    (hR'' : kepLogSlopeNorm R'' ≤ A'' * Real.exp (-rate * (L : ℝ)) + K * I)
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput D i r 0 w s u v)| ≤ B) :
    |kepLogGraphIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w
        (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2) φ +
      kepLogGraphFluxIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w
        (kepGraphTransferredScalar D R R') φ +
      kepGraphBoundarySum i r w
        (kepGraphLeftPinRemainder pA qA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ)
        (kepGraphRightPinRemainder pA pB qB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ)| ≤
      (1 + C * w) ^ 2 * B * (4 * K * I * Real.exp (-rate * (i + r : ℕ)) +
        kepGraphSecondBudget C J w S A A' A'' i r * Real.exp (-rate * (L + i + r : ℕ))) := by
  let E := Real.exp (-rate * (L : ℝ))
  let F := Real.exp (-rate * (i + r : ℕ))
  let T := (1 + C * w) ^ 2 * B
  let V := fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / D ^ 2
  let U := kepGraphTransferredScalar D R R'
  let G0 := kepLogGraphIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w V φ
  let G1 := kepLogGraphFluxIntegral pA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w U φ
  let G2 := kepGraphBoundarySum i r w
    (kepGraphLeftPinRemainder pA qA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ)
    (kepGraphRightPinRemainder pA pB qB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ)
  have hw := HA.width_nonneg
  have hC : 0 ≤ C := by have := HA.constant_ge_one; linarith
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hwb : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
  have hRn : kepLogSlopeNorm R ≤ 2 * (A * E) := kepLogSlopeNorm_uniform (by positivity) hR
  have hVc : Continuous V := by dsimp [V]; fun_prop
  have hUc : Continuous U := by
    change Continuous (fun s => Real.exp s * (R s + R' s) / D)
    fun_prop
  have hVn : kepLogSlopeNorm V ≤ 4 * ((4 * A + 3 * A' + A'') * E + K * I) := by
    apply (kepGraphSecondScalar_norm_bound hcR hcR' hcR'' hD).trans
    have hh : 2 * kepLogSlopeNorm R + 3 * kepLogSlopeNorm R' + kepLogSlopeNorm R'' ≤
        (4 * A + 3 * A' + A'') * E + K * I := by nlinarith only [hRn, hR', hR'']
    exact mul_le_mul_of_nonneg_left hh (by norm_num)
  have hUn : kepLogSlopeNorm U ≤ 2 * (2 * A + A') * E := by
    apply (kepGraphTransferredScalar_norm_bound hcR hcR' hD).trans
    nlinarith only [hRn, hR']
  have hG0 : |G0| ≤ T * F * (4 * ((4 * A + 3 * A' + A'') * E + K * I)) := by
    have hh := kepLogGraphIntegral_killed_bound HA.continuous_step HB.continuous_step
      hw hC hB HA.pointwise HB.pointwise i r h0 hwb hVc hφ hTest
    exact hh.trans (mul_le_mul_of_nonneg_left hVn (by positivity))
  have hG1 : |G1| ≤ (4 * (i + r : ℕ) * (w + (i + r : ℕ)) * T * C * F) *
      (2 * (2 * A + A') * E) := by
    have hh := kepLogGraphFluxIntegral_killed_bound HA.continuous_step HB.continuous_step
      hw hC hB hD HA.pointwise HB.pointwise i r h0 hwb hUc hφ hTest
    have hm := mul_le_mul_of_nonneg_left hUn (by positivity : 0 ≤
      4 * (i + r : ℕ) * (w + (i + r : ℕ)) * (1 + C * w) ^ 2 * C * B * F)
    exact (hh.trans hm).trans_eq (by dsimp [T]; ring)
  have hG2 : |G2| ≤ 2 * (i + r : ℕ) *
      (T * kepGraphUniformPinBudget C J S A A' * Real.exp (-rate * (L + i + r : ℕ))) :=
    kepGraphBoundarySum_uniform_bound
      (fun l hl b hb => kepGraphLeftPinRemainder_uniform_bound HA HB hD hA hA' hB
        L i r l hl hSlen hb hcR hcR' hφ hR hR' hTest)
      (fun l hl b hb => kepGraphRightPinRemainder_uniform_bound HA HB hD hA hA' hB
        L i r l hl hSlen hb hcR hcR' hφ hR hR' hTest)
  have he : E * F = Real.exp (-rate * (L + i + r : ℕ)) := by
    rw [kep_length_exp_product, ← Nat.add_assoc]
  have hsum : |G0 + G1 + G2| ≤ |G0| + |G1| + |G2| := by
    have h1 := abs_add_le G0 G1
    have h2 := abs_add_le (G0 + G1) G2
    linarith
  apply hsum.trans
  calc
    _ ≤ T * F * (4 * ((4 * A + 3 * A' + A'') * E + K * I)) +
        (4 * (i + r : ℕ) * (w + (i + r : ℕ)) * T * C * F) * (2 * (2 * A + A') * E) +
        2 * (i + r : ℕ) * (T * kepGraphUniformPinBudget C J S A A' * (E * F)) := by
      rw [he]
      exact add_le_add (add_le_add hG0 hG1) hG2
    _ = T * (4 * K * I * F + kepGraphSecondBudget C J w S A A' A'' i r * (E * F)) := by
      unfold kepGraphSecondBudget
      ring
    _ = _ := by rw [he]

end

end PGM
