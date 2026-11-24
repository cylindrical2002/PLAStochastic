import PLAStochastic.Index.KEP.ReferenceScale.FiniteGraphSecondBudget
import PLAStochastic.Index.KEP.ReferenceScale.ActualCertificateTransfer

/-!
# The complete finite second graph budget on the actual reference orbit

The original cutoff, coefficient derivatives, killed class data, all exterior
pins and their further fluxes are paid without analytic hypotheses. The only
remaining second-kernel norm is on the original selected bridge. The physical
exponential test weight uses the unchanged output coordinate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_finite_second_graph_uniform :
    ∃ C κ A eps0 : ℝ, 1 ≤ C ∧ 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ A ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ i r n : ℕ,
        let w := 2 * eps
        let d := (n + 1 : ℕ) - w
        1 ≤ d → ∀ theta c B : ℝ, 0 ≤ theta → 0 < c → 0 ≤ B →
        ∀ φ : ℝ → ℝ, Continuous φ →
          (∀ t, 0 ≤ t → |φ t| ≤ B * Real.exp (theta * t / c)) →
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        let p := kepLogStep f 1
        let p'' := kepLogStepSecond f'' 1
        let L := n + 1
        let k := i + r + L
        let S := w + (k + 1 : ℕ)
        let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
        let rate := κ / (2 * w ^ 2)
        let A0 := d * A * C
        let A1 := d * A * (2 * C + 8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J)
        let A2 := d * A * (2 * C + 16 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J +
          kepBridgeSecondRemainderBudget C J w n)
        let K2 := d * A * (w + (n + 1 : ℕ)) ^ 2
        let I2 := kepLogSlopeNorm (fun s => kepFixedBridgeRight p p'' w s n 0 w)
        |kepCertificateSecondGraph f f' f'' eps d i r n φ| ≤
          (1 + C * w) ^ 2 * (B * Real.exp (2 * theta * ((k : ℝ) + w) / c)) *
            (4 * K2 * I2 * Real.exp (-rate * (i + r : ℕ)) +
              kepGraphSecondBudget C J w S A0 A1 A2 i r * Real.exp (-rate * (L + i + r : ℕ))) := by
  obtain ⟨C, κ, e0, hC, hκ, hκ1, he0, hbudget⟩ := kepReference_killed_bridge_budget_uniform
  obtain ⟨A, hA, hcut⟩ := kepCertificateLogCutoff_uniform_bounds
  refine ⟨C, κ, A, e0, hC, hκ, hκ1, hA, he0, ?_⟩
  intro eps he heps j hj i r n
  dsimp only
  intro hd theta c B htheta hc hB φ hφ hφweight
  let w := 2 * eps
  let d := (n + 1 : ℕ) - w
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let pA := kepLogStep f (-1)
  let pB := kepLogStep f 1
  let qA := kepLogStepSlope f f' (-1)
  let qB := kepLogStepSlope f f' 1
  let rate := κ / (2 * w ^ 2)
  let J := Real.sqrt (1 + kepReferenceSecondNorm eps j)
  let R := kepCertificateScalar pB w d n kepCertificateLogCutoff
  let R' := kepCertificateScalarFirst pB qB w d n kepCertificateLogCutoff (deriv kepCertificateLogCutoff)
  let R'' := kepCertificateScalarSecond pB (kepLogStepFirst f' 1) (kepLogStepSecond f'' 1)
    qB w d n kepCertificateLogCutoff (deriv kepCertificateLogCutoff) (deriv (deriv kepCertificateLogCutoff))
  let k := i + r + (n + 1)
  let A0 := d * A * C
  let A1 := d * A * (2 * C + 8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J)
  let A2 := d * A * (2 * C + 16 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J +
    kepBridgeSecondRemainderBudget C J w n)
  let K2 := d * A * (w + (n + 1 : ℕ)) ^ 2
  let I2 := kepLogSlopeNorm (fun s => kepFixedBridgeRight pB (kepLogStepSecond f'' 1) w s n 0 w)
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hw : 2 ≤ w := by dsimp [w]; linarith
  have hw0 : 0 ≤ w := by linarith
  have hd0 : 0 ≤ d := by change 1 ≤ d at hd; linarith
  have hA0 : 0 ≤ A := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := Real.sqrt_nonneg _
  have HA := hbudget eps he heps j hj (-1) (Or.inr rfl) w hw
  have HB := hbudget eps he heps j hj 1 (Or.inl rfl) w hw
  have hκc := kepCertificateLogCutoff_C2
  have hκ0 (s : ℝ) (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) := (hcut s hs).1
  have hκ1' (s : ℝ) (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) := (hcut s hs).2.1
  have hκ2 (s : ℝ) (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) := (hcut s hs).2.2
  have hRreg := kepReference_certificateScalar_C2 heps hj hκc.1 hκc.2.1 hκc.2.2.1
    hκc.2.2.2.1 hκc.2.2.2.2 hw0 d n
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw0⟩
  have hwb : w ∈ Icc 0 w := ⟨hw0, le_rfl⟩
  have hRb (s : ℝ) (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2)) :
      |R s| ≤ A0 * Real.exp (-rate * (n + 1 : ℕ)) :=
    kepCertificateScalar_pointwise_bound hd0 hA0 hC0 n (hκ0 s hs) (HB.pointwise s hs n 0 h0 w hwb)
  have hR'n : kepLogSlopeNorm R' ≤ A1 * Real.exp (-rate * (n + 1 : ℕ)) :=
    kepCertificateScalarFirst_norm_bound HB hd0 hA0 n hκc.1 hκc.2.1 hκ0 hκ1'
  have hcf'' := (kepReferenceDensity_classical heps hj).2.2.2.1
  have hpp'' := continuous_kepLogStepSecond hcf'' 1
  have hR''n : kepLogSlopeNorm R'' ≤ A2 * Real.exp (-rate * (n + 1 : ℕ)) + K2 * I2 := by
    have hh := kepCertificateScalarSecond_norm_bound HB hpp'' hd0 hA0 n
      hκc.1 hκc.2.1 hκc.2.2.1 hκ0 hκ1' hκ2
    change kepLogSlopeNorm R'' ≤ K2 * I2 + A2 * Real.exp (-rate * (n + 1 : ℕ)) at hh
    linarith only [hh]
  have hrem : 0 ≤ kepBridgeSecondRemainderBudget C J w n := by
    unfold kepBridgeSecondRemainderBudget
    positivity
  have hkw : w ≤ (k : ℝ) := by
    have hn : (n + 1 : ℕ) ≤ k := by dsimp [k]; omega
    have hn' : (n + 1 : ℕ) ≤ (k : ℝ) := by exact_mod_cast hn
    linarith
  have hSlen : w + (i + r + 1 : ℕ) ≤ w + (k + 1 : ℕ) := by
    have hh : i + r + 1 ≤ k + 1 := by dsimp [k]; omega
    have hh' : ((i + r + 1 : ℕ) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast hh
    linarith
  have hTest := kepCertificateGraphOutput_weight hw0 hkw (d := d) (i := i) (r := r)
    (n := n) (k := k) rfl rfl htheta hc hφweight
  have hh := kepFiniteGraphSecond_killed_bound HA HB hd
    (by dsimp [A0]; positivity) (by dsimp [A1]; positivity)
    (by dsimp [A2]; positivity) (by dsimp [K2]; positivity)
    (kepLogSlopeNorm_nonneg _) (by positivity : 0 ≤ B * Real.exp (2 * theta * ((k : ℝ) + w) / c))
    (n + 1) i r hSlen hRreg.1 hRreg.2.1 hRreg.2.2.1 hφ hRb hR'n hR''n hTest
  exact hh

end

end PGM
