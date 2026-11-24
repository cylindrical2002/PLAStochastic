import PLAStochastic.Index.KEP.ReferenceScale.CertificateGraph
import PLAStochastic.Index.KEP.ReferenceScale.CertificateCutoff
import PLAStochastic.Index.KEP.ReferenceScale.ActualGraphSecondTransfer

/-!
# Second derivative transfer for the original iid certificate

The left side is the original selected-pair event and physical prefix sum.
The right side contains only the undifferentiated test. The actual density,
coarea, exterior independence, bridge smoothness and cutoff endpoint conditions
are all discharged; the remaining task is to estimate and sum these terms.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kepReferenceLaw_Iic_zero {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {j : ℕ} (hj : 1 ≤ j) :
    (kepReferenceLaw eps j : Measure ℝ) (Iic 0) = 0 := by
  rw [← kepReferenceDensity_toMeasure heps hj]
  change volume.withDensity (fun x => ENNReal.ofReal
    ((kepReferenceDensity heps hj).density x)) (Iic 0) = 0
  rw [withDensity_apply _ measurableSet_Iic]
  refine (setLIntegral_congr_fun measurableSet_Iic (g := fun _ => (0 : ℝ≥0∞)) ?_).trans
    (by simp)
  intro x hx
  dsimp only
  rw [(kepReferenceDensity_classical heps hj).1 x hx, ENNReal.ofReal_zero]

def kepCertificateSecondGraph (f f' f'' : ℝ → ℝ) (eps d : ℝ) (i r n : ℕ)
    (φ : ℝ → ℝ) : ℝ :=
  let w := 2 * eps
  let lo := Real.log (1 / 2)
  let hi := Real.log 2
  let pA := kepLogStep f (-1)
  let pB := kepLogStep f 1
  let qA := kepLogStepSlope f f' (-1)
  let qB := kepLogStepSlope f f' 1
  let κ := kepCertificateLogCutoff
  let R := kepCertificateScalar pB w d n κ
  let R' := kepCertificateScalarFirst pB qB w d n κ (deriv κ)
  let R'' := kepCertificateScalarSecond pB (kepLogStepFirst f' 1) (kepLogStepSecond f'' 1)
    qB w d n κ (deriv κ) (deriv (deriv κ))
  kepLogGraphIntegral pA pB w lo hi d i r 0 w
    (fun s => Real.exp (2 * s) * (2 * R s + 3 * R' s + R'' s) / d ^ 2) φ +
    kepLogGraphFluxIntegral pA pB w lo hi d i r 0 w
      (kepGraphTransferredScalar d R R') φ +
    kepGraphBoundarySum i r w
      (kepGraphLeftPinRemainder pA qA pB w lo hi d i r 0 w R R' φ)
      (kepGraphRightPinRemainder pA pB qB w lo hi d i r 0 w R R' φ)

/-- Exact finite second transfer with the fixed, proved smooth cutoff.
No Ward, graph, density, or cutoff regularity hypothesis remains. -/
theorem kepReference_certificate_second_transfer {eps : ℝ}
    (heps : kepReferenceClassicalThreshold ≤ eps) {layer : ℕ} (hlayer : 1 ≤ layer)
    {k i j L : ℕ} (hij : i < j) (hL : i + L = j) (hjk : j ≤ k)
    (hd : 0 < (L : ℝ) - 2 * eps) (n : ℕ) (hn : L = n + 1)
    {φ φ' φ'' : ℝ → ℝ} (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφ'' : Continuous φ'') (hdφ : ∀ y, HasDerivAt φ (φ' y) y)
    (hddφ : ∀ y, HasDerivAt φ' (φ'' y) y)
    {B : ℝ} (hB : 0 ≤ B) (hφ''b : ∀ y, |φ'' y| ≤ B) :
    let f := (kepReferenceDensity heps hlayer).density
    let f' := gammaScaledFirst (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
    let f'' := gammaScaledSecond (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
    kepCertificateTerm eps (kepReferenceLaw eps layer) k i j kepCertificateCutoff φ'' =
      kepCertificateSecondGraph f f' f'' eps ((L : ℝ) - 2 * eps) i (k - j) n φ := by
  have heps2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have hw : 0 ≤ 2 * eps := by linarith
  let f := (kepReferenceDensity heps hlayer).density
  let f' := gammaScaledFirst (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
  let f'' := gammaScaledSecond (kepReferenceWeights eps layer) (kepReferenceSpan eps layer)
  let d := (L : ℝ) - 2 * eps
  let p := kepLogStep f 1
  let q := kepLogStepSlope f f' 1
  let κ := kepCertificateLogCutoff
  let R := kepCertificateScalar p (2 * eps) d n κ
  let R' := kepCertificateScalarFirst p q (2 * eps) d n κ (deriv κ)
  let R'' := kepCertificateScalarSecond p (kepLogStepFirst f' 1) (kepLogStepSecond f'' 1)
    q (2 * eps) d n κ (deriv κ) (deriv (deriv κ))
  have hc := kepReferenceDensity_classical heps hlayer
  have hf : Continuous f := continuous_iff_continuousAt.mpr fun t => (hc.2.1 t).continuousAt
  have hν : (kepReferenceLaw eps layer : Measure ℝ) = volume.withDensity
      (fun t => ENNReal.ofReal (f t)) := by
    rw [← kepReferenceDensity_toMeasure heps hlayer]
    rfl
  rw [kepCertificateTerm_eq_graph (kepReferenceLaw eps layer) hf.measurable
    (kepReferenceDensity heps hlayer).nonneg (kepReferenceDensity_le_span heps hlayer)
    hν (kepReferenceLaw_Iic_zero heps hlayer) (by linarith) hij hL hjk hd
    contDiff_kepCertificateCutoff.continuous.measurable hφ''.measurable
    abs_kepCertificateCutoff_le (fun a ha => kepCertificateCutoff_eq_zero ha) hB hφ''b n hn]
  rcases kepCertificateLogCutoff_C2 with ⟨hκ, hκ', hκ'', hdκ, hddκ⟩
  rcases kepReference_certificateScalar_C2 heps hlayer hκ hκ' hκ'' hdκ hddκ hw d n with
    ⟨hR, hR', hR'', hdR, hddR⟩
  rcases kepCertificateLogCutoff_endpoints with ⟨hlo, hhi, hlo', hhi'⟩
  have hRl : R (Real.log (1 / 2)) = 0 := by
    simp only [R, kepCertificateScalar, κ, hlo, mul_zero, zero_mul]
  have hRh : R (Real.log 2) = 0 := by
    simp only [R, kepCertificateScalar, κ, hhi, mul_zero, zero_mul]
  have hR'l : R' (Real.log (1 / 2)) = 0 := by
    simp only [R', kepCertificateScalarFirst, κ, hlo, hlo', zero_mul, zero_add, mul_zero]
  have hR'h : R' (Real.log 2) = 0 := by
    simp only [R', kepCertificateScalarFirst, κ, hhi, hhi', zero_mul, zero_add, mul_zero]
  have hlh : Real.log (1 / 2 : ℝ) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  change kepLogGraphIntegral (kepLogStep f (-1)) p (2 * eps)
    (Real.log (1 / 2)) (Real.log 2) d i (k - j) 0 (2 * eps) R φ'' = _
  exact kepReference_graph_second_transfer heps hlayer hφ hφ' hφ'' hdφ hddφ
    hR hR' hR'' hdR hddR hw hlh hd hRl hRh hR'l hR'h i (k - j) 0 (2 * eps)

end

end PGM
