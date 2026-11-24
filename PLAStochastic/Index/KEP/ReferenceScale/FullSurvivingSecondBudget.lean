import PLAStochastic.Index.KEP.ReferenceScale.PhysicalWeightBudgets
import PLAStochastic.Index.KEP.ReferenceScale.BoundedRareCertificateSeries

/-!
# The full original long surviving-prefix second budget

The original core and complementary certificates are summed at the genuine
output weight theta/C. The unweighted core cost is paid by the same weighted
input norm. All test, moment, negative-moment, and fixed-rate conditions are
discharged for the actual reference orbit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_full_surviving_second_series_budget :
    ∃ thetaMax : ℝ, 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c E : ℝ,
        0 < K ∧ 0 < c ∧ kepReferenceClassicalThreshold ≤ E ∧
        ∀ eps, E ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
          ∀ j : ℕ, ∀ _hj : 1 ≤ j, ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ M : ℝ,
              (∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M) →
            ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |phi t| ≤
              B * Real.exp (theta * t / lawC eps (kepReferenceLaw eps j))) →
          let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
            |∫ g in {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g},
              phi'' (gapKeys g n) ∂iidLaw (kepReferenceLaw eps j)| else 0
          Summable F ∧ (∑' n : ℕ, F n) ≤
            B * K * eps ^ 43 *
              (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j) +
                Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) := by
  obtain ⟨tc, cc, Kc, ec, htc, hcc, hKc, hec, hcore⟩ := kepReference_surviving_core_series_budget
  obtain ⟨tr, er, V, htr, her, hV, hrare⟩ := kepReference_original_bounded_rare_certificate_fixed_scale_series_budget
  obtain ⟨ti, _Ki, ei, hti, -, _hei, hinitial⟩ := kepReference_small_weight_initial_budget
  let tm := min tc (min tr (min ti (V / kepGraphMeanBracket)))
  have hcb : 0 < kepGraphMeanBracket := lt_of_lt_of_le (by norm_num) kepGraphMeanBracket_ge_one
  refine ⟨tm, lt_min htc (lt_min htr (lt_min hti (div_pos hV hcb))), ?_⟩
  intro theta ht htmax
  have htc' : theta ≤ tc := htmax.trans (min_le_left _ _)
  have htr' : theta ≤ tr := htmax.trans ((min_le_right tc _).trans (min_le_left tr _))
  have hti' : theta ≤ ti := htmax.trans ((min_le_right tc _).trans
    ((min_le_right tr _).trans (min_le_left ti _)))
  have htV : theta ≤ V / kepGraphMeanBracket :=
    htmax.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨Kr, cr, u0, hKr, hcr, hu0, -, hr⟩ := hrare theta ht htr'
  obtain ⟨ew, _hew, hw⟩ := kepReference_output_weight_admissible ht.le hV hu0 htV
  let E := max (max ec er) (max ei ew)
  let c := min cc cr
  refine ⟨Kc + Kr, c, E, by positivity, lt_min hcc hcr,
    hec.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro eps he heps j hj phi phi' phi'' hdphi hddphi hcphi'' M htest B hB hphiB
  dsimp only
  have hec' : ec ≤ eps := (le_max_left _ _).trans ((le_max_left _ _).trans he)
  have her' : er ≤ eps := (le_max_right _ _).trans ((le_max_left _ _).trans he)
  have hei' : ei ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have hew' : ew ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans he)
  have he2 : 2 ≤ eps := (le_max_left _ _).trans heps
  have he1 : 1 ≤ eps := by linarith
  have hepos : 0 < eps := by linarith
  have hphysical := hw eps hew' j
  let C := lawC eps (kepReferenceLaw eps j)
  let u := theta / C
  let J := kepReferenceWeightedSecondNorm theta eps j
  let J0 := kepReferenceSecondNorm eps j
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hJ0 : J0 ≤ J := kepReference_second_norm_le_weighted heps ht.le j
    ((hinitial theta ht.le hti' eps hei').1 j hj)
  have hcphi := continuous_iff_continuousAt.mpr fun x => (hdphi x).continuousAt
  have hcphi' := continuous_iff_continuousAt.mpr fun x => (hddphi x).continuousAt
  have hM : 0 ≤ M := (abs_nonneg (phi'' 0)).trans (htest 0).2.2
  let f := (kepReferenceDensity heps hj).density
  let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let f'' := gammaScaledSecond (kepReferenceWeights eps j) (kepReferenceSpan eps j)
  let A := fun n : ℕ => |kepSurvivingSecondCore f f' f'' eps
    (kepReferenceGraphBridgeCutoff eps) n phi|
  let R := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
    |kepSurvivingRareTerm eps (kepReferenceLaw eps j) (kepReferenceGraphBridgeCutoff eps) n phi''| else 0
  obtain ⟨hsA, hbA⟩ := hcore eps hec' heps j hj B hB (fun _ => phi) (fun _ => hcphi) (fun _n t htn => by
    apply (hphiB t htn).trans
    apply mul_le_mul_of_nonneg_left _ hB
    apply Real.exp_le_exp.mpr
    rw [← kepReference_lawC_eq_segMean heps j]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right htc' htn) (by linarith [hphysical.1]))
  obtain ⟨hsR, hbR⟩ := hr eps her' heps j hj u hphysical.2.1 hphysical.2.2.1 hphysical.2.2.2.1
    (fun _ => phi) (fun _ => phi') (fun _ => phi'') (fun _ => hdphi) (fun _ => hddphi)
    (fun _ => hcphi'') (fun _ => ⟨M, htest⟩) B hB (fun _n t ht0 => by
      simpa only [u, C, div_mul_eq_mul_div] using hphiB t ht0)
  let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
    |∫ g in {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g},
      phi'' (gapKeys g n) ∂iidLaw (kepReferenceLaw eps j)| else 0
  have hF (n : ℕ) : F n ≤ A n + R n := by
    by_cases hn : 16 * eps ≤ (n : ℝ)
    · have hkn : 2 * eps < n := by linarith
      have hid := kepReference_surviving_second_core_add_rare heps hj
        (kepReferenceGraphBridgeCutoff eps) n hkn hcphi hcphi' hcphi'' hdphi hddphi hM (fun x => (htest x).2.2)
      dsimp only [F, A, R, f, f', f'']
      rw [if_pos hn, if_pos hn, hid]
      exact abs_add_le _ _
    · simp only [F, R, if_neg hn, add_zero, A]
      exact abs_nonneg _
  have hsF := (hsA.add hsR).of_nonneg_of_le (fun n => by dsimp [F]; split <;> positivity) hF
  have hec : Real.exp (-cc * eps) ≤ Real.exp (-c * eps) := by
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left cc cr) hepos.le)
  have her : Real.exp (-cr * eps) ≤ Real.exp (-c * eps) := by
    apply Real.exp_le_exp.mpr
    dsimp only [c]
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right cc cr) hepos.le)
  have hexp1 : Real.exp (-cr * eps) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hcr, hepos])
  let W := 1 + Real.sqrt J + Real.exp (-c * eps) * J
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hAw : 1 + Real.sqrt J0 + Real.exp (-cc * eps) * J0 ≤ W := by
    have hmul := mul_le_mul hec hJ0 (show 0 ≤ J0 from integral_nonneg fun _ => abs_nonneg _) (Real.exp_pos _).le
    have hsqrt := Real.sqrt_le_sqrt hJ0
    dsimp only [W]
    linarith
  have hRw : Real.exp (-cr * eps) * (1 + J) ≤ W := by
    have hmul := mul_le_mul_of_nonneg_right her hJ
    dsimp only [W]
    nlinarith only [hmul, hexp1, Real.sqrt_nonneg J]
  have hep : eps ^ 6 ≤ eps ^ 43 := pow_le_pow_right₀ he1 (by omega)
  refine ⟨hsF, ?_⟩
  calc
    _ ≤ ∑' n : ℕ, (A n + R n) := hsF.tsum_le_tsum hF (hsA.add hsR)
    _ = (∑' n : ℕ, A n) + ∑' n : ℕ, R n := hsA.tsum_add hsR
    _ ≤ B * Kc * eps ^ 43 * W + B * Kr * eps ^ 43 * W := by
      apply add_le_add
      · exact hbA.trans (mul_le_mul_of_nonneg_left hAw (by positivity))
      · apply hbR.trans
        calc
          _ = B * Kr * eps ^ 6 * (Real.exp (-cr * eps) * (1 + J)) := by ring
          _ ≤ B * Kr * eps ^ 6 * W := mul_le_mul_of_nonneg_left hRw (by positivity)
          _ ≤ _ := by gcongr
    _ = _ := by dsimp only [W, J]; ring

end

end PGM
