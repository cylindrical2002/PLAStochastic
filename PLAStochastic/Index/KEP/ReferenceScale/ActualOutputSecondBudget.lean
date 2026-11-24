import PLAStochastic.Index.KEP.ReferenceScale.OutputSecondAssembly
import PLAStochastic.Index.KEP.ReferenceScale.FullSurvivingSecondBudget
import PLAStochastic.Index.KEP.ReferenceScale.FullStoppedSecondBudget

/-!
# Unconditional weighted weak-second budget of the actual next reference law

The free cutoff, full surviving convolution series, and finite stopped
correction are all paid by the original core and rare prefix estimates. The
one-gap exponential factor and actual normalization are paid uniformly. No
analytic recurrence or unproved convolution budget is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_actual_output_weak_second_budget :
    ∃ thetaMax : ℝ, 0 < thetaMax ∧
      ∀ theta : ℝ, 0 < theta → theta ≤ thetaMax → ∃ K c E : ℝ,
        0 < K ∧ 0 < c ∧ kepReferenceClassicalThreshold ≤ E ∧
        ∀ eps, E ≤ eps → ∀ j : ℕ, 1 ≤ j →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ L : ℝ,
              (∀ t, |phi t| ≤ L ∧ |phi' t| ≤ L ∧ |phi'' t| ≤ L) →
            ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |phi t| ≤ B * Real.exp (theta * t)) →
          |∫ x, phi'' x ∂(kepReferenceLaw eps (j + 1) : Measure ℝ)| ≤
            B * K * eps ^ 47 *
              (1 + Real.sqrt (kepReferenceWeightedSecondNorm theta eps j) +
                Real.exp (-c * eps) * kepReferenceWeightedSecondNorm theta eps j) := by
  obtain ⟨ts, hts, hsurv⟩ := kepReference_full_surviving_second_series_budget
  obtain ⟨td, htd, hstop⟩ := kepReference_full_short_stopped_second_budget
  obtain ⟨Cm, t0, em, hCm, ht0, hmoment⟩ := kepReference_uniform_two_sided_mgf
  obtain ⟨eo, houtput⟩ := kepReference_output_convolution_series
  refine ⟨min ts (min td t0), lt_min hts (lt_min htd ht0), ?_⟩
  intro theta ht htmax
  have hts' : theta ≤ ts := htmax.trans (min_le_left _ _)
  have htd' : theta ≤ td := htmax.trans ((min_le_right ts _).trans (min_le_left td _))
  have ht0' : theta ≤ t0 := htmax.trans ((min_le_right ts _).trans (min_le_right td _))
  obtain ⟨Ks, cs, es, hKs, hcs, hes, hs⟩ := hsurv theta ht hts'
  obtain ⟨Kd, cd, ed, hKd, hcd, _hed, hd⟩ := hstop theta ht htd'
  have hcb1 : 1 ≤ kepGraphMeanBracket := kepGraphMeanBracket_ge_one
  have hcb : 0 < kepGraphMeanBracket := by linarith
  obtain ⟨ew, _hew, hw⟩ := kepReference_output_weight_admissible ht.le (mul_pos ht hcb)
    (by norm_num : (0 : ℝ) < 1) (by rw [mul_div_cancel_right₀ _ hcb.ne'])
  let H := 1 + Real.exp (t0 + Cm * t0 ^ 2)
  let c := min cs cd
  let E := max (max es ed) (max em (max eo (max ew 3)))
  let K := kepGraphMeanBracket ^ 2 * (1 + H) * (Ks + 324 * Kd)
  have hH : 0 < H := by dsimp [H]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨K, c, E, hK, lt_min hcs hcd,
    hes.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro eps he j hj phi phi' phi'' hdphi hddphi hcphi'' L htest B hB hphiB
  have hes' : es ≤ eps := (le_max_left _ _).trans ((le_max_left _ _).trans he)
  have hed' : ed ≤ eps := (le_max_right _ _).trans ((le_max_left _ _).trans he)
  have hem : em ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans he)
  have heo : eo ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans he))
  have hew : ew ≤ eps := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans he)))
  have he3 : 3 ≤ eps := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans he)))
  have heps : kepReferenceClassicalThreshold ≤ eps := hes.trans hes'
  have he1 : 1 ≤ eps := by linarith
  have hepos : 0 < eps := by linarith
  let nu := kepReferenceLaw eps j
  let C := lawC eps nu
  let M := ⌈16 * eps⌉₊
  let J := kepReferenceWeightedSecondNorm theta eps j
  let A := Ks * eps ^ 43 * (1 + Real.sqrt J + Real.exp (-cs * eps) * J)
  let D := Kd * (1 + J) * Real.exp (-cd * eps)
  have hJ : 0 ≤ J := kepReferenceWeightedSecondNorm_nonneg theta eps j
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hphysical := hw eps hew j
  have hC1 : 1 ≤ C := hphysical.1
  have hu : 0 ≤ theta / C := hphysical.2.1
  have huTop : theta / C ≤ t0 := hphysical.2.2.2.2.trans ht0'
  obtain ⟨hmi, hmb⟩ := hmoment eps hem j (theta / C) (by rwa [abs_of_nonneg hu])
  have hMGF : (∫ x, Real.exp ((theta / C) * x) ∂(nu : Measure ℝ)) ≤ H - 1 := by
    apply hmb.trans
    dsimp only [H]
    simp only [add_sub_cancel_left]
    apply Real.exp_le_exp.mpr
    have hsq : (theta / C) ^ 2 ≤ t0 ^ 2 := by nlinarith
    exact add_le_add huTop (mul_le_mul_of_nonneg_left hsq hCm.le)
  have hM : 16 * eps ≤ (M : ℝ) := Nat.le_ceil _
  have hMupper : (M : ℝ) ≤ 17 * eps := by
    have hh := Nat.ceil_lt_add_one (by positivity : 0 ≤ 16 * eps)
    dsimp only [M]
    linarith
  have hMM : (M + 1 : ℝ) ≤ 18 * eps := by linarith
  have hbudget := kepReference_output_second_budget_assembly eps theta j M hC1 hM
    (kepReferenceLaw_Iic_zero heps hj) hH.le hA hD hmi hMGF
    (fun psi psi' psi'' hdpsi hddpsi hcpsi Lt hbt Bt hBt hpsiB => by
      obtain ⟨hsum, hbound⟩ := hs eps hes' heps j hj psi psi' psi'' hdpsi hddpsi hcpsi Lt hbt Bt hBt hpsiB
      refine ⟨hsum, hbound.trans_eq ?_⟩
      dsimp only [A, J]
      ring)
    (fun n hn psi psi' psi'' hdpsi hddpsi hcpsi Lt hbt Bt hBt hpsiB => by
      have hnMax : (n : ℝ) ≤ 17 * eps :=
        (show (n : ℝ) ≤ M by exact_mod_cast hn).trans hMupper
      convert hd eps hed' heps j hj n hnMax psi psi' psi'' hdpsi hddpsi hcpsi Lt hbt Bt hBt hpsiB using 1
      dsimp only [D, J]
      ring)
    (fun psi hpsi Lt hLt hbpsi => (houtput eps heo j psi hpsi Lt hLt hbpsi M).2)
    hdphi hddphi hcphi'' htest hB hphiB
  let W := 1 + Real.sqrt J + Real.exp (-c * eps) * J
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hcs' : Real.exp (-cs * eps) ≤ Real.exp (-c * eps) := Real.exp_le_exp.mpr (by
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_left cs cd) hepos.le))
  have hcd' : Real.exp (-cd * eps) ≤ Real.exp (-c * eps) := Real.exp_le_exp.mpr (by
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right (min_le_right cs cd) hepos.le))
  have hexp1 : Real.exp (-cd * eps) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hcd, hepos])
  have hAW : A ≤ Ks * eps ^ 43 * W := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    dsimp only [W]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcs' hJ)
  have hDW : D ≤ Kd * W := by
    dsimp only [D]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hKd.le
    have hmul := mul_le_mul_of_nonneg_right hcd' hJ
    dsimp only [W]
    nlinarith only [hmul, hexp1, Real.sqrt_nonneg J]
  have hep : eps ^ 2 ≤ eps ^ 43 := pow_le_pow_right₀ he1 (by omega)
  have hprefix : A + (M + 1 : ℝ) ^ 2 * D ≤ (Ks + 324 * Kd) * eps ^ 43 * W := by
    have hMsq : (M + 1 : ℝ) ^ 2 ≤ 324 * eps ^ 2 := by
      calc
        _ ≤ (18 * eps) ^ 2 := by gcongr
        _ = _ := by ring
    have hprod := mul_le_mul hMsq hDW hD (by positivity : 0 ≤ 324 * eps ^ 2)
    have hp2 := mul_le_mul_of_nonneg_left hep (by positivity : 0 ≤ 324 * Kd * W)
    calc
      _ ≤ Ks * eps ^ 43 * W + (324 * eps ^ 2) * (Kd * W) := add_le_add hAW hprod
      _ = Ks * eps ^ 43 * W + (324 * Kd * W) * eps ^ 2 := by ring
      _ ≤ Ks * eps ^ 43 * W + (324 * Kd * W) * eps ^ 43 := add_le_add le_rfl hp2
      _ = _ := by ring
  have hCupper := (kepReference_lawC_bracket heps j).2
  have hC2 : C ^ 2 ≤ kepGraphMeanBracket ^ 2 * eps ^ 4 := by
    have hh : C ^ 2 ≤ (kepGraphMeanBracket * eps ^ 2) ^ 2 := by gcongr
    exact hh.trans_eq (by ring)
  apply hbudget.trans
  calc
    _ ≤ (kepGraphMeanBracket ^ 2 * eps ^ 4) * B * (1 + H) *
        ((Ks + 324 * Kd) * eps ^ 43 * W) := by gcongr
    _ = _ := by dsimp only [K, W, J]; ring

end

end PGM
