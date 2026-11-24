import PLAStochastic.Index.KEP.ReferenceScale.ActualConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.WeightedIntegrableConeTransfer
import PLAStochastic.Index.KEP.ReferenceScale.PhysicalCutoffDerivatives

/-!
# The actual rare cutoff for bounded tests meeting the physical origin

An inverse-homogeneous slope has exactly the original physical complement
cutoff and its two true radial derivatives. The actual reference density pays
all Mellin and multivariate integrability inputs. No weak derivative or cutoff
regularity certificate is supplied by the caller.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

theorem kepReference_bounded_rare_cutoff_second_transfer :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ k M i l : ℕ, 18 ≤ k + 1 →
          ∀ aSlope : (Fin (k + 1) → ℝ) → ℝ, Measurable aSlope →
            (∀ x (c : ℝ), 0 < c → aSlope (c • x) = aSlope x / c) →
          ∀ A : Set (Fin (k + 1) → ℝ), MeasurableSet A →
            (∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A)) →
            (∀ x ∈ A, 0 < ∑ t, x t) →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ Mtest : ℝ, (∀ t, |phi t| ≤ Mtest ∧ |phi' t| ≤ Mtest ∧ |phi'' t| ≤ Mtest) →
          let f := (kepReferenceDensity heps hj).density
          let rho0 := fun x => 1 - kepCertificateCoreCutoff M i l (aSlope x)
          let rho1 := fun x => -kepCertificateCoreFirst M i l (aSlope x)
          let rho2 := fun x => -kepCertificateCoreSecond M i l (aSlope x)
          (∫ x in A, phi'' (∑ t, x t) * rho0 x ∂Measure.pi (fun _ => (kepReferenceLaw eps j : Measure ℝ))) =
            ∫ x in A, phi (∑ t, x t) / (∑ t, x t) ^ 2 *
              (rho0 x * (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
                rho1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + rho2 x * kepProductDensity f x) := by
  obtain ⟨e0, he0, hib⟩ := kepReference_mellin_insertions_integrable
  obtain ⟨eI, heI, hInv⟩ := kepReference_inverse_second_mellin_fields_integrable
  refine ⟨max e0 eI, he0.trans (le_max_left _ _), ?_⟩
  intro eps he heps j hj k M i l hn18 aSlope hmSlope hSlope A hA hcone hpos
    phi phi' phi'' hdphi hddphi hcphi'' Mtest htest
  let f := (kepReferenceDensity heps hj).density
  let rho0 := fun x : Fin (k + 1) → ℝ => 1 - kepCertificateCoreCutoff M i l (aSlope x)
  let rho1 := fun x : Fin (k + 1) → ℝ => -kepCertificateCoreFirst M i l (aSlope x)
  let rho2 := fun x : Fin (k + 1) → ℝ => -kepCertificateCoreSecond M i l (aSlope x)
  dsimp only
  have hm0 : Measurable rho0 := measurable_const.sub ((measurable_kepCertificateCoreCutoff M i l).comp hmSlope)
  have hm1 : Measurable rho1 := ((measurable_kepCertificateCoreFirst M i l).comp hmSlope).neg
  have hm2 : Measurable rho2 := ((measurable_kepCertificateCoreSecond M i l).comp hmSlope).neg
  obtain ⟨B, hB, hb⟩ := kepCertificateCore_physical_bounds
  have hb0 (x) : |rho0 x| ≤ B := by
    have hh := kepCertificateCoreCutoff_bounds M i l (aSlope x)
    dsimp [rho0]
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hb1 (x) : |rho1 x| ≤ B := by simpa only [rho1, abs_neg] using (hb M i l (aSlope x)).2.1
  have hb2 (x) : |rho2 x| ≤ B := by simpa only [rho2, abs_neg] using (hb M i l (aSlope x)).2.2
  have hr0 (x : Fin (k + 1) → ℝ) : (fun t => rho0 (Real.exp t • x)) =
      fun t => 1 - kepCertificateCoreCutoff M i l (aSlope x / Real.exp t) := by
    funext t
    dsimp [rho0]
    rw [hSlope x (Real.exp t) (Real.exp_pos t)]
  have hr1 (x : Fin (k + 1) → ℝ) : (fun t => rho1 (Real.exp t • x)) =
      fun t => -kepCertificateCoreFirst M i l (aSlope x / Real.exp t) := by
    funext t
    dsimp [rho1]
    rw [hSlope x (Real.exp t) (Real.exp_pos t)]
  have hdr0 (x : Fin (k + 1) → ℝ) (s : ℝ) :
      HasDerivAt (fun t => rho0 (Real.exp t • x)) (rho1 (Real.exp s • x)) s := by
    rw [hr0]
    dsimp [rho1]
    rw [hSlope x (Real.exp s) (Real.exp_pos s)]
    convert (hasDerivAt_const s (1 : ℝ)).sub
      (kepCertificateCore_physical_derivatives M i l (aSlope x) s).1 using 1 <;> first | rfl | ring
  have hdr1 (x : Fin (k + 1) → ℝ) (s : ℝ) :
      HasDerivAt (fun t => rho1 (Real.exp t • x)) (rho2 (Real.exp s • x)) s := by
    rw [hr1]
    dsimp [rho2]
    rw [hSlope x (Real.exp s) (Real.exp_pos s)]
    exact (kepCertificateCore_physical_derivatives M i l (aSlope x) s).2.neg
  have hcr2 (x : Fin (k + 1) → ℝ) : Continuous (fun s => rho2 (Real.exp s • x)) := by
    have he (s : ℝ) : rho2 (Real.exp s • x) = -kepCertificateCoreSecond M i l (aSlope x / Real.exp s) := by
      dsimp [rho2]
      rw [hSlope x (Real.exp s) (Real.exp_pos s)]
    rw [funext he]
    by_cases hapos : 0 < aSlope x
    · have he2 (s : ℝ) := (kepCertificateCore_positive_radial M i l hapos s).2.2
      simp_rw [he2]
      unfold kepRadialCoreWeightSecond
      by_cases hM : M ≤ l - i
      · simp only [hM, if_true]
        exact (kepCertificateLogCutoff_C2.2.2.1.comp (continuous_const.sub continuous_id)).neg
      · simp only [hM, if_false, neg_zero]
        exact continuous_const
    · have he2 (s : ℝ) : kepCertificateCoreSecond M i l (aSlope x / Real.exp s) = 0 := by
        have hn : aSlope x / Real.exp s ≤ 0 := div_nonpos_of_nonpos_of_nonneg
          (not_lt.mp hapos) (Real.exp_pos s).le
        simp only [kepCertificateCoreSecond, not_lt.mpr hn, and_false, if_false]
      simp_rw [he2, neg_zero]
      exact continuous_const
  obtain ⟨hi0, hi1, hi2⟩ := hib eps ((le_max_left _ _).trans he) heps j hj
  obtain ⟨hiInv0, hiInv1, hiInv2⟩ := hInv eps ((le_max_right _ _).trans he) heps j hj (k + 1) hn18
  have hc := kepReferenceDensity_classical heps hj
  have hid : (∫ x in A, phi'' (∑ t, x t) * rho0 x ∂Measure.pi (fun _ : Fin (k + 1) =>
      (kepReferenceLaw eps j : Measure ℝ))) =
      ∫ x in A, phi'' (∑ t, x t) * rho0 x * kepProductDensity f x := by
    rw [← integral_indicator hA, kepReference_iid_integral_eq_product_density heps hj,
      ← integral_indicator hA]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      by_cases hx : x ∈ A
      · rw [indicator_of_mem hx, indicator_of_mem hx]
      · rw [indicator_of_notMem hx, indicator_of_notMem hx, zero_mul]
  rw [hid]
  exact kep_weighted_integrable_product_cone_second_transfer hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1
    hi0 hi1 hi2 hA hcone hpos hm0 hm1 hm2 hb0 hb1 hb2 hdr0 hdr1 hcr2
    hdphi hddphi hcphi'' htest hiInv0 hiInv1 hiInv2

end

end PGM
