import PLAStochastic.Index.KEP.ReferenceScale.FiniteCertificateTransfer
import PLAStochastic.Index.KEP.ReferenceScale.ActualIntegrableCutoffTransfer

/-!
# The original iid certificate for bounded tests meeting the origin

All finite coordinates, positivity and the genuine slope are unchanged. The
actual negative moments now pay the complete weak-transfer integrability.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

theorem kepReference_original_bounded_rare_certificate_second_transfer :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ layer, ∀ hlayer : 1 ≤ layer, ∀ k M i j : ℕ, 18 ≤ k + 1 → i ≤ k + 1 → j ≤ k + 1 →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ Mtest : ℝ, (∀ t, |phi t| ≤ Mtest ∧ |phi' t| ≤ Mtest ∧ |phi'' t| ≤ Mtest) →
          let f := (kepReferenceDensity heps hlayer).density
          let A := kepFiniteCertificateEvent eps (k + 1) i j
          let slope := kepFiniteCertificateSlope eps (k + 1) i j
          let rho0 := fun x => 1 - kepCertificateCoreCutoff M i j (slope x)
          let rho1 := fun x => -kepCertificateCoreFirst M i j (slope x)
          let rho2 := fun x => -kepCertificateCoreSecond M i j (slope x)
          kepCertificateTerm eps (kepReferenceLaw eps layer) (k + 1) i j
            (kepCertificateRareCutoff M i j) phi'' =
            ∫ x in A, phi (∑ t, x t) / (∑ t, x t) ^ 2 *
              (rho0 x * (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) +
                rho1 x * (2 * kepProductMellinFirst f x - 3 * kepProductDensity f x) + rho2 x * kepProductDensity f x) := by
  obtain ⟨e0, he0, htransfer⟩ := kepReference_bounded_rare_cutoff_second_transfer
  refine ⟨e0, he0, ?_⟩
  intro eps he heps layer hlayer k M i j hn18 hi hj phi phi' phi'' hdphi hddphi hcphi'' Mtest htest
  dsimp only
  have hrare : Measurable (kepCertificateRareCutoff M i j) :=
    measurable_const.sub (measurable_kepCertificateCoreCutoff M i j)
  rw [kepCertificateTerm_eq_finite_cone (kepReferenceLaw_Iic_zero heps hlayer) hi hj hrare hcphi''.measurable]
  have heq : (fun x : Fin (k + 1) → ℝ => kepCertificateRareCutoff M i j
      (kepFiniteCertificateSlope eps (k + 1) i j x) * phi'' (∑ t, x t)) =
      fun x => phi'' (∑ t, x t) * (1 - kepCertificateCoreCutoff M i j
        (kepFiniteCertificateSlope eps (k + 1) i j x)) := by
    funext x
    unfold kepCertificateRareCutoff
    ring
  rw [heq]
  exact htransfer eps he heps layer hlayer k M i j hn18 (kepFiniteCertificateSlope eps (k + 1) i j)
    (measurable_kepFiniteCertificateSlope eps (k + 1) i j)
    (fun x c _hc => kepFiniteCertificateSlope_smul eps (k + 1) i j x c)
    (kepFiniteCertificateEvent eps (k + 1) i j) (measurableSet_kepFiniteCertificateEvent eps (k + 1) i j)
    (fun x _c hc => kepFiniteCertificateEvent_smul eps (k + 1) i j x hc)
    (fun _x hx => kepFiniteCertificateEvent_sum_pos (by omega) hx)
    phi phi' phi'' hdphi hddphi hcphi'' Mtest htest

end

end PGM
