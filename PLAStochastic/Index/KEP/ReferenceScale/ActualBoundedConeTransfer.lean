import PLAStochastic.Index.KEP.ReferenceScale.ActualIntegrableCutoffTransfer

/-!
# The actual unweighted cone formula for bounded C2 tests

The trivial physical cutoff reads the fully paid weighted formula as the
ordinary product-cone formula. Tests may meet the physical origin, and their
three bounds need not be uniform across later shifted convolution tests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepReference_bounded_cone_second_transfer :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ k : ℕ, 18 ≤ k + 1 →
          ∀ A : Set (Fin (k + 1) → ℝ), MeasurableSet A →
          (∀ x (c : ℝ), 0 < c → (c • x ∈ A ↔ x ∈ A)) →
          (∀ x ∈ A, 0 < ∑ i, x i) →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ Mtest : ℝ,
              (∀ t, |phi t| ≤ Mtest ∧ |phi' t| ≤ Mtest ∧ |phi'' t| ≤ Mtest) →
          let f := (kepReferenceDensity heps hj).density
          (∫ x in A, phi'' (∑ i, x i) ∂Measure.pi (fun _ => (kepReferenceLaw eps j : Measure ℝ))) =
            ∫ x in A, phi (∑ i, x i) / (∑ i, x i) ^ 2 *
              (kepProductMellinSecond f x - 3 * kepProductMellinFirst f x + 2 * kepProductDensity f x) := by
  obtain ⟨e0, he0, htransfer⟩ := kepReference_bounded_rare_cutoff_second_transfer
  refine ⟨e0, he0, ?_⟩
  intro eps he heps j hj k hn18 A hA hcone hpos phi phi' phi'' hdphi hddphi hcphi Mtest htest
  have hh := htransfer eps he heps j hj k 1 0 0 hn18 (fun _ => 0) measurable_const
    (by intro x c _; simp) A hA hcone hpos phi phi' phi'' hdphi hddphi hcphi Mtest htest
  simpa [kepCertificateCoreCutoff, kepCertificateCoreFirst, kepCertificateCoreSecond] using hh

theorem kep_C2_compact_bounded_test {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x) (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x)
    (hcphi'' : Continuous phi'') (hcompact : HasCompactSupport phi) :
    ∃ M : ℝ, ∀ t, |phi t| ≤ M ∧ |phi' t| ≤ M ∧ |phi'' t| ≤ M := by
  have hcphi := continuous_iff_continuousAt.mpr fun x => (hdphi x).continuousAt
  have hcphi' := continuous_iff_continuousAt.mpr fun x => (hddphi x).continuousAt
  have he1 : phi' = deriv phi := funext fun x => (hdphi x).deriv.symm
  have he2 : phi'' = deriv phi' := funext fun x => (hddphi x).deriv.symm
  have hcompact' : HasCompactSupport phi' := by rw [he1]; exact hcompact.deriv
  have hcompact'' : HasCompactSupport phi'' := by rw [he2]; exact hcompact'.deriv
  obtain ⟨M0, hM0⟩ := hcphi.bounded_above_of_compact_support hcompact
  obtain ⟨M1, hM1⟩ := hcphi'.bounded_above_of_compact_support hcompact'
  obtain ⟨M2, hM2⟩ := hcphi''.bounded_above_of_compact_support hcompact''
  refine ⟨max M0 (max M1 M2), ?_⟩
  intro t
  simpa only [Real.norm_eq_abs] using
    And.intro ((hM0 t).trans (le_max_left _ _))
      (And.intro ((hM1 t).trans ((le_max_left _ _).trans (le_max_right _ _)))
        ((hM2 t).trans ((le_max_right _ _).trans (le_max_right _ _))))

end

end PGM
