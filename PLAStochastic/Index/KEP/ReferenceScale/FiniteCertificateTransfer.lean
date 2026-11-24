import PLAStochastic.Index.KEP.ReferenceScale.FiniteCertificateGeometry
import PLAStochastic.Index.KEP.ReferenceScale.ActualWeightedConeTransfer

/-!
# The original iid rare certificate in the complete physical weak transfer

The finite cone is read back on the unchanged infinite iid path. Its actual
slope, positive support and dilation invariance pay every geometric premise
of the multivariate transfer. Only the original physical test remains input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

theorem kepFiniteCertificateSlope_prefix (eps : ℝ) {n i j : ℕ}
    (hi : i ≤ n) (hj : j ≤ n) (g : ℕ → ℝ) :
    kepFiniteCertificateSlope eps n i j (fun l : Fin n => g l) = certSlope eps (gapKeys g) i j := by
  unfold kepFiniteCertificateSlope certSlope
  rw [kepFiniteGapSequence_prefix g hj, kepFiniteGapSequence_prefix g hi]

theorem kepFiniteCertificateBand_prefix (eps : ℝ) {n i j : ℕ}
    (hi : i ≤ n) (hj : j ≤ n) (g : ℕ → ℝ) :
    certOK eps (gapKeys (kepFiniteGapSequence (fun l : Fin n => g l))) n i j ↔
      certOK eps (gapKeys g) n i j := by
  have ha := kepFiniteCertificateSlope_prefix eps hi hj g
  change certSlope eps (gapKeys (kepFiniteGapSequence (fun l : Fin n => g l))) i j = _ at ha
  unfold certOK certBand
  rw [ha]
  have he (t : ℕ) (ht : t ≤ n) :
      certResid (certSlope eps (gapKeys g) i j)
        (gapKeys (kepFiniteGapSequence (fun l : Fin n => g l))) t =
      certResid (certSlope eps (gapKeys g) i j) (gapKeys g) t := by
    unfold certResid
    rw [kepFiniteGapSequence_prefix g ht]
  constructor
  · intro h t ht
    have hh := h t ht
    rw [he t ht, he i hi] at hh
    exact hh
  · intro h t ht
    rw [he t ht, he i hi]
    exact h t ht

theorem kepCertificateTerm_eq_finite_cone {eps : ℝ} {nu : ProbabilityMeasure ℝ}
    (hnu : (nu : Measure ℝ) (Iic 0) = 0) {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n)
    {chi phi : ℝ → ℝ} (hchi : Measurable chi) (hphi : Measurable phi) :
    kepCertificateTerm eps nu n i j chi phi =
      ∫ x in kepFiniteCertificateEvent eps n i j,
        chi (kepFiniteCertificateSlope eps n i j x) * phi (∑ l, x l)
        ∂Measure.pi (fun _ : Fin n => (nu : Measure ℝ)) := by
  let F := (kepFiniteCertificateEvent eps n i j).indicator
    (fun x : Fin n → ℝ => chi (kepFiniteCertificateSlope eps n i j x) * phi (∑ l, x l))
  have hm : Measurable F := ((hchi.comp (measurable_kepFiniteCertificateSlope eps n i j)).mul
    (hphi.comp (Finset.measurable_sum Finset.univ (fun l _ => measurable_pi_apply l)))).indicator
    (measurableSet_kepFiniteCertificateEvent eps n i j)
  have hh := kep_iidLaw_finite_prefix_integral nu n hm
  dsimp only [F] at hh
  rw [integral_indicator (measurableSet_kepFiniteCertificateEvent eps n i j)] at hh
  unfold kepCertificateTerm
  rw [← integral_indicator (measurableSet_certOK eps n i j)]
  apply Eq.trans _ hh
  apply integral_congr_ae
  have hpos : ∀ᵐ g ∂iidLaw nu, ∀ l, 0 < g l := by
    simpa only [wordLaw, iidLaw, Finset.notMem_empty, if_false] using cert_ae_pos_wordLaw hnu hnu ∅
  filter_upwards [hpos] with g hg
  let x : Fin n → ℝ := fun l => g l
  have hxpos : x ∈ kepFinitePositive n := fun l => hg l
  have hcert : x ∈ kepFiniteCertificateEvent eps n i j ↔ certOK eps (gapKeys g) n i j := by
    change x ∈ kepFinitePositive n ∧ certOK eps (gapKeys (kepFiniteGapSequence x)) n i j ↔ _
    rw [kepFiniteCertificateBand_prefix eps hi hj g]
    exact and_iff_right hxpos
  by_cases hc : certOK eps (gapKeys g) n i j
  · have hx := hcert.mpr hc
    have hc' : g ∈ {g : ℕ → ℝ | certOK eps (gapKeys g) n i j} := hc
    rw [indicator_of_mem hc', indicator_of_mem hx, kepFiniteCertificateSlope_prefix eps hi hj g]
    rw [← kepFiniteGapSequence_total, kepFiniteGapSequence_prefix g le_rfl]
  · have hx := mt hcert.mp hc
    have hc' : g ∉ {g : ℕ → ℝ | certOK eps (gapKeys g) n i j} := hc
    rw [indicator_of_notMem hc', indicator_of_notMem hx]

theorem kepReference_original_rare_certificate_second_transfer :
    ∃ eps0 : ℝ, kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ layer, ∀ hlayer : 1 ≤ layer, ∀ k M i j : ℕ, i ≤ k + 1 → j ≤ k + 1 →
          ∀ phi phi' phi'' : ℝ → ℝ,
            (∀ x, HasDerivAt phi (phi' x) x) → (∀ x, HasDerivAt phi' (phi'' x) x) →
            Continuous phi'' → ∀ a b : ℝ, 0 < a → Function.support phi ⊆ Icc a b →
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
  obtain ⟨e0, he0, htransfer⟩ := kepReference_rare_cutoff_second_transfer
  refine ⟨e0, he0, ?_⟩
  intro eps he heps layer hlayer k M i j hi hj phi phi' phi'' hdphi hddphi hcphi'' a b ha hsupp
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
  exact htransfer eps he heps layer hlayer k M i j (kepFiniteCertificateSlope eps (k + 1) i j)
    (measurable_kepFiniteCertificateSlope eps (k + 1) i j)
    (fun x c _hc => kepFiniteCertificateSlope_smul eps (k + 1) i j x c)
    (kepFiniteCertificateEvent eps (k + 1) i j) (measurableSet_kepFiniteCertificateEvent eps (k + 1) i j)
    (fun x _c hc => kepFiniteCertificateEvent_smul eps (k + 1) i j x hc)
    (fun _x hx => kepFiniteCertificateEvent_sum_pos (by omega) hx)
    phi phi' phi'' hdphi hddphi hcphi'' a b ha hsupp

end

end PGM
