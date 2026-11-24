import PLAStochastic.Index.KEP.ReferenceScale.FiniteCertificateGeometry

/-!
# The complete nonzero support of the original rare radial fields

The support retains the genuine certificate and all three cutoff fields. Its
bad-proportion and remaining tiny-bridge pieces are measurable and satisfy
the exact event containments required by the actual insertion estimates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set

def kepFiniteRareSupport (eps : ℝ) (n i j : ℕ) : Set (Fin n → ℝ) :=
  kepFiniteCertificateEvent eps n i j ∩
    {x | 1 - kepCertificateCoreCutoff (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0 ∨
      kepCertificateCoreFirst (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0 ∨
      kepCertificateCoreSecond (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0}

def kepFiniteProportionBad (n : ℕ) : Set (Fin n → ℝ) :=
  {x | 7 * n / 6 ≤ ∑ t, x t} ∪ {x | (∑ t, x t) ≤ 3 * n / 4}

theorem measurableSet_kepFiniteProportionBad (n : ℕ) : MeasurableSet (kepFiniteProportionBad n) := by
  have hS : Measurable (fun x : Fin n → ℝ => ∑ t, x t) :=
    Finset.measurable_sum Finset.univ (fun t _ => measurable_pi_apply t)
  exact (measurableSet_le measurable_const hS).union (measurableSet_le hS measurable_const)

theorem measurableSet_kepFiniteRareSupport (eps : ℝ) (n i j : ℕ) :
    MeasurableSet (kepFiniteRareSupport eps n i j) := by
  let M := kepReferenceGraphBridgeCutoff eps
  let a := kepFiniteCertificateSlope eps n i j
  have ha := measurable_kepFiniteCertificateSlope eps n i j
  have h0 : Measurable (fun x => 1 - kepCertificateCoreCutoff M i j (a x)) :=
    measurable_const.sub ((measurable_kepCertificateCoreCutoff M i j).comp ha)
  have h1 := (measurable_kepCertificateCoreFirst M i j).comp ha
  have h2 := (measurable_kepCertificateCoreSecond M i j).comp ha
  exact (measurableSet_kepFiniteCertificateEvent eps n i j).inter
    ((measurableSet_eq_fun h0 measurable_const).compl.union
      ((measurableSet_eq_fun h1 measurable_const).compl.union
        (measurableSet_eq_fun h2 measurable_const).compl))

theorem kepFiniteRareSupport_tiny_subset_survival (eps : ℝ) (n i j : ℕ) :
    kepFiniteRareSupport eps n i j \ kepFiniteProportionBad n ⊆ (kepFiniteStoppedEvent eps n)ᶜ := by
  intro x hx
  exact not_le_of_gt (cert_lt_gapSegLen_of_certOK hx.1.1.2)

theorem kepFiniteRareSupport_tiny_subset_bridge {eps : ℝ} (heps : 104 ≤ eps)
    {n i j : ℕ} (hn : 16 * eps ≤ n) (hij : i < j) (hjn : j ≤ n)
    (hL : 2 * eps < (j : ℝ) - i) :
    kepFiniteRareSupport eps n i j \ kepFiniteProportionBad n ⊆
      {x : Fin n → ℝ | (∑ t ∈ kepFiniteBridge n i j, x t) ≤ (kepFiniteBridge n i j).card / 8} := by
  intro x hx
  have hh := kepFiniteCertificate_rare_support heps hn hij hjn hL hx.1.1 hx.1.2
  rcases hh with hbad | hbad | htiny
  · exact False.elim (hx.2 (Or.inl hbad))
  · exact False.elim (hx.2 (Or.inr hbad))
  · rw [kepFiniteBridge_card hij.le hjn]
    exact htiny.2

end

end PGM
