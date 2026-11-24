import PLAStochastic.Index.KEP.ReferenceScale.FinitePrefixLaw
import PLAStochastic.Index.KEP.ReferenceScale.PhysicalCutoffDerivatives

/-!
# Original finite certificate cones and complete rare supports

The cone is the genuine certificate on positive original gaps. Its slope is
inverse homogeneous. Every nonzero rare radial field lies either on a fixed
proportion deviation or on a short bridge with an actual small bridge sum.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory Finset Set

def kepFinitePositive (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 < x i}

def kepFiniteCertificateEvent (eps : ℝ) (n i j : ℕ) : Set (Fin n → ℝ) :=
  kepFinitePositive n ∩ {x | certOK eps (gapKeys (kepFiniteGapSequence x)) n i j}

def kepFiniteCertificateSlope (eps : ℝ) (n i j : ℕ) (x : Fin n → ℝ) : ℝ :=
  certSlope eps (gapKeys (kepFiniteGapSequence x)) i j

def kepFiniteBridge (n i j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun t => i ≤ t.val ∧ t.val < j)

theorem measurableSet_kepFinitePositive (n : ℕ) : MeasurableSet (kepFinitePositive n) := by
  have heq : kepFinitePositive n = ⋂ i : Fin n, {x : Fin n → ℝ | 0 < x i} := by
    ext x
    simp only [kepFinitePositive, mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)

theorem measurableSet_kepFiniteCertificateEvent (eps : ℝ) (n i j : ℕ) :
    MeasurableSet (kepFiniteCertificateEvent eps n i j) :=
  (measurableSet_kepFinitePositive n).inter
    ((measurableSet_certOK eps n i j).preimage (measurable_kepFiniteGapSequence n))

theorem measurable_kepFiniteCertificateSlope (eps : ℝ) (n i j : ℕ) :
    Measurable (kepFiniteCertificateSlope eps n i j) :=
  (surv_measurable_certSlope eps i j).comp (measurable_kepFiniteGapSequence n)

theorem kepFiniteCertificateSlope_smul (eps : ℝ) (n i j : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    kepFiniteCertificateSlope eps n i j (c • x) = kepFiniteCertificateSlope eps n i j x / c := by
  unfold kepFiniteCertificateSlope
  rw [kepFiniteGapSequence_smul, certSlope_gapKeys_const_mul]

theorem kepFiniteCertificateEvent_smul (eps : ℝ) (n i j : ℕ) (x : Fin n → ℝ)
    {c : ℝ} (hc : 0 < c) :
    c • x ∈ kepFiniteCertificateEvent eps n i j ↔ x ∈ kepFiniteCertificateEvent eps n i j := by
  have hpos : c • x ∈ kepFinitePositive n ↔ x ∈ kepFinitePositive n := by
    simp only [kepFinitePositive, mem_ofPred_eq, Pi.smul_apply, smul_eq_mul,
      mul_pos_iff_of_pos_left hc]
  unfold kepFiniteCertificateEvent
  rw [mem_inter_iff, mem_inter_iff, hpos]
  apply and_congr_right
  intro _
  change certOK eps (gapKeys (kepFiniteGapSequence (c • x))) n i j ↔ _
  rw [kepFiniteGapSequence_smul]
  exact certOK_gapKeys_const_mul eps _ n i j hc.ne'

theorem kepFiniteCertificateEvent_sum_pos {eps : ℝ} {n i j : ℕ} (hn : 0 < n)
    {x : Fin n → ℝ} (hx : x ∈ kepFiniteCertificateEvent eps n i j) : 0 < ∑ t, x t := by
  apply sum_pos (fun t _ => hx.1 t)
  exact ⟨⟨0, hn⟩, Finset.mem_univ _⟩

theorem kepFiniteBridge_eq_sdiff (n i j : ℕ) :
    kepFiniteBridge n i j = kepFinitePrefix n j \ kepFinitePrefix n i := by
  ext t
  simp only [kepFiniteBridge, kepFinitePrefix, mem_filter, Finset.mem_univ, true_and,
    Finset.mem_sdiff, not_lt]
  tauto

theorem kepFinitePrefix_mono (n : ℕ) {i j : ℕ} (hij : i ≤ j) :
    kepFinitePrefix n i ⊆ kepFinitePrefix n j := by
  intro t ht
  exact mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (mem_filter.mp ht).2 hij⟩

theorem kepFiniteBridge_card {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (kepFiniteBridge n i j).card = j - i := by
  rw [kepFiniteBridge_eq_sdiff, card_sdiff_of_subset (kepFinitePrefix_mono n hij),
    kepFinitePrefix_card hjn, kepFinitePrefix_card (hij.trans hjn)]

theorem kepFiniteBridge_sum {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (x : Fin n → ℝ) :
    (∑ t ∈ kepFiniteBridge n i j, x t) =
      gapKeys (kepFiniteGapSequence x) j - gapKeys (kepFiniteGapSequence x) i := by
  rw [kepFiniteBridge_eq_sdiff, kepFiniteGapSequence_gapKeys x hjn,
    kepFiniteGapSequence_gapKeys x (hij.trans hjn)]
  have hh := sum_sdiff (f := x) (kepFinitePrefix_mono n hij)
  linarith only [hh]

theorem kepCertificateCore_physical_good (M i j : ℕ) (hM : M ≤ j - i)
    {a : ℝ} (ha : a ∈ Ioo (3 / 4 : ℝ) (3 / 2)) :
    1 - kepCertificateCoreCutoff M i j a = 0 ∧
      kepCertificateCoreFirst M i j a = 0 ∧ kepCertificateCoreSecond M i j a = 0 := by
  have hapos : 0 < a := by linarith [ha.1]
  have hgood := kepRadialCoreWeight_good M i j hM
    (ell := Real.log a) (s := 0) (by simpa only [sub_zero, Real.exp_log hapos] using ha)
  obtain ⟨h0, h1, h2⟩ := kepCertificateCore_positive_radial M i j hapos 0
  simpa only [Real.exp_zero, div_one, ← h0, ← h1, ← h2] using hgood

theorem kepFiniteCertificate_rare_support {eps : ℝ} (heps : 104 ≤ eps)
    {n i j : ℕ} (hn : 16 * eps ≤ n) (hij : i < j) (hjn : j ≤ n)
    (hL : 2 * eps < (j : ℝ) - i) {x : Fin n → ℝ}
    (hx : x ∈ kepFiniteCertificateEvent eps n i j)
    (hfield : 1 - kepCertificateCoreCutoff (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0 ∨
      kepCertificateCoreFirst (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0 ∨
      kepCertificateCoreSecond (kepReferenceGraphBridgeCutoff eps) i j
        (kepFiniteCertificateSlope eps n i j x) ≠ 0) :
    7 * n / 6 ≤ (∑ t, x t) ∨ (∑ t, x t) ≤ 3 * n / 4 ∨
      ((j - i : ℕ) < kepReferenceGraphBridgeCutoff eps ∧
        (∑ t ∈ kepFiniteBridge n i j, x t) ≤ ((j - i : ℕ) : ℝ) / 8) := by
  let p := gapKeys (kepFiniteGapSequence x)
  let a := kepFiniteCertificateSlope eps n i j x
  by_cases ha : a ∈ Ioo (3 / 4 : ℝ) (3 / 2)
  · right
    right
    have hshort : j - i < kepReferenceGraphBridgeCutoff eps := by
      by_contra hnot
      obtain ⟨h0, h1, h2⟩ := kepCertificateCore_physical_good
        (kepReferenceGraphBridgeCutoff eps) i j (not_lt.mp hnot) ha
      rcases hfield with h | h | h
      · exact h h0
      · exact h h1
      · exact h h2
    refine ⟨hshort, ?_⟩
    have hsumPos : 0 < ∑ t ∈ kepFiniteBridge n i j, x t := by
      apply sum_pos (fun t _ => hx.1 t)
      apply card_pos.mp
      rw [kepFiniteBridge_card hij.le hjn]
      omega
    rw [kepFiniteBridge_sum hij.le hjn x] at hsumPos ⊢
    exact kep_short_certificate_bridge_small_sum heps hij.le hshort hL
      (sub_pos.mp hsumPos) (by linarith [ha.1] : (1 / 2 : ℝ) ≤ a)
  · have hpk : 0 ≤ p n := by
      rw [show p n = ∑ t, x t from kepFiniteGapSequence_total x]
      exact sum_nonneg fun t _ => (hx.1 t).le
    have hh := kep_bad_core_slope_forces_deviation (gapKeys_zero _) hpk hn hx.2 ha
    rw [kepFiniteGapSequence_total] at hh
    rcases hh with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

end

end PGM
