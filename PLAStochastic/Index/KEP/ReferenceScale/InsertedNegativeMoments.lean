import PLAStochastic.Index.KEP.ReferenceScale.ReferenceBand
import PLAStochastic.Index.KEP.ReferenceScale.ActualCertificateTransfer
import PLAStochastic.ForMathlib.Probability.Moments.ProductNegativeMoment

/-!
# Negative moments after finitely many positive coordinate insertions

The inserted measures need not have inverse moments or a normalized density.
The sum dominates its clean coordinates. Tonelli pays only the total masses
of the inserted measures, and the proved bounded-density AM--GM estimate
controls all clean coordinates uniformly on the actual reference orbit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal

theorem kep_inserted_negative_moment_le {n : ℕ} (mu : Fin n → Measure ℝ)
    [∀ i, IsFiniteMeasure (mu i)] {nu : Measure ℝ} [IsProbabilityMeasure nu]
    (H : Finset (Fin n)) (hmu : ∀ i ∉ H, mu i = nu)
    (hpos : ∀ i, mu i (Iic 0) = 0) (hnu0 : nu (Iic 0) = 0)
    {f : ℝ → ℝ} (hfm : Measurable f) {D : ℝ} (hD : 0 ≤ D)
    (hnu : nu = volume.withDensity fun x => ENNReal.ofReal (f x))
    (hfD : ∀ x, f x ≤ D) {a : ℝ} (ha : 0 ≤ a)
    (hH : H.card < n) (hn : 4 * a ≤ n - H.card) :
    (∫⁻ x, ENNReal.ofReal ((∑ i, x i) ^ (-a)) ∂Measure.pi mu) ≤
      (∏ i ∈ H, mu i univ) *
        ENNReal.ofReal (((n - H.card : ℕ) : ℝ) ^ (-a) * Real.exp (8 * D * a)) := by
  classical
  let S := Hᶜ
  have hcard : S.card = n - H.card := by simp only [S, card_compl, Fintype.card_fin]
  have hS : S.Nonempty := card_pos.mp (by rw [hcard]; omega)
  have hposall : ∀ᵐ x ∂Measure.pi mu, ∀ i, 0 < x i := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    have he : {x : Fin n → ℝ | ¬ 0 < x i} = Function.eval i ⁻¹' Iic 0 := by
      ext x
      simp only [not_lt, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Iic]
    rw [he]
    exact Measure.pi_eval_preimage_null mu (hpos i)
  have hpt : ∀ᵐ x ∂Measure.pi mu,
      ENNReal.ofReal ((∑ i, x i) ^ (-a)) ≤ ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) := by
    filter_upwards [hposall] with x hx
    have hsumpos : 0 < ∑ i ∈ S, x i := sum_pos (fun i _ => hx i) hS
    have hsumle : (∑ i ∈ S, x i) ≤ ∑ i, x i :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _ => (hx i).le)
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_nonpos hsumpos hsumle (by linarith))
  have hmeas : Measurable (fun x : Fin n → ℝ =>
      ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a))) :=
    (Finset.measurable_sum S (fun i _ => measurable_pi_apply i)).pow_const (-a) |>.ennreal_ofReal
  have hind : ∀ x y : Fin n → ℝ, (∀ i ∉ H, x i = y i) →
      ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) =
        ENNReal.ofReal ((∑ i ∈ S, y i) ^ (-a)) := by
    intro x y hxy
    congr 2
    exact sum_congr rfl (fun i hi => hxy i (mem_compl.mp hi))
  have hq (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4) :
      (∫⁻ x, ENNReal.ofReal (x ^ (-q)) ∂nu) ≤ ENNReal.ofReal (1 + (8 * D) * q) := by
    simpa only [mul_assoc] using lintegral_rpow_neg_le_of_density hfm hD hnu hfD hnu0 hq0 hq
  have hb := lintegral_sum_rpow_neg_le hnu0 (by positivity : 0 ≤ 8 * D) hq S hS ha
    (by rw [hcard, Nat.cast_sub hH.le]; exact hn)
  rw [hcard] at hb
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) ∂Measure.pi mu := lintegral_mono_ae hpt
    _ = (∏ i ∈ H, mu i univ) *
        ∫⁻ x, ENNReal.ofReal ((∑ i ∈ S, x i) ^ (-a)) ∂(Measure.pi fun _ => nu) :=
      lintegral_pi_eq_mul_of_indep mu nu H hmu hmeas hind
    _ ≤ _ := by simpa only [mul_comm] using mul_le_mul_left hb (∏ i ∈ H, mu i univ)

theorem kepReference_inserted_negative_moments :
    ∃ D eps0 : ℝ, 0 < D ∧ kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ _heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ _hj : 1 ≤ j, ∀ n : ℕ, ∀ mu : Fin n → Measure ℝ,
          [∀ i, IsFiniteMeasure (mu i)] →
          ∀ H : Finset (Fin n), (∀ i ∉ H, mu i = (kepReferenceLaw eps j : Measure ℝ)) →
            (∀ i, mu i (Iic 0) = 0) → ∀ a : ℝ, 0 ≤ a → H.card < n →
              4 * a ≤ n - H.card →
              (∫⁻ x, ENNReal.ofReal ((∑ i, x i) ^ (-a)) ∂Measure.pi mu) ≤
                (∏ i ∈ H, mu i univ) *
                  ENNReal.ofReal (((n - H.card : ℕ) : ℝ) ^ (-a) * Real.exp (8 * D * a)) := by
  obtain ⟨D, theta, vlo, vhi, e0, hD, ht, _, _, hreg⟩ := kepReferenceLaw_regular
  refine ⟨D, max kepReferenceClassicalThreshold e0, hD, le_max_left _ _, ?_⟩
  intro eps he heps j hj n mu hfinite H hmu hpos a ha hH hn
  let f := (kepReferenceDensity heps hj).density
  have henv := kepReferenceDensity_envelope_of_regular heps hj hD ht
    (hreg eps ((le_max_right _ _).trans he) j)
  have hnu : (kepReferenceLaw eps j : Measure ℝ) =
      volume.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [← kepReferenceDensity_toMeasure heps hj]
    rfl
  exact kep_inserted_negative_moment_le mu H hmu hpos (kepReferenceLaw_Iic_zero heps hj)
    (kepReferenceDensity heps hj).measurable hD.le hnu henv.1 ha hH hn

end

end PGM
