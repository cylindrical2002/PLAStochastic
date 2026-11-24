import PLAStochastic.Index.GEP.Kernel.FarSlope.Annulus
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedAnnulusBudget

/-! # Physical output weights on the actual infinite saddle annulus -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem kernel_saddle_time_weight_absorb {a k w s N U : ℝ} (ha : 1/2 ≤ a)
    (hk : 0 < k) (hw : 0 < w) (hs0 : 0 ≤ s) (hs : s ≤ k/(8*w^2)) (hN : 1 ≤ N) :
    Real.exp (s*(N+1)/a) * Real.exp (U-k*N/w^2) ≤
      Real.exp (U-(k/2)*N/w^2) := by
  have hh := kernel_large_time_weight_absorb (k := 4*k) ha (by positivity) hw hs0
    (by simpa only [show 4*k/(32*w^2) = k/(8*w^2) by ring] using hs) hN
  have h1 : Real.exp (s*(N+1)/a) * Real.exp (U-k*N/w^2) =
      Real.exp U * (Real.exp (s*(N+1)/a) * Real.exp (-(4*k/(4*w^2))*N)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [h1]
  apply (mul_le_mul_of_nonneg_left hh (Real.exp_nonneg U)).trans_eq
  rw [← Real.exp_add]
  congr 1
  ring

theorem kernel_regLaw_weighted_bulk_far_annulus (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ δ q ρ K : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ 0 < q ∧ 0 < ρ ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ w s x A : ℝ, 1 ≤ w → 0 ≤ s → s ≤ ρ/w^2 → 0 ≤ x →
      ∀ y z : ℝ, |z-y|=w →
        (∫⁻ a in kernelSaddleAnnulus δ w A, ∑' p : ℕ × ℕ × ℕ,
          ENNReal.ofReal (kernelWeightedBulkTailTerm ν f w s x y z a p)) ≤
            ENNReal.ofReal (K*w^16*Real.exp (θ/2*x-q*A)) := by
  obtain ⟨δ,q,k,K,hδ,hδhi,hq,hk,hK,hpair⟩ :=
    kernel_regLaw_full_marked_pin_far_window_of_density D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρo,Os,Ol,hρo,hOs,hOl,houter⟩ :=
    kernel_regLaw_physical_outer_weight_bound D θ vlo vhi hD hθ hvlo hv
  refine ⟨δ,q,min ρo (k/8),2*(Os+Ol)*K*(3*(1+4/(k/2))^4),
    hδ,hδhi,hq,lt_min hρo (by positivity),by positivity,?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf w s x A hw hs0 hs hx y z hyz
  have hw0 : 0 < w := by linarith
  have hso : s ≤ ρo/w^2 := hs.trans (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hsk : s ≤ k/(8*w^2) := by
    have hh := hs.trans (div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg w))
    simpa only [show (k/8)/w^2 = k/(8*w^2) by ring] using hh
  apply kernel_weighted_bulk_saddle_integral ν hf0 hw (show 0 < k/2 by positivity) hK.le
    (show 0 ≤ Os+Ol by positivity) (kernelSaddleAnnulus_subset hδhi) ?_ ?_
    (measurableSet_kernelSaddleAnnulus δ w A)
  · intro a ha
    have haa := kernelSaddleAnnulus_subset hδhi ha
    have ha0 : 0 < a := by linarith [haa.1]
    have ho := houter ν hν w s a hw hs0 hso ha0
    by_cases halo : a ≤ 1/2
    · rw [if_pos halo] at ho
      have hw26 : w^2 ≤ w^6 := pow_le_pow_right₀ hw (by omega)
      have hm := mul_le_mul_of_nonneg_left hw26 hOs.le
      have hOlw : 0 ≤ Ol*w^6 := by positivity
      nlinarith
    · rw [if_neg halo] at ho
      have hOsw : 0 ≤ Os*w^6 := by positivity
      nlinarith
  · intro a ha l r M hlr hM
    have hp := hpair ν hν f hf hf0 hfD hfz hfe hνf a ha.1 w hw x hx A ha.2 y z hyz l r M hlr hM
    have hN : 1 ≤ (l : ℝ)+r+M := by
      have : 1 ≤ (M : ℝ) := by exact_mod_cast hM
      linarith [Nat.cast_nonneg (α := ℝ) l,Nat.cast_nonneg (α := ℝ) r]
    calc
      _ ≤ Real.exp (s*((l : ℝ)+r+M+1)/a) *
          (K*w*Real.exp (θ/2*x-q*A-k*((l : ℝ)+r+M)/w^2)) :=
        mul_le_mul_of_nonneg_left hp (Real.exp_nonneg _)
      _ = (K*w) * (Real.exp (s*((l : ℝ)+r+M+1)/a) *
          Real.exp (θ/2*x-q*A-k*((l : ℝ)+r+M)/w^2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (kernel_saddle_time_weight_absorb (kernelSaddleAnnulus_subset hδhi ha).1
          hk hw0 hs0 hsk hN) (by positivity)

end
end PGM
