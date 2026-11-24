import PLAStochastic.Index.KEP.ReferenceScale.PrefixWeakOutput
import PLAStochastic.Index.KEP.ReferenceScale.PhysicalOutputTests

/-!
# Summing the true output second test from its paid physical prefix budgets

This assembly preserves the actual output law and original cutoff identity.
Its two prefix-budget inputs are discharged on that law in the subsequent
uniform output theorem; the assembly does not replace the reference process.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

theorem kepReference_output_second_budget_assembly (eps theta : ℝ) (j M : ℕ)
    (hC1 : 1 ≤ lawC eps (kepReferenceLaw eps j)) (hM : 16 * eps ≤ (M : ℝ))
    (hnu : (kepReferenceLaw eps j : Measure ℝ) (Iic 0) = 0)
    {H A D : ℝ} (hH : 0 ≤ H) (_hA : 0 ≤ A) (hD : 0 ≤ D)
    (hmgf : Integrable (fun x => Real.exp ((theta / lawC eps (kepReferenceLaw eps j)) * x))
      (kepReferenceLaw eps j : Measure ℝ))
    (hmgfb : (∫ x, Real.exp ((theta / lawC eps (kepReferenceLaw eps j)) * x)
      ∂(kepReferenceLaw eps j : Measure ℝ)) ≤ H - 1)
    (hsurv : ∀ psi psi' psi'' : ℝ → ℝ,
      (∀ x, HasDerivAt psi (psi' x) x) → (∀ x, HasDerivAt psi' (psi'' x) x) →
      Continuous psi'' → ∀ L : ℝ,
        (∀ t, |psi t| ≤ L ∧ |psi' t| ≤ L ∧ |psi'' t| ≤ L) →
      ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |psi t| ≤
        B * Real.exp (theta * t / lawC eps (kepReferenceLaw eps j))) →
      let F := fun n : ℕ => if 16 * eps ≤ (n : ℝ) then
        |∫ g in {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g},
          psi'' (gapKeys g n) ∂iidLaw (kepReferenceLaw eps j)| else 0
      Summable F ∧ (∑' n : ℕ, F n) ≤ B * A)
    (hstop : ∀ n : ℕ, n ≤ M → ∀ psi psi' psi'' : ℝ → ℝ,
      (∀ x, HasDerivAt psi (psi' x) x) → (∀ x, HasDerivAt psi' (psi'' x) x) →
      Continuous psi'' → ∀ L : ℝ,
        (∀ t, |psi t| ≤ L ∧ |psi' t| ≤ L ∧ |psi'' t| ≤ L) →
      ∀ B : ℝ, 0 ≤ B → (∀ t, 0 ≤ t → |psi t| ≤
        B * Real.exp (theta * t / lawC eps (kepReferenceLaw eps j))) →
      |∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)},
        psi'' (gapKeys g n) ∂iidLaw (kepReferenceLaw eps j)| ≤ B * D * (n + 1 : ℝ))
    (houtput : ∀ psi : ℝ → ℝ, Measurable psi → ∀ L : ℝ, 0 ≤ L →
      (∀ x, |psi x| ≤ L) →
      (∫ x, psi x ∂(kepReferenceLaw eps (j + 1) : Measure ℝ)) =
        (∫ g, psi (gapKeys g M / lawC eps (kepReferenceLaw eps j)) ∂iidLaw (kepReferenceLaw eps j)) +
        (∑' k : ℕ, kepReferenceSurvivingIncrement eps j psi (k + M)) -
        ∑ k ∈ range M, kepReferenceStoppedIncrement eps j psi k)
    {phi phi' phi'' : ℝ → ℝ}
    (hdphi : ∀ x, HasDerivAt phi (phi' x) x) (hddphi : ∀ x, HasDerivAt phi' (phi'' x) x)
    (hcphi'' : Continuous phi'') {L B : ℝ}
    (hb : ∀ t, |phi t| ≤ L ∧ |phi' t| ≤ L ∧ |phi'' t| ≤ L)
    (hB : 0 ≤ B) (hphiB : ∀ t, 0 ≤ t → |phi t| ≤ B * Real.exp (theta * t)) :
    |∫ x, phi'' x ∂(kepReferenceLaw eps (j + 1) : Measure ℝ)| ≤
      (lawC eps (kepReferenceLaw eps j)) ^ 2 * B * (1 + H) * (A + (M + 1 : ℝ) ^ 2 * D) := by
  let nu := kepReferenceLaw eps j
  let C := lawC eps nu
  have hCp : 0 < C := by dsimp only [C, nu]; linarith
  have hL : 0 ≤ L := (abs_nonneg (phi 0)).trans (hb 0).1
  let Phi := fun t : ℝ => phi (t / C)
  let Phi' := fun t : ℝ => phi' (t / C) / C
  let Phi'' := fun t : ℝ => phi'' (t / C) / C ^ 2
  have hs := kep_scaled_output_test_C2 hdphi hddphi hcphi'' hC1 hb
  have hPhi : ∀ t, 0 ≤ t → |Phi t| ≤ B * Real.exp (theta * t / C) := by
    intro t ht
    simpa only [mul_div_assoc] using hphiB (t / C) (by positivity)
  let Psi := kepConvolutionTest nu Phi
  let Psi' := kepConvolutionTest nu Phi'
  let Psi'' := kepConvolutionTest nu Phi''
  have hcPhi := continuous_iff_continuousAt.mpr fun x => (hs.1 x).continuousAt
  have hc := kepConvolutionTest_C2 nu hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
  have hPsi : ∀ t, 0 ≤ t → |Psi t| ≤ (B * H) * Real.exp (theta * t / C) := by
    intro t ht
    have hh := kepConvolutionTest_exponential_bound nu hnu hcPhi.measurable
      (fun x => (hs.2.2.2 x).1) hB (fun x hx => by
        simpa only [div_mul_eq_mul_div] using hPhi x hx) hmgf t ht
    apply hh.trans
    have hco : 1 + ∫ x, Real.exp ((theta / C) * x) ∂(nu : Measure ℝ) ≤ H := by linarith [hmgfb]
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hco hB)
      (Real.exp_pos ((theta / C) * t)).le using 1
    first | rfl | (rw [div_mul_eq_mul_div])
  let V := fun (psi : ℝ → ℝ) (n : ℕ) => ∫ g in {g : ℕ → ℝ | (n : ℕ∞) < gapSegLen eps g}, psi (gapKeys g n) ∂iidLaw nu
  let W := fun (psi : ℝ → ℝ) (n : ℕ) => ∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (n : ℕ∞)}, psi (gapKeys g n) ∂iidLaw nu
  obtain ⟨hsPhi, hbPhi⟩ := hsurv Phi Phi' Phi'' hs.1 hs.2.1 hs.2.2.1 L hs.2.2.2 B hB hPhi
  obtain ⟨hsPsi, hbPsi⟩ := hsurv Psi Psi' Psi'' hc.1 hc.2.1 hc.2.2.1 (2 * L) hc.2.2.2
    (B * H) (mul_nonneg hB hH) hPsi
  have htail := kep_masked_series_tail_budget hsPsi M hM
  have hsingle := (kep_masked_series_tail_budget hsPhi M hM).2.2.trans hbPhi
  have hstopPhi := hstop M le_rfl Phi Phi' Phi'' hs.1 hs.2.1 hs.2.2.1 L hs.2.2.2 B hB hPhi
  have hstopPsi (k : ℕ) (hk : k ≤ M) :=
    hstop k hk Psi Psi' Psi'' hc.1 hc.2.1 hc.2.2.1 (2 * L) hc.2.2.2 (B * H) (mul_nonneg hB hH) hPsi
  have hfree : |∫ g, Phi'' (gapKeys g M) ∂iidLaw nu| ≤ B * A + B * D * (M + 1 : ℝ) := by
    rw [kep_free_prefix_second_split nu eps M hs.2.2.1.measurable (fun t => (hs.2.2.2 t).2.2)]
    exact (abs_add_le _ _).trans (add_le_add hsingle hstopPhi)
  have hsurvId (k : ℕ) : kepReferenceSurvivingIncrement eps j phi'' k = C ^ 2 * V Psi'' k := by
    change (∫ g in {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g},
      kepPrefixConvolutionIncrement nu C phi'' k g ∂iidLaw nu) = _
    simp_rw [kep_physical_convolution_second_identity nu hCp.ne' phi'' k]
    exact integral_const_mul _ _
  have hstopId (k : ℕ) : kepReferenceStoppedIncrement eps j phi'' k = C ^ 2 * W Psi'' k := by
    change (∫ g in {g : ℕ → ℝ | gapSegLen eps g ≤ (k : ℕ∞)},
      kepPrefixConvolutionIncrement nu C phi'' k g ∂iidLaw nu) = _
    simp_rw [kep_physical_convolution_second_identity nu hCp.ne' phi'' k]
    exact integral_const_mul _ _
  have hnorm : |∑' k : ℕ, V Psi'' (k + M)| ≤ B * H * A := by
    have hsNorm : Summable (fun k : ℕ => ‖V Psi'' (k + M)‖) := by
      simpa only [Real.norm_eq_abs] using htail.1
    have hn : |∑' k : ℕ, V Psi'' (k + M)| ≤ ∑' k : ℕ, |V Psi'' (k + M)| := by
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hsNorm
    exact hn.trans (htail.2.1.trans hbPsi)
  have hfinite : |∑ k ∈ range M, W Psi'' k| ≤ B * H * D * (M + 1 : ℝ) ^ 2 := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hbterm (k : ℕ) (hk : k ∈ range M) : |W Psi'' k| ≤ B * H * D * (M + 1 : ℝ) := by
      have hkM : k ≤ M := (mem_range.mp hk).le
      apply (hstopPsi k hkM).trans
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.add_le_add_right hkM 1) (by positivity)
    apply (Finset.sum_le_card_nsmul (range M) _ _ hbterm).trans
    simp only [card_range, nsmul_eq_mul]
    calc
      _ = (B * H * D) * ((M : ℝ) * (M + 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith [Nat.cast_nonneg (α := ℝ) M]) (by positivity)
  rw [houtput phi'' hcphi''.measurable L hL (fun x => (hb x).2.2),
    kep_physical_free_second_identity nu hCp.ne' phi'' M]
  simp_rw [hsurvId, hstopId, tsum_mul_left, ← Finset.mul_sum]
  apply (abs_sub _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg C)]
  have hsum := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfree (sq_nonneg C))
    (mul_le_mul_of_nonneg_left hnorm (sq_nonneg C)))
    (mul_le_mul_of_nonneg_left hfinite (sq_nonneg C))
  apply hsum.trans
  have hm : (M + 1 : ℝ) ≤ (M + 1 : ℝ) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hmul := mul_le_mul_of_nonneg_left hm (mul_nonneg hB hD)
  nlinarith only [mul_le_mul_of_nonneg_left hmul (sq_nonneg C)]

end

end PGM
