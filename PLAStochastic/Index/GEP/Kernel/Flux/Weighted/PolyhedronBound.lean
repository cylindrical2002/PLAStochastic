import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.InteriorBound
import PLAStochastic.Index.GEP.Kernel.Flux.Weighted.Polyhedron

/-!
# Quantitative primitives for weighted finite affine constraints

The whole derivative has a local L¹ bound by the compact-spatial interior
majorant plus twice the reward majorant. Empty and unbounded sections remain
part of the original finite system of inequalities.
-/

namespace PGM
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

theorem fluxPoly_weighted_primitive_bound {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (c : ι → ℝ) {d : ι → Ω → ℝ} (hd : ∀ q, Measurable (d q))
    (hac : ∀ q, (P.map (fun ω => d q ω / c q)).restrict (Ioi 0) ≪ volume)
    {F f : Ω → ℝ → ℝ} {BF Bf : ℝ → Ω → ℝ}
    (hFm : Measurable (fun p : Ω × ℝ => F p.1 p.2))
    (hfm : Measurable (fun p : Ω × ℝ => f p.1 p.2))
    (hBFi : ∀ R, Integrable (BF R) P) (hBfi : ∀ R, Integrable (Bf R) P)
    (hBF : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖F ω x‖ ≤ BF R ω)
    (hBf : ∀ R, ∀ᵐ ω ∂P, ∀ x ∈ Icc (0 : ℝ) (max 0 R), ‖f ω x‖ ≤ Bf R ω)
    (hF : ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ t in a..b, f ω t) = F ω b - F ω a) :
    ∃ j : ℝ → ℝ,
      AEPrimitive
        (fun x => ∫ ω, {ω | ∀ q, c q * x ≤ d q ω}.indicator (fun ω => F ω x) ω ∂P) j ∧
      ∀ R : ℝ, (∫ x in Ι (0 : ℝ) R, ‖j x‖) ≤
        |R| * (∫ ω, Bf R ω ∂P) + 2 * ∫ ω, BF R ω ∂P := by
  classical
  have hL := measurable_fluxPolyLower c hd
  have hacL := fluxPolyLower_ac_positive P c hd hac
  have hBF0 (R : ℝ) : ∀ᵐ ω ∂P, 0 ≤ BF R ω :=
    (hBF R).mono fun ω hω => (norm_nonneg _).trans (hω 0 ⟨le_rfl, le_max_left _ _⟩)
  have hBf0 (R : ℝ) : ∀ᵐ ω ∂P, 0 ≤ Bf R ω :=
    (hBf R).mono fun ω hω => (norm_nonneg _).trans (hω 0 ⟨le_rfl, le_max_left _ _⟩)
  by_cases h : (fluxPos c).Nonempty
  · let S := fluxPolyActive c d h
    let Q := P.restrict S
    have hS : MeasurableSet S := measurableSet_fluxPolyActive c hd h
    have hU := measurable_fluxPolyUpper c hd h
    have hLU : ∀ᵐ ω ∂Q, 0 ≤ fluxPolyLower c d ω ∧
        fluxPolyLower c d ω ≤ fluxPolyUpper c d h ω := by
      filter_upwards [ae_restrict_mem hS] with ω hω
      exact ⟨fluxPolyLower_nonneg c d ω, hω.2⟩
    obtain ⟨B, ⟨hI, a, ha⟩, hBI, hb⟩ := flux_weighted_section_bound_of_local_bound Q hL hU
      (flux_endpoint_restrict_ac_positive P hL hacL S)
      (flux_endpoint_restrict_ac_positive P hU (fluxPolyUpper_ac_positive P c hd hac h) S)
      hLU hFm hfm (fun R => (hBFi R).integrableOn) (fun R => (hBfi R).integrableOn)
      (fun R => ae_restrict_of_ae (hBF R)) (fun R => ae_restrict_of_ae (hBf R))
      (ae_restrict_of_ae hF)
    let A : Set (Ω × ℝ) := {p | fluxPolyLower c d p.1 < p.2 ∧ p.2 ≤ fluxPolyUpper c d h p.1}
    have hA : MeasurableSet A :=
      (measurableSet_lt (hL.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd (hU.comp measurable_fst))
    have hA0 : ∀ᵐ ω ∂Q, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
      hLU.mono fun ω hω t ht => hω.1.trans ht.1.le
    let H : ℝ → ℝ := fun x => ∫ ω, (Ioc (fluxPolyLower c d ω)
      (fluxPolyUpper c d h ω)).indicator (f ω) x ∂Q
    have hHI (R : ℝ) : Integrable H (volume.restrict (Ι (0 : ℝ) R)) :=
      (flux_section_integrable_prod_of_local_bound Q hA hA0 hfm
        (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBf R)) R).integral_prod_right
    refine ⟨fun x => H x + B x, ⟨hI, a, ?_⟩, fun R => ?_⟩
    · filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
      rw [flux_poly_weighted_integral_bounded P c hd hacL h F hx]
      exact hax
    · have hHmass := flux_section_interior_mass_le Q hA hA0 hfm
        (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBf R)) R
      change (∫ x in Ι (0 : ℝ) R, ‖H x‖) ≤ |R| * ∫ ω, Bf R ω ∂Q at hHmass
      calc
        _ ≤ ∫ x in Ι (0 : ℝ) R, ‖H x‖ + ‖B x‖ :=
          integral_mono ((hHI R).add (hBI R).def').norm
            ((hHI R).norm.add (hBI R).def'.norm) (fun x => norm_add_le _ _)
        _ = (∫ x in Ι (0 : ℝ) R, ‖H x‖) + ∫ x in Ι (0 : ℝ) R, ‖B x‖ :=
          integral_add (hHI R).norm (hBI R).def'.norm
        _ ≤ |R| * (∫ ω, Bf R ω ∂Q) + 2 * ∫ ω, BF R ω ∂Q := add_le_add hHmass (hb R)
        _ ≤ _ := add_le_add
          (mul_le_mul_of_nonneg_left (setIntegral_le_integral (hBfi R) (hBf0 R)) (abs_nonneg R))
          (mul_le_mul_of_nonneg_left (setIntegral_le_integral (hBFi R) (hBF0 R)) (by norm_num))
  · let S := fluxPolyZeroOK c d
    let Q := P.restrict S
    have hL0 : ∀ᵐ ω ∂Q, 0 ≤ fluxPolyLower c d ω :=
      Eventually.of_forall fun ω => fluxPolyLower_nonneg c d ω
    obtain ⟨B, ⟨hI, a, ha⟩, hBI, hb⟩ := flux_weighted_halfLine_bound_of_local_bound Q hL
      (flux_endpoint_restrict_ac_positive P hL hacL S) hL0 hFm hfm
      (fun R => (hBFi R).integrableOn) (fun R => (hBfi R).integrableOn)
      (fun R => ae_restrict_of_ae (hBF R)) (fun R => ae_restrict_of_ae (hBf R))
      (ae_restrict_of_ae hF)
    let A : Set (Ω × ℝ) := {p | fluxPolyLower c d p.1 < p.2}
    have hA : MeasurableSet A := measurableSet_lt (hL.comp measurable_fst) measurable_snd
    have hA0 : ∀ᵐ ω ∂Q, ∀ t, (ω, t) ∈ A → 0 ≤ t :=
      hL0.mono fun ω hω t ht => hω.trans ht.le
    let H : ℝ → ℝ := fun x => ∫ ω, (Ioi (fluxPolyLower c d ω)).indicator (f ω) x ∂Q
    have hHI (R : ℝ) : Integrable H (volume.restrict (Ι (0 : ℝ) R)) :=
      (flux_section_integrable_prod_of_local_bound Q hA hA0 hfm
        (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBf R)) R).integral_prod_right
    refine ⟨fun x => H x + B x, ⟨hI, a, ?_⟩, fun R => ?_⟩
    · filter_upwards [ha, ae_restrict_mem measurableSet_Ioi] with x hax hx
      rw [flux_poly_weighted_integral_halfLine P c hd hacL h F hx]
      exact hax
    · have hHmass := flux_section_interior_mass_le Q hA hA0 hfm
        (fun R => (hBfi R).integrableOn) (fun R => ae_restrict_of_ae (hBf R)) R
      change (∫ x in Ι (0 : ℝ) R, ‖H x‖) ≤ |R| * ∫ ω, Bf R ω ∂Q at hHmass
      calc
        _ ≤ ∫ x in Ι (0 : ℝ) R, ‖H x‖ + ‖B x‖ :=
          integral_mono ((hHI R).add (hBI R).def').norm
            ((hHI R).norm.add (hBI R).def'.norm) (fun x => norm_add_le _ _)
        _ = (∫ x in Ι (0 : ℝ) R, ‖H x‖) + ∫ x in Ι (0 : ℝ) R, ‖B x‖ :=
          integral_add (hHI R).norm (hBI R).def'.norm
        _ ≤ |R| * (∫ ω, Bf R ω ∂Q) + ∫ ω, BF R ω ∂Q := add_le_add hHmass (hb R)
        _ ≤ |R| * (∫ ω, Bf R ω ∂P) + ∫ ω, BF R ω ∂P := add_le_add
          (mul_le_mul_of_nonneg_left (setIntegral_le_integral (hBfi R) (hBf0 R)) (abs_nonneg R))
          (setIntegral_le_integral (hBFi R) (hBF0 R))
        _ ≤ _ := by linarith [integral_nonneg_of_ae (hBF0 R)]

end
end PGM
