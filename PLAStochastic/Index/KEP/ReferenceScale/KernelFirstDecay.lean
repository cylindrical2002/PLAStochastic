import PLAStochastic.Index.KEP.ReferenceScale.LongKernelBudgets
import PLAStochastic.Index.KEP.ReferenceScale.ActualLongKernelSlope

/-!
# Direct first derivatives with the actual killed spectral decay

Two endpoint steps and the killed L2 contraction bound a row at arbitrary
endpoints. A final genuine convolution places the derivative on the input
density once. Unlike an unweighted rough bound, this estimate retains the
geometric decay needed when a differentiated factor occurs in a pin graph.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem krDens_le_spectral_two_steps
    (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (n : ℕ) (x y : ℝ) :
    krDens (Icc 0 w) ν f β a' (n + 2) x y ≤
      2 * D * Real.sqrt (krLam D vlo vhi w) ^ n := by
  have hD : 0 < D := H.hD
  have hR := integral_sq_krDens_le_two_D ν H 0 x
  have hL : (∫ z, krDens (Icc 0 w) ν f β a' 1 z y ^ 2) ≤ 2 * D := by
    calc
      _ = ∫ z, krDens (Icc 0 w) ν f (-β) (-a') 1 y z ^ 2 := by
        apply integral_congr_ae
        exact ae_of_all _ fun z => by
          simpa only [Nat.zero_add] using congrArg (fun t : ℝ => t ^ 2)
            (krDens_symm ν (β := β) H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' 0 z y)
      _ ≤ _ := integral_sq_krDens_le_two_D ν H.rev 0 y
  have h := sq_krDens_add_krRow_le ν H 0 n 0 x y
  have hL0 : (0 : ℝ) ≤ ∫ z, krDens (Icc 0 w) ν f β a' 1 z y ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hlam0 : 0 ≤ krLam D vlo vhi w ^ n := pow_nonneg H.lam_nonneg n
  apply kr_le_of_sq_le (by positivity)
  calc
    _ ≤ (∫ z, krDens (Icc 0 w) ν f β a' 1 x z ^ 2) *
        (krLam D vlo vhi w ^ n * ∫ z, krDens (Icc 0 w) ν f β a' 1 z y ^ 2) := by
      simpa only [Nat.zero_add, Nat.zero_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    _ ≤ (2 * D) * (krLam D vlo vhi w ^ n * (2 * D)) := by
      exact mul_le_mul hR (mul_le_mul_of_nonneg_left hL hlam0)
        (mul_nonneg hlam0 hL0) (by positivity)
    _ = _ := by
      rw [mul_pow, kr_sqrt_pow_sq H.lam_nonneg n]
      ring

theorem krDens_first_spectral_bound
    (ν : ProbabilityMeasure ℝ) {f f' : ℝ → ℝ} {D θ vlo vhi K L w A a β a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a')
    (hpi' : Integrable f' volume) (n : ℕ) (x y : ℝ) :
    |truncatedConvolution 0 w (kepStepSpatialFirst f' β a')
        (fun z => krDens (Icc 0 w) ν f β a' (n + 2) x z) y| ≤
      4 * D * (∫ t, |f' t|) * Real.sqrt (krLam D vlo vhi w) ^ n := by
  have hD : 0 < D := H.hD
  have hJ : (0 : ℝ) ≤ ∫ t, |f' t| := integral_nonneg fun _ => abs_nonneg _
  have ha : 1 / 2 ≤ |a'| := H.ha₁'
  have ha0 : 0 < |a'| := by linarith
  have h1 : (∫ t, |f' t|) / |a'| ≤ 2 * (∫ t, |f' t|) :=
    (div_le_iff₀ ha0).mpr (by nlinarith)
  have hb := abs_truncatedConvolution_le_input_bound (a := 0) (b := w)
    (integrable_kepStepSpatialFirst hpi' H.ha' β)
    (measurable_krDens_right ν H.hJ H.hf β a' (n + 2) x)
    (by positivity : 0 ≤ 2 * D * Real.sqrt (krLam D vlo vhi w) ^ n)
    (fun z _ => by
      rw [abs_of_nonneg (krDens_nonneg ν H.hf0 (n + 2) x z)]
      exact krDens_le_spectral_two_steps ν H n x z) y
  rw [integral_abs_kepStepSpatialFirst f' β H.ha'] at hb
  apply hb.trans
  have hmul := mul_le_mul_of_nonneg_right h1
    (by positivity : 0 ≤ 2 * D * Real.sqrt (krLam D vlo vhi w) ^ n)
  nlinarith

/-- The actual reference orbit supplies all class and derivative hypotheses. -/
theorem kepReference_first_spectral_uniform :
    ∃ D vlo vhi eps0 : ℝ, 0 < D ∧ 0 < vlo ∧ vlo ≤ vhi ∧
      kepReferenceClassicalThreshold ≤ eps0 ∧
      ∀ eps, eps0 ≤ eps → ∀ heps : kepReferenceClassicalThreshold ≤ eps,
        ∀ j, ∀ hj : 1 ≤ j, ∀ w a σ : ℝ, 1 ≤ w → 1 / 2 ≤ a → a ≤ 2 →
        (σ = 1 ∨ σ = -1) → ∀ n : ℕ, ∀ x y : ℝ,
        let f := (kepReferenceDensity heps hj).density
        let f' := gammaScaledFirst (kepReferenceWeights eps j) (kepReferenceSpan eps j)
        |truncatedConvolution 0 w (kepStepSpatialFirst f' σ (σ * a))
            (fun z => krDens (Icc 0 w) (kepReferenceLaw eps j) f σ (σ * a) (n + 2) x z) y| ≤
          12 * D * Real.sqrt (1 + kepReferenceSecondNorm eps j) *
            Real.sqrt (krLam D vlo vhi w) ^ n := by
  obtain ⟨D, θ, vlo, vhi, K, L, e0, hD, -, hvlo, hvhi, -, -, he0, hband⟩ :=
    kepReferenceBand_uniform
  refine ⟨D, vlo, vhi, e0, hD, hvlo, hvhi, he0, ?_⟩
  intro eps he heps j hj w a σ hw ha ha2 hσ n x y
  dsimp only
  obtain ⟨hf, hr⟩ := hband eps he heps j hj w a hw ha ha2
  have H : KrBand D θ vlo vhi K L (kepReferenceLaw eps j)
      (kepReferenceDensity heps hj).density w w a σ (σ * a) := by
    rcases hσ with rfl | rfl
    · simpa only [one_mul] using hf
    · simpa only [neg_one_mul] using hr
  apply (krDens_first_spectral_bound (kepReferenceLaw eps j) H
    (kepReferenceDensity_classical heps hj).2.2.2.2.1 n x y).trans
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (kepReferenceFirstNorm_le_sqrt heps hj)
      (by positivity : 0 ≤ 4 * D))
    (by positivity : 0 ≤ Real.sqrt (krLam D vlo vhi w) ^ n)
  convert hfirst using 1
  ring

end

end PGM
