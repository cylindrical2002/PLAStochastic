import PLAStochastic.Index.GEP.Kernel.Output.Identification.StepExpansion

/-!
# Absolute summation of the actual inserted occupation expansion

The same argument applies to the test primitive and to its measurable direct
derivative. In particular, none of the rearrangements presupposes a bound on
an ungrouped signed infinite series.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Interval ENNReal

theorem output_step_integral_norm_le {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {eps κ A : ℝ} {F : ℝ → ℝ} (hFm : Measurable F)
    (hκ : 0 ≤ κ) (hκθ : κ ≤ θ/2) (hA : 0 ≤ A)
    (hF : ∀ s, 0 ≤ s → ‖F s‖ ≤ A * Real.exp (κ*s))
    {x : ℝ} (hx : 0 ≤ x) (a : ℕ × ℕ) :
    Integrable (outputStep eps F a x) (iidLaw ν) ∧
      (∫ g, ‖outputStep eps F a x g‖ ∂iidLaw ν) ≤
        (2*A*Real.exp (κ*x)) * fluxWindowMoment eps ν κ (a.1+1,a.2) := by
  classical
  by_cases ha : a.2 ≤ a.1
  · have he := flux_regLaw_unmarked_exp hν hθ hκ hκθ (a.1+1) a.2
    have hi := (he.indicator (measurableSet_winSet eps a.2 (a.1+1))).const_mul
      (2*A*Real.exp (κ*x))
    have hB : ∀ᵐ g ∂iidLaw ν, ‖outputStep eps F a x g‖ ≤
        (2*A*Real.exp (κ*x)) * (winSet eps a.2 (a.1+1)).indicator
          (fun g => Real.exp (κ*fluxUnmarkedSum (a.1+1) a.2 g)) g := by
      have hall : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
        rw [ae_all_iff]
        intro j
        exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving
          |>.ae hν.ae_pos
      filter_upwards [hall] with g hg
      exact output_step_bound hκ hA hF (fun j => (hg j).le) hx a
    have hI := hi.mono' (output_step_measurable eps hFm a x).aestronglyMeasurable hB
    refine ⟨hI, (integral_mono_ae hI.norm hi hB).trans_eq ?_⟩
    rw [integral_const_mul, integral_indicator (measurableSet_winSet eps a.2 (a.1+1))]
    simp only [fluxWindowMoment, show a.2 < a.1+1 by omega, if_true]
  · have hz : outputStep eps F a x = fun _ => 0 := by
      funext g
      exact if_neg ha
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    simp only [norm_zero, integral_zero, fluxWindowMoment,
      show ¬ a.2 < a.1+1 by omega, if_false, mul_zero, le_refl]

theorem output_step_norm_summable {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {eps κ A : ℝ} {F : ℝ → ℝ} (hFm : Measurable F)
    (hκ : 0 ≤ κ) (hκθ : κ ≤ θ/2) (hA : 0 ≤ A)
    (hF : ∀ s, 0 ≤ s → ‖F s‖ ≤ A * Real.exp (κ*s))
    (hWin : Summable (fluxWindowMoment eps ν κ)) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun a : ℕ × ℕ => ∫ g, ‖outputStep eps F a x g‖ ∂iidLaw ν) := by
  have hs : Summable (fun a : ℕ × ℕ => fluxWindowMoment eps ν κ (a.1+1,a.2)) :=
    hWin.comp_injective (fun a b h => by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (by simpa using h1) h2)
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun a => (output_step_integral_norm_le hν hθ hFm hκ hκθ hA hF hx a).2)
    (hs.mul_left _)

/-- The original insertion functional, including its original mark-survival
event, is the absolutely convergent birth/occupation triangle. -/
theorem output_steps_eq_insKernel {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {eps κ A : ℝ} {F : ℝ → ℝ} (hFm : Measurable F)
    (hκ : 0 ≤ κ) (hκθ : κ ≤ θ/2) (hA : 0 ≤ A)
    (hF : ∀ s, 0 ≤ s → ‖F s‖ ≤ A * Real.exp (κ*s))
    (hWin : Summable (fluxWindowMoment eps ν κ))
    (hfin : ∀ᵐ g ∂iidLaw ν, gapSegLen eps g ≠ ⊤) {x : ℝ} (hx : 0 ≤ x) :
    (∑' a : ℕ × ℕ, ∫ g, outputStep eps F a x g ∂iidLaw ν) =
      insKernel eps ν (fun g => F (stopSum eps g)) x := by
  have hnorm := output_step_norm_summable hν hθ hFm hκ hκθ hA hF hWin hx
  have hI (a : ℕ × ℕ) := (output_step_integral_norm_le hν hθ (eps := eps) hFm hκ hκθ hA hF hx a).1
  have hs : Summable (fun a : ℕ × ℕ => ∫ g, outputStep eps F a x g ∂iidLaw ν) :=
    hnorm.of_norm_bounded fun a => norm_integral_le_integral_norm _
  calc
    _ = ∑' k : ℕ, ∑' i : ℕ, ∫ g, outputStep eps F (k,i) x g ∂iidLaw ν := hs.tsum_prod
    _ = ∑' i : ℕ, ∑' k : ℕ, ∫ g, outputStep eps F (k,i) x g ∂iidLaw ν := hs.tsum_comm.symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [integral_tsum_of_summable_integral_norm (fun k => hI (k,i))
        (hnorm.prod_symm.prod_factor i)]
      apply integral_congr_ae
      filter_upwards [ae_gapSegLen_update_ne_top hfin i x] with g hg
      exact output_step_tsum F g i hg

theorem output_step_joint_measurable (eps : ℝ) {F : ℝ → ℝ} (hF : Measurable F)
    (a : ℕ × ℕ) : Measurable (fun p : ℝ × (ℕ → ℝ) => outputStep eps F a p.1 p.2) := by
  classical
  unfold outputStep
  split_ifs with ha he
  · exact ((hF.comp (rawAsm_measurable_gapKeys (a.1+1))).sub measurable_const
      |>.indicator (measurableSet_survSet eps a.1)).comp (measurable_update_pair a.2)
  · exact ((hF.comp (rawAsm_measurable_gapKeys (a.1+1))).sub
      (hF.comp (rawAsm_measurable_gapKeys a.1))
      |>.indicator (measurableSet_survSet eps a.1)).comp (measurable_update_pair a.2)
  · exact measurable_const

theorem output_step_local_mass {D θ vlo vhi : ℝ}
    {ν : ProbabilityMeasure ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ)
    {eps κ A : ℝ} {F : ℝ → ℝ} (hFm : Measurable F)
    (hκ : 0 ≤ κ) (hκθ : κ ≤ θ/2) (hA : 0 ≤ A)
    (hF : ∀ s, 0 ≤ s → ‖F s‖ ≤ A * Real.exp (κ*s)) (a : ℕ × ℕ) (R : ℝ) :
    IntervalIntegrable ((Ioi (0 : ℝ)).indicator
      (fun x => ∫ g, outputStep eps F a x g ∂iidLaw ν)) volume 0 R ∧
    (∫ x in Ι (0 : ℝ) R, ‖(Ioi (0 : ℝ)).indicator
      (fun x => ∫ g, outputStep eps F a x g ∂iidLaw ν) x‖) ≤
      (|R| * (2*A*Real.exp (κ*max 0 R))) * fluxWindowMoment eps ν κ (a.1+1,a.2) := by
  have : IsFiniteMeasure (volume.restrict (Ι (0 : ℝ) R)) := ⟨by simp [Real.volume_uIoc]⟩
  let B := (2*A*Real.exp (κ*max 0 R)) * fluxWindowMoment eps ν κ (a.1+1,a.2)
  have hB0 : 0 ≤ B := mul_nonneg (by positivity) (fluxWindowMoment_nonneg _ _ _ _)
  have hm : Measurable (fun x => ∫ g, outputStep eps F a x g ∂iidLaw ν) :=
    (output_step_joint_measurable eps hFm a).stronglyMeasurable.integral_prod_right'.measurable
  have hb : ∀ᵐ x ∂volume.restrict (Ι (0 : ℝ) R),
      ‖(Ioi (0 : ℝ)).indicator (fun x => ∫ g, outputStep eps F a x g ∂iidLaw ν) x‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
    by_cases hx0 : x ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hx0]
      exact (norm_integral_le_integral_norm _).trans
        ((output_step_integral_norm_le hν hθ hFm hκ hκθ hA hF hx0.le a).2.trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
              (mul_le_mul_of_nonneg_left hx.2 hκ)) (by positivity))
            (fluxWindowMoment_nonneg _ _ _ _)))
    · simpa only [indicator_of_notMem hx0, norm_zero] using hB0
  have hi : Integrable ((Ioi (0 : ℝ)).indicator
      (fun x => ∫ g, outputStep eps F a x g ∂iidLaw ν))
      (volume.restrict (Ι (0 : ℝ) R)) :=
    (integrable_const B).mono' (hm.indicator measurableSet_Ioi).aestronglyMeasurable hb
  refine ⟨intervalIntegrable_iff.mpr hi, ?_⟩
  calc
    _ ≤ ∫ _x in Ι (0 : ℝ) R, B := integral_mono_ae hi.norm (integrable_const _) hb
    _ = _ := by simp [B, measureReal_def, Real.volume_uIoc, smul_eq_mul, mul_assoc]

end
end PGM
