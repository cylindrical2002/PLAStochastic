import PLAStochastic.Index.GEP.Kernel.FarSlope.OriginalMass
import PLAStochastic.Index.GEP.Kernel.Influence.Signed.SlopeError
import PLAStochastic.Index.GEP.Kernel.Leaves.OutputExteriorCut
import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputTail
import PLAStochastic.Index.GEP.Kernel.Insertion.SlopeWindow

/-!
# The actual output boundary differs from its near part by a small error

The physical absolute mass proves finiteness before the signed slope partition
is used. The output exponent is fixed before the spatial logarithmic window.
The density supplied by the actual full-tail estimates works at every tolerance.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1800000

theorem kernelPositiveBoundaryReward_abs_le (ν : ProbabilityMeasure ℝ)
    (C : ℝ) (ψ : ℝ → ℝ) (s : ℝ) :
    |kernelPositiveBoundaryReward ν C ψ s| ≤ |kernelBoundaryReward ν C ψ s| := by
  unfold kernelPositiveBoundaryReward
  by_cases hs : s ∈ Ici (0 : ℝ)
  · rw [indicator_of_mem hs]
  · rw [indicator_of_notMem hs, abs_zero]
    exact abs_nonneg _

/-- Finiteness of the original absolute physical reward justifies the exact
signed partition; the far mass may retain the original uncut reward. -/
theorem output_IF_near_error_of_mass {D θ vlo vhi η M C eps R E : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hψ : OutTest η M ψ) {f : ℝ → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D) (hfz : ∀ x ≤ 0, f x = 0)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (heps : 0 ≤ eps) {S : Set ℝ} (hS : MeasurableSet S) (hE : 0 ≤ E)
    (hfin : ∀ x, 0 < x → kernelIFTotalPinBlockMass ν f eps
      (fun s => ENNReal.ofReal |kernelBoundaryReward ν C ψ s|) (fun _ => True) x ≠ ∞)
    (hfar : ∀ x ∈ Ioo (0 : ℝ) R, kernelIFTotalPinBlockMassOn ν f eps Sᶜ
      (fun s => ENNReal.ofReal |kernelBoundaryReward ν C ψ s|) (fun _ => True) x ≤
        ENNReal.ofReal E) :
    ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) R),
      |outputIFBoundary eps ν (fun x => ENNReal.ofReal (f x)) ψ C x -
        kernelIFTotalPinBoundaryOn ν f eps S (kernelPositiveBoundaryReward ν C ψ) x| ≤ 4*E := by
  have he := output_IF_boundary_eq_cut_pins_ae ν hf hf0 hfD hfz hνf hν.ae_pos heps
    (C := C) hψ
  have hm (s : ℝ) := ENNReal.ofReal_le_ofReal (kernelPositiveBoundaryReward_abs_le ν C ψ s)
  filter_upwards [ae_restrict_of_ae he, ae_restrict_mem measurableSet_Ioo] with x hx hxR
  rw [hx]
  have hfc := ne_top_of_le_ne_top (hfin x hxR.1)
    (kernel_IF_total_block_mass_mono ν f eps x hm (A := fun _ => True)
      (fun _ _ => trivial))
  have hb := (kernel_IF_total_block_massOn_mono ν f eps Sᶜ x hm (A := fun _ => True)
    (fun _ _ => trivial)).trans
    (hfar x hxR)
  have hb' := ENNReal.toReal_mono (by finiteness : ENNReal.ofReal E ≠ ∞) hb
  rw [ENNReal.toReal_ofReal hE] at hb'
  exact (kernel_IF_total_near_error_le ν f eps hS _ hxR.1 hfc).trans
    (mul_le_mul_of_nonneg_left hb' (by norm_num))

/-- The complementary slopes contribute `O(M / eps)` to the actual output
boundary on every prescribed logarithmic spatial window. All physical times
and the short deterministic bridge are included. -/
theorem kernel_regLaw_output_near_error (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ b : ℝ, 0 < b →
    ∃ α K e0 : ℝ, 0 < α ∧ 0 < K ∧ 2 ≤ e0 ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ D) ∧
        (∀ x ≤ 0, f x=0) ∧ (∀ x, f x ≤ D*Real.exp (-θ*x)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) ∧
        ∀ eps : ℝ, e0 ≤ eps → ∀ η M : ℝ, 0 ≤ η → η ≤ ηB →
        ∀ ψ : ℝ → ℝ, OutTest η M ψ →
          (∀ x, 0 < x → kernelIFTotalPinBlockMass ν f eps
            (fun s => ENNReal.ofReal |kernelPositiveBoundaryReward ν (lawC eps ν) ψ s|)
            (fun _ => True) x ≠ ∞) ∧
          ∀ᵐ x ∂volume.restrict (Ioo (0 : ℝ) (b*Real.log eps)),
            |outputIFBoundary eps ν (fun x => ENNReal.ofReal (f x)) ψ (lawC eps ν) x -
              kernelIFTotalPinBoundaryOn ν f eps
                (kernelNearSlopes (2*eps) (α*Real.log (2*eps)))
                (kernelPositiveBoundaryReward ν (lawC eps ν) ψ) x| ≤ M*(K/eps) := by
  obtain ⟨ρf,hρf,hfar⟩ := kernel_regLaw_original_output_far_mass D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρt,hρt,htail⟩ := kernel_regLaw_joint_weighted_tail D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρo,hρo,houter⟩ := kernel_regLaw_physical_outer_pair_sum D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηB,hηB,hscale⟩ := kernel_regLaw_tail_physical_scale D θ vlo vhi
    (min ρf (min ρt ρo)) hD hθ hvlo hv (lt_min hρf (lt_min hρt hρo))
  obtain ⟨σ,Kt,hσ,hKt,ht⟩ := htail 1 zero_lt_one
  obtain ⟨es,hes,hsc⟩ := hscale (min σ (θ/4)) (lt_min hσ (by positivity))
  refine ⟨ηB,hηB,?_⟩
  intro b hb
  obtain ⟨α,Kf,wf,hα,hKf,hwf,hfars⟩ := hfar b hb 1
  let B := 128*regB vhi
  have hB : 0 < B := mul_pos (by norm_num) ((regV_pos hvlo).trans_le (regV_le_regB hv))
  let K := 4*(8*D/θ^2)*B*Kf
  let e0 := max 2 (max es wf)
  refine ⟨α,K,e0,hα,by dsimp [K]; positivity,le_max_left _ _,?_⟩
  intro ν hν
  obtain ⟨f,hf,hf0,hfD,hfz,hfe,hνf,hbt⟩ := ht ν hν
  refine ⟨f,hf,hf0,hfD,hfz,hfe,hνf,?_⟩
  intro eps heps η M hη hηle ψ hψ
  have he2 : 2 ≤ eps := (le_max_left 2 (max es wf)).trans heps
  have he1 : 1 ≤ eps := by linarith
  have he0 : 0 < eps := by linarith
  have heS : es ≤ eps := (le_max_of_le_right (le_max_left es wf)).trans heps
  have heF : wf ≤ 2*eps := by
    have hh := (show wf ≤ e0 from le_max_of_le_right (le_max_right es wf)).trans heps
    linarith
  obtain ⟨hC,hInv,hsρ,hsσ⟩ := hsc eps heS ν hν η hη hηle
  have hs0 : 0 ≤ η/lawC eps ν := by positivity
  have hsf := hsρ.trans (div_le_div_of_nonneg_right (min_le_left ρf (min ρt ρo)) (sq_nonneg _))
  have hst := hsρ.trans (div_le_div_of_nonneg_right
    ((min_le_right ρf (min ρt ρo)).trans (min_le_left ρt ρo)) (sq_nonneg _))
  have hso := hsρ.trans (div_le_div_of_nonneg_right
    ((min_le_right ρf (min ρt ρo)).trans (min_le_right ρt ρo)) (sq_nonneg _))
  have hscaleθ := hsσ.trans (min_le_right σ (θ/4))
  have ho (a : ℝ) (ha : 0 < a) :=
    houter ν hν (2*eps) (η/lawC eps ν) a (by linarith) hs0 hso ha
  have hfinite (x : ℝ) (hx : 0 < x) : kernelIFTotalPinBlockMass ν f eps
      (fun s => ENNReal.ofReal |kernelBoundaryReward ν (lawC eps ν) ψ s|)
      (fun _ => True) x ≠ ∞ := by
    obtain ⟨hb,hds,hdb⟩ := hbt (2*eps) (η/lawC eps ν) x (by linarith) hs0 hst
      (hsσ.trans (min_le_left σ (θ/4))) hx
    have hm := kernel_output_actual_block_mass_le hν hθ hψ hη hC hscaleθ hf hf0 he1 hx ho
      (measurable_kernelPhysicalOuterPairAt ν (2*eps) (η/lawC eps ν))
    have hd : kernelWeightedDiracMass ν f (2*eps) (η/lawC eps ν) x ≤
        ENNReal.ofReal (Kt*(2*eps)^16*Real.exp (1*x)) := by
      rw [kernelWeightedDiracMass, ← ENNReal.ofReal_tsum_of_nonneg
        (kernelWeightedDiracTailTerm_nonneg ν hf0 _ (by linarith) hx.le) hds]
      exact ENNReal.ofReal_le_ofReal hdb
    apply ne_top_of_le_ne_top _ hm
    have hb0 : kernelWeightedBulkMass ν f (2*eps) (η/lawC eps ν) x 0 (2*eps)
        (volume.restrict (Ioi (0 : ℝ))) ≠ ∞ := ne_top_of_le_ne_top (by finiteness) (hb 0 (2*eps))
    have hbw : kernelWeightedBulkMass ν f (2*eps) (η/lawC eps ν) x (2*eps) 0
        (volume.restrict (Ioi (0 : ℝ))) ≠ ∞ := ne_top_of_le_ne_top (by finiteness) (hb (2*eps) 0)
    have hd0 := ne_top_of_le_ne_top (by finiteness : ENNReal.ofReal (Kt*(2*eps)^16*Real.exp (1*x)) ≠ ∞) hd
    finiteness
  constructor
  · intro x hx
    exact ne_top_of_le_ne_top (hfinite x hx)
      (kernel_IF_total_block_mass_mono ν f eps x
        (fun s => ENNReal.ofReal_le_ofReal (kernelPositiveBoundaryReward_abs_le ν (lawC eps ν) ψ s))
        (fun _ _ => trivial))
  · let S := kernelNearSlopes (2*eps) (α*Real.log (2*eps))
    let E := (M*(8*D/θ^2)/lawC eps ν)*(Kf/(2*eps))
    have hM := hψ.nonneg
    have hE : 0 ≤ E := by dsimp [E]; positivity
    have hm := output_IF_near_error_of_mass hν hψ hf hf0 hfD hfz hνf he0.le
      (S := S) (measurableSet_kernelNearSlopes _ _) hE hfinite
      (R := b*Real.log eps) (fun x hx => by
        have hh := (hfars eps he1 heF).2.2 ν hν f hf hf0 hfD hfz hfe hνf
          η M (lawC eps ν) hη hC hscaleθ hsf ψ hψ Sᶜ
          (measurableSet_kernelNearSlopes _ _).compl
          (fun a ha _ => le_of_not_gt (fun h => ha ((kernelNearSlopes_iff (by positivity)).mpr h))) x
          ⟨hx.1,hx.2.le.trans (mul_le_mul_of_nonneg_left
            (Real.log_le_log he0 (by linarith : eps ≤ 2*eps)) hb.le)⟩
        simpa only [pow_one] using hh)
    filter_upwards [hm] with x hx
    apply hx.trans
    have hcoef := mul_le_mul_of_nonneg_left hInv
      (show 0 ≤ 4*M*(8*D/θ^2)*(Kf/(2*eps)) by positivity)
    have hden : Kf/(2*eps) ≤ Kf/eps := div_le_div_of_nonneg_left hKf.le he0 (by linarith)
    calc
      4*E = (4*M*(8*D/θ^2)*(Kf/(2*eps)))*(1/lawC eps ν) := by dsimp [E]; ring
      _ ≤ (4*M*(8*D/θ^2)*(Kf/(2*eps)))*B := hcoef
      _ ≤ (4*M*(8*D/θ^2)*(Kf/eps))*B := by gcongr
      _ = M*(K/eps) := by dsimp [K]; ring

end
end PGM
