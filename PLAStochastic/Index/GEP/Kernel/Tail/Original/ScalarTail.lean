import PLAStochastic.Index.GEP.Kernel.Tail.Original.ScalarSum
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Mass
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Scale

/-! # The all-slope tail bound for the original scalar influence -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem kernel_scalar_original_tail_of_bounds (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi)
    (ν : ProbabilityMeasure ℝ) (hν : RegLaw D θ vlo vhi ν)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t) (hfD : ∀ t, f t ≤ D)
    (hfz : ∀ t ≤ 0, f t = 0)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    {eps K ζ : ℝ} (heps : 1 ≤ eps) (hK : 0 ≤ K)
    (hbulk : ∀ x, 0 < x → ∀ y z, kernelBulkMass ν f (2*eps) x y z ≤
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)))
    (hdirac : ∀ x, 0 < x → kernelDiracMass ν f (2*eps) x ≤
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x))) :
    KernelTail ((12*K)*(2*eps)^16) ζ (kernelIFInfluence ν (fun t => ENNReal.ofReal (f t)) eps) := by
  filter_upwards [kernel_IF_influence_enorm_le_blocks_ae ν hf hf0 hfD hfz hνf hν.ae_pos
    (show 0 ≤ eps by linarith), ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  have hnon : 0 ≤ K * (2*eps)^16 * Real.exp (ζ*x) := by positivity
  have hm := kernel_scalar_actual_block_mass_le D θ vlo vhi hD hθ hvlo hv ν hν hf hf0 heps hxpos
  have hh := hx.trans (hm.trans (mul_le_mul' le_rfl
    (add_le_add (add_le_add (hbulk x hxpos 0 (2*eps)) (hbulk x hxpos (2*eps) 0)) (hdirac x hxpos))))
  have he : (4 : ℝ≥0∞) * (ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) +
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) +
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x))) =
      ENNReal.ofReal (((12*K)*(2*eps)^16) * Real.exp (ζ*x)) := by
    rw [← ENNReal.ofReal_add hnon hnon,
      ← ENNReal.ofReal_add (add_nonneg hnon hnon) hnon]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  rw [he, Real.enorm_eq_ofReal_abs] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- A single legal density representative gives the actual scalar influence
its global tail with the fixed power 16. -/
theorem kernel_regLaw_original_scalar_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≤ D) ∧
        (∀ t ≤ 0, f t = 0) ∧ (∀ t, f t ≤ D * Real.exp (-θ*t)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)) ∧
        ∀ eps : ℝ, 1 ≤ eps →
          KernelTail (K * eps^16) ζ (kernelIFInfluence ν (fun t => ENNReal.ofReal (f t)) eps) := by
  obtain ⟨ρ, hρ, hall⟩ := kernel_regLaw_joint_weighted_tail D θ vlo vhi hD hθ hvlo hv
  intro ζ hζ
  obtain ⟨σ,K,hσ,hK,hh⟩ := hall ζ hζ
  refine ⟨12*K*2^16, by positivity, ?_⟩
  intro ν hν
  obtain ⟨f,hf,hf0,hfD,hfz,hfe,hνf,hh⟩ := hh ν hν
  refine ⟨f,hf,hf0,hfD,hfz,hfe,hνf,?_⟩
  intro eps heps
  have hb (x : ℝ) (hx : 0 < x) := hh (2*eps) 0 x (by linarith) le_rfl (by positivity) hσ.le hx
  have hbulk : ∀ x, 0 < x → ∀ y z, kernelBulkMass ν f (2*eps) x y z ≤
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) := by
    intro x hx y z
    simpa only [kernelBulkMass, kernelWeightedBulkTailTerm_zero] using (hb x hx).1 y z
  have hd : ∀ x, 0 < x → kernelDiracMass ν f (2*eps) x ≤
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) := by
    intro x hx
    have hs : Summable (kernelDiracTailTerm ν f (2*eps) x) := by
      simpa only [show kernelWeightedDiracTailTerm ν f (2*eps) 0 x = kernelDiracTailTerm ν f (2*eps) x from
        funext (kernelWeightedDiracTailTerm_zero ν f (2*eps) x)] using (hb x hx).2.1
    have hbound : (∑' m, kernelDiracTailTerm ν f (2*eps) x m) ≤ K * (2*eps)^16 * Real.exp (ζ*x) := by
      simpa only [kernelWeightedDiracTailTerm_zero] using (hb x hx).2.2
    rw [kernelDiracMass, ← ENNReal.ofReal_tsum_of_nonneg
      (kernelDiracTailTerm_nonneg ν hf0 (by linarith) hx.le) hs]
    exact ENNReal.ofReal_le_ofReal hbound
  convert kernel_scalar_original_tail_of_bounds D θ vlo vhi hD hθ hvlo hv ν hν hf hf0 hfD hfz hνf heps hK.le hbulk hd using 1; ring

/-- Dividing by the original scale C preserves the class-fixed tail power. -/
theorem kernel_regLaw_original_normalized_scalar_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≤ D) ∧
        (∀ t ≤ 0, f t = 0) ∧ (∀ t, f t ≤ D * Real.exp (-θ*t)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)) ∧
        ∀ eps : ℝ, e0 ≤ eps →
          KernelTail (K * eps^16) ζ
            (fun x => kernelIFInfluence ν (fun t => ENNReal.ofReal (f t)) eps x / lawC eps ν) := by
  obtain ⟨ηB,hηB,hscale⟩ := kernel_regLaw_tail_physical_scale D θ vlo vhi 1 hD hθ hvlo hv zero_lt_one
  obtain ⟨e0,he0,hsc⟩ := hscale 1 zero_lt_one
  refine ⟨e0,he0,?_⟩
  intro ζ hζ
  obtain ⟨K,hK,ht⟩ := kernel_regLaw_original_scalar_tail D θ vlo vhi hD hθ hvlo hv ζ hζ
  have hB : 0 < 128*regB vhi := mul_pos (by norm_num) ((regV_pos hvlo).trans_le (regV_le_regB hv))
  refine ⟨(128*regB vhi)*K,by positivity,?_⟩
  intro ν hν
  obtain ⟨f,hf,hf0,hfD,hfz,hfe,hνf,ht⟩ := ht ν hν
  refine ⟨f,hf,hf0,hfD,hfz,hfe,hνf,?_⟩
  intro eps heps
  obtain ⟨hC,hInv,_⟩ := hsc eps heps ν hν 0 le_rfl hηB.le
  filter_upwards [ht eps (he0.trans heps)] with x hx
  rw [abs_div, abs_of_pos hC]
  apply (div_le_div_of_nonneg_right hx hC.le).trans
  have hh := mul_le_mul_of_nonneg_left hInv
    (show 0 ≤ K*eps^16*Real.exp (ζ*x) by positivity)
  calc
    _ = (K*eps^16*Real.exp (ζ*x))*(1/lawC eps ν) := by ring
    _ ≤ _ := hh
    _ = _ := by ring

end
end PGM
