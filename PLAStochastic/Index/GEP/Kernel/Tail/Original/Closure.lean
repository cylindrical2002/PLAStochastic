import PLAStochastic.Index.GEP.Kernel.Tail.Original.ScalarTail
import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputTail
import PLAStochastic.Index.GEP.Kernel.Output.Identification.UniformWindow
import PLAStochastic.Index.GEP.Kernel.Output.Identification.InterfaceTransfer

/-!
# Fixed-power tails on the original scalar and output kernel interfaces

The tail estimates and primitive identities initially use different legal
density representatives. Uniqueness of the original primitive identifies their
derivatives almost everywhere, so the estimates hold for every original
kernel. The power is 16 throughout; the output weight cap is chosen before the
arbitrary input exponent. No approximation or regularity assumption is used.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

theorem AEPrimitive.div_const {J j : ℝ → ℝ} (h : AEPrimitive J j) (C : ℝ) :
    AEPrimitive (fun x => J x / C) (fun x => j x / C) := by
  simpa only [div_eq_mul_inv, mul_comm] using h.const_mul C⁻¹

/-- Primitive and fixed-power tail for one actual normalized scalar kernel.
The threshold can be chosen before the arbitrary tail exponent. -/
theorem kernel_scalar_primitive_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∃ j : ℝ → ℝ,
        AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j ∧
        KernelTail (K * eps^16) ζ j := by
  obtain ⟨ep,hp⟩ := kernel_IF_influence_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨et,het,ht⟩ := kernel_regLaw_original_normalized_scalar_tail
    D θ vlo vhi hD hθ hvlo hv
  refine ⟨max ep et,het.trans (le_max_right _ _),?_⟩
  intro ζ hζ
  obtain ⟨K,hK,ht⟩ := ht ζ hζ
  refine ⟨K,hK,?_⟩
  intro eps heps ν hν
  obtain ⟨f,hf,_,_,_,_,hνf,ht⟩ := ht ν hν
  refine ⟨fun x => kernelIFInfluence ν (fun t => ENNReal.ofReal (f t)) eps x /
    lawC eps ν, ?_,ht eps ((le_max_right _ _).trans heps)⟩
  exact (hp eps ((le_max_left _ _).trans heps) ν hν _
    (ENNReal.measurable_ofReal.comp hf) hνf).1.div_const _

/-- Every derivative in the original scalar interface has the same fixed-power
tail. In particular, an independently constructed AL representative is legal. -/
theorem kernel_scalar_tail_all_primitives (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ j : ℝ → ℝ,
        AEPrimitive (fun x => lawJC eps ν x / lawC eps ν) j →
        KernelTail (K * eps^16) ζ j := by
  obtain ⟨e0,he0,ht⟩ := kernel_scalar_primitive_tail D θ vlo vhi hD hθ hvlo hv
  refine ⟨e0,he0,?_⟩
  intro ζ hζ
  obtain ⟨K,hK,ht⟩ := ht ζ hζ
  refine ⟨K,hK,?_⟩
  intro eps heps ν hν j hj
  obtain ⟨k,hk,hkt⟩ := ht eps heps ν hν
  exact hkt.congr_ae (kernel_aePrimitive_unique hj hk)

/-- Scalar primitive and tail with any measurable density of the original law.
No pointwise density envelope is needed by this transfer. -/
theorem kernel_scalar_tail_any_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ e0 : ℝ, 1 ≤ e0 ∧ ∀ ζ : ℝ, 0 < ζ → ∃ K : ℝ, 0 < K ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (ν : Measure ℝ) = volume.withDensity f →
        AEPrimitive (fun x => lawJC eps ν x / lawC eps ν)
          (fun x => kernelIFInfluence ν f eps x / lawC eps ν) ∧
        KernelTail (K * eps^16) ζ
          (fun x => kernelIFInfluence ν f eps x / lawC eps ν) := by
  obtain ⟨ep,hp⟩ := kernel_IF_influence_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨et,het,ht⟩ := kernel_scalar_tail_all_primitives D θ vlo vhi hD hθ hvlo hv
  refine ⟨max ep et,het.trans (le_max_right _ _),?_⟩
  intro ζ hζ
  obtain ⟨K,hK,ht⟩ := ht ζ hζ
  refine ⟨K,hK,?_⟩
  intro eps heps ν hν f hf hνf
  have hp := (hp eps ((le_max_left _ _).trans heps) ν hν f hf hνf).1.div_const (lawC eps ν)
  exact ⟨hp,ht eps ((le_max_right _ _).trans heps) ν hν _ hp⟩

/-- The actual output primitive and its tail share one boundary kernel. The
class weight cap precedes the arbitrary input exponent and all tests. -/
theorem kernel_output_primitive_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ ζ : ℝ, 0 < ζ →
      ∃ K e0 : ℝ, 0 < K ∧ 1 ≤ e0 ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ η : ℝ, 0 < η → η ≤ ηB →
      ∀ M : ℝ, ∀ ψ : ℝ → ℝ, OutTest η M ψ → ∃ B : ℝ → ℝ,
        IsBdryKernel eps ν ψ B ∧ KernelTail (M * (K * eps^16)) ζ B := by
  obtain ⟨ηp,ep,hηp,_,hp⟩ := output_isBdryKernel_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηt,hηt,ht⟩ := kernel_regLaw_original_output_tail D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ηp ηt,lt_min hηp hηt,?_⟩
  intro ζ hζ
  obtain ⟨et,K,het,hK,ht⟩ := ht ζ hζ
  refine ⟨K,max ep et,hK,het.trans (le_max_right _ _),?_⟩
  intro eps heps ν hν η hη hηle M ψ hψ
  obtain ⟨f,hf,_,_,_,_,hνf,ht⟩ := ht ν hν
  refine ⟨outputBoundaryKernel eps ν (fun t => ENNReal.ofReal (f t)) ψ,
    hp eps ((le_max_left _ _).trans heps) ν hν _
      (ENNReal.measurable_ofReal.comp hf) hνf η M hη
      (hηle.trans (min_le_left _ _)) ψ hψ,?_⟩
  have ht := ht eps ((le_max_right _ _).trans heps) η hη.le
    (hηle.trans (min_le_right _ _)) M ψ hψ
  have he : outputBoundaryKernel eps ν (fun t => ENNReal.ofReal (f t)) ψ =ᵐ[
      volume.restrict (Ioi (0 : ℝ))]
      outputIFBoundary eps ν (fun t => ENNReal.ofReal (f t)) ψ (lawC eps ν) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact output_boundary_kernel_pos eps ν _ ψ hx
  simpa only [mul_assoc] using ht.congr_ae he

/-- The fixed-power estimate holds for every original output boundary kernel,
independently of how its AL decomposition or density representative was chosen. -/
theorem kernel_output_tail_all_boundaries (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ ζ : ℝ, 0 < ζ →
      ∃ K e0 : ℝ, 0 < K ∧ 1 ≤ e0 ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ η : ℝ, 0 < η → η ≤ ηB →
      ∀ M : ℝ, ∀ ψ : ℝ → ℝ, OutTest η M ψ → ∀ B : ℝ → ℝ,
        IsBdryKernel eps ν ψ B → KernelTail (M * (K * eps^16)) ζ B := by
  obtain ⟨ηB,hηB,ht⟩ := kernel_output_primitive_tail D θ vlo vhi hD hθ hvlo hv
  refine ⟨ηB,hηB,?_⟩
  intro ζ hζ
  obtain ⟨K,e0,hK,he0,ht⟩ := ht ζ hζ
  refine ⟨K,e0,hK,he0,?_⟩
  intro eps heps ν hν η hη hηle M ψ hψ B hB
  obtain ⟨B',hB',ht⟩ := ht eps heps ν hν η hη hηle M ψ hψ
  exact ht.congr_ae (kernel_bdryKernel_unique hB hB')

/-- The output primitive and tail for any measurable density of the original
law, with a single class weight cap and the fixed polynomial power 16. -/
theorem kernel_output_tail_any_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ ζ : ℝ, 0 < ζ →
      ∃ K e0 : ℝ, 0 < K ∧ 1 ≤ e0 ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (ν : Measure ℝ) = volume.withDensity f →
      ∀ η : ℝ, 0 < η → η ≤ ηB → ∀ M : ℝ, ∀ ψ : ℝ → ℝ,
      OutTest η M ψ →
        IsBdryKernel eps ν ψ (outputBoundaryKernel eps ν f ψ) ∧
        KernelTail (M * (K * eps^16)) ζ (outputBoundaryKernel eps ν f ψ) := by
  obtain ⟨ηp,ep,hηp,_,hp⟩ := output_isBdryKernel_regLaw D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηt,hηt,ht⟩ := kernel_output_tail_all_boundaries D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ηp ηt,lt_min hηp hηt,?_⟩
  intro ζ hζ
  obtain ⟨K,et,hK,het,ht⟩ := ht ζ hζ
  refine ⟨K,max ep et,hK,het.trans (le_max_right _ _),?_⟩
  intro eps heps ν hν f hf hνf η hη hηle M ψ hψ
  have hp := hp eps ((le_max_left _ _).trans heps) ν hν f hf hνf η M hη
    (hηle.trans (min_le_left _ _)) ψ hψ
  exact ⟨hp,ht eps ((le_max_right _ _).trans heps) ν hν η hη
    (hηle.trans (min_le_right _ _)) M ψ hψ _ hp⟩

/-- The same representative-independent tail applies directly to the actual
output IF series, which agrees with the original boundary on positive inputs. -/
theorem kernel_output_IF_tail_any_density (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ ζ : ℝ, 0 < ζ →
      ∃ K e0 : ℝ, 0 < K ∧ 1 ≤ e0 ∧
      ∀ eps : ℝ, e0 ≤ eps → ∀ ν : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → ∀ f : ℝ → ℝ≥0∞, Measurable f →
        (ν : Measure ℝ) = volume.withDensity f →
      ∀ η : ℝ, 0 < η → η ≤ ηB → ∀ M : ℝ, ∀ ψ : ℝ → ℝ,
      OutTest η M ψ →
        KernelTail (M * (K * eps^16)) ζ
          (outputIFBoundary eps ν f ψ (lawC eps ν)) := by
  obtain ⟨ηB,hηB,ht⟩ := kernel_output_tail_any_density D θ vlo vhi hD hθ hvlo hv
  refine ⟨ηB,hηB,?_⟩
  intro ζ hζ
  obtain ⟨K,e0,hK,he0,ht⟩ := ht ζ hζ
  refine ⟨K,e0,hK,he0,?_⟩
  intro eps heps ν hν f hf hνf η hη hηle M ψ hψ
  apply (ht eps heps ν hν f hf hνf η hη hηle M ψ hψ).2.congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact (output_boundary_kernel_pos eps ν f ψ hx).symm

end
end PGM
