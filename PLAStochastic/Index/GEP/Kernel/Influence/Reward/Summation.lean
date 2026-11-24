import PLAStochastic.Index.GEP.Kernel.Influence.Reward.OutputBoundary

/-! # Absolute convergence and signed regrouping of physical reward masses -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1200000

theorem kernel_IF_total_facet_pin_mono (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) {k : ℕ} (q : FluxFacetIndex k) (i : ℕ) (x : ℝ)
    {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, H₁ s ≤ H₂ s) :
    kernelIFFacetTotalPinDensity ν f eps q i H₁ x ≤
      kernelIFFacetTotalPinDensity ν f eps q i H₂ x := by
  classical
  unfold kernelIFFacetTotalPinDensity
  split_ifs <;> try exact le_rfl
  · unfold kernelIFLeftTotalPinDensity
    gcongr with a g
    exact hH _
  · unfold kernelIFLeftTotalDiracPinDensity
    gcongr with g
    exact hH _
  · unfold kernelIFRightTotalPinDensity
    gcongr with a g
    exact hH _
  · unfold kernelIFRightTotalDiracPinDensity
    gcongr with g
    exact hH _

theorem kernel_IF_total_block_mass_mono (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps x : ℝ) {H₁ H₂ : ℝ → ℝ≥0∞} (hH : ∀ s, H₁ s ≤ H₂ s)
    {A B : KernelIFSourceIndex → Prop} (hAB : ∀ b, A b → B b) :
    kernelIFTotalPinBlockMass ν f eps H₁ A x ≤ kernelIFTotalPinBlockMass ν f eps H₂ B x := by
  classical
  rw [← kernel_IF_total_pin_mass_reindex, ← kernel_IF_total_pin_mass_reindex]
  apply ENNReal.tsum_le_tsum
  intro b
  by_cases ha : A b
  · simp only [if_pos ha, if_pos (hAB b ha)]
    exact kernel_IF_total_facet_pin_mono ν f eps b.2.2 b.2.1 x hH
  · simp only [if_neg ha]
    exact bot_le

/-- A finite actual physical mass proves absolute convergence of its real
oriented series. The original `tsum` conventions are never used to infer finiteness. -/
theorem kernel_IF_total_oriented_real_summable (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ≥0∞) (A : KernelIFSourceIndex → Prop) [DecidablePred A]
    {x : ℝ} (hx : 0 < x) (hfin : kernelIFTotalPinBlockMass ν f eps H A x ≠ ∞) :
    Summable (fun b : FluxInfluenceIndex => fluxPositiveDensity
      (kernelIFTotalPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1,b.2,q⟩) H) x) ∧
    (∑' b : FluxInfluenceIndex, fluxPositiveDensity
      (kernelIFTotalPinOrientedDensity ν f eps b.1 b.2 (fun q => A ⟨b.1,b.2,q⟩) H) x) =
        (kernelIFTotalPinBlockMass ν f eps H A x).toReal := by
  have hh : (∑' b : FluxInfluenceIndex, kernelIFTotalPinOrientedDensity ν f eps b.1 b.2
      (fun q => A ⟨b.1,b.2,q⟩) H x) ≠ ∞ := by
    rwa [kernel_IF_total_oriented_mass_eq_blocks]
  have he (d : ℝ → ℝ≥0∞) : fluxPositiveDensity d x = (d x).toReal :=
    indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx) _
  simp_rw [he]
  exact ⟨ENNReal.summable_toReal hh,
    (ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hh)).symm.trans
      (congrArg ENNReal.toReal (kernel_IF_total_oriented_mass_eq_blocks ν f eps H A x))⟩

/-- The original signed ordering may be regrouped into the four nonnegative
physical masses once the actual absolute-reward mass is finite. -/
theorem kernel_IF_total_pin_boundary_eq_masses (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (eps : ℝ) (H : ℝ → ℝ) {x : ℝ} (hx : 0 < x)
    (hfin : kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal |H s|) (fun _ => True) x ≠ ∞) :
    Summable (fun b : FluxInfluenceIndex => ‖kernelIFTotalPinPrefix ν f eps b.1 b.2 H x‖) ∧
    kernelIFTotalPinBoundary ν f eps H x =
      ((kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (H s))
          (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal -
        (kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (-H s))
          (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) x).toReal) -
      ((kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (H s))
          (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal -
        (kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (-H s))
          (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) x).toReal) := by
  have hp (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_mass_mono ν f eps x
      (fun s => ENNReal.ofReal_le_ofReal (le_abs_self _)) (fun _ _ => trivial))
  have hn (A : KernelIFSourceIndex → Prop) :
      kernelIFTotalPinBlockMass ν f eps (fun s => ENNReal.ofReal (-H s)) A x ≠ ∞ :=
    ne_top_of_le_ne_top hfin (kernel_IF_total_block_mass_mono ν f eps x
      (fun s => ENNReal.ofReal_le_ofReal (neg_le_abs _)) (fun _ _ => trivial))
  obtain ⟨hLp,eLp⟩ := kernel_IF_total_oriented_real_summable ν f eps (fun s => ENNReal.ofReal (H s))
    (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) hx (hp _)
  obtain ⟨hLn,eLn⟩ := kernel_IF_total_oriented_real_summable ν f eps (fun s => ENNReal.ofReal (-H s))
    (fun b => fluxFacetCoef eps b.2.2 b.2.1 < 0) hx (hn _)
  obtain ⟨hUp,eUp⟩ := kernel_IF_total_oriented_real_summable ν f eps (fun s => ENNReal.ofReal (H s))
    (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) hx (hp _)
  obtain ⟨hUn,eUn⟩ := kernel_IF_total_oriented_real_summable ν f eps (fun s => ENNReal.ofReal (-H s))
    (fun b => 0 < fluxFacetCoef eps b.2.2 b.2.1) hx (hn _)
  refine ⟨((hLp.sub hLn).sub (hUp.sub hUn)).norm, ?_⟩
  unfold kernelIFTotalPinBoundary kernelIFTotalPinPrefix kernelIFTotalPinSignedDensity
  rw [(hLp.sub hLn).tsum_sub (hUp.sub hUn), hLp.tsum_sub hLn, hUp.tsum_sub hUn,
    eLp, eLn, eUp, eUn]

end
end PGM
