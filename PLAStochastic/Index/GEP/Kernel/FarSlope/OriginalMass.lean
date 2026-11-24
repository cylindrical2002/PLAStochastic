import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputSum
import PLAStochastic.Index.GEP.Kernel.Tail.Original.PhysicalOuterSum
import PLAStochastic.Index.GEP.Kernel.FarSlope.WeightedLogWindow

/-! # Arbitrarily small far-slope mass for the original output reward -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1400000

theorem kernel_regLaw_original_output_far_mass (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ b : ℝ, 0 < b → ∀ B : ℕ,
    ∃ α K w0 : ℝ, 0 < α ∧ 0 < K ∧ 1 ≤ w0 ∧
      ∀ eps : ℝ, 1 ≤ eps → w0 ≤ 2*eps →
      1 ≤ α*Real.log (2*eps) ∧ α*Real.log (2*eps) ≤ (2*eps)/2 ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
        (∀ x ≤ 0, f x=0) → (∀ x, f x ≤ D*Real.exp (-θ*x)) →
        (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      ∀ η M C : ℝ, 0 ≤ η → 0 < C → η/C ≤ θ/4 → η/C ≤ ρ/(2*eps)^2 →
      ∀ ψ : ℝ → ℝ, OutTest η M ψ → ∀ S : Set ℝ, MeasurableSet S →
        (∀ a ∈ S, 0 < a → α*Real.log (2*eps) ≤ (2*eps)*|a-1|) →
      ∀ x, x ∈ Ioc (0 : ℝ) (b*Real.log (2*eps)) →
      kernelIFTotalPinBlockMassOn ν f eps S
        (fun z => ENNReal.ofReal |kernelBoundaryReward ν C ψ z|) (fun _ => True) x ≤
        ENNReal.ofReal ((M*(8*D/θ^2)/C)*(K/(2*eps)^B)) := by
  obtain ⟨ρb,hρb,hbulk⟩ := kernel_regLaw_weighted_bulk_log_far D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρd,hρd,hdirac⟩ := kernel_regLaw_weighted_dirac_log_far D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρo,hρo,houter⟩ := kernel_regLaw_physical_outer_pair_sum D θ vlo vhi hD hθ hvlo hv
  refine ⟨min ρb (min ρd ρo),lt_min hρb (lt_min hρd hρo),fun b hb B => ?_⟩
  obtain ⟨α,Kb,wb,hα,hKb,hwb,hbf⟩ := hbulk b hb B
  obtain ⟨Kd,wd,hKd,hwd,hdf⟩ := hdirac b hb B
  refine ⟨α,4*(2*Kb+Kd),max wb wd,hα,by positivity,hwb.trans (le_max_left _ _),?_⟩
  intro eps heps hw
  have hw' : 1 ≤ 2*eps := by linarith
  have hbdata := hbf (2*eps) ((le_max_left wb wd).trans hw)
  refine ⟨hbdata.1,hbdata.2.1,?_⟩
  intro ν hν f hf hf0 hfD hfz hfe hνf η M C hη hC hscale hs ψ hψ S hS hfar x hx
  have hs0 : 0 ≤ η/C := by positivity
  have hsb := hs.trans (div_le_div_of_nonneg_right (min_le_left ρb (min ρd ρo)) (sq_nonneg _))
  have hsd := hs.trans (div_le_div_of_nonneg_right
    ((min_le_right ρb (min ρd ρo)).trans (min_le_left ρd ρo)) (sq_nonneg _))
  have hso := hs.trans (div_le_div_of_nonneg_right
    ((min_le_right ρb (min ρd ρo)).trans (min_le_right ρd ρo)) (sq_nonneg _))
  have hb0 := hbdata.2.2 (η/C) hs0 hsb ν hν f hf hf0 hfD hfz hfe hνf x ⟨hx.1.le,hx.2⟩
  have hd := hdf (2*eps) ((le_max_right wb wd).trans hw) (η/C) hs0 hsd ν hν f hf hf0 hfD hfz hfe x hx
  have hμ : ((volume.restrict (Ioi (0 : ℝ))).restrict S) ≤
      volume.restrict (kernelFarSlopes (2*eps) (α*Real.log (2*eps))) := by
    rw [Measure.restrict_restrict hS]
    apply Measure.restrict_mono _ le_rfl
    intro a ha
    exact ⟨ha.2,hfar a ha.1 ha.2⟩
  have hb1 : kernelWeightedBulkMass ν f (2*eps) (η/C) x 0 (2*eps)
      ((volume.restrict (Ioi (0 : ℝ))).restrict S) ≤ ENNReal.ofReal (Kb/(2*eps)^B) :=
    (lintegral_mono' hμ le_rfl).trans (hb0 0 (2*eps) (Or.inl ⟨rfl,rfl⟩))
  have hb2 : kernelWeightedBulkMass ν f (2*eps) (η/C) x (2*eps) 0
      ((volume.restrict (Ioi (0 : ℝ))).restrict S) ≤ ENNReal.ofReal (Kb/(2*eps)^B) :=
    (lintegral_mono' hμ le_rfl).trans (hb0 (2*eps) 0 (Or.inr ⟨rfl,rfl⟩))
  have hd' : kernelWeightedDiracMass ν f (2*eps) (η/C) x ≤ ENNReal.ofReal (Kd/(2*eps)^B) := by
    unfold kernelWeightedDiracMass
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (kernelWeightedDiracTailTerm_nonneg ν hf0 (η/C) (by linarith) hx.1.le) hd.1]
    exact ENNReal.ofReal_le_ofReal hd.2
  have hm := kernel_output_actual_block_mass_on_le hν hθ hψ hη hC hscale hf hf0 heps hx.1
    (houter ν hν (2*eps) (η/C) · hw' hs0 hso)
    (measurable_kernelPhysicalOuterPairAt ν (2*eps) (η/C)) S
  apply hm.trans ((mul_le_mul' le_rfl (add_le_add (add_le_add hb1 hb2) hd')).trans_eq ?_)
  have hM := hψ.nonneg
  rw [← ENNReal.ofReal_add (by positivity : 0 ≤ Kb/(2*eps)^B) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4*(M*(8*D/θ^2)/C))]
  congr 1
  ring

end
end PGM
