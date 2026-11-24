import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputSum
import PLAStochastic.Index.GEP.Kernel.Tail.Original.OutputMass
import PLAStochastic.Index.GEP.Kernel.Tail.Original.PhysicalOuterSum
import PLAStochastic.Index.GEP.Kernel.Tail.Original.Scale

/-! # Fixed-power tails for the original output boundary and physical reward -/
namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1800000

theorem kernel_output_original_tail_of_bounds {D θ vlo vhi η M C eps K ζ : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η/C ≤ θ/4) {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hfD : ∀ t, f t ≤ D) (hfz : ∀ t ≤ 0, f t = 0)
    (hνf : (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)))
    (heps : 1 ≤ eps) (hK : 0 ≤ K)
    (houter : ∀ a, 0 < a → (∑' u : ℕ, ∑' v : ℕ, ENNReal.ofReal (kernelPhysicalOuterPairAt ν (2*eps) (η/C) a u v)) =
      ENNReal.ofReal (kernelPhysicalOuterWeight ν (2*eps) (η/C) a))
    (hbulk : ∀ x, 0 < x → ∀ y z, kernelWeightedBulkMass ν f (2*eps) (η/C) x y z
      (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)))
    (hdirac : ∀ x, 0 < x → kernelWeightedDiracMass ν f (2*eps) (η/C) x ≤
      ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x))) :
    KernelTail ((24*(M*(8*D/θ^2)/C)*K)*(2*eps)^16) ζ
      (outputIFBoundary eps ν (fun t => ENNReal.ofReal (f t)) ψ C) := by
  have hM := hψ.nonneg
  have hD := hν.D_nonneg
  have hA : 0 ≤ M*(8*D/θ^2)/C := by positivity
  filter_upwards [output_IF_boundary_enorm_le_blocks_ae ν hψ hf hf0 hfD hfz hνf hν.ae_pos
    (show 0 ≤ eps by linarith) C, ae_restrict_mem measurableSet_Ioi] with x hx hxpos
  have hnon : 0 ≤ K * (2*eps)^16 * Real.exp (ζ*x) := by positivity
  have hm := kernel_output_actual_block_mass_le hν hθ hψ hη hC hscale hf hf0 heps hxpos houter
    (measurable_kernelPhysicalOuterPairAt ν (2*eps) (η/C))
  have hh := hx.trans ((mul_le_mul' le_rfl hm).trans (mul_le_mul' le_rfl
    (mul_le_mul' le_rfl (add_le_add (add_le_add (hbulk x hxpos 0 (2*eps))
      (hbulk x hxpos (2*eps) 0)) (hdirac x hxpos)))))
  have he : (2 : ℝ≥0∞) * ((4*ENNReal.ofReal (M*(8*D/θ^2)/C)) *
      (ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) +
       ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)) +
       ENNReal.ofReal (K * (2*eps)^16 * Real.exp (ζ*x)))) =
      ENNReal.ofReal (((24*(M*(8*D/θ^2)/C)*K)*(2*eps)^16) * Real.exp (ζ*x)) := by
    rw [← ENNReal.ofReal_add hnon hnon,
      ← ENNReal.ofReal_add (add_nonneg hnon hnon) hnon]
    rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
      show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (mul_nonneg (by norm_num) hA),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [he, Real.enorm_eq_ofReal_abs] at hh
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hh

/-- The output exponent is fixed by the class before the arbitrary input
exponent. The original boundary, with its genuine coupled physical reward,
has fixed polynomial power 16. -/
theorem kernel_regLaw_original_output_tail (D θ vlo vhi : ℝ)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) :
    ∃ ηB : ℝ, 0 < ηB ∧ ∀ ζ : ℝ, 0 < ζ → ∃ e0 K : ℝ, 1 ≤ e0 ∧ 0 < K ∧
      ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
      ∃ f : ℝ → ℝ, Measurable f ∧ (∀ t, 0 ≤ f t) ∧ (∀ t, f t ≤ D) ∧
        (∀ t ≤ 0, f t = 0) ∧ (∀ t, f t ≤ D * Real.exp (-θ*t)) ∧
        (ν : Measure ℝ) = volume.withDensity (fun t => ENNReal.ofReal (f t)) ∧
        ∀ eps : ℝ, e0 ≤ eps → ∀ η : ℝ, 0 ≤ η → η ≤ ηB →
        ∀ M : ℝ, ∀ ψ : ℝ → ℝ, OutTest η M ψ →
          KernelTail (M*K*eps^16) ζ
            (outputIFBoundary eps ν (fun t => ENNReal.ofReal (f t)) ψ (lawC eps ν)) := by
  obtain ⟨ρt,hρt,htail⟩ := kernel_regLaw_joint_weighted_tail D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ρo,hρo,houter⟩ := kernel_regLaw_physical_outer_pair_sum D θ vlo vhi hD hθ hvlo hv
  obtain ⟨ηB,hηB,hscale⟩ := kernel_regLaw_tail_physical_scale D θ vlo vhi (min ρt ρo)
    hD hθ hvlo hv (lt_min hρt hρo)
  refine ⟨ηB,hηB,?_⟩
  intro ζ hζ
  obtain ⟨σ,K,hσ,hK,ht⟩ := htail ζ hζ
  obtain ⟨e0,he0,hsc⟩ := hscale (min σ (θ/4)) (lt_min hσ (by positivity))
  let B := 128 * regB vhi
  have hB : 0 < B := mul_pos (by norm_num) ((regV_pos hvlo).trans_le (regV_le_regB hv))
  refine ⟨e0,24*(8*D/θ^2)*K*B*2^16,he0,by positivity,?_⟩
  intro ν hν
  obtain ⟨f,hf,hf0,hfD,hfz,hfe,hνf,ht⟩ := ht ν hν
  refine ⟨f,hf,hf0,hfD,hfz,hfe,hνf,?_⟩
  intro eps heps η hη hηle M ψ hψ
  have he1 := he0.trans heps
  obtain ⟨hC,hInv,hsρ,hsσ⟩ := hsc eps heps ν hν η hη hηle
  have hs0 : 0 ≤ η / lawC eps ν := div_nonneg hη hC.le
  have hst : η / lawC eps ν ≤ ρt / (2*eps)^2 := hsρ.trans
    (div_le_div_of_nonneg_right (min_le_left _ _) (sq_nonneg _))
  have hso : η / lawC eps ν ≤ ρo / (2*eps)^2 := hsρ.trans
    (div_le_div_of_nonneg_right (min_le_right _ _) (sq_nonneg _))
  have ho (a : ℝ) (ha : 0 < a) := houter ν hν (2*eps) (η/lawC eps ν) a (by linarith) hs0 hso ha
  have hb (x : ℝ) (hx : 0 < x) := ht (2*eps) (η/lawC eps ν) x (by linarith) hs0 hst
    (hsσ.trans (min_le_left _ _)) hx
  have hbulk : ∀ x, 0 < x → ∀ y z, kernelWeightedBulkMass ν f (2*eps) (η/lawC eps ν) x y z
      (volume.restrict (Ioi (0 : ℝ))) ≤ ENNReal.ofReal (K*(2*eps)^16*Real.exp (ζ*x)) := by
    intro x hx y z
    exact (hb x hx).1 y z
  have hd : ∀ x, 0 < x → kernelWeightedDiracMass ν f (2*eps) (η/lawC eps ν) x ≤
      ENNReal.ofReal (K*(2*eps)^16*Real.exp (ζ*x)) := by
    intro x hx
    rw [kernelWeightedDiracMass, ← ENNReal.ofReal_tsum_of_nonneg
      (kernelWeightedDiracTailTerm_nonneg ν hf0 _ (by linarith) hx.le) (hb x hx).2.1]
    exact ENNReal.ofReal_le_ofReal (hb x hx).2.2
  have hfull := kernel_output_original_tail_of_bounds hν hθ hψ hη hC
    (hsσ.trans (min_le_right _ _)) hf hf0 hfD hfz hνf he1 hK.le ho hbulk hd
  filter_upwards [hfull] with x hx
  apply hx.trans
  have hM := hψ.nonneg
  have hh := mul_le_mul_of_nonneg_left hInv
    (show 0 ≤ 24*M*(8*D/θ^2)*K*(2*eps)^16*Real.exp (ζ*x) by positivity)
  calc
    _ = (24*M*(8*D/θ^2)*K*(2*eps)^16*Real.exp (ζ*x))*(1/lawC eps ν) := by ring
    _ ≤ _ := hh
    _ = _ := by dsimp [B]; ring

end
end PGM
