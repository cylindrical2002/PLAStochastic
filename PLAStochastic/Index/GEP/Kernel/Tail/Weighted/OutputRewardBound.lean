import PLAStochastic.Index.GEP.Kernel.Influence.Reward.PhysicalSum
import PLAStochastic.Index.GEP.Kernel.Influence.Pins.OuterRows
import PLAStochastic.Index.GEP.Kernel.Tail.Weighted.ExtremeSlopeOuter

/-! # The actual output reward and physical outer survival weights -/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

theorem kernel_physical_block_coord_measurable {J : Set ℝ} (hJ : MeasurableSet J)
    (β a s : ℝ) (n : ℕ) (b : ℝ) {S : Set ℕ} {c : ℕ → ℕ}
    (hc : ∀ j < n, c j ∈ S) :
    Measurable[kCoordSigma S] (fun g : ℕ → ℝ =>
      krAlive J β a n b (fun j => g (c j)) *
        Real.exp (s * gapKeys (fun j => g (c j)) n)) := by
  have hal : Measurable[kCoordSigma S] (fun g : ℕ → ℝ =>
      krAlive J β a n b (fun j => g (c j))) := by
    simpa only [kernelBlockTest, mul_one] using
      kernel_blockTest_coord_measurable hJ β a n b (φ := fun _ => (1 : ℝ))
        measurable_const hc
  let _ : MeasurableSpace (ℕ → ℝ) := kCoordSigma S
  have hsum : Measurable (fun g : ℕ → ℝ => gapKeys (fun j => g (c j)) n) := by
    exact Finset.measurable_sum _ fun j hj => kill_measurable_coord (hc j (Finset.mem_range.mp hj))
  exact hal.mul ((measurable_const.mul hsum).exp)

theorem kernel_physical_block_integrable {J : Set ℝ} (hJ : MeasurableSet J)
    (ν : ProbabilityMeasure ℝ) (β a s : ℝ) (n : ℕ) (b : ℝ)
    (hi : Integrable (fun g => Real.exp (s * gapKeys g n)) (iidLaw ν)) :
    Integrable (fun g => krAlive J β a n b g * Real.exp (s * gapKeys g n)) (iidLaw ν) := by
  apply hi.mono' ((measurable_krAlive_right hJ β a n b).mul
    ((rawAsm_measurable_gapKeys n).const_mul s).exp).aestronglyMeasurable
  exact Eventually.of_forall fun g => by
    change ‖krAlive J β a n b g * Real.exp (s * gapKeys g n)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _))]
    exact mul_le_of_le_one_left (Real.exp_nonneg _) (krAlive_le_one _ _ _)

theorem kernel_regLaw_physical_exp {D θ vlo vhi s : ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hs : 0 ≤ s) (hsθ : s ≤ θ / 2)
    (n : ℕ) : Integrable (fun g => Real.exp (s * gapKeys g n)) (iidLaw ν) := by
  simpa only [fluxUnmarkedSum, gapKeys, Finset.erase_eq_of_notMem (Finset.notMem_range_self)] using
    flux_regLaw_unmarked_exp hν hθ hs hsθ n n

/-- Exact factorization of the physical exponential weight on the two exterior
rows. The internal deterministic time is retained as a separate factor. -/
theorem kernel_IF_physical_outer_lintegral (ν : ProbabilityMeasure ℝ) (eps a s : ℝ)
    {k : ℕ} (q : FluxFacetIndex k) (hrt : (q.1 : ℕ) ≤ q.2.2.1)
    (hi : ∀ n, Integrable (fun g => Real.exp (s * gapKeys g n)) (iidLaw ν)) :
    (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) *
      ENNReal.ofReal (Real.exp (s * kernelIFPhysicalSum a q g)) ∂iidLaw ν) =
    ENNReal.ofReal (Real.exp (s * (((q.2.2.1 : ℕ) - (q.1 : ℝ)) / a))) *
      (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν (-1) (-a) s q.1
        (eps-fluxFacetSign q*eps)) *
      ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν 1 a s (k-q.2.2.1)
        (eps-fluxFacetSign q*eps))) := by
  let J := Icc (0 : ℝ) (2*eps)
  let b := eps-fluxFacetSign q*eps
  let r : ℕ := q.1
  let t : ℕ := q.2.2.1
  let F := fun g : ℕ → ℝ => krAlive J (-1) (-a) r b (kernelReversePrefix g r) *
    Real.exp (s * gapKeys (kernelReversePrefix g r) r)
  let G := fun g : ℕ → ℝ => krAlive J 1 a (k-t) b (fun j => g (j+t)) *
    Real.exp (s * gapKeys (fun j => g (j+t)) (k-t))
  have hF : Measurable[kCoordSigma (Iio r)] F :=
    kernel_physical_block_coord_measurable measurableSet_Icc (-1) (-a) s r b
      (by intro j hj; change r-1-j < r; omega)
  have hG : Measurable[kCoordSigma (Ici t)] G :=
    kernel_physical_block_coord_measurable measurableSet_Icc 1 a s (k-t) b
      (by intro j _; change t ≤ j+t; omega)
  have heq (g : ℕ → ℝ) :
      ENNReal.ofReal (kernelIFOuterSurvival eps a q g) *
        ENNReal.ofReal (Real.exp (s * kernelIFPhysicalSum a q g)) =
      ENNReal.ofReal (Real.exp (s * (((t : ℝ)-r)/a))) *
        (ENNReal.ofReal (F g) * ENNReal.ofReal (G g)) := by
    rw [kernel_IF_physical_sum_outer]
    have hrev : gapKeys (kernelReversePrefix g r) r = gapKeys g r := Finset.sum_range_reflect g r
    simp only [F, G, hrev, kernelIFOuterSurvival, mul_add, Real.exp_add]
    simp only [ENNReal.ofReal_mul, krAlive_nonneg, Real.exp_nonneg, mul_nonneg]
    dsimp [J, b, r, t]
    ac_rfl
  simp_rw [heq]
  have hFG : Measurable (fun g => ENNReal.ofReal (F g) * ENNReal.ofReal (G g)) :=
    (hF.mono (kCoordSigma_le _) le_rfl).ennreal_ofReal.mul
      (hG.mono (kCoordSigma_le _) le_rfl).ennreal_ofReal
  rw [lintegral_const_mul _ hFG,
    kernel_iid_lintegral_mul_coords ν (S := Iio r) (T := Ici t)
      (Set.disjoint_left.mpr (by intro j hj ht; change j < r at hj; change t ≤ j at ht; omega))
      hF.ennreal_ofReal hG.ennreal_ofReal]
  have hrev : (∫⁻ g, ENNReal.ofReal (F g) ∂iidLaw ν) =
      ENNReal.ofReal (kernelPhysicalSurv J ν (-1) (-a) s r b) := by
    let H := fun g : ℕ → ℝ => krAlive J (-1) (-a) r b g * Real.exp (s * gapKeys g r)
    have hH : Measurable H := (measurable_krAlive_right measurableSet_Icc (-1) (-a) r b).mul
      ((rawAsm_measurable_gapKeys r).const_mul s).exp
    calc
      _ = ∫⁻ g, ENNReal.ofReal (H (fun j => g (kernelReverseIndex r j))) ∂iidLaw ν := by
        apply lintegral_congr
        intro g
        have hh : ∀ j < r, kernelReversePrefix g r j = g (kernelReverseIndex r j) := by
          intro j hj
          simp only [kernelReversePrefix, kernelReverseIndex, if_pos hj]
        have hal := kernel_krAlive_congr J (-1) (-a) r b hh
        have hsum : gapKeys (kernelReversePrefix g r) r =
            gapKeys (fun j => g (kernelReverseIndex r j)) r :=
          Finset.sum_congr rfl fun j hj => hh j (Finset.mem_range.mp hj)
        simp only [F, H, hal, hsum]
      _ = ∫⁻ g, ENNReal.ofReal (H g) ∂iidLaw ν :=
        kernel_iid_lintegral_reindex ν (kernelReverseIndex_injective r) hH.ennreal_ofReal
      _ = _ := (ofReal_integral_eq_lintegral_ofReal
        (kernel_physical_block_integrable measurableSet_Icc ν (-1) (-a) s r b (hi r))
        (Eventually.of_forall fun g => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _))).symm
  have htail : (∫⁻ g, ENNReal.ofReal (G g) ∂iidLaw ν) =
      ENNReal.ofReal (kernelPhysicalSurv J ν 1 a s (k-t) b) := by
    have hm : Measurable (fun g : ℕ → ℝ => ENNReal.ofReal
        (krAlive J 1 a (k-t) b g * Real.exp (s * gapKeys g (k-t)))) :=
      ((measurable_krAlive_right measurableSet_Icc 1 a (k-t) b).mul
        ((rawAsm_measurable_gapKeys (k-t)).const_mul s).exp).ennreal_ofReal
    change (∫⁻ g, ENNReal.ofReal (krAlive J 1 a (k-t) b (fun j => g (j+t)) *
      Real.exp (s * gapKeys (fun j => g (j+t)) (k-t))) ∂iidLaw ν) = _
    rw [kernel_iid_lintegral_reindex ν (c := fun j => j+t)
      (fun _ _ h => Nat.add_right_cancel h) hm]
    exact (ofReal_integral_eq_lintegral_ofReal
      (kernel_physical_block_integrable measurableSet_Icc ν 1 a s (k-t) b (hi (k-t)))
      (Eventually.of_forall fun g => mul_nonneg (krAlive_nonneg _ _ _) (Real.exp_nonneg _))).symm
  rw [hrev, htail]

theorem kernel_IF_reward_physical_outer_le {D θ vlo vhi η M C eps a : ℝ}
    {ν : ProbabilityMeasure ℝ} {ψ : ℝ → ℝ} (hν : RegLaw D θ vlo vhi ν)
    (hθ : 0 < θ) (hψ : OutTest η M ψ) (hη : 0 ≤ η) (hC : 0 < C)
    (hscale : η / C ≤ θ / 4) (ha : 0 < a) {k : ℕ} {q : FluxFacetIndex k}
    (hq : fluxFacetValid q) :
    (∫⁻ g, ENNReal.ofReal (kernelIFOuterSurvival eps a q g) *
      ENNReal.ofReal |kernelBoundaryReward ν C ψ (kernelIFPhysicalSum a q g)| ∂iidLaw ν) ≤
    ENNReal.ofReal (M * (8*D/θ^2) / C) *
      (ENNReal.ofReal (Real.exp ((η/C) * (((q.2.2.1 : ℕ)-(q.1 : ℝ))/a))) *
        (ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν (-1) (-a) (η/C) q.1
          (eps-fluxFacetSign q*eps)) *
         ENNReal.ofReal (kernelPhysicalSurv (Icc 0 (2*eps)) ν 1 a (η/C) (k-q.2.2.1)
          (eps-fluxFacetSign q*eps)))) := by
  have hg : ∀ᵐ g ∂iidLaw ν, ∀ j, 0 < g j := by
    rw [ae_all_iff]
    intro j
    exact (measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) j).quasiMeasurePreserving.ae hν.ae_pos
  have hs : 0 ≤ η/C := div_nonneg hη hC.le
  have hExp := kernel_regLaw_physical_exp hν hθ hs (show η/C ≤ θ/2 by linarith)
  rw [← kernel_IF_physical_outer_lintegral ν eps a (η/C) q (lt_trans hq.1 hq.2).le hExp]
  have hm : Measurable (fun g => ENNReal.ofReal (kernelIFOuterSurvival eps a q g) *
      ENNReal.ofReal (Real.exp ((η/C) * kernelIFPhysicalSum a q g))) :=
    ((measurable_kernelIFOuterSurvival_coords eps a q).mono
      (kCoordSigma_le _) le_rfl).ennreal_ofReal.mul
      ((((kernel_IF_physical_sum_coord_measurable a q).mono
        (kCoordSigma_le _) le_rfl).const_mul (η/C)).exp.ennreal_ofReal)
  rw [← lintegral_const_mul _ hm]
  apply lintegral_mono_ae
  filter_upwards [hg] with g hg
  have hb := kernelBoundaryReward_le hν hθ hψ hη hC hscale
    (kernel_IF_physical_sum_nonneg ha hq (fun j _ => (hg j).le))
  have hM := hψ.nonneg
  have hD : 0 ≤ D := hν.D_nonneg
  have he : η * kernelIFPhysicalSum a q g / C = (η/C) * kernelIFPhysicalSum a q g := by ring
  rw [he] at hb
  have hh := mul_le_mul' (le_refl (ENNReal.ofReal (kernelIFOuterSurvival eps a q g)))
    (ENNReal.ofReal_le_ofReal hb)
  rw [ENNReal.ofReal_mul (by positivity : 0 ≤ M*(8*D/θ^2)/C)] at hh
  simpa only [mul_assoc, mul_left_comm] using hh

end
end PGM
