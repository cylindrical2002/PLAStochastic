import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.BlockFactorization
import Mathlib.MeasureTheory.MeasurableSpace.Invariants

/-!
# Nonnegative rewards coupling the two outer paths

The reward may depend jointly on every coordinate outside the two internal
bridges. Only independence from the bridge coordinates is used; no product
decomposition of the outer reward and no finite reward moment are assumed.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 800000


/-- Coordinate-measurability gives actual invariance under every change of the
other coordinates. This is pointwise, not only almost everywhere. -/
theorem kernel_coord_measurable_invariant {E : Type*} [MeasurableSpace E]
    [MeasurableSingletonClass E] {S : Set ℕ} {W : (ℕ → ℝ) → E}
    (hW : Measurable[kCoordSigma S] W) (T : (ℕ → ℝ) → (ℕ → ℝ))
    (hT : ∀ g j, j ∈ S → T g j = g j) (g : ℕ → ℝ) : W (T g) = W g := by
  have hle : kCoordSigma S ≤ MeasurableSpace.invariants T := by
    apply iSup₂_le
    intro j hj
    apply Measurable.comap_le
    intro U hU
    refine ⟨(measurable_pi_apply j) hU, ?_⟩
    ext p
    change T p j ∈ U ↔ p j ∈ U
    rw [hT p j hj]
  exact congrFun (MeasurableSpace.comp_eq_of_measurable_invariants
    (hW.mono hle le_rfl)) g

theorem kernel_iid_lintegral_mul_coords (ν : ProbabilityMeasure ℝ)
    {S T : Set ℕ} (hST : Disjoint S T) {F G : (ℕ → ℝ) → ℝ≥0∞}
    (hF : Measurable[kCoordSigma S] F) (hG : Measurable[kCoordSigma T] G) :
    (∫⁻ g, F g * G g ∂iidLaw ν) =
      (∫⁻ g, F g ∂iidLaw ν) * ∫⁻ g, G g ∂iidLaw ν := by
  have hind : IndepFun F G (iidLaw ν) := kill_indepFun_of_disjoint hST hF hG
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (hF.mono (kCoordSigma_le S) le_rfl) (hG.mono (kCoordSigma_le T) le_rfl) hind

theorem kernel_iid_outer_two_blocks (ν : ProbabilityMeasure ℝ) {r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) {W F G : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio r ∪ Ici t)] W)
    (hF : Measurable[kCoordSigma (Ico r s)] F)
    (hG : Measurable[kCoordSigma (Ico s t)] G) :
    (∫⁻ g, W g * (F g * G g) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) * ((∫⁻ g, F g ∂iidLaw ν) * ∫⁻ g, G g ∂iidLaw ν) := by
  have hFm : Measurable[kCoordSigma (Ico r t)] F :=
    hF.mono (kernel_coordSigma_mono fun _ h => ⟨h.1, lt_of_lt_of_le h.2 hst⟩) le_rfl
  have hGm : Measurable[kCoordSigma (Ico r t)] G :=
    hG.mono (kernel_coordSigma_mono fun _ h => ⟨le_trans hrs h.1, h.2⟩) le_rfl
  rw [kernel_iid_lintegral_mul_coords ν (S := Iio r ∪ Ici t) (T := Ico r t)
    (G := fun g => F g * G g)
    (Set.disjoint_left.mpr (by
      intro j hj hout
      rcases hj with hj | hj <;> simp only [mem_Iio, mem_Ici, mem_Ico] at * <;> omega))
    hW (hFm.mul hGm)]
  rw [kernel_iid_lintegral_mul_coords ν (S := Ico r s) (T := Ico s t)
    (Set.disjoint_left.mpr (by
      intro j hj hk
      simp only [mem_Ico] at *
      omega)) hF hG]

theorem kernel_iid_lintegral_reindex (ν : ProbabilityMeasure ℝ) {c : ℕ → ℕ}
    (hc : Function.Injective c) {F : (ℕ → ℝ) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ g, F (fun j => g (c j)) ∂iidLaw ν) = ∫⁻ g, F g ∂iidLaw ν := by
  have hm : Measurable (fun g : ℕ → ℝ => fun j => g (c j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (c j)
  have hmap : (iidLaw ν).map (fun g : ℕ → ℝ => fun j => g (c j)) = iidLaw ν :=
    Measure.map_infinitePi_infinitePi_of_inj hc
  have h := lintegral_map hF hm (μ := iidLaw ν)
  rw [hmap] at h
  exact h.symm

theorem kernel_lintegral_pin_block (ν : ProbabilityMeasure ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (β a y z : ℝ) (n : ℕ) :
    (∫⁻ g, ENNReal.ofReal (kernelBlockTest J β a n y (fun u => krKer J f β a u z) g)
      ∂iidLaw ν) = ENNReal.ofReal (krDens J ν f β a (n+1) y z) := by
  have hm : Measurable (kernelBlockTest J β a n y (fun u => krKer J f β a u z)) :=
    measurable_kernelBlockTest hJ β a n y
    ((measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const))
  have hi : Integrable (kernelBlockTest J β a n y (fun u => krKer J f β a u z)) (iidLaw ν) := by
    apply kr_integrable_of_bdd hm (M := D / |a|)
    intro g
    rw [kernelBlockTest, abs_mul]
    exact (mul_le_mul (abs_krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ z)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun g =>
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _))]
  congr 1

theorem kernel_lintegral_marked_pin_block (ν : ProbabilityMeasure ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β x y z : ℝ) (l : ℕ) {r : ℕ} (hr : 1 ≤ r) :
    (∫⁻ g, ENNReal.ofReal (kernelBlockTest J β a (l+r) y (fun u => krKer J f β a u z)
      (Function.update g l x)) ∂iidLaw ν) =
      ENNReal.ofReal (kernelMarkedFullDens J ν f β a x l r y z) := by
  have hm : Measurable (fun g => kernelBlockTest J β a (l+r) y
      (fun u => krKer J f β a u z) (Function.update g l x)) :=
    (measurable_kernelBlockTest hJ β a (l+r) y
    ((measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const))).comp
      ((measurable_update_pair l).comp (measurable_const.prodMk measurable_id))
  have hi : Integrable (fun g => kernelBlockTest J β a (l+r) y
      (fun u => krKer J f β a u z) (Function.update g l x)) (iidLaw ν) := by
    apply kr_integrable_of_bdd hm (M := D / |a|)
    intro g
    rw [kernelBlockTest, abs_mul]
    exact (mul_le_mul (abs_krAlive_le_one _ _ _) (abs_krKer_le hf0 hfD _ z)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun g =>
    mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _))]
  congr 1
  exact kernelUpdatedLastDensity_eq_full hJ hJfin ν hf hf0 hfD hν ha β x l hr y z

/-- The outer reward stays joint. It may, in particular, encode an arbitrary
nonnegative function of the two outer terminal residuals. -/
theorem kernel_marked_pins_with_outer_reward (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β x b b' : ℝ) (r l s m : ℕ) (hs : 1 ≤ s)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio r ∪ Ici (r+(l+s+1)+(m+1)))] W) :
    (∫⁻ g, W g *
      (ENNReal.ofReal (kernelBlockTest J β a (l+s) b (fun u => krKer J f β a u b')
        (Function.update (fun j => g (j+r)) l x)) *
      ENNReal.ofReal (kernelBlockTest J β a m b' (fun u => krKer J f β a u b)
        (fun j => g (j+(r+(l+s+1)))))) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens J ν f β a x l s b b') *
          ENNReal.ofReal (krDens J ν f β a (m+1) b' b)) := by
  have hK (z : ℝ) : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have hF := (kernel_marked_blockTest_coord_measurable hJ β a x l (l+s) b (hK b')
    (c := fun j => j+r) (S := Ico r (r+(l+s+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  have hG := (kernel_blockTest_coord_measurable hJ β a m b' (hK b)
    (c := fun j => j+(r+(l+s+1))) (S := Ico (r+(l+s+1)) (r+(l+s+1)+(m+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  rw [kernel_iid_outer_two_blocks ν (by omega) (by omega) hW hF hG]
  have hFm : Measurable (fun g : ℕ → ℝ => ENNReal.ofReal
      (kernelBlockTest J β a (l+s) b (fun u => krKer J f β a u b') (Function.update g l x))) :=
    ((measurable_kernelBlockTest hJ β a (l+s) b (hK b')).comp
      ((measurable_update_pair l).comp (measurable_const.prodMk measurable_id))).ennreal_ofReal
  rw [kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h) hFm,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelBlockTest hJ β a m b' (hK b)).ennreal_ofReal,
    kernel_lintegral_marked_pin_block ν hJ hJfin hf hf0 hfD hν ha β x b b' l hs,
    kernel_lintegral_pin_block ν hJ hf hf0 hfD β a b' b m]

end
end PGM
