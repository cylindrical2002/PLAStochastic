import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.OuterReward
import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.CoareaPath

/-!
# A single physical marked pin for every non-Dirac length

The last random gap is integrated against its physical density. If the marked
gap is last, its deterministic translation and the terminal band projection
are retained. The zero-zero case is intentionally not asserted to have a density.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
set_option maxHeartbeats 1000000

def kernelMarkedPinBlock (J : Set ℝ) (f : ℝ → ℝ) (β a x : ℝ)
    (l r : ℕ) (y z : ℝ) (g : ℕ → ℝ) : ℝ :=
  if r = 0 then
    kernelBlockTest J β a (l-1) y (fun u => krKer J f β a u (z-β+a*x)) g *
      J.indicator (fun _ => (1 : ℝ)) z
  else
    kernelBlockTest J β a (l+r) y (fun u => krKer J f β a u z) (Function.update g l x)

theorem kernel_marked_pin_block_nonneg {J : Set ℝ} {f : ℝ → ℝ}
    (hf0 : ∀ u, 0 ≤ f u) (β a x : ℝ) (l r : ℕ) (y z : ℝ) (g : ℕ → ℝ) :
    0 ≤ kernelMarkedPinBlock J f β a x l r y z g := by
  unfold kernelMarkedPinBlock
  split_ifs
  · exact mul_nonneg (mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _))
      (indicator_nonneg (fun _ _ => zero_le_one) _)
  · exact mul_nonneg (krAlive_nonneg _ _ _) (krKer_nonneg hf0 _ _)

theorem measurable_kernelMarkedPinBlock {J : Set ℝ} (hJ : MeasurableSet J)
    {f : ℝ → ℝ} (hf : Measurable f) (β a x : ℝ) (l r : ℕ) (y z : ℝ) :
    Measurable (kernelMarkedPinBlock J f β a x l r y z) := by
  have hK (z : ℝ) : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  unfold kernelMarkedPinBlock
  split_ifs
  · exact (measurable_kernelBlockTest hJ β a (l-1) y (hK _)).mul_const _
  · exact (measurable_kernelBlockTest hJ β a (l+r) y (hK _)).comp
      ((measurable_update_pair l).comp (measurable_const.prodMk measurable_id))

theorem kernel_marked_pin_block_coord_measurable {J : Set ℝ} (hJ : MeasurableSet J)
    {f : ℝ → ℝ} (hf : Measurable f) (β a x : ℝ) (l r : ℕ) (y z : ℝ)
    {c : ℕ → ℕ} {S : Set ℕ} (hc : ∀ j < l+r, c j ∈ S) :
    Measurable[kCoordSigma S] (fun g : ℕ → ℝ =>
      kernelMarkedPinBlock J f β a x l r y z (fun j => g (c j))) := by
  apply kernel_finite_path_coord_measurable (measurable_kernelMarkedPinBlock hJ hf β a x l r y z)
    (n := l+r) _ hc
  intro g h he
  unfold kernelMarkedPinBlock
  split_ifs with hr
  · congr 1
    apply kernel_blockTest_congr
    intro j hj
    exact he j (by omega)
  · apply kernel_blockTest_congr
    intro j hj
    by_cases hji : j = l
    · subst j
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hji]
      exact he j hj

theorem kernel_lintegral_marked_pin_block_full (ν : ProbabilityMeasure ℝ) {J : Set ℝ}
    (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤) {f : ℝ → ℝ} {D : ℝ}
    (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    {a : ℝ} (ha : a ≠ 0) (β x y z : ℝ) (l r : ℕ) (hlr : 1 ≤ l+r) :
    (∫⁻ g, ENNReal.ofReal (kernelMarkedPinBlock J f β a x l r y z g) ∂iidLaw ν) =
      ENNReal.ofReal (kernelMarkedFullDens J ν f β a x l r y z) := by
  cases r with
  | zero =>
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : l ≠ 0)
    change (∫⁻ g, ENNReal.ofReal (kernelBlockTest J β a n y
      (fun u => krKer J f β a u (z-β+a*x)) g * J.indicator (fun _ => (1 : ℝ)) z) ∂iidLaw ν) =
      ENNReal.ofReal (krDens J ν f β a (n+1) y (z-β+a*x) * J.indicator (fun _ => (1 : ℝ)) z)
    simp_rw [ENNReal.ofReal_mul' (indicator_nonneg (fun _ _ => (zero_le_one : (0 : ℝ) ≤ 1)) z)]
    rw [lintegral_mul_const' _ _ (by finiteness), kernel_lintegral_pin_block ν hJ hf hf0 hfD]
  | succ r =>
    simp only [kernelMarkedPinBlock, Nat.succ_ne_zero, if_false]
    exact kernel_lintegral_marked_pin_block ν hJ hJfin hf hf0 hfD hν ha β x y z l (by omega)

theorem kernel_pin_marked_end_factor_of_endpoint (J : Set ℝ) (f : ℝ → ℝ)
    {a : ℝ} (ha : a ≠ 0) (β x y z : ℝ) (n : ℕ) (g : ℕ → ℝ)
    (hx : g (n+1) = x) (hz : kWalk y β a g (n+2) = z) :
    f (g n) * krAlive J β a (n+2) y g =
      |a| * kernelMarkedPinBlock J f β a x (n+1) 0 y z g := by
  have hp : kWalk y β a g (n+1) = z-β+a*x := by
    rw [show n+2 = (n+1)+1 by omega, kernel_kWalk_succ_last, hx] at hz
    linarith
  have hpin := kernel_pin_density_factor_of_endpoint J f ha β y (z-β+a*x) n g hp
  rw [show n+2 = (n+1)+1 by omega, krAlive_succ_last, hz]
  simp only [kernelMarkedPinBlock, if_true, Nat.add_sub_cancel]
  linear_combination J.indicator (fun _ => (1 : ℝ)) z * hpin

/-- Every non-Dirac marked bridge factors from a joint exterior reward. -/
theorem kernel_marked_pins_with_outer_reward_full (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    {a : ℝ} (ha : a ≠ 0) (β x b b' : ℝ) (r l s m : ℕ) (hls : 1 ≤ l+s)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio r ∪ Ici (r+(l+s+1)+(m+1)))] W) :
    (∫⁻ g, W g *
      (ENNReal.ofReal (kernelMarkedPinBlock J f β a x l s b b' (fun j => g (j+r))) *
        ENNReal.ofReal (kernelBlockTest J β a m b' (fun u => krKer J f β a u b)
          (fun j => g (j+(r+(l+s+1)))))) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) *
        (ENNReal.ofReal (kernelMarkedFullDens J ν f β a x l s b b') *
          ENNReal.ofReal (krDens J ν f β a (m+1) b' b)) := by
  have hK : Measurable (fun u => krKer J f β a u b) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have hF := (kernel_marked_pin_block_coord_measurable hJ hf β a x l s b b'
    (c := fun j => j+r) (S := Ico r (r+(l+s+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  have hG := (kernel_blockTest_coord_measurable hJ β a m b' hK
    (c := fun j => j+(r+(l+s+1))) (S := Ico (r+(l+s+1)) (r+(l+s+1)+(m+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  rw [kernel_iid_outer_two_blocks ν (by omega) (by omega) hW hF hG,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelMarkedPinBlock hJ hf β a x l s b b').ennreal_ofReal,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelBlockTest hJ β a m b' hK).ennreal_ofReal,
    kernel_lintegral_marked_pin_block_full ν hJ hJfin hf hf0 hfD hν ha β x b b' l s hls,
    kernel_lintegral_pin_block ν hJ hf hf0 hfD β a b' b m]

/-- The marked bridge may be the second internal block. -/
theorem kernel_pins_marked_with_outer_reward_full (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ u, 0 ≤ f u) (hfD : ∀ u, f u ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun u => ENNReal.ofReal (f u)))
    {a : ℝ} (ha : a ≠ 0) (β x b b' : ℝ) (r m l s : ℕ) (hls : 1 ≤ l+s)
    {W : (ℕ → ℝ) → ℝ≥0∞}
    (hW : Measurable[kCoordSigma (Iio r ∪ Ici (r+(m+1)+(l+s+1)))] W) :
    (∫⁻ g, W g *
      (ENNReal.ofReal (kernelBlockTest J β a m b (fun u => krKer J f β a u b')
        (fun j => g (j+r))) *
        ENNReal.ofReal (kernelMarkedPinBlock J f β a x l s b' b
          (fun j => g (j+(r+(m+1)))))) ∂iidLaw ν) =
      (∫⁻ g, W g ∂iidLaw ν) *
        (ENNReal.ofReal (krDens J ν f β a (m+1) b b') *
          ENNReal.ofReal (kernelMarkedFullDens J ν f β a x l s b' b)) := by
  have hK : Measurable (fun u => krKer J f β a u b') :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have hF := (kernel_blockTest_coord_measurable hJ β a m b hK
    (c := fun j => j+r) (S := Ico r (r+(m+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  have hG := (kernel_marked_pin_block_coord_measurable hJ hf β a x l s b' b
    (c := fun j => j+(r+(m+1))) (S := Ico (r+(m+1)) (r+(m+1)+(l+s+1)))
      (by intro j hj; constructor <;> omega)).ennreal_ofReal
  rw [kernel_iid_outer_two_blocks ν (by omega) (by omega) hW hF hG,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelBlockTest hJ β a m b hK).ennreal_ofReal,
    kernel_iid_lintegral_reindex ν (fun _ _ h => Nat.add_right_cancel h)
      (measurable_kernelMarkedPinBlock hJ hf β a x l s b' b).ennreal_ofReal,
    kernel_lintegral_pin_block ν hJ hf hf0 hfD β a b b' m,
    kernel_lintegral_marked_pin_block_full ν hJ hJfin hf hf0 hfD hν ha β x b' b l s hls]

end
end PGM
