import PLAStochastic.Index.GEP.Kernel.Influence.PinBridge.LastGap
import PLAStochastic.Index.GEP.Kernel.Influence.Coarea.KilledBlocks

/-!
# Actual iid block factorization with marked pin densities

The two bridge factors are genuine last-random-step densities on disjoint
coordinate blocks. Endpoint tests on both outer rows are retained. This is the
fixed-slope factorization used after the physical coarea reconstruction.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set
set_option maxHeartbeats 800000

theorem kernel_finite_path_coord_measurable {E : Type*} [MeasurableSpace E]
    {n : ℕ} {F : (ℕ → ℝ) → E}
    (hF : Measurable F)
    (hdep : ∀ g h, (∀ j < n, g j = h j) → F g = F h)
    {S : Set ℕ} {c : ℕ → ℕ} (hc : ∀ j < n, c j ∈ S) :
    Measurable[kCoordSigma S] (fun g : ℕ → ℝ => F (fun j => g (c j))) := by
  let _ : MeasurableSpace (ℕ → ℝ) := kCoordSigma S
  let cut : (ℕ → ℝ) → (ℕ → ℝ) := fun g j => if j < n then g (c j) else 0
  have hm : @Measurable (ℕ → ℝ) (ℕ → ℝ) (kCoordSigma S) MeasurableSpace.pi cut := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j < n
    · simpa only [cut, if_pos hj] using kill_measurable_coord (hc j hj)
    · simpa only [cut, if_neg hj] using (measurable_const : Measurable fun _ : ℕ → ℝ => (0 : ℝ))
  have he : (fun g : ℕ → ℝ => F (fun j => g (c j))) = fun g => F (cut g) := by
    funext g
    exact hdep _ _ fun j hj => by simp only [cut, if_pos hj]
  rw [he]
  exact hF.comp hm

/-- Integration of four finite path functionals on the original iid path.
The first block is reversed, and all four intervals are disjoint. -/
theorem kernel_finite_four_blocks_integral (ν : ProbabilityMeasure ℝ)
    (r L M N : ℕ) {F₀ F₁ F₂ F₃ : (ℕ → ℝ) → ℝ}
    (h₀ : Measurable F₀) (h₁ : Measurable F₁) (h₂ : Measurable F₂) (h₃ : Measurable F₃)
    (d₀ : ∀ g h, (∀ j < r, g j = h j) → F₀ g = F₀ h)
    (d₁ : ∀ g h, (∀ j < L, g j = h j) → F₁ g = F₁ h)
    (d₂ : ∀ g h, (∀ j < M, g j = h j) → F₂ g = F₂ h)
    (d₃ : ∀ g h, (∀ j < N, g j = h j) → F₃ g = F₃ h) :
    (∫ g, F₀ (kernelReversePrefix g r) *
      (F₁ (fun j => g (j+r)) * (F₂ (fun j => g (j+(r+L))) *
        F₃ (fun j => g (j+(r+L+M))))) ∂iidLaw ν) =
      (∫ g, F₀ g ∂iidLaw ν) * ((∫ g, F₁ g ∂iidLaw ν) *
        ((∫ g, F₂ g ∂iidLaw ν) * ∫ g, F₃ g ∂iidLaw ν)) := by
  have hf := kernel_iid_four_blocks ν (r := r) (s := r+L) (t := r+L+M)
    (by omega) (by omega)
    (kernel_finite_path_coord_measurable h₀ d₀
      (c := fun j => r-1-j) (S := Iio r) (by intro j hj; change r-1-j < r; omega))
    (kernel_finite_path_coord_measurable h₁ d₁
      (c := fun j => j+r) (S := Ico r (r+L)) (by intro j hj; constructor <;> omega))
    (kernel_finite_path_coord_measurable h₂ d₂
      (c := fun j => j+(r+L)) (S := Ico (r+L) (r+L+M)) (by intro j hj; constructor <;> omega))
    (kernel_finite_path_coord_measurable h₃ d₃
      (c := fun j => j+(r+L+M)) (S := Ici (r+L+M)) (by intro j _; change r+L+M ≤ j+(r+L+M); omega))
  have hfac :
      (∫ g, F₀ (kernelReversePrefix g r) *
        (F₁ (fun j => g (j+r)) * (F₂ (fun j => g (j+(r+L))) *
          F₃ (fun j => g (j+(r+L+M))))) ∂iidLaw ν) =
        (∫ g, F₀ (kernelReversePrefix g r) ∂iidLaw ν) *
          ((∫ g, F₁ (fun j => g (j+r)) ∂iidLaw ν) *
            ((∫ g, F₂ (fun j => g (j+(r+L))) ∂iidLaw ν) *
              ∫ g, F₃ (fun j => g (j+(r+L+M))) ∂iidLaw ν)) := by
    unfold kernelReversePrefix
    exact hf
  rw [hfac]
  have he (g : ℕ → ℝ) : F₀ (kernelReversePrefix g r) =
      F₀ (fun j => g (kernelReverseIndex r j)) := by
    apply d₀
    intro j hj
    simp only [kernelReversePrefix, kernelReverseIndex, if_pos hj]
  simp_rw [he]
  rw [kernel_iid_integral_reindex ν (kernelReverseIndex_injective r) h₀,
    kernel_iid_integral_reindex ν (fun _ _ h => Nat.add_right_cancel h) h₁,
    kernel_iid_integral_reindex ν (fun _ _ h => Nat.add_right_cancel h) h₂,
    kernel_iid_integral_reindex ν (fun _ _ h => Nat.add_right_cancel h) h₃]

theorem kernel_marked_blockTest_coord_measurable {J : Set ℝ} (hJ : MeasurableSet J)
    (β a t : ℝ) (l n : ℕ) (b : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {S : Set ℕ} {c : ℕ → ℕ} (hc : ∀ j < n, c j ∈ S) :
    Measurable[kCoordSigma S] (fun g : ℕ → ℝ =>
      kernelBlockTest J β a n b φ (Function.update (fun j => g (c j)) l t)) := by
  have hm : Measurable (fun g : ℕ → ℝ => kernelBlockTest J β a n b φ (Function.update g l t)) :=
    (measurable_kernelBlockTest hJ β a n b hφ).comp
      ((measurable_update_pair l).comp (measurable_const.prodMk measurable_id))
  apply kernel_finite_path_coord_measurable hm (n := n) ?_ hc
  intro g h hgh
  apply kernel_blockTest_congr
  intro j hj
  by_cases hjl : j = l
  · simp only [hjl, Function.update_self]
  · simp only [Function.update_of_ne hjl, hgh j hj]

/-- The first bridge contains the mark and has at least one random step after
it. The four factors are actual reversed row, marked pin, pin and forward row. -/
theorem kernel_marked_pinned_four_blocks (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJfin : volume J ≠ ⊤)
    {f : ℝ → ℝ} {D : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    {a : ℝ} (ha : a ≠ 0) (β x b b' : ℝ) (r l s m N : ℕ) (hs : 1 ≤ s)
    {φ₀ φ₃ : ℝ → ℝ} (hφ₀ : Measurable φ₀) (hφ₃ : Measurable φ₃)
    {M₀ M₃ : ℝ} (hM₀ : ∀ y, |φ₀ y| ≤ M₀) (hM₃ : ∀ y, |φ₃ y| ≤ M₃) :
    (∫ g, kernelBlockTest J (-β) (-a) r b φ₀ (kernelReversePrefix g r) *
      (kernelBlockTest J β a (l+s) b (fun u => krKer J f β a u b')
          (Function.update (fun j => g (j+r)) l x) *
        (kernelBlockTest J β a m b' (fun u => krKer J f β a u b)
          (fun j => g (j+(r+(l+s+1)))) *
          kernelBlockTest J β a N b φ₃ (fun j => g (j+(r+(l+s+1)+(m+1)))))) ∂iidLaw ν) =
      krRow J ν (-β) (-a) r φ₀ b *
        (kernelMarkedFullDens J ν f β a x l s b b' *
          (krDens J ν f β a (m+1) b' b * krRow J ν β a N φ₃ b)) := by
  let F₀ := kernelBlockTest J (-β) (-a) r b φ₀
  let F₁ := fun g : ℕ → ℝ => kernelBlockTest J β a (l+s) b
    (fun u => krKer J f β a u b') (Function.update g l x)
  let F₂ := kernelBlockTest J β a m b' (fun u => krKer J f β a u b)
  let F₃ := kernelBlockTest J β a N b φ₃
  have hK (z : ℝ) : Measurable (fun u => krKer J f β a u z) :=
    (measurable_krKer_prod hJ hf β a).comp (measurable_id.prodMk measurable_const)
  have h₁ : Measurable F₁ :=
    (measurable_kernelBlockTest hJ β a (l+s) b (hK b')).comp
      ((measurable_update_pair l).comp (measurable_const.prodMk measurable_id))
  have d₁ : ∀ g h, (∀ j < l+s+1, g j = h j) → F₁ g = F₁ h := by
    intro g h hgh
    apply kernel_blockTest_congr
    intro j hj
    by_cases hjl : j = l
    · simp only [hjl, Function.update_self]
    · simp only [Function.update_of_ne hjl, hgh j (by omega)]
  have hb := kernel_finite_four_blocks_integral ν r (l+s+1) (m+1) N
    (measurable_kernelBlockTest hJ (-β) (-a) r b hφ₀) h₁
    (measurable_kernelBlockTest hJ β a m b' (hK b))
    (measurable_kernelBlockTest hJ β a N b hφ₃)
    (fun _ _ h => kernel_blockTest_congr _ _ _ _ _ _ h) d₁
    (fun _ _ h => kernel_blockTest_congr _ _ _ _ _ _ fun j hj => h j (by omega))
    (fun _ _ h => kernel_blockTest_congr _ _ _ _ _ _ h)
  change _ = _ at hb
  rw [hb]
  have hrow₀ : (∫ g, F₀ g ∂iidLaw ν) = krRow J ν (-β) (-a) r φ₀ b :=
    (krRow_eq_integral hJ ν (-β) (-a) r hφ₀ hM₀ b).symm
  have hrow₃ : (∫ g, F₃ g ∂iidLaw ν) = krRow J ν β a N φ₃ b :=
    (krRow_eq_integral hJ ν β a N hφ₃ hM₃ b).symm
  have hpin₁ : (∫ g, F₁ g ∂iidLaw ν) = kernelMarkedFullDens J ν f β a x l s b b' :=
    kernelUpdatedLastDensity_eq_full hJ hJfin ν hf hf0 hfD hν ha β x l hs b b'
  have hpin₂ : (∫ g, F₂ g ∂iidLaw ν) = krDens J ν f β a (m+1) b' b :=
    (krDens_succ ν m b' b).symm
  change (∫ g, F₀ g ∂iidLaw ν) * ((∫ g, F₁ g ∂iidLaw ν) *
    ((∫ g, F₂ g ∂iidLaw ν) * ∫ g, F₃ g ∂iidLaw ν)) = _
  rw [hrow₀, hrow₃, hpin₁, hpin₂]

end
end PGM
