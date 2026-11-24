import PLAStochastic.Index.GEP.Kernel.Facet.ActiveRoot
import PLAStochastic.Index.GEP.Kernel.Row.KilledTransition

/-!
# Actual facet paths split into four killed blocks

The first block runs backwards from the first contact. The two bridges and the
last block run forwards. Every block includes both of its endpoints, so the
identities also cover zero-step outer blocks.
-/

namespace PGM
noncomputable section
open MeasureTheory ProbabilityTheory Set

def kernelReversePrefix (g : ℕ → ℝ) (r : ℕ) (j : ℕ) : ℝ := g (r - 1 - j)

theorem kernel_kWalk_succ_last (b β a : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    kWalk b β a g (n + 1) = kWalk b β a g n + β - a * g n := by
  simp only [kWalk, gapKeys, Finset.sum_range_succ]
  push_cast
  ring

theorem kernel_krAlive_eq_one_iff (J : Set ℝ) (β a b : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    krAlive J β a n b g = 1 ↔ ∀ l ≤ n, kWalk b β a g l ∈ J := by
  constructor
  · intro h l hl
    by_contra hn
    have hz : krAlive J β a n b g = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : l < n + 1))
      exact indicator_of_notMem hn _
    rw [h] at hz
    exact one_ne_zero hz
  · intro h
    apply Finset.prod_eq_one
    intro l hl
    exact indicator_of_mem (h l (by simpa using Finset.mem_range.mp hl)) _

theorem kernel_facet_walk_forward (eps σ : ℝ) (g : ℕ → ℝ) (r s t m l : ℕ) :
    kWalk (kernelFacetBandCoord eps σ (gapKeys g) r s t m) 1
      (fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
        (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s))
      (fun j => g (j + m)) l = kernelFacetBandCoord eps σ (gapKeys g) r s t (m + l) := by
  induction l with
  | zero => simp [kWalk_zero]
  | succ l ih =>
    rw [kernel_kWalk_succ_last, ih, Nat.add_succ, kernel_gap_facet_band_step]
    rw [Nat.add_comm l m]

theorem kernel_facet_walk_reverse (eps σ : ℝ) (g : ℕ → ℝ) (r s t : ℕ)
    {l : ℕ} (hl : l ≤ r) :
    kWalk (kernelFacetBandCoord eps σ (gapKeys g) r s t r) (-1)
      (-(fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
        (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s)))
      (kernelReversePrefix g r) l = kernelFacetBandCoord eps σ (gapKeys g) r s t (r - l) := by
  induction l with
  | zero => simp [kWalk_zero]
  | succ l ih =>
    rw [kernel_kWalk_succ_last, ih (by omega)]
    have he := kernel_gap_facet_band_step eps σ g r s t (r - (l + 1))
    have hn : r - (l + 1) + 1 = r - l := by omega
    rw [hn] at he
    have hm : r - 1 - l = r - (l + 1) := by omega
    simp only [kernelReversePrefix, hm]
    linarith

/-- Four-block splitting before specializing the three contact heights. -/
theorem kernel_facet_band_four_blocks (eps σ : ℝ) (g : ℕ → ℝ) {k r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) (htk : t ≤ k) :
    let a := fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s)
    let y := kernelFacetBandCoord eps σ (gapKeys g) r s t
    (∀ j ≤ k, y j ∈ Icc 0 (2 * eps)) ↔
      krAlive (Icc 0 (2 * eps)) (-1) (-a) r (y r) (kernelReversePrefix g r) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (s - r) (y r) (fun j => g (j + r)) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (t - s) (y s) (fun j => g (j + s)) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (k - t) (y t) (fun j => g (j + t)) = 1 := by
  dsimp only
  simp only [kernel_krAlive_eq_one_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro l hl
      rw [kernel_facet_walk_reverse eps σ g r s t hl]
      exact h _ (by omega)
    · intro l hl
      rw [kernel_facet_walk_forward]
      exact h _ (by omega)
    · intro l hl
      rw [kernel_facet_walk_forward]
      exact h _ (by omega)
    · intro l hl
      rw [kernel_facet_walk_forward]
      exact h _ (by omega)
  · rintro ⟨h₀, h₁, h₂, h₃⟩ j hj
    by_cases hjr : j ≤ r
    · have h := h₀ (r - j) (by omega)
      rw [kernel_facet_walk_reverse eps σ g r s t (by omega), Nat.sub_sub_self hjr] at h
      exact h
    · by_cases hjs : j ≤ s
      · have h := h₁ (j - r) (by omega)
        rw [kernel_facet_walk_forward, Nat.add_sub_of_le (by omega : r ≤ j)] at h
        exact h
      · by_cases hjt : j ≤ t
        · have h := h₂ (j - s) (by omega)
          rw [kernel_facet_walk_forward, Nat.add_sub_of_le (by omega : s ≤ j)] at h
          exact h
        · have h := h₃ (j - t) (by omega)
          rw [kernel_facet_walk_forward, Nat.add_sub_of_le (by omega : t ≤ j)] at h
          exact h

/-- On the actual active triple the four starts are the alternating contacts. -/
theorem kernel_prefix_facet_four_blocks {eps σ : ℝ} {g : ℕ → ℝ} {k r s t : ℕ}
    (hg : ∀ j < k, 0 < g j) (hrs : r < s) (hst : s < t) (htk : t ≤ k)
    (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s) = σ * eps) :
    let a := fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s)
    let b := eps - σ * eps
    let b' := eps + σ * eps
    prefixAffineFeasible eps (gapKeys g) (k + 1) ↔
      krAlive (Icc 0 (2 * eps)) (-1) (-a) r b (kernelReversePrefix g r) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (s - r) b (fun j => g (j + r)) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (t - s) b' (fun j => g (j + s)) = 1 ∧
      krAlive (Icc 0 (2 * eps)) 1 a (k - t) b (fun j => g (j + t)) = 1 := by
  dsimp only
  have hblocks := kernel_facet_band_four_blocks eps σ g hrs.le hst.le htk
  dsimp only at hblocks
  rw [kernel_gap_prefix_facet_band_iff hg hrs hst htk hσ hfacet, hblocks]
  obtain ⟨hr, hs, ht⟩ := kernel_facet_band_contacts
    (cert_gapKeys_lt hg _ _ hrs (by omega)) (cert_gapKeys_lt hg _ _ hst htk) hfacet
  rw [hr, hs, ht]

/-- A tested killed block, retaining an arbitrary measurable endpoint test. -/
def kernelBlockTest (J : Set ℝ) (β a : ℝ) (n : ℕ) (b : ℝ)
    (φ : ℝ → ℝ) (g : ℕ → ℝ) : ℝ :=
  krAlive J β a n b g * φ (kWalk b β a g n)

theorem kernel_blockTest_coord_measurable {J : Set ℝ} (hJ : MeasurableSet J)
    (β a : ℝ) (n : ℕ) (b : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {S : Set ℕ} {c : ℕ → ℕ} (hc : ∀ j < n, c j ∈ S) :
    Measurable[kCoordSigma S] (fun g : ℕ → ℝ =>
      kernelBlockTest J β a n b φ (fun j => g (c j))) := by
  let _ : MeasurableSpace (ℕ → ℝ) := kCoordSigma S
  have hw (l : ℕ) (hl : l ≤ n) :
      Measurable (fun g : ℕ → ℝ => kWalk b β a (fun j => g (c j)) l) := by
    unfold kWalk gapKeys
    exact measurable_const.sub (measurable_const.mul
      (Finset.measurable_sum _ fun j hj => kill_measurable_coord
        (hc j (lt_of_lt_of_le (Finset.mem_range.mp hj) hl))))
  have ha : Measurable (fun g : ℕ → ℝ => krAlive J β a n b (fun j => g (c j))) := by
    unfold krAlive
    exact Finset.measurable_prod _ fun l hl =>
      (measurable_const.indicator hJ).comp (hw l (by simpa using Finset.mem_range.mp hl))
  exact ha.mul (hφ.comp (hw n le_rfl))

theorem kernel_coordSigma_mono {S T : Set ℕ} (h : S ⊆ T) :
    kCoordSigma S ≤ kCoordSigma T := by
  apply iSup₂_le
  intro i hi
  exact le_iSup₂ (f := fun j (_ : j ∈ T) =>
    MeasurableSpace.comap (fun g : ℕ → ℝ => g j) inferInstance) i (h hi)

theorem kernel_iid_integral_mul_coords (ν : ProbabilityMeasure ℝ)
    {S T : Set ℕ} (hST : Disjoint S T) {F G : (ℕ → ℝ) → ℝ}
    (hF : Measurable[kCoordSigma S] F) (hG : Measurable[kCoordSigma T] G) :
    (∫ g, F g * G g ∂iidLaw ν) =
      (∫ g, F g ∂iidLaw ν) * ∫ g, G g ∂iidLaw ν := by
  have hind : IndepFun F G (iidLaw ν) := kill_indepFun_of_disjoint hST hF hG
  exact hind.integral_fun_mul_eq_mul_integral
    (hF.mono (kCoordSigma_le S) le_rfl).aestronglyMeasurable
    (hG.mono (kCoordSigma_le T) le_rfl).aestronglyMeasurable

/-- Actual disjoint-coordinate factorization on the original iid path space. -/
theorem kernel_iid_four_blocks (ν : ProbabilityMeasure ℝ) {r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t) {F₀ F₁ F₂ F₃ : (ℕ → ℝ) → ℝ}
    (h₀ : Measurable[kCoordSigma (Iio r)] F₀)
    (h₁ : Measurable[kCoordSigma (Ico r s)] F₁)
    (h₂ : Measurable[kCoordSigma (Ico s t)] F₂)
    (h₃ : Measurable[kCoordSigma (Ici t)] F₃) :
    (∫ g, F₀ g * (F₁ g * (F₂ g * F₃ g)) ∂iidLaw ν) =
      (∫ g, F₀ g ∂iidLaw ν) * ((∫ g, F₁ g ∂iidLaw ν) *
        ((∫ g, F₂ g ∂iidLaw ν) * ∫ g, F₃ g ∂iidLaw ν)) := by
  have h₁r : Measurable[kCoordSigma (Ici r)] F₁ :=
    h₁.mono (kernel_coordSigma_mono fun _ hj => hj.1) le_rfl
  have h₂s : Measurable[kCoordSigma (Ici s)] F₂ :=
    h₂.mono (kernel_coordSigma_mono fun _ hj => hj.1) le_rfl
  have h₃s : Measurable[kCoordSigma (Ici s)] F₃ :=
    h₃.mono (kernel_coordSigma_mono fun _ hj => le_trans hst hj) le_rfl
  have h₂r : Measurable[kCoordSigma (Ici r)] F₂ :=
    h₂s.mono (kernel_coordSigma_mono fun _ hj => le_trans hrs hj) le_rfl
  have h₃r : Measurable[kCoordSigma (Ici r)] F₃ :=
    h₃s.mono (kernel_coordSigma_mono fun _ hj => le_trans hrs hj) le_rfl
  rw [kernel_iid_integral_mul_coords ν (S := Iio r) (T := Ici r)
    (G := fun g => F₁ g * (F₂ g * F₃ g))
    (Set.disjoint_left.mpr (by
    intro j hj₁ hj₂
    change j < r at hj₁
    change r ≤ j at hj₂
    omega)) h₀ (h₁r.mul (h₂r.mul h₃r))]
  rw [kernel_iid_integral_mul_coords ν (S := Ico r s) (T := Ici s)
    (G := fun g => F₂ g * F₃ g)
    (Set.disjoint_left.mpr (by
    intro j hj₁ hj₂
    change r ≤ j ∧ j < s at hj₁
    change s ≤ j at hj₂
    omega)) h₁ (h₂s.mul h₃s)]
  rw [kernel_iid_integral_mul_coords ν (S := Ico s t) (T := Ici t)
    (Set.disjoint_left.mpr (by
    intro j hj₁ hj₂
    change s ≤ j ∧ j < t at hj₁
    change t ≤ j at hj₂
    omega)) h₂ h₃]

/-- Four killed blocks with fixed starts and slope factor under the actual iid
law. Endpoint tests are retained; no bridge pin event is used as a density. -/
theorem kernel_facet_tested_blocks_factor (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (a b b' : ℝ) {k r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t)
    {φ₀ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφ₀ : Measurable φ₀) (hφ₁ : Measurable φ₁)
    (hφ₂ : Measurable φ₂) (hφ₃ : Measurable φ₃) :
    let F₀ := fun g => kernelBlockTest J (-1) (-a) r b φ₀ (kernelReversePrefix g r)
    let F₁ := fun g => kernelBlockTest J 1 a (s-r) b φ₁ (fun j => g (j+r))
    let F₂ := fun g => kernelBlockTest J 1 a (t-s) b' φ₂ (fun j => g (j+s))
    let F₃ := fun g => kernelBlockTest J 1 a (k-t) b φ₃ (fun j => g (j+t))
    (∫ g, F₀ g * (F₁ g * (F₂ g * F₃ g)) ∂iidLaw ν) =
      (∫ g, F₀ g ∂iidLaw ν) * ((∫ g, F₁ g ∂iidLaw ν) *
        ((∫ g, F₂ g ∂iidLaw ν) * ∫ g, F₃ g ∂iidLaw ν)) := by
  apply kernel_iid_four_blocks ν hrs hst
  · exact kernel_blockTest_coord_measurable hJ (-1) (-a) r b hφ₀
      (S := Iio r) (c := fun j => r-1-j) (by intro j hj; change r-1-j < r; omega)
  · exact kernel_blockTest_coord_measurable hJ 1 a (s-r) b hφ₁
      (S := Ico r s) (by intro j hj; constructor <;> omega)
  · exact kernel_blockTest_coord_measurable hJ 1 a (t-s) b' hφ₂
      (S := Ico s t) (by intro j hj; constructor <;> omega)
  · exact kernel_blockTest_coord_measurable hJ 1 a (k-t) b hφ₃
      (S := Ici t) (by intro j _; change t ≤ j+t; omega)

theorem kernel_blockTest_congr (J : Set ℝ) (β a : ℝ) (n : ℕ) (b : ℝ)
    (φ : ℝ → ℝ) {g h : ℕ → ℝ} (he : ∀ j < n, g j = h j) :
    kernelBlockTest J β a n b φ g = kernelBlockTest J β a n b φ h := by
  have hw (l : ℕ) (hl : l ≤ n) : kWalk b β a g l = kWalk b β a h l := by
    unfold kWalk gapKeys
    congr 2
    exact Finset.sum_congr rfl fun j hj => he j (lt_of_lt_of_le (Finset.mem_range.mp hj) hl)
  have ha : krAlive J β a n b g = krAlive J β a n b h := by
    unfold krAlive
    apply Finset.prod_congr rfl
    intro l hl
    rw [hw l (by simpa using Finset.mem_range.mp hl)]
  simp only [kernelBlockTest, ha, hw n le_rfl]

/-- An injective extension of reversal of the first `r` coordinates. -/
def kernelReverseIndex (r j : ℕ) : ℕ := if j < r then r-1-j else j

theorem kernelReverseIndex_injective (r : ℕ) : Function.Injective (kernelReverseIndex r) := by
  intro i j hij
  unfold kernelReverseIndex at hij
  split_ifs at hij <;> omega

theorem kernel_iid_integral_reindex (ν : ProbabilityMeasure ℝ) {c : ℕ → ℕ}
    (hc : Function.Injective c) {F : (ℕ → ℝ) → ℝ} (hF : Measurable F) :
    (∫ g, F (fun j => g (c j)) ∂iidLaw ν) = ∫ g, F g ∂iidLaw ν := by
  have hm : Measurable (fun g : ℕ → ℝ => fun j => g (c j)) :=
    measurable_pi_lambda _ fun j => measurable_pi_apply (c j)
  have hmap : (iidLaw ν).map (fun g : ℕ → ℝ => fun j => g (c j)) = iidLaw ν :=
    Measure.map_infinitePi_infinitePi_of_inj hc
  have hh := integral_map hm.aemeasurable (f := F)
    (by rw [hmap]; exact hF.aestronglyMeasurable)
  rw [hmap] at hh
  exact hh.symm

theorem measurable_kernelBlockTest {J : Set ℝ} (hJ : MeasurableSet J)
    (β a : ℝ) (n : ℕ) (b : ℝ) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (kernelBlockTest J β a n b φ) :=
  (measurable_krAlive_right hJ β a n b).mul
    (hφ.comp ((measurable_kWalk_prod β a n).comp (measurable_const.prodMk measurable_id)))

theorem kernel_shifted_block_integral (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (β a : ℝ) (m n : ℕ) (b : ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ g, kernelBlockTest J β a n b φ (fun j => g (j+m)) ∂iidLaw ν) =
      krRow J (ν : Measure ℝ) β a n φ b := by
  rw [kernel_iid_integral_reindex ν (fun i j hij => Nat.add_right_cancel hij)
    (measurable_kernelBlockTest hJ β a n b hφ)]
  exact (krRow_eq_integral hJ ν β a n hφ hM b).symm

theorem kernel_reversed_block_integral (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (β a : ℝ) (r : ℕ) (b : ℝ)
    {φ : ℝ → ℝ} (hφ : Measurable φ) {M : ℝ} (hM : ∀ y, |φ y| ≤ M) :
    (∫ g, kernelBlockTest J β a r b φ (kernelReversePrefix g r) ∂iidLaw ν) =
      krRow J (ν : Measure ℝ) β a r φ b := by
  have he (g : ℕ → ℝ) :
      kernelBlockTest J β a r b φ (kernelReversePrefix g r) =
        kernelBlockTest J β a r b φ (fun j => g (kernelReverseIndex r j)) := by
    apply kernel_blockTest_congr
    intro j hj
    simp only [kernelReversePrefix, kernelReverseIndex, hj, if_true]
  simp_rw [he]
  rw [kernel_iid_integral_reindex ν (kernelReverseIndex_injective r)
    (measurable_kernelBlockTest hJ β a r b hφ)]
  exact (krRow_eq_integral hJ ν β a r hφ hM b).symm

/-- The four-factor integral equals the four genuine killed rows. This is a
fixed-slope identity with endpoint tests, suitable for subsequent density coarea. -/
theorem kernel_facet_tested_blocks_eq_rows (ν : ProbabilityMeasure ℝ)
    {J : Set ℝ} (hJ : MeasurableSet J) (a b b' : ℝ) {k r s t : ℕ}
    (hrs : r ≤ s) (hst : s ≤ t)
    {φ₀ φ₁ φ₂ φ₃ : ℝ → ℝ} (hφ₀ : Measurable φ₀) (hφ₁ : Measurable φ₁)
    (hφ₂ : Measurable φ₂) (hφ₃ : Measurable φ₃)
    {M₀ M₁ M₂ M₃ : ℝ} (hM₀ : ∀ y, |φ₀ y| ≤ M₀) (hM₁ : ∀ y, |φ₁ y| ≤ M₁)
    (hM₂ : ∀ y, |φ₂ y| ≤ M₂) (hM₃ : ∀ y, |φ₃ y| ≤ M₃) :
    (∫ g, kernelBlockTest J (-1) (-a) r b φ₀ (kernelReversePrefix g r) *
      (kernelBlockTest J 1 a (s-r) b φ₁ (fun j => g (j+r)) *
        (kernelBlockTest J 1 a (t-s) b' φ₂ (fun j => g (j+s)) *
          kernelBlockTest J 1 a (k-t) b φ₃ (fun j => g (j+t)))) ∂iidLaw ν) =
      krRow J (ν : Measure ℝ) (-1) (-a) r φ₀ b *
        (krRow J (ν : Measure ℝ) 1 a (s-r) φ₁ b *
          (krRow J (ν : Measure ℝ) 1 a (t-s) φ₂ b' *
            krRow J (ν : Measure ℝ) 1 a (k-t) φ₃ b)) := by
  have h := kernel_facet_tested_blocks_factor ν hJ a b b' hrs hst hφ₀ hφ₁ hφ₂ hφ₃
    (k := k)
  dsimp only at h
  rw [h, kernel_reversed_block_integral ν hJ (-1) (-a) r b hφ₀ hM₀,
    kernel_shifted_block_integral ν hJ 1 a r (s-r) b hφ₁ hM₁,
    kernel_shifted_block_integral ν hJ 1 a s (t-s) b' hφ₂ hM₂,
    kernel_shifted_block_integral ν hJ 1 a t (k-t) b hφ₃ hM₃]

theorem kernel_facet_contact_mem {eps σ : ℝ} (heps : 0 ≤ eps)
    (hσ : σ = 1 ∨ σ = -1) :
    eps - σ * eps ∈ Icc 0 (2 * eps) ∧ eps + σ * eps ∈ Icc 0 (2 * eps) := by
  rcases hσ with hσ | hσ <;> rw [hσ] <;>
    constructor <;> constructor <;> nlinarith

/-- The zero-step outer row has mass one at either prescribed contact. -/
theorem kernel_facet_zero_outer_survival (ν : ProbabilityMeasure ℝ)
    {eps σ : ℝ} (heps : 0 ≤ eps) (hσ : σ = 1 ∨ σ = -1) (β a : ℝ) :
    krSurv (Icc 0 (2 * eps)) (ν : Measure ℝ) β a 0 (eps - σ * eps) = 1 := by
  rw [krSurv, krRow_zero, indicator_of_mem (kernel_facet_contact_mem heps hσ).1]

/-- The two actual bridge endpoints are the opposite and the original contact. -/
theorem kernel_facet_bridge_contacts {eps σ : ℝ} (g : ℕ → ℝ) {r s t : ℕ}
    (hrs : r < s) (hst : s < t)
    (hA : gapKeys g r < gapKeys g s) (hB : gapKeys g s < gapKeys g t)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s) = σ * eps) :
    let a := fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s)
    kWalk (eps - σ * eps) 1 a (fun j => g (j+r)) (s-r) = eps + σ * eps ∧
      kWalk (eps + σ * eps) 1 a (fun j => g (j+s)) (t-s) = eps - σ * eps := by
  dsimp only
  obtain ⟨hr, hs, ht⟩ := kernel_facet_band_contacts hA hB hfacet
  have h₁ := kernel_facet_walk_forward eps σ g r s t r (s-r)
  have h₂ := kernel_facet_walk_forward eps σ g r s t s (t-s)
  rw [hr, Nat.add_sub_of_le hrs.le, hs] at h₁
  rw [hs, Nat.add_sub_of_le hst.le, ht] at h₂
  exact ⟨h₁, h₂⟩

theorem kernel_krAlive_zero_or_one (J : Set ℝ) (β a b : ℝ) (g : ℕ → ℝ) (n : ℕ) :
    krAlive J β a n b g = 0 ∨ krAlive J β a n b g = 1 := by
  by_cases h : ∀ l ≤ n, kWalk b β a g l ∈ J
  · exact Or.inr ((kernel_krAlive_eq_one_iff J β a b g n).mpr h)
  · push Not at h
    obtain ⟨l, hl, hn⟩ := h
    left
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : l < n+1))
    exact indicator_of_notMem hn _

/-- Pointwise indicator factorization on an actual active facet. -/
theorem kernel_prefix_facet_indicator_blocks {eps σ : ℝ} {g : ℕ → ℝ} {k r s t : ℕ}
    (hg : ∀ j < k, 0 < g j) (hrs : r < s) (hst : s < t) (htk : t ≤ k)
    (hσ : σ = 1 ∨ σ = -1)
    (hfacet : fluxSignedWidth ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s) = σ * eps) :
    let a := fluxSlope ((s : ℝ) - r) ((t : ℝ) - s)
      (gapKeys g s - gapKeys g r) (gapKeys g t - gapKeys g s)
    let b := eps - σ * eps
    let b' := eps + σ * eps
    {h : ℕ → ℝ | prefixAffineFeasible eps (gapKeys h) (k+1)}.indicator
      (fun _ => (1 : ℝ)) g =
      krAlive (Icc 0 (2*eps)) (-1) (-a) r b (kernelReversePrefix g r) *
        (krAlive (Icc 0 (2*eps)) 1 a (s-r) b (fun j => g (j+r)) *
          (krAlive (Icc 0 (2*eps)) 1 a (t-s) b' (fun j => g (j+s)) *
            krAlive (Icc 0 (2*eps)) 1 a (k-t) b (fun j => g (j+t)))) := by
  classical
  dsimp only
  have he := kernel_prefix_facet_four_blocks hg hrs hst htk hσ hfacet
  dsimp only at he
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hf
  · obtain ⟨h₀, h₁, h₂, h₃⟩ := he.mp hf
    simp only [h₀, h₁, h₂, h₃, mul_one]
  · have hn := mt he.mpr hf
    rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) (-1) _ _ (kernelReversePrefix g r) r
      with h₀ | h₀
    · rw [h₀, zero_mul]
    rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) 1 _ _ (fun j => g (j+r)) (s-r)
      with h₁ | h₁
    · rw [h₁, zero_mul, mul_zero]
    rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) 1 _ _ (fun j => g (j+s)) (t-s)
      with h₂ | h₂
    · rw [h₂, zero_mul, mul_zero, mul_zero]
    rcases kernel_krAlive_zero_or_one (Icc 0 (2*eps)) 1 _ _ (fun j => g (j+t)) (k-t)
      with h₃ | h₃
    · rw [h₃, mul_zero, mul_zero, mul_zero]
    exact (hn ⟨h₀, h₁, h₂, h₃⟩).elim

end
end PGM
