import PLAStochastic.Index.KEP.CountRoute.WindowTail
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# The window configuration of the sorted uniform sample

Source: `pgm-analysis/research/2026-09-28-kep-additive/poisson-bridge.md`, §2–§3.

Under `Renyi.orderLaw M` the sorted uniforms `w` are the anchored positions of the `M` keys
after an anchor.  The **window** is `[0, β)` in the uniform coordinate; its configuration is
the number of sorted coordinates below `β` together with those coordinates, padded by `1`
(`winConf`).  Conditionally on the count `k`, the window coordinates are `k` sorted iid
uniforms on `[0, β]` (`winKernel`), and the count is binomial:

`(orderLaw M).map (winConf β) = binomial M β ⊗ₘ winKernel β` (`map_winConf_orderLaw`).

The proof splits the simplex of `k + m` coordinates into the first `k` (below `β`) and the
last `m` (at or above `β`) by `Renyi.appendMap`; the first block is a `β`-dilation of the
`k`-simplex, the second a `(1 - β)`-dilation of the `m`-simplex.
-/

set_option autoImplicit false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset Renyi Function
open scoped ENNReal Nat

/-! ## Window count, padded coordinates and the configuration kernel -/

/-- Number of sorted coordinates strictly below `β`. -/
def winPts (β : ℝ) {M : ℕ} (w : Fin M → ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin M => w i < β).card

/-- Window coordinates: `w t` when `w t < β`, the sentinel `1` otherwise and beyond `M`. -/
def winPad (β : ℝ) {M : ℕ} (w : Fin M → ℝ) : ℕ → ℝ := fun t =>
  if h : t < M then (if w ⟨t, h⟩ < β then w ⟨t, h⟩ else 1) else 1

/-- The window configuration: count and padded window coordinates. -/
def winConf (β : ℝ) {M : ℕ} (w : Fin M → ℝ) : ℕ × (ℕ → ℝ) := (winPts β w, winPad β w)

/-- A finite vector padded by `1`. -/
def padFin {k : ℕ} (x : Fin k → ℝ) : ℕ → ℝ := fun t => if h : t < k then x ⟨t, h⟩ else 1

/-- `k` sorted uniforms on `[0, β]`, padded by `1`. -/
def padScale (β : ℝ) {k : ℕ} (v : Fin k → ℝ) : ℕ → ℝ := padFin fun i => β * v i

/-- The window configuration kernel: given the count `k`, `k` sorted iid uniforms on
    `[0, β]`. -/
def winKernel (β : ℝ) : Kernel ℕ (ℕ → ℝ) :=
  Kernel.ofFunOfCountable fun k => (orderLaw k).map (padScale β)

theorem winKernel_apply (β : ℝ) (k : ℕ) : winKernel β k = (orderLaw k).map (padScale β) := rfl

theorem measurable_padFin {k : ℕ} : Measurable (padFin : (Fin k → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun t => ?_
  unfold padFin
  split_ifs
  · exact measurable_pi_apply _
  · exact measurable_const

theorem measurable_padScale (β : ℝ) {k : ℕ} :
    Measurable (padScale β : (Fin k → ℝ) → ℕ → ℝ) :=
  measurable_padFin.comp (measurable_pi_lambda _ fun i => measurable_const.mul (measurable_pi_apply i))

instance isMarkovKernel_winKernel (β : ℝ) : IsMarkovKernel (winKernel β) :=
  ⟨fun k => by
    rw [winKernel_apply]
    exact Measure.isProbabilityMeasure_map (measurable_padScale β).aemeasurable⟩

theorem measurable_winPts (β : ℝ) {M : ℕ} : Measurable (winPts β : (Fin M → ℝ) → ℕ) := by
  have : (winPts β : (Fin M → ℝ) → ℕ) =
      fun w => ∑ i : Fin M, if w i < β then 1 else 0 := by
    funext w
    rw [winPts, Finset.card_filter]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    Measurable.ite (measurableSet_lt (measurable_pi_apply i) measurable_const)
      measurable_const measurable_const

theorem measurable_winPad (β : ℝ) {M : ℕ} : Measurable (winPad β : (Fin M → ℝ) → ℕ → ℝ) := by
  refine measurable_pi_lambda _ fun t => ?_
  unfold winPad
  split_ifs with h
  · exact Measurable.ite (measurableSet_lt (measurable_pi_apply _) measurable_const)
      (measurable_pi_apply _) measurable_const
  · exact measurable_const

theorem measurable_winConf (β : ℝ) {M : ℕ} :
    Measurable (winConf β : (Fin M → ℝ) → ℕ × (ℕ → ℝ)) :=
  (measurable_winPts β).prodMk (measurable_winPad β)

theorem winPts_le (β : ℝ) {M : ℕ} (w : Fin M → ℝ) : winPts β w ≤ M := by
  unfold winPts
  exact (Finset.card_filter_le _ _).trans (by simp)

/-! ## Measures on `ℕ × X` are determined by their slices -/

theorem Measure.ext_nat_prod {X : Type*} [MeasurableSpace X] {μ ν : Measure (ℕ × X)}
    (h : ∀ k (t : Set X), MeasurableSet t → μ ({k} ×ˢ t) = ν ({k} ×ˢ t)) : μ = ν := by
  ext S hS
  have hS' : S = ⋃ k, ({k} : Set ℕ) ×ˢ (Prod.mk k ⁻¹' S) := by
    ext ⟨a, b⟩
    simp only [mem_iUnion, mem_prod, mem_singleton_iff, Set.mem_preimage]
    constructor
    · intro hab
      exact ⟨a, rfl, hab⟩
    · rintro ⟨k, rfl, hab⟩
      exact hab
  have hdisj : Pairwise (Disjoint on fun k => ({k} : Set ℕ) ×ˢ (Prod.mk k ⁻¹' S)) := by
    intro i j hij
    exact Set.disjoint_prod.2 (Or.inl (Set.disjoint_singleton.2 hij))
  have hmeas : ∀ k, MeasurableSet (({k} : Set ℕ) ×ˢ (Prod.mk k ⁻¹' S)) := fun k =>
    (measurableSet_singleton k).prod (measurable_prodMk_left hS)
  rw [hS', measure_iUnion hdisj hmeas, measure_iUnion hdisj hmeas]
  exact tsum_congr fun k => h k _ (measurable_prodMk_left hS)

/-! ## The split sample -/

section Split

variable {k m : ℕ} {β : ℝ}

theorem winPts_append_of_lt_of_le {x : Fin k → ℝ} {y : Fin m → ℝ}
    (hx : ∀ i, x i < β) (hy : ∀ j, β ≤ y j) : winPts β (Fin.append x y) = k := by
  rw [winPts, Finset.card_filter, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, hx, if_true, not_lt.2 (hy _), if_false,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one, mul_zero,
    add_zero]

theorem lt_of_winPts_append_eq {x : Fin k → ℝ} {y : Fin m → ℝ}
    (hmono : StrictMono (Fin.append x y)) (hk : winPts β (Fin.append x y) = k) :
    (∀ i, x i < β) ∧ ∀ j, β ≤ y j := by
  set w := Fin.append x y with hw
  constructor
  · intro i
    by_contra hi
    rw [not_lt] at hi
    have hsub : (Finset.univ.filter fun a : Fin (k + m) => w a < β) ⊆
        Finset.Iio (Fin.castAdd m i) := by
      intro a ha
      rw [Finset.mem_filter] at ha
      rw [Finset.mem_Iio]
      by_contra hle
      rw [not_lt] at hle
      have : x i ≤ w a := by
        have := hmono.monotone hle
        simpa [hw, Fin.append_left] using this
      linarith [ha.2]
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    change winPts β w ≤ _ at this
    rw [hk] at this
    simp only [Fin.val_castAdd] at this
    exact absurd this (not_le.2 i.isLt)
  · intro j
    by_contra hj
    rw [not_le] at hj
    have hsub : Finset.Iic (Fin.natAdd k j) ⊆
        (Finset.univ.filter fun a : Fin (k + m) => w a < β) := by
      intro a ha
      rw [Finset.mem_Iic] at ha
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have : w a ≤ y j := by
        have := hmono.monotone ha
        simpa [hw, Fin.append_right] using this
      linarith
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    change _ ≤ winPts β w at this
    rw [hk] at this
    simp only [Fin.val_natAdd] at this
    omega

theorem winPad_append_eq_padFin {x : Fin k → ℝ} {y : Fin m → ℝ}
    (hx : ∀ i, x i < β) (hy : ∀ j, β ≤ y j) : winPad β (Fin.append x y) = padFin x := by
  funext t
  unfold winPad padFin
  by_cases ht : t < k + m
  · rw [dif_pos ht]
    by_cases htk : t < k
    · rw [dif_pos htk]
      have : (⟨t, ht⟩ : Fin (k + m)) = Fin.castAdd m ⟨t, htk⟩ := rfl
      rw [this, Fin.append_left, if_pos (hx _)]
    · rw [dif_neg htk]
      have : (⟨t, ht⟩ : Fin (k + m)) = Fin.natAdd k ⟨t - k, by omega⟩ := by
        ext
        simp only [Fin.val_natAdd]
        omega
      rw [this, Fin.append_right, if_neg (not_lt.2 (hy _))]
  · rw [dif_neg ht, dif_neg (by omega)]

/-- The first block of the split window set. -/
def winHead (β : ℝ) (k : ℕ) (C : Set (ℕ → ℝ)) : Set (Fin k → ℝ) :=
  {x | x ∈ simplex k ∧ (∀ i, x i < β) ∧ padFin x ∈ C}

/-- The second block of the split window set. -/
def winTailSet (β : ℝ) (m : ℕ) : Set (Fin m → ℝ) :=
  {y | StrictMono y ∧ (∀ j, β ≤ y j) ∧ ∀ j, y j < 1}

theorem append_mem_winSet_iff (hβ0 : 0 < β) {C : Set (ℕ → ℝ)} {x : Fin k → ℝ}
    {y : Fin m → ℝ} :
    Fin.append x y ∈ (winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C) ∩ simplex (k + m) ↔
      x ∈ winHead β k C ∧ y ∈ winTailSet β m := by
  constructor
  · rintro ⟨⟨hpts, hpad⟩, hmono, hpos, hlt⟩
    obtain ⟨hx, hy⟩ := lt_of_winPts_append_eq hmono hpts
    rw [Set.mem_preimage, winPad_append_eq_padFin hx hy] at hpad
    refine ⟨⟨⟨fun a b hab => ?_, fun i => ?_, fun i => ?_⟩, hx, hpad⟩,
      fun a b hab => ?_, hy, fun j => ?_⟩
    · simpa using hmono ((Fin.strictMono_castAdd m) hab)
    · simpa using hpos (Fin.castAdd m i)
    · simpa using hlt (Fin.castAdd m i)
    · simpa using hmono ((Fin.strictMono_natAdd k) hab)
    · simpa using hlt (Fin.natAdd k j)
  · rintro ⟨⟨⟨hxmono, hxpos, hxlt⟩, hx, hpad⟩, hymono, hy, hy1⟩
    have hmono : StrictMono (Fin.append x y) := by
      intro a b hab
      induction a using Fin.addCases with
      | left i =>
        induction b using Fin.addCases with
        | left j =>
          simp only [Fin.append_left]
          exact hxmono ((Fin.strictMono_castAdd m).lt_iff_lt.1 hab)
        | right j =>
          simp only [Fin.append_left, Fin.append_right]
          exact lt_of_lt_of_le (hx i) (hy j)
      | right i =>
        induction b using Fin.addCases with
        | left j =>
          exfalso
          rw [Fin.lt_def] at hab
          simp only [Fin.val_natAdd, Fin.val_castAdd] at hab
          omega
        | right j =>
          simp only [Fin.append_right]
          exact hymono ((Fin.strictMono_natAdd k).lt_iff_lt.1 hab)
    refine ⟨⟨winPts_append_of_lt_of_le hx hy, ?_⟩, hmono, fun a => ?_, fun a => ?_⟩
    · rw [Set.mem_preimage, winPad_append_eq_padFin hx hy]
      exact hpad
    · induction a using Fin.addCases with
      | left i => simpa using hxpos i
      | right j => simpa using lt_of_lt_of_le hβ0 (hy j)
    · induction a using Fin.addCases with
      | left i => simpa using hxlt i
      | right j => simpa using hy1 j

end Split

/-! ## Volumes of the two blocks -/

section Volumes

variable {β : ℝ}

theorem winHead_eq_preimage_smul (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) (C : Set (ℕ → ℝ)) :
    winHead β k C = (fun x : Fin k → ℝ => β⁻¹ • x) ⁻¹' (simplex k ∩ padScale β ⁻¹' C) := by
  have hβ : 0 < β⁻¹ := inv_pos.2 hβ0
  ext x
  have hps : padScale β (β⁻¹ • x) = padFin x := by
    funext t
    unfold padScale padFin
    split_ifs with h
    · show β * (β⁻¹ • x) ⟨t, h⟩ = x ⟨t, h⟩
      rw [Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hβ0.ne']
    · rfl
  have hmono : StrictMono (β⁻¹ • x) ↔ StrictMono x := by
    constructor
    · intro h a b hab
      have := h hab
      simp only [Pi.smul_apply, smul_eq_mul] at this
      exact lt_of_mul_lt_mul_left this hβ.le
    · intro h a b hab
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_lt_mul_of_pos_left (h hab) hβ
  have hpos : (∀ i, 0 < (β⁻¹ • x) i) ↔ ∀ i, 0 < x i :=
    forall_congr' fun i => by rw [Pi.smul_apply, smul_eq_mul, mul_pos_iff_of_pos_left hβ]
  have hlt : (∀ i, (β⁻¹ • x) i < 1) ↔ ∀ i, x i < β :=
    forall_congr' fun i => by rw [Pi.smul_apply, smul_eq_mul, inv_mul_lt_iff₀ hβ0, mul_one]
  have h1 : (∀ i, x i < β) → ∀ i, x i < 1 := fun h i => (h i).trans hβ1
  rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_preimage, hps]
  simp only [winHead, mem_ofPred_eq, simplex, hmono, hpos, hlt]
  tauto

theorem volume_winHead (hβ0 : 0 < β) (hβ1 : β < 1) (k : ℕ) (C : Set (ℕ → ℝ)) :
    volume (winHead β k C) =
      ENNReal.ofReal (β ^ k) * volume (simplex k ∩ padScale β ⁻¹' C) := by
  rw [winHead_eq_preimage_smul hβ0 hβ1 k C,
    Measure.addHaar_preimage_smul _ (inv_ne_zero hβ0.ne'), Module.finrank_fin_fun, inv_pow,
    inv_inv, abs_of_pos (pow_pos hβ0 k)]

theorem winTailSet_eq_ae (hβ1 : β < 1) (m : ℕ) :
    winTailSet β m =ᵐ[volume] rescVec β ⁻¹' simplex m := by
  have hsub : rescVec β ⁻¹' simplex m ⊆ winTailSet β m := by
    intro y hy
    rw [Set.mem_preimage, rescVec_mem_simplex_iff hβ1] at hy
    exact ⟨hy.1, fun j => (hy.2.1 j).le, hy.2.2⟩
  have hdiff : winTailSet β m \ rescVec β ⁻¹' simplex m ⊆ ⋃ j, {y : Fin m → ℝ | y j = β} := by
    intro y ⟨hy, hy'⟩
    rw [Set.mem_preimage, rescVec_mem_simplex_iff hβ1] at hy'
    simp only [mem_iUnion, mem_ofPred_eq]
    by_contra hne
    push Not at hne
    exact hy' ⟨hy.1, fun j => lt_of_le_of_ne (hy.2.1 j) (Ne.symm (hne j)), hy.2.2⟩
  have hnull : volume (⋃ j, {y : Fin m → ℝ | y j = β}) = 0 := by
    rw [measure_iUnion_null_iff]
    intro j
    rw [volume_pi]
    exact Measure.pi_hyperplane (μ := fun _ : Fin m => (volume : Measure ℝ)) j β
  refine ae_eq_set.2 ⟨measure_mono_null hdiff hnull, ?_⟩
  rw [sdiff_eq_empty.2 hsub, measure_empty]

theorem volume_winTailSet (hβ1 : β < 1) (m : ℕ) :
    volume (winTailSet β m) = ENNReal.ofReal ((1 - β) ^ m) * volume (simplex m) := by
  rw [measure_congr (winTailSet_eq_ae hβ1 m), volume_preimage_rescVec hβ1]

end Volumes

/-! ## The law of the window configuration -/

section Law

variable {β : ℝ}

theorem measurableSet_winPtsPad (β : ℝ) {M : ℕ} (k : ℕ) {C : Set (ℕ → ℝ)}
    (hC : MeasurableSet C) :
    MeasurableSet (winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C : Set (Fin M → ℝ)) :=
  (measurable_winPts β (measurableSet_singleton k)).inter (measurable_winPad β hC)

/-- The split sample: `(k + m)` sorted uniforms with exactly `k` below `β`. -/
theorem orderLaw_winSet (hβ0 : 0 < β) (hβ1 : β < 1) (k m : ℕ) {C : Set (ℕ → ℝ)}
    (hC : MeasurableSet C) :
    orderLaw (k + m) (winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C) =
      ENNReal.ofReal (((k + m).choose k : ℝ) * β ^ k * (1 - β) ^ m) *
        orderLaw k (padScale β ⁻¹' C) := by
  set S : Set (Fin (k + m) → ℝ) := winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C with hS
  have hSm : MeasurableSet S := measurableSet_winPtsPad β k hC
  have hpre : appendMap k m ⁻¹' (S ∩ simplex (k + m)) = winHead β k C ×ˢ winTailSet β m := by
    ext ⟨x, y⟩
    exact append_mem_winSet_iff hβ0
  rw [orderLaw_apply, ← (measurePreserving_appendMap k m).measure_preimage
    (hSm.inter measurableSet_simplex).nullMeasurableSet, hpre, Measure.prod_prod,
    volume_winHead hβ0 hβ1 k C, volume_winTailSet hβ1 m, orderLaw_apply, volume_simplex m,
    inter_comm (padScale β ⁻¹' C)]
  set V := volume (simplex k ∩ padScale β ⁻¹' C)
  have hfac : ((k + m)! : ℝ≥0∞) = ((k + m).choose k : ℝ≥0∞) * k ! * m ! := by
    have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right k m)
    rw [Nat.add_sub_cancel_left] at h
    rw [← h]
    push_cast
    ring
  have hm : (m ! : ℝ≥0∞) * (m ! : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.factorial_pos m).ne')
      (ENNReal.natCast_ne_top _)
  have hchoose : ENNReal.ofReal (((k + m).choose k : ℝ) * β ^ k * (1 - β) ^ m) =
      ((k + m).choose k : ℝ≥0∞) * ENNReal.ofReal (β ^ k) * ENNReal.ofReal ((1 - β) ^ m) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
  calc ((k + m)! : ℝ≥0∞) * (ENNReal.ofReal (β ^ k) * V *
        (ENNReal.ofReal ((1 - β) ^ m) * (m ! : ℝ≥0∞)⁻¹))
      = ((m ! : ℝ≥0∞) * (m ! : ℝ≥0∞)⁻¹) * (((k + m).choose k : ℝ≥0∞) *
          ENNReal.ofReal (β ^ k) * ENNReal.ofReal ((1 - β) ^ m) * ((k ! : ℝ≥0∞) * V)) := by
        rw [hfac]; ring
    _ = _ := by rw [hm, one_mul, hchoose]

theorem winConf_preimage (β : ℝ) {M : ℕ} (k : ℕ) (C : Set (ℕ → ℝ)) :
    (winConf β ⁻¹' ({k} ×ˢ C) : Set (Fin M → ℝ)) = winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C := by
  ext w
  simp only [winConf, Set.mem_preimage, mem_prod, mem_singleton_iff, mem_inter_iff]

/-- **The law of the window configuration.**  Under `orderLaw M`, the number of sorted
    coordinates below `β` is binomial `(M, β)` and, given this count `k`, the window
    coordinates are `k` sorted iid uniforms on `[0, β]`. -/
theorem map_winConf_orderLaw (hβ0 : 0 < β) (hβ1 : β < 1) (M : ℕ) :
    (orderLaw M).map (winConf β) = binomial M ⟨β, hβ0.le, hβ1.le⟩ ⊗ₘ winKernel β := by
  refine Measure.ext_nat_prod fun k C hC => ?_
  rw [Measure.map_apply (measurable_winConf β) ((measurableSet_singleton k).prod hC),
    Measure.compProd_apply_prod (measurableSet_singleton k) hC, lintegral_singleton,
    winKernel_apply, Measure.map_apply (measurable_padScale β) hC, binomial_singleton,
    winConf_preimage]
  rcases le_or_gt k M with hk | hk
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [orderLaw_winSet hβ0 hβ1 k m hC, Nat.add_sub_cancel_left, mul_comm]
  · have h0 : (winPts β ⁻¹' {k} ∩ winPad β ⁻¹' C : Set (Fin M → ℝ)) = ∅ := by
      refine eq_empty_of_forall_notMem fun w hw => ?_
      have h1 := winPts_le β w
      have h2 : winPts β w = k := hw.1
      omega
    rw [h0, measure_empty, Nat.choose_eq_zero_of_lt hk]
    simp

end Law

end

end PGM
