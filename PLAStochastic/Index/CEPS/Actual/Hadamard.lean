import PLAStochastic.Index.CEPS.Actual.Drawup

/-!
# P-CEPS WP8: the width Hadamard identity (S-2 (c))

`research/2026-10-02-lean-ceps/blueprint-CS.md` lemma S-2 (c); source (L13) of
`pgm-analysis/research/2026-09-28-gep-expansion/linear-coefficient-attack.md` §3.

For the walk `W_n = kWalk 0 β a g n` (step `β - aX`, gap density `f`, `a ≠ 0`) killed outside the
closed band `[0, z]`, let

* `h₋(z) = ∑ₙ e^{-qn} P_0(W_0, …, W_n ∈ [0, z])` (`cepsBottomSurv`, started at the bottom),
* `h₊(z) = ∑ₙ e^{-qn} P_z(W_0, …, W_n ∈ [0, z])` (`cepsTopSurv`, started at the top),
* `U(z) = ∑_{n ≥ 1} e^{-qn} k_n(0, z)` (`cepsBridgeSeries`), `k_n` the killed density from `0` to `z`.

Then `h₋(z₂) - h₋(z₁) = ∫_{(z₁, z₂]} U h₊` (`cepsBottomSurv_sub`), and `h₋` has derivative `U h₊`
wherever `U h₊` is continuous (`cepsBottomSurv_hasDerivAt`). Proof: on paths in `[0, z₂]` not in
`[0, z₁]`, split at the first time `k` of the maximum (`hadamard_pathwise`); the prefix before `k`
stays in `[0, W_k)`, the suffix in `[0, W_k]`. Integrating the last prefix step against the gap density
turns `W_k` into the endpoint variable `z` (`integral_lastStep`), and the suffix is the survival from
the top. The strict and closed prefix bands differ only at finitely many `z`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter

/-! ## The first-argmax decomposition of paths -/

open Classical in
/-- The first time `k ∈ [1, n]` at which the maximum of `W_0, …, W_n` is attained, with the maximum
in `(z₁, z₂]` and all values `≥ 0`. -/
def cepsArgmaxInd (z₁ z₂ β a : ℝ) (n k : ℕ) (g : ℕ → ℝ) : ℝ :=
  if (∀ i < k, kWalk 0 β a g i ∈ Ico 0 (kWalk 0 β a g k)) ∧ kWalk 0 β a g k ∈ Ioc z₁ z₂ ∧
      (∀ i, k < i → i ≤ n → kWalk 0 β a g i ∈ Icc 0 (kWalk 0 β a g k)) then 1 else 0

open Classical in
theorem krAlive_eq_ite (J : Set ℝ) (β a y : ℝ) (n : ℕ) (g : ℕ → ℝ) :
    krAlive J β a n y g = if ∀ i ≤ n, kWalk y β a g i ∈ J then 1 else 0 := by
  unfold krAlive
  exact cert_prod_indicator J (fun i => kWalk y β a g i) n

open Classical in
/-- **Pathwise first-argmax decomposition.** -/
theorem hadamard_pathwise {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) (β a : ℝ) (g : ℕ → ℝ)
    (n : ℕ) :
    krAlive (Icc 0 z₂) β a n 0 g - krAlive (Icc 0 z₁) β a n 0 g =
      ∑ j ∈ Finset.range n, cepsArgmaxInd z₁ z₂ β a n (j + 1) g := by
  set W : ℕ → ℝ := fun i => kWalk 0 β a g i with hW
  have hW0 : W 0 = 0 := kWalk_zero 0 β a g
  rw [krAlive_eq_ite, krAlive_eq_ite]
  -- a valid first argmax forces all values into `[0, z₂]`
  have hvalid : ∀ k ≤ n, cepsArgmaxInd z₁ z₂ β a n k g = 1 → ∀ i ≤ n, W i ∈ Icc 0 z₂ := by
    intro k hk h i hi
    unfold cepsArgmaxInd at h
    split_ifs at h with hc
    · obtain ⟨h1, h2, h3⟩ := hc
      rcases lt_trichotomy i k with hik | rfl | hik
      · exact ⟨(h1 i hik).1, ((h1 i hik).2.le).trans h2.2⟩
      · exact ⟨hz₁.trans h2.1.le, h2.2⟩
      · exact ⟨(h3 i hik hi).1, (h3 i hik hi).2.trans h2.2⟩
    · norm_num at h
  have hzero_or_one : ∀ k, cepsArgmaxInd z₁ z₂ β a n k g = 0 ∨ cepsArgmaxInd z₁ z₂ β a n k g = 1 := by
    intro k; unfold cepsArgmaxInd; split_ifs <;> simp
  by_cases h₁ : ∀ i ≤ n, kWalk 0 β a g i ∈ Icc 0 z₁
  · have h₂ : ∀ i ≤ n, kWalk 0 β a g i ∈ Icc 0 z₂ := fun i hi => ⟨(h₁ i hi).1, (h₁ i hi).2.trans hz⟩
    rw [if_pos h₂, if_pos h₁, sub_self]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hj := Finset.mem_range.1 hj
    unfold cepsArgmaxInd
    rw [if_neg]
    rintro ⟨-, h2, -⟩
    have := (h₁ (j + 1) (by omega)).2
    linarith [h2.1]
  by_cases h₂ : ∀ i ≤ n, kWalk 0 β a g i ∈ Icc 0 z₂
  · rw [if_pos h₂, if_neg h₁]
    -- the maximum exceeds `z₁`
    push Not at h₁
    obtain ⟨i₀, hi₀, hi₀'⟩ := h₁
    have hi₀z : z₁ < W i₀ := by
      by_contra hc
      exact hi₀' ⟨(h₂ i₀ hi₀).1, not_lt.1 hc⟩
    have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
    set M := (Finset.range (n + 1)).sup' hne W with hM
    have hle : ∀ i ≤ n, W i ≤ M := fun i hi =>
      Finset.le_sup' W (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    obtain ⟨i₁, hi₁, hi₁M⟩ := Finset.exists_mem_eq_sup' hne W
    have hSne : ((Finset.range (n + 1)).filter fun i => W i = M).Nonempty :=
      ⟨i₁, Finset.mem_filter.2 ⟨hi₁, hi₁M.symm⟩⟩
    set K := ((Finset.range (n + 1)).filter fun i => W i = M).min' hSne with hK
    have hKmem := Finset.min'_mem _ hSne
    rw [← hK, Finset.mem_filter, Finset.mem_range] at hKmem
    obtain ⟨hKn, hKM⟩ := hKmem
    have hKmin : ∀ i < K, W i ≠ M := fun i hi h => by
      have hmem : i ∈ (Finset.range (n + 1)).filter (fun i => W i = M) :=
        Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), h⟩
      have := Finset.min'_le _ i hmem
      rw [← hK] at this
      omega
    have hMz : z₁ < M := hi₀z.trans_le (hle i₀ hi₀)
    have hK0 : K ≠ 0 := fun h0 => by
      have : W 0 = M := h0 ▸ hKM
      rw [hW0] at this
      linarith
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, K = j₀ + 1 := Nat.exists_eq_succ_of_ne_zero hK0
    have hterm : cepsArgmaxInd z₁ z₂ β a n K g = 1 := by
      unfold cepsArgmaxInd
      rw [if_pos]
      refine ⟨fun i hi => ⟨(h₂ i (by omega)).1, ?_⟩, ⟨?_, ?_⟩, fun i hi1 hi2 => ⟨(h₂ i hi2).1, ?_⟩⟩
      · show W i < W K
        rw [hKM]
        exact lt_of_le_of_ne (hle i (by omega)) (hKmin i hi)
      · show z₁ < W K
        rw [hKM]; exact hMz
      · exact (h₂ K (by omega)).2
      · show W i ≤ W K
        rw [hKM]; exact hle i hi2
    have huniq : ∀ k, k ≤ n → k ≠ K → cepsArgmaxInd z₁ z₂ β a n k g = 0 := by
      intro k hk hkK
      rcases hzero_or_one k with h | h
      · exact h
      exfalso
      unfold cepsArgmaxInd at h hterm
      split_ifs at h hterm with hc hc'
      · rcases lt_or_gt_of_ne hkK with hlt | hlt
        · have := (hc.2.2 K hlt (by omega)).2
          have := (hc'.1 k hlt).2
          linarith
        · have := (hc'.2.2 k hlt hk).2
          have := (hc.1 K hlt).2
          linarith
      all_goals first | exact absurd hterm zero_ne_one | exact absurd h zero_ne_one
    rw [Finset.sum_eq_single j₀]
    · rw [← hj₀, hterm]; norm_num
    · intro j hj hjne
      exact huniq (j + 1) (by have := Finset.mem_range.1 hj; omega) (by omega)
    · intro h
      exact absurd (Finset.mem_range.2 (by omega)) h
  · rw [if_neg h₂, if_neg (fun h => h₂ fun i hi => ⟨(h i hi).1, (h i hi).2.trans hz⟩), sub_self]
    refine (Finset.sum_eq_zero fun j hj => ?_).symm
    have hj := Finset.mem_range.1 hj
    rcases hzero_or_one (j + 1) with h | h
    · exact h
    · exact absurd (hvalid (j + 1) (by omega) h) h₂

/-! ## Real-valued Fubini tools -/

theorem integral_iidLaw_update_real (ν : ProbabilityMeasure ℝ) (m : ℕ) {F : (ℕ → ℝ) → ℝ}
    (hF : Integrable F (iidLaw ν)) :
    ∫ g, F g ∂(iidLaw ν) = ∫ g, ∫ x, F (Function.update g m x) ∂(ν : Measure ℝ) ∂(iidLaw ν) := by
  have h := integral_iidLaw_update ν m (F := fun g => (F g : ℂ)) hF.ofReal
  simp only [integral_complex_ofReal] at h
  exact_mod_cast h

theorem integral_mul_shift_dep_real (ν : ProbabilityMeasure ℝ) (k : ℕ) {F : (ℕ → ℝ) → ℝ}
    (hF : Measurable F) (hFd : ∀ g g' : ℕ → ℝ, (∀ i < k, g i = g' i) → F g = F g')
    {W : (ℕ → ℝ) → ℝ} (hW : Measurable W) (hWd : ∀ g g' : ℕ → ℝ, (∀ i < k, g i = g' i) → W g = W g')
    {G : ℝ → (ℕ → ℝ) → ℝ} (hG : Measurable (Function.uncurry G)) (hFb : ∀ g, |F g| ≤ 1)
    (hGb : ∀ x h, |G x h| ≤ 1) :
    ∫ g, F g * G (W g) (fun i => g (i + k)) ∂(iidLaw ν) =
      ∫ g, F g * ∫ h, G (W g) h ∂(iidLaw ν) ∂(iidLaw ν) := by
  have h := integral_mul_shift_dep ν k (F := fun g => (F g : ℂ)) (Complex.measurable_ofReal.comp hF)
    (fun g g' hg => by simp only [hFd g g' hg]) hW hWd (G := fun x h => (G x h : ℂ))
    (Complex.measurable_ofReal.comp hG) (fun g => by rw [Complex.norm_real]; exact hFb g)
    (fun x h => by rw [Complex.norm_real]; exact hGb x h)
  simp only [← Complex.ofReal_mul, integral_complex_ofReal] at h
  exact_mod_cast h

/-- Change of variables for an affine image of a gap with density `f`. -/
theorem integral_density_affine {f : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0) (c : ℝ) (Ψ : ℝ → ℝ) :
    ∫ x, f x * Ψ (c - a * x) = ∫ z, f ((c - z) / a) / |a| * Ψ z := by
  set G : ℝ → ℝ := fun z => f ((c - z) / a) * Ψ z with hG
  have h1 : ∀ x, f x * Ψ (c - a * x) = G (-a * x + c) := by
    intro x
    simp only [hG]
    rw [show (c - (-a * x + c)) / a = x by field_simp; ring, show -a * x + c = c - a * x by ring]
  simp_rw [h1]
  have h2 := Measure.integral_comp_mul_left (fun y => G (y + c)) (-a)
  rw [h2, integral_add_right_eq_self (fun y => G y) c, abs_inv, abs_neg, smul_eq_mul,
    ← integral_const_mul]
  congr 1
  funext z
  simp only [hG]
  ring

/-! ## The last prefix step becomes the endpoint variable -/

variable {ν : ProbabilityMeasure ℝ} {f : ℝ → ℝ} {D : ℝ}

theorem CepsGapDensity.integral_lastStep (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) (j : ℕ) {Θ : (ℕ → ℝ) → ℝ → ℝ} (hΘ : Measurable (Function.uncurry Θ))
    (hΘb : ∀ g z, |Θ g z| ≤ 1) (hΘd : ∀ g z x, Θ (Function.update g j x) z = Θ g z) :
    ∫ g, Θ g (kWalk 0 β a g (j + 1)) ∂(iidLaw ν) =
      ∫ g, (∫ z, Θ g z * (f ((kWalk 0 β a g j + β - z) / a) / |a|)) ∂(iidLaw ν) := by
  have hm : Measurable fun g : ℕ → ℝ => Θ g (kWalk 0 β a g (j + 1)) :=
    hΘ.comp (measurable_id.prodMk (measurable_kWalk_right 0 β a (j + 1)))
  have hint : Integrable (fun g : ℕ → ℝ => Θ g (kWalk 0 β a g (j + 1))) (iidLaw ν) :=
    kr_integrable_of_bdd hm fun g => hΘb _ _
  rw [integral_iidLaw_update_real ν j hint]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  have hupd : ∀ x, Θ (Function.update g j x) (kWalk 0 β a (Function.update g j x) (j + 1)) =
      Θ g (kWalk 0 β a g j + β - a * x) := by
    intro x
    rw [hΘd, kernel_kWalk_succ_last, kernel_kWalk_update_after β a 0 g le_rfl, Function.update_self]
  simp_rw [hupd]
  rw [hf.eq, integral_withDensity_eq_integral_toReal_smul hf.measurable.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (hf.nonneg _), smul_eq_mul]
  rw [integral_density_affine ha (kWalk 0 β a g j + β) (Θ g)]
  congr 1
  funext z
  ring

theorem CepsGapDensity.integrable_density_prod (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) (j : ℕ) {Φ : (ℕ → ℝ) × ℝ → ℝ} (hΦ : Measurable Φ) (hΦb : ∀ p, |Φ p| ≤ 1) :
    Integrable (fun p : (ℕ → ℝ) × ℝ => Φ p * (f ((kWalk 0 β a p.1 j + β - p.2) / a) / |a|))
      ((iidLaw ν).prod volume) := by
  obtain ⟨hfi, hf1⟩ := surv_integrable_density hf.measurable hf.nonneg hf.eq
  have hR : Measurable fun g : ℕ → ℝ => kWalk 0 β a g j + β :=
    (measurable_kWalk_right 0 β a j).add_const β
  have hfm : Measurable fun p : (ℕ → ℝ) × ℝ => f ((kWalk 0 β a p.1 j + β - p.2) / a) / |a| :=
    (hf.measurable.comp (((hR.comp measurable_fst).sub measurable_snd).div_const a)).div_const _
  have hdens : ∀ c : ℝ, Integrable (fun z => f ((c - z) / a) / |a|) ∧
      ∫ z, f ((c - z) / a) / |a| = 1 := by
    intro c
    have h1 : ∫ z, f ((c - z) / a) / |a| = ∫ x, f x * (fun _ => (1 : ℝ)) (c - a * x) := by
      rw [integral_density_affine ha c (fun _ => (1 : ℝ))]
      simp
    refine ⟨?_, by rw [h1]; simpa using hf1⟩
    have h2 : (fun z => f ((c - z) / a) / |a|) = fun z => |a⁻¹| * f (a⁻¹ * (-z) + a⁻¹ * c) := by
      funext z
      rw [abs_inv]
      field_simp
      ring_nf
    rw [h2]
    refine Integrable.const_mul ?_ _
    have := ((hfi.comp_add_right (a⁻¹ * c)).comp_mul_left' (inv_ne_zero ha)).comp_neg
    simpa [add_comm] using this
  have hdom : Integrable (fun p : (ℕ → ℝ) × ℝ => f ((kWalk 0 β a p.1 j + β - p.2) / a) / |a|)
      ((iidLaw ν).prod volume) := by
    refine (integrable_prod_iff hfm.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Eventually.of_forall fun g => (hdens (kWalk 0 β a g j + β)).1
    · have e : ∀ g : ℕ → ℝ, ∫ z, ‖f ((kWalk 0 β a g j + β - z) / a) / |a|‖ = 1 := by
        intro g
        have hnn : ∀ z, ‖f ((kWalk 0 β a g j + β - z) / a) / |a|‖ =
            f ((kWalk 0 β a g j + β - z) / a) / |a| := fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hf.nonneg _) (abs_nonneg _))]
        simp_rw [hnn]
        exact (hdens _).2
      simp only [e]
      exact integrable_const _
  refine hdom.mono' (hΦ.mul hfm).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (hf.nonneg _) (abs_nonneg _))]
  calc _ ≤ 1 * (f ((kWalk 0 β a p.1 j + β - p.2) / a) / |a|) :=
        mul_le_mul_of_nonneg_right (hΦb p) (div_nonneg (hf.nonneg _) (abs_nonneg _))
    _ = _ := one_mul _

/-! ## One first-argmax time -/

theorem measurable_indicator_Ico_param {α : Type*} [MeasurableSpace α] {X hi : α → ℝ}
    (hX : Measurable X) (hhi : Measurable hi) :
    Measurable (fun p => (Ico 0 (hi p)).indicator (fun _ => (1 : ℝ)) (X p)) := by
  classical
  have hs : MeasurableSet {p | 0 ≤ X p ∧ X p < hi p} :=
    (measurableSet_le measurable_const hX).inter (measurableSet_lt hX hhi)
  have e : (fun p => (Ico 0 (hi p)).indicator (fun _ => (1 : ℝ)) (X p)) =
      {p | 0 ≤ X p ∧ X p < hi p}.indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases h : 0 ≤ X p ∧ X p < hi p
    · rw [indicator_of_mem (show X p ∈ Ico 0 (hi p) from h),
        indicator_of_mem (show p ∈ {p | 0 ≤ X p ∧ X p < hi p} from h)]
    · rw [indicator_of_notMem (show X p ∉ Ico 0 (hi p) from h),
        indicator_of_notMem (show p ∉ {p | 0 ≤ X p ∧ X p < hi p} from h)]
  rw [e]
  exact measurable_const.indicator hs

/-- The strict prefix band `[0, z)` along the path, jointly in `(g, z)`. -/
theorem measurable_krAlive_Ico (β a : ℝ) (j : ℕ) :
    Measurable fun p : (ℕ → ℝ) × ℝ => krAlive (Ico 0 p.2) β a j 0 p.1 := by
  unfold krAlive
  exact Finset.measurable_prod _ fun i _ => measurable_indicator_Ico_param
    ((measurable_kWalk_right 0 β a i).comp measurable_fst) measurable_snd

theorem measurable_krSurv_top (ν : ProbabilityMeasure ℝ) (β a : ℝ) (m : ℕ) :
    Measurable fun z : ℝ => krSurv (Icc 0 z) (ν : Measure ℝ) β a m z := by
  have h : Measurable fun p : ℝ × (ℕ → ℝ) => krAlive (Icc 0 p.1) β a m p.1 p.2 :=
    measurable_krAlive_band measurable_fst measurable_fst measurable_const measurable_const
      measurable_snd m
  have e : (fun z : ℝ => krSurv (Icc 0 z) (ν : Measure ℝ) β a m z) =
      fun z => ∫ g, krAlive (Icc 0 z) β a m z g ∂(iidLaw ν) :=
    funext fun z => krSurv_eq_integral measurableSet_Icc ν β a m z
  rw [e]
  exact (h.stronglyMeasurable.integral_prod_right' (ν := iidLaw ν)).measurable

theorem krSurv_top_nonneg (ν : ProbabilityMeasure ℝ) (β a : ℝ) (m : ℕ) (z : ℝ) :
    0 ≤ krSurv (Icc 0 z) (ν : Measure ℝ) β a m z := krSurv_nonneg measurableSet_Icc ν β a m z

theorem krSurv_top_le_one (ν : ProbabilityMeasure ℝ) (β a : ℝ) (m : ℕ) (z : ℝ) :
    krSurv (Icc 0 z) (ν : Measure ℝ) β a m z ≤ 1 := krSurv_le_one measurableSet_Icc ν β a m z

open Classical in
/-- The first-argmax indicator splits at the argmax time into a strict prefix band, the level
window, and the suffix survival in `[0, W_k]` from the top. -/
theorem cepsArgmaxInd_eq {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (β a : ℝ) (n j : ℕ) (g : ℕ → ℝ) :
    cepsArgmaxInd z₁ z₂ β a n (j + 1) g =
      krAlive (Ico 0 (kWalk 0 β a g (j + 1))) β a j 0 g *
        (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (j + 1)) *
        krAlive (Icc 0 (kWalk 0 β a g (j + 1))) β a (n - (j + 1)) (kWalk 0 β a g (j + 1))
          (fun i => g (i + (j + 1))) := by
  set W := kWalk 0 β a g (j + 1) with hW
  rw [krAlive_eq_ite, krAlive_eq_ite]
  unfold cepsArgmaxInd
  by_cases h2 : W ∈ Ioc z₁ z₂
  · rw [indicator_of_mem h2, mul_one]
    have hW0 : 0 ≤ W := hz₁.trans h2.1.le
    have hpre : (∀ i < j + 1, kWalk 0 β a g i ∈ Ico 0 W) ↔ ∀ i ≤ j, kWalk 0 β a g i ∈ Ico 0 W :=
      ⟨fun h i hi => h i (by omega), fun h i hi => h i (by omega)⟩
    have hsuf : (∀ i, j + 1 < i → i ≤ n → kWalk 0 β a g i ∈ Icc 0 W) ↔
        ∀ i ≤ n - (j + 1), kWalk W β a (fun i => g (i + (j + 1))) i ∈ Icc 0 W := by
      constructor
      · intro h i hi
        rw [hW, kWalk_shift]
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; rw [Nat.add_zero]; exact ⟨hW0, le_rfl⟩
        · exact h (j + 1 + i) (by omega) (by omega)
      · intro h i hi1 hi2
        have := h (i - (j + 1)) (by omega)
        rw [hW, kWalk_shift, show j + 1 + (i - (j + 1)) = i by omega] at this
        exact this
    by_cases hc1 : ∀ i ≤ j, kWalk 0 β a g i ∈ Ico 0 W
    · by_cases hc3 : ∀ i ≤ n - (j + 1), kWalk W β a (fun i => g (i + (j + 1))) i ∈ Icc 0 W
      · rw [if_pos ⟨hpre.2 hc1, h2, hsuf.2 hc3⟩, if_pos hc1, if_pos hc3]; norm_num
      · rw [if_neg (fun h => hc3 (hsuf.1 h.2.2)), if_pos hc1, if_neg hc3]; norm_num
    · rw [if_neg (fun h => hc1 (hpre.1 h.1)), if_neg hc1]; norm_num
  · rw [indicator_of_notMem h2, if_neg (fun h => h2 h.2.1)]
    norm_num

open Classical in
/-- Off finitely many `z`, the strict and closed prefix bands agree. -/
theorem krAlive_Ico_ae_eq (β a : ℝ) (j : ℕ) (g : ℕ → ℝ) :
    ∀ᵐ z ∂(volume : Measure ℝ), krAlive (Ico 0 z) β a j 0 g = krAlive (Icc 0 z) β a j 0 g := by
  have hfin : (((Finset.range (j + 1)).image fun i => kWalk 0 β a g i : Finset ℝ) : Set ℝ).Finite :=
    Finset.finite_toSet _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hfin.measure_zero volume)] with z hz
  rw [krAlive_eq_ite, krAlive_eq_ite]
  have hiff : (∀ i ≤ j, kWalk 0 β a g i ∈ Ico 0 z) ↔ ∀ i ≤ j, kWalk 0 β a g i ∈ Icc 0 z := by
    constructor
    · intro h i hi; exact ⟨(h i hi).1, (h i hi).2.le⟩
    · intro h i hi
      refine ⟨(h i hi).1, lt_of_le_of_ne (h i hi).2 fun heq => hz ?_⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨i, Finset.mem_range.2 (by omega), heq⟩)
  by_cases h : ∀ i ≤ j, kWalk 0 β a g i ∈ Icc 0 z
  · rw [if_pos (hiff.2 h), if_pos h]
  · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]

/-- **The integral of one first-argmax time**: the endpoint `z = W_{j+1}` is integrated against the
killed density `k_{j+1}(0, z)`, times the survival from the top. -/
theorem CepsGapDensity.integral_cepsArgmaxInd (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (n j : ℕ) :
    ∫ g, cepsArgmaxInd z₁ z₂ β a n (j + 1) g ∂(iidLaw ν) =
      ∫ z in Ioc z₁ z₂, krDens (Icc 0 z) ν f β a (j + 1) 0 z *
        krSurv (Icc 0 z) (ν : Measure ℝ) β a (n - (j + 1)) z := by
  set m := n - (j + 1)
  set S : ℝ → ℝ := fun z => krSurv (Icc 0 z) (ν : Measure ℝ) β a m z with hS
  have hSm : Measurable S := measurable_krSurv_top ν β a m
  have hSb : ∀ z, 0 ≤ S z ∧ S z ≤ 1 := fun z => ⟨krSurv_top_nonneg ν β a m z,
    krSurv_top_le_one ν β a m z⟩
  have hIoc : Measurable fun z : ℝ => (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) z :=
    measurable_const.indicator measurableSet_Ioc
  have hind01 : ∀ z, 0 ≤ (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) z ∧
      (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) z ≤ 1 := fun z => by
    by_cases h : z ∈ Ioc z₁ z₂ <;> simp [h]
  -- step 1: Markov split at `j + 1`
  have hsplit : ∫ g, cepsArgmaxInd z₁ z₂ β a n (j + 1) g ∂(iidLaw ν) =
      ∫ g, (krAlive (Ico 0 (kWalk 0 β a g (j + 1))) β a j 0 g *
        (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (j + 1))) *
        S (kWalk 0 β a g (j + 1)) ∂(iidLaw ν) := by
    simp_rw [cepsArgmaxInd_eq hz₁ β a n j]
    have hF : Measurable fun g : ℕ → ℝ => krAlive (Ico 0 (kWalk 0 β a g (j + 1))) β a j 0 g *
        (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (j + 1)) := by
      have h1 := (measurable_krAlive_Ico β a j).comp
        (measurable_id.prodMk (measurable_kWalk_right 0 β a (j + 1)))
      have h2 := hIoc.comp (measurable_kWalk_right 0 β a (j + 1))
      exact h1.mul h2
    have hG : Measurable (Function.uncurry fun (x : ℝ) (h : ℕ → ℝ) =>
        krAlive (Icc 0 x) β a m x h) :=
      measurable_krAlive_band measurable_fst measurable_fst measurable_const measurable_const
        measurable_snd m
    rw [integral_mul_shift_dep_real ν (j + 1) hF ?_ (measurable_kWalk_right 0 β a (j + 1))
      (fun g g' h => surv_kWalk_congr h) hG ?_ ?_]
    · refine integral_congr_ae (Eventually.of_forall fun g => ?_)
      simp only [hS]
      rw [krSurv_eq_integral measurableSet_Icc]
    · intro g g' h
      rw [surv_kWalk_congr h, krAlive_congr fun i hi => h i (by omega)]
    · intro g
      rw [abs_of_nonneg (mul_nonneg (krAlive_nonneg _ _ _) (hind01 _).1)]
      calc _ ≤ 1 * 1 := mul_le_mul (krAlive_le_one _ _ _) (hind01 _).2 (hind01 _).1 zero_le_one
        _ = 1 := one_mul 1
    · intro x h
      rw [abs_of_nonneg (krAlive_nonneg _ _ _)]
      exact krAlive_le_one _ _ _
  -- step 2: the last prefix step
  set Θ : (ℕ → ℝ) → ℝ → ℝ := fun g z => krAlive (Ico 0 z) β a j 0 g *
    (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) z * S z with hΘ
  have hΘm : Measurable (Function.uncurry Θ) :=
    ((measurable_krAlive_Ico β a j).mul (hIoc.comp measurable_snd)).mul (hSm.comp measurable_snd)
  have hΘb : ∀ g z, |Θ g z| ≤ 1 := fun g z => by
    simp only [hΘ]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (krAlive_nonneg _ _ _) (hind01 z).1) (hSb z).1)]
    calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul (krAlive_le_one _ _ _) (hind01 z).2
          (hind01 z).1 zero_le_one) (hSb z).2 (hSb z).1 (by norm_num)
      _ = 1 := by norm_num
  have hΘd : ∀ g z x, Θ (Function.update g j x) z = Θ g z := fun g z x => by
    simp only [hΘ]
    rw [krAlive_congr fun i hi => Function.update_of_ne (by omega) _ _]
  rw [hsplit, show (fun g => (krAlive (Ico 0 (kWalk 0 β a g (j + 1))) β a j 0 g *
      (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (j + 1))) *
      S (kWalk 0 β a g (j + 1))) = fun g => Θ g (kWalk 0 β a g (j + 1)) from rfl,
    hf.integral_lastStep ha β j hΘm hΘb hΘd]
  -- step 3: strict to closed prefix band, then swap
  set Θ' : (ℕ → ℝ) × ℝ → ℝ := fun p => krAlive (Icc 0 p.2) β a j 0 p.1 *
    (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) p.2 * S p.2 with hΘ'
  have hΘ'm : Measurable Θ' :=
    ((measurable_krAlive_band measurable_snd measurable_const measurable_const measurable_const
      measurable_fst j).mul (hIoc.comp measurable_snd)).mul (hSm.comp measurable_snd)
  have hΘ'b : ∀ p, |Θ' p| ≤ 1 := fun p => by
    simp only [hΘ']
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (krAlive_nonneg _ _ _) (hind01 _).1) (hSb _).1)]
    calc _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul (krAlive_le_one _ _ _) (hind01 _).2
          (hind01 _).1 zero_le_one) (hSb _).2 (hSb _).1 (by norm_num)
      _ = 1 := by norm_num
  have hinner : ∀ g : ℕ → ℝ, ∫ z, Θ g z * (f ((kWalk 0 β a g j + β - z) / a) / |a|) =
      ∫ z, Θ' (g, z) * (f ((kWalk 0 β a g j + β - z) / a) / |a|) := fun g => by
    refine integral_congr_ae ?_
    filter_upwards [krAlive_Ico_ae_eq β a j g] with z hz
    simp only [hΘ, hΘ', hz]
  simp_rw [hinner]
  rw [integral_integral_swap (hf.integrable_density_prod ha β j hΘ'm hΘ'b),
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hΘ']
  by_cases hz : z ∈ Ioc z₁ z₂
  · rw [indicator_of_mem hz, indicator_of_mem hz]
    simp_rw [mul_one]
    have hz0 : z ∈ Icc 0 z := ⟨hz₁.trans hz.1.le, le_rfl⟩
    rw [krDens_succ, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only
    have hk := krAlive_mul_indicator (J := Icc 0 z) (β := β) (a := a) j 0 g
    unfold krKer
    rw [indicator_of_mem hz0]
    linear_combination (-(S z * (f ((kWalk 0 β a g j + β - z) / a) / |a|))) * hk
  · rw [indicator_of_notMem hz, indicator_of_notMem hz]
    simp

/-- **The Hadamard identity for one time `n`.** -/
theorem CepsGapDensity.krSurv_bottom_sub (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) (n : ℕ) :
    krSurv (Icc 0 z₂) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 z₁) (ν : Measure ℝ) β a n 0 =
      ∑ j ∈ Finset.range n, ∫ z in Ioc z₁ z₂, krDens (Icc 0 z) ν f β a (j + 1) 0 z *
        krSurv (Icc 0 z) (ν : Measure ℝ) β a (n - (j + 1)) z := by
  have hint : ∀ z, Integrable (fun g => krAlive (Icc 0 z) β a n 0 g) (iidLaw ν) := fun z =>
    kr_integrable_of_bdd (measurable_krAlive_right measurableSet_Icc β a n 0) (abs_krAlive_le_one n 0)
  have hmeasA : ∀ j, Measurable (cepsArgmaxInd z₁ z₂ β a n (j + 1)) := by
    intro j
    have e := funext (cepsArgmaxInd_eq (z₂ := z₂) hz₁ β a n j)
    rw [e]
    have h1 := (measurable_krAlive_Ico β a j).comp
      (measurable_id.prodMk (measurable_kWalk_right 0 β a (j + 1)))
    have h2 : Measurable fun g : ℕ → ℝ =>
        (Ioc z₁ z₂).indicator (fun _ => (1 : ℝ)) (kWalk 0 β a g (j + 1)) :=
      (measurable_const.indicator measurableSet_Ioc).comp (measurable_kWalk_right 0 β a (j + 1))
    have h3 := measurable_krAlive_band (α := (ℕ → ℝ)) (l := fun g => kWalk 0 β a g (j + 1))
      (y := fun g => kWalk 0 β a g (j + 1)) (β := fun _ => β) (a := fun _ => a)
      (G := fun g => fun i => g (i + (j + 1))) (measurable_kWalk_right 0 β a (j + 1))
      (measurable_kWalk_right 0 β a (j + 1)) measurable_const measurable_const
      (measurable_pi_lambda _ fun i => measurable_pi_apply (i + (j + 1))) (n - (j + 1))
    exact (h1.mul h2).mul h3
  have hbA : ∀ k g, |cepsArgmaxInd z₁ z₂ β a n k g| ≤ 1 := fun k g => by
    unfold cepsArgmaxInd; split_ifs <;> simp
  rw [krSurv_eq_integral measurableSet_Icc, krSurv_eq_integral measurableSet_Icc,
    ← integral_sub (hint z₂) (hint z₁),
    integral_congr_ae (Eventually.of_forall fun g => hadamard_pathwise hz₁ hz β a g n),
    integral_finsetSum _ fun j _ => kr_integrable_of_bdd (hmeasA j) (hbA (j + 1))]
  exact Finset.sum_congr rfl fun j _ => hf.integral_cepsArgmaxInd ha β hz₁ n j

/-! ## Summing over time -/

/-- `h₋(z) = ∑ₙ e^{-qn} P_0(W_0, …, W_n ∈ [0, z])`. -/
def cepsBottomSurv (ν : ProbabilityMeasure ℝ) (β a : ℝ) (q : ℂ) (z : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * n) * (krSurv (Icc 0 z) (ν : Measure ℝ) β a n 0 : ℂ)

/-- `h₊(z) = ∑ₙ e^{-qn} P_z(W_0, …, W_n ∈ [0, z])`. -/
def cepsTopSurv (ν : ProbabilityMeasure ℝ) (β a : ℝ) (q : ℂ) (z : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * n) * (krSurv (Icc 0 z) (ν : Measure ℝ) β a n z : ℂ)

/-- `U(z) = ∑_{n ≥ 1} e^{-qn} k_n(0, z)`. -/
def cepsBridgeSeries (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (β a : ℝ) (q : ℂ) (z : ℝ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-q * ((n : ℂ) + 1)) * (krDens (Icc 0 z) ν f β a (n + 1) 0 z : ℂ)

theorem measurable_krDens_top (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} (hf : Measurable f)
    (β a : ℝ) (j : ℕ) : Measurable fun z : ℝ => krDens (Icc 0 z) ν f β a (j + 1) 0 z := by
  have hW : Measurable fun p : ℝ × (ℕ → ℝ) => kWalk 0 β a p.2 j :=
    (measurable_kWalk_right 0 β a j).comp measurable_snd
  have h : Measurable fun p : ℝ × (ℕ → ℝ) =>
      krAlive (Icc 0 p.1) β a j 0 p.2 * krKer (Icc 0 p.1) f β a (kWalk 0 β a p.2 j) p.1 := by
    refine (measurable_krAlive_band measurable_fst measurable_const measurable_const
      measurable_const measurable_snd j).mul ?_
    unfold krKer
    exact ((measurable_indicator_Icc_param hW measurable_const measurable_fst).mul
      (measurable_indicator_Icc_param measurable_fst measurable_const measurable_fst)).mul
      ((hf.comp (((hW.add_const β).sub measurable_fst).div_const a)).div_const _)
  have e : (fun z : ℝ => krDens (Icc 0 z) ν f β a (j + 1) 0 z) = fun z =>
      ∫ g, krAlive (Icc 0 z) β a j 0 g * krKer (Icc 0 z) f β a (kWalk 0 β a g j) z ∂(iidLaw ν) :=
    funext fun z => krDens_succ ν j 0 z
  rw [e]
  exact (h.stronglyMeasurable.integral_prod_right' (ν := iidLaw ν)).measurable

/-- The real layer `∑_{k + m = K} k_{k+1}(0, z) P_z(survive m)`. -/
def cepsHadamardLayer (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (β a : ℝ) (K : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ Finset.antidiagonal K, krDens (Icc 0 z) ν f β a (p.1 + 1) 0 z *
    krSurv (Icc 0 z) (ν : Measure ℝ) β a p.2 z

theorem CepsGapDensity.cepsHadamardLayer_nonneg (hf : CepsGapDensity ν f D) (β a : ℝ) (K : ℕ)
    (z : ℝ) : 0 ≤ cepsHadamardLayer ν f β a K z :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (krDens_nonneg ν hf.nonneg _ _ _)
    (krSurv_top_nonneg ν β a _ z)

theorem CepsGapDensity.integrableOn_krDens_mul (hf : CepsGapDensity ν f D) (a β : ℝ) (j m : ℕ)
    (z₁ z₂ : ℝ) :
    IntegrableOn (fun z => krDens (Icc 0 z) ν f β a (j + 1) 0 z *
      krSurv (Icc 0 z) (ν : Measure ℝ) β a m z) (Ioc z₁ z₂) := by
  refine Measure.integrableOn_of_bounded (M := D / |a|) measure_Ioc_lt_top.ne
    ((measurable_krDens_top ν hf.measurable β a j).mul
      (measurable_krSurv_top ν β a m)).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (krDens_nonneg ν hf.nonneg _ _ _)
    (krSurv_top_nonneg ν β a m z))]
  calc _ ≤ D / |a| * 1 := mul_le_mul (krDens_le_div ν hf.nonneg hf.le _ _ _)
        (krSurv_top_le_one ν β a m z) (krSurv_top_nonneg ν β a m z)
        (div_nonneg hf.nonneg_D (abs_nonneg _))
    _ = _ := mul_one _

theorem CepsGapDensity.integral_cepsHadamardLayer (hf : CepsGapDensity ν f D) {a : ℝ}
    (ha : a ≠ 0) (β : ℝ) {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) (K : ℕ) :
    IntegrableOn (cepsHadamardLayer ν f β a K) (Ioc z₁ z₂) ∧
      ∫ z in Ioc z₁ z₂, cepsHadamardLayer ν f β a K z =
        krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 -
          krSurv (Icc 0 z₁) (ν : Measure ℝ) β a (K + 1) 0 := by
  have hint : ∀ p ∈ Finset.antidiagonal K, IntegrableOn (fun z => krDens (Icc 0 z) ν f β a
      (p.1 + 1) 0 z * krSurv (Icc 0 z) (ν : Measure ℝ) β a p.2 z) (Ioc z₁ z₂) :=
    fun p _ => hf.integrableOn_krDens_mul a β p.1 p.2 z₁ z₂
  refine ⟨integrable_finsetSum _ hint, ?_⟩
  unfold cepsHadamardLayer
  rw [integral_finsetSum _ hint, hf.krSurv_bottom_sub ha β hz₁ hz (K + 1),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjK := Finset.mem_range.1 hj
  rw [show K + 1 - (j + 1) = K - j by omega]

/-- **S-2 (c): the width Hadamard identity**, integrated form:
`h₋(z₂) - h₋(z₁) = ∫_{(z₁, z₂]} U h₊`, with `U h₊` integrable on `(z₁, z₂]`. -/
theorem CepsGapDensity.cepsBottomSurv_sub (hf : CepsGapDensity ν f D) {a : ℝ} (ha : a ≠ 0)
    (β : ℝ) {q : ℂ} (hq : 0 ≤ q.re) {z₁ z₂ : ℝ} (hz₁ : 0 ≤ z₁) (hz : z₁ ≤ z₂) :
    IntegrableOn (fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) (Ioc z₁ z₂) ∧
      cepsBottomSurv ν β a q z₂ - cepsBottomSurv ν β a q z₁ =
        ∫ z in Ioc z₁ z₂, cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z := by
  -- the complex layers
  set L : ℕ → ℝ → ℂ := fun K z => Complex.exp (-q * ((K : ℂ) + 1)) *
    (cepsHadamardLayer ν f β a K z : ℂ) with hL
  have hLnorm : ∀ K z, ‖L K z‖ ≤ cepsHadamardLayer ν f β a K z := fun K z => by
    rw [hL, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hf.cepsHadamardLayer_nonneg β a K z)]
    calc _ ≤ 1 * cepsHadamardLayer ν f β a K z := mul_le_mul_of_nonneg_right
          (norm_cexp_neg_mul_succ_le_one hq K) (hf.cepsHadamardLayer_nonneg β a K z)
      _ = _ := one_mul _
  -- pointwise Cauchy product
  have hpt : ∀ z, 0 ≤ z → HasSum (fun K => L K z)
      (cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) := by
    intro z hz0
    obtain ⟨C, r, hC, hr0, hr1, hb⟩ := hf.krSurv_geometric z β ha
    set u : ℕ → ℂ := fun k => Complex.exp (-q * ((k : ℂ) + 1)) *
      (krDens (Icc 0 z) ν f β a (k + 1) 0 z : ℂ)
    set v : ℕ → ℂ := fun m => Complex.exp (-q * m) * (krSurv (Icc 0 z) (ν : Measure ℝ) β a m z : ℂ)
    have hus : Summable fun k => ‖u k‖ := by
      refine ((summable_geometric_of_lt_one hr0 hr1).mul_left (D / |a| * C)).of_nonneg_of_le
        (fun k => norm_nonneg _) fun k => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krDens_nonneg ν hf.nonneg _ _ _)]
      calc _ ≤ 1 * (D / |a| * (C * r ^ k)) := mul_le_mul (norm_cexp_neg_mul_succ_le_one hq k)
            ((krDens_le_div_mul_krSurv ν measurableSet_Icc hf.measurable hf.nonneg hf.le k 0 z).trans
              (mul_le_mul_of_nonneg_left (hb k 0) (div_nonneg hf.nonneg_D (abs_nonneg _))))
            (krDens_nonneg ν hf.nonneg _ _ _) zero_le_one
        _ = D / |a| * C * r ^ k := by ring
    have hvs : Summable fun m => ‖v m‖ := by
      refine ((summable_geometric_of_lt_one hr0 hr1).mul_left C).of_nonneg_of_le
        (fun m => norm_nonneg _) fun m => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (krSurv_top_nonneg ν β a m z)]
      calc _ ≤ 1 * (C * r ^ m) := mul_le_mul (norm_cexp_neg_mul_nat_le_one hq m) (hb m z)
            (krSurv_top_nonneg ν β a m z) zero_le_one
        _ = _ := one_mul _
    have hEs := (summable_norm_sum_mul_antidiagonal_of_summable_norm hus hvs).of_norm
    have hcp := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hus hvs
    have hlayer : ∀ K, ∑ p ∈ Finset.antidiagonal K, u p.1 * v p.2 = L K z := by
      intro K
      show _ = Complex.exp (-q * ((K : ℂ) + 1)) * ((cepsHadamardLayer ν f β a K z : ℝ) : ℂ)
      unfold cepsHadamardLayer
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hpK := Finset.mem_antidiagonal.1 hp
      have hexp : Complex.exp (-q * ((K : ℂ) + 1)) = Complex.exp (-q * ((p.1 : ℂ) + 1)) *
          Complex.exp (-q * (p.2 : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; rw [← hpK]; push_cast; ring
      rw [hexp]
      push_cast
      ring
    have e : cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z = (∑' k, u k) * ∑' m, v m := rfl
    rw [e, hcp]
    simp only [hlayer] at hEs ⊢
    exact hEs.hasSum
  -- integrability and the integral of each layer
  have hlay := fun K => hf.integral_cepsHadamardLayer ha β hz₁ hz K
  have hLint : ∀ K, IntegrableOn (L K) (Ioc z₁ z₂) := fun K =>
    ((hlay K).1.ofReal).const_mul _
  -- the bottom series in layers
  obtain ⟨C₂, r₂, hC₂, hr₂0, hr₂1, hb₂⟩ := hf.krSurv_geometric z₂ β ha
  have hnn : ∀ K, 0 ≤ krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 -
      krSurv (Icc 0 z₁) (ν : Measure ℝ) β a (K + 1) 0 := fun K => by
    rw [← (hlay K).2]
    exact setIntegral_nonneg measurableSet_Ioc fun z _ => hf.cepsHadamardLayer_nonneg β a K z
  have hRsum : Summable fun K => krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 -
      krSurv (Icc 0 z₁) (ν : Measure ℝ) β a (K + 1) 0 := by
    refine Summable.of_nonneg_of_le hnn (fun K => ?_)
      ((summable_geometric_of_lt_one hr₂0 hr₂1).mul_left C₂)
    have := krSurv_nonneg measurableSet_Icc ν β a (K + 1) 0 (J := Icc 0 z₁)
    calc _ ≤ krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 := by linarith
      _ ≤ C₂ * r₂ ^ (K + 1) := hb₂ (K + 1) 0
      _ ≤ C₂ * r₂ ^ K := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr₂0 hr₂1.le
          (Nat.le_succ K)) hC₂
  have hlin : ∑' K, ∫⁻ z in Ioc z₁ z₂, ‖L K z‖ₑ ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := ∑' K, ENNReal.ofReal
      (krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 - krSurv (Icc 0 z₁) (ν : Measure ℝ) β a (K + 1) 0))
      ?_ (ENNReal.tsum_le_tsum fun K => ?_)
    · rw [← ENNReal.ofReal_tsum_of_nonneg hnn hRsum]
      exact ENNReal.ofReal_ne_top
    · rw [← (hlay K).2, ofReal_integral_eq_lintegral_ofReal (hlay K).1
        (Eventually.of_forall fun z => hf.cepsHadamardLayer_nonneg β a K z)]
      refine lintegral_mono fun z => ?_
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hLnorm K z)
  have hexch : ∫ z in Ioc z₁ z₂, (∑' K, L K z) = ∑' K, ∫ z in Ioc z₁ z₂, L K z :=
    integral_tsum (fun K => (hLint K).aestronglyMeasurable) hlin
  have hpt' : ∀ z ∈ Ioc z₁ z₂, ∑' K, L K z =
      cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z := fun z hz' =>
    (hpt z (hz₁.trans hz'.1.le)).tsum_eq
  -- integrability of the product
  refine ⟨?_, ?_⟩
  · have hm : AEStronglyMeasurable (fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z)
        (volume.restrict (Ioc z₁ z₂)) := by
      refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N z =>
        ∑ K ∈ Finset.range N, L K z) (fun N => (integrable_finsetSum _ fun K _ =>
          hLint K).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz'
      exact (hpt z (hz₁.trans hz'.1.le)).tendsto_sum_nat
    refine ⟨hm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hlin)
    rw [← lintegral_tsum fun K => (hLint K).aestronglyMeasurable.enorm]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz'
    rw [← hpt' z hz']
    exact enorm_tsum_le_tsum_enorm
  · have hdiff : cepsBottomSurv ν β a q z₂ - cepsBottomSurv ν β a q z₁ =
        ∑' n : ℕ, Complex.exp (-q * n) * ((krSurv (Icc 0 z₂) (ν : Measure ℝ) β a n 0 -
          krSurv (Icc 0 z₁) (ν : Measure ℝ) β a n 0 : ℝ) : ℂ) := by
      obtain ⟨C₁, r₁, hC₁, hr₁0, hr₁1, hb₁⟩ := hf.krSurv_geometric z₁ β ha
      have hs : ∀ (z C r : ℝ), 0 ≤ C → 0 ≤ r → r < 1 →
          (∀ n y, krSurv (Icc 0 z) (ν : Measure ℝ) β a n y ≤ C * r ^ n) →
          Summable fun n : ℕ => Complex.exp (-q * n) * (krSurv (Icc 0 z) (ν : Measure ℝ) β a n 0 : ℂ) := by
        intro z C r hC hr0 hr1 hb
        refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hr0 hr1).mul_left C)
          fun n => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (krSurv_nonneg measurableSet_Icc ν β a n 0)]
        calc _ ≤ 1 * (C * r ^ n) := mul_le_mul (norm_cexp_neg_mul_nat_le_one hq n) (hb n 0)
              (krSurv_nonneg measurableSet_Icc ν β a n 0) zero_le_one
          _ = _ := one_mul _
      unfold cepsBottomSurv
      rw [← (hs z₂ C₂ r₂ hC₂ hr₂0 hr₂1 hb₂).tsum_sub (hs z₁ C₁ r₁ hC₁ hr₁0 hr₁1 hb₁)]
      congr 1
      funext n
      push_cast
      ring
    have hsum2 : Summable fun n : ℕ => Complex.exp (-q * n) *
        ((krSurv (Icc 0 z₂) (ν : Measure ℝ) β a n 0 - krSurv (Icc 0 z₁) (ν : Measure ℝ) β a n 0 : ℝ) : ℂ) := by
      refine (summable_nat_add_iff 1).1 ?_
      refine Summable.of_norm_bounded hRsum fun K => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [abs_of_nonneg (hnn K)]
      calc _ ≤ 1 * (krSurv (Icc 0 z₂) (ν : Measure ℝ) β a (K + 1) 0 -
            krSurv (Icc 0 z₁) (ν : Measure ℝ) β a (K + 1) 0) :=
            mul_le_mul_of_nonneg_right (by simpa using norm_cexp_neg_mul_succ_le_one hq K) (hnn K)
        _ = _ := one_mul _
    rw [hdiff, tsum_eq_zero_add' ((summable_nat_add_iff 1).2 hsum2)]
    have h0 : Complex.exp (-q * ((0 : ℕ) : ℂ)) * ((krSurv (Icc 0 z₂) (ν : Measure ℝ) β a 0 0 -
        krSurv (Icc 0 z₁) (ν : Measure ℝ) β a 0 0 : ℝ) : ℂ) = 0 := by
      have e1 : ∀ z : ℝ, 0 ≤ z → krSurv (Icc 0 z) (ν : Measure ℝ) β a 0 0 = 1 := fun z hz0 => by
        rw [krSurv_eq_integral measurableSet_Icc]
        simp [krAlive_zero, indicator_of_mem (show (0 : ℝ) ∈ Icc 0 z from ⟨le_rfl, hz0⟩)]
      rw [e1 z₂ (hz₁.trans hz), e1 z₁ hz₁]
      simp
    rw [h0, zero_add, ← setIntegral_congr_fun measurableSet_Ioc hpt', hexch]
    congr 1
    funext K
    rw [hL, integral_const_mul, integral_complex_ofReal, (hlay K).2]
    push_cast
    ring_nf

/-- **S-2 (c), differential form**: `h₋` is differentiable with derivative `U h₊` at every `z > 0`
where `U h₊` is continuous. -/
theorem CepsGapDensity.cepsBottomSurv_hasDerivAt (hf : CepsGapDensity ν f D) {a : ℝ}
    (ha : a ≠ 0) (β : ℝ) {q : ℂ} (hq : 0 ≤ q.re) {z : ℝ} (hz : 0 < z)
    (hc : ContinuousAt (fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) z) :
    HasDerivAt (cepsBottomSurv ν β a q)
      (cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z) z := by
  set F := fun z => cepsBridgeSeries ν f β a q z * cepsTopSurv ν β a q z with hF
  have hz2 : 0 ≤ z / 2 := by linarith
  have hint : IntegrableOn F (Ioc (z / 2) (2 * z)) :=
    (hf.cepsBottomSurv_sub ha β hq hz2 (by linarith)).1
  have hII : IntervalIntegrable F volume (z / 2) z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).2
      (hint.mono_set (Ioc_subset_Ioc le_rfl (by linarith)))
  have hmeas : StronglyMeasurableAtFilter F (nhds z) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem (s := Ioc (z / 2) (2 * z))
      (Integrable.aestronglyMeasurable hint)
      (Ioc_mem_nhds (show z / 2 < z by linarith) (show z < 2 * z by linarith))
  have hd := intervalIntegral.integral_hasDerivAt_right hII hmeas hc
  have heq : (fun u => cepsBottomSurv ν β a q (z / 2) + ∫ x in z / 2..u, F x) =ᶠ[nhds z]
      cepsBottomSurv ν β a q := by
    filter_upwards [Ioi_mem_nhds (show z / 2 < z by linarith)] with u hu
    rw [intervalIntegral.integral_of_le (le_of_lt hu),
      ← (hf.cepsBottomSurv_sub ha β hq hz2 (le_of_lt hu)).2]
    ring
  exact (hd.const_add _).congr_of_eventuallyEq heq.symm

/-! ## The blueprint objects -/

/-- The top-started survival series of the `Y_μ`-walk is the strip entrance `H_0` of theorem (E). -/
theorem cepsTopSurv_eq_stripEntrance (ν : ProbabilityMeasure ℝ) (μ : ℝ) (q : ℂ) (l : ℝ) :
    cepsTopSurv ν (1 + μ) 1 q l = cepsStripEntrance ν 0 μ q l := by
  unfold cepsTopSurv cepsStripEntrance
  congr 1
  funext n
  rw [cepsStripTerm_zero, ← krSurv_reflect ν l (1 + μ) 1 n l, sub_self]

theorem cepsBridgeSeries_eq_bridge (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ) (μ : ℝ) (q : ℂ)
    (l : ℝ) : cepsBridgeSeries ν f (1 + μ) 1 q l = cepsBridge ν f μ q l := rfl

/-- **S-2 (c) in the blueprint's notation** (L13): for the `Y_μ`-walk (step `1 + μ - X`),
`h₋(l₂) - h₋(l₁) = ∫_{(l₁, l₂]} U h₊` with `U = cepsBridge`, `h₊ = H_0 = cepsStripEntrance ν 0`. -/
theorem CepsGapDensity.cepsBottomSurv_sub_bridge (hf : CepsGapDensity ν f D) (μ : ℝ) {q : ℂ}
    (hq : 0 ≤ q.re) {l₁ l₂ : ℝ} (hl₁ : 0 ≤ l₁) (hl : l₁ ≤ l₂) :
    cepsBottomSurv ν (1 + μ) 1 q l₂ - cepsBottomSurv ν (1 + μ) 1 q l₁ =
      ∫ l in Ioc l₁ l₂, cepsBridge ν f μ q l * cepsStripEntrance ν 0 μ q l := by
  rw [(hf.cepsBottomSurv_sub one_ne_zero (1 + μ) hq hl₁ hl).2]
  refine setIntegral_congr_fun measurableSet_Ioc fun l _ => ?_
  rw [cepsBridgeSeries_eq_bridge, cepsTopSurv_eq_stripEntrance]

end

end PGM
