import PLAStochastic.Index.Model.IIDGaps
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Quantitative threshold margins (`proofK_margin_core.tex`)

* `prefixAffineFeasible_iff_certZ` (`marg:thm:certificate`): for keys strictly increasing on
  `0, …, n` and `e ≥ 0`, the first `n + 1` keys are `e`-feasible iff every active
  certificate `Z_{I,J} = (r_I X_J - r_J X_I) / (2 (X_I + X_J))` is at most `e`
  (feasibility ⇔ a common slope in all intervals `[(r - 2e)/X, (r + 2e)/X]`, 1-D Helly).
* `LocalGapLaw P g μ K`: iid a.s. positive gaps with mean `μ > 0` and
  `P (g 0 ∈ A) ≤ (K / μ) |A|`.  `LocalGapLaw.gsum_local_bound`: every nonempty sum of
  distinct gaps has the same bound.  `LocalGapLaw.certZ_Icc_le`
  (`marg:thm:certificate-density`): for the partial-sum walk and distinct index pairs,
  `P (Z_{I,J} ∈ [z, z + h]) ≤ 32 K h`.  No densities are used: we condition on the
  independent remaining sums (`measure_pair_le_lintegral`), use that `Z` is a monotone function
  of the varied sum with an explicitly bounded preimage interval (`measure_certForm_le`), and
  split `[z, z + h]` according to which of the two bounds of the TeX applies
  (`measure_Icc_split`).
* `LocalGapLaw.fixed_margin` (`marg:eq:fixed-margin`): for `0 < u < a`,
  `P ((a+u)`-feasible `∧ ¬ (a-u)`-feasible for `n + 1` keys`) ≤ 64 K n^4 u`.
* `LocalGapLaw.stopped_margin`, `LocalGapLaw.stopped_margin_segLen` (`marg:cor:base-margin`):
  under the tail `P (T > R) ≤ C₀ exp (-c₀ R / eps^2)` (`R ≥ 1`), for `eps ≥ 1` and
  `0 < u ≤ 1/2`, a near-tie at the stop has probability at most
  `64 (1/c₀ + 2)^5 K eps^10 u (1 + log (1/u))^5 + C₀ u`.
* `poissonisation_bound` (`marg:lem:poissonisation`): under the Gamma kernel,
  `P (g ∈ A) ≤ (sup_m P (N = m)) |A|`; `localGapLaw_of_gammaKernel` and `hier_margin`
  (`marg:cor:hier-margin`) combine it with the stopped margin.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace PGM

/-! ## Exact active certificates -/

/-- The active certificate `Z_{I,J}` of the pairs `I = (j₁, i₁)` and `J = (j₂, i₂)`:
`(r_I X_J - r_J X_I) / (2 (X_I + X_J))` with `r = i - j` and `X = x i - x j`. -/
def certZ (x : ℕ → ℝ) (j₁ i₁ j₂ i₂ : ℕ) : ℝ :=
  (((i₁ : ℝ) - j₁) * (x i₂ - x j₂) - ((i₂ : ℝ) - j₂) * (x i₁ - x j₁)) /
    (2 * ((x i₁ - x j₁) + (x i₂ - x j₂)))

theorem certZ_self (x : ℕ → ℝ) (j i : ℕ) : certZ x j i j i = 0 := by
  simp [certZ]

theorem certZ_swap (x : ℕ → ℝ) (j₁ i₁ j₂ i₂ : ℕ) :
    certZ x j₂ i₂ j₁ i₁ = -certZ x j₁ i₁ j₂ i₂ := by
  unfold certZ
  rw [← neg_div, add_comm (x i₂ - x j₂)]
  ring_nf

/-- For positive increments, `Z_{I,J} ≤ e` says that the lower end of the slope interval of
`I` is below the upper end of the slope interval of `J`. -/
theorem certZ_le_iff {x : ℕ → ℝ} {j₁ i₁ j₂ i₂ : ℕ} {e : ℝ} (h₁ : 0 < x i₁ - x j₁)
    (h₂ : 0 < x i₂ - x j₂) :
    certZ x j₁ i₁ j₂ i₂ ≤ e ↔
      ((i₁ : ℝ) - j₁ - 2 * e) / (x i₁ - x j₁) ≤ ((i₂ : ℝ) - j₂ + 2 * e) / (x i₂ - x j₂) := by
  unfold certZ
  rw [div_le_iff₀ (by positivity), div_le_div_iff₀ h₁ h₂]
  constructor <;> intro h <;> linarith

/-- One-dimensional Helly: finitely many intervals `[L p, U p]` that pairwise intersect have a
common point. -/
theorem exists_common_point {ι : Type*} (S : Finset ι) (L U : ι → ℝ)
    (h : ∀ p ∈ S, ∀ q ∈ S, L p ≤ U q) : ∃ a : ℝ, ∀ p ∈ S, L p ≤ a ∧ a ≤ U p := by
  rcases S.eq_empty_or_nonempty with hS | hS
  · exact ⟨0, fun p hp => by simp [hS] at hp⟩
  · obtain ⟨p₀, hp₀, hmax⟩ := S.exists_max_image L hS
    exact ⟨L p₀, fun p hp => ⟨hmax p hp, h p₀ hp₀ p hp⟩⟩

/-- **Exact active-certificate formula** (`marg:thm:certificate`). -/
theorem prefixAffineFeasible_iff_certZ {x : ℕ → ℝ} {n : ℕ} {e : ℝ}
    (hx : ∀ j i, j < i → i ≤ n → x j < x i) (he : 0 ≤ e) :
    prefixAffineFeasible e x (n + 1) ↔
      ∀ i₁ j₁ i₂ j₂, j₁ < i₁ → i₁ ≤ n → j₂ < i₂ → i₂ ≤ n → certZ x j₁ i₁ j₂ i₂ ≤ e := by
  constructor
  · rintro ⟨a, b, hab⟩ i₁ j₁ i₂ j₂ hji₁ hi₁ hji₂ hi₂
    have hX₁ := sub_pos.mpr (hx j₁ i₁ hji₁ hi₁)
    have hX₂ := sub_pos.mpr (hx j₂ i₂ hji₂ hi₂)
    rw [certZ_le_iff hX₁ hX₂]
    have e₁ := abs_le.mp (hab i₁ (by omega))
    have e₁' := abs_le.mp (hab j₁ (by omega))
    have e₂ := abs_le.mp (hab i₂ (by omega))
    have e₂' := abs_le.mp (hab j₂ (by omega))
    calc ((i₁ : ℝ) - j₁ - 2 * e) / (x i₁ - x j₁) ≤ a := by
          rw [div_le_iff₀ hX₁]; linarith
      _ ≤ ((i₂ : ℝ) - j₂ + 2 * e) / (x i₂ - x j₂) := by
          rw [le_div_iff₀ hX₂]; linarith
  · intro hZ
    classical
    set S : Finset (ℕ × ℕ) :=
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 < p.2) with hSdef
    have hmem : ∀ p ∈ S, p.1 < p.2 ∧ p.2 ≤ n := by
      intro p hp
      simp only [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      exact ⟨hp.2, by omega⟩
    obtain ⟨a, ha⟩ := exists_common_point S
      (fun p => ((p.2 : ℝ) - p.1 - 2 * e) / (x p.2 - x p.1))
      (fun p => ((p.2 : ℝ) - p.1 + 2 * e) / (x p.2 - x p.1)) (fun p hp q hq => by
        obtain ⟨hp1, hp2⟩ := hmem p hp
        obtain ⟨hq1, hq2⟩ := hmem q hq
        exact (certZ_le_iff (sub_pos.mpr (hx _ _ hp1 hp2)) (sub_pos.mpr (hx _ _ hq1 hq2))).mp
          (hZ _ _ _ _ hp1 hp2 hq1 hq2))
    -- the residuals `y i = i - a x i` oscillate by at most `2e`
    set y : ℕ → ℝ := fun i => (i : ℝ) - a * x i with hy
    have hpair : ∀ j i, j < i → i ≤ n → y i - y j ≤ 2 * e ∧ y j - y i ≤ 2 * e := by
      intro j i hji hi
      have hX := sub_pos.mpr (hx j i hji hi)
      have hp : (j, i) ∈ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, hji⟩
      obtain ⟨hL, hU⟩ := ha _ hp
      simp only at hL hU
      rw [div_le_iff₀ hX] at hL
      rw [le_div_iff₀ hX] at hU
      simp only [hy]
      constructor <;> nlinarith
    have hosc : ∀ i j, i ≤ n → j ≤ n → y i - y j ≤ 2 * e := by
      intro i j hi hj
      rcases lt_trichotomy j i with hji | rfl | hij
      · exact (hpair j i hji hi).1
      · simp; linarith
      · exact (hpair i j hij hj).2
    have hne : (Finset.range (n + 1)).Nonempty := ⟨0, by simp⟩
    obtain ⟨imax, himax, hmax⟩ := (Finset.range (n + 1)).exists_max_image y hne
    obtain ⟨imin, himin, hmin⟩ := (Finset.range (n + 1)).exists_min_image y hne
    rw [Finset.mem_range] at himax himin
    have hw := hosc imax imin (by omega) (by omega)
    refine ⟨a, (y imax + y imin) / 2, fun i hi => ?_⟩
    have h1 := hmax i (Finset.mem_range.mpr hi)
    have h2 := hmin i (Finset.mem_range.mpr hi)
    have : (i : ℝ) - (a * x i + (y imax + y imin) / 2) = y i - (y imax + y imin) / 2 := by
      simp only [hy]; ring
    rw [this, abs_le]
    constructor <;> linarith

/-! ## Conditioning on an independent variable -/

section Smoothing

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Conditioning on an independent variable: if `X` has the local bound
`P (X ∈ A) ≤ c |A|` and is independent of `W`, then the probability of `(X, W) ∈ E` is at most
`c` times the average Lebesgue measure of the slices of `E`. -/
theorem measure_pair_le_lintegral [IsProbabilityMeasure P] {β : Type*} [MeasurableSpace β]
    {X : Ω → ℝ} {W : Ω → β} (hX : Measurable X) (hW : Measurable W) (hind : IndepFun X W P)
    {c : ENNReal} (hloc : ∀ A : Set ℝ, MeasurableSet A → P (X ⁻¹' A) ≤ c * volume A)
    {E : Set (ℝ × β)} (hE : MeasurableSet E) :
    P ((fun ω => (X ω, W ω)) ⁻¹' E) ≤
      c * ∫⁻ w, volume ((fun x => (x, w)) ⁻¹' E) ∂(P.map W) := by
  rw [← Measure.map_apply (hX.prodMk hW) hE,
    (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hW.aemeasurable).mp hind,
    Measure.prod_apply_symm hE, ← lintegral_const_mul c (measurable_measure_prodMk_right hE)]
  refine lintegral_mono fun w => ?_
  rw [Measure.map_apply hX (measurable_prodMk_right hE)]
  exact hloc _ (measurable_prodMk_right hE)

/-- iid almost surely positive gaps with mean `μ > 0` whose law satisfies the density-type
bound `P (g 0 ∈ A) ≤ (K / μ) |A|` (the measure form of `μ ‖f‖_∞ ≤ K`). -/
structure LocalGapLaw (P : Measure Ω) (g : ℕ → Ω → ℝ) (μ K : ℝ) : Prop where
  iid : IIDSeq P g
  pos : ∀ᵐ ω ∂P, 0 < g 0 ω
  mean : ∫ ω, g 0 ω ∂P = μ
  mu_pos : 0 < μ
  local_bound : ∀ A : Set ℝ, MeasurableSet A →
    P (g 0 ⁻¹' A) ≤ ENNReal.ofReal (K / μ) * volume A

/-- The sum of the gaps with indices in `S`. -/
def gsum (g : ℕ → Ω → ℝ) (S : Finset ℕ) (ω : Ω) : ℝ := ∑ t ∈ S, g t ω

theorem measurable_gsum {g : ℕ → Ω → ℝ} (hg : ∀ t, Measurable (g t)) (S : Finset ℕ) :
    Measurable (gsum g S) :=
  Finset.measurable_sum S fun t _ => hg t

namespace LocalGapLaw

variable {g : ℕ → Ω → ℝ} {μ K : ℝ}

theorem isProbabilityMeasure (hg : LocalGapLaw P g μ K) : IsProbabilityMeasure P :=
  hg.iid.indep.isProbabilityMeasure

theorem local_bound_t (hg : LocalGapLaw P g μ K) (t : ℕ) (A : Set ℝ) (hA : MeasurableSet A) :
    P (g t ⁻¹' A) ≤ ENNReal.ofReal (K / μ) * volume A := by
  rw [(hg.iid.ident t).measure_mem_eq hA]
  exact hg.local_bound A hA

theorem pos_t (hg : LocalGapLaw P g μ K) (t : ℕ) : ∀ᵐ ω ∂P, 0 < g t ω :=
  (hg.iid.ident t).symm.ae_snd (p := fun x => 0 < x) measurableSet_Ioi hg.pos

theorem pos_all (hg : LocalGapLaw P g μ K) : ∀ᵐ ω ∂P, ∀ t, 0 < g t ω :=
  ae_all_iff.mpr hg.pos_t

theorem integrable (hg : LocalGapLaw P g μ K) (t : ℕ) : Integrable (g t) P := by
  have h0 : Integrable (g 0) P :=
    Integrable.of_integral_ne_zero (by rw [hg.mean]; exact hg.mu_pos.ne')
  exact (hg.iid.ident t).integrable_iff.mpr h0

theorem lintegral_ofReal (hg : LocalGapLaw P g μ K) (t : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (g t ω) ∂P = ENNReal.ofReal μ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (hg.integrable t)
    ((hg.pos_t t).mono fun ω h => h.le), hg.iid.integral_eq t, hg.mean]

theorem lintegral_ofReal_gsum_le (hg : LocalGapLaw P g μ K) (S : Finset ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gsum g S ω) ∂P ≤ ENNReal.ofReal (S.card * μ) := by
  have hpt : ∀ ω, ENNReal.ofReal (gsum g S ω) ≤ ∑ t ∈ S, ENNReal.ofReal (g t ω) := by
    intro ω
    unfold gsum
    induction S using Finset.induction_on with
    | empty => simp
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact ENNReal.ofReal_add_le.trans (add_le_add_right ih _)
  calc ∫⁻ ω, ENNReal.ofReal (gsum g S ω) ∂P
      ≤ ∫⁻ ω, ∑ t ∈ S, ENNReal.ofReal (g t ω) ∂P := lintegral_mono hpt
    _ = ∑ t ∈ S, ∫⁻ ω, ENNReal.ofReal (g t ω) ∂P :=
        lintegral_finsetSum _ fun t _ => (hg.iid.measurable t).ennreal_ofReal
    _ = ENNReal.ofReal (S.card * μ) := by
        simp only [hg.lintegral_ofReal, Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

/-- Every nonempty sum of distinct gaps satisfies the same local bound (convolution with a
probability law does not increase the bound). -/
theorem gsum_local_bound (hg : LocalGapLaw P g μ K) {S : Finset ℕ} (hS : S.Nonempty)
    (A : Set ℝ) (hA : MeasurableSet A) :
    P (gsum g S ⁻¹' A) ≤ ENNReal.ofReal (K / μ) * volume A := by
  have := hg.isProbabilityMeasure
  induction hS using Finset.Nonempty.cons_induction generalizing A with
  | singleton a =>
    have h1 : gsum g {a} = g a := by funext ω; simp [gsum]
    rw [h1]
    exact hg.local_bound_t a A hA
  | cons a s has hs ih =>
    have hind : IndepFun (gsum g s) (g a) P := by
      have := hg.iid.indep.indepFun_finsetSum_of_notMem hg.iid.measurable has
      convert this using 1
      funext ω
      simp [gsum, Finset.sum_apply]
    have hE : MeasurableSet {q : ℝ × ℝ | q.1 + q.2 ∈ A} := (measurable_fst.add measurable_snd) hA
    have key := measure_pair_le_lintegral (measurable_gsum hg.iid.measurable s)
      (hg.iid.measurable a) hind (fun A hA => ih A hA) hE
    have heq : gsum g (Finset.cons a s has) ⁻¹' A =
        (fun ω => (gsum g s ω, g a ω)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 ∈ A} := by
      ext ω
      simp only [gsum, Set.mem_preimage, Set.mem_ofPred_eq, Finset.sum_cons]
      rw [add_comm]
    rw [heq]
    refine key.trans (le_of_eq ?_)
    have hslice : ∀ w : ℝ,
        volume ((fun x => (x, w)) ⁻¹' {q : ℝ × ℝ | q.1 + q.2 ∈ A}) = volume A :=
      fun w => measure_preimage_add_right volume w A
    simp_rw [hslice, lintegral_const]
    rw [Measure.map_apply (hg.iid.measurable a) MeasurableSet.univ]
    simp

theorem K_pos (hg : LocalGapLaw P g μ K) : 0 < K := by
  have := hg.isProbabilityMeasure
  by_contra hK'
  have hK : K ≤ 0 := not_lt.mp hK'
  have hκ : ENNReal.ofReal (K / μ) = 0 :=
    ENNReal.ofReal_eq_zero.mpr (div_nonpos_of_nonpos_of_nonneg hK hg.mu_pos.le)
  have h0 : ∀ n : ℕ, P (g 0 ⁻¹' Icc (-(n : ℝ)) n) = 0 := fun n =>
    le_antisymm (by simpa [hκ] using hg.local_bound _ measurableSet_Icc) zero_le
  have hU : (univ : Set Ω) = ⋃ n : ℕ, g 0 ⁻¹' Icc (-(n : ℝ)) n := by
    ext ω
    simp only [mem_univ, mem_iUnion, mem_preimage, mem_Icc, true_iff]
    obtain ⟨n, hn⟩ := exists_nat_ge |g 0 ω|
    exact ⟨n, by linarith [neg_abs_le (g 0 ω)], by linarith [le_abs_self (g 0 ω)]⟩
  have h1 : P univ = 0 := by rw [hU]; exact measure_iUnion_null h0
  simp at h1

end LocalGapLaw

/-! ## Independence of sums over disjoint index sets -/

omit [MeasurableSpace Ω] in
theorem measurable_gsum_sup {g : ℕ → Ω → ℝ} {S T : Finset ℕ} (hST : S ⊆ T) :
    Measurable[⨆ i ∈ (T : Set ℕ), MeasurableSpace.comap (g i) inferInstance] (gsum g S) :=
  Finset.measurable_sum S fun i hi =>
    (comap_measurable (g i)).mono (le_iSup₂ (f := fun i (_ : i ∈ (T : Set ℕ)) =>
      MeasurableSpace.comap (g i) inferInstance) i (Finset.mem_coe.mpr (hST hi))) le_rfl

theorem IIDSeq.indepFun_of_disjoint {g : ℕ → Ω → ℝ} (hg : IIDSeq P g) {S T : Finset ℕ}
    (hST : Disjoint S T) {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    {F : Ω → β} {G : Ω → γ}
    (hF : Measurable[⨆ i ∈ (S : Set ℕ), MeasurableSpace.comap (g i) inferInstance] F)
    (hG : Measurable[⨆ i ∈ (T : Set ℕ), MeasurableSpace.comap (g i) inferInstance] G) :
    IndepFun F G P := by
  rw [IndepFun_iff_Indep]
  have hind := indep_iSup_of_disjoint (fun k => (hg.measurable k).comap_le) hg.indep.iIndep
    (Finset.disjoint_coe.mpr hST)
  exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hF.comap_le) hG.comap_le

/-- The sum over `S` is independent of the pair of sums over `T₁` and `T₂` when `S` is disjoint
from both. -/
theorem IIDSeq.indepFun_gsum_pair {g : ℕ → Ω → ℝ} (hg : IIDSeq P g) {S T₁ T₂ : Finset ℕ}
    (h₁ : Disjoint S T₁) (h₂ : Disjoint S T₂) :
    IndepFun (gsum g S) (fun ω => (gsum g T₁ ω, gsum g T₂ ω)) P := by
  classical
  exact hg.indepFun_of_disjoint (Finset.disjoint_union_right.mpr ⟨h₁, h₂⟩)
    (measurable_gsum_sup subset_rfl)
    ((measurable_gsum_sup Finset.subset_union_left).prodMk
      (measurable_gsum_sup Finset.subset_union_right))

/-! ## The monotone change of variables -/

/-- The core smoothing estimate.  For fixed `(V, D)`, the quantity
`M V / (2 (λ Y + D)) - β / 2` is monotone in `Y` on `λ Y + D > 0`, and the set of `Y` for which
it lies in `[z, z + h]` is an interval of length at most `2 h M V / (λ (β + 2 z)^2)`. -/
theorem measure_certForm_le [IsProbabilityMeasure P] {Y V D : Ω → ℝ}
    (hY : Measurable Y) (hV : Measurable V) (hD : Measurable D)
    (hind : IndepFun Y (fun ω => (V ω, D ω)) P) {κ : ℝ}
    (hloc : ∀ A : Set ℝ, MeasurableSet A → P (Y ⁻¹' A) ≤ ENNReal.ofReal κ * volume A)
    {M lam β z h : ℝ} (hM : 0 ≤ M) (hlam : 0 < lam) (hz : 0 < β + 2 * z) (hh : 0 ≤ h) :
    P {ω | 0 < lam * Y ω + D ω ∧ M * V ω / (2 * (lam * Y ω + D ω)) - β / 2 ∈ Icc z (z + h)} ≤
      ENNReal.ofReal κ * (ENNReal.ofReal (2 * h * M / (lam * (β + 2 * z) ^ 2)) *
        ∫⁻ ω, ENNReal.ofReal (V ω) ∂P) := by
  set c := 2 * h * M / (lam * (β + 2 * z) ^ 2) with hc
  have hc0 : 0 ≤ c := by positivity
  set E : Set (ℝ × (ℝ × ℝ)) := {q | 0 < lam * q.1 + q.2.2 ∧
    M * q.2.1 / (2 * (lam * q.1 + q.2.2)) - β / 2 ∈ Icc z (z + h)} with hEdef
  have hE : MeasurableSet E := by
    have hf : Measurable (fun q : ℝ × (ℝ × ℝ) => lam * q.1 + q.2.2) := by fun_prop
    have hφ : Measurable (fun q : ℝ × (ℝ × ℝ) =>
        M * q.2.1 / (2 * (lam * q.1 + q.2.2)) - β / 2) := by fun_prop
    exact (measurableSet_lt measurable_const hf).inter (hφ measurableSet_Icc)
  have heq : {ω | 0 < lam * Y ω + D ω ∧
      M * V ω / (2 * (lam * Y ω + D ω)) - β / 2 ∈ Icc z (z + h)} =
      (fun ω => (Y ω, (V ω, D ω))) ⁻¹' E := rfl
  rw [heq]
  refine (measure_pair_le_lintegral hY (hV.prodMk hD) hind hloc hE).trans ?_
  refine mul_le_mul_right ?_ _
  have hslice : ∀ w : ℝ × ℝ, volume ((fun x => (x, w)) ⁻¹' E) ≤ ENNReal.ofReal (c * w.1) := by
    rintro ⟨v, d⟩
    have hD₁ : 0 < β + 2 * z := hz
    have hD₂ : 0 < β + 2 * z + 2 * h := by linarith
    have hsub : (fun x => (x, (v, d))) ⁻¹' E ⊆
        Icc ((M * v / (β + 2 * z + 2 * h) - d) / lam) ((M * v / (β + 2 * z) - d) / lam) := by
      rintro y ⟨hs, ht1, ht2⟩
      simp only at hs ht1 ht2
      have h2s : 0 < 2 * (lam * y + d) := by linarith
      have e1 : (z + β / 2) * (2 * (lam * y + d)) ≤ M * v :=
        (le_div_iff₀ h2s).mp (by linarith)
      have e2 : M * v ≤ (z + h + β / 2) * (2 * (lam * y + d)) :=
        (div_le_iff₀ h2s).mp (by linarith)
      constructor
      · rw [div_le_iff₀ hlam]
        have : M * v / (β + 2 * z + 2 * h) ≤ lam * y + d := by
          rw [div_le_iff₀ hD₂]; linarith
        linarith
      · rw [le_div_iff₀ hlam]
        have : lam * y + d ≤ M * v / (β + 2 * z) := by
          rw [le_div_iff₀ hD₁]; linarith
        linarith
    refine (measure_mono hsub).trans ?_
    rw [Real.volume_Icc]
    have hlen : (M * v / (β + 2 * z) - d) / lam - (M * v / (β + 2 * z + 2 * h) - d) / lam =
        2 * h * (M * v) / (lam * (β + 2 * z) * (β + 2 * z + 2 * h)) := by
      field_simp
      ring
    rw [hlen, ENNReal.ofReal_le_ofReal_iff']
    rcases le_or_gt (M * v) 0 with hMv | hMv
    · right
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · positivity
    · left
      have hcv : c * (v, d).1 = 2 * h * (M * v) / (lam * (β + 2 * z) ^ 2) := by
        simp only [hc]; ring
      rw [hcv]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      rw [sq, ← mul_assoc]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  calc ∫⁻ w, volume ((fun x => (x, w)) ⁻¹' E) ∂(P.map (fun ω => (V ω, D ω)))
      ≤ ∫⁻ w, ENNReal.ofReal (c * w.1) ∂(P.map (fun ω => (V ω, D ω))) := lintegral_mono hslice
    _ = ∫⁻ ω, ENNReal.ofReal (c * V ω) ∂P :=
        lintegral_map (by fun_prop) (hV.prodMk hD)
    _ = ENNReal.ofReal c * ∫⁻ ω, ENNReal.ofReal (V ω) ∂P := by
        simp_rw [ENNReal.ofReal_mul hc0]
        exact lintegral_const_mul _ hV.ennreal_ofReal

/-! ## Certificates of two gap intervals -/

/-- The certificate of two index sets of gaps: with `A = #SI`, `B = #SJ`, `X_I = ∑_{SI} g`,
`X_J = ∑_{SJ} g`, it is `(A X_J - B X_I) / (2 (X_I + X_J))`. -/
def certSum (g : ℕ → Ω → ℝ) (SI SJ : Finset ℕ) (ω : Ω) : ℝ :=
  ((SI.card : ℝ) * gsum g SJ ω - (SJ.card : ℝ) * gsum g SI ω) /
    (2 * (gsum g SI ω + gsum g SJ ω))

omit [MeasurableSpace Ω] in
theorem certSum_swap (g : ℕ → Ω → ℝ) (SI SJ : Finset ℕ) (ω : Ω) :
    certSum g SJ SI ω = -certSum g SI SJ ω := by
  unfold certSum
  rw [← neg_div, add_comm (gsum g SJ ω)]
  ring_nf

omit [MeasurableSpace Ω] in
theorem certSum_mem_Icc_swap (g : ℕ → Ω → ℝ) (SI SJ : Finset ℕ) (z h : ℝ) :
    {ω | certSum g SI SJ ω ∈ Icc z (z + h)} =
      {ω | certSum g SJ SI ω ∈ Icc (-(z + h)) (-(z + h) + h)} := by
  ext ω
  simp only [mem_ofPred_eq, mem_Icc]
  rw [certSum_swap g SI SJ ω]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

namespace LocalGapLaw

variable {g : ℕ → Ω → ℝ} {μ K : ℝ}

/-- First smoothing bound: vary the gaps exclusive to `SI`, conditioning on the others. -/
theorem certSum_bound_left (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ}
    (hd : (SI \ SJ).Nonempty) {z h : ℝ} (hz : 0 < (SJ.card : ℝ) + 2 * z) (hh : 0 ≤ h) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤
      ENNReal.ofReal (2 * h * K * SJ.card * (SI.card + SJ.card) /
        ((SJ.card : ℝ) + 2 * z) ^ 2) := by
  classical
  have := hg.isProbabilityMeasure
  have hmeas := hg.iid.measurable
  have hI : SI.Nonempty := hd.mono Finset.sdiff_subset
  set A : ℝ := (SI.card : ℝ) with hA
  set B : ℝ := (SJ.card : ℝ) with hB
  have hdisj : Disjoint (SI \ SJ) (SI ∩ SJ) :=
    Finset.disjoint_left.mpr fun x hx hx' => (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp hx').2
  have hind0 := hg.iid.indepFun_gsum_pair (S := SI \ SJ) (T₁ := SJ) (T₂ := SI ∩ SJ)
    Finset.sdiff_disjoint hdisj
  have hind : IndepFun (gsum g (SI \ SJ))
      (fun ω => (gsum g SJ ω, gsum g SJ ω + gsum g (SI ∩ SJ) ω)) P :=
    hind0.comp (φ := id) (ψ := fun q : ℝ × ℝ => (q.1, q.1 + q.2)) measurable_id (by fun_prop)
  have hcore := measure_certForm_le (measurable_gsum hmeas _) (measurable_gsum hmeas _)
    ((measurable_gsum hmeas _).add (measurable_gsum hmeas _)) hind (hg.gsum_local_bound hd)
    (M := A + B) (lam := 1) (β := B) (by positivity) one_pos hz hh
  have hμ := hg.mu_pos
  have hK := hg.K_pos
  refine (measure_mono_ae ?_).trans (hcore.trans ?_)
  · filter_upwards [hg.pos_all] with ω hω hmem
    have hXI : gsum g SI ω = gsum g (SI \ SJ) ω + gsum g (SI ∩ SJ) ω := by
      simp only [gsum]
      rw [← Finset.sum_inter_add_sum_sdiff SI SJ]
      ring
    have hIpos : 0 < gsum g SI ω := Finset.sum_pos (fun t _ => hω t) hI
    have hJnn : 0 ≤ gsum g SJ ω := Finset.sum_nonneg fun t _ => (hω t).le
    have hs : 0 < 1 * gsum g (SI \ SJ) ω + (gsum g SJ ω + gsum g (SI ∩ SJ) ω) := by linarith
    refine ⟨hs, ?_⟩
    have hs' : gsum g SI ω + gsum g SJ ω ≠ 0 := by linarith
    have hs'' : 1 * gsum g (SI \ SJ) ω + (gsum g SJ ω + gsum g (SI ∩ SJ) ω) ≠ 0 := hs.ne'
    have : (A + B) * gsum g SJ ω /
        (2 * (1 * gsum g (SI \ SJ) ω + (gsum g SJ ω + gsum g (SI ∩ SJ) ω))) - B / 2 =
        certSum g SI SJ ω := by
      unfold certSum
      rw [div_sub' (by positivity), div_eq_div_iff (by positivity) (by positivity)]
      rw [hXI]
      ring
    simp only [Pi.add_apply]
    rw [this]
    exact hmem
  · have hκ0 : 0 ≤ K / μ := by positivity
    have hc0 : 0 ≤ 2 * h * (A + B) / (1 * (B + 2 * z) ^ 2) := by positivity
    calc ENNReal.ofReal (K / μ) * (ENNReal.ofReal (2 * h * (A + B) / (1 * (B + 2 * z) ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (gsum g SJ ω) ∂P)
        ≤ ENNReal.ofReal (K / μ) * (ENNReal.ofReal (2 * h * (A + B) / (1 * (B + 2 * z) ^ 2)) *
          ENNReal.ofReal (SJ.card * μ)) := by
          gcongr
          exact hg.lintegral_ofReal_gsum_le SJ
      _ = ENNReal.ofReal (K / μ * (2 * h * (A + B) / (1 * (B + 2 * z) ^ 2) * (B * μ))) := by
          rw [ENNReal.ofReal_mul hκ0, ENNReal.ofReal_mul hc0]
      _ = ENNReal.ofReal (2 * h * K * B * (A + B) / (B + 2 * z) ^ 2) := by
          congr 1
          field_simp

/-- First smoothing bound in scale-free form. -/
theorem certSum_bound_left' (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ}
    (hd : (SI \ SJ).Nonempty) {m z h : ℝ} (hm : 0 < m)
    (hmz : (SI.card : ℝ) + SJ.card ≤ m * (SJ.card + 2 * z)) (hh : 0 ≤ h) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (2 * m ^ 2 * K * h) := by
  have hI : SI.Nonempty := hd.mono Finset.sdiff_subset
  have hA1 : (1 : ℝ) ≤ SI.card := by exact_mod_cast hI.card_pos
  have hB0 : (0 : ℝ) ≤ SJ.card := Nat.cast_nonneg _
  have hz : 0 < (SJ.card : ℝ) + 2 * z := by
    by_contra hneg
    have : m * ((SJ.card : ℝ) + 2 * z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.mp hneg)
    linarith
  refine (hg.certSum_bound_left hd hz hh).trans (ENNReal.ofReal_le_ofReal ?_)
  have hK := hg.K_pos
  rw [div_le_iff₀ (by positivity)]
  have h1 : (SJ.card : ℝ) * (SI.card + SJ.card) ≤ (SI.card + SJ.card) * (SI.card + SJ.card) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : ((SI.card : ℝ) + SJ.card) * (SI.card + SJ.card) ≤
      (m * (SJ.card + 2 * z)) * (m * (SJ.card + 2 * z)) :=
    mul_self_le_mul_self (by positivity) hmz
  have h3 : 0 ≤ 2 * h * K := by positivity
  calc 2 * h * K * SJ.card * (SI.card + SJ.card) =
        2 * h * K * (SJ.card * (SI.card + SJ.card)) := by ring
    _ ≤ 2 * h * K * ((m * (SJ.card + 2 * z)) * (m * (SJ.card + 2 * z))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = 2 * m ^ 2 * K * h * ((SJ.card : ℝ) + 2 * z) ^ 2 := by ring

/-- Second smoothing bound for nested intervals `SJ ⊆ SI`: vary the common gaps `SJ`,
conditioning on the exclusive gaps `SI \ SJ`. -/
theorem certSum_bound_contain (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ} (hsub : SJ ⊆ SI)
    (hJ : SJ.Nonempty) {z h : ℝ}
    (hz : 0 < ((SI \ SJ).card : ℝ) - 4 * z - 4 * h) (hh : 0 ≤ h) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤
      ENNReal.ofReal (2 * h * K * (SI \ SJ).card * (SI.card + SJ.card) /
        (((SI \ SJ).card : ℝ) - 4 * z - 4 * h) ^ 2) := by
  classical
  have := hg.isProbabilityMeasure
  have hmeas := hg.iid.measurable
  set A : ℝ := (SI.card : ℝ) with hA
  set B : ℝ := (SJ.card : ℝ) with hB
  set a : ℝ := ((SI \ SJ).card : ℝ) with ha
  have hAab : A = a + B := by
    rw [hA, ha, hB, ← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hsub]
  have hind0 := hg.iid.indepFun_gsum_pair (S := SJ) (T₁ := SI \ SJ) (T₂ := SI \ SJ)
    Finset.disjoint_sdiff Finset.disjoint_sdiff
  have hind : IndepFun (gsum g SJ) (fun ω => (gsum g (SI \ SJ) ω, 2 * gsum g (SI \ SJ) ω)) P :=
    hind0.comp (φ := id) (ψ := fun q : ℝ × ℝ => (q.1, 2 * q.2)) measurable_id (by fun_prop)
  have hz' : 0 < a / 2 + 2 * (-z - h) := by linarith
  have hcore := measure_certForm_le (measurable_gsum hmeas _) (measurable_gsum hmeas _)
    ((measurable_gsum hmeas _).const_mul 2) hind (hg.gsum_local_bound hJ)
    (M := A + B) (lam := 4) (β := a / 2) (by positivity) (by norm_num) hz' hh
  have hμ := hg.mu_pos
  have hK := hg.K_pos
  refine (measure_mono_ae ?_).trans (hcore.trans ?_)
  · filter_upwards [hg.pos_all] with ω hω hmem
    have hXI : gsum g SI ω = gsum g (SI \ SJ) ω + gsum g SJ ω := by
      simp only [gsum]
      rw [Finset.sum_sdiff hsub]
    have hJpos : 0 < gsum g SJ ω := Finset.sum_pos (fun t _ => hω t) hJ
    have hPnn : 0 ≤ gsum g (SI \ SJ) ω := Finset.sum_nonneg fun t _ => (hω t).le
    have hs : 0 < 4 * gsum g SJ ω + 2 * gsum g (SI \ SJ) ω := by linarith
    refine ⟨hs, ?_⟩
    have hs' : gsum g SI ω + gsum g SJ ω ≠ 0 := by linarith
    have : (A + B) * gsum g (SI \ SJ) ω / (2 * (4 * gsum g SJ ω + 2 * gsum g (SI \ SJ) ω)) -
        a / 2 / 2 = -certSum g SI SJ ω := by
      unfold certSum
      rw [← neg_div, div_sub' (by positivity), div_eq_div_iff (by positivity) (by positivity)]
      rw [hXI, ← hA, ← hB, hAab]
      ring
    rw [this]
    obtain ⟨h1, h2⟩ := hmem
    constructor <;> linarith
  · have hκ0 : 0 ≤ K / μ := by positivity
    have hc0 : 0 ≤ 2 * h * (A + B) / (4 * (a / 2 + 2 * (-z - h)) ^ 2) := by positivity
    calc ENNReal.ofReal (K / μ) *
          (ENNReal.ofReal (2 * h * (A + B) / (4 * (a / 2 + 2 * (-z - h)) ^ 2)) *
          ∫⁻ ω, ENNReal.ofReal (gsum g (SI \ SJ) ω) ∂P)
        ≤ ENNReal.ofReal (K / μ) *
          (ENNReal.ofReal (2 * h * (A + B) / (4 * (a / 2 + 2 * (-z - h)) ^ 2)) *
          ENNReal.ofReal ((SI \ SJ).card * μ)) := by
          gcongr
          exact hg.lintegral_ofReal_gsum_le (SI \ SJ)
      _ = ENNReal.ofReal (K / μ * (2 * h * (A + B) / (4 * (a / 2 + 2 * (-z - h)) ^ 2) *
            (a * μ))) := by
          rw [ENNReal.ofReal_mul hκ0, ENNReal.ofReal_mul hc0]
      _ = ENNReal.ofReal (2 * h * K * a * (A + B) / (a - 4 * z - 4 * h) ^ 2) := by
          congr 1
          have h1 : a / 2 + 2 * (-z - h) ≠ 0 := hz'.ne'
          have h2 : a - 4 * z - 4 * h ≠ 0 := hz.ne'
          field_simp
          ring

/-- Second smoothing bound in scale-free form. -/
theorem certSum_bound_contain' (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ} (hsub : SJ ⊆ SI)
    (hJ : SJ.Nonempty) (hd : (SI \ SJ).Nonempty) {m z h : ℝ} (hm : 0 < m)
    (hmz : (SI.card : ℝ) + SJ.card ≤ m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h)) (hh : 0 ≤ h) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (2 * m ^ 2 * K * h) := by
  have hI : SI.Nonempty := hd.mono Finset.sdiff_subset
  have hA1 : (1 : ℝ) ≤ SI.card := by exact_mod_cast hI.card_pos
  have hB0 : (0 : ℝ) ≤ SJ.card := Nat.cast_nonneg _
  have ha : ((SI \ SJ).card : ℝ) ≤ SI.card := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hz : 0 < ((SI \ SJ).card : ℝ) - 4 * z - 4 * h := by
    by_contra hneg
    have : m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hm.le (not_lt.mp hneg)
    linarith
  refine (hg.certSum_bound_contain hsub hJ hz hh).trans (ENNReal.ofReal_le_ofReal ?_)
  have hK := hg.K_pos
  rw [div_le_iff₀ (by positivity)]
  have h1 : ((SI \ SJ).card : ℝ) * (SI.card + SJ.card) ≤
      (SI.card + SJ.card) * (SI.card + SJ.card) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have h2 : ((SI.card : ℝ) + SJ.card) * (SI.card + SJ.card) ≤
      (m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h)) *
        (m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h)) :=
    mul_self_le_mul_self (by positivity) hmz
  have h3 : 0 ≤ 2 * h * K := by positivity
  calc 2 * h * K * (SI \ SJ).card * (SI.card + SJ.card) =
        2 * h * K * ((SI \ SJ).card * (SI.card + SJ.card)) := by ring
    _ ≤ 2 * h * K * ((m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h)) *
          (m * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h))) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) h3
    _ = 2 * m ^ 2 * K * h * (((SI \ SJ).card : ℝ) - 4 * z - 4 * h) ^ 2 := by ring

end LocalGapLaw

/-- Splitting an interval at a point `zs`: a bound `c h` on intervals entirely above `zs` and on
intervals entirely below `zs` gives the same bound on every interval. -/
theorem measure_Icc_split {Zf : Ω → ℝ} {c zs : ℝ} (hc : 0 ≤ c)
    (hup : ∀ z h, zs ≤ z → 0 ≤ h → P {ω | Zf ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (c * h))
    (hdown : ∀ z h, z + h ≤ zs → 0 ≤ h →
      P {ω | Zf ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (c * h))
    (z h : ℝ) : P {ω | Zf ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (c * h) := by
  rcases lt_or_ge h 0 with hh | hh
  · have : {ω | Zf ω ∈ Icc z (z + h)} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_Icc, mem_empty_iff_false, iff_false, not_and, not_le]
      intro h1
      linarith
    rw [this]
    simp
  rcases le_or_gt zs z with hz | hz
  · exact hup z h hz hh
  rcases le_or_gt (z + h) zs with hz' | hz'
  · exact hdown z h hz' hh
  have hsub : {ω | Zf ω ∈ Icc z (z + h)} ⊆
      {ω | Zf ω ∈ Icc z (z + (zs - z))} ∪ {ω | Zf ω ∈ Icc zs (zs + (z + h - zs))} := by
    rintro ω ⟨h1, h2⟩
    rcases le_total (Zf ω) zs with h3 | h3
    · left; exact ⟨h1, by linarith⟩
    · right; exact ⟨h3, by linarith⟩
  calc P {ω | Zf ω ∈ Icc z (z + h)}
      ≤ P ({ω | Zf ω ∈ Icc z (z + (zs - z))} ∪ {ω | Zf ω ∈ Icc zs (zs + (z + h - zs))}) :=
        measure_mono hsub
    _ ≤ P {ω | Zf ω ∈ Icc z (z + (zs - z))} + P {ω | Zf ω ∈ Icc zs (zs + (z + h - zs))} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (c * (zs - z)) + ENNReal.ofReal (c * (z + h - zs)) :=
        add_le_add (hdown z (zs - z) (by linarith) (by linarith))
          (hup zs (z + h - zs) le_rfl (by linarith))
    _ = ENNReal.ofReal (c * h) := by
        rw [← ENNReal.ofReal_add (by nlinarith) (by nlinarith)]
        ring_nf

namespace LocalGapLaw

variable {g : ℕ → Ω → ℝ} {μ K : ℝ}

theorem certSum_Icc_le_of_sdiff (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ}
    (hJ : SJ.Nonempty) (hd : (SI \ SJ).Nonempty) (z h : ℝ) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (32 * K * h) := by
  classical
  have hK := hg.K_pos
  have hmono : ∀ h' : ℝ, 0 ≤ h' → ∀ m : ℝ, 2 * m ^ 2 ≤ 32 →
      ENNReal.ofReal (2 * m ^ 2 * K * h') ≤ ENNReal.ofReal (32 * K * h') := by
    intro h' hh' m hm
    apply ENNReal.ofReal_le_ofReal
    have : 0 ≤ K * h' := by positivity
    nlinarith
  by_cases hd' : (SJ \ SI).Nonempty
  · refine measure_Icc_split (zs := ((SI.card : ℝ) - SJ.card) / 4) (by positivity)
      (fun z' h' hz' hh' => ?_) (fun z' h' hz' hh' => ?_) z h
    · refine (hg.certSum_bound_left' hd (m := 2) two_pos ?_ hh').trans (hmono h' hh' 2 (by norm_num))
      linarith
    · rw [certSum_mem_Icc_swap]
      refine (hg.certSum_bound_left' hd' (m := 2) two_pos ?_ hh').trans
        (hmono h' hh' 2 (by norm_num))
      linarith
  · have hsub : SJ ⊆ SI :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hd')
    have hcard : (((SI \ SJ).card : ℕ) : ℝ) = SI.card - SJ.card := by
      rw [eq_sub_iff_add_eq, ← Nat.cast_add, Finset.card_sdiff_add_card_eq_card hsub]
    refine measure_Icc_split (zs := ((SI.card : ℝ) - 3 * SJ.card) / 8) (by positivity)
      (fun z' h' hz' hh' => ?_) (fun z' h' hz' hh' => ?_) z h
    · refine (hg.certSum_bound_left' hd (m := 4) (by norm_num) ?_ hh').trans
        (hmono h' hh' 4 (by norm_num))
      linarith
    · refine (hg.certSum_bound_contain' hsub hJ hd (m := 2) two_pos ?_ hh').trans
        (hmono h' hh' 2 (by norm_num))
      rw [hcard]
      linarith

/-- **Scale-free certificate smoothing** (`marg:thm:certificate-density`), finite-set form:
for distinct nonempty index sets, every interval of length `h` carries probability at most
`32 K h`. -/
theorem certSum_Icc_le (hg : LocalGapLaw P g μ K) {SI SJ : Finset ℕ} (hI : SI.Nonempty)
    (hJ : SJ.Nonempty) (hne : SI ≠ SJ) (z h : ℝ) :
    P {ω | certSum g SI SJ ω ∈ Icc z (z + h)} ≤ ENNReal.ofReal (32 * K * h) := by
  classical
  by_cases hd : (SI \ SJ).Nonempty
  · exact hg.certSum_Icc_le_of_sdiff hJ hd z h
  · have hsub : SI ⊆ SJ :=
      Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hd)
    have hd' : (SJ \ SI).Nonempty := by
      by_contra hd'
      exact hne (Finset.Subset.antisymm hsub
        (Finset.sdiff_eq_empty_iff_subset.mp (Finset.not_nonempty_iff_eq_empty.mp hd')))
    rw [certSum_mem_Icc_swap]
    have := hg.certSum_Icc_le_of_sdiff hI hd' (-(z + h)) h
    exact this

end LocalGapLaw

omit [MeasurableSpace Ω] in
/-- Increments of the gap walk are sums over integer intervals of gaps. -/
theorem certZ_gapKeys_eq (g : ℕ → Ω → ℝ) {j₁ i₁ j₂ i₂ : ℕ} (h₁ : j₁ ≤ i₁) (h₂ : j₂ ≤ i₂)
    (ω : Ω) :
    certZ (gapKeys (seq g ω)) j₁ i₁ j₂ i₂ =
      certSum g (Finset.Ico j₁ i₁) (Finset.Ico j₂ i₂) ω := by
  have hX : ∀ j i, j ≤ i → gapKeys (seq g ω) i - gapKeys (seq g ω) j =
      gsum g (Finset.Ico j i) ω := by
    intro j i hji
    simp only [gapKeys, gsum, seq]
    rw [Finset.sum_Ico_eq_sub _ hji]
  unfold certZ certSum
  rw [hX _ _ h₁, hX _ _ h₂, Nat.card_Ico, Nat.card_Ico, Nat.cast_sub h₁, Nat.cast_sub h₂]

theorem Ico_ne_Ico_of_ne {j₁ i₁ j₂ i₂ : ℕ} (h₁ : j₁ < i₁) (h₂ : j₂ < i₂)
    (hne : (j₁, i₁) ≠ (j₂, i₂)) : Finset.Ico j₁ i₁ ≠ Finset.Ico j₂ i₂ := by
  intro heq
  have key : ∀ x, x ∈ Finset.Ico j₁ i₁ ↔ x ∈ Finset.Ico j₂ i₂ := fun x => by rw [heq]
  have a1 := (key j₁).mp (by simp; omega)
  have a2 := (key j₂).mpr (by simp; omega)
  have a3 := (key (i₁ - 1)).mp (by simp; omega)
  have a4 := (key (i₂ - 1)).mpr (by simp; omega)
  simp only [Finset.mem_Ico] at a1 a2 a3 a4
  exact hne (Prod.ext (by simp only; omega) (by simp only; omega))

/-- **Scale-free certificate smoothing** (`marg:thm:certificate-density`): for the partial-sum
walk of the gaps and distinct index pairs `I = (j₁, i₁)`, `J = (j₂, i₂)`, every interval of
length `h` carries probability at most `32 K h` for the certificate `Z_{I,J}`. -/
theorem LocalGapLaw.certZ_Icc_le {g : ℕ → Ω → ℝ} {μ K : ℝ} (hg : LocalGapLaw P g μ K)
    {j₁ i₁ j₂ i₂ : ℕ} (h₁ : j₁ < i₁) (h₂ : j₂ < i₂) (hne : (j₁, i₁) ≠ (j₂, i₂)) (z h : ℝ) :
    P {ω | certZ (gapKeys (seq g ω)) j₁ i₁ j₂ i₂ ∈ Icc z (z + h)} ≤
      ENNReal.ofReal (32 * K * h) := by
  simp_rw [certZ_gapKeys_eq g h₁.le h₂.le]
  exact hg.certSum_Icc_le (Finset.nonempty_Ico.mpr h₁) (Finset.nonempty_Ico.mpr h₂)
    (Ico_ne_Ico_of_ne h₁ h₂ hne) z h

end Smoothing

/-! ## Fixed-window margin -/

/-- The keys of a walk with positive gaps are strictly increasing. -/
theorem gapKeys_lt_of_pos {g : ℕ → ℝ} (hg : ∀ t, 0 < g t) {j i : ℕ} (hji : j < i) :
    gapKeys g j < gapKeys g i :=
  strictMono_nat_of_lt_succ (fun n => by
    simp only [gapKeys, Finset.sum_range_succ]
    linarith [hg n]) hji

/-- The ordered pairs `(j, i)` with `j < i ≤ n`. -/
def indexPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter (fun p => p.1 < p.2)

theorem mem_indexPairs {n : ℕ} {p : ℕ × ℕ} : p ∈ indexPairs n ↔ p.1 < p.2 ∧ p.2 ≤ n := by
  simp only [indexPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

theorem card_indexPairs_le (n : ℕ) : (indexPairs n).card ≤ n ^ 2 := by
  have h := Finset.card_le_card_of_injOn (s := indexPairs n) (t := Finset.range n ×ˢ Finset.range n)
    (fun p => (p.1, p.2 - 1)) (fun p hp => by
      have := mem_indexPairs.mp hp
      simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
      omega) (fun p hp q hq hpq => by
      have h1 := mem_indexPairs.mp hp
      have h2 := mem_indexPairs.mp hq
      simp only [Prod.mk.injEq] at hpq
      exact Prod.ext hpq.1 (by omega))
  simpa [sq] using h

section Margins

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : ℕ → Ω → ℝ} {μ K : ℝ}

/-- **Fixed-window margin** (`marg:eq:fixed-margin`): the half-width of the first `n + 1`
keys lies within `u` of `a` (in the form `(a + u)`-feasible but not `(a - u)`-feasible) with
probability at most `64 K n^4 u`. -/
theorem LocalGapLaw.fixed_margin (hg : LocalGapLaw P g μ K) (n : ℕ) {a u : ℝ} (hu : 0 < u)
    (hua : u < a) :
    P {ω | prefixAffineFeasible (a + u) (gapKeys (seq g ω)) (n + 1) ∧
        ¬ prefixAffineFeasible (a - u) (gapKeys (seq g ω)) (n + 1)} ≤
      ENNReal.ofReal (64 * K * n ^ 4 * u) := by
  classical
  have hK := hg.K_pos
  set S := indexPairs n ×ˢ indexPairs n with hS
  set F : (ℕ × ℕ) × (ℕ × ℕ) → Set Ω := fun pq =>
    {ω | certZ (gapKeys (seq g ω)) pq.1.1 pq.1.2 pq.2.1 pq.2.2 ∈ Icc (a - u) (a - u + 2 * u)}
    with hF
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | prefixAffineFeasible (a + u) (gapKeys (seq g ω)) (n + 1) ∧
      ¬ prefixAffineFeasible (a - u) (gapKeys (seq g ω)) (n + 1)} → ω ∈ ⋃ pq ∈ S, F pq := by
    filter_upwards [hg.pos_all] with ω hω hmem
    obtain ⟨hfa, hnf⟩ := hmem
    have hx : ∀ j i, j < i → i ≤ n → gapKeys (seq g ω) j < gapKeys (seq g ω) i :=
      fun j i hji _ => gapKeys_lt_of_pos (fun t => hω t) hji
    rw [prefixAffineFeasible_iff_certZ hx (by linarith)] at hfa hnf
    push Not at hnf
    obtain ⟨i₁, j₁, i₂, j₂, h1, h2, h3, h4, hZ⟩ := hnf
    simp only [mem_iUnion]
    refine ⟨((j₁, i₁), (j₂, i₂)), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨mem_indexPairs.mpr ⟨h1, h2⟩, mem_indexPairs.mpr ⟨h3, h4⟩⟩
    · have := hfa i₁ j₁ i₂ j₂ h1 h2 h3 h4
      simp only [hF, mem_ofPred_eq, mem_Icc]
      constructor <;> linarith
  have hterm : ∀ pq ∈ S, P (F pq) ≤ ENNReal.ofReal (32 * K * (2 * u)) := by
    rintro ⟨⟨j₁, i₁⟩, ⟨j₂, i₂⟩⟩ hpq
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have hp' := mem_indexPairs.mp hp
    have hq' := mem_indexPairs.mp hq
    by_cases heq : (j₁, i₁) = (j₂, i₂)
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have : F ((j₁, i₁), (j₁, i₁)) = ∅ := by
        ext ω
        simp only [hF, certZ_self, mem_ofPred_eq, mem_Icc, mem_empty_iff_false, iff_false,
          not_and, not_le]
        intro h
        linarith
      rw [this, measure_empty]
      exact zero_le
    · exact hg.certZ_Icc_le hp'.1 hq'.1 heq (a - u) (2 * u)
  calc P _ ≤ P (⋃ pq ∈ S, F pq) := measure_mono_ae hsub
    _ ≤ ∑ pq ∈ S, P (F pq) := measure_biUnion_finset_le S F
    _ ≤ S.card • ENNReal.ofReal (32 * K * (2 * u)) := Finset.sum_le_card_nsmul S _ _ hterm
    _ = ENNReal.ofReal (S.card * (64 * K * u)) := by
        rw [nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
        ring_nf
    _ ≤ ENNReal.ofReal (64 * K * n ^ 4 * u) := by
        apply ENNReal.ofReal_le_ofReal
        have hc : (S.card : ℝ) ≤ (n : ℝ) ^ 4 := by
          rw [hS, Finset.card_product]
          have := card_indexPairs_le n
          have h2 : (indexPairs n).card * (indexPairs n).card ≤ n ^ 2 * n ^ 2 :=
            Nat.mul_le_mul this this
          have h3 : ((indexPairs n).card * (indexPairs n).card : ℕ) ≤ n ^ 4 := by
            calc _ ≤ n ^ 2 * n ^ 2 := h2
              _ = n ^ 4 := by ring
          exact_mod_cast h3
        have : 0 ≤ 64 * K * u := by positivity
        nlinarith

/-- A near-tie of the first `len` keys at level `eps` with tolerance `u`: they are
`(eps + u)`-feasible but not `(eps - u)`-feasible. -/
def nearTie (eps u : ℝ) (keys : ℕ → ℝ) (len : ℕ) : Prop :=
  prefixAffineFeasible (eps + u) keys len ∧ ¬ prefixAffineFeasible (eps - u) keys len

/-- The first failure happens at `t`: the first `t` keys are `eps`-feasible and the first
`t + 1` keys are not (`T = t` in `marg:cor:base-margin`). -/
def firstFailureAt (eps : ℝ) (keys : ℕ → ℝ) (t : ℕ) : Prop :=
  prefixAffineFeasible eps keys t ∧ ¬ prefixAffineFeasible eps keys (t + 1)

theorem not_nearTie_zero (eps u : ℝ) (keys : ℕ → ℝ) : ¬ nearTie eps u keys 0 :=
  fun h => h.2 (prefixAffineFeasible_zero _ _)

omit [MeasurableSpace Ω] in
/-- The first failure happens at `t` exactly when the ALG-OPT segment length is `t`. -/
theorem firstFailureAt_iff_segLen_eq {eps : ℝ} {p : ℕ → ℝ} {t : ℕ} :
    firstFailureAt eps p t ↔ segLen eps p = t := by
  constructor
  · rintro ⟨hf, hnf⟩
    refine le_antisymm ((segLen_le_iff t).mpr hnf) ?_
    rcases t with _ | s
    · exact bot_le
    · have := (lt_segLen_iff s).mpr hf
      push_cast
      exact Order.add_one_le_of_lt this
  · intro h
    refine ⟨?_, (segLen_le_iff t).mp h.le⟩
    rcases t with _ | s
    · exact prefixAffineFeasible_zero _ _
    · refine (lt_segLen_iff s).mp ?_
      rw [h]
      exact_mod_cast Nat.lt_succ_self s

/-- **Stopped margin** (`marg:cor:base-margin`, `marg:cor:hier-margin`).  Let `T` be the first
failure of `eps`-feasibility and assume the tail bound `P (T > R) ≤ C₀ exp (-c₀ R / eps²)`,
written as `P (first R + 1 keys are eps-feasible) ≤ …`.  Then the probability of a near-tie
of tolerance `u` for the first `T` or the first `T + 1` keys is at most
`64 (1/c₀ + 2)^5 K eps^10 u (1 + log (1/u))^5 + C₀ u`. -/
theorem LocalGapLaw.stopped_margin (hg : LocalGapLaw P g μ K) {eps u C₀ c₀ : ℝ}
    (heps : 1 ≤ eps) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (hC₀ : 0 ≤ C₀) (hc₀ : 0 < c₀)
    (htail : ∀ R : ℕ, 1 ≤ R → P {ω | prefixAffineFeasible eps (gapKeys (seq g ω)) (R + 1)} ≤
      ENNReal.ofReal (C₀ * Real.exp (-(c₀ * R / eps ^ 2)))) :
    P {ω | ∃ t, firstFailureAt eps (gapKeys (seq g ω)) t ∧
        (nearTie eps u (gapKeys (seq g ω)) t ∨ nearTie eps u (gapKeys (seq g ω)) (t + 1))} ≤
      ENNReal.ofReal (64 * (1 / c₀ + 2) ^ 5 * K * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 +
        C₀ * u) := by
  have hK := hg.K_pos
  set L : ℝ := 1 + Real.log (1 / u) with hL
  have hlog : 0 ≤ Real.log (1 / u) := Real.log_nonneg (by rw [le_div_iff₀ hu]; linarith)
  have hL1 : 1 ≤ L := by linarith
  have heps2 : 1 ≤ eps ^ 2 := by nlinarith
  set x : ℝ := eps ^ 2 * L / c₀ with hx
  have hxpos : 0 < x := by positivity
  have hx0 : 0 ≤ x := hxpos.le
  set R : ℕ := ⌈x⌉₊ with hR
  have hRx : x ≤ R := Nat.le_ceil x
  have hRx' : (R : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  set keys : Ω → ℕ → ℝ := fun ω => gapKeys (seq g ω) with hkeys
  -- decomposition of the event
  have hsub : {ω | ∃ t, firstFailureAt eps (keys ω) t ∧
      (nearTie eps u (keys ω) t ∨ nearTie eps u (keys ω) (t + 1))} ⊆
      {ω | prefixAffineFeasible eps (keys ω) (R + 1)} ∪
        ⋃ m ∈ Finset.range (R + 1), {ω | nearTie eps u (keys ω) (m + 1)} := by
    rintro ω ⟨t, ⟨hft, _⟩, hnt⟩
    by_cases htR : R + 1 ≤ t
    · left
      exact prefixAffineFeasible_mono hft htR
    · right
      simp only [mem_iUnion, Finset.mem_range, exists_prop]
      rcases hnt with hnt | hnt
      · rcases Nat.eq_zero_or_pos t with rfl | ht0
        · exact absurd hnt (not_nearTie_zero _ _ _)
        · refine ⟨t - 1, by omega, ?_⟩
          rw [Nat.sub_add_cancel ht0]
          exact hnt
      · exact ⟨t, by omega, hnt⟩
  have hterm : ∀ m ∈ Finset.range (R + 1),
      P {ω | nearTie eps u (keys ω) (m + 1)} ≤ ENNReal.ofReal (64 * K * R ^ 4 * u) := by
    intro m hm
    have hmR : (m : ℝ) ≤ R := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    refine (hg.fixed_margin m hu (by linarith)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : (m : ℝ) ^ 4 ≤ (R : ℝ) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmR 4
    have : 0 ≤ 64 * K * u := by positivity
    nlinarith
  have htail' : P {ω | prefixAffineFeasible eps (keys ω) (R + 1)} ≤ ENNReal.ofReal (C₀ * u) := by
    have hR1 : 1 ≤ R := Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (Nat.ceil_pos.mpr hxpos))
    refine (htail R hR1).trans (ENNReal.ofReal_le_ofReal ?_)
    refine mul_le_mul_of_nonneg_left ?_ hC₀
    have h1 : L ≤ c₀ * R / eps ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have : c₀ * x = eps ^ 2 * L := by rw [hx]; field_simp
      nlinarith
    calc Real.exp (-(c₀ * R / eps ^ 2)) ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp (-1) * u := by
          rw [hL, neg_add, Real.exp_add, Real.log_div one_ne_zero hu.ne', Real.log_one,
            zero_sub, neg_neg, Real.exp_log hu]
      _ ≤ u := by
          have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
          nlinarith
  have hR1 : (R : ℝ) + 1 ≤ (1 / c₀ + 2) * eps ^ 2 * L := by
    have : x = 1 / c₀ * (eps ^ 2 * L) := by rw [hx]; ring
    have h1 : 1 ≤ eps ^ 2 * L := by nlinarith
    nlinarith
  calc P {ω | ∃ t, firstFailureAt eps (keys ω) t ∧
        (nearTie eps u (keys ω) t ∨ nearTie eps u (keys ω) (t + 1))}
      ≤ P ({ω | prefixAffineFeasible eps (keys ω) (R + 1)} ∪
        ⋃ m ∈ Finset.range (R + 1), {ω | nearTie eps u (keys ω) (m + 1)}) := measure_mono hsub
    _ ≤ P {ω | prefixAffineFeasible eps (keys ω) (R + 1)} +
        ∑ m ∈ Finset.range (R + 1), P {ω | nearTie eps u (keys ω) (m + 1)} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_biUnion_finset_le _ _))
    _ ≤ ENNReal.ofReal (C₀ * u) + (Finset.range (R + 1)).card • ENNReal.ofReal (64 * K * R ^ 4 * u) :=
        add_le_add htail' (Finset.sum_le_card_nsmul _ _ _ hterm)
    _ = ENNReal.ofReal (C₀ * u + (R + 1) * (64 * K * R ^ 4 * u)) := by
        rw [Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (p := (R : ℝ) + 1) (by positivity)]
        congr
        rw [← Nat.cast_succ, ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (64 * (1 / c₀ + 2) ^ 5 * K * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 +
        C₀ * u) := by
        apply ENNReal.ofReal_le_ofReal
        have h5 : ((R : ℝ) + 1) ^ 5 ≤ ((1 / c₀ + 2) * eps ^ 2 * L) ^ 5 :=
          pow_le_pow_left₀ (by positivity) hR1 5
        have hR4 : (R + 1) * (R : ℝ) ^ 4 ≤ ((R : ℝ) + 1) ^ 5 := by
          have : (R : ℝ) ^ 4 ≤ ((R : ℝ) + 1) ^ 4 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) 4
          nlinarith [pow_nonneg (Nat.cast_nonneg R : (0:ℝ) ≤ R) 4]
        have hK' : 0 ≤ 64 * K * u := by positivity
        have : ((1 / c₀ + 2) * eps ^ 2 * L) ^ 5 = (1 / c₀ + 2) ^ 5 * eps ^ 10 * L ^ 5 := by ring
        rw [← hL]
        nlinarith

/-- `stopped_margin` with `T = gapSegLen eps (seq g ω)` the ALG-OPT segment length. -/
theorem LocalGapLaw.stopped_margin_segLen (hg : LocalGapLaw P g μ K) {eps u C₀ c₀ : ℝ}
    (heps : 1 ≤ eps) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (hC₀ : 0 ≤ C₀) (hc₀ : 0 < c₀)
    (htail : ∀ R : ℕ, 1 ≤ R → P {ω | (R : ℕ∞) < gapSegLen eps (seq g ω)} ≤
      ENNReal.ofReal (C₀ * Real.exp (-(c₀ * R / eps ^ 2)))) :
    P {ω | ∃ t : ℕ, gapSegLen eps (seq g ω) = t ∧
        (nearTie eps u (gapKeys (seq g ω)) t ∨ nearTie eps u (gapKeys (seq g ω)) (t + 1))} ≤
      ENNReal.ofReal (64 * (1 / c₀ + 2) ^ 5 * K * eps ^ 10 * u * (1 + Real.log (1 / u)) ^ 5 +
        C₀ * u) := by
  have h := hg.stopped_margin heps hu hu2 hC₀ hc₀ (fun R hR => by
    have := htail R hR
    simp only [gapSegLen, lt_segLen_iff] at this
    exact this)
  simp only [gapSegLen, ← firstFailureAt_iff_segLen_eq]
  exact h

end Margins

/-! ## Poissonisation -/

/-- The `Gamma(k + 1, 1)` density at `x ≥ 0` is the `Poisson(x)` point probability at `k`. -/
theorem gammaPDFReal_succ_one {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    gammaPDFReal ((k + 1 : ℕ) : ℝ) 1 x = Real.exp (-x) * x ^ k / (k.factorial : ℝ) := by
  rw [gammaPDFReal, if_pos hx, Real.one_rpow, Nat.cast_succ, Real.Gamma_nat_eq_factorial,
    add_sub_cancel_right, Real.rpow_natCast, one_mul]
  ring

theorem gammaPDFReal_zero_one (x : ℝ) : gammaPDFReal 0 1 x = 0 := by
  simp [gammaPDFReal, Real.Gamma_zero]

theorem gammaPDFReal_nat_nonneg (m : ℕ) (x : ℝ) : 0 ≤ gammaPDFReal m 1 x := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [gammaPDFReal_zero_one]
  · exact gammaPDFReal_nonneg (by exact_mod_cast hm) one_pos x

/-- The `Gamma(m, 1)` densities, `m ≥ 1`, sum to at most one at every point. -/
theorem tsum_gammaPDF_le_one (x : ℝ) : ∑' m : ℕ, gammaPDF m 1 x ≤ 1 := by
  rcases lt_or_ge x 0 with hx | hx
  · simp [gammaPDF, gammaPDFReal, not_le.mpr hx]
  · have h2 : HasSum (fun k : ℕ => gammaPDFReal ((k + 1 : ℕ) : ℝ) 1 x) 1 := by
      have h1 := hasSum_one_poissonMeasure ⟨x, hx⟩
      convert h1 using 1
      funext k
      rw [gammaPDFReal_succ_one hx]
      rfl
    have hsum : HasSum (fun m : ℕ => gammaPDFReal m 1 x) 1 := by
      have := (hasSum_nat_add_iff (f := fun m : ℕ => gammaPDFReal m 1 x) 1).mp h2
      simpa [gammaPDFReal_zero_one] using this
    simp only [gammaPDF]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => gammaPDFReal_nat_nonneg m x) hsum.summable,
      hsum.tsum_eq, ENNReal.ofReal_one]

section Poisson

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Poissonisation** (`marg:lem:poissonisation`): if `(g, N)` has the Gamma kernel
`P (g ∈ A, N = m) = P (N = m) · Gamma(m, 1)(A)` and `N ≥ 1` almost surely, then
`P (g ∈ A) ≤ (sup_m P (N = m)) · |A|`. -/
theorem poissonisation_bound {g : Ω → ℝ} {N : Ω → ℕ} (hN0 : P (N ⁻¹' {0}) = 0)
    (hker : ∀ m : ℕ, 0 < m → ∀ A : Set ℝ, MeasurableSet A →
      P (g ⁻¹' A ∩ N ⁻¹' {m}) = P (N ⁻¹' {m}) * gammaMeasure m 1 A)
    (A : Set ℝ) (hA : MeasurableSet A) :
    P (g ⁻¹' A) ≤ (⨆ m, P (N ⁻¹' {m})) * volume A := by
  set s := ⨆ m, P (N ⁻¹' {m}) with hs
  have hcover : g ⁻¹' A ⊆ ⋃ m : ℕ, g ⁻¹' A ∩ N ⁻¹' {m} := fun ω hω =>
    mem_iUnion.mpr ⟨N ω, hω, rfl⟩
  have hterm : ∀ m : ℕ, P (g ⁻¹' A ∩ N ⁻¹' {m}) ≤ s * gammaMeasure m 1 A := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · calc P (g ⁻¹' A ∩ N ⁻¹' {0}) ≤ P (N ⁻¹' {0}) := measure_mono inter_subset_right
        _ = 0 := hN0
        _ ≤ _ := zero_le
    · rw [hker m hm A hA]
      gcongr
      exact le_iSup (fun m => P (N ⁻¹' {m})) m
  have hgam : ∑' m : ℕ, gammaMeasure m 1 A ≤ volume A := by
    have hmeas : ∀ m : ℕ, Measurable (gammaPDF m 1) := fun m =>
      (measurable_gammaPDFReal _ _).ennreal_ofReal
    simp_rw [gammaMeasure, withDensity_apply _ hA]
    rw [← lintegral_tsum (fun m => (hmeas m).aemeasurable)]
    calc ∫⁻ x in A, ∑' m : ℕ, gammaPDF m 1 x ≤ ∫⁻ _ in A, 1 :=
          lintegral_mono fun x => tsum_gammaPDF_le_one x
      _ = volume A := by simp
  calc P (g ⁻¹' A) ≤ P (⋃ m : ℕ, g ⁻¹' A ∩ N ⁻¹' {m}) := measure_mono hcover
    _ ≤ ∑' m : ℕ, P (g ⁻¹' A ∩ N ⁻¹' {m}) := measure_iUnion_le _
    _ ≤ ∑' m : ℕ, s * gammaMeasure m 1 A := ENNReal.tsum_le_tsum hterm
    _ = s * ∑' m : ℕ, gammaMeasure m 1 A := ENNReal.tsum_mul_left
    _ ≤ s * volume A := by gcongr

/-- An iid gap sequence whose first gap has the Gamma kernel satisfies the local bound with
`K = μ · sup_m P (N = m)` (the constant `K_ℓ` of `marg:cor:hier-margin`). -/
theorem localGapLaw_of_gammaKernel {g : ℕ → Ω → ℝ} {N : Ω → ℕ} {μ : ℝ} (hiid : IIDSeq P g)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (hmean : ∫ ω, g 0 ω ∂P = μ) (hμ : 0 < μ)
    (hN0 : P (N ⁻¹' {0}) = 0)
    (hker : ∀ m : ℕ, 0 < m → ∀ A : Set ℝ, MeasurableSet A →
      P (g 0 ⁻¹' A ∩ N ⁻¹' {m}) = P (N ⁻¹' {m}) * gammaMeasure m 1 A) :
    LocalGapLaw P g μ (μ * (⨆ m, P (N ⁻¹' {m})).toReal) where
  iid := hiid
  pos := hpos
  mean := hmean
  mu_pos := hμ
  local_bound A hA := by
    have := hiid.indep.isProbabilityMeasure
    have hfin : (⨆ m, P (N ⁻¹' {m})) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun m => prob_le_one)
    rw [mul_div_cancel_left₀ _ hμ.ne', ENNReal.ofReal_toReal hfin]
    exact poissonisation_bound hN0 hker A hA

/-- **Hierarchy margin** (`marg:cor:hier-margin`): for gaps with the Gamma kernel and the
uniform segment-length tail, the stopped near-tie probability is at most
`64 (1/c₀ + 2)^5 K eps^10 u (1 + log (1/u))^5 + C₀ u` with `K = μ · sup_m P (N = m)`. -/
theorem hier_margin {g : ℕ → Ω → ℝ} {N : Ω → ℕ} {μ : ℝ} (hiid : IIDSeq P g)
    (hpos : ∀ᵐ ω ∂P, 0 < g 0 ω) (hmean : ∫ ω, g 0 ω ∂P = μ) (hμ : 0 < μ)
    (hN0 : P (N ⁻¹' {0}) = 0)
    (hker : ∀ m : ℕ, 0 < m → ∀ A : Set ℝ, MeasurableSet A →
      P (g 0 ⁻¹' A ∩ N ⁻¹' {m}) = P (N ⁻¹' {m}) * gammaMeasure m 1 A)
    {eps u C₀ c₀ : ℝ} (heps : 1 ≤ eps) (hu : 0 < u) (hu2 : u ≤ 1 / 2) (hC₀ : 0 ≤ C₀)
    (hc₀ : 0 < c₀)
    (htail : ∀ R : ℕ, 1 ≤ R → P {ω | prefixAffineFeasible eps (gapKeys (seq g ω)) (R + 1)} ≤
      ENNReal.ofReal (C₀ * Real.exp (-(c₀ * R / eps ^ 2)))) :
    P {ω | ∃ t, firstFailureAt eps (gapKeys (seq g ω)) t ∧
        (nearTie eps u (gapKeys (seq g ω)) t ∨ nearTie eps u (gapKeys (seq g ω)) (t + 1))} ≤
      ENNReal.ofReal (64 * (1 / c₀ + 2) ^ 5 * (μ * (⨆ m, P (N ⁻¹' {m})).toReal) * eps ^ 10 * u *
        (1 + Real.log (1 / u)) ^ 5 + C₀ * u) :=
  (localGapLaw_of_gammaKernel hiid hpos hmean hμ hN0 hker).stopped_margin heps hu hu2 hC₀ hc₀
    htail

end Poisson

end PGM
