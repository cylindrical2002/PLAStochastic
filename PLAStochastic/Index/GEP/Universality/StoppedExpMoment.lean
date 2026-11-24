import PLAStochastic.Index.GEP.Universality.LayerTail
import PLAStochastic.Index.GEP.Universality.PerIntegerSandwich

/-!
# WP5, D4: the stopped exponential moment

Blueprint `kmt-blueprint/main.tex` Lemma 8.7 (`lem:stopexp`), on the canonical space:
for iid positive mean-one gaps with `E e^{θX} ≤ B`, the ALG-OPT segment length `T` and
`S_T = ∑_{i<T} X_i`,

  `E e^{λ S_T} ≤ (E e^{4λ T})^{1/2}`   for `0 < λ ≤ min(θ/4, θ²/(16 B))`.

Proof.  `Z_k = e^{2λ S_k} m(2λ)^{-k}` is a product martingale; `E Z_{T∧k} = 1` by induction,
using the independence of `X_k` from `F_k` (one lower-integral product identity, no
integrability bookkeeping); Fatou gives `E Z_T ≤ 1`; Hölder with `p = q = 2` gives the claim,
and `m(2λ) ≤ e^{4λ}` is `integral_exp_mul_le_of_expMom`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

/-! ## The product martingale and its stopped version -/

/-- `e^{λ S_k} / m^k`. -/
def zReal (lam m : ℝ) (k : ℕ) (g : ℕ → ℝ) : ℝ := Real.exp (lam * gapKeys g k) / m ^ k

/-- `Z_{T ∧ k}`. -/
def zStop (eps lam m : ℝ) (k : ℕ) (g : ℕ → ℝ) : ℝ :=
  if (k : ℕ∞) < gapSegLen eps g then zReal lam m k g else zReal lam m (gapSegLen eps g).toNat g

theorem zReal_nonneg {lam m : ℝ} (hm : 0 < m) (k : ℕ) (g : ℕ → ℝ) : 0 ≤ zReal lam m k g := by
  unfold zReal; positivity

theorem zStop_nonneg {eps lam m : ℝ} (hm : 0 < m) (k : ℕ) (g : ℕ → ℝ) : 0 ≤ zStop eps lam m k g := by
  unfold zStop; split_ifs <;> exact zReal_nonneg hm _ _

theorem zReal_zero (lam m : ℝ) (g : ℕ → ℝ) : zReal lam m 0 g = 1 := by
  simp [zReal, gapKeys]

theorem zReal_succ {lam m : ℝ} (hm : 0 < m) (k : ℕ) (g : ℕ → ℝ) :
    zReal lam m (k + 1) g = zReal lam m k g * (Real.exp (lam * g k) / m) := by
  unfold zReal
  rw [gapKeys, Finset.sum_range_succ, ← gapKeys, mul_add, Real.exp_add, pow_succ]
  field_simp

theorem measurable_zReal (lam m : ℝ) (k : ℕ) : Measurable (zReal lam m k) :=
  ((measurable_const.mul (measurable_gapKeys_apply k)).exp).div_const _

theorem measurable_zStop (eps lam m : ℝ) (k : ℕ) : Measurable (zStop eps lam m k) := by
  have hT : Measurable fun g : ℕ → ℝ => (gapSegLen eps g).toNat :=
    measurable_from_top.comp (isStoppingRule_gapSegLen eps).measurable
  have h2 : Measurable fun g : ℕ → ℝ => zReal lam m (gapSegLen eps g).toNat g := by
    have hm : Measurable (fun p : (ℕ → ℝ) × ℕ => zReal lam m p.2 p.1) :=
      measurable_from_prod_countable_left fun n => measurable_zReal lam m n
    exact hm.comp (measurable_id.prodMk hT)
  exact Measurable.ite (measurableSet_lt_gapSegLen eps k) (measurable_zReal lam m k) h2

theorem zStop_zero (eps lam m : ℝ) (g : ℕ → ℝ) : zStop eps lam m 0 g = 1 := by
  unfold zStop
  split_ifs with h
  · exact zReal_zero _ _ _
  · have : gapSegLen eps g = 0 := by
      rcases eq_or_lt_of_le (not_lt.1 h) with h0 | h0
      · exact h0
      · exact absurd h0 (not_lt.2 zero_le)
    rw [this]; exact zReal_zero _ _ _

/-- `Z_{T ∧ (k+1)} = Z_{k+1}` on `{k < T}` and `Z_{T ∧ k}` otherwise. -/
theorem zStop_succ (eps lam m : ℝ) (k : ℕ) (g : ℕ → ℝ) :
    zStop eps lam m (k + 1) g =
      if (k : ℕ∞) < gapSegLen eps g then zReal lam m (k + 1) g else zStop eps lam m k g := by
  unfold zStop
  by_cases hk : (k : ℕ∞) < gapSegLen eps g
  · rw [if_pos hk]
    by_cases hk1 : ((k + 1 : ℕ) : ℕ∞) < gapSegLen eps g
    · rw [if_pos hk1]
    · rw [if_neg hk1]
      have hle : gapSegLen eps g ≤ ((k + 1 : ℕ) : ℕ∞) := not_lt.1 hk1
      have hge : ((k + 1 : ℕ) : ℕ∞) ≤ gapSegLen eps g := by
        exact_mod_cast Order.add_one_le_of_lt hk
      have heq : gapSegLen eps g = ((k + 1 : ℕ) : ℕ∞) := le_antisymm hle hge
      rw [heq, ENat.toNat_natCast]
  · rw [if_neg hk]
    have hk1 : ¬ ((k + 1 : ℕ) : ℕ∞) < gapSegLen eps g := fun h =>
      hk (lt_of_le_of_lt (by exact_mod_cast Nat.le_succ k) h)
    rw [if_neg hk1, if_neg hk]

/-! ## `E Z_{T ∧ k} = 1` -/

variable {ν : ProbabilityMeasure ℝ}

theorem lintegral_exp_gapCoord (ν : ProbabilityMeasure ℝ) (lam : ℝ) (k : ℕ) {m : ℝ}
    (hm : 0 < m) (hmint : Integrable (fun x => Real.exp (lam * x)) (ν : Measure ℝ))
    (hmeq : ∫ x, Real.exp (lam * x) ∂(ν : Measure ℝ) = m) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (lam * g k) / m) ∂(iidLaw ν) = 1 := by
  have hmp := measurePreserving_eval_infinitePi (fun _ : ℕ => (ν : Measure ℝ)) k
  have e : ∫⁻ g, ENNReal.ofReal (Real.exp (lam * g k) / m) ∂(iidLaw ν) =
      ∫⁻ x, ENNReal.ofReal (Real.exp (lam * x) / m) ∂(ν : Measure ℝ) := by
    rw [← hmp.lintegral_comp (by fun_prop)]; rfl
  rw [e, ← ofReal_integral_eq_lintegral_ofReal (hmint.div_const m)
    (ae_of_all _ fun x => by positivity), integral_div, hmeq, div_self hm.ne', ENNReal.ofReal_one]

/-- The product-martingale identity: `E Z_{T ∧ k} = 1` for every `k`. -/
theorem lintegral_zStop_eq_one {vlo vhi κ₃ B θ : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν) (hvlo : 0 < vlo)
    (eps : ℝ) {lam m : ℝ} (hm : 0 < m)
    (hmint : Integrable (fun x => Real.exp (lam * x)) (ν : Measure ℝ))
    (hmeq : ∫ x, Real.exp (lam * x) ∂(ν : Measure ℝ) = m) (k : ℕ) :
    ∫⁻ g, ENNReal.ofReal (zStop eps lam m k g) ∂(iidLaw ν) = 1 := by
  induction k with
  | zero => simp [zStop_zero]
  | succ k ih =>
    have hX := h.gapLaw hvlo
    set P := iidLaw ν with hP
    set F := gapFiltration gapCoord (fun t => measurable_pi_apply t) with hF
    have hset : MeasurableSet[F k] {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} :=
      gapSegLen_lt_measurable (X := gapCoord) (fun t => measurable_pi_apply t) eps k
    have hsetm : MeasurableSet {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g} := F.le k _ hset
    -- the two pieces of `Z_{T ∧ (k+1)}`
    have hsplit : ∀ g, ENNReal.ofReal (zStop eps lam m (k + 1) g) =
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (zReal lam m k g) *
            ENNReal.ofReal (Real.exp (lam * g k) / m)) g +
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}ᶜ.indicator
          (fun g => ENNReal.ofReal (zStop eps lam m k g)) g := by
      intro g
      rw [zStop_succ]
      by_cases hk : (k : ℕ∞) < gapSegLen eps g
      · rw [if_pos hk, Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
          from hk), Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}ᶜ
          from not_not.2 hk), add_zero, zReal_succ hm, ENNReal.ofReal_mul (zReal_nonneg hm _ _)]
      · rw [if_neg hk, Set.indicator_of_notMem (show g ∉ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
          from hk), Set.indicator_of_mem (show g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}ᶜ
          from hk), zero_add]
    -- independence of `1{k < T} Z_k` and `e^{λ X_k}/m`
    have hf : Measurable[F k] fun g : ℕ → ℝ => {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (zReal lam m k g)) g := by
      refine Measurable.indicator ?_ hset
      refine Measurable.ennreal_ofReal ?_
      unfold zReal
      refine Measurable.div_const ?_ _
      refine Measurable.exp ?_
      refine Measurable.const_mul ?_ _
      refine Finset.measurable_sum _ fun i hi => ?_
      exact gapFiltration_measurable_lt (X := gapCoord) (fun t => measurable_pi_apply t)
        (Finset.mem_range.1 hi)
    have hgm : Measurable fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (lam * g k) / m) :=
      ((measurable_const.mul (measurable_pi_apply k)).exp.div_const m).ennreal_ofReal
    have hfmeas : Measurable fun g : ℕ → ℝ => ENNReal.ofReal (zReal lam m k g) :=
      (measurable_zReal lam m k).ennreal_ofReal
    have hg : Measurable[MeasurableSpace.comap (centred gapCoord 1 k) inferInstance]
        fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (lam * g k) / m) := by
      have : (fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (lam * g k) / m)) =
          (fun y : ℝ => ENNReal.ofReal (Real.exp (lam * (y + 1)) / m)) ∘ centred gapCoord 1 k := by
        funext g; simp [centred, gapCoord]
      rw [this]
      exact (Measurable.ennreal_ofReal (by fun_prop)).comp (comap_measurable _)
    have hind : IndepFun
        (fun g : ℕ → ℝ => {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (zReal lam m k g)) g)
        (fun g : ℕ → ℝ => ENNReal.ofReal (Real.exp (lam * g k) / m)) P := by
      rw [IndepFun_iff_Indep]
      have h0 := (hX.indepIncrements.indep k).symm
      exact indep_of_indep_of_le_right (indep_of_indep_of_le_left h0 hf.comap_le) hg.comap_le
    have hprod : ∫⁻ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (zReal lam m k g) *
          ENNReal.ofReal (Real.exp (lam * g k) / m)) g ∂P =
        ∫⁻ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (zReal lam m k g)) g ∂P := by
      have e : ∀ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (zReal lam m k g) *
            ENNReal.ofReal (Real.exp (lam * g k) / m)) g =
          {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
            (fun g => ENNReal.ofReal (zReal lam m k g)) g *
            ENNReal.ofReal (Real.exp (lam * g k) / m) := by
        intro g
        by_cases hk : g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
        · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
        · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk, zero_mul]
      simp_rw [e]
      rw [lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hf.mono (F.le k) le_rfl).aemeasurable
        hgm.aemeasurable hind, lintegral_exp_gapCoord ν lam k hm hmint hmeq, mul_one]
    -- on `{k < T}`, `Z_k = Z_{T ∧ k}`
    have hsame : ∀ g, {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (zReal lam m k g)) g =
        {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
          (fun g => ENNReal.ofReal (zStop eps lam m k g)) g := by
      intro g
      by_cases hk : g ∈ {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}
      · rw [Set.indicator_of_mem hk, Set.indicator_of_mem hk]
        unfold zStop
        rw [if_pos (show (k : ℕ∞) < gapSegLen eps g from hk)]
      · rw [Set.indicator_of_notMem hk, Set.indicator_of_notMem hk]
    simp_rw [hsplit]
    have hfm2 : Measurable fun g : ℕ → ℝ => {g : ℕ → ℝ | (k : ℕ∞) < gapSegLen eps g}.indicator
        (fun g => ENNReal.ofReal (zReal lam m k g) *
          ENNReal.ofReal (Real.exp (lam * g k) / m)) g :=
      (hfmeas.mul hgm).indicator hsetm
    rw [lintegral_add_left hfm2, hprod]
    simp_rw [hsame]
    rw [← lintegral_add_left ((measurable_zStop eps lam m k).ennreal_ofReal.indicator hsetm)]
    rw [← ih]
    refine lintegral_congr fun g => ?_
    rw [Set.indicator_self_add_compl_apply]

/-! ## Fatou and Hölder -/

/-- `E Z_T ≤ 1`. -/
theorem lintegral_zReal_stop_le_one {vlo vhi κ₃ B θ : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps) {lam m : ℝ}
    (hm : 0 < m) (hmint : Integrable (fun x => Real.exp (lam * x)) (ν : Measure ℝ))
    (hmeq : ∫ x, Real.exp (lam * x) ∂(ν : Measure ℝ) = m) :
    ∫⁻ g, ENNReal.ofReal (zReal lam m (gapSegLen eps g).toNat g) ∂(iidLaw ν) ≤ 1 := by
  have hfin := (h.oneLayer hvlo heps).1
  have hlim : ∀ᵐ g ∂(iidLaw ν), ENNReal.ofReal (zReal lam m (gapSegLen eps g).toNat g) =
      liminf (fun k => ENNReal.ofReal (zStop eps lam m k g)) atTop := by
    filter_upwards [hfin] with g hg
    obtain ⟨t, ht⟩ := ENat.ne_top_iff_exists.1 hg
    have hev : ∀ᶠ k in atTop, ENNReal.ofReal (zStop eps lam m k g) =
        ENNReal.ofReal (zReal lam m (gapSegLen eps g).toNat g) := by
      rw [eventually_atTop]
      refine ⟨t, fun k hk => ?_⟩
      unfold zStop
      rw [if_neg]
      rw [← ht]
      exact not_lt.2 (by exact_mod_cast hk)
    exact (Filter.Tendsto.liminf_eq (tendsto_const_nhds.congr' (hev.mono fun k hk => hk.symm))).symm
  rw [lintegral_congr_ae hlim]
  refine (lintegral_liminf_le fun k => (measurable_zStop eps lam m k).ennreal_ofReal).trans ?_
  have : ∀ k, ∫⁻ g, ENNReal.ofReal (zStop eps lam m k g) ∂(iidLaw ν) = 1 :=
    lintegral_zStop_eq_one h hvlo eps hm hmint hmeq
  simp_rw [this]
  rw [liminf_const]

/-- **Stopped exponential moment** (blueprint Lemma 8.7):
`E e^{λ S_T} ≤ (E e^{4λ T})^{1/2}` for `0 < λ ≤ min(θ/4, θ²/(16B))`. -/
theorem lintegral_exp_stopSum_le {vlo vhi κ₃ B θ : ℝ} (h : UnivClass vlo vhi κ₃ B θ ν)
    (hvlo : 0 < vlo) (hθ : 0 < θ) {eps : ℝ} (heps : epsZero vhi (univBeta vlo κ₃) ≤ eps)
    {lam : ℝ} (hlam : 0 < lam) (hlamθ : lam ≤ θ / 4) (hlamB : lam ≤ θ ^ 2 / (16 * B)) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (lam * stopSum eps g)) ∂(iidLaw ν) ≤
      (∫⁻ g, ENNReal.ofReal (Real.exp (4 * lam * ((gapSegLen eps g).toNat : ℝ)))
        ∂(iidLaw ν)) ^ ((1 : ℝ) / 2) := by
  have hB := h.B_pos
  -- `m = E e^{2λ X} ≤ e^{4λ}`
  obtain ⟨hmint, hmle⟩ := integral_exp_mul_le_of_expMom (P := (ν : Measure ℝ)) (X := id) hθ
    (h.ae_pos.mono fun x hx => hx.le) (h.memLp3.integrable (by norm_num)) (le_of_eq h.mean)
    h.expMom'.integrable h.expMom'.le (θ := 2 * lam) (by positivity) (by linarith)
  set m := ∫ x, Real.exp (2 * lam * x) ∂(ν : Measure ℝ) with hmdef
  have hm : 0 < m := integral_exp_pos hmint
  have hm4 : m ≤ Real.exp (4 * lam) := by
    refine hmle.trans (Real.exp_le_exp.2 ?_)
    have : 8 * B / θ ^ 2 * (2 * lam) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hlamB
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 2 * lam)]
  have hZ := lintegral_zReal_stop_le_one h hvlo heps hm hmint rfl
  -- Hölder with `p = q = 2`
  set f : (ℕ → ℝ) → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (zReal (2 * lam) m (gapSegLen eps g).toNat g) ^ ((1 : ℝ) / 2) with hfdef
  set gg : (ℕ → ℝ) → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (m ^ (gapSegLen eps g).toNat) ^ ((1 : ℝ) / 2) with hgdef
  have hT : Measurable fun g : ℕ → ℝ => (gapSegLen eps g).toNat :=
    measurable_from_top.comp (isStoppingRule_gapSegLen eps).measurable
  have hzT : Measurable fun g : ℕ → ℝ => zReal (2 * lam) m (gapSegLen eps g).toNat g := by
    have hm' : Measurable (fun p : (ℕ → ℝ) × ℕ => zReal (2 * lam) m p.2 p.1) :=
      measurable_from_prod_countable_left fun n => measurable_zReal _ m n
    exact hm'.comp (measurable_id.prodMk hT)
  have hfm : Measurable f := hzT.ennreal_ofReal.pow_const _
  have hgm : Measurable gg :=
    ((Measurable.of_discrete (f := fun n : ℕ => m ^ n)).comp hT).ennreal_ofReal.pow_const _
  have hfg : ∀ g, ENNReal.ofReal (Real.exp (lam * stopSum eps g)) = (f * gg) g := by
    intro g
    simp only [Pi.mul_apply, hfdef, hgdef]
    rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.ofReal_mul (zReal_nonneg hm _ _)]
    have hmT : 0 < m ^ (gapSegLen eps g).toNat := by positivity
    have e1 : zReal (2 * lam) m (gapSegLen eps g).toNat g * m ^ (gapSegLen eps g).toNat =
        Real.exp (lam * stopSum eps g) ^ 2 := by
      unfold zReal stopSum
      rw [div_mul_cancel₀ _ hmT.ne', ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e1, ← Real.rpow_natCast, ← ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num),
      ← ENNReal.rpow_mul]
    norm_num
  simp_rw [hfg]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq (iidLaw ν) (Real.HolderConjugate.two_two)
    hfm.aemeasurable hgm.aemeasurable).trans ?_
  have e2 : ∀ g, f g ^ (2 : ℝ) = ENNReal.ofReal (zReal (2 * lam) m (gapSegLen eps g).toNat g) := by
    intro g
    simp only [hfdef]
    rw [← ENNReal.rpow_mul]; norm_num
  have e3 : ∀ g, gg g ^ (2 : ℝ) = ENNReal.ofReal (m ^ (gapSegLen eps g).toNat) := by
    intro g
    simp only [hgdef]
    rw [← ENNReal.rpow_mul]; norm_num
  simp_rw [e2, e3]
  calc (∫⁻ g, ENNReal.ofReal (zReal (2 * lam) m (gapSegLen eps g).toNat g) ∂(iidLaw ν)) ^ (1 / (2 : ℝ)) *
        (∫⁻ g, ENNReal.ofReal (m ^ (gapSegLen eps g).toNat) ∂(iidLaw ν)) ^ (1 / (2 : ℝ))
      ≤ 1 ^ (1 / (2 : ℝ)) *
        (∫⁻ g, ENNReal.ofReal (Real.exp (4 * lam * ((gapSegLen eps g).toNat : ℝ))) ∂(iidLaw ν)) ^
          (1 / (2 : ℝ)) := by
        gcongr with g
        rw [mul_comm (4 * lam), Real.exp_nat_mul]
        exact pow_le_pow_left₀ hm.le hm4 _
    _ = _ := by rw [ENNReal.one_rpow, one_mul]

end

end PGM
