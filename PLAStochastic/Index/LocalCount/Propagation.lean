import PLAStochastic.Index.LocalCount.CyclicEarlyMark
import PLAStochastic.Index.Endpoint.HyperSegmentMoments
import PLAStochastic.Index.Endpoint.ReferenceNodes

/-!
# Local-count propagation through the reference hierarchy

Source: `theory/proofs/proofK_local_count_core.tex` (`klc:thm:stopped-propagation`,
`klc:lem:cyclic-early-mark`, `klc:thm:constant-propagation`, `klc:cor:hierarchy`).

Standing hypotheses on one layer (`LocalCountHyp P Z m θ B B₂`, in `PLAStochastic.Index.LocalCount.Decomposition`): `Z`
is an iid pair sequence with counts `N ≥ 1`, the Gamma kernel, `E N = m > 0`,
`E exp(θ N/m) ≤ B` and `E N² ≤ B₂ m²`.  The stop `T = pairSegLen eps (seq Z ·)` is then almost
surely finite.  Write `p = cntAtom P Z = sup_q P(N = q)` (`cntAtom_eq_iSup`) and
`N⁺ = (nextLayer eps Z 0).2`, `p⁺ = cntAtom P (nextLayer eps Z)`.

* Decomposition (`PLAStochastic.Index.LocalCount.Decomposition`): `measure_nextCount_eq_tsum`,
  `P(N⁺ = k) = ∑' t, P(T = t ∧ S_t = k)`, and `measure_pairRank_eq_convFin`,
  `P(S_t = k) = convFin t (law N) {k}`.
* Cyclic early mark (`PLAStochastic.Index.LocalCount.CyclicEarlyMark`): `cyclic_early_mark`, for `p ≤ 1/2`, `eps ≥ 1`,
  `P(T = t, S_t = k) ≤ 7168 p t^{-3/2} exp(-(c/36) eps²/t)`, `c = bernsteinRate θ B`.
* `constant_propagation` (klc:thm:constant-propagation): `p ≤ 1/2`, `eps ≥ 2` give
  `p⁺ ≤ propConst θ B B₂ · p / eps²`.
* `log_transition_stop`, `log_transition` (klc:thm:stopped-propagation at a layer with
  `N ≡ 1`, so `N⁺ = T`): `P(T = t) ≤ logConst θ B · log(e eps²)/eps²` for every `t`, hence the
  same bound for `p⁺`.  With deterministic counts the decomposition over `t` has the single
  term `t = k`, so the bound is proved pointwise from `P(T = t) ≤ 2/t` (marked cyclic two) and
  `P(T ≤ t) ≤ 2 exp(-c eps²/t)` (early stop) instead of through the dyadic block sum.
* `local_count_hierarchy` (klc:cor:hierarchy): on the exponential reference hierarchy
  `W ℓ = epLayerSeq eps g ℓ` (`g` iid `Exp(1)`, `H : RefHyp P g b β vmin Kc eps`), with
  `π ℓ = cntAtom P (W ℓ) = sup_k P(N^{(ℓ)} = k)` and `K ℓ = lcount P (W ℓ) · π ℓ`, for
  `eps ≥ hierEps`:
  `π 1 ≤ logConst θK CK · log(e eps²)/eps²`, `π ℓ ≤ 1/2` and
  `π (ℓ+1) ≤ propConst θK CK (2 CK/θK²) · π ℓ / eps²` for `ℓ ≥ 1`, and
  `K ℓ ≤ hierConst vmin ^ ℓ · log(e eps²)` for `ℓ ≥ 1`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset LocalCountBase LocalCount
open scoped ENNReal

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

/-! ## Constants -/

/-- The constant of the constant-loss propagation:
`32·224·max(1, 4B₂) · (100/c' + 16/c'²) + 2 max(2, 1 + 240·224·max(1, 4B₂))` with
`c' = cycRate θ B = bernsteinRate θ B / 36`. -/
def propConst (θ B B₂ : ℝ) : ℝ :=
  32 * 224 * max 1 (4 * B₂) * (100 / cycRate θ B + 16 / cycRate θ B ^ 2) +
    2 * max 2 (1 + 240 * 224 * max 1 (4 * B₂))

/-- The constant of the logarithmic transition: `2 max(1, 1/c)`, `c = bernsteinRate θ B`. -/
def logConst (θ B : ℝ) : ℝ := 2 * max 1 (1 / bernsteinRate θ B)

theorem propConst_pos {θ B B₂ : ℝ} (hθ : 0 < θ) (hB : 0 < B) : 0 < propConst θ B B₂ := by
  unfold propConst
  have := cycRate_pos hθ hB
  have h1 : (0 : ℝ) < max 1 (4 * B₂) := lt_max_of_lt_left one_pos
  have h2 : (0 : ℝ) < max 2 (1 + 240 * 224 * max 1 (4 * B₂)) := lt_max_of_lt_left two_pos
  positivity

theorem two_le_logConst (θ B : ℝ) : 2 ≤ logConst θ B := by
  unfold logConst; have := le_max_left (1 : ℝ) (1 / bernsteinRate θ B); linarith

theorem one_le_logConst (θ B : ℝ) : 1 ≤ logConst θ B := le_trans one_le_two (two_le_logConst θ B)

/-! ## Point masses of a count law -/

namespace LocalCount

theorem measurable_nextLayer_zero (h : IIDPairs P Z) (eps : ℝ) :
    Measurable (nextLayer eps Z 0) :=
  (measurable_pi_apply 0).comp ((measurable_layerMap eps).comp (measurable_seq h.measurable))

/-- A uniform bound on the atoms `P(N = n)` bounds `cntAtom`. -/
theorem cntAtom_le_of_forall (hZ : Measurable (Z 0)) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ n : ℕ, P.real {ω | (Z 0 ω).2 = n} ≤ c) : cntAtom P Z ≤ c := by
  refine lconc_le fun x => ?_
  rw [Nat.cast_one, Ico_one]
  cases x with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, cntLaw_apply_natCast hZ]
    exact h n
  | negSucc n =>
    have e : cntLaw P Z {Int.negSucc n} = 0 := by
      rw [cntLaw, Measure.map_apply (measurable_cnt hZ) (measurableSet_singleton _)]
      convert measure_empty (μ := P)
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      omega
    rw [e, ENNReal.toReal_zero]
    exact hc

end LocalCount

/-- `cntAtom P Z = sup_k P(N = k)`: the largest atom of the count law is the supremum of the
point masses of `N = (Z 0).2`. -/
theorem cntAtom_eq_iSup [IsProbabilityMeasure P] (hZ : Measurable (Z 0)) :
    cntAtom P Z = ⨆ k : ℕ, P.real {ω | (Z 0 ω).2 = k} := by
  have hbdd : BddAbove (Set.range fun k : ℕ => P.real {ω | (Z 0 ω).2 = k}) :=
    ⟨1, by rintro _ ⟨k, rfl⟩; exact measureReal_le_one⟩
  refine le_antisymm (cntAtom_le_of_forall hZ (Real.iSup_nonneg fun _ => measureReal_nonneg)
    fun n => le_ciSup hbdd n) (ciSup_le fun n => ?_)
  have := isProbabilityMeasure_cntLaw (P := P) hZ
  have h := atom_le_lconc (cntLaw P Z) (n : ℤ)
  rw [cntLaw_apply_natCast hZ] at h
  exact h

/-! ## Constant-loss propagation -/

/-- **Constant-loss stopped-rank propagation** (klc:thm:constant-propagation,
klc:eq:constant-point-mass).  Under the standing hypotheses, if `p = cntAtom P Z ≤ 1/2` and
`eps ≥ 2`, the next-layer count `N⁺ = (nextLayer eps Z 0).2` has
`p⁺ = sup_k P(N⁺ = k) ≤ propConst θ B B₂ · p / eps²`. -/
theorem constant_propagation [IsProbabilityMeasure P] {m θ B B₂ : ℝ}
    (H : LocalCountHyp P Z m θ B B₂) (hp : cntAtom P Z ≤ 1 / 2) {eps : ℝ} (heps : 2 ≤ eps) :
    cntAtom P (nextLayer eps Z) ≤ propConst θ B B₂ * cntAtom P Z / eps ^ 2 := by
  set p := cntAtom P Z with hpdef
  set μ := cntLaw P Z with hμdef
  have := isProbabilityMeasure_cntLaw (P := P) (H.iid.measurable 0)
  have hp0 : 0 ≤ p := cntAtom_nonneg P Z
  have heps0 : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  set c := cycRate θ B with hcdef
  have hc : 0 < c := cycRate_pos H.θ_pos H.B_pos
  have hPC := propConst_pos (B₂ := B₂) H.θ_pos H.B_pos
  refine cntAtom_le_of_forall (measurable_nextLayer_zero H.iid eps) (by positivity) fun n => ?_
  set a : ℕ → ℝ≥0∞ := fun t =>
    P {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = n} with hadef
  have hdec : P {ω | (nextLayer eps Z 0 ω).2 = n} = ∑' t, a t :=
    measure_nextCount_eq_tsum H.iid eps (H.fin eps) n
  set M := ⌊eps ^ 2⌋₊ with hMdef
  set x : ℝ := ((n : ℤ) : ℝ) / m with hxdef
  set M' := max 1 (4 * B₂) with hM'def
  have hM'1 : 1 ≤ M' := le_max_left _ _
  set Cm : ℝ := 32 * 224 * M' with hCmdef
  have hCm : 0 ≤ Cm := by positivity
  set f : ℕ → ℝ := fun t => Cm * p * (((t : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
    min (Real.exp (-(c * eps ^ 2 / t))) ((t : ℝ) / max (t : ℝ) (((t : ℝ) - x) ^ 2))) with hfdef
  have hf0 : ∀ t, 0 ≤ f t := fun t => by
    refine mul_nonneg (mul_nonneg hCm hp0) (mul_nonneg (by positivity) (le_min (by positivity) ?_))
    exact div_nonneg (Nat.cast_nonneg _) (le_max_of_le_left (Nat.cast_nonneg _))
  -- short times: the cyclic early mark and the one-time renewal bound
  have hhead : ∀ t, a t ≤ ENNReal.ofReal (f t) := by
    intro t
    rcases le_or_gt (t : ℝ) (2 * eps) with hsmall | hbig
    · simp only [hadef]
      rw [stop_rank_eq_empty heps0.le hsmall n, measure_empty]
      exact zero_le
    have ht2 : 2 ≤ t := by
      have : (2 : ℝ) < t := by linarith
      exact_mod_cast this.le
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
    rw [← ENNReal.ofReal_toReal (show a t ≠ ⊤ from measure_ne_top P _)]
    refine ENNReal.ofReal_le_ofReal ?_
    set q := (a t).toReal with hq
    have hqdef : q = P.real {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = n} := rfl
    set T : ℝ := ((t : ℝ) ^ (3 / 2 : ℝ))⁻¹ with hT
    have hT0 : 0 ≤ T := by positivity
    set e := Real.exp (-(c * eps ^ 2 / t)) with he
    set r := (t : ℝ) / max (t : ℝ) (((t : ℝ) - x) ^ 2) with hr
    -- the cyclic early mark
    have h1 : q ≤ Cm * p * T * e := by
      refine (hqdef ▸ cyclic_early_mark H hp (by linarith) t n).trans ?_
      rw [cycConst]
      gcongr
      rw [hCmdef]
      nlinarith
    -- the marked cyclic-two estimate and the one-time renewal bound
    have h2 : q ≤ Cm * p * T * r := by
      have hmc := marked_cyclic_two_pairSegLen H.iid heps0.le H.gap_pos (by omega : 0 < t) n
      have hmc' : q ≤ 2 / t * P.real {ω | pairRank (seq Z ω) t = n} := by
        rw [hq, measureReal_def]
        have := ENNReal.toReal_mono (by finiteness) hmc
        rwa [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
          ENNReal.toReal_natCast] at this
      rw [measureReal_pairRank_eq_convFin H.iid t n] at hmc'
      have hren := renewal_one_time_le kestenIID_224 H.integrable_sq_cntLaw H.integral_cntLaw
        H.m_pos H.integral_sq_cntLaw_le hp (t := t) ht2 (n : ℤ)
      have hr0 : 0 ≤ r := div_nonneg ht0.le (le_max_of_le_left ht0.le)
      refine hmc'.trans ?_
      have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
      have hTeq : T = 1 / (t * Real.sqrt t) := by
        rw [hT, rpow_three_halves_eq_mul_sqrt ht0.le, one_div]
      calc 2 / t * (convFin t (fun _ => μ) {(n : ℤ)}).toReal
          ≤ 2 / t * (8 * 224 * M' * p / Real.sqrt t * r) := by gcongr; exact hren
        _ = 16 * 224 * M' * p * T * r := by rw [hTeq]; field_simp; ring
        _ ≤ Cm * p * T * r := by
            gcongr
            rw [hCmdef]
            nlinarith
    have hmin := le_min h1 h2
    rw [← mul_min_of_nonneg _ _ (by positivity : 0 ≤ Cm * p * T)] at hmin
    simp only [hfdef]
    linarith [hmin, show Cm * p * T * min e r = Cm * p * (T * min e r) by ring]
  have hheadsum : ∑ t ∈ range (M + 1), f t ≤ Cm * p * ((100 / c + 16 / c ^ 2) / eps ^ 2) := by
    have hsub : ∑ t ∈ Icc 1 M, f t = ∑ t ∈ range (M + 1), f t := by
      refine Finset.sum_subset (fun t ht => ?_) (fun t ht htn => ?_)
      · simp only [Finset.mem_Icc] at ht
        exact Finset.mem_range.2 (by omega)
      · have h0 : t = 0 := by
          simp only [Finset.mem_Icc, Finset.mem_range, not_and_or, not_le] at ht htn
          omega
        subst h0
        simp [hfdef, Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)]
    rw [← hsub]
    simp only [hfdef]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (early_local_kernel_le hc hE x) (mul_nonneg hCm hp0)
  -- long times: the marked cyclic-two estimate and the renewal mass
  set C₂ := max 2 (1 + 240 * 224 * M') with hC₂def
  have htail : ∑' t, a (t + (M + 1)) ≤ ENNReal.ofReal (2 / eps ^ 2 * (C₂ * p)) := by
    have hterm : ∀ t, a (t + (M + 1)) ≤
        ENNReal.ofReal (2 / eps ^ 2) * convFin (t + (M + 1)) (fun _ => μ) {(n : ℤ)} := by
      intro t
      have htM : eps ^ 2 < ((t + (M + 1) : ℕ) : ℝ) := by
        have := Nat.lt_floor_add_one (eps ^ 2)
        push_cast
        linarith [(Nat.cast_nonneg t : (0 : ℝ) ≤ t)]
      have htpos : (0 : ℝ) < ((t + (M + 1) : ℕ) : ℝ) := lt_trans hE htM
      have hmc := marked_cyclic_two_pairSegLen H.iid heps0.le H.gap_pos
        (by omega : 0 < t + (M + 1)) n
      simp only [hadef]
      refine hmc.trans ?_
      rw [show {ω | pairRank (seq Z ω) (t + (M + 1)) = n} =
        {ω | ∑ i ∈ range (t + (M + 1)), (Z i ω).2 = n} from rfl, measure_pairRank_eq_convFin H.iid]
      gcongr
      rw [ENNReal.ofReal_div_of_pos hE, ENNReal.ofReal_ofNat]
      refine ENNReal.div_le_div_left ?_ 2
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal htM.le
    calc ∑' t, a (t + (M + 1))
        ≤ ∑' t, ENNReal.ofReal (2 / eps ^ 2) * convFin (t + (M + 1)) (fun _ => μ) {(n : ℤ)} :=
          ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (2 / eps ^ 2) * ∑' t, convFin (t + M + 1) (fun _ => μ) {(n : ℤ)} :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (2 / eps ^ 2) * ∑' t, convFin (t + 1) (fun _ => μ) {(n : ℤ)} := by
          exact mul_le_mul_of_nonneg_left (ENNReal.tsum_comp_le_tsum_of_injective
            (add_left_injective M) (fun s => convFin (s + 1) (fun _ => μ) {(n : ℤ)})) zero_le
      _ ≤ ENNReal.ofReal (2 / eps ^ 2) * ENNReal.ofReal (C₂ * p) := by
          gcongr
          exact renewal_mass_le kestenIID_224 μ H.cntLaw_Iic_zero H.integrable_sq_cntLaw
            H.integral_cntLaw H.m_pos H.integral_sq_cntLaw_le (n : ℤ)
      _ = ENNReal.ofReal (2 / eps ^ 2 * (C₂ * p)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
  -- assembly
  have htot : P {ω | (nextLayer eps Z 0 ω).2 = n} ≤
      ENNReal.ofReal (Cm * p * ((100 / c + 16 / c ^ 2) / eps ^ 2) + 2 / eps ^ 2 * (C₂ * p)) := by
    have hsplit : ∑' t, a t = ∑ t ∈ range (M + 1), a t + ∑' t, a (t + (M + 1)) :=
      (ENNReal.summable (f := fun t => a (t + (M + 1)))).sum_add_tsum_nat_add'.symm
    rw [hdec, hsplit, ENNReal.ofReal_add (by positivity) (by positivity)]
    refine add_le_add ?_ htail
    calc ∑ t ∈ range (M + 1), a t ≤ ∑ t ∈ range (M + 1), ENNReal.ofReal (f t) :=
          Finset.sum_le_sum fun t _ => hhead t
      _ = ENNReal.ofReal (∑ t ∈ range (M + 1), f t) :=
          (ENNReal.ofReal_sum_of_nonneg fun t _ => hf0 t).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hheadsum
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (htot.trans
    (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  rw [propConst, ← hcdef, ← hM'def, hCmdef, hC₂def]
  field_simp

/-! ## The logarithmic transition at a deterministic layer -/

/-- **Logarithmic transition, pointwise form** (klc:thm:stopped-propagation at a layer with
deterministic counts `N ≡ 1`, where `N⁺ = T`).  Under the standing hypotheses and `eps ≥ 1`,
for every `t`, `P(T = t) ≤ logConst θ B · log(e eps²)/eps²`.  Long times use the marked
cyclic-two estimate `P(T = t) ≤ 2/t` (`S_t = t`), short times the early stop
`P(T ≤ t) ≤ 2 exp(-c eps²/t)`. -/
theorem log_transition_stop [IsProbabilityMeasure P] {m θ B B₂ : ℝ}
    (H : LocalCountHyp P Z m θ B B₂) (hone : ∀ i ω, (Z i ω).2 = 1) {eps : ℝ} (heps : 1 ≤ eps)
    (t : ℕ) :
    P.real {ω | pairSegLen eps (seq Z ω) = t} ≤
      logConst θ B * Real.log (Real.exp 1 * eps ^ 2) / eps ^ 2 := by
  have heps0 : 0 < eps := by linarith
  set E := eps ^ 2 with hEdef
  have hE1 : 1 ≤ E := by nlinarith
  have hE0 : 0 < E := by linarith
  set L := Real.log (Real.exp 1 * E) with hLdef
  have hL : L = 1 + Real.log E := by
    rw [hLdef, Real.log_mul (Real.exp_pos 1).ne' hE0.ne', Real.log_exp]
  have hL1 : 1 ≤ L := by rw [hL]; linarith [Real.log_nonneg hE1]
  set c := bernsteinRate θ B with hcdef
  have hc : 0 < c := bernsteinRate_pos H.θ_pos H.B_pos
  have hC1 := one_le_logConst θ B
  have hRHS : 0 ≤ logConst θ B * L / E := by positivity
  have hrank : ∀ ω, pairRank (seq Z ω) t = t := fun ω => by
    simp [pairRank_seq, hone]
  have hset : {ω | pairSegLen eps (seq Z ω) = t} =
      {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = t} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hrank, and_true]
  rcases le_or_gt (t : ℝ) (2 * eps) with hsmall | hbig
  · rw [hset, stop_rank_eq_empty heps0.le hsmall t, measureReal_empty]
    exact hRHS
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) < t := by linarith
    exact_mod_cast this.le
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  -- long times: `P(T = t) ≤ 2/t`
  have h1 : P.real {ω | pairSegLen eps (seq Z ω) = t} ≤ 2 / t := by
    have hmc := marked_cyclic_two_pairSegLen H.iid heps0.le H.gap_pos (by omega : 0 < t) t
    rw [← hset] at hmc
    rw [measureReal_def]
    have := ENNReal.toReal_mono (by finiteness) hmc
    rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofNat,
      ENNReal.toReal_natCast] at this
    refine this.trans ?_
    have hP1 : (P {ω | pairRank (seq Z ω) t = t}).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    have : 0 ≤ 2 / (t : ℝ) := by positivity
    nlinarith
  -- short times: the early stop
  have h2 : P.real {ω | pairSegLen eps (seq Z ω) = t} ≤ 2 * Real.exp (-(c * (E / t))) := by
    refine (measureReal_mono (fun ω (hω : pairSegLen eps (seq Z ω) = t) =>
      (show pairSegLen eps (seq Z ω) ≤ t from hω.le))).trans ?_
    refine (pairSegLen_le_prob H.iid H.θ_pos H.pos H.gam_all H.m_pos H.mean H.exp_int H.exp_le
      heps0 t ht1).trans ?_
    have hmin : min (eps ^ 2 / t) eps = E / t := by
      refine min_eq_left ?_
      rw [div_le_iff₀ ht0]
      nlinarith
    rw [hmin]
  rcases le_or_gt (c * (E / t)) L with hcase | hcase
  · refine h1.trans ?_
    have hEt : 2 / (t : ℝ) = 2 * (E / t) / E := by field_simp
    rw [hEt]
    have hle : E / t ≤ L / c := by rw [le_div_iff₀ hc]; linarith
    have hc' : 2 / c ≤ logConst θ B := by
      unfold logConst
      have := le_max_right (1 : ℝ) (1 / c)
      rw [← hcdef]
      have e : 2 / c = 2 * (1 / c) := by ring
      linarith
    calc 2 * (E / t) / E ≤ 2 * (L / c) / E := by gcongr
      _ = 2 / c * L / E := by ring
      _ ≤ logConst θ B * L / E := by gcongr
  · refine h2.trans ?_
    have hexp : Real.exp (-(c * (E / t))) ≤ Real.exp (-L) := Real.exp_le_exp.2 (by linarith)
    have hexpL : Real.exp (-L) = (Real.exp 1 * E)⁻¹ := by
      rw [Real.exp_neg, hLdef, Real.exp_log (by positivity)]
    have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp zero_le_one
    calc 2 * Real.exp (-(c * (E / t))) ≤ 2 * (Real.exp 1 * E)⁻¹ := by rw [← hexpL]; gcongr
      _ ≤ 2 / E := by
          rw [div_eq_mul_inv]
          gcongr
          nlinarith
      _ ≤ logConst θ B * L / E := by
          gcongr
          nlinarith [two_le_logConst θ B]

/-- **Logarithmic transition** (klc:thm:stopped-propagation, klc:eq:stopped-point-mass, at a
layer with deterministic counts `N ≡ 1`).  The next-layer count `N⁺ = T` has
`p⁺ = sup_t P(T = t) ≤ logConst θ B · log(e eps²)/eps²`. -/
theorem log_transition [IsProbabilityMeasure P] {m θ B B₂ : ℝ}
    (H : LocalCountHyp P Z m θ B B₂) (hone : ∀ i ω, (Z i ω).2 = 1) {eps : ℝ} (heps : 1 ≤ eps) :
    cntAtom P (nextLayer eps Z) ≤ logConst θ B * Real.log (Real.exp 1 * eps ^ 2) / eps ^ 2 := by
  have heps0 : 0 < eps := by linarith
  have hC1 := one_le_logConst θ B
  have hL : 0 ≤ Real.log (Real.exp 1 * eps ^ 2) :=
    Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  refine cntAtom_le_of_forall (measurable_nextLayer_zero H.iid eps) (by positivity) fun n => ?_
  have hae : {ω | (nextLayer eps Z 0 ω).2 = n} =ᵐ[P] {ω | pairSegLen eps (seq Z ω) = n} := by
    refine Filter.eventuallyEq_set.2 ((H.fin eps).mono fun ω hω => ?_)
    simp only [Set.mem_ofPred_eq, nextLayer_zero_snd, pairRank_seq, hone, Finset.sum_const,
      Finset.card_range, smul_eq_mul, mul_one]
    constructor
    · intro h
      rw [← h]
      exact (ENat.natCast_toNat hω).symm
    · intro h
      rw [h, ENat.toNat_natCast]
  rw [measureReal_congr hae]
  exact log_transition_stop H hone heps n

/-! ## Iteration through the exponential reference hierarchy -/

/-- The bound `2 CK/θK²` on `E (N/m)²` in every layer (`hyperexp_sq_all`). -/
def hierB₂ : ℝ := 2 * CK / θK ^ 2

/-- The threshold of the hierarchy corollary: `max(2, 4 logConst θK CK, √(propConst θK CK hierB₂))`. -/
def hierEps : ℝ := max 2 (max (4 * logConst θK CK) (Real.sqrt (propConst θK CK hierB₂)))

/-- The per-level growth constant of the normalized local count:
`max(1, cPlus · max(logConst θK CK, propConst θK CK hierB₂) / vmin)`. -/
def hierConst (vmin : ℝ) : ℝ :=
  max 1 (cPlus * max (logConst θK CK) (propConst θK CK hierB₂) / vmin)

/-- Every layer of the exponential reference hierarchy satisfies the standing hypotheses with
`m = lcount`, `θ = θK`, `B = CK` and `B₂ = 2 CK/θK²`. -/
theorem RefHyp.localCountHyp {g : ℕ → Ω → ℝ} (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) {b β vmin Kc eps : ℝ}
    (H : RefHyp P g b β vmin Kc eps) (ℓ : ℕ) :
    LocalCountHyp P (epLayerSeq eps g ℓ) (lcount P (epLayerSeq eps g ℓ)) θK CK hierB₂ := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  have heps0 : 0 ≤ eps := le_trans zero_le_one H.one_le_eps
  obtain ⟨hiid, hgam, hpos, -⟩ := gammaClosure_epLayerSeq hg hlaw heps0 ℓ
  obtain ⟨hexpint, hexp⟩ :=
    hyperexp_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps H.hepsK ℓ
  obtain ⟨hsqint, hsq⟩ :=
    hyperexp_sq_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps H.hepsK ℓ
  have hm := H.lcount_pos ℓ
  set m := lcount P (epLayerSeq eps g ℓ) with hmdef
  have hpt : ∀ ω, ((epLayerSeq eps g ℓ 0 ω).2 : ℝ) ^ 2 =
      m ^ 2 * (((epLayerSeq eps g ℓ 0 ω).2 : ℝ) / m) ^ 2 := fun ω => by
    field_simp
  refine
    { iid := hiid
      pos := hpos
      gamma := hgam
      m_pos := hm
      mean := rfl
      θ_pos := θK_pos
      exp_int := hexpint
      exp_le := hexp
      sq_int := ?_
      sq_le := ?_ }
  · exact (hsqint.const_mul (m ^ 2)).congr (Filter.Eventually.of_forall fun ω => (hpt ω).symm)
  · rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, hierB₂,
      mul_comm (2 * CK / θK ^ 2)]
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg m)

namespace LocalCount

theorem log_mul_le_half {C eps : ℝ} (hC : 1 ≤ C) (heps : 2 ≤ eps) (hCe : 4 * C ≤ eps) :
    C * Real.log (Real.exp 1 * eps ^ 2) / eps ^ 2 ≤ 1 / 2 := by
  have heps0 : 0 < eps := by linarith
  have hL : Real.log (Real.exp 1 * eps ^ 2) ≤ 2 * eps := by
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity), Real.log_exp, Real.log_pow]
    have := Real.log_le_sub_one_of_pos heps0
    push_cast
    linarith
  rw [div_le_iff₀ (by positivity)]
  have hC0 : 0 ≤ C := by linarith
  calc C * Real.log (Real.exp 1 * eps ^ 2) ≤ C * (2 * eps) := by gcongr
    _ ≤ 1 / 2 * eps ^ 2 := by nlinarith

end LocalCount

/-- **Local count through the reference hierarchy** (klc:cor:hierarchy,
klc:eq:hierarchy-recurrence, klc:eq:hierarchy-geometric).  Let `g` be iid `Exp(1)` and
`W ℓ = epLayerSeq eps g ℓ` under the standing hypotheses `RefHyp P g b β vmin Kc eps`; put
`π ℓ = cntAtom P (W ℓ) = sup_k P(N^{(ℓ)} = k)` and `K ℓ = lcount P (W ℓ) · π ℓ`.  For
`eps ≥ hierEps`:
* `π 1 ≤ logConst θK CK · log(e eps²)/eps²` (logarithmic transition at layer `0`, `N ≡ 1`);
* `π ℓ ≤ 1/2` for `ℓ ≥ 1`;
* `π (ℓ+1) ≤ propConst θK CK hierB₂ · π ℓ / eps²` for `ℓ ≥ 1` (constant-loss propagation);
* `K ℓ ≤ hierConst vmin ^ ℓ · log(e eps²)` for `ℓ ≥ 1`. -/
theorem local_count_hierarchy {g : ℕ → Ω → ℝ} (hg : IIDSeq P g)
    (hlaw : HasLaw (g 0) (expMeasure 1) P) {b β vmin Kc eps : ℝ}
    (H : RefHyp P g b β vmin Kc eps) (heps : hierEps ≤ eps) :
    cntAtom P (epLayerSeq eps g 1) ≤
        logConst θK CK * Real.log (Real.exp 1 * eps ^ 2) / eps ^ 2 ∧
      (∀ ℓ, 1 ≤ ℓ → cntAtom P (epLayerSeq eps g ℓ) ≤ 1 / 2) ∧
      (∀ ℓ, 1 ≤ ℓ → cntAtom P (epLayerSeq eps g (ℓ + 1)) ≤
        propConst θK CK hierB₂ * cntAtom P (epLayerSeq eps g ℓ) / eps ^ 2) ∧
      ∀ ℓ, 1 ≤ ℓ → lcount P (epLayerSeq eps g ℓ) * cntAtom P (epLayerSeq eps g ℓ) ≤
        hierConst vmin ^ ℓ * Real.log (Real.exp 1 * eps ^ 2) := by
  have := isProbabilityMeasure_of_hasLaw_exp hlaw
  set W := epLayerSeq eps g with hW
  set Clog := logConst θK CK with hClog
  set Cp := propConst θK CK hierB₂ with hCp
  set L := Real.log (Real.exp 1 * eps ^ 2) with hLdef
  have heps2 : 2 ≤ eps := le_trans (le_max_left _ _) heps
  have hepsL : 4 * Clog ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have hepsP : Real.sqrt Cp ≤ eps := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) heps
  have heps0 : 0 < eps := by linarith
  have hE : 0 < eps ^ 2 := by positivity
  have hCp0 : 0 < Cp := propConst_pos θK_pos CK_pos
  have hCpE : Cp ≤ eps ^ 2 := by
    rw [← Real.sq_sqrt hCp0.le]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hepsP 2
  have hClog1 : 1 ≤ Clog := one_le_logConst θK CK
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [Real.add_one_le_exp (1 : ℝ)])
  have HL := RefHyp.localCountHyp hg hlaw H
  have hsucc : ∀ ℓ, W (ℓ + 1) = nextLayer eps (W ℓ) := epLayerSeq_succ eps g
  -- layer `0` → `1`: the logarithmic transition
  have hone : ∀ i ω, (W 0 i ω).2 = 1 := fun i ω => rfl
  have hπ1 : cntAtom P (W 1) ≤ Clog * L / eps ^ 2 := by
    rw [hsucc 0]
    exact log_transition (HL 0) hone (by linarith)
  have hπ1half : cntAtom P (W 1) ≤ 1 / 2 :=
    hπ1.trans (log_mul_le_half hClog1 heps2 hepsL)
  -- layers `ℓ ≥ 1`: constant-loss propagation
  have hprop : ∀ ℓ, cntAtom P (W ℓ) ≤ 1 / 2 →
      cntAtom P (W (ℓ + 1)) ≤ Cp * cntAtom P (W ℓ) / eps ^ 2 := by
    intro ℓ hℓ
    rw [hsucc ℓ]
    exact constant_propagation (HL ℓ) hℓ heps2
  have hhalf : ∀ ℓ, 1 ≤ ℓ → cntAtom P (W ℓ) ≤ 1 / 2 := by
    intro ℓ hℓ
    induction ℓ, hℓ using Nat.le_induction with
    | base => exact hπ1half
    | succ ℓ _ ih =>
      refine (hprop ℓ ih).trans ?_
      have h0 := cntAtom_nonneg P (W ℓ)
      rw [div_le_iff₀ hE]
      nlinarith
  refine ⟨hπ1, hhalf, fun ℓ hℓ => hprop ℓ (hhalf ℓ hℓ), ?_⟩
  -- the normalized local count
  have hall := layerOK_all H.input H.hb H.hβ H.hvmin0 H.hvmin H.hKc H.heps
  have hb0 : 0 < b := lt_of_lt_of_le bAbs_pos H.hb
  have hvmin0 := H.hvmin0
  set C₃ := hierConst vmin with hC₃
  have hC₃1 : 1 ≤ C₃ := le_max_left _ _
  have hC₃log : cPlus * Clog / vmin ≤ C₃ := by
    refine le_trans ?_ (le_max_right _ _)
    gcongr
    · exact cPlus_pos.le
    · exact le_max_left _ _
  have hC₃p : cPlus * Cp / vmin ≤ C₃ := by
    refine le_trans ?_ (le_max_right _ _)
    gcongr
    · exact cPlus_pos.le
    · exact le_max_right _ _
  have hseg : ∀ ℓ, 0 ≤ segMean P eps (W ℓ) ∧ segMean P eps (W ℓ) ≤ cPlus * eps ^ 2 / vmin :=
    fun ℓ => ⟨le_trans (by positivity) (hall ℓ).2.2.2.1, (hall ℓ).2.2.2.2⟩
  have hcount : ∀ ℓ, lcount P (W (ℓ + 1)) = lcount P (W ℓ) * segMean P eps (W ℓ) :=
    fun ℓ => (hall ℓ).2.2.1
  have hlc0 : lcount P (W 0) = 1 := by simp [hW, lcount, epLayerSeq, inputPairs]
  intro ℓ hℓ
  induction ℓ, hℓ using Nat.le_induction with
  | base =>
    rw [hcount 0, hlc0, one_mul, pow_one]
    obtain ⟨hs0, hs1⟩ := hseg 0
    calc segMean P eps (W 0) * cntAtom P (W 1)
        ≤ cPlus * eps ^ 2 / vmin * (Clog * L / eps ^ 2) :=
          mul_le_mul hs1 hπ1 (cntAtom_nonneg _ _) (by have := cPlus_pos; positivity)
      _ = cPlus * Clog / vmin * L := by field_simp
      _ ≤ C₃ * L := by gcongr
  | succ ℓ hℓ ih =>
    rw [hcount ℓ]
    obtain ⟨hs0, hs1⟩ := hseg ℓ
    have hlc : 0 ≤ lcount P (W ℓ) := (H.lcount_pos ℓ).le
    have hπ := hprop ℓ (hhalf ℓ hℓ)
    have hπ0 := cntAtom_nonneg P (W ℓ)
    have hπ0' := cntAtom_nonneg P (W (ℓ + 1))
    have hcP := cPlus_pos
    calc lcount P (W ℓ) * segMean P eps (W ℓ) * cntAtom P (W (ℓ + 1))
        ≤ lcount P (W ℓ) * (cPlus * eps ^ 2 / vmin) * (Cp * cntAtom P (W ℓ) / eps ^ 2) := by
          gcongr
      _ = cPlus * Cp / vmin * (lcount P (W ℓ) * cntAtom P (W ℓ)) := by field_simp
      _ ≤ C₃ * (C₃ ^ ℓ * L) := by gcongr
      _ = C₃ ^ (ℓ + 1) * L := by ring

end

end PGM
