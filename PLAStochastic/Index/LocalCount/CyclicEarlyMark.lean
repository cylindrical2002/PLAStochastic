import PLAStochastic.Index.LocalCount.Decomposition

/-!
# Cyclic early failure with a retained rank mark

Source: `theory/proofs/proofK_local_count_core.tex`, `klc:lem:cyclic-early-mark`.

* `cyclicCount_eq_zero_of_walk_le` (klc:eq:cyclic-needs-max): if every partial sum of the
  centred normalized gaps `W_j = ∑_{i<j} (g_i/m - 1)`, `j ≤ t`, is at most `eps/3` in absolute
  value, no cyclic start stops at the last gap (the line of slope `1/m` through the origin
  fits every rotation, since each rotated partial sum is `W_v - W_u` or `W_t - W_u + W_v`).
* `LocalCount.gapWalk_le_of_halves`: the two half-block maxima control the whole walk.
* `cyclic_early_mark` (klc:eq:joint-early-local): for `p ≤ 1/2` and `eps ≥ 1`,
  `P(T = t, S_t = k) ≤ 7168 p t^{-3/2} exp(-(c/36) eps²/t)` with `c = bernsteinRate θ B`,
  through the half factorisation (Kesten on the untouched half, `LocalCountHyp.atom_rank_le`;
  `maximal_bernstein` on the other, `LocalCountHyp.half_max_le`), the marked cyclic identity and
  `cyclicCount ≤ 2`; only `t > 2 eps` contributes (`LocalCount.stop_rank_eq_empty`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Finset LocalCountBase LocalCount
open scoped ENNReal

/-! ## The deterministic cyclic estimate -/

namespace LocalCount

theorem pkeys_eq_sum {t : ℕ} (g : ℕ → ℝ) {j : ℕ} (hj : j ≤ t) :
    pkeys (fun i : Fin t => g i) j = ∑ q ∈ range j, g q := by
  simp only [pkeys, gapKeys]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq' : q < t := lt_of_lt_of_le (Finset.mem_range.1 hq) hj
  simp [vext, Nat.mod_eq_of_lt hq', hq']

end LocalCount

/-- **Cyclic failure needs a large walk** (klc:eq:cyclic-needs-max).  If
`|∑_{i<j} (g_i/m - 1)| ≤ eps/3` for all `j ≤ t`, then `𝒦_{t,eps}(g_0, …, g_{t-1}) = 0`. -/
theorem cyclicCount_eq_zero_of_walk_le {eps m : ℝ} {t : ℕ} (g : ℕ → ℝ)
    (hW : ∀ j ≤ t, |∑ i ∈ range j, (g i / m - 1)| ≤ eps / 3) :
    cyclicCount eps (fun i : Fin t => g i) = 0 := by
  classical
  unfold cyclicCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro r _ hr
  apply hr.2
  set z : Fin t → ℝ := fun i => g i with hz
  set W : ℕ → ℝ := fun j => ∑ q ∈ range j, (g q / m - 1) with hWdef
  have hWsum : ∀ j ≤ t, pkeys z j / m - j = W j := by
    intro j hj
    rw [pkeys_eq_sum g hj]
    simp only [hWdef, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hper : ∀ j, pkeys z (j + t) / m - ((j + t : ℕ) : ℝ) =
      (pkeys z j / m - j) + (pkeys z t / m - t) := by
    intro j; rw [pkeys_add_period]; push_cast; ring
  have heps : 0 ≤ eps := by
    have := hW 0 (Nat.zero_le _)
    simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at this
    linarith
  have hrt : (r : ℕ) < t := r.2
  refine ⟨1 / m, 0, fun i hi => ?_⟩
  have hit : i ≤ t := Nat.lt_succ_iff.1 hi
  rw [vkeys_rot z r hit]
  have key : (i : ℝ) - (1 / m * (pkeys z (r + i) - pkeys z r) + 0) =
      -((pkeys z (r + i) / m - ((r + i : ℕ) : ℝ)) - (pkeys z r / m - (r : ℕ))) := by
    push_cast; ring
  rw [key, abs_neg]
  have h2 := abs_le.1 (hW _ hrt.le)
  rcases le_or_gt (r + i) t with hle | hlt
  · rw [hWsum _ hle, hWsum _ hrt.le]
    have h1 := abs_le.1 (hW _ hle)
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · obtain ⟨j, hj⟩ : ∃ j, (r : ℕ) + i = j + t := ⟨r + i - t, by omega⟩
    have hjt : j ≤ t := by omega
    rw [hj, hper, hWsum _ hjt, hWsum _ le_rfl, hWsum _ hrt.le]
    have h1 := abs_le.1 (hW _ hjt)
    have h3 := abs_le.1 (hW _ le_rfl)
    exact abs_le.2 ⟨by linarith, by linarith⟩

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {Z : ℕ → Ω → ℝ × ℕ}

namespace LocalCount

omit mΩ in
theorem gapWalk_add (m : ℝ) (Z : ℕ → Ω → ℝ × ℕ) (r j : ℕ) (ω : Ω) :
    gapWalk m Z (r + j) ω = gapWalk m Z r ω + gapWalk m (fun i => Z (r + i)) j ω := by
  simp only [gapWalk, Finset.sum_range_add]

omit mΩ in
/-- The two half-block maxima control the whole walk. -/
theorem gapWalk_le_of_halves {m x : ℝ} {r s : ℕ} {ω : Ω}
    (h1 : ∀ j ≤ r, |gapWalk m Z j ω| ≤ x)
    (h2 : ∀ j ≤ s, |gapWalk m (fun i => Z (r + i)) j ω| ≤ x) :
    ∀ j ≤ r + s, |gapWalk m Z j ω| ≤ 2 * x := by
  have hx : 0 ≤ x := by
    have := h1 0 (Nat.zero_le _)
    simp only [gapWalk, Finset.range_zero, Finset.sum_empty, abs_zero] at this
    exact this
  intro j hj
  rcases le_or_gt j r with hjr | hjr
  · linarith [h1 j hjr]
  · obtain ⟨j', rfl⟩ : ∃ j', j = r + j' := ⟨j - r, by omega⟩
    rw [gapWalk_add]
    have a := h1 r le_rfl
    have b := h2 j' (by omega)
    calc |gapWalk m Z r ω + gapWalk m (fun i => Z (r + i)) j' ω|
        ≤ |gapWalk m Z r ω| + |gapWalk m (fun i => Z (r + i)) j' ω| := abs_add_le _ _
      _ ≤ 2 * x := by linarith

/-! ## The half-block atoms -/

theorem cntAtom_shift (h : IIDPairs P Z) (r : ℕ) :
    cntAtom P (fun i => Z (r + i)) = cntAtom P Z := by
  rw [cntAtom, cntAtom, h.cntLaw_shift r]

/-- `t^{3/2} = t √t`. -/
theorem rpow_three_halves_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) :
    x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
  rw [rpow_three_halves_eq hx, pow_succ, pow_two, Real.mul_self_sqrt hx]

end LocalCount

namespace LocalCountHyp

variable {m θ B B₂ : ℝ}

/-- Kesten's bound for a block of `n` counts, in the scale of a total length `t ≤ 4 n`:
`P(N₀ + ⋯ + N_{n-1} = v) ≤ 896 p / √t` (with `896 = 4 · 224`). -/
theorem atom_rank_le [IsProbabilityMeasure P] (H : LocalCountHyp P Z m θ B B₂)
    (hp : cntAtom P Z ≤ 1 / 2) {n t : ℕ} (hn : 1 ≤ n) (htpos : 0 < t) (ht : t ≤ 4 * n) (v : ℕ) :
    P {ω | ∑ i ∈ range n, (Z i ω).2 = v} ≤ ENNReal.ofReal (896 * cntAtom P Z / Real.sqrt t) := by
  have := isProbabilityMeasure_cntLaw (P := P) (H.iid.measurable 0)
  have := isProbabilityMeasure_convFin_const (cntLaw P Z) n
  rw [measure_pairRank_eq_convFin H.iid n v]
  refine (atom_le_ofReal_lconc _ _).trans (ENNReal.ofReal_le_ofReal ?_)
  refine (lconc_convFin_le kestenIID_224 hp hn).trans ?_
  set p := cntAtom P Z
  have hp0 : 0 ≤ p := cntAtom_nonneg P Z
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht' : (0 : ℝ) < t := by exact_mod_cast htpos
  have hsq : Real.sqrt t ≤ 2 * Real.sqrt n := by
    have e : (2 : ℝ) = Real.sqrt 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by exact_mod_cast ht)
  show 2 * 224 * p / Real.sqrt n ≤ 896 * p / Real.sqrt t
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hn') (Real.sqrt_pos.2 ht')]
  have := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ 2 * 224 * p)
  nlinarith

/-- The maximal Bernstein bound on a half block of length `n ≤ t`, for `t > 2 eps`:
`P(max_{j ≤ n} |W_j| > eps/6) ≤ 2 exp(-(c/36) eps²/t)`. -/
theorem half_max_le [IsProbabilityMeasure P] (H : LocalCountHyp P Z m θ B B₂) {eps : ℝ}
    (heps : 0 < eps) {n t : ℕ} (hn : 1 ≤ n) (hnt : n ≤ t) (ht : 2 * eps < t) :
    P {ω | ∃ j ≤ n, eps / 6 < |gapWalk m Z j ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-(bernsteinRate θ B / 36 * eps ^ 2 / t))) := by
  have hb := H.bernstein n hn (x := eps / 6) (by positivity)
  rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
  refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
  have hc := bernsteinRate_pos H.θ_pos H.B_pos
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt' : (n : ℝ) ≤ t := by exact_mod_cast hnt
  have ht' : (0 : ℝ) < t := lt_of_lt_of_le hn' hnt'
  gcongr
  -- `c · eps²/(36 t) ≤ c · min(eps²/(36 n), eps/6)`
  rw [show bernsteinRate θ B / 36 * eps ^ 2 / t = bernsteinRate θ B * (eps ^ 2 / (36 * t)) by
    ring]
  refine mul_le_mul_of_nonneg_left (le_min ?_ ?_) hc.le
  · rw [div_pow, div_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

end LocalCountHyp

/-! ## The cyclic early-mark estimate -/

/-- The constant `32 · 224` of the cyclic early-mark estimate. -/
def cycConst : ℝ := 7168

/-- The rate `c/36`, `c = bernsteinRate θ B`, of the cyclic early-mark estimate. -/
def cycRate (θ B : ℝ) : ℝ := bernsteinRate θ B / 36

theorem cycRate_pos {θ B : ℝ} (hθ : 0 < θ) (hB : 0 < B) : 0 < cycRate θ B := by
  unfold cycRate; have := bernsteinRate_pos hθ hB; positivity

namespace LocalCount

omit mΩ in
/-- A stop at `t` forces `t > 2 eps`: `P(T = t) = 0` for `t ≤ 2 eps`. -/
theorem stop_rank_eq_empty {eps : ℝ} (heps : 0 ≤ eps) {t : ℕ} (ht : (t : ℝ) ≤ 2 * eps) (k : ℕ) :
    {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hT
  have h := floor_two_eps_lt_pairSegLen heps (seq Z ω)
  rw [hT] at h
  have h' : ⌊2 * eps⌋₊ < t := by exact_mod_cast h
  have : t ≤ ⌊2 * eps⌋₊ := Nat.le_floor ht
  omega

end LocalCount

/-- **Cyclic early failure with a retained rank mark** (klc:lem:cyclic-early-mark,
klc:eq:joint-early-local).  Under the standing hypotheses, with `p = cntAtom P Z ≤ 1/2` and
`eps ≥ 1`, for all `t, k`:
`P(T = t, S_t = k) ≤ 7168 p t^{-3/2} exp(-(c/36) eps²/t)`, `c = bernsteinRate θ B`. -/
theorem cyclic_early_mark [IsProbabilityMeasure P] {m θ B B₂ : ℝ}
    (H : LocalCountHyp P Z m θ B B₂) (hp : cntAtom P Z ≤ 1 / 2) {eps : ℝ} (heps : 1 ≤ eps)
    (t k : ℕ) :
    P.real {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} ≤
      cycConst * cntAtom P Z * ((t : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
        Real.exp (-(cycRate θ B * eps ^ 2 / t)) := by
  set p := cntAtom P Z with hpdef
  have hp0 : 0 ≤ p := cntAtom_nonneg P Z
  have heps0 : 0 < eps := by linarith
  have hRHS : 0 ≤ cycConst * p * ((t : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
      Real.exp (-(cycRate θ B * eps ^ 2 / t)) := by
    unfold cycConst; positivity
  rcases le_or_gt (t : ℝ) (2 * eps) with hsmall | hbig
  · rw [stop_rank_eq_empty heps0.le hsmall k, measureReal_empty]
    exact hRHS
  have ht3 : 3 ≤ t := by
    have : (2 : ℝ) < t := by linarith
    exact_mod_cast (show 2 < t by exact_mod_cast this)
  set r := t / 2 with hr
  set s := t - r with hs
  have hr1 : 1 ≤ r := by omega
  have hs1 : 1 ≤ s := by omega
  have hrs : r + s = t := by omega
  have htr : t ≤ 4 * r := by omega
  have hts : t ≤ 4 * s := by omega
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  -- the events
  set S : Set Ω := {ω | ∑ i ∈ range t, (Z i ω).2 = k} with hSdef
  set A₁ : Set Ω := {ω | ∃ j ≤ r, eps / 6 < |gapWalk m Z j ω|} with hA₁
  set A₂set : Set (ℕ → ℝ × ℕ) :=
    {z | ∃ j ≤ s, eps / 6 < |∑ i ∈ range j, ((z i).1 / m - 1)|} with hA₂set
  set Y : Ω → ℕ → ℝ × ℕ := fun ω i => Z (r + i) ω with hY
  set A₂ : Set Ω := Y ⁻¹' A₂set with hA₂
  have hA₂eq : A₂ = {ω | ∃ j ≤ s, eps / 6 < |gapWalk m (fun i => Z (r + i)) j ω|} := rfl
  have hSm : MeasurableSet S := measurableSet_rank_eq H.iid t k
  have hA₁m : MeasurableSet A₁ :=
    (pairFiltration Z H.iid.measurable).le r _ (measurableSet_past_max H.iid m (eps / 6) r)
  have hYm : Measurable Y := measurable_pi_lambda _ fun i => H.iid.measurable (r + i)
  have hA₂m : MeasurableSet A₂ := hYm (measurableSet_seq_max m (eps / 6) s)
  -- Step 1: the marked cyclic identity and `𝒦 ≤ 2`
  have hstep1 : P {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} ≤
      2 / (t : ℝ≥0∞) * P ((A₁ ∪ A₂) ∩ S) := by
    have hset : {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} =
        {ω | stopsAt eps (fun i : Fin t => (Z i ω).1) ∧ ∑ i ∈ range t, (Z i ω).2 = k} := by
      ext ω
      exact and_congr (stopsAt_iff_pairSegLen (seq Z ω) t).symm Iff.rfl
    rw [hset, marked_cyclic_identity H.iid eps (by omega) k]
    have hae : ∀ᵐ ω ∂P, ∀ i, 0 < (Z i ω).1 := ae_all_iff.2 H.gap_pos
    have hle : ∫⁻ ω, S.indicator
        (fun ω => (cyclicCount eps (fun i : Fin t => (Z i ω).1) : ℝ≥0∞)) ω ∂P ≤
          ∫⁻ ω, ((A₁ ∪ A₂) ∩ S).indicator (fun _ => (2 : ℝ≥0∞)) ω ∂P := by
      refine lintegral_mono_ae (hae.mono fun ω hω => ?_)
      by_cases hωS : ω ∈ S
      · rw [Set.indicator_of_mem hωS]
        by_cases hωA : ω ∈ A₁ ∪ A₂
        · rw [Set.indicator_of_mem (show ω ∈ (A₁ ∪ A₂) ∩ S from ⟨hωA, hωS⟩)]
          exact_mod_cast cyclicCount_le_two heps0.le (fun i => hω i)
        · have h1 : ∀ j ≤ r, |gapWalk m Z j ω| ≤ eps / 6 := fun j hj =>
            not_lt.1 fun hlt => hωA (Or.inl ⟨j, hj, hlt⟩)
          have h2 : ∀ j ≤ s, |gapWalk m (fun i => Z (r + i)) j ω| ≤ eps / 6 := fun j hj =>
            not_lt.1 fun hlt => hωA (Or.inr (by rw [hA₂eq]; exact ⟨j, hj, hlt⟩ : ω ∈ A₂))
          have hW := gapWalk_le_of_halves h1 h2
          rw [hrs] at hW
          have h0 : cyclicCount eps (fun i : Fin t => (Z i ω).1) = 0 :=
            cyclicCount_eq_zero_of_walk_le (fun i => (Z i ω).1) fun j hj => by
              have := hW j hj
              simp only [gapWalk] at this
              show |∑ i ∈ range j, ((Z i ω).1 / m - 1)| ≤ eps / 3
              linarith
          rw [h0, Nat.cast_zero]
          exact zero_le
      · rw [Set.indicator_of_notMem hωS]
        exact zero_le
    rw [lintegral_indicator_const ((hA₁m.union hA₂m).inter hSm)] at hle
    calc (t : ℝ≥0∞)⁻¹ * _ ≤ (t : ℝ≥0∞)⁻¹ * (2 * P ((A₁ ∪ A₂) ∩ S)) := by gcongr
      _ = 2 / (t : ℝ≥0∞) * P ((A₁ ∪ A₂) ∩ S) := by rw [div_eq_mul_inv]; ring
  -- Step 2: the two half factorisations
  set L : ℝ := 896 * p / Real.sqrt t with hL
  have hL0 : 0 ≤ L := by positivity
  set E : ℝ := 2 * Real.exp (-(cycRate θ B * eps ^ 2 / t)) with hE
  have hE0 : 0 ≤ E := by positivity
  have hS' : S = {ω | ∑ i ∈ range (r + s), (Z i ω).2 = k} := by rw [hrs]
  have hA₁S : P (A₁ ∩ S) ≤ ENNReal.ofReal L * ENNReal.ofReal E := by
    rw [hS']
    refine (measure_past_inter_rank_le H.iid (measurableSet_past_max H.iid m (eps / 6) r) s k
      (L := ENNReal.ofReal L) fun v => ?_).trans ?_
    · have h := (H.shift r).atom_rank_le (by rw [cntAtom_shift H.iid r]; exact hp) hs1 (by omega) hts v
      rw [cntAtom_shift H.iid r] at h
      exact h
    · gcongr
      exact H.half_max_le heps0 hr1 (by omega) hbig
  have hA₂S : P (A₂ ∩ S) ≤ ENNReal.ofReal L * ENNReal.ofReal E := by
    rw [hS']
    refine (measure_future_inter_rank_le H.iid (r := r) (measurableSet_seq_max m (eps / 6) s) s k
      (L := ENNReal.ofReal L) fun u => H.atom_rank_le hp hr1 (by omega) htr u).trans ?_
    gcongr
    rw [show Y ⁻¹' A₂set = A₂ from rfl, hA₂eq]
    exact (H.shift r).half_max_le heps0 hs1 (by omega) hbig
  -- Step 3: assembly
  have hfin : P ((A₁ ∪ A₂) ∩ S) ≤ ENNReal.ofReal (2 * (L * E)) := by
    rw [Set.union_inter_distrib_right]
    refine (measure_union_le _ _).trans ?_
    rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hL0]
    exact add_le_add hA₁S hA₂S
  have htot : P {ω | pairSegLen eps (seq Z ω) = t ∧ pairRank (seq Z ω) t = k} ≤
      ENNReal.ofReal (2 / t * (2 * (L * E))) := by
    refine hstep1.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_div_of_pos ht0, ENNReal.ofReal_ofNat,
      ENNReal.ofReal_natCast]
    gcongr
  rw [measureReal_def]
  refine ENNReal.toReal_le_of_le_ofReal hRHS (htot.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
  rw [hL, hE, rpow_three_halves_eq_mul_sqrt ht0.le, cycConst]
  have hsq : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  field_simp
  ring

end

end PGM
