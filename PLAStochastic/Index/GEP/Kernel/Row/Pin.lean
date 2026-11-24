import PLAStochastic.Index.GEP.Kernel.Row.LargeTime
import PLAStochastic.Index.GEP.OrbitClosure.OrbitMoments

/-!
# WP4 kernel rows: boundary-to-boundary pins

Source: `influence-lipschitz.md` §3, (pin): for boundary points `b, b'` of the band,

* medium time (`n ≤ 2 w²`): `q_n(b, b') ≤ K (1 + A)² n^{-3/2}` — one third of the time is spent
  on each one-sided survival (forward from `b`, reverse from `b'`), the middle third is the free
  density (`krDens_bdry_pin_medium`);
* large time: `q_{T+j+T}(b, b') ≤ 3 C₂ (1 + A)² (√λ)^j / w³` (`krDens_bdry_pin_large`, in
  `GEPKernelRowLarge`);
* short time (`n ≤ w/4`, `A ≤ w`): the "upward" pin (against the jumps) vanishes identically,
  because every step moves at most `1` in the drift direction (`krDens_up_zero`), and the
  "downward" pin is at most `6 D e^{-c₀ w}` by the two-halves argument: either the walk is still
  in the upper half of the band at time `n - 1`, and then the last jump must be of size `≥ w/2`,
  which the exponential envelope of `f` makes `≤ 2 D e^{-θ w / 4}`, or it has already fallen by
  `w/2` in `n - 1 ≤ w/4` steps, which the endpoint Bernstein inequality
  (`iid_endpoint_bernstein`) makes `≤ 4 D e^{-c w / 64}` (`krDens_down_short`).
  The reverse direction follows from `krDens_symm`.  Both cases are collected in
  `krDens_bdry_pin_short`.

The Bernstein rate is `krRate D θ = bernsteinRate (θ/2) (2 D / θ)` (from `RegLaw.expMom`), and
`krC₀ D θ = min (θ/4) (krRate D θ / 64)`; both are chosen before the law.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Medium-time pin -/

/-- Medium-time pin constant `288 D + 16 K² L`. -/
def krCpin (D K L : ℝ) : ℝ := 288 * D + 16 * K ^ 2 * L

theorem krCpin_nonneg {K L : ℝ} (hD : 0 ≤ D) (hL : 0 ≤ L) : 0 ≤ krCpin D K L := by
  unfold krCpin; positivity

/-- Arithmetic of the third split for `n ≥ 13`: `m := n / 3`, `j := n - 2 (n / 3) - 1` satisfy
`1 ≤ m`, `2 ≤ j`, `n = (m - 1 + 1) + (j + 1) + (m - 1 + 1)`, `m ≤ n / 3`, and
`n √n / 8 ≤ √(m (j m))`. -/
theorem kr_third_split {n : ℕ} (hn : 13 ≤ n) :
    1 ≤ n / 3 ∧ 2 ≤ n - 2 * (n / 3) - 1 ∧
      n = (n / 3 - 1 + 1) + (n - 2 * (n / 3) - 1 + 1) + (n / 3 - 1 + 1) ∧
      ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 ∧
      (n : ℝ) * Real.sqrt n / 8 ≤
        Real.sqrt (((n / 3 : ℕ) : ℝ) * (((n - 2 * (n / 3) - 1 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ))) := by
  have h1 : 1 ≤ n / 3 := by omega
  have h2 : 2 ≤ n - 2 * (n / 3) - 1 := by omega
  have h3 : n = (n / 3 - 1 + 1) + (n - 2 * (n / 3) - 1 + 1) + (n / 3 - 1 + 1) := by omega
  have hm : ((n / 3 : ℕ) : ℝ) ≤ (n : ℝ) / 3 := by
    have : 3 * (n / 3) ≤ n := Nat.mul_div_le n 3
    have h' : (3 : ℝ) * (n / 3 : ℕ) ≤ n := by exact_mod_cast this
    linarith
  refine ⟨h1, h2, h3, hm, ?_⟩
  have hn' : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have hm' : (n : ℝ) / 4 ≤ (n / 3 : ℕ) := by
    have : n - 2 ≤ 3 * (n / 3) := by omega
    have h' : ((n - 2 : ℕ) : ℝ) ≤ 3 * (n / 3 : ℕ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    push_cast at h'
    linarith
  have hj' : (n : ℝ) / 4 ≤ ((n - 2 * (n / 3) - 1 : ℕ) : ℝ) := by
    have e : ((n - 2 * (n / 3) - 1 : ℕ) : ℝ) = n - 2 * ((n / 3 : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [e]
    linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
  refine Real.le_sqrt_of_sq_le ?_
  have hn4 : (0 : ℝ) ≤ n / 4 := by positivity
  have hprod : (n / 4 : ℝ) * ((n / 4) * (n / 4)) ≤
      ((n / 3 : ℕ) : ℝ) * (((n - 2 * (n / 3) - 1 : ℕ) : ℝ) * ((n / 3 : ℕ) : ℝ)) :=
    mul_le_mul hm' (mul_le_mul hj' hm' hn4 (by positivity)) (by positivity) (by positivity)
  calc ((n : ℝ) * Real.sqrt n / 8) ^ 2 = (n / 4 : ℝ) * ((n / 4) * (n / 4)) := by
        rw [div_pow, mul_pow, hsq]; ring
    _ ≤ _ := hprod

/-- **Medium-time pin**: `q_n(b, b') ≤ (288 D + 16 K² L) (1 + A)² / (n √n)` for
`1 ≤ n ≤ 2 w²` and boundary points `b, b'`. -/
theorem krDens_bdry_pin_medium {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) {n : ℕ} (hn : 1 ≤ n) (hnw : (n : ℝ) ≤ 2 * w ^ 2) :
    krDens (Icc 0 w) ν f β a' n b b' ≤ krCpin D K L * (1 + A) ^ 2 / (n * Real.sqrt n) := by
  have hD0 := H.hD0
  have hL0 := H.hL0
  have hK := H.hK
  have hA := H.hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hA1 : 1 ≤ (1 + A) ^ 2 := one_le_pow₀ (by linarith)
  unfold krCpin
  by_cases hn12 : n ≤ 12
  · refine (H.krDens_le_two_D n b b').trans ?_
    have hn12' : (n : ℝ) ≤ 12 := by exact_mod_cast hn12
    have hsn' : Real.sqrt n ≤ n := by
      rw [Real.sqrt_le_left hn0.le]
      nlinarith
    have hns : (n : ℝ) * Real.sqrt n ≤ 144 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    have e1 : D * (n * Real.sqrt n) ≤ D * 144 := mul_le_mul_of_nonneg_left hns hD0
    have e2 : 288 * D * 1 ≤ 288 * D * (1 + A) ^ 2 :=
      mul_le_mul_of_nonneg_left hA1 (by positivity)
    have e3 : 0 ≤ 16 * K ^ 2 * L * (1 + A) ^ 2 := by positivity
    nlinarith
  · have hn13 : 13 ≤ n := by omega
    obtain ⟨hm1, hj2, heq, hmthird, hsq⟩ := kr_third_split hn13
    set m := n / 3 with hm
    set j := n - 2 * (n / 3) - 1 with hj
    have hmw : ((m - 1 + 1 : ℕ) : ℝ) ≤ w ^ 2 := by
      rw [Nat.sub_add_cancel hm1]
      nlinarith
    have hB : ∀ y z, krDens (Icc 0 w) ν f β a' (j + 1) y z ≤ 2 * L / Real.sqrt j :=
      fun y z => H.krDens_le_free_two hj2 y z
    have h1 := krDens_three_block_le ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' (m - 1) j (m - 1)
      hB b b'
    rw [← heq] at h1
    refine h1.trans ?_
    have hs := H.krSurv_medium hb (n := m - 1 + 1) (by omega) hmw
    have hs' := H.rev.krSurv_medium hb' (n := m - 1 + 1) (by omega) hmw
    have hmm : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℕ) := by rw [Nat.sub_add_cancel hm1]
    rw [hmm] at hs hs'
    have hj0 : 0 < Real.sqrt j := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < j))
    have hm0 : 0 < Real.sqrt (m : ℕ) := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m))
    have hB0 : 0 ≤ 2 * L / Real.sqrt j := by positivity
    have hs0 : 0 ≤ K * (1 + A) / Real.sqrt (m : ℕ) := by positivity
    calc krSurv (Icc 0 w) (ν : Measure ℝ) β a' (m - 1 + 1) b *
          (2 * L / Real.sqrt j * krSurv (Icc 0 w) (ν : Measure ℝ) (-β) (-a') (m - 1 + 1) b')
        ≤ K * (1 + A) / Real.sqrt (m : ℕ) *
          (2 * L / Real.sqrt j * (K * (1 + A) / Real.sqrt (m : ℕ))) :=
          mul_le_mul hs (mul_le_mul_of_nonneg_left hs' hB0)
            (mul_nonneg hB0 (krSurv_nonneg H.hJ ν _ _ _ _)) hs0
      _ = 2 * (K ^ 2 * L) * (1 + A) ^ 2 /
          Real.sqrt (((m : ℕ) : ℝ) * (((j : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_mul (Nat.cast_nonneg _),
            div_mul_div_comm, div_mul_div_comm]
          ring
      _ ≤ (288 * D + 16 * K ^ 2 * L) * (1 + A) ^ 2 / (n * Real.sqrt n) := by
          have hsq0 : 0 < Real.sqrt (((m : ℕ) : ℝ) * (((j : ℕ) : ℝ) * ((m : ℕ) : ℝ))) :=
            lt_of_lt_of_le (by positivity) hsq
          rw [div_le_div_iff₀ hsq0 (by positivity)]
          have : 2 * (K ^ 2 * L) * (1 + A) ^ 2 * (n * Real.sqrt n) =
              16 * (K ^ 2 * L) * (1 + A) ^ 2 * (n * Real.sqrt n / 8) := by ring
          rw [this]
          calc 16 * (K ^ 2 * L) * (1 + A) ^ 2 * (n * Real.sqrt n / 8)
              ≤ 16 * (K ^ 2 * L) * (1 + A) ^ 2 *
                  Real.sqrt (((m : ℕ) : ℝ) * (((j : ℕ) : ℝ) * ((m : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ ≤ (288 * D + 16 * K ^ 2 * L) * (1 + A) ^ 2 *
                  Real.sqrt (((m : ℕ) : ℝ) * (((j : ℕ) : ℝ) * ((m : ℕ) : ℝ))) := by
                gcongr
                linarith

/-! ## Short time: the upward pin vanishes -/

/-- For the forward step `1 - aX` with `a > 0` and a law on `(0, ∞)`, the walk from `0` is at
most `l` at time `l` almost surely, so the `n`-step kernel from `0` vanishes at every `z ≥ n`. -/
theorem krDens_up_zero {θ vlo vhi : ℝ} (hν : RegLaw D θ vlo vhi ν) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hfz : ∀ x, x ≤ 0 → f x = 0) (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) {z : ℝ} (hz : (n : ℝ) ≤ z) :
    krDens J ν f 1 a n 0 z = 0 := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [krDens_succ]
  have hpos : (ν : Measure ℝ) (Iic 0) = 0 := (hν.momClass hθ hvlo).pos
  refine integral_eq_zero_of_ae ?_
  filter_upwards [ae_pos_iidLaw hpos] with g hg
  simp only [Pi.zero_apply]
  have hS : 0 ≤ gapKeys g n' := Finset.sum_nonneg fun i _ => (hg i).le
  have hy : kWalk 0 1 a g n' ≤ n' := by
    unfold kWalk
    nlinarith
  have hn'z : (n' : ℝ) + 1 ≤ z := by push_cast at hz; linarith
  have harg : (kWalk 0 1 a g n' + 1 - z) / a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  unfold krKer
  rw [hfz _ harg, zero_div, mul_zero, mul_zero]

/-! ## Short time: the downward pin is exponentially small -/

/-- Bernstein rate of the class: `bernsteinRate (θ/2) (2D/θ)` (from `RegLaw.expMom`). -/
def krRate (D θ : ℝ) : ℝ := bernsteinRate (θ / 2) (2 * D / θ)

/-- Short-time pin rate `c₀ = min (θ/4) (krRate / 64)`. -/
def krC₀ (D θ : ℝ) : ℝ := min (θ / 4) (krRate D θ / 64)

theorem krRate_pos {θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) : 0 < krRate D θ :=
  bernsteinRate_pos (by linarith) (by positivity)

theorem krC₀_pos {θ : ℝ} (hD : 0 < D) (hθ : 0 < θ) : 0 < krC₀ D θ :=
  lt_min (by linarith) (by linarith [krRate_pos hD hθ])

/-- The set of paths whose forward walk from `w` has fallen below `w/2` at time `n'`. -/
theorem kr_measurableSet_fall (w a : ℝ) (n' : ℕ) :
    MeasurableSet {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := by
  have hm : Measurable fun g : ℕ → ℝ => kWalk w 1 a g n' :=
    (measurable_kWalk_prod 1 a n').comp (measurable_const.prodMk measurable_id)
  exact measurableSet_lt hm measurable_const

/-- Falling by `w/2` in `n' ≤ w/4` steps forces `|S_{n'} - n'| ≥ w/8` in the slope window. -/
theorem kr_fall_subset {w A : ℝ} (hw : 0 < w) (hAw : A ≤ w) (haA : |a - 1| ≤ A / w)
    (ha : 0 < a) (ha₂ : |a| ≤ 2) {n' : ℕ} (hn' : (n' : ℝ) ≤ w / 4) :
    {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} ⊆ {g | w / 8 ≤ |gapKeys g n' - n'|} := by
  intro g hg
  have hg' : w + n' * 1 - a * gapKeys g n' < w / 2 := hg
  show w / 8 ≤ |gapKeys g n' - n'|
  rw [mul_one] at hg'
  set S := gapKeys g n'
  have ha2 : a ≤ 2 := (le_abs_self a).trans ha₂
  have ha1 : a - 1 ≤ A / w := (le_abs_self _).trans haA
  have hAw' : A / w ≤ 1 := by rw [div_le_one hw]; exact hAw
  have hn0 : (0 : ℝ) ≤ n' := Nat.cast_nonneg _
  have hdrift : (a - 1) * n' ≤ w / 4 := by
    calc (a - 1) * n' ≤ A / w * n' := mul_le_mul_of_nonneg_right ha1 hn0
      _ ≤ 1 * (w / 4) := mul_le_mul hAw' hn' hn0 zero_le_one
      _ = w / 4 := one_mul _
  have h1 : w / 4 < a * (S - n') := by nlinarith
  have h2 : a * (S - n') ≤ 2 * (S - n') := by
    have : 0 < S - n' := by
      by_contra hc
      push Not at hc
      nlinarith
    nlinarith
  refine le_trans (by linarith) (le_abs_self _)

/-- The two-halves pointwise bound on the last-step integrand of `q_{n'+1}(w, 0)`: either the
last jump is of size `≥ w/2` (envelope of `f`), or the walk has fallen below `w/2` by time `n'`. -/
theorem kr_down_pointwise {θ vlo vhi K L w A : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a 1 a) (ha : 0 < a) (n' : ℕ) (g : ℕ → ℝ) :
    krAlive (Icc 0 w) 1 a n' w g * krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0 ≤
      2 * D * Real.exp (-(θ / 4 * w)) +
        {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2}.indicator (fun _ => 2 * D) g := by
  have hw0 := H.hw0
  have hD0 := H.hD0
  have hθ := H.hθ
  have ha2 : a ≤ 2 := (le_abs_self a).trans H.ha₂
  have hexp0 : 0 ≤ 2 * D * Real.exp (-(θ / 4 * w)) := by positivity
  have hind0 : 0 ≤ {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2}.indicator (fun _ => 2 * D) g :=
    indicator_nonneg (fun _ _ => by linarith) _
  by_cases hyJ : kWalk w 1 a g n' ∈ Icc 0 w
  · have hker : krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0 ≤
        2 * D * Real.exp (-(θ / 2 * kWalk w 1 a g n')) := by
      unfold krKer
      have h0J : (0 : ℝ) ∈ Icc 0 w := ⟨le_refl _, hw0.le⟩
      rw [indicator_of_mem hyJ, indicator_of_mem h0J, one_mul, one_mul, abs_of_pos ha]
      have hfe := H.hfe ((kWalk w 1 a g n' + 1 - 0) / a)
      have harg : θ / 2 * kWalk w 1 a g n' ≤ θ * ((kWalk w 1 a g n' + 1 - 0) / a) := by
        rw [sub_zero, mul_div_assoc', le_div_iff₀ ha]
        have : θ / 2 * kWalk w 1 a g n' * a ≤ θ / 2 * kWalk w 1 a g n' * 2 :=
          mul_le_mul_of_nonneg_left ha2 (mul_nonneg (by positivity) hyJ.1)
        linarith
      have hexp : Real.exp (-θ * ((kWalk w 1 a g n' + 1 - 0) / a)) ≤
          Real.exp (-(θ / 2 * kWalk w 1 a g n')) := by
        apply Real.exp_le_exp.2
        linarith
      rw [div_le_iff₀ ha]
      have h1a : 1 ≤ 2 * a := by linarith [H.ha₁, abs_of_pos ha]
      have h0 : 0 ≤ D * Real.exp (-(θ / 2 * kWalk w 1 a g n')) := by positivity
      calc f ((kWalk w 1 a g n' + 1 - 0) / a)
          ≤ D * Real.exp (-θ * ((kWalk w 1 a g n' + 1 - 0) / a)) := hfe
        _ ≤ D * Real.exp (-(θ / 2 * kWalk w 1 a g n')) := mul_le_mul_of_nonneg_left hexp hD0
        _ ≤ 2 * D * Real.exp (-(θ / 2 * kWalk w 1 a g n')) * a := by nlinarith
    by_cases hhalf : w / 2 ≤ kWalk w 1 a g n'
    · have hexp : Real.exp (-(θ / 2 * kWalk w 1 a g n')) ≤ Real.exp (-(θ / 4 * w)) := by
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonneg_left hhalf hθ.le
        linarith
      calc krAlive (Icc 0 w) 1 a n' w g * krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0
          ≤ 1 * (2 * D * Real.exp (-(θ / 4 * w))) :=
            mul_le_mul (krAlive_le_one _ _ _)
              (hker.trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
              (krKer_nonneg H.hf0 _ _) zero_le_one
        _ ≤ _ := by linarith
    · have hgE : g ∈ {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := lt_of_not_ge hhalf
      rw [indicator_of_mem hgE]
      have hker' : krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0 ≤ 2 * D := by
        refine hker.trans ?_
        have : Real.exp (-(θ / 2 * kWalk w 1 a g n')) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [hyJ.1]
        nlinarith
      calc krAlive (Icc 0 w) 1 a n' w g * krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0
          ≤ 1 * (2 * D) :=
            mul_le_mul (krAlive_le_one _ _ _) hker' (krKer_nonneg H.hf0 _ _) zero_le_one
        _ ≤ _ := by linarith
  · rw [krKer_eq_zero_of_left_notMem hyJ, mul_zero]
    linarith

/-- The probability of having fallen below `w/2` by time `n' ≤ w/4` is `≤ 2 e^{-krRate w / 64}`. -/
theorem kr_fall_prob {θ vlo vhi K L w A : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a 1 a) (hAw : A ≤ w) (ha : 0 < a) {n' : ℕ}
    (hn'w : (n' : ℝ) ≤ w / 4) :
    (iidLaw ν).real {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} ≤
      2 * Real.exp (-(krRate D θ / 64 * w)) := by
  have hw0 := H.hw0
  have hθ := H.hθ
  cases n' with
  | zero =>
    have hEe : {g : ℕ → ℝ | kWalk w 1 a g 0 < w / 2} = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro g hg
      have hg' : kWalk w 1 a g 0 < w / 2 := hg
      rw [kWalk_zero] at hg'
      linarith
    rw [hEe, measureReal_empty]
    positivity
  | succ n'' =>
    have hsub := kr_fall_subset (a := a) hw0 hAw H.haA ha H.ha₂ hn'w
    have hB := iid_endpoint_bernstein (ρ := ν) (θ₁ := θ / 2) (B₁ := 2 * D / θ) (by linarith)
      (H.hν.momClass hθ H.hvlo).pos (H.hν.momClass hθ H.hvlo).mean (H.hν.expMom hθ)
      (n'' + 1) (by omega) (d := w / 8) (by positivity)
    refine (measureReal_mono hsub).trans (hB.trans ?_)
    have hc := krRate_pos H.hD hθ
    have hn1 : (0 : ℝ) < ((n'' + 1 : ℕ) : ℝ) := by positivity
    have hmin : w / 16 ≤ min ((w / 8) ^ 2 / ((n'' + 1 : ℕ) : ℝ)) (w / 8) := by
      refine le_min ?_ (by linarith)
      rw [le_div_iff₀ hn1]
      nlinarith
    have hmono : krRate D θ / 64 * w ≤ krRate D θ / 4 * min ((w / 8) ^ 2 / ((n'' + 1 : ℕ) : ℝ)) (w / 8) := by
      have : krRate D θ / 64 * w = krRate D θ / 4 * (w / 16) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hmin (by positivity)
    have : Real.exp (-(krRate D θ / 4 * min ((w / 8) ^ 2 / ((n'' + 1 : ℕ) : ℝ)) (w / 8))) ≤
        Real.exp (-(krRate D θ / 64 * w)) := Real.exp_le_exp.2 (by linarith)
    unfold krRate at this ⊢
    linarith

/-- **Downward short-time pin** (forward step `1 - aX`, from `w` to `0`): for `1 ≤ n ≤ w/4` and
`A ≤ w`, `q_n(w, 0) ≤ 6 D e^{-c₀ w}`. -/
theorem krDens_down_short {θ vlo vhi K L w A : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a 1 a) (hAw : A ≤ w) {n : ℕ} (hn : 1 ≤ n)
    (hnw : (n : ℝ) ≤ w / 4) :
    krDens (Icc 0 w) ν f 1 a n w 0 ≤ 6 * D * Real.exp (-(krC₀ D θ * w)) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hw0 := H.hw0
  have hD0 := H.hD0
  have hθ := H.hθ
  have ha : 0 < a := by
    have hAw' : A / w ≤ 1 := by rw [div_le_one hw0]; exact hAw
    have h1 := (abs_le.1 H.haA).1
    have ha0 : 0 ≤ a := by linarith
    have := H.ha₁
    rw [abs_of_nonneg ha0] at this
    linarith
  have hn'w : (n' : ℝ) ≤ w / 4 := by push_cast at hnw; linarith
  have hEm : MeasurableSet {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := kr_measurableSet_fall w a n'
  have hF : Measurable fun g : ℕ → ℝ =>
      krAlive (Icc 0 w) 1 a n' w g * krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0 :=
    (measurable_krAlive_right H.hJ 1 a n' w).mul ((measurable_krKer_prod H.hJ H.hf 1 a).comp
      (((measurable_kWalk_prod 1 a n').comp (measurable_const.prodMk measurable_id)).prodMk
        measurable_const))
  have hFM : ∀ g, |krAlive (Icc 0 w) 1 a n' w g * krKer (Icc 0 w) f 1 a (kWalk w 1 a g n') 0| ≤
      D / |a| := fun g => by
    rw [abs_mul, abs_of_nonneg (krAlive_nonneg _ _ _)]
    calc _ ≤ 1 * (D / |a|) :=
          mul_le_mul (krAlive_le_one _ _ _) (abs_krKer_le H.hf0 H.hfD _ _) (abs_nonneg _)
            zero_le_one
      _ = D / |a| := one_mul _
  have hint : Integrable (fun g : ℕ → ℝ => 2 * D * Real.exp (-(θ / 4 * w)) +
      {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2}.indicator (fun _ => 2 * D) g) (iidLaw ν) :=
    (integrable_const _).add ((integrable_const _).indicator hEm)
  have hI : krDens (Icc 0 w) ν f 1 a (n' + 1) w 0 ≤
      2 * D * Real.exp (-(θ / 4 * w)) +
        2 * D * (iidLaw ν).real {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := by
    rw [krDens_succ]
    refine (integral_mono (kr_integrable_of_bdd hF hFM) hint
      (kr_down_pointwise ν H ha n')).trans (le_of_eq ?_)
    rw [integral_add (integrable_const _) ((integrable_const _).indicator hEm),
      integral_const, integral_indicator_const _ hEm, smul_eq_mul, smul_eq_mul, probReal_univ,
      one_mul]
    ring
  have hPE := kr_fall_prob ν H hAw ha hn'w
  have hc₀ := krC₀_pos H.hD hθ
  have he1 : Real.exp (-(θ / 4 * w)) ≤ Real.exp (-(krC₀ D θ * w)) := by
    apply Real.exp_le_exp.2
    have : krC₀ D θ ≤ θ / 4 := min_le_left _ _
    nlinarith
  have he2 : Real.exp (-(krRate D θ / 64 * w)) ≤ Real.exp (-(krC₀ D θ * w)) := by
    apply Real.exp_le_exp.2
    have : krC₀ D θ ≤ krRate D θ / 64 := min_le_right _ _
    nlinarith
  have hP0 : 0 ≤ (iidLaw ν).real {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := measureReal_nonneg
  calc krDens (Icc 0 w) ν f 1 a (n' + 1) w 0
      ≤ 2 * D * Real.exp (-(θ / 4 * w)) +
        2 * D * (iidLaw ν).real {g : ℕ → ℝ | kWalk w 1 a g n' < w / 2} := hI
    _ ≤ 2 * D * Real.exp (-(krC₀ D θ * w)) + 2 * D * (2 * Real.exp (-(krC₀ D θ * w))) := by
        have e1 := mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ 2 * D)
        have e2 := mul_le_mul_of_nonneg_left (hPE.trans (mul_le_mul_of_nonneg_left he2
          (by norm_num))) (by positivity : (0 : ℝ) ≤ 2 * D)
        linarith
    _ = 6 * D * Real.exp (-(krC₀ D θ * w)) := by ring

/-! ## Short time, both directions -/

/-- **Short-time opposite-side pin**: for boundary `b ≠ b'`, `1 ≤ n ≤ w/4` and `A ≤ w`, in either
direction, `q_n(b, b') ≤ 6 D e^{-c₀ w}` (the pin against the jumps is exactly `0`). -/
theorem krDens_bdry_pin_short {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') (hAw : A ≤ w) {b b' : ℝ} (hb : b = 0 ∨ b = w)
    (hb' : b' = 0 ∨ b' = w) (hbb : b ≠ b') {n : ℕ} (hn : 1 ≤ n) (hnw : (n : ℝ) ≤ w / 4) :
    krDens (Icc 0 w) ν f β a' n b b' ≤ 6 * D * Real.exp (-(krC₀ D θ * w)) := by
  have hw0 := H.hw0
  have hD0 := H.hD0
  have hnw' : (n : ℝ) ≤ w := by linarith
  have hpos : 0 ≤ 6 * D * Real.exp (-(krC₀ D θ * w)) := by positivity
  -- the forward chain from the same data
  have H1 : KrBand D θ vlo vhi K L ν f w A a 1 a :=
    { H with hβ := Or.inl ⟨rfl, rfl⟩ }
  have ha : 0 < a := by
    have hAw' : A / w ≤ 1 := by rw [div_le_one hw0]; exact hAw
    have h1 := (abs_le.1 H.haA).1
    have ha0 : 0 ≤ a := by linarith
    have := H.ha₁
    rw [abs_of_nonneg ha0] at this
    linarith
  have hup : krDens (Icc 0 w) ν f 1 a n 0 w = 0 :=
    krDens_up_zero ν H.hν H.hθ H.hvlo H.hfz ha hn hnw'
  have hdown := krDens_down_short ν H1 hAw hn hnw
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rcases H.hβ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hbb
    · rw [hup]; exact hpos
    · exact hdown
    · exact absurd rfl hbb
  · rw [krDens_symm ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' n' b b', neg_neg, neg_neg]
    rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl
    · exact absurd rfl hbb
    · exact hdown
    · rw [hup]; exact hpos
    · exact absurd rfl hbb

end

end PGM
