import PLAStochastic.Index.GEP.Kernel.Row.BoundarySurvival

/-!
# WP4 kernel rows: medium-time boundary row bounds

Source: `influence-lipschitz.md` §3, second paragraph: for `|a - 1| ≤ A/w` and `n ≤ w²`,
`‖q_n(b, ·)‖_∞ ≤ K (1 + A) n⁻¹` and `‖q_n(b, ·)‖₂ ≤ K (1 + A) n^{-3/4}` from any boundary point
`b ∈ {0, w}` of the band, in either direction.

* `KrFreeBound D θ vlo vhi L` is the class-uniform free-density bound (`krDens_le_free`).
* `KrBand` collects the standing hypotheses of the band chain (class, density representative,
  band width, slope window, boundary direction) so that later statements stay short.  Nothing in
  it is an unproved premise: `KrLinearSurvival` is the conclusion of `linearSurvival_regLaw`
  (separate module) and `KrFreeBound` is provided by `krFreeBound_exists`.
* `krDens_bdry_medium`: `q_n(b, z) ≤ 8 (D + K L) (1 + A) / n` for `1 ≤ n ≤ 2 w²` (the survival
  half of the split is `⌊n/2⌋ ≤ w²`).
* `integral_sq_krDens_bdry_medium`: `∫ q_n(b, z)² dz ≤ 8 (D + K L) K (1 + A)² / (n √n)` for
  `1 ≤ n ≤ w²`.
* `kr_cauchy_schwarz`: the real Cauchy–Schwarz inequality used for the large-time bounds.

All constants are chosen before the law and lose only a fixed power of `(1 + A)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {J : Set ℝ} {β a : ℝ} (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ} {D : ℝ}

/-! ## Interfaces and the standing hypotheses -/

/-- **Interface**: the class-uniform free-density bound, i.e. the conclusion of
`krDens_le_free` for its constant `L`. -/
def KrFreeBound (D θ vlo vhi L : ℝ) : Prop :=
  0 < L ∧ ∀ ν : ProbabilityMeasure ℝ, RegLaw D θ vlo vhi ν →
    ∀ f : ℝ → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ x, f x ≤ D) →
    (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)) →
    ∀ J : Set ℝ, MeasurableSet J → ∀ β a : ℝ, a ≠ 0 → ∀ n : ℕ, 2 ≤ n → ∀ y₀ z : ℝ,
      krDens J ν f β a (n + 1) y₀ z ≤ L / (Real.sqrt n * |a|)

theorem krFreeBound_exists (D θ vlo vhi : ℝ) (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo)
    (hv : vlo ≤ vhi) : ∃ L : ℝ, KrFreeBound D θ vlo vhi L := by
  obtain ⟨L, hL, h⟩ := krDens_le_free D θ vlo vhi hD hθ hvlo hv
  exact ⟨L, hL, h⟩

/-- The standing hypotheses of the near-critical band chain on `[0, w]`:
class parameters, the two interfaces, a law of the class with its density representative `f`,
the band width `w ≥ 1`, the slope window `|a - 1| ≤ A/w`, `1/2 ≤ |a| ≤ 2`, and the direction
`(β, a') ∈ {(1, a), (-1, -a)}` (forward step `1 - aX`, reverse step `aX - 1`).
The density facts `hf, hf0, hfz, hfD, hfe, hνf` are exactly those of `kr_regLaw_density`. -/
structure KrBand (D θ vlo vhi K L : ℝ) (ν : ProbabilityMeasure ℝ) (f : ℝ → ℝ)
    (w A a β a' : ℝ) : Prop where
  hD : 0 < D
  hθ : 0 < θ
  hvlo : 0 < vlo
  hvhi : vlo ≤ vhi
  hLS : KrLinearSurvival D θ vlo vhi K
  hFree : KrFreeBound D θ vlo vhi L
  hν : RegLaw D θ vlo vhi ν
  hK : 0 ≤ K
  hf : Measurable f
  hf0 : ∀ x, 0 ≤ f x
  hfz : ∀ x, x ≤ 0 → f x = 0
  hfD : ∀ x, f x ≤ D
  hfe : ∀ x, f x ≤ D * Real.exp (-θ * x)
  hνf : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x))
  hw : 1 ≤ w
  hA : 0 ≤ A
  haA : |a - 1| ≤ A / w
  ha₁ : 1 / 2 ≤ |a|
  ha₂ : |a| ≤ 2
  hβ : (β = 1 ∧ a' = a) ∨ (β = -1 ∧ a' = -a)

namespace KrBand

variable {ν} {θ vlo vhi K L w A a' : ℝ}

theorem habs (H : KrBand D θ vlo vhi K L ν f w A a β a') : |a'| = |a| := by
  rcases H.hβ with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp

theorem ha' (H : KrBand D θ vlo vhi K L ν f w A a β a') : a' ≠ 0 := by
  intro h
  have := H.ha₁
  rw [← H.habs, h, abs_zero] at this
  norm_num at this

theorem hw0 (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 < w := lt_of_lt_of_le one_pos H.hw

theorem hD0 (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 ≤ D := (H.hf0 0).trans (H.hfD 0)

theorem hL0 (H : KrBand D θ vlo vhi K L ν f w A a β a') : 0 < L := H.hFree.1

/-- The reversed chain satisfies the same hypotheses. -/
theorem rev (H : KrBand D θ vlo vhi K L ν f w A a β a') :
    KrBand D θ vlo vhi K L ν f w A a (-β) (-a') where
  hD := H.hD
  hθ := H.hθ
  hvlo := H.hvlo
  hvhi := H.hvhi
  hLS := H.hLS
  hFree := H.hFree
  hν := H.hν
  hK := H.hK
  hf := H.hf
  hf0 := H.hf0
  hfz := H.hfz
  hfD := H.hfD
  hfe := H.hfe
  hνf := H.hνf
  hw := H.hw
  hA := H.hA
  haA := H.haA
  ha₁ := H.ha₁
  ha₂ := H.ha₂
  hβ := by rcases H.hβ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp

theorem hJ (_H : KrBand D θ vlo vhi K L ν f w A a β a') : MeasurableSet (Icc (0 : ℝ) w) :=
  measurableSet_Icc

theorem hJfin (_H : KrBand D θ vlo vhi K L ν f w A a β a') : volume (Icc (0 : ℝ) w) ≠ ⊤ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top

theorem bdry_mem (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w) :
    b ∈ Icc (0 : ℝ) w := by
  have := H.hw0
  rcases hb with rfl | rfl <;> constructor <;> linarith

/-- The pointwise crude bound `q_n ≤ D/|a'| ≤ 2 D`. -/
theorem krDens_le_two_D (H : KrBand D θ vlo vhi K L ν f w A a β a') (n : ℕ) (y₀ z : ℝ) :
    krDens (Icc 0 w) ν f β a' n y₀ z ≤ 2 * D := by
  refine (krDens_le_div ν H.hf0 H.hfD n y₀ z).trans ?_
  have ha0 : 0 < |a| := lt_of_lt_of_le (by norm_num) H.ha₁
  rw [H.habs, div_le_iff₀ ha0]
  nlinarith [H.hD0, H.ha₁]

/-- The free-density bound in the band, with `|a'| ≥ 1/2` absorbed. -/
theorem krDens_le_free_two (H : KrBand D θ vlo vhi K L ν f w A a β a') {k : ℕ} (hk : 2 ≤ k)
    (y₀ z : ℝ) :
    krDens (Icc 0 w) ν f β a' (k + 1) y₀ z ≤ 2 * L / Real.sqrt k := by
  have h := H.hFree.2 ν H.hν f H.hf H.hf0 H.hfD H.hνf _ H.hJ β a' H.ha' k hk y₀ z
  refine h.trans ?_
  rw [H.habs]
  have hk0 : 0 < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < k))
  have ha0 : 0 < |a| := lt_of_lt_of_le (by norm_num) H.ha₁
  rw [div_le_div_iff₀ (mul_pos hk0 ha0) hk0]
  have : L * Real.sqrt k * (1 / 2) ≤ L * Real.sqrt k * |a| :=
    mul_le_mul_of_nonneg_left H.ha₁ (by positivity [H.hL0])
  nlinarith [this]

/-- Medium-time boundary survival `s_n(b) ≤ K (1 + A) / √n` for `1 ≤ n ≤ w²`. -/
theorem krSurv_medium (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 1 ≤ n) (hnw : (n : ℝ) ≤ w ^ 2) :
    krSurv (Icc 0 w) (ν : Measure ℝ) β a' n b ≤ K * (1 + A) / Real.sqrt n :=
  krSurv_bdry_le_medium ν H.hLS H.hν H.hK H.hw0 H.hA H.haA H.ha₁ H.ha₂ hn hnw H.hβ hb

end KrBand

/-! ## Constants -/

/-- Medium-time row sup constant `8 (D + K L)`. -/
def krC₁ (D K L : ℝ) : ℝ := 8 * (D + K * L)

/-- Medium-time row `L²` constant `8 (D + K L) K`. -/
def krC₂ (D K L : ℝ) : ℝ := 8 * (D + K * L) * K

theorem krC₁_nonneg {K L : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L) : 0 ≤ krC₁ D K L := by
  unfold krC₁; positivity

theorem krC₂_nonneg {K L : ℝ} (hD : 0 ≤ D) (hK : 0 ≤ K) (hL : 0 ≤ L) : 0 ≤ krC₂ D K L := by
  unfold krC₂; positivity

/-! ## The medium-time sup bound -/

/-- Arithmetic of the half split: for `n ≥ 5`, `m := n / 2` and `k := n - n / 2 - 1` satisfy
`1 ≤ m`, `2 ≤ k`, `n = (m - 1 + 1) + (k + 1)`, `m ≤ n/2` and `√(m k) ≥ n / 4`. -/
theorem kr_half_split {n : ℕ} (hn : 5 ≤ n) :
    1 ≤ n / 2 ∧ 2 ≤ n - n / 2 - 1 ∧ n = (n / 2 - 1 + 1) + (n - n / 2 - 1 + 1) ∧
      (n / 2 : ℕ) ≤ (n : ℝ) / 2 ∧
      (n : ℝ) / 4 ≤ Real.sqrt ((n / 2 : ℕ) * ((n - n / 2 - 1 : ℕ) : ℝ)) := by
  have h1 : 1 ≤ n / 2 := by omega
  have h2 : 2 ≤ n - n / 2 - 1 := by omega
  have h3 : n = (n / 2 - 1 + 1) + (n - n / 2 - 1 + 1) := by omega
  have hm : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have h' : (2 : ℝ) * (n / 2 : ℕ) ≤ n := by exact_mod_cast this
    linarith
  refine ⟨h1, h2, h3, hm, ?_⟩
  have hm' : (n : ℝ) - 1 ≤ 2 * (n / 2 : ℕ) := by
    have : n - 1 ≤ 2 * (n / 2) := by omega
    have h' : ((n - 1 : ℕ) : ℝ) ≤ 2 * (n / 2 : ℕ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    simpa using h'
  have hk' : (n : ℝ) - 3 ≤ 2 * ((n - n / 2 - 1 : ℕ) : ℝ) := by
    have : n - 3 ≤ 2 * (n - n / 2 - 1) := by omega
    have h' : ((n - 3 : ℕ) : ℝ) ≤ 2 * ((n - n / 2 - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by omega)] at h'
    simpa using h'
  have hn' : (5 : ℝ) ≤ n := by exact_mod_cast hn
  refine Real.le_sqrt_of_sq_le ?_
  have hm0 : (0 : ℝ) ≤ (n / 2 : ℕ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ ((n - n / 2 - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul hm' hk' (by linarith) (by linarith)]

/-- **Medium-time boundary row sup bound**: `q_n(b, z) ≤ 8 (D + K L) (1 + A) / n` for
`1 ≤ n ≤ 2 w²`, all `z`. -/
theorem krDens_bdry_medium {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 1 ≤ n) (hnw : (n : ℝ) ≤ 2 * w ^ 2) (z : ℝ) :
    krDens (Icc 0 w) ν f β a' n b z ≤ krC₁ D K L * (1 + A) / n := by
  have hD0 := H.hD0
  have hL0 := H.hL0
  have hK := H.hK
  have hA := H.hA
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hKL : 0 ≤ K * L := mul_nonneg hK hL0.le
  unfold krC₁
  by_cases hn4 : n ≤ 4
  · refine (H.krDens_le_two_D n b z).trans ?_
    have hn4' : (n : ℝ) ≤ 4 := by exact_mod_cast hn4
    rw [le_div_iff₀ hn0]
    nlinarith
  · have hn5 : 5 ≤ n := by omega
    obtain ⟨hm1, hk2, heq, hmhalf, hsq⟩ := kr_half_split hn5
    set m := n / 2 with hm
    set k := n - n / 2 - 1 with hk
    have hmw : ((m - 1 + 1 : ℕ) : ℝ) ≤ w ^ 2 := by
      rw [Nat.sub_add_cancel hm1]
      linarith
    have hB : ∀ y, krDens (Icc 0 w) ν f β a' (k + 1) y z ≤ 2 * L / Real.sqrt k :=
      fun y => H.krDens_le_free_two hk2 y z
    have h1 := krDens_add_le_krSurv_mul ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha' (m - 1) k b z hB
    rw [← heq] at h1
    refine h1.trans ?_
    have hs := H.krSurv_medium hb (n := m - 1 + 1) (by omega) hmw
    have hk0 : 0 < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < k))
    have hm0 : 0 < Real.sqrt ((m - 1 + 1 : ℕ) : ℝ) :=
      Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < m - 1 + 1))
    have hB0 : 0 ≤ 2 * L / Real.sqrt k := by positivity
    have hs0 : 0 ≤ K * (1 + A) / Real.sqrt ((m - 1 + 1 : ℕ) : ℝ) := by positivity
    calc krSurv (Icc 0 w) (ν : Measure ℝ) β a' (m - 1 + 1) b * (2 * L / Real.sqrt k)
        ≤ K * (1 + A) / Real.sqrt ((m - 1 + 1 : ℕ) : ℝ) * (2 * L / Real.sqrt k) :=
          mul_le_mul_of_nonneg_right hs hB0
      _ = 2 * (K * L) * (1 + A) / Real.sqrt (((m - 1 + 1 : ℕ) : ℝ) * k) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), div_mul_div_comm]
          ring
      _ ≤ 8 * (D + K * L) * (1 + A) / n := by
          have hmm : ((m - 1 + 1 : ℕ) : ℝ) = (m : ℕ) := by rw [Nat.sub_add_cancel hm1]
          rw [hmm]
          have hsq0 : 0 < Real.sqrt ((m : ℕ) * (k : ℝ)) := lt_of_lt_of_le (by positivity) hsq
          rw [div_le_div_iff₀ hsq0 hn0]
          have : 2 * (K * L) * (1 + A) * n = 8 * (K * L) * (1 + A) * (n / 4) := by ring
          rw [this]
          calc 8 * (K * L) * (1 + A) * (n / 4)
              ≤ 8 * (K * L) * (1 + A) * Real.sqrt ((m : ℕ) * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ ≤ 8 * (D + K * L) * (1 + A) * Real.sqrt ((m : ℕ) * (k : ℝ)) := by
                gcongr
                linarith

/-! ## The medium-time `L²` bound -/

/-- **Medium-time boundary row `L²` bound**: `∫ q_n(b, z)² dz ≤ 8 (D + K L) K (1 + A)² / (n √n)`
for `1 ≤ n ≤ w²`. -/
theorem integral_sq_krDens_bdry_medium {θ vlo vhi K L w A a' : ℝ}
    (H : KrBand D θ vlo vhi K L ν f w A a β a') {b : ℝ} (hb : b = 0 ∨ b = w)
    {n : ℕ} (hn : 1 ≤ n) (hnw : (n : ℝ) ≤ w ^ 2) :
    ∫ z, krDens (Icc 0 w) ν f β a' n b z ^ 2 ≤
      krC₂ D K L * (1 + A) ^ 2 / (n * Real.sqrt n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn0 : (0 : ℝ) < (n' + 1 : ℕ) := by exact_mod_cast hn
  have hsup : ∀ z, krDens (Icc 0 w) ν f β a' (n' + 1) b z ≤ krC₁ D K L * (1 + A) / (n' + 1 : ℕ) :=
    fun z => krDens_bdry_medium ν H hb hn (by linarith [sq_nonneg w]) z
  have hint : Integrable (fun z => krDens (Icc 0 w) ν f β a' (n' + 1) b z) :=
    kr_integrable_krDens_right ν H.hJ H.hJfin H.hf H.hf0 H.hfD (n' + 1) b
  have hint2 : Integrable (fun z => krDens (Icc 0 w) ν f β a' (n' + 1) b z ^ 2) :=
    kr_integrable_sq_of_bdd H.hJ H.hJfin (measurable_krDens_right ν H.hJ H.hf β a' (n' + 1) b)
      (fun _ hz => krDens_eq_zero_of_right_notMem ν hz (n' + 1) b)
      (abs_krDens_le ν H.hf0 H.hfD (n' + 1) b)
  have hC := krC₁_nonneg (K := K) (L := L) H.hD0 H.hK H.hL0.le
  have hA := H.hA
  calc ∫ z, krDens (Icc 0 w) ν f β a' (n' + 1) b z ^ 2
      ≤ ∫ z, krC₁ D K L * (1 + A) / (n' + 1 : ℕ) * krDens (Icc 0 w) ν f β a' (n' + 1) b z := by
        refine integral_mono hint2 (hint.const_mul _) fun z => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hsup z) (krDens_nonneg ν H.hf0 _ _ _)
    _ = krC₁ D K L * (1 + A) / (n' + 1 : ℕ) * krSurv (Icc 0 w) (ν : Measure ℝ) β a' (n' + 1) b := by
        rw [integral_const_mul, integral_krDens ν H.hJ H.hJfin H.hf H.hf0 H.hfD H.hνf H.ha']
    _ ≤ krC₁ D K L * (1 + A) / (n' + 1 : ℕ) * (K * (1 + A) / Real.sqrt (n' + 1 : ℕ)) :=
        mul_le_mul_of_nonneg_left (H.krSurv_medium hb hn hnw) (by positivity)
    _ = krC₂ D K L * (1 + A) ^ 2 / ((n' + 1 : ℕ) * Real.sqrt (n' + 1 : ℕ)) := by
        unfold krC₁ krC₂
        rw [div_mul_div_comm]
        ring

/-! ## Cauchy–Schwarz -/

/-- Real Cauchy–Schwarz for nonnegative square-integrable functions on `ℝ`. -/
theorem kr_cauchy_schwarz {F G : ℝ → ℝ} (hF : Measurable F) (hG : Measurable G)
    (hF0 : ∀ x, 0 ≤ F x) (hG0 : ∀ x, 0 ≤ G x)
    (hF2 : Integrable (fun x => F x ^ 2)) (hG2 : Integrable (fun x => G x ^ 2)) :
    (∫ x, F x * G x) ^ 2 ≤ (∫ x, F x ^ 2) * ∫ x, G x ^ 2 := by
  have hF' : MemLp F (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hF.aestronglyMeasurable).2 hF2
  have hG' : MemLp G (ENNReal.ofReal 2) volume := by
    rw [ENNReal.ofReal_ofNat]
    exact (memLp_two_iff_integrable_sq hG.aestronglyMeasurable).2 hG2
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hF0) (Filter.Eventually.of_forall hG0) hF' hG'
  simp only [Real.rpow_two] at h
  have hF2' : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hG2' : 0 ≤ ∫ x, G x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have h0 : 0 ≤ ∫ x, F x * G x := integral_nonneg fun x => mul_nonneg (hF0 x) (hG0 x)
  have e : ∀ t : ℝ, 0 ≤ t → (t ^ (1 / (2 : ℝ))) ^ 2 = t := fun t ht => by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt ht]
  calc (∫ x, F x * G x) ^ 2
      ≤ ((∫ x, F x ^ 2) ^ (1 / (2 : ℝ)) * (∫ x, G x ^ 2) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = _ := by rw [mul_pow, e _ hF2', e _ hG2']

end

end PGM
