import PLAStochastic.Index.Algorithm.SegmentLength
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# WP5, D1–D2: the deterministic envelope comparison

Blueprint `kmt-blueprint/main.tex` Lemma 7.3 (`lem:envelope`) and Lemma 7.4(a) (`lem:pathwise`),
in existential form.  Keys `x_t = t + R_t`, `t ≤ k`, with oscillation `osc R ≤ D < k/4`.

* `affine_of_keys`: an `(a, b)`-fit of the keys with error `e` yields a `(λ, c)`-fit of the
  fluctuation `R` with error `e + 2D²/k`;
* `keys_of_affine`: conversely.

Both directions are direct: the fallback `λ = 0`, `c = midpoint` handles `e ≥ D/2`, and the
substitution `λ = (1 - a)/a` (`a = 1/(1 + λ)`) with the two-point bound at `t = 0, k` handles
the rest.  No infimum is used.
-/

namespace PGM

open Finset

/-! ## Midpoint fit of a bounded-oscillation sequence -/

/-- Any real sequence with oscillation at most `D` on `{0, …, k}` is within `D/2` of a constant. -/
theorem exists_const_of_osc_le {R : ℕ → ℝ} {k : ℕ} {D : ℝ}
    (hD : ∀ s ≤ k, ∀ t ≤ k, |R s - R t| ≤ D) :
    ∃ c : ℝ, ∀ t ≤ k, |R t - c| ≤ D / 2 := by
  classical
  have hne : (Finset.range (k + 1)).Nonempty := ⟨0, by simp⟩
  set M := (Finset.range (k + 1)).sup' hne R with hM
  set m := (Finset.range (k + 1)).inf' hne R with hm
  obtain ⟨tM, htM, hMeq⟩ := Finset.exists_mem_eq_sup' hne R
  obtain ⟨tm, htm, hmeq⟩ := Finset.exists_mem_eq_inf' hne R
  have hMm : M - m ≤ D := by
    rw [hM, hm, hMeq, hmeq]
    have := hD tM (by simpa [Finset.mem_range, Nat.lt_succ_iff] using htM) tm
      (by simpa [Finset.mem_range, Nat.lt_succ_iff] using htm)
    exact (le_abs_self _).trans this
  refine ⟨(M + m) / 2, fun t ht => ?_⟩
  have htmem : t ∈ Finset.range (k + 1) := by simpa [Finset.mem_range, Nat.lt_succ_iff] using ht
  have h1 : R t ≤ M := Finset.le_sup' R htmem
  have h2 : m ≤ R t := Finset.inf'_le R htmem
  rw [abs_le]
  constructor <;> linarith

/-! ## Keys to fluctuation -/

/-- **Envelope, one direction.**  If `(a, b)` fits the keys `t + R_t` with error `e` and
`osc R ≤ D < k/4`, then some `(λ, c)` fits `R` with error `e + 2D²/k`. -/
theorem affine_of_keys {R : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) {D e a b : ℝ} (hD0 : 0 ≤ D)
    (hDk : D < k / 4) (hD : ∀ s ≤ k, ∀ t ≤ k, |R s - R t| ≤ D)
    (hfit : ∀ t ≤ k, |(t : ℝ) - (a * (t + R t) + b)| ≤ e) :
    ∃ lam c : ℝ, ∀ t ≤ k, |R t - lam * t - c| ≤ e + 2 * D ^ 2 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hDD : 0 ≤ 2 * D ^ 2 / k := by positivity
  obtain ⟨c₀, hc₀⟩ := exists_const_of_osc_le hD
  -- the two-point consequence of the fit
  have h0 := hfit 0 (Nat.zero_le _)
  have hkk := hfit k le_rfl
  simp only [Nat.cast_zero, zero_add] at h0
  have hRk := hD k le_rfl 0 (Nat.zero_le _)
  -- fallback: `λ = 0`, `c = c₀`, valid as soon as `D/2 ≤ e`
  have fallback : D / 2 ≤ e → ∃ lam c : ℝ, ∀ t ≤ k, |R t - lam * t - c| ≤ e + 2 * D ^ 2 / k := by
    intro he
    refine ⟨0, c₀, fun t ht => ?_⟩
    have := hc₀ t ht
    rw [zero_mul, sub_zero]
    linarith
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) h0
  rcases le_or_gt a 0 with ha | ha
  · -- `a ≤ 0`: the fit error is at least `k/2 > D/2`
    apply fallback
    have h1 : |(k : ℝ) - (a * (k + R k) + b)| ≤ e := hkk
    have h2 : |(0 : ℝ) - (a * R 0 + b)| ≤ e := by simpa using h0
    rw [abs_le] at h1 h2 hRk
    have : (k : ℝ) - a * k - a * (R k - R 0) ≤ 2 * e := by linarith
    have hneg : a * (R k - R 0) ≤ -a * D := by nlinarith
    nlinarith
  · -- `a > 0`: substitute `λ = (1 - a)/a`, `c = -b/a`
    set lam := (1 - a) / a with hlam
    set c := -b / a with hc
    have hlam1 : -1 < lam := by
      rw [hlam, lt_div_iff₀ ha]; linarith
    have hfit' : ∀ t ≤ k, |R t - lam * t - c| ≤ (1 + lam) * e := by
      intro t ht
      have h := hfit t ht
      have e1 : (t : ℝ) - (a * (t + R t) + b) = -a * (R t - lam * t - c) := by
        rw [hlam, hc]; field_simp; ring
      rw [e1, abs_mul, abs_neg, abs_of_pos ha] at h
      have e2 : (1 + lam) = 1 / a := by rw [hlam]; field_simp; ring
      rw [e2]
      have h' : |R t - lam * t - c| ≤ e / a := by
        rw [le_div_iff₀ ha, mul_comm]; exact h
      calc |R t - lam * t - c| ≤ e / a := h'
        _ = 1 / a * e := by ring
    rcases le_or_gt lam 0 with hl | hl
    · -- `λ ≤ 0`: the factor `1 + λ ≤ 1`
      refine ⟨lam, c, fun t ht => ?_⟩
      have := hfit' t ht
      nlinarith
    · rcases le_or_gt (D / 2) e with he | he
      · exact fallback he
      · -- `λ > 0`, `e < D/2`: two-point bound gives `λ < 8D/(3k)`
        refine ⟨lam, c, fun t ht => ?_⟩
        have h1 := hfit' k le_rfl
        have h2 := hfit' 0 (Nat.zero_le _)
        simp only [Nat.cast_zero, mul_zero, sub_zero] at h2
        rw [abs_le] at h1 h2 hRk
        have hlk : lam * k ≤ 2 * (1 + lam) * e + D := by nlinarith
        have hlk' : lam * (k - D) < 2 * D := by nlinarith
        have hkD : 3 * k / 4 < k - D := by linarith
        have hlam8 : lam < 8 * D / (3 * k) := by
          rw [lt_div_iff₀ (by positivity)]
          nlinarith
        have := hfit' t ht
        have hle : lam * e ≤ 2 * D ^ 2 / k := by
          have h3 : lam * e ≤ 8 * D / (3 * k) * (D / 2) := by
            apply mul_le_mul hlam8.le he.le he0 (by positivity)
          calc lam * e ≤ 8 * D / (3 * k) * (D / 2) := h3
            _ = 4 * D ^ 2 / (3 * k) := by ring
            _ ≤ 2 * D ^ 2 / k := by
                rw [div_le_div_iff₀ (by positivity) hk0]
                nlinarith [sq_nonneg D]
        nlinarith

/-! ## Fluctuation to keys -/

/-- **Envelope, other direction.**  If `(λ, c)` fits `R` with error `e` and `osc R ≤ D < k/4`,
then some `(a, b)` fits the keys `t + R_t` with error `e + 2D²/k`. -/
theorem keys_of_affine {R : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) {D e lam c : ℝ} (hD0 : 0 ≤ D)
    (hDk : D < k / 4) (hD : ∀ s ≤ k, ∀ t ≤ k, |R s - R t| ≤ D)
    (hfit : ∀ t ≤ k, |R t - lam * t - c| ≤ e) :
    ∃ a b : ℝ, ∀ t ≤ k, |(t : ℝ) - (a * (t + R t) + b)| ≤ e + 2 * D ^ 2 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hDD : 0 ≤ 2 * D ^ 2 / k := by positivity
  have h0 := hfit 0 (Nat.zero_le _)
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h0
  have he0 : 0 ≤ e := le_trans (abs_nonneg _) h0
  obtain ⟨c₀, hc₀⟩ := exists_const_of_osc_le hD
  rcases le_or_gt (D / 2) e with he | he
  · -- fallback `a = 1`, `b = -c₀`
    refine ⟨1, -c₀, fun t ht => ?_⟩
    have := hc₀ t ht
    have e1 : (t : ℝ) - (1 * (t + R t) + -c₀) = -(R t - c₀) := by ring
    rw [e1, abs_neg]
    linarith
  · -- `e < D/2` forces `|λ| < 2D/k`
    have h1 := hfit k le_rfl
    have hRk := hD k le_rfl 0 (Nat.zero_le _)
    rw [abs_le] at h1 h0 hRk
    have hlk : |lam| * k < 2 * D := by
      rcases le_or_gt 0 lam with hl | hl
      · rw [abs_of_nonneg hl]; nlinarith
      · rw [abs_of_neg hl]; nlinarith
    set δ := 2 * D / k with hδ
    have hδ0 : 0 ≤ δ := by positivity
    have hδhalf : δ < 1 / 2 := by
      rw [hδ, div_lt_iff₀ hk0]; linarith
    have hlamδ : |lam| < δ := by
      rw [hδ, lt_div_iff₀ hk0]; exact hlk
    have hpos : 0 < 1 + lam := by
      have := neg_abs_le lam
      linarith
    refine ⟨1 / (1 + lam), -(c / (1 + lam)), fun t ht => ?_⟩
    have hf := hfit t ht
    have e1 : (t : ℝ) - (1 / (1 + lam) * (t + R t) + -(c / (1 + lam))) =
        -(R t - lam * t - c) / (1 + lam) := by
      field_simp
      ring
    rw [e1, abs_div, abs_neg, abs_of_pos hpos, div_le_iff₀ hpos]
    -- `e/(1+λ) ≤ e(1 + 2δ)` and `2δe ≤ 2D²/k`
    have h2 : e ≤ (e + 2 * D ^ 2 / k) * (1 + lam) := by
      have hl : -δ < lam := by
        have := neg_abs_le lam
        linarith
      have h3 : 2 * D ^ 2 / k * (1 - δ) ≥ δ * e := by
        have e2 : 2 * D ^ 2 / k = δ * D := by rw [hδ]; ring
        rw [e2]
        have : δ * e ≤ δ * (D / 2) := mul_le_mul_of_nonneg_left he.le hδ0
        nlinarith
      nlinarith
    linarith

/-! ## Pathwise comparison (D2(a)) -/

/-- A fit of the keys `t + s_t` transfers to any nearby sequence `g`. -/
theorem affine_of_keys_close {s g : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) {D e η a b : ℝ} (hD0 : 0 ≤ D)
    (hDk : D < k / 4) (hD : ∀ t₁ ≤ k, ∀ t₂ ≤ k, |s t₁ - s t₂| ≤ D)
    (hclose : ∀ t ≤ k, |s t - g t| ≤ η)
    (hfit : ∀ t ≤ k, |(t : ℝ) - (a * (t + s t) + b)| ≤ e) :
    ∃ lam c : ℝ, ∀ t ≤ k, |g t - lam * t - c| ≤ e + 2 * D ^ 2 / k + η := by
  obtain ⟨lam, c, h⟩ := affine_of_keys hk hD0 hDk hD hfit
  refine ⟨lam, c, fun t ht => ?_⟩
  have h1 := h t ht
  have h2 := hclose t ht
  calc |g t - lam * t - c| = |(s t - lam * t - c) - (s t - g t)| := by ring_nf
    _ ≤ |s t - lam * t - c| + |s t - g t| := abs_sub _ _
    _ ≤ e + 2 * D ^ 2 / k + η := by linarith

/-- A fit of a nearby sequence `g` transfers back to the keys `t + s_t`. -/
theorem keys_of_affine_close {s g : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) {D e η lam c : ℝ} (hD0 : 0 ≤ D)
    (hDk : D < k / 4) (hD : ∀ t₁ ≤ k, ∀ t₂ ≤ k, |s t₁ - s t₂| ≤ D)
    (hclose : ∀ t ≤ k, |s t - g t| ≤ η)
    (hfit : ∀ t ≤ k, |g t - lam * t - c| ≤ e) :
    ∃ a b : ℝ, ∀ t ≤ k, |(t : ℝ) - (a * (t + s t) + b)| ≤ e + η + 2 * D ^ 2 / k := by
  have hfit' : ∀ t ≤ k, |s t - lam * t - c| ≤ e + η := by
    intro t ht
    have h1 := hfit t ht
    have h2 := hclose t ht
    calc |s t - lam * t - c| = |(g t - lam * t - c) + (s t - g t)| := by ring_nf
      _ ≤ |g t - lam * t - c| + |s t - g t| := abs_add_le _ _
      _ ≤ e + η := by linarith
  exact keys_of_affine hk hD0 hDk hD hfit'

end PGM
