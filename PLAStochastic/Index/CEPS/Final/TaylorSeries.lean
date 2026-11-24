import PLAStochastic.Index.CEPS.Final.TaylorRep
import PLAStochastic.ForMathlib.Analysis.Calculus.TaylorBound

/-!
# Composition of box Taylor representations

* `CepsJetScal.of_series`, `CepsJetDecay.of_series`: if `F ≈ ∑_{n ≤ M} gₙ δⁿ` up to
  `O(|δ|^{M+1})` for every `M`, with `δ` vanishing at the reference point, then `F` has the
  box Taylor representation with coefficients `∑_{n ≤ |α|} gₙ (δ-coefficients)^{*n}(α)`;
* `CepsJetScal.inv`: inverses of scalar representations not vanishing at the reference point;
* `CepsJetDecay.comp_scale`: `f (a u (1 + δ(p)))` for a smooth `f` whose derivatives decay
  stretched-exponentially (one-variable Taylor expansion around `a u`);
* `CepsJetDecay.of_family`: a function approximated by `∑_{α ∈ box N} f_α(u, p) yᵅ` to every
  order, with each `f_α` represented.
-/

namespace PGM

noncomputable section

open Finset

variable {p₀ : ℕ → ℝ} {d : ℕ}

/-! ## Algebra of coefficient families -/

theorem cepsBoxMul_single_zero_left {R : Type*} [CommSemiring R] (a : R)
    (S : (Fin d → ℕ) → R) (γ : Fin d → ℕ) :
    cepsBoxMul (fun α => if α = 0 then a else 0) S γ = a * S γ := by
  classical
  unfold cepsBoxMul
  rw [sum_eq_single 0 (fun b _ hb => by simp [hb])
    (fun h => absurd (mem_cepsLowerBox.mpr fun i => Nat.zero_le (γ i)) h)]
  have : γ - 0 = γ := funext fun i => Nat.sub_zero _
  simp [this]

theorem cepsBoxMul_indicator_right {R : Type*} [CommSemiring R] (T : (Fin d → ℕ) → R)
    (α γ : Fin d → ℕ) :
    cepsBoxMul T (fun β => if β = α then 1 else 0) γ =
      if ∀ i, α i ≤ γ i then T (γ - α) else 0 := by
  classical
  unfold cepsBoxMul
  split_ifs with hαγ
  · rw [sum_eq_single (γ - α)]
    · have : γ - (γ - α) = α := funext fun i => by
        simp [Nat.sub_sub_self (hαγ i)]
      simp [this]
    · intro b hb hne
      rw [mem_cepsLowerBox] at hb
      have : γ - b ≠ α := by
        intro h
        apply hne
        funext i
        have h1 : γ i - b i = α i := congrFun h i
        have h2 : b i ≤ γ i := hb i
        show b i = γ i - α i
        omega
      simp [this]
    · intro h
      exact absurd (mem_cepsLowerBox.mpr fun i => Nat.sub_le _ _) h
  · refine sum_eq_zero fun b hb => ?_
    have : γ - b ≠ α := by
      intro h
      apply hαγ
      intro i
      have := congrFun h i
      simp only [Pi.sub_apply] at this
      omega
    simp [this]

/-- Total degree of a multi-index. -/
theorem cepsJet_degree_le_of_mem_box {N : ℕ} {α : Fin d → ℕ} (hα : α ∈ cepsTaylorBox d N) :
    ∑ i, α i ≤ d * N := by
  rw [mem_cepsTaylorBox] at hα
  calc ∑ i, α i ≤ ∑ _i : Fin d, N := sum_le_sum fun i _ => hα i
    _ = d * N := by simp

/-- Cauchy powers of a family without constant term vanish below the power. -/
theorem cepsBoxPow_eq_zero {R : Type*} [CommSemiring R] {T : (Fin d → ℕ) → R} (hT : T 0 = 0) :
    ∀ (n : ℕ) (α : Fin d → ℕ), ∑ i, α i < n → cepsBoxPow T n α = 0 := by
  intro n
  induction n with
  | zero => intro α h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro α hα
    simp only [cepsBoxPow, cepsBoxMul]
    refine sum_eq_zero fun β hβ => ?_
    rw [mem_cepsLowerBox] at hβ
    by_cases hβα : β = α
    · subst hβα
      have : β - β = 0 := funext fun i => Nat.sub_self _
      rw [this, hT, mul_zero]
    · have hlt : ∑ i, β i < ∑ i, α i := by
        obtain ⟨j, hj⟩ : ∃ j, β j ≠ α j := by
          by_contra hc
          push Not at hc
          exact hβα (funext hc)
        exact sum_lt_sum (fun i _ => hβ i) ⟨j, mem_univ j, lt_of_le_of_ne (hβ j) hj⟩
      rw [ih β (by omega), zero_mul]

/-! ## Monomials -/

theorem CepsJetScal.monomial (α : Fin d → ℕ) :
    CepsJetScal p₀ (fun p => (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))
      (fun β => if β = α then 1 else 0) := by
  classical
  intro N
  refine ⟨1, 1, one_pos, fun p hp => ?_⟩
  by_cases hα : α ∈ cepsTaylorBox d N
  · rw [sum_eq_single α (fun b _ hb => by simp [hb]) (fun h => absurd hα h)]
    simp only [if_true, one_mul, sub_self, norm_zero]
    positivity
  · rw [sum_eq_zero fun b hb => by
      have : b ≠ α := fun h => hα (h ▸ hb)
      simp [this]]
    rw [sub_zero, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_cepsMonomial_le_of_not_mem hp hα

/-! ## Series composition -/

theorem CepsJetScal.of_series {δ : (ℕ → ℝ) → ℂ} {Tδ : (Fin d → ℕ) → ℂ}
    (hδ : CepsJetScal p₀ δ Tδ) (hδ0 : δ p₀ = 0) (g : ℕ → ℂ) {F : (ℕ → ℝ) → ℂ}
    (hF : ∀ M : ℕ, ∃ ρ K : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
      ‖F p - ∑ n ∈ range (M + 1), g n * δ p ^ n‖ ≤ K * ‖δ p‖ ^ (M + 1)) :
    CepsJetScal p₀ F (fun α => ∑ n ∈ range (∑ i, α i + 1), g n * cepsBoxPow Tδ n α) := by
  intro N
  have hT0 : Tδ 0 = 0 := by rw [hδ.coeff_zero, hδ0]
  set M := d * N + N
  have hG : CepsJetScal p₀ (fun p => ∑ n ∈ range (M + 1), g n * δ p ^ n)
      (fun α => ∑ n ∈ range (M + 1), g n * cepsBoxPow Tδ n α) :=
    CepsJetScal.sum _ fun n _ => (hδ.pow n).const_mul (g n)
  refine ((hG N).congr_coeff ?_).of_close ?_
  · intro α hα
    have hdeg := cepsJet_degree_le_of_mem_box hα
    refine (sum_subset (range_subset_range.mpr (by omega)) fun n hn hn' => ?_).symm
    simp only [mem_range, not_lt] at hn hn'
    rw [cepsBoxPow_eq_zero hT0 n α (by omega), mul_zero]
  · obtain ⟨ρ₁, K₁, hρ₁, H₁⟩ := hF M
    obtain ⟨ρ₂, K₂, hρ₂, hK₂, H₂⟩ := hδ.norm_le_of_ref hδ0
    refine ⟨min (min ρ₁ ρ₂) (1 / ((d : ℝ) + 1)), |K₁| * K₂ ^ (M + 1),
      cepsJet_small_box_pos (lt_min hρ₁ hρ₂), fun p hp => ?_⟩
    obtain ⟨hp', -, hs⟩ := cepsJet_small_box hp
    set s := ∑ i : Fin d, |p i - p₀ i|
    have hs0 : 0 ≤ s := cepsJet_size_nonneg p
    have h1 := H₁ p fun i => (hp' i).trans (min_le_left _ _)
    have h2 := H₂ p fun i => (hp' i).trans (min_le_right _ _)
    have hpow : ‖δ p‖ ^ (M + 1) ≤ K₂ ^ (M + 1) * s ^ (N + 1) := by
      calc ‖δ p‖ ^ (M + 1) ≤ (K₂ * s) ^ (M + 1) := pow_le_pow_left₀ (norm_nonneg _) h2 _
        _ = K₂ ^ (M + 1) * s ^ (M + 1) := mul_pow _ _ _
        _ ≤ K₂ ^ (M + 1) * s ^ (N + 1) := mul_le_mul_of_nonneg_left
            (pow_le_pow_of_le_one hs0 hs (by omega)) (pow_nonneg hK₂ _)
    calc _ ≤ K₁ * ‖δ p‖ ^ (M + 1) := h1
      _ ≤ |K₁| * ‖δ p‖ ^ (M + 1) := mul_le_mul_of_nonneg_right (le_abs_self _)
          (pow_nonneg (norm_nonneg _) _)
      _ ≤ |K₁| * (K₂ ^ (M + 1) * s ^ (N + 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
      _ = _ := by ring

theorem CepsJetDecay.of_series {δ : (ℕ → ℝ) → ℂ} {Tδ : (Fin d → ℕ) → ℂ}
    (hδ : CepsJetScal p₀ δ Tδ) (hδ0 : δ p₀ = 0) {g : ℕ → ℝ → ℂ}
    (hg : ∀ n, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ u, ‖g n u‖ ≤ K * cepsStretchedWeight c e u)
    {F : ℝ → (ℕ → ℝ) → ℂ}
    (hF : ∀ M : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (u : ℝ) (p : ℕ → ℝ),
      (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
        ‖F u p - ∑ n ∈ range (M + 1), g n u * δ p ^ n‖ ≤
          K * cepsStretchedWeight c e u * ‖δ p‖ ^ (M + 1)) :
    CepsJetDecay p₀ F
      (fun α u => ∑ n ∈ range (∑ i, α i + 1), g n u * cepsBoxPow Tδ n α) := by
  have hT0 : Tδ 0 = 0 := by rw [hδ.coeff_zero, hδ0]
  -- each term `gₙ(u) δⁿ`
  have hterm : ∀ n, CepsJetDecay p₀ (fun u p => g n u * δ p ^ n)
      (fun α u => g n u * cepsBoxPow Tδ n α) := by
    intro n
    obtain ⟨K, c, hc, e, H⟩ := hg n
    have h := (CepsJetDecay.of_fun (p₀ := p₀) (d := d) hc H).mul_scal (hδ.pow n)
    refine ⟨fun α => ?_, fun N => ?_⟩
    · obtain ⟨K', c', hc', e', H'⟩ := h.1 α
      exact ⟨K', c', hc', e', fun u => by simpa [cepsBoxMul_single_zero_left] using H' u⟩
    · exact (h.2 N).congr_coeff fun α _ u => cepsBoxMul_single_zero_left _ _ _
  refine ⟨fun α => ?_, fun N => ?_⟩
  · obtain ⟨K, c, hK, hc, e, H⟩ := exists_common_stretched_bound (range (∑ i, α i + 1)) g
      fun n _ => hg n
    refine ⟨∑ n ∈ range (∑ i, α i + 1), K * ‖cepsBoxPow Tδ n α‖, c, hc, e, fun u => ?_⟩
    calc _ ≤ ∑ n ∈ range (∑ i, α i + 1), ‖g n u * cepsBoxPow Tδ n α‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ range (∑ i, α i + 1), K * cepsStretchedWeight c e u * ‖cepsBoxPow Tδ n α‖ :=
          sum_le_sum fun n hn => by
            rw [norm_mul]; exact mul_le_mul_of_nonneg_right (H n hn u) (norm_nonneg _)
      _ = _ := by rw [sum_mul]; exact sum_congr rfl fun _ _ => by ring
  · set M := d * N + N
    have hG := CepsJetDecayAt.sum (range (M + 1)) fun n _ => (hterm n).2 N
    refine (hG.congr_coeff ?_).of_close ?_
    · intro α hα u
      have hdeg := cepsJet_degree_le_of_mem_box hα
      refine (sum_subset (range_subset_range.mpr (by omega)) fun n hn hn' => ?_).symm
      simp only [mem_range, not_lt] at hn hn'
      rw [cepsBoxPow_eq_zero hT0 n α (by omega), mul_zero]
    · obtain ⟨ρ₁, K₁, c₁, hρ₁, hc₁, e₁, H₁⟩ := hF M
      obtain ⟨ρ₂, K₂, hρ₂, hK₂, H₂⟩ := hδ.norm_le_of_ref hδ0
      refine ⟨min (min ρ₁ ρ₂) (1 / ((d : ℝ) + 1)), |K₁| * K₂ ^ (M + 1), c₁,
        cepsJet_small_box_pos (lt_min hρ₁ hρ₂), hc₁, e₁, fun u p hp => ?_⟩
      obtain ⟨hp', -, hs⟩ := cepsJet_small_box hp
      set s := ∑ i : Fin d, |p i - p₀ i|
      have hs0 : 0 ≤ s := cepsJet_size_nonneg p
      have h1 := H₁ u p fun i => (hp' i).trans (min_le_left _ _)
      have h2 := H₂ p fun i => (hp' i).trans (min_le_right _ _)
      have hw := (cepsStretchedWeight_pos c₁ e₁ u).le
      have hpow : ‖δ p‖ ^ (M + 1) ≤ K₂ ^ (M + 1) * s ^ (N + 1) := by
        calc ‖δ p‖ ^ (M + 1) ≤ (K₂ * s) ^ (M + 1) := pow_le_pow_left₀ (norm_nonneg _) h2 _
          _ = K₂ ^ (M + 1) * s ^ (M + 1) := mul_pow _ _ _
          _ ≤ K₂ ^ (M + 1) * s ^ (N + 1) := mul_le_mul_of_nonneg_left
              (pow_le_pow_of_le_one hs0 hs (by omega)) (pow_nonneg hK₂ _)
      calc _ ≤ K₁ * cepsStretchedWeight c₁ e₁ u * ‖δ p‖ ^ (M + 1) := h1
        _ ≤ |K₁| * cepsStretchedWeight c₁ e₁ u * ‖δ p‖ ^ (M + 1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hw)
              (pow_nonneg (norm_nonneg _) _)
        _ ≤ |K₁| * cepsStretchedWeight c₁ e₁ u * (K₂ ^ (M + 1) * s ^ (N + 1)) :=
            mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) hw)
        _ = _ := by ring

/-! ## Inverses -/

theorem one_add_inv_sub_geom_sum (x : ℂ) (hx : 1 + x ≠ 0) (M : ℕ) :
    (1 + x)⁻¹ - ∑ n ∈ range (M + 1), (-x) ^ n = (-x) ^ (M + 1) / (1 + x) := by
  rw [eq_div_iff hx, sub_mul, inv_mul_cancel₀ hx]
  have hg := geom_sum_mul (-x) (M + 1)
  linear_combination hg

theorem CepsJetScal.inv {s : (ℕ → ℝ) → ℂ} {Ts : (Fin d → ℕ) → ℂ} (hs : CepsJetScal p₀ s Ts)
    (ha : s p₀ ≠ 0) : ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀ (fun p => (s p)⁻¹) T := by
  set a := s p₀
  have hδ : CepsJetScal p₀ (fun p => a⁻¹ * s p - 1) (fun α => a⁻¹ * Ts α -
      (if α = 0 then 1 else 0)) := (hs.const_mul a⁻¹).sub (CepsJetScal.const 1)
  have hδ0 : a⁻¹ * s p₀ - 1 = 0 := by rw [inv_mul_cancel₀ ha, sub_self]
  refine ⟨_, CepsJetScal.of_series hδ hδ0 (fun n => (-1) ^ n * a⁻¹) fun M => ?_⟩
  obtain ⟨ρ, K, hρ, hK, H⟩ := hδ.norm_le_of_ref hδ0
  refine ⟨min ρ (1 / (2 * ((d : ℝ) * K + 1))), 2 * ‖a⁻¹‖, lt_min hρ (by positivity),
    fun p hp => ?_⟩
  set x := a⁻¹ * s p - 1
  have hx : ‖x‖ ≤ 1 / 2 := by
    have h1 := H p fun i => (hp i).trans (min_le_left _ _)
    have h2 := cepsJet_size_le_of_box fun i => (hp i).trans (min_le_right _ _)
    have hden : 0 < 2 * ((d : ℝ) * K + 1) := by positivity
    calc ‖x‖ ≤ K * (d * (1 / (2 * ((d : ℝ) * K + 1)))) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hK)
      _ = (d * K) / (2 * ((d : ℝ) * K + 1)) := by ring
      _ ≤ 1 / 2 := by
          rw [div_le_iff₀ hden]; nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hK]
  have h1x : 1 + x ≠ 0 := by
    intro h
    have : ‖(1 : ℂ)‖ ≤ ‖x‖ := by rw [show (1 : ℂ) = -x by linear_combination h, norm_neg]
    rw [norm_one] at this
    linarith
  have hnorm1x : 1 / 2 ≤ ‖1 + x‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-x)
    rw [norm_one, norm_neg, sub_neg_eq_add] at this
    linarith
  have hsp : s p = a * (1 + x) := by
    simp only [x]; field_simp; ring
  have hkey : (s p)⁻¹ - ∑ n ∈ range (M + 1), (-1) ^ n * a⁻¹ * x ^ n =
      a⁻¹ * ((-x) ^ (M + 1) / (1 + x)) := by
    rw [← one_add_inv_sub_geom_sum x h1x M, hsp, mul_inv, mul_sub, mul_sum]
    congr 1
    exact sum_congr rfl fun n _ => by rw [neg_pow]; ring_nf
  rw [hkey, norm_mul, norm_div, norm_pow, norm_neg]
  calc ‖a⁻¹‖ * (‖x‖ ^ (M + 1) / ‖1 + x‖) ≤ ‖a⁻¹‖ * (‖x‖ ^ (M + 1) / (1 / 2)) := by
        gcongr
    _ = 2 * ‖a⁻¹‖ * ‖x‖ ^ (M + 1) := by ring

/-! ## Rescaled smooth functions -/

/-- Points between `x₀` and `x₀ (1 + δ)` with `|δ| ≤ 1/2` are comparable to `x₀`. -/
theorem abs_comparable_of_mem_uIcc {x₀ δ t : ℝ} (hδ : |δ| ≤ 1 / 2)
    (ht : t ∈ Set.uIcc x₀ (x₀ * (1 + δ))) : |t| ≤ 3 / 2 * |x₀| ∧ 1 / 2 * |x₀| ≤ |t| := by
  have h1 : |t - x₀| ≤ |x₀ * (1 + δ) - x₀| := Set.abs_sub_left_of_mem_uIcc ht
  have h2 : |x₀ * (1 + δ) - x₀| = |x₀| * |δ| := by
    rw [show x₀ * (1 + δ) - x₀ = x₀ * δ by ring, abs_mul]
  have h3 : |x₀| * |δ| ≤ |x₀| * (1 / 2) := mul_le_mul_of_nonneg_left hδ (abs_nonneg _)
  have h4 := abs_sub_abs_le_abs_sub t x₀
  have h5 := abs_sub_abs_le_abs_sub x₀ t
  rw [abs_sub_comm x₀ t] at h5
  constructor <;> linarith

theorem CepsJetDecay.comp_scale {f : ℝ → ℂ} (hf : ∀ n : ℕ, ContDiff ℝ n f)
    (hfb : ∀ n : ℕ, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y,
      ‖iteratedDeriv n f y‖ ≤ K * cepsStretchedWeight c e y)
    {a : ℝ} (ha : a ≠ 0) {δ : (ℕ → ℝ) → ℝ} {Tδ : (Fin d → ℕ) → ℂ}
    (hδ : CepsJetScal p₀ (fun p => (δ p : ℂ)) Tδ) (hδ0 : δ p₀ = 0) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ,
      CepsJetDecay p₀ (fun u p => f (a * u * (1 + δ p))) T := by
  have hδ0' : ((δ p₀ : ℝ) : ℂ) = 0 := by rw [hδ0, Complex.ofReal_zero]
  have hapos : 0 < |a| := abs_pos.mpr ha
  -- weights at `a u`
  have hscale : ∀ (c : ℝ), 0 ≤ c → ∀ (e : ℕ) (u : ℝ), cepsStretchedWeight c e (a * u) ≤
      (max 1 |a|) ^ e * cepsStretchedWeight (c * Real.sqrt |a|) e u :=
    fun c hc e u => cepsStretchedWeight_mul_arg_le hc e a u
  have hpolyw : ∀ (c : ℝ) (n e : ℕ) (u : ℝ),
      (1 + |u|) ^ n * cepsStretchedWeight c e u = cepsStretchedWeight c (n + e) u := by
    intro c n e u
    rw [← cepsStretchedWeight_zero_rate, cepsStretchedWeight_mul, zero_add]
  refine ⟨_, CepsJetDecay.of_series hδ hδ0'
    (g := fun n u => ((n.factorial : ℂ)⁻¹ * ((a * u : ℝ) : ℂ) ^ n) * iteratedDeriv n f (a * u))
    (fun n => ?_) fun M => ?_⟩
  · -- the coefficient functions decay
    obtain ⟨K, c, hc, e, H⟩ := hfb n
    refine ⟨(n.factorial : ℝ)⁻¹ * |a| ^ n * |K| * (max 1 |a|) ^ e,
      c * Real.sqrt |a|, mul_pos hc (Real.sqrt_pos.mpr hapos), n + e, fun u => ?_⟩
    have h1 : ‖iteratedDeriv n f (a * u)‖ ≤
        |K| * ((max 1 |a|) ^ e * cepsStretchedWeight (c * Real.sqrt |a|) e u) :=
      (H _).trans (mul_le_mul (le_abs_self K) (hscale c hc.le e u)
        (cepsStretchedWeight_pos _ _ _).le (abs_nonneg _))
    have h2 : ‖((n.factorial : ℂ)⁻¹ * ((a * u : ℝ) : ℂ) ^ n)‖ ≤
        (n.factorial : ℝ)⁻¹ * (|a| ^ n * (1 + |u|) ^ n) := by
      rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_mul,
        mul_pow, Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (abs_nonneg u) (by linarith) n) (by positivity)) (by positivity)
    rw [norm_mul]
    calc _ ≤ (n.factorial : ℝ)⁻¹ * (|a| ^ n * (1 + |u|) ^ n) *
          (|K| * ((max 1 |a|) ^ e * cepsStretchedWeight (c * Real.sqrt |a|) e u)) :=
          mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = (n.factorial : ℝ)⁻¹ * |a| ^ n * |K| * (max 1 |a|) ^ e *
          ((1 + |u|) ^ n * cepsStretchedWeight (c * Real.sqrt |a|) e u) := by ring
      _ = _ := by rw [hpolyw]
  · -- the one-variable Taylor remainder around `a u`
    obtain ⟨K₁, c₁, hc₁, e₁, H₁⟩ := hfb (M + 1)
    obtain ⟨ρ, Kδ, hρ, hKδ, Hδ⟩ := hδ.norm_le_of_ref hδ0'
    set c' := c₁ * Real.sqrt (1 / 2) * Real.sqrt |a|
    have hc' : 0 < c' := by
      have : (0 : ℝ) < Real.sqrt (1 / 2) := Real.sqrt_pos.mpr (by norm_num)
      exact mul_pos (mul_pos hc₁ this) (Real.sqrt_pos.mpr hapos)
    refine ⟨min ρ (1 / (2 * ((d : ℝ) * Kδ + 1))),
      |K₁| * (3 / 2) ^ e₁ * (max 1 |a|) ^ e₁ * |a| ^ (M + 1), c', lt_min hρ (by positivity),
      hc', (M + 1) + e₁, fun u p hp => ?_⟩
    have hδp : |δ p| ≤ 1 / 2 := by
      have h1 := Hδ p fun i => (hp i).trans (min_le_left _ _)
      have h2 := cepsJet_size_le_of_box fun i => (hp i).trans (min_le_right _ _)
      have hden : 0 < 2 * ((d : ℝ) * Kδ + 1) := by positivity
      rw [Complex.norm_real, Real.norm_eq_abs] at h1
      calc |δ p| ≤ Kδ * (d * (1 / (2 * ((d : ℝ) * Kδ + 1)))) :=
            h1.trans (mul_le_mul_of_nonneg_left h2 hKδ)
        _ = (d * Kδ) / (2 * ((d : ℝ) * Kδ + 1)) := by ring
        _ ≤ 1 / 2 := by
            rw [div_le_iff₀ hden]; nlinarith [mul_nonneg (Nat.cast_nonneg d : (0 : ℝ) ≤ d) hKδ]
    set x₀ := a * u
    set L := |K₁| * (3 / 2) ^ e₁ * ((max 1 |a|) ^ e₁ * cepsStretchedWeight c' e₁ u)
    have hL : ∀ t ∈ Set.uIcc x₀ (x₀ * (1 + δ p)), ‖iteratedDeriv (M + 1) f t‖ ≤ L := by
      intro t ht
      obtain ⟨hup, hlo⟩ := abs_comparable_of_mem_uIcc hδp ht
      have hw1 := cepsStretchedWeight_le_of_comparable hc₁.le e₁ (by norm_num : (1 : ℝ) ≤ 3 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) hup hlo
      have hw2 := hscale (c₁ * Real.sqrt (1 / 2)) (by positivity) e₁ u
      calc ‖iteratedDeriv (M + 1) f t‖ ≤ |K₁| * cepsStretchedWeight c₁ e₁ t :=
            (H₁ t).trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (cepsStretchedWeight_pos _ _ _).le)
        _ ≤ |K₁| * ((3 / 2) ^ e₁ * cepsStretchedWeight (c₁ * Real.sqrt (1 / 2)) e₁ x₀) :=
            mul_le_mul_of_nonneg_left hw1 (abs_nonneg _)
        _ ≤ |K₁| * ((3 / 2) ^ e₁ * ((max 1 |a|) ^ e₁ * cepsStretchedWeight c' e₁ u)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw2 (by positivity))
              (abs_nonneg _)
        _ = L := by ring
    have htay := norm_sub_taylor_le (M + 1) (hf (M + 1)) x₀ (x₀ * (1 + δ p)) hL
    have hsum : ∑ m ∈ range (M + 1), (((m.factorial : ℝ)⁻¹ * (x₀ * (1 + δ p) - x₀) ^ m) •
        iteratedDeriv m f x₀) = ∑ n ∈ range (M + 1),
          ((n.factorial : ℂ)⁻¹ * ((a * u : ℝ) : ℂ) ^ n) * iteratedDeriv n f (a * u) *
            ((δ p : ℝ) : ℂ) ^ n := by
      refine sum_congr rfl fun m _ => ?_
      rw [Complex.real_smul]
      simp only [x₀]
      push_cast
      ring
    rw [hsum] at htay
    have hxx : |x₀ * (1 + δ p) - x₀| = |a| * |u| * |δ p| := by
      rw [show x₀ * (1 + δ p) - x₀ = a * u * δ p by simp only [x₀]; ring, abs_mul, abs_mul]
    rw [hxx] at htay
    have hu1 : |u| ^ (M + 1) ≤ (1 + |u|) ^ (M + 1) :=
      pow_le_pow_left₀ (abs_nonneg u) (by linarith) _
    rw [Complex.norm_real, Real.norm_eq_abs]
    calc _ ≤ L * (|a| * |u| * |δ p|) ^ (M + 1) := htay
      _ = |K₁| * (3 / 2) ^ e₁ * (max 1 |a|) ^ e₁ * |a| ^ (M + 1) *
          (|u| ^ (M + 1) * cepsStretchedWeight c' e₁ u) * |δ p| ^ (M + 1) := by
          simp only [L]; ring
      _ ≤ |K₁| * (3 / 2) ^ e₁ * (max 1 |a|) ^ e₁ * |a| ^ (M + 1) *
          ((1 + |u|) ^ (M + 1) * cepsStretchedWeight c' e₁ u) * |δ p| ^ (M + 1) := by
          have hw0 := (cepsStretchedWeight_pos c' e₁ u).le
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hu1 hw0) (by positivity)) (by positivity)
      _ = _ := by rw [hpolyw]

/-! ## Families of representations -/

theorem CepsJetDecay.of_family {f : (Fin d → ℕ) → ℝ → (ℕ → ℝ) → ℂ}
    {C : (Fin d → ℕ) → (Fin d → ℕ) → ℝ → ℂ} (hf : ∀ α, CepsJetDecay p₀ (f α) (C α))
    {F : ℝ → (ℕ → ℝ) → ℂ}
    (hF : ∀ N : ℕ, ∃ ρ K c : ℝ, 0 < ρ ∧ 0 < c ∧ ∃ e : ℕ, ∀ (u : ℝ) (p : ℕ → ℝ),
      (∀ i : Fin d, |p i - p₀ i| ≤ ρ) →
        ‖F u p - ∑ α ∈ cepsTaylorBox d N,
            f α u p * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ)‖ ≤
          K * cepsStretchedWeight c e u * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)) :
    CepsJetDecay p₀ F (fun γ u => ∑ β ∈ cepsLowerBox γ, C β (γ - β) u) := by
  classical
  refine ⟨fun γ => ?_, fun N => ?_⟩
  · obtain ⟨K, c, hK, hc, e, H⟩ := exists_common_stretched_bound (cepsLowerBox γ)
      (fun β => C β (γ - β)) fun β _ => (hf β).1 (γ - β)
    refine ⟨(cepsLowerBox γ).card * K, c, hc, e, fun u => ?_⟩
    calc _ ≤ ∑ β ∈ cepsLowerBox γ, ‖C β (γ - β) u‖ := norm_sum_le _ _
      _ ≤ ∑ _β ∈ cepsLowerBox γ, K * cepsStretchedWeight c e u := sum_le_sum fun β hβ => H β hβ u
      _ = _ := by rw [sum_const, nsmul_eq_mul]; ring
  · have hterm : ∀ α, CepsJetDecayAt p₀ N
        (fun u p => f α u p * (cepsMonomial (fun i : Fin d => p i - p₀ i) α : ℂ))
        (fun γ u => if ∀ i, α i ≤ γ i then C α (γ - α) u else 0) := fun α =>
      ((hf α).2 N).mul_scal (hf α).1 (CepsJetScal.monomial α N) |>.congr_coeff
        fun γ _ u => cepsBoxMul_indicator_right _ α γ
    have hG := CepsJetDecayAt.sum (cepsTaylorBox d N) fun α _ => hterm α
    refine (hG.congr_coeff fun γ hγ u => ?_).of_close (hF N)
    rw [← sum_filter]
    refine sum_congr ?_ fun _ _ => rfl
    ext β
    rw [mem_filter, mem_cepsLowerBox]
    exact ⟨fun h => h.2, fun h => ⟨cepsLowerBox_subset hγ (mem_cepsLowerBox.mpr h), h⟩⟩

end

end PGM
