import PLAStochastic.Index.CEPS.Final.TaylorExtend
import PLAStochastic.Index.CEPS.ZeroOrder.PhiZero

/-!
# Jet Taylor representation of the composed low-band coefficients

`cepsLowCoeff Gk' sc k u p` (WP11a) is, by `lowCompCoeff_eq_sum`,

`∑_{j,m ≤ k} (m!)⁻¹ 2^{-j} ∂_yᵐ Gk'_j(p)(-4u/c₀(p)) (-4u)ᵐ [X^{k-j}] (invTail c(p))ᵐ`.

With box Taylor representations of the scalar coefficients `c_i = sc i` and of the
frequency derivatives of the normal coefficients `Gk j`, every factor is represented:

* `[Xⁿ] (invTail c(p))ᵐ` through the inverse recursion (`cepsJet_invTail_coeff`);
* the zero-order factor `∂_yᵐ φ_Λ(-c₀(p) y / 4)` at `y = -4u/c₀(p)` equals
  `(c₀(p)/a)ᵐ φ^{(m)}(-4u/a)` once `φ_Λ = φ(-4 · / a)`, `a = c₀(p₀)` (`cepsJet_D_zero`);
* the higher factors `∂_yᵐ Gk_j(p)(-4u/c₀(p))` through the one-variable Taylor expansion of the
  coefficient functions at `-4u/a` (`cepsJet_D_succ`).

The result `cepsJet_phi_rep` is the `CepsT3` Taylor data of `Φ_k`.
-/

namespace PGM

noncomputable section

open Finset PowerSeries

/-! ## The composed coefficient as a finite sum -/

theorem lowCompCoeff_eq_sum (g : ℕ → ℝ → ℂ) (c : ℕ → ℝ) (ω : ℝ) (k : ℕ) :
    lowCompCoeff g c ω k = ∑ j ∈ range (k + 1), ∑ m ∈ range (k + 1),
      (m.factorial : ℂ)⁻¹ * iteratedDeriv m (g j) (ω / c 0) * (ω : ℂ) ^ m *
        coeff (k - j) (invTail c ^ m) := by
  rw [lowCompCoeff, coeff_compSeries_eq g c ω le_rfl]
  refine sum_congr rfl fun j hj => sum_congr rfl fun m _ => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
  rw [coeff_X_pow_mul', if_pos hjk, coeff_C_mul, mul_pow, ← map_pow, coeff_C_mul]
  ring

theorem constantCoeff_mk_ofReal (f : ℕ → ℝ) :
    constantCoeff (PowerSeries.mk fun i => (f i : ℂ)) = (f 0 : ℂ) := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_mk]

variable {p₀ : ℕ → ℝ} {d : ℕ}

/-! ## Near the reference point -/

theorem CepsJetScal.near_ref {s : (ℕ → ℝ) → ℝ} {T : (Fin d → ℕ) → ℂ}
    (hs : CepsJetScal p₀ (fun p => (s p : ℂ)) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : ℕ → ℝ, (∀ i : Fin d, |p i - p₀ i| ≤ ρ) → |s p - s p₀| ≤ ε := by
  have h := hs.sub (CepsJetScal.const (p₀ := p₀) (d := d) (s p₀ : ℂ))
  obtain ⟨ρ, K, hρ, hK, H⟩ := h.norm_le_of_ref (by simp)
  refine ⟨min ρ (ε / ((d : ℝ) * K + 1)), lt_min hρ (by positivity), fun p hp => ?_⟩
  have h1 := H p fun i => (hp i).trans (min_le_left _ _)
  have h2 := cepsJet_size_le_of_box fun i => (hp i).trans (min_le_right _ _)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h1
  have hden : 0 < (d : ℝ) * K + 1 := by positivity
  calc |s p - s p₀| ≤ K * (d * (ε / ((d : ℝ) * K + 1))) := h1.trans (mul_le_mul_of_nonneg_left h2 hK)
    _ = ε * ((d * K) / ((d : ℝ) * K + 1)) := by ring
    _ ≤ ε * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hden).mpr (by linarith)) hε.le
    _ = ε := mul_one ε

/-! ## Coefficients of the inverse scale series -/

theorem cepsJet_invTail_coeff {k : ℕ} {sc : ℕ → (ℕ → ℝ) → ℝ}
    (hsc : ∀ i ≤ k, ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀ (fun p => (sc i p : ℂ)) T)
    (hinv : ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀ (fun p => ((sc 0 p : ℂ))⁻¹) T) :
    ∀ m : ℕ, ∀ n ≤ k, ∃ T : (Fin d → ℕ) → ℂ,
      CepsJetScal p₀ (fun p => coeff n (invTail (fun i => sc i p) ^ m)) T := by
  -- coefficients of the inverse series
  have hI : ∀ n ≤ k, ∃ T : (Fin d → ℕ) → ℂ,
      CepsJetScal p₀ (fun p => coeff n (PowerSeries.mk fun i => (sc i p : ℂ))⁻¹) T := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · obtain ⟨T, hT⟩ := hinv
        refine ⟨T, hT.congr_fun ⟨1, one_pos, fun p _ => ?_⟩⟩
        rw [coeff_inv, if_pos rfl, constantCoeff_mk_ofReal]
      · have hterm : ∀ x ∈ (antidiagonal n).filter (fun x => x.2 < n),
            ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀ (fun p => (sc x.1 p : ℂ) *
              coeff x.2 (PowerSeries.mk fun i => (sc i p : ℂ))⁻¹) T := by
          intro x hx
          rw [mem_filter, mem_antidiagonal] at hx
          obtain ⟨T₁, h₁⟩ := hsc x.1 (by omega)
          obtain ⟨T₂, h₂⟩ := ih x.2 hx.2 (by omega)
          exact ⟨_, h₁.mul h₂⟩
        choose! T hT using hterm
        obtain ⟨Ti, hTi⟩ := hinv
        refine ⟨_, (((CepsJetScal.sum _ hT).mul hTi).const_mul (-1)).congr_fun
          ⟨1, one_pos, fun p _ => ?_⟩⟩
        rw [coeff_inv, if_neg hpos.ne', constantCoeff_mk_ofReal, ← sum_filter]
        simp only [coeff_mk]
        ring
  -- coefficients of the tail
  have hJ : ∀ n ≤ k, ∃ T : (Fin d → ℕ) → ℂ,
      CepsJetScal p₀ (fun p => coeff n (invTail fun i => sc i p)) T := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · refine ⟨_, (CepsJetScal.const (p₀ := p₀) (d := d) (0 : ℂ)).congr_fun
        ⟨1, one_pos, fun p _ => ?_⟩⟩
      rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_invTail]
    · obtain ⟨T, hT⟩ := hI n hn
      refine ⟨T, hT.congr_fun ⟨1, one_pos, fun p _ => ?_⟩⟩
      rw [invTail, map_sub, coeff_C, if_neg hpos.ne', sub_zero]
  -- powers
  intro m
  induction m with
  | zero =>
    intro n _
    refine ⟨_, (CepsJetScal.const (p₀ := p₀) (d := d) (if n = 0 then (1 : ℂ) else 0)).congr_fun
      ⟨1, one_pos, fun p _ => ?_⟩⟩
    rw [pow_zero, coeff_one]
  | succ m ih =>
    intro n hn
    have hterm : ∀ x ∈ antidiagonal n, ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀
        (fun p => coeff x.1 (invTail (fun i => sc i p) ^ m) *
          coeff x.2 (invTail fun i => sc i p)) T := by
      intro x hx
      rw [mem_antidiagonal] at hx
      obtain ⟨T₁, h₁⟩ := ih x.1 (by omega)
      obtain ⟨T₂, h₂⟩ := hJ x.2 (by omega)
      exact ⟨_, h₁.mul h₂⟩
    choose! T hT using hterm
    refine ⟨_, (CepsJetScal.sum _ hT).congr_fun ⟨1, one_pos, fun p _ => ?_⟩⟩
    rw [pow_succ, coeff_mul]

/-! ## The zero-order factor -/

theorem cepsJet_D_zero {sc0 : (ℕ → ℝ) → ℝ} {a : ℝ} (ha : 0 < a) (hsc0 : sc0 p₀ = a)
    {T0 : (Fin d → ℕ) → ℂ} (hs : CepsJetScal p₀ (fun p => (sc0 p : ℂ)) T0)
    {φ : ℝ → ℂ} (hφs : ∀ n : ℕ, ContDiff ℝ n φ)
    (hφb : ∀ n : ℕ, ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y,
      ‖iteratedDeriv n φ y‖ ≤ K * cepsStretchedWeight c e y)
    (hΛ : ∀ x, cepsLambdaChar x = φ (-4 * x / a)) (m : ℕ) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ, CepsJetDecay p₀
      (fun u p => iteratedDeriv m (fun y => cepsLambdaChar (-(sc0 p) * y / 4)) (-4 * u / sc0 p))
      T := by
  obtain ⟨K, c, hc, e, H⟩ := hφb m
  have hfu : ∀ u, ‖iteratedDeriv m φ (-4 * u / a)‖ ≤
      (|K| * (max 1 |-4 / a|) ^ e) * cepsStretchedWeight (c * Real.sqrt |-4 / a|) e u := by
    intro u
    have h1 := H (-4 * u / a)
    rw [show -4 * u / a = (-4 / a) * u by ring] at h1 ⊢
    calc _ ≤ K * cepsStretchedWeight c e ((-4 / a) * u) := h1
      _ ≤ |K| * ((max 1 |-4 / a|) ^ e * cepsStretchedWeight (c * Real.sqrt |-4 / a|) e u) :=
          mul_le_mul (le_abs_self K) (cepsStretchedWeight_mul_arg_le hc.le e _ u)
            (cepsStretchedWeight_pos _ _ _).le (abs_nonneg _)
      _ = _ := by ring
  have hc' : 0 < c * Real.sqrt |-4 / a| :=
    mul_pos hc (Real.sqrt_pos.mpr (abs_pos.mpr (by positivity)))
  have hprod := (CepsJetDecay.of_fun (p₀ := p₀) (d := d) hc' hfu).mul_scal
    ((hs.const_mul ((a : ℂ)⁻¹)).pow m)
  obtain ⟨ρ, hρ, Hρ⟩ := hs.near_ref (half_pos ha)
  refine ⟨_, hprod.congr_fun ⟨ρ, hρ, fun u p hp => ?_⟩⟩
  have hsp : sc0 p ≠ 0 := by
    have := Hρ p hp
    rw [hsc0] at this
    have := (abs_le.mp this).1
    intro h0; rw [h0] at this; linarith
  have hfun : (fun y => cepsLambdaChar (-(sc0 p) * y / 4)) =
      fun y => φ ((sc0 p / a) * y) := by
    funext y
    rw [hΛ]
    congr 1
    field_simp
  rw [hfun, iteratedDeriv_comp_const_smul (hφs m) (sc0 p / a)]
  simp only [Complex.real_smul]
  have harg : sc0 p / a * (-4 * u / sc0 p) = -4 * u / a := by field_simp
  rw [harg]
  push_cast
  ring

/-! ## The higher factors -/

theorem iteratedDeriv_iteratedDeriv' (f : ℝ → ℂ) (n m : ℕ) :
    iteratedDeriv n (iteratedDeriv m f) = iteratedDeriv (n + m) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add]
  rfl

theorem cepsJet_D_succ {sc0 : (ℕ → ℝ) → ℝ} {a : ℝ} (ha : 0 < a) (hsc0 : sc0 p₀ = a)
    {Ti : (Fin d → ℕ) → ℂ} (hinv : CepsJetScal p₀ (fun p => ((sc0 p : ℂ))⁻¹) Ti)
    {G : (ℕ → ℝ) → ℝ → ℂ} {TG : (Fin d → ℕ) → ℝ → ℂ}
    (hTs : ∀ (α : Fin d → ℕ) (n : ℕ), ContDiff ℝ n (TG α))
    (hTb : ∀ (α : Fin d → ℕ) (n : ℕ), ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y,
      ‖iteratedDeriv n (TG α) y‖ ≤ K * cepsStretchedWeight c e y)
    (m : ℕ) (hG : CepsJetDecay p₀ (fun y p => iteratedDeriv m (G p) y)
      (fun α => iteratedDeriv m (TG α))) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ, CepsJetDecay p₀
      (fun u p => iteratedDeriv m (G p) (-4 * u / sc0 p)) T := by
  have ha0 : a ≠ 0 := ha.ne'
  set δ : (ℕ → ℝ) → ℝ := fun p => a * (sc0 p)⁻¹ - 1 with hδdef
  have hδ : CepsJetScal p₀ (fun p => (δ p : ℂ)) (fun α => (a : ℂ) * Ti α -
      (if α = 0 then 1 else 0)) :=
    ((hinv.const_mul (a : ℂ)).sub (CepsJetScal.const 1)).congr_fun
      ⟨1, one_pos, fun p _ => by simp only [δ]; push_cast; ring⟩
  have hδ0 : δ p₀ = 0 := by simp only [δ, hsc0]; field_simp; ring
  have ha' : (-4 / a) ≠ 0 := by positivity
  have hfam : ∀ α : Fin d → ℕ, ∃ T : (Fin d → ℕ) → ℝ → ℂ, CepsJetDecay p₀
      (fun u p => iteratedDeriv m (TG α) ((-4 / a) * u * (1 + δ p))) T := by
    intro α
    refine CepsJetDecay.comp_scale (fun n => ?_) (fun n => ?_) ha' hδ hδ0
    · rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv' n m (hTs α (n + m))
    · rw [iteratedDeriv_iteratedDeriv']
      exact hTb α (n + m)
  choose C hC using hfam
  refine ⟨_, CepsJetDecay.of_family hC fun N => ?_⟩
  obtain ⟨ρ₁, K, c, hρ₁, hc, e, H⟩ := hG.2 N
  obtain ⟨ρ₂, hρ₂, H₂⟩ := hδ.near_ref (by norm_num : (0 : ℝ) < 1 / 2)
  set c' := c * Real.sqrt (1 / 2) * Real.sqrt |-4 / a|
  have hc' : 0 < c' := mul_pos (mul_pos hc (Real.sqrt_pos.mpr (by norm_num)))
    (Real.sqrt_pos.mpr (abs_pos.mpr ha'))
  refine ⟨min ρ₁ ρ₂, |K| * (3 / 2) ^ e * (max 1 |-4 / a|) ^ e, c', lt_min hρ₁ hρ₂, hc', e,
    fun u p hp => ?_⟩
  have hδp : |δ p| ≤ 1 / 2 := by
    have := H₂ p fun i => (hp i).trans (min_le_right _ _)
    rwa [hδ0, sub_zero] at this
  have harg : -4 * u / sc0 p = (-4 / a) * u * (1 + δ p) := by
    simp only [δ]; field_simp; ring
  have h1 := H ((-4 / a) * u * (1 + δ p)) p fun i => (hp i).trans (min_le_left _ _)
  rw [harg]
  refine h1.trans ?_
  -- weight conversion from `y = (-4/a) u (1 + δ)` to `u`
  set x₀ := (-4 / a) * u
  have hx : |x₀ * (1 + δ p)| ≤ 3 / 2 * |x₀| ∧ 1 / 2 * |x₀| ≤ |x₀ * (1 + δ p)| := by
    rw [abs_mul]
    have h3 : |1 + δ p| ≤ 3 / 2 := by
      calc |1 + δ p| ≤ |1| + |δ p| := abs_add_le _ _
        _ ≤ 3 / 2 := by rw [abs_one]; linarith
    have h4 : 1 / 2 ≤ |1 + δ p| := by
      have := abs_sub_abs_le_abs_sub 1 (-δ p)
      rw [abs_one, abs_neg, sub_neg_eq_add] at this
      linarith
    exact ⟨by rw [mul_comm]; exact mul_le_mul_of_nonneg_right h3 (abs_nonneg _),
      by rw [mul_comm]; exact mul_le_mul_of_nonneg_left h4 (abs_nonneg _)⟩
  have hw1 := cepsStretchedWeight_le_of_comparable hc.le e (by norm_num : (1 : ℝ) ≤ 3 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) hx.1 hx.2
  have hw2 := cepsStretchedWeight_mul_arg_le (c := c * Real.sqrt (1 / 2)) (by positivity) e
    (-4 / a) u
  have hs := pow_nonneg (cepsJet_size_nonneg (p₀ := p₀) (d := d) p) (N + 1)
  calc K * cepsStretchedWeight c e (x₀ * (1 + δ p)) * (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1)
      ≤ |K| * ((3 / 2) ^ e * ((max 1 |-4 / a|) ^ e * cepsStretchedWeight c' e u)) *
          (∑ i : Fin d, |p i - p₀ i|) ^ (N + 1) := by
        refine mul_le_mul_of_nonneg_right ?_ hs
        refine mul_le_mul (le_abs_self K) (hw1.trans ?_) (cepsStretchedWeight_pos _ _ _).le
          (abs_nonneg _)
        exact mul_le_mul_of_nonneg_left hw2 (by positivity)
    _ = _ := by ring

/-! ## The composed coefficient -/

theorem norm_lowCompPoly_le (j m : ℕ) (u : ℝ) :
    ‖(m.factorial : ℂ)⁻¹ * (2⁻¹ : ℂ) ^ j * (((-4 * u : ℝ)) : ℂ) ^ m‖ ≤
      (4 : ℝ) ^ m * (1 + |u|) ^ m := by
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_pow, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, norm_inv, Complex.norm_ofNat]
  have hf : (1 : ℝ) ≤ m.factorial := by exact_mod_cast Nat.factorial_pos m
  have h1 : (m.factorial : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hf
  have h2 : (2⁻¹ : ℝ) ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h3 : |(-4 * u)| ^ m ≤ (4 : ℝ) ^ m * (1 + |u|) ^ m := by
    rw [← mul_pow, abs_mul]
    have h4 : |(-4 : ℝ)| * |u| ≤ 4 * (1 + |u|) := by
      rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 4)]; linarith [abs_nonneg u]
    exact pow_le_pow_left₀ (by positivity) h4 m
  calc (m.factorial : ℝ)⁻¹ * (2⁻¹) ^ j * |(-4 * u)| ^ m ≤ 1 * 1 * ((4 : ℝ) ^ m * (1 + |u|) ^ m) :=
        mul_le_mul (mul_le_mul h1 h2 (by positivity) zero_le_one) h3 (by positivity)
          (by norm_num)
    _ = _ := by ring

theorem cepsJet_phi_rep {k : ℕ} {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} {sc : ℕ → (ℕ → ℝ) → ℝ}
    {a : ℝ} (ha : 0 < a) (hsc0 : sc 0 p₀ = a)
    (hsc : ∀ i ≤ k, ∃ T : (Fin d → ℕ) → ℂ, CepsJetScal p₀ (fun p => (sc i p : ℂ)) T)
    {TG : ℕ → (Fin d → ℕ) → ℝ → ℂ}
    (hTs : ∀ j ≤ k, ∀ (α : Fin d → ℕ) (n : ℕ), ContDiff ℝ n (TG j α))
    (hTb : ∀ j ≤ k, ∀ (α : Fin d → ℕ) (n : ℕ), ∃ K c : ℝ, 0 < c ∧ ∃ e : ℕ, ∀ y,
      ‖iteratedDeriv n (TG j α) y‖ ≤ K * cepsStretchedWeight c e y)
    (hG : ∀ j ≤ k, ∀ m : ℕ, CepsJetDecay p₀ (fun y p => iteratedDeriv m (Gk j p) y)
      (fun α => iteratedDeriv m (TG j α)))
    (hΛ : ∀ x, cepsLambdaChar x = TG 0 0 (-4 * x / a)) :
    ∃ T : (Fin d → ℕ) → ℝ → ℂ,
      CepsJetDecay p₀ (fun u p => cepsLowCoeff (cepsGkLambda Gk sc) sc k u p) T := by
  obtain ⟨T0, hT0⟩ := hsc 0 (Nat.zero_le k)
  have hT0' : (fun p => (sc 0 p : ℂ)) p₀ ≠ 0 := by
    simp only [hsc0]; exact_mod_cast ha.ne'
  obtain ⟨Ti, hTi⟩ := hT0.inv hT0'
  have hI := cepsJet_invTail_coeff hsc ⟨Ti, hTi⟩
  have hD : ∀ j ≤ k, ∀ m : ℕ, ∃ T : (Fin d → ℕ) → ℝ → ℂ, CepsJetDecay p₀
      (fun u p => iteratedDeriv m (cepsGkLambda Gk sc j p) (-4 * u / sc 0 p)) T := by
    intro j hj m
    rcases j with _ | j
    · have hfun : ∀ p, cepsGkLambda Gk sc 0 p = fun y => cepsLambdaChar (-(sc 0 p) * y / 4) :=
        fun p => funext fun y => cepsGkLambda_zero Gk sc p y
      simp_rw [hfun]
      exact cepsJet_D_zero ha hsc0 hT0 (hTs 0 hj 0) (hTb 0 hj 0) hΛ m
    · have hfun : ∀ p, cepsGkLambda Gk sc (j + 1) p = Gk (j + 1) p :=
        fun p => funext fun y => cepsGkLambda_succ Gk sc j p y
      simp_rw [hfun]
      exact cepsJet_D_succ ha hsc0 hTi (hTs (j + 1) hj) (hTb (j + 1) hj) m (hG (j + 1) hj m)
  choose! TD hTD using hD
  choose! TI hTI using hI
  have hfun : (fun u p => cepsLowCoeff (cepsGkLambda Gk sc) sc k u p) =
      fun u p => ∑ j ∈ range (k + 1), ∑ m ∈ range (k + 1),
        (m.factorial : ℂ)⁻¹ * (2⁻¹ : ℂ) ^ j * (((-4 * u : ℝ)) : ℂ) ^ m *
          (iteratedDeriv m (cepsGkLambda Gk sc j p) (-4 * u / sc 0 p) *
            coeff (k - j) (invTail (fun i => sc i p) ^ m)) := by
    funext u p
    rw [cepsLowCoeff, lowCompCoeff_eq_sum]
    refine sum_congr rfl fun j _ => sum_congr rfl fun m _ => ?_
    rw [iteratedDeriv_const_mul_field]
    ring
  rw [hfun]
  exact ⟨_, CepsJetDecay.sum _ fun j hj => CepsJetDecay.sum _ fun m _ =>
    ((hTD j (Nat.lt_succ_iff.mp (mem_range.mp hj)) m).mul_scal
      (hTI m (k - j) (Nat.sub_le k j))).poly_mul (norm_lowCompPoly_le j m)⟩

end

end PGM
