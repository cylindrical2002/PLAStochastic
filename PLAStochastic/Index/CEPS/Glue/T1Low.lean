import PLAStochastic.Index.CEPS.Glue.Moments

/-!
# WP11a: S-11, low band (T1-low) from the normal transform

* `cepsT5_scal_bounds`: `CepsT5 J` and the class bounds on `C/ε²` give, uniformly over the
  class, `c₀(J ν) ≥ c_lo > 0` and `|c_k(J ν)| ≤ B` for `k ≤ P` (recursive coefficient
  extraction at one fixed `ε`);
* `cepsT1Low_of_normal`: on `|u| ≤ (A log ε)²`, `φ_ν(u) = Ĝ(b, -4iu/(h²C)) + O(εᵖ e^{-cε})`
  (S-9), and the composition theorem `norm_sub_sum_lowCompCoeff_le` applied to C-10 and to the
  T5 expansion of `h²C` gives `CepsT1Low J` with `Φ_k = cepsLowCoeff Gk J.scal k`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

/-- **Scalar coefficient bounds on the class.** -/
theorem cepsT5_scal_bounds {J : CepsJetData} (hT5 : CepsT5 J) (P : ℕ) :
    ∃ m : ℕ, ∀ D θ vlo vhi η : ℝ, 0 < D → 0 < θ → 0 < vlo → vlo ≤ vhi → 0 < η →
      ∃ r : ℝ, 0 < r ∧ ∃ c_lo B : ℝ, 0 < c_lo ∧
        ∀ ν : ProbabilityMeasure ℝ, CepsInputClass D θ vlo vhi m η r ν →
          c_lo ≤ J.scal 0 (J.jet ν) ∧ ∀ k ≤ P, |J.scal k (J.jet ν)| ≤ B := by
  induction P with
  | zero =>
    obtain ⟨m, hm⟩ := hT5 0
    refine ⟨m, fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
    obtain ⟨r, hr, K, e, H⟩ := hm D θ vlo vhi η hD hθ hvlo hv hη
    obtain ⟨e₃, s_lo, s_hi, B₂, he₃, hslo, -, Hm⟩ := ceps_class_moments hD hθ hvlo hv
    set E : ℝ := max (max e e₃) (2 * |K| / s_lo + 1) with hE
    have hE1 : e ≤ E := le_trans (le_max_left _ _) (le_max_left _ _)
    have hE3 : e₃ ≤ E := le_trans (le_max_right _ _) (le_max_left _ _)
    have hEK : 2 * |K| / s_lo + 1 ≤ E := le_max_right _ _
    have hE0 : 1 ≤ E := he₃.trans hE3
    have hEpos : 0 < E := lt_of_lt_of_le one_pos hE0
    refine ⟨r, hr, s_lo / 2, s_hi + |K|, half_pos hslo, fun ν hν => ?_⟩
    have h1 := H E hE1 ν hν
    obtain ⟨hlo, hhi, -⟩ := Hm E hE3 ν hν.reg
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one] at h1
    have hKE : |K| * E⁻¹ ≤ s_lo / 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hEpos]
      have : 2 * |K| / s_lo ≤ E := by linarith
      rw [div_le_iff₀ hslo] at this
      linarith
    have hKE' : K * E⁻¹ ≤ |K| * E⁻¹ :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (inv_nonneg.mpr hEpos.le)
    have hEi : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE0
    have hab := abs_le.mp h1
    refine ⟨by linarith, fun k hk => ?_⟩
    have hk0 : k = 0 := by omega
    subst hk0
    rw [abs_le]
    have : |K| * E⁻¹ ≤ |K| := mul_le_of_le_one_right (abs_nonneg K) hEi
    constructor <;> linarith
  | succ P ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨m', hm'⟩ := hT5 (P + 1)
    refine ⟨max m m', fun D θ vlo vhi η hD hθ hvlo hv hη => ?_⟩
    obtain ⟨r, hr, c_lo, B, hclo, H⟩ := hm D θ vlo vhi η hD hθ hvlo hv hη
    obtain ⟨r', hr', K', e', H'⟩ := hm' D θ vlo vhi η hD hθ hvlo hv hη
    obtain ⟨e₃, s_lo, s_hi, B₂, he₃, hslo, -, Hm⟩ := ceps_class_moments hD hθ hvlo hv
    set E : ℝ := max e' e₃ with hE
    have hE0 : 1 ≤ E := he₃.trans (le_max_right _ _)
    have hEpos : 0 < E := lt_of_lt_of_le one_pos hE0
    set Mb : ℝ := s_hi + ((P : ℝ) + 1) * |B| + |K'| with hMb
    refine ⟨min r r', lt_min hr hr', c_lo, max B (E ^ (P + 1) * Mb), hclo, fun ν hν => ?_⟩
    obtain ⟨h0, hk⟩ := H ν (hν.mono (le_max_left _ _) (min_le_left _ _))
    refine ⟨h0, fun k hk' => ?_⟩
    rcases Nat.lt_or_ge k (P + 1) with hlt | hge
    · exact (hk k (by omega)).trans (le_max_left _ _)
    · have hkeq : k = P + 1 := by omega
      subst hkeq
      refine le_trans ?_ (le_max_right _ _)
      have h1 := H' E (le_max_left _ _) ν (hν.mono (le_max_right _ _) (min_le_right _ _))
      obtain ⟨hlo, hhi, -⟩ := Hm E (le_max_right _ _) ν hν.reg
      rw [Finset.sum_range_succ] at h1
      have hEi0 : 0 ≤ E⁻¹ := inv_nonneg.mpr hEpos.le
      have hEi : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE0
      set x := lawC E ν / E ^ 2
      have hx : |x| ≤ s_hi := by
        rw [abs_of_nonneg ((hslo.le).trans hlo)]
        exact hhi
      have hS : |∑ k ∈ Finset.range (P + 1), (E⁻¹) ^ k * J.scal k (J.jet ν)| ≤
          ((P : ℝ) + 1) * |B| := by
        calc |∑ k ∈ Finset.range (P + 1), (E⁻¹) ^ k * J.scal k (J.jet ν)|
            ≤ ∑ k ∈ Finset.range (P + 1), |(E⁻¹) ^ k * J.scal k (J.jet ν)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _k ∈ Finset.range (P + 1), |B| := by
              refine Finset.sum_le_sum fun k hkr => ?_
              have hkP : k ≤ P := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkr)
              rw [abs_mul, abs_of_nonneg (pow_nonneg hEi0 k)]
              calc (E⁻¹) ^ k * |J.scal k (J.jet ν)| ≤ 1 * |B| :=
                    mul_le_mul (pow_le_one₀ hEi0 hEi) ((hk k hkP).trans (le_abs_self B))
                      (abs_nonneg _) zero_le_one
                _ = |B| := one_mul _
          _ = ((P : ℝ) + 1) * |B| := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring
      have hK' : K' * (E⁻¹) ^ (P + 1 + 1) ≤ |K'| := by
        calc K' * (E⁻¹) ^ (P + 1 + 1) ≤ |K'| * (E⁻¹) ^ (P + 1 + 1) :=
              mul_le_mul_of_nonneg_right (le_abs_self K') (pow_nonneg hEi0 _)
          _ ≤ |K'| * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hEi0 hEi) (abs_nonneg _)
          _ = |K'| := mul_one _
      have hc : (E⁻¹) ^ (P + 1) * |J.scal (P + 1) (J.jet ν)| ≤ Mb := by
        have e : (E⁻¹) ^ (P + 1) * J.scal (P + 1) (J.jet ν) =
            x - (∑ k ∈ Finset.range (P + 1), (E⁻¹) ^ k * J.scal k (J.jet ν)) -
              (x - (∑ k ∈ Finset.range (P + 1), (E⁻¹) ^ k * J.scal k (J.jet ν) +
                (E⁻¹) ^ (P + 1) * J.scal (P + 1) (J.jet ν))) := by ring
        rw [← abs_of_nonneg (pow_nonneg hEi0 (P + 1)), ← abs_mul, e]
        refine (abs_sub _ _).trans ?_
        refine (add_le_add (abs_sub _ _) h1).trans ?_
        rw [hMb]
        linarith
      have hEp : 0 < E ^ (P + 1) := pow_pos hEpos _
      have e2 : |J.scal (P + 1) (J.jet ν)| =
          E ^ (P + 1) * ((E⁻¹) ^ (P + 1) * |J.scal (P + 1) (J.jet ν)|) := by
        rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hEpos.ne', one_pow, one_mul]
      rw [e2]
      exact mul_le_mul_of_nonneg_left hc hEp.le

/-- `(log ε)² ≤ 4ε` for `ε ≥ 1`. -/
theorem log_sq_le_four_mul {eps : ℝ} (heps : 1 ≤ eps) : Real.log eps ^ 2 ≤ 4 * eps := by
  have hpos : 0 < eps := lt_of_lt_of_le one_pos heps
  have hl0 : 0 ≤ Real.log eps := Real.log_nonneg heps
  have hsq : 0 < Real.sqrt eps := Real.sqrt_pos.2 hpos
  have h1 : Real.log (Real.sqrt eps) ≤ Real.sqrt eps - 1 := Real.log_le_sub_one_of_pos hsq
  have h2 : Real.log eps = 2 * Real.log (Real.sqrt eps) := by
    rw [Real.log_sqrt hpos.le]; ring
  have h3 : Real.log eps ≤ 2 * Real.sqrt eps := by linarith
  have h4 : Real.sqrt eps ^ 2 = eps := Real.sq_sqrt hpos.le
  nlinarith

/-- **T1-low from the normal transform.** -/
theorem cepsT1Low_of_normal {J : CepsJetData} {Gn : ℝ → ProbabilityMeasure ℝ → ℂ → ℂ}
    {Gk : ℕ → (ℕ → ℝ) → ℝ → ℂ} (hT5 : CepsT5 J) (hclose : CepsNormalClose Gn)
    (hexp : CepsNormalLowExpansion J Gn Gk) (hreg : CepsNormalCoeffReg J Gk)
    (hphi : ∀ k u p, J.phi k u p = cepsLowCoeff Gk J.scal k u p) : CepsT1Low J := by
  intro P
  obtain ⟨mb, hb⟩ := cepsT5_scal_bounds hT5 P
  obtain ⟨m5, h5⟩ := hT5 P
  obtain ⟨m0, h0⟩ := hclose
  obtain ⟨me, he⟩ := hexp P
  obtain ⟨mr, hr⟩ := hreg P
  refine ⟨max (max mb m5) (max m0 (max me mr)),
    fun D θ vlo vhi η hD hθ hvlo hv hη A hA => ?_⟩
  obtain ⟨rb, hrb, c_lo, Bc, hclo, Hb⟩ := hb D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r5, hr5, K5, e5, H5⟩ := h5 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨r0, hr0, K0, c0, t0, e0, hc0, ht0, p0, H0⟩ := h0 D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨re, hre, Ke, R, ee, hR, de, He⟩ := he D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨rr, hrr, Br, dr, Hr⟩ := hr D θ vlo vhi η hD hθ hvlo hv hη
  obtain ⟨em, s_lo, s_hi, B₂, hem, hslo, -, Hm⟩ := ceps_class_moments hD hθ hvlo hv
  set d : ℕ := max de dr with hd
  set B : ℝ := max Bc Br with hB
  obtain ⟨h₀, Kc, hh₀, Hc⟩ := norm_sub_sum_lowCompCoeff_le P d (c_lo := c_lo) (B := B)
    (K₁ := K5) (K₂ := |Ke|) hclo
  obtain ⟨Ka, hKa0, hKa⟩ := exists_pow_mul_exp_neg_le p0 (P + 1) hc0
  set eps₀ : ℝ := max (max (max e5 e0) (max ee em))
    (max h₀⁻¹ (max (4 * A ^ 2 / (s_lo * t0)) (16 * A ^ 2 / (s_lo * R)))) with heps₀
  refine ⟨min (min rb r5) (min r0 (min re rr)),
    lt_min (lt_min hrb hr5) (lt_min hr0 (lt_min hre hrr)),
    Kc * 4 ^ (d + P + 1) + |K0| * Ka, eps₀, d + P + 1, fun eps heps ν hν u hu => ?_⟩
  -- thresholds
  have he5 : e5 ≤ eps := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _))
    (le_max_left _ _)) heps
  have he0 : e0 ≤ eps := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _))
    (le_max_left _ _)) heps
  have hee : ee ≤ eps := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_left _ _)) heps
  have hemm : em ≤ eps := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_left _ _)) heps
  have hh₀' : h₀⁻¹ ≤ eps := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) heps
  have ht0' : 4 * A ^ 2 / (s_lo * t0) ≤ eps := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) heps
  have hR' : 16 * A ^ 2 / (s_lo * R) ≤ eps := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) heps
  have heps1 : 1 ≤ eps := hem.trans hemm
  have hepspos : 0 < eps := lt_of_lt_of_le one_pos heps1
  -- class memberships
  have hνb := hν.mono ((le_max_left mb m5).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_left _ _))
  have hν5 := hν.mono ((le_max_right mb m5).trans (le_max_left _ _))
    ((min_le_left _ _).trans (min_le_right _ _))
  have hν0 := hν.mono ((le_max_left m0 _).trans (le_max_right _ _))
    ((min_le_right _ _).trans (min_le_left _ _))
  have hνe := hν.mono (((le_max_left me mr).trans (le_max_right m0 _)).trans (le_max_right _ _))
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hνr := hν.mono (((le_max_right me mr).trans (le_max_right m0 _)).trans (le_max_right _ _))
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hlo, hhi, -⟩ := Hm eps hemm ν hν.reg
  obtain ⟨hc0', hcB⟩ := Hb ν hνb
  set p := J.jet ν with hp
  set C := lawC eps ν with hC
  have he2 : 0 < eps ^ 2 := by positivity
  set s : ℝ := C / eps ^ 2 with hs
  have hspos : 0 < s := lt_of_lt_of_le hslo hlo
  have hCpos : 0 < C := by
    have := mul_pos hspos he2
    rwa [hs, div_mul_cancel₀ _ he2.ne'] at this
  -- the band
  have hu4 : |u| ≤ 4 * A ^ 2 * eps := by
    refine hu.trans ?_
    rw [mul_pow]
    calc A ^ 2 * Real.log eps ^ 2 ≤ A ^ 2 * (4 * eps) :=
          mul_le_mul_of_nonneg_left (log_sq_le_four_mul heps1) (sq_nonneg A)
      _ = 4 * A ^ 2 * eps := by ring
  set ω : ℝ := -4 * u with hω
  set y : ℝ := ω / s with hy
  have hyabs : |y| ≤ 16 * A ^ 2 * eps / s_lo := by
    rw [hy, abs_div, abs_of_pos hspos, hω, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4),
      div_le_div_iff₀ hspos hslo]
    have := mul_le_mul hu4 hlo hslo.le (by positivity)
    linarith
  have hyR : |y| ≤ R * eps ^ 2 := by
    refine hyabs.trans ?_
    rw [div_le_iff₀ hslo]
    have : 16 * A ^ 2 ≤ eps * (s_lo * R) := by
      rwa [div_le_iff₀ (mul_pos hslo hR)] at hR'
    have := mul_le_mul_of_nonneg_left this hepspos.le
    linarith
  set y' : ℝ := -(u / C) with hy'
  have hy't : |y'| ≤ t0 := by
    rw [hy', abs_neg, abs_div, abs_of_pos hCpos, div_le_iff₀ hCpos]
    have hC' : s_lo * eps ^ 2 ≤ C := by rwa [hs, le_div_iff₀ he2] at hlo
    have h4 : 4 * A ^ 2 ≤ eps * (s_lo * t0) := by
      rwa [div_le_iff₀ (mul_pos hslo ht0)] at ht0'
    calc |u| ≤ 4 * A ^ 2 * eps := hu4
      _ ≤ eps * (s_lo * t0) * eps := mul_le_mul_of_nonneg_right h4 hepspos.le
      _ = t0 * (s_lo * eps ^ 2) := by ring
      _ ≤ t0 * C := mul_le_mul_of_nonneg_left hC' ht0.le
  have hyy : 4 * eps ^ 2 * y' = y := by
    rw [hy', hy, hω, hs]
    field_simp
  -- the actual/normal step
  have hact : ‖cepsOutChar eps ν u - Gn eps ν (Complex.I * y)‖ ≤
      |K0| * Ka * (eps⁻¹) ^ (P + 1) := by
    rw [cepsOutChar_eq_actual, ← hyy]
    refine (H0 eps he0 ν hν0 y' hy't).trans ?_
    calc K0 * eps ^ p0 * Real.exp (-c0 * eps) ≤ |K0| * (eps ^ p0 * Real.exp (-c0 * eps)) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_abs_self K0) (by positivity)
      _ ≤ |K0| * (Ka * (eps⁻¹) ^ (P + 1)) :=
          mul_le_mul_of_nonneg_left (hKa eps heps1) (abs_nonneg _)
      _ = |K0| * Ka * (eps⁻¹) ^ (P + 1) := by ring
  -- the composition step
  have hh0 : 0 < eps⁻¹ := inv_pos.mpr hepspos
  have hhh₀ : eps⁻¹ ≤ h₀ := by
    rw [inv_le_comm₀ hepspos hh₀]
    exact hh₀'
  have hg : ∀ j ≤ P, ContDiff ℝ (P + 1) (fun x => (2⁻¹ : ℂ) ^ j * Gk j p x) :=
    fun j hj => contDiff_const.mul (Hr ν hνr j hj).1
  have hgB : ∀ j ≤ P, ∀ m ≤ P + 1, ∀ x : ℝ,
      ‖iteratedDeriv m (fun x => (2⁻¹ : ℂ) ^ j * Gk j p x) x‖ ≤ B * (1 + |x|) ^ d := by
    intro j hj m hm x
    rw [iteratedDeriv_const_mul_field, norm_mul, norm_pow, norm_inv, Complex.norm_two]
    have hbd := (Hr ν hνr j hj).2 m hm x
    have hBr0 : 0 ≤ Br := by
      have h1 := (norm_nonneg _).trans ((Hr ν hνr j hj).2 m hm 0)
      have h2 : (0 : ℝ) < (1 + |(0 : ℝ)|) ^ dr := by positivity
      exact nonneg_of_mul_nonneg_left h1 h2
    have hpow : (1 + |x|) ^ dr ≤ (1 + |x|) ^ d :=
      pow_le_pow_right₀ (by linarith [abs_nonneg x]) (le_max_right _ _)
    calc (2⁻¹ : ℝ) ^ j * ‖iteratedDeriv m (Gk j p) x‖ ≤ 1 * (Br * (1 + |x|) ^ dr) :=
          mul_le_mul (pow_le_one₀ (by norm_num) (by norm_num)) hbd (norm_nonneg _) zero_le_one
      _ ≤ B * (1 + |x|) ^ d := by
          rw [one_mul]
          exact mul_le_mul (le_max_right _ _) hpow (by positivity)
            (hBr0.trans (le_max_right _ _))
  have hcB' : ∀ k ≤ P, |J.scal k p| ≤ B := fun k hk => (hcB k hk).trans (le_max_left _ _)
  have hsexp := H5 eps he5 ν hν5
  have hFexp : ‖Gn eps ν (Complex.I * y) - ∑ j ∈ Finset.range (P + 1),
      ((eps⁻¹ : ℝ) : ℂ) ^ j * ((2⁻¹ : ℂ) ^ j * Gk j p (ω / s))‖ ≤
      |Ke| * (eps⁻¹) ^ (P + 1) * (1 + |ω / s|) ^ d := by
    have h1 := He eps hee ν hνe y hyR
    have e : ∑ j ∈ Finset.range (P + 1), ((eps⁻¹ : ℝ) : ℂ) ^ j *
          ((2⁻¹ : ℂ) ^ j * Gk j p (ω / s)) =
        ∑ j ∈ Finset.range (P + 1), ((((2 * eps)⁻¹) ^ j : ℝ) : ℂ) * Gk j p y := by
      refine Finset.sum_congr rfl fun j _ => ?_
      push_cast
      rw [mul_inv]
      ring
    rw [e]
    refine h1.trans ?_
    have hpow : (1 + |y|) ^ de ≤ (1 + |y|) ^ d :=
      pow_le_pow_right₀ (by linarith [abs_nonneg y]) (le_max_left _ _)
    calc Ke * (eps⁻¹) ^ (P + 1) * (1 + |y|) ^ de ≤ |Ke| * (eps⁻¹) ^ (P + 1) * (1 + |y|) ^ de :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self Ke) (by positivity)) (by positivity)
      _ ≤ |Ke| * (eps⁻¹) ^ (P + 1) * (1 + |y|) ^ d :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcomp := Hc (fun i => J.scal i p) (fun j x => (2⁻¹ : ℂ) ^ j * Gk j p x) ω s eps⁻¹
    (Gn eps ν (Complex.I * y)) hc0' hcB' hg hgB hh0 hhh₀ hsexp hFexp
  -- assemble
  have hsum : ∑ k ∈ Finset.range (P + 1), ((eps⁻¹) ^ k : ℝ) • J.phi k u (J.jet ν) =
      ∑ k ∈ Finset.range (P + 1), ((eps⁻¹ : ℝ) : ℂ) ^ k *
        lowCompCoeff (fun j x => (2⁻¹ : ℂ) ^ j * Gk j p x) (fun i => J.scal i p) ω k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hphi, Complex.real_smul]
    push_cast
    rfl
  rw [hsum]
  have hω' : (1 + |ω|) ^ (d + P + 1) ≤ 4 ^ (d + P + 1) * (1 + |u|) ^ (d + P + 1) := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [hω, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith [abs_nonneg u]
  have hKc : 0 ≤ Kc := by
    have h1 := (norm_nonneg _).trans hcomp
    have h2 : 0 < (eps⁻¹) ^ (P + 1) * (1 + |ω|) ^ (d + P + 1) := by positivity
    rw [mul_assoc] at h1
    exact nonneg_of_mul_nonneg_left h1 h2
  have h1u : 1 ≤ (1 + |u|) ^ (d + P + 1) := one_le_pow₀ (by linarith [abs_nonneg u])
  calc ‖cepsOutChar eps ν u - ∑ k ∈ Finset.range (P + 1), ((eps⁻¹ : ℝ) : ℂ) ^ k *
        lowCompCoeff (fun j x => (2⁻¹ : ℂ) ^ j * Gk j p x) (fun i => J.scal i p) ω k‖
      ≤ ‖cepsOutChar eps ν u - Gn eps ν (Complex.I * y)‖ +
          ‖Gn eps ν (Complex.I * y) - ∑ k ∈ Finset.range (P + 1), ((eps⁻¹ : ℝ) : ℂ) ^ k *
            lowCompCoeff (fun j x => (2⁻¹ : ℂ) ^ j * Gk j p x) (fun i => J.scal i p) ω k‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ |K0| * Ka * (eps⁻¹) ^ (P + 1) +
          Kc * (eps⁻¹) ^ (P + 1) * (4 ^ (d + P + 1) * (1 + |u|) ^ (d + P + 1)) := by
        refine add_le_add hact (hcomp.trans ?_)
        exact mul_le_mul_of_nonneg_left hω' (by positivity)
    _ ≤ |K0| * Ka * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ (d + P + 1) +
          Kc * (eps⁻¹) ^ (P + 1) * (4 ^ (d + P + 1) * (1 + |u|) ^ (d + P + 1)) := by
        exact add_le_add (le_mul_of_one_le_right (by positivity) h1u) le_rfl
    _ = (Kc * 4 ^ (d + P + 1) + |K0| * Ka) * (eps⁻¹) ^ (P + 1) * (1 + |u|) ^ (d + P + 1) := by
        ring

end

end PGM
