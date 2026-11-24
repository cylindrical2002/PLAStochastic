import PLAStochastic.Index.GEP.PointwiseSmall.SegmentFacts

/-!
# WP4 leaf `PointwiseSmall`, row V: the direction derivative of `v(Φ_ε ν)`

`J_V = outJ psiVar`, `φ_V(y) = y² - 2y`.  Along `ν_z = (1 - z) ν + z σ` let `f_V` be the
`RawDiscId` continuation of `E φ_V(S_T/C)` (fixed base scale `C = C_ε(ν)`), `f_C` that of `C_ε`,
and `f_M = C² f_V + 2 C f_C`: on the real segment `f_M(t) = E_{ν_t} S_T²` (Wald).  With the real
base constant `lam₀ = m₂(0)/m₁(0)²`, `m_j` the raw moments of `rawLaw ε ν_t`,
`F₂(z) = v_z² f_M(z)/ε⁴ - lam₀ (v_z f_C(z)/ε²)²`
is holomorphic, polynomially bounded, and equals `m₂(t) - lam₀ m₁(t)²` on the real segment, which is
`O(ε^{-βU})` by (U) (`F₂(0) = 0`).  Interpolation bounds `F₂'(0)`, and algebraically
(`pw_rowV_hasDerivAt`, no division by the complex continuation)
`F₂'(0) = m₁(0)² (V' - 2(M₂/C² - 1) D/C) = m₁(0)² ∫ J_V d(σ - ν)`,
`V' = ∫ I_{φ_V} d(σ - ν)`, `D = ∫ J_C d(σ - ν)`, since `κ_{psiVar} = 2(M₂/C² - 1)`.
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

variable {D θ vlo vhi : ℝ}

/-! ## The derivative of `F₂` -/

/-- **The derivative identity of row V** (no division by the complex continuation). -/
theorem pw_rowV_hasDerivAt {fV fC : ℂ → ℂ} {v vσ C₀ M₂ V' Dj e lam₀ : ℝ}
    (hV : HasDerivAt fV (V' : ℂ) 0) (hC : HasDerivAt fC (Dj : ℂ) 0)
    (hV0 : fV 0 = ((M₂ / C₀ ^ 2 - 2 : ℝ) : ℂ)) (hC0 : fC 0 = (C₀ : ℂ))
    (hlam : lam₀ = M₂ / C₀ ^ 2) (hC₀ : C₀ ≠ 0) (he : e ≠ 0) :
    HasDerivAt (fun z => pwVz v vσ z ^ 2 * ((C₀ : ℂ) ^ 2 * fV z + 2 * (C₀ : ℂ) * fC z) /
        ((e : ℂ) ^ 2) - (lam₀ : ℂ) * (pwVz v vσ z * fC z / (e : ℂ)) ^ 2)
      ((((v * C₀ / e) ^ 2 * (V' - 2 * (M₂ / C₀ ^ 2 - 1) * Dj / C₀)) : ℝ) : ℂ) 0 := by
  have ha := hasDerivAt_pwVz v vσ (0 : ℂ)
  have hg : HasDerivAt (fun z => (C₀ : ℂ) ^ 2 * fV z + 2 * (C₀ : ℂ) * fC z)
      ((C₀ : ℂ) ^ 2 * V' + 2 * (C₀ : ℂ) * Dj) 0 :=
    (hV.const_mul _).add (hC.const_mul _)
  have h1 := ((ha.pow 2).mul hg).div_const ((e : ℂ) ^ 2)
  have h2 := (((ha.mul hC).div_const (e : ℂ)).pow 2).const_mul (lam₀ : ℂ)
  refine (h1.sub h2).congr_deriv ?_
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [pwVz_zero, hV0, hC0, hlam]
  have hC₀' : (C₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hC₀
  have he' : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 he
  push_cast
  field_simp
  ring

/-- **The disc bound of `F₂`** (pure algebra). -/
theorem pw_rowV_norm_le {a fV fC : ℂ} {Va C₀ kV KR KC Cp Λ lam₀ eps : ℝ} (pR pC : ℕ)
    (heps1 : 1 ≤ eps) (ha : ‖a‖ ≤ Va) (hVa0 : 0 ≤ Va) (hkV : 0 ≤ kV)
    (hfV : ‖fV‖ ≤ kV * (|KR| * eps ^ pR)) (hfC : ‖fC‖ ≤ |KC| * eps ^ pC) (hC0 : 0 < C₀)
    (hCp0 : 0 ≤ Cp) (hCp : C₀ ≤ Cp * eps ^ 2) (hlam0 : 0 ≤ lam₀) (hlamle : lam₀ ≤ Λ) :
    ‖a ^ 2 * ((C₀ : ℂ) ^ 2 * fV + 2 * (C₀ : ℂ) * fC) / (((eps ^ 2 : ℝ) : ℂ) ^ 2) -
        (lam₀ : ℂ) * (a * fC / ((eps ^ 2 : ℝ) : ℂ)) ^ 2‖ ≤
      Va ^ 2 * (Cp ^ 2 * kV * |KR| + 2 * Cp * |KC| + Λ * |KC| ^ 2) * eps ^ (pR + 2 * pC) := by
  have heps0 : 0 < eps := by linarith
  have heps2 : 0 < eps ^ 2 := by positivity
  have hpR : eps ^ pR ≤ eps ^ (pR + 2 * pC) := pow_le_pow_right₀ heps1 (by omega)
  have hpC : eps ^ pC ≤ eps ^ (pR + 2 * pC) := pow_le_pow_right₀ heps1 (by omega)
  have hpC2 : (eps ^ pC) ^ 2 ≤ eps ^ (pR + 2 * pC) := by
    rw [← pow_mul]; exact pow_le_pow_right₀ heps1 (by omega)
  have he4 : ‖(((eps ^ 2 : ℝ) : ℂ) ^ 2)‖ = (eps ^ 2) ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps2]
  have he2' : ‖((eps ^ 2 : ℝ) : ℂ)‖ = eps ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos heps2]
  have hC₀n : ‖(C₀ : ℂ)‖ = C₀ := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hC0]
  set P := pR + 2 * pC
  have hg : ‖(C₀ : ℂ) ^ 2 * fV + 2 * (C₀ : ℂ) * fC‖ ≤
      C₀ ^ 2 * (kV * (|KR| * eps ^ pR)) + 2 * C₀ * (|KC| * eps ^ pC) := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul, norm_pow, hC₀n, show ‖(2 : ℂ)‖ = 2 by simp]
    gcongr
  have hX : C₀ ^ 2 * (kV * (|KR| * eps ^ pR)) + 2 * C₀ * (|KC| * eps ^ pC) ≤
      (eps ^ 2) ^ 2 * ((Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P) := by
    have a1 : C₀ ^ 2 * (kV * (|KR| * eps ^ pR)) ≤
        (Cp * eps ^ 2) ^ 2 * (kV * (|KR| * eps ^ P)) := by gcongr
    have a2 : 2 * C₀ * (|KC| * eps ^ pC) ≤ 2 * (Cp * eps ^ 2) * (|KC| * eps ^ P) := by
      gcongr
    have a3 : 2 * (Cp * eps ^ 2) * (|KC| * eps ^ P) ≤
        2 * (Cp * (eps ^ 2) ^ 2) * (|KC| * eps ^ P) := by
      gcongr
      exact le_self_pow₀ heps1 (by norm_num)
    have e : (Cp * eps ^ 2) ^ 2 * (kV * (|KR| * eps ^ P)) + 2 * (Cp * (eps ^ 2) ^ 2) *
        (|KC| * eps ^ P) = (eps ^ 2) ^ 2 * ((Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P) := by
      ring
    linarith
  have hT1 : ‖a ^ 2 * ((C₀ : ℂ) ^ 2 * fV + 2 * (C₀ : ℂ) * fC) / (((eps ^ 2 : ℝ) : ℂ) ^ 2)‖ ≤
      Va ^ 2 * (Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P := by
    rw [norm_div, he4, norm_mul, norm_pow, div_le_iff₀ (by positivity)]
    calc ‖a‖ ^ 2 * ‖(C₀ : ℂ) ^ 2 * fV + 2 * (C₀ : ℂ) * fC‖
        ≤ Va ^ 2 * ((eps ^ 2) ^ 2 * ((Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P)) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) ha 2) (hg.trans hX) (norm_nonneg _)
            (by positivity)
      _ = Va ^ 2 * (Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P * (eps ^ 2) ^ 2 := by ring
  have hT2 : ‖(lam₀ : ℂ) * (a * fC / ((eps ^ 2 : ℝ) : ℂ)) ^ 2‖ ≤ Va ^ 2 * (Λ * |KC| ^ 2) * eps ^ P := by
    rw [norm_mul, norm_pow, norm_div, norm_mul, he2', Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlam0]
    have h1 : ‖a‖ * ‖fC‖ / eps ^ 2 ≤ Va * (|KC| * eps ^ pC) :=
      (div_le_self (by positivity) (one_le_pow₀ heps1)).trans
        (mul_le_mul ha hfC (norm_nonneg _) hVa0)
    calc lam₀ * (‖a‖ * ‖fC‖ / eps ^ 2) ^ 2 ≤ Λ * (Va * (|KC| * eps ^ pC)) ^ 2 :=
          mul_le_mul hlamle (pow_le_pow_left₀ (by positivity) h1 2) (by positivity)
            (hlam0.trans hlamle)
      _ = Va ^ 2 * (Λ * |KC| ^ 2) * (eps ^ pC) ^ 2 := by ring
      _ ≤ Va ^ 2 * (Λ * |KC| ^ 2) * eps ^ P := by
          have : 0 ≤ Va ^ 2 * (Λ * |KC| ^ 2) := by
            have := hlam0.trans hlamle
            positivity
          gcongr
  calc ‖a ^ 2 * ((C₀ : ℂ) ^ 2 * fV + 2 * (C₀ : ℂ) * fC) / (((eps ^ 2 : ℝ) : ℂ) ^ 2) -
        (lam₀ : ℂ) * (a * fC / ((eps ^ 2 : ℝ) : ℂ)) ^ 2‖ ≤ _ := norm_sub_le _ _
    _ ≤ Va ^ 2 * (Cp ^ 2 * kV * |KR| + 2 * Cp * |KC|) * eps ^ P +
        Va ^ 2 * (Λ * |KC| ^ 2) * eps ^ P := add_le_add hT1 hT2
    _ = Va ^ 2 * (Cp ^ 2 * kV * |KR| + 2 * Cp * |KC| + Λ * |KC| ^ 2) * eps ^ P := by ring

/-- **The real-segment bound of `F₂`** (pure algebra). -/
theorem pw_rowV_seg_le {m2t m20 m1t m10 lam₀ Λ KM Bm1 δ : ℝ} (hlam0 : 0 ≤ lam₀)
    (hΛ0 : 0 ≤ Λ) (hlamle : lam₀ ≤ Λ) (hz : m20 - lam₀ * m10 ^ 2 = 0) (h1 : |m1t - m10| ≤ KM * δ)
    (h2 : |m2t - m20| ≤ KM * δ) (hp1 : 0 ≤ m1t) (hq1 : m1t ≤ Bm1) (hp0 : 0 ≤ m10)
    (hq0 : m10 ≤ Bm1) (hδ : 0 ≤ KM * δ) :
    |m2t - lam₀ * m1t ^ 2| ≤ KM * (1 + 2 * Λ * Bm1) * δ := by
  have e : m2t - lam₀ * m1t ^ 2 = (m2t - m20) - lam₀ * ((m1t - m10) * (m1t + m10)) := by
    linear_combination hz
  rw [e]
  have hsum : |m1t + m10| ≤ 2 * Bm1 := by
    rw [abs_of_nonneg (by positivity)]; linarith
  calc |(m2t - m20) - lam₀ * ((m1t - m10) * (m1t + m10))|
      ≤ |m2t - m20| + lam₀ * (|m1t - m10| * |m1t + m10|) := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hlam0]
    _ ≤ KM * δ + Λ * (KM * δ * (2 * Bm1)) := by
        gcongr
    _ = KM * (1 + 2 * Λ * Bm1) * δ := by ring

/-- **The real-segment value of `F₂`** (pure algebra). -/
theorem pw_rowV_real_eq {vt Ct M2t C₀ lam₀ e : ℝ} (hC₀ : C₀ ≠ 0) (he : e ≠ 0) :
    (vt : ℂ) ^ 2 * ((C₀ : ℂ) ^ 2 * ((M2t / C₀ ^ 2 - 2 * Ct / C₀ : ℝ) : ℂ) +
        2 * (C₀ : ℂ) * (Ct : ℂ)) / ((e : ℂ) ^ 2) -
      (lam₀ : ℂ) * ((vt : ℂ) * (Ct : ℂ) / (e : ℂ)) ^ 2 =
      (((vt / e) ^ 2 * M2t - lam₀ * (vt * Ct / e) ^ 2 : ℝ) : ℂ) := by
  have hC₀' : (C₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hC₀
  have he' : (e : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 he
  push_cast
  field_simp
  ring

/-! ## Row V -/

/-- **Row V along one direction**: `|∫ J_V dσ - ∫ J_V dν| ≤ K ε^{-βU} (1 + log ε)²`. -/
theorem pw_rowV (hS : SurvivalBound) {βU : ℝ} (hβU : 0 ≤ βU) (hUM : PwUnivMix βU)
    (hD : 0 < D) (hθ : 0 < θ) (hvlo : 0 < vlo) (hv : vlo ≤ vhi) (A θσ : ℝ) (hθσ : 0 < θσ) :
    ∃ K e0 : ℝ, 0 ≤ K ∧ 1 ≤ e0 ∧ ∀ eps, e0 ≤ eps → ∀ ν σ : ProbabilityMeasure ℝ,
      RegLaw D θ vlo vhi ν → SigmaLaw A θσ σ →
        |(∫ x, lawJV eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJV eps ν x ∂(ν : Measure ℝ)| ≤
          K * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by
  -- constants of the class
  have hvhi : 0 < vhi + 1 := by linarith
  set b₀ : ℝ := 128 * (vhi + 1) with hb₀
  have hb₀0 : 0 < b₀ := by positivity
  have hcP := cPlus_pos
  set Cp : ℝ := cPlus / (vlo / 2) with hCp
  have hCp0 : 0 < Cp := by positivity
  set cs : ℝ := gamMix vlo with hcs
  have hcs0 : 0 < cs := gamMix_pos hvlo
  have hCK : (0 : ℝ) < CK := by unfold CK; norm_num
  set Bm1 : ℝ := (vhi + 1) * Cp with hBm1
  set Bm2 : ℝ := (vhi + 1) ^ 2 * (2 * (1 / cs) ^ 2 * CK) with hBm2
  set Λ : ℝ := Bm2 * (b₀ / vlo) ^ 2 with hΛ
  have hks := kapSig_nonneg A θσ hθσ
  set Va : ℝ := 2 * vhi + kapSig A θσ with hVa
  have hVa0 : 0 ≤ Va := by rw [hVa]; linarith
  -- the analytic inputs
  obtain ⟨γR, hγR, hRD⟩ := rawDiscId_of_survivalBound hS D θ vlo vhi hD hθ hvlo hv
  obtain ⟨κ₁, K₁, e₁, hκ₁, -, -, hker⟩ := pw_kernel_facts hD hθ hvlo hv
  set ηV : ℝ := min γR κ₁ / (2 * b₀) with hηV
  have hηV0 : 0 < ηV := by positivity
  have hηVb : 2 * ηV * b₀ = min γR κ₁ := by rw [hηV]; field_simp
  set MV : ℝ := 2 / ηV + 2 with hMV
  have hMV0 : 0 < MV := by positivity
  have hkV0 : 0 < MV / ηV := by positivity
  obtain ⟨rR, KR, eR, pR, hrR, hRD'⟩ := hRD A θσ hθσ
  obtain ⟨rC, KC, eC, pC, hrC, hrCt, heC, hCD⟩ := pw_cDisc hS hD hθ hvlo hv (A := A) hθσ
  obtain ⟨KJ, eJ, -, -, hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  obtain ⟨KM, eM, hKM, -, hRM⟩ := pw_real_moments hUM hD hθ hvlo hv A θσ hθσ
  obtain ⟨es, -, hseg⟩ := pw_seg_facts (vhi := vhi) hD hθ hvlo A θσ hθσ
  set R : ℝ := min rR rC with hRdef
  have hR0 : 0 < R := lt_min hrR hrC
  have hRr : R ≤ rR := min_le_left _ _
  have hRc : R ≤ rC := min_le_right _ _
  have hRt : R ≤ tMix A θσ := hRc.trans hrCt
  have hR1 : R ≤ 1 := hRt.trans ((tMix_le A θσ hθσ).trans (by norm_num))
  set P : ℕ := pR + 2 * pC with hP
  set K₁' : ℝ := Va ^ 2 * (Cp ^ 2 * (MV / ηV) * |KR| + 2 * Cp * |KC| + Λ * |KC| ^ 2) with hK₁'
  set K₂' : ℝ := KM * (1 + 2 * Λ * Bm1) with hK₂'
  obtain ⟨K₃, hK₃, hint⟩ := pw_interp_small discInterp (R := R) (K₁ := K₁') (K₂ := K₂')
    (b := βU) P hR0 hβU
  set eκ : ℝ := 2 * ηV * b₀ * (1 / θσ + 2 / θ) + 1 with heκ
  refine ⟨K₃ * (b₀ / vlo) ^ 2,
    max (max (max eR eC) (max eJ eM)) (max (max es e₁) eκ),
    by positivity, heC.trans ((le_max_right _ _).trans ((le_max_left _ _).trans
      (le_max_left _ _))), ?_⟩
  intro eps heps ν σ hν hσ
  have hle1 : ∀ {a : ℝ}, a ≤ max (max (max eR eC) (max eJ eM)) (max (max es e₁) eκ) →
      a ≤ eps := fun h => h.trans heps
  have heR' : eR ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _)))
  have heC' : eC ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_left _ _)))
  have heJ' : eJ ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _)))
  have heM' : eM ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_left _ _)))
  have hes' : es ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have he₁' : e₁ ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have heκ' : eκ ≤ eps := hle1 ((le_max_right _ _).trans (le_max_right _ _))
  have heps1 : 1 ≤ eps := heC.trans heC'
  have heps0 : 0 < eps := by linarith only [heps1]
  have heps2 : (0 : ℝ) < eps ^ 2 := by positivity
  -- the class facts along the segment
  have hSfacts := hseg eps hes' ν σ hν hσ
  have h0t : (0 : ℝ) ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨le_rfl, (tMix_pos A θσ hθσ).le⟩
  obtain ⟨-, -, i1ν, i2ν, hb2ν, hWν, hCmν, hCpν, -, hm1ν⟩ := hSfacts 0 h0t
  simp only [mixPM_zero] at i1ν i2ν hb2ν hWν hCmν hCpν hm1ν
  rw [← hb₀] at hCmν
  rw [← hCp] at hCpν
  set C₀ := lawC eps ν with hC₀
  have hC0 : 0 < C₀ := lt_of_lt_of_le (by positivity) hCmν
  set v := lawVar ν with hvdef
  set vσ := lawVar σ with hvσdef
  have hv0 : vlo ≤ v := hν.var_ge
  have hvle : v ≤ vhi := hν.var_le
  have hvpos : 0 < v := hvlo.trans_le hv0
  have hvσ0 : 0 ≤ vσ := hσ.lawVar_nonneg
  have hvσle : vσ ≤ kapSig A θσ := hσ.lawVar_le hθσ
  set M₂ := ∫ g, stopSum eps g ^ 2 ∂(iidLaw ν) with hM₂
  -- bounds on the raw moments
  have hm1le : ∀ t ∈ Icc (0 : ℝ) (tMix A θσ), 0 ≤ pwM1 eps (mixPM ν σ t) ∧
      pwM1 eps (mixPM ν σ t) ≤ Bm1 := by
    intro t ht
    obtain ⟨hm, -, -, -, -, -, hCm, hCp', -, hm1⟩ := hSfacts t ht
    rw [← hb₀] at hCm
    rw [← hCp] at hCp'
    rw [hm1]
    have hvt0 : 0 ≤ lawVar (mixPM ν σ t) := (by positivity : (0 : ℝ) ≤ vlo / 2).trans hm.var_ge
    have hC0' : 0 ≤ lawC eps (mixPM ν σ t) := (by positivity : (0 : ℝ) ≤ eps ^ 2 / b₀).trans hCm
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ heps2, hBm1]
    calc lawVar (mixPM ν σ t) * lawC eps (mixPM ν σ t) ≤ (vhi + 1) * (Cp * eps ^ 2) :=
          mul_le_mul hm.var_le hCp' hC0' hvhi.le
      _ = (vhi + 1) * Cp * eps ^ 2 := by ring
  have hm2le : pwM2 eps ν ≤ Bm2 := by
    rw [pwM2_eq]
    have h1 : (v / eps ^ 2) ^ 2 ≤ (vhi + 1) ^ 2 / (eps ^ 2) ^ 2 := by
      rw [div_pow]
      gcongr
      linarith only [hvle]
    have hM0 : 0 ≤ M₂ := integral_nonneg fun g => sq_nonneg _
    calc (v / eps ^ 2) ^ 2 * M₂ ≤ (vhi + 1) ^ 2 / (eps ^ 2) ^ 2 * (2 * (eps ^ 2 / cs) ^ 2 * CK) :=
          mul_le_mul h1 hb2ν hM0 (by positivity)
      _ = Bm2 := by rw [hBm2]; field_simp
  have hm1pos : vlo / b₀ ≤ pwM1 eps ν := by
    rw [hm1ν, le_div_iff₀ heps2]
    rw [div_le_iff₀ hb₀0] at hCmν
    calc vlo / b₀ * eps ^ 2 = vlo * (eps ^ 2 / b₀) := by ring
      _ ≤ v * C₀ := mul_le_mul hv0 (by rw [div_le_iff₀ hb₀0]; exact hCmν) (by positivity)
          hvpos.le
  have hm1pos' : 0 < pwM1 eps ν := lt_of_lt_of_le (by positivity) hm1pos
  set lam₀ := pwM2 eps ν / pwM1 eps ν ^ 2 with hlam
  have hlam0 : 0 ≤ lam₀ := by
    rw [hlam]
    have : 0 ≤ pwM2 eps ν := integral_nonneg fun g => sq_nonneg _
    positivity
  have hbv : (b₀ / vlo) ^ 2 * (vlo / b₀) ^ 2 = 1 := by
    rw [← mul_pow, div_mul_div_comm, mul_comm b₀ vlo,
      div_self (by positivity : (vlo * b₀ : ℝ) ≠ 0), one_pow]
  have hBm20 : 0 ≤ Bm2 := by rw [hBm2]; positivity
  have hΛ0 : 0 ≤ Λ := by rw [hΛ]; positivity
  have hlamle : lam₀ ≤ Λ := by
    rw [hlam, hΛ, div_le_iff₀ (by positivity)]
    have h1 : (vlo / b₀) ^ 2 ≤ pwM1 eps ν ^ 2 := pow_le_pow_left₀ (by positivity) hm1pos 2
    have hB0 : 0 ≤ Bm2 * (b₀ / vlo) ^ 2 := by positivity
    calc pwM2 eps ν ≤ Bm2 := hm2le
      _ = Bm2 * (b₀ / vlo) ^ 2 * (vlo / b₀) ^ 2 := by rw [mul_assoc, hbv, mul_one]
      _ ≤ Bm2 * (b₀ / vlo) ^ 2 * pwM1 eps ν ^ 2 := mul_le_mul_of_nonneg_left h1 hB0
  have hlamM : lam₀ = M₂ / C₀ ^ 2 := by
    rw [hlam, pwM2_eq, hm1ν, ← hvdef, ← hM₂]
    field_simp
  -- the normalised variance test
  have hψV := outTest_psiVar hηV0
  obtain ⟨hFhm, hFhκ⟩ := pw_normTest hψV hηV0 hMV0 hb₀0 heps0 hCmν
  set Fh : ℝ → ℝ := fun y => testFn psiVar (y / C₀) / (MV / ηV) with hFh
  set κ : ℝ := 2 * ηV * b₀ / eps ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hκγ : κ * eps ^ 2 ≤ min γR κ₁ := by
    rw [hκ, div_mul_cancel₀ _ heps2.ne', hηVb]
  have hFhγ : ∀ y, 0 ≤ y → |Fh y| ≤ Real.exp (γR * y / eps ^ 2) := by
    intro y hy
    refine (hFhκ y hy).trans (Real.exp_le_exp.2 ?_)
    have h1 : κ ≤ γR / eps ^ 2 := by
      rw [le_div_iff₀ heps2]; exact hκγ.trans (min_le_left _ _)
    calc κ * y ≤ γR / eps ^ 2 * y := mul_le_mul_of_nonneg_right h1 hy
      _ = γR * y / eps ^ 2 := by ring
  -- the kernel of the variance test
  obtain ⟨-, -, hIint⟩ := hker eps he₁' ν hν κ hκ0 (hκγ.trans (min_le_right _ _)) Fh hFhm hFhκ
  have heκ1 : 2 * ηV * b₀ * (1 / θσ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηV * b₀ * (2 / θ) := by positivity
    linarith only [this]
  have heκ2 : 2 * ηV * b₀ * (2 / θ) + 1 ≤ eps := by
    refine le_trans ?_ heκ'
    rw [heκ]
    have : 0 ≤ 2 * ηV * b₀ * (1 / θσ) := by positivity
    linarith only [this]
  have hκσ : κ ≤ θσ := by
    rw [hκ]
    refine pw_kappa_le (by positivity) hθσ ?_
    rw [div_eq_mul_one_div]; exact heκ1
  have hκν : κ ≤ θ / 2 := by
    rw [hκ]
    refine pw_kappa_le (by positivity) (half_pos hθ) ?_
    rw [div_div_eq_mul_div, mul_div_assoc]; exact heκ2
  have hIσ := hIint σ hσ.pos (hσ.integrable_exp hκσ)
  have hIν := hIint ν (hν.pos' hθ hvlo) (hν.integrable_exp hθ hvlo hκν)
  have houtIns : outIns eps ν psiVar =
      fun x => MV / ηV * insKernel eps ν (fun g => Fh (stopSum eps g)) x := by
    funext x
    exact pw_outIns_eq_mul eps ν psiVar hkV0.ne' x
  -- the continuations
  obtain ⟨fh, hfh, hfhb, -, hfhd, hfhr⟩ := hRD' eps heR' ν σ hν hσ Fh hFhm hFhγ
  obtain ⟨fC, hfC, hfCb, hfCr, hfCd⟩ := hCD eps heC' ν σ hν hσ
  obtain ⟨-, -, hJi⟩ := hJC eps heJ' ν hν
  set fV : ℂ → ℂ := fun z => ((MV / ηV : ℝ) : ℂ) * fh z with hfV
  set V' : ℝ := MV / ηV *
    ((∫ x, insKernel eps ν (fun g => Fh (stopSum eps g)) x ∂(σ : Measure ℝ)) -
      ∫ x, insKernel eps ν (fun g => Fh (stopSum eps g)) x ∂(ν : Measure ℝ)) with hV'
  set Dj : ℝ := (∫ x, lawJC eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)
    with hDj
  have hfhR : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 →
      fV t = ((∫ g, stopSum eps g ^ 2 ∂(iidLaw (mixPM ν σ t))) / C₀ ^ 2 -
        2 * lawC eps (mixPM ν σ t) / C₀ : ℝ) := by
    intro t ht0 ht1
    have ht : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith only [ht1, hRt, hR0]⟩
    obtain ⟨-, hS0, i1, i2, -, hW, -, -, -, -⟩ := hSfacts t ht
    rw [hfV]
    simp only
    rw [hfhr t ht0 (by linarith only [ht1, hRr]), ← Complex.ofReal_mul, hFh, integral_div,
      mul_div_cancel₀ _ hkV0.ne', pw_integral_psiVar hC0 hS0 i1 i2, hW]
  have hfV0 : fV 0 = ((M₂ / C₀ ^ 2 - 2 : ℝ) : ℂ) := by
    have h := hfhR 0 le_rfl (by positivity)
    simp only [mixPM_zero, Complex.ofReal_zero] at h
    rw [h, ← hC₀, ← hM₂, mul_div_cancel_right₀ _ hC0.ne']
  have hfC0 : fC 0 = (C₀ : ℂ) := by
    have h := hfCr 0 le_rfl hrC.le
    simpa only [mixPM_zero, Complex.ofReal_zero] using h
  have hfhda : HasDerivAt fh (deriv fh 0) 0 :=
    (hfh.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrR))).hasDerivAt
  have hfVd : HasDerivAt fV (V' : ℂ) 0 := by
    refine (hfhda.const_mul (((MV / ηV : ℝ)) : ℂ)).congr_deriv ?_
    rw [hfhd, hV']
    push_cast
    ring
  have hfCd' : HasDerivAt fC (Dj : ℂ) 0 := by
    have h := (hfC.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hrC))).hasDerivAt
    rwa [hfCd] at h
  -- the function `F₂`
  set F₂ : ℂ → ℂ := fun z => pwVz v vσ z ^ 2 * ((C₀ : ℂ) ^ 2 * fV z + 2 * (C₀ : ℂ) * fC z) /
    (((eps ^ 2 : ℝ) : ℂ) ^ 2) - (lam₀ : ℂ) * (pwVz v vσ z * fC z / ((eps ^ 2 : ℝ) : ℂ)) ^ 2
    with hF₂
  have hF₂D := pw_rowV_hasDerivAt (v := v) (vσ := vσ) (e := eps ^ 2) hfVd hfCd' hfV0 hfC0 hlamM
    hC0.ne' heps2.ne'
  have hF₂d : DifferentiableOn ℂ F₂ (ball 0 R) := by
    have ha := (differentiable_pwVz v vσ).differentiableOn (s := ball (0 : ℂ) R)
    have hfV' : DifferentiableOn ℂ fV (ball 0 R) :=
      (hfh.mono (ball_subset_ball hRr)).const_mul _
    have hfC' : DifferentiableOn ℂ fC (ball 0 R) := hfC.mono (ball_subset_ball hRc)
    exact ((ha.pow 2).mul ((hfV'.const_mul _).add (hfC'.const_mul _))).div_const _ |>.sub
      ((((ha.mul hfC').div_const _).pow 2).const_mul _)
  -- the bound on the disc
  have hF₂b : ∀ z ∈ ball (0 : ℂ) R, ‖F₂ z‖ ≤ K₁' * eps ^ P := by
    intro z hz
    have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.1 hz).le.trans hR1
    have ha : ‖pwVz v vσ z‖ ≤ Va :=
      (norm_pwVz_le hvpos.le hvσ0 hz1).trans (by rw [hVa]; linarith only [hvle, hvσle])
    have hfhz : ‖fh z‖ ≤ |KR| * eps ^ pR :=
      (hfhb z (ball_subset_ball hRr hz)).trans (by gcongr; exact le_abs_self _)
    have hfCz : ‖fC z‖ ≤ |KC| * eps ^ pC :=
      (hfCb z (ball_subset_ball hRc hz)).trans (by gcongr; exact le_abs_self _)
    have hfVz : ‖fV z‖ ≤ MV / ηV * (|KR| * eps ^ pR) := by
      rw [hfV]
      simp only
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hkV0]
      gcongr
    exact pw_rowV_norm_le pR pC heps1 ha hVa0 hkV0.le hfVz hfCz hC0 hCp0.le hCpν hlam0 hlamle
  -- the real segment
  have hF₂r : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 →
      F₂ t = ((pwM2 eps (mixPM ν σ t) - lam₀ * pwM1 eps (mixPM ν σ t) ^ 2 : ℝ) : ℂ) := by
    intro t ht0 ht1
    have ht : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith only [ht1, hRt, hR0]⟩
    obtain ⟨-, -, -, -, -, -, -, -, hvar, hm1⟩ := hSfacts t ht
    rw [pwM2_eq, hm1, hF₂]
    simp only
    rw [hfhR t ht0 ht1, hfCr t ht0 (by linarith only [ht1, hRc, hR0]), pwVz_ofReal, ← hvar]
    exact pw_rowV_real_eq hC0.ne' heps2.ne'
  have hF₂0 : F₂ 0 = 0 := by
    have h := hF₂r 0 le_rfl (by positivity)
    simp only [mixPM_zero, Complex.ofReal_zero] at h
    rw [h, hlam, div_mul_cancel₀ _ (pow_ne_zero 2 hm1pos'.ne'), sub_self, Complex.ofReal_zero]
  have hF₂s : ∀ t : ℝ, 0 ≤ t → t ≤ R / 8 → ‖F₂ t - F₂ 0‖ ≤ K₂' * eps ^ (-βU) := by
    intro t ht0 ht1
    have ht : t ∈ Icc (0 : ℝ) (tMix A θσ) := ⟨ht0, by linarith only [ht1, hRt, hR0]⟩
    rw [hF₂0, sub_zero, hF₂r t ht0 ht1, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨h1, h2⟩ := hRM eps heM' ν σ hν hσ t ht
    obtain ⟨hp1, hq1⟩ := hm1le t ht
    obtain ⟨hp0, hq0⟩ := hm1le 0 h0t
    simp only [mixPM_zero] at hp0 hq0
    have hz : pwM2 eps ν - lam₀ * pwM1 eps ν ^ 2 = 0 := by
      rw [hlam, div_mul_cancel₀ _ (pow_ne_zero 2 hm1pos'.ne'), sub_self]
    exact pw_rowV_seg_le hlam0 hΛ0 hlamle hz h1 h2 hp1 hq1 hp0 hq0 (by positivity)
  -- interpolation
  have hmain := hint F₂ eps heps1 hF₂d hF₂b hF₂s
  rw [hF₂D.deriv, Complex.norm_real, Real.norm_eq_abs] at hmain
  -- the identification with `J_V`
  have hκV := pw_outKappa_psiVar hC0 i1ν i2ν hWν
  have hIσ' : Integrable (outIns eps ν psiVar) (σ : Measure ℝ) := by
    rw [houtIns]; exact hIσ.const_mul _
  have hIν' : Integrable (outIns eps ν psiVar) (ν : Measure ℝ) := by
    rw [houtIns]; exact hIν.const_mul _
  have hJV := pw_integral_outJ_sub hIσ' hIν' (hJi σ) (hJi ν)
  have hV'' : (∫ x, outIns eps ν psiVar x ∂(σ : Measure ℝ)) -
      ∫ x, outIns eps ν psiVar x ∂(ν : Measure ℝ) = V' := by
    rw [houtIns, integral_const_mul, integral_const_mul, hV']
    ring
  have hid : (∫ x, lawJV eps ν x ∂(σ : Measure ℝ)) - ∫ x, lawJV eps ν x ∂(ν : Measure ℝ) =
      ((v * C₀ / eps ^ 2) ^ 2 * (V' - 2 * (M₂ / C₀ ^ 2 - 1) * Dj / C₀)) /
        (v * C₀ / eps ^ 2) ^ 2 := by
    rw [mul_div_cancel_left₀ _ (by positivity)]
    show (∫ x, outJ eps ν psiVar x ∂(σ : Measure ℝ)) - ∫ x, outJ eps ν psiVar x ∂(ν : Measure ℝ) = _
    rw [hJV, hV'', hκV, ← hC₀, ← hM₂, ← hDj]
    ring
  have hq0 : 0 < (v * C₀ / eps ^ 2) ^ 2 := by positivity
  rw [hid, abs_div, abs_of_pos hq0]
  have hq : vlo / b₀ ≤ v * C₀ / eps ^ 2 := by rw [← hm1ν]; exact hm1pos
  have hq2 : (vlo / b₀) ^ 2 ≤ (v * C₀ / eps ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) hq 2
  rw [div_le_iff₀ (by positivity)]
  calc |(v * C₀ / eps ^ 2) ^ 2 * (V' - 2 * (M₂ / C₀ ^ 2 - 1) * Dj / C₀)|
      ≤ K₃ * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := hmain
    _ = K₃ * (b₀ / vlo) ^ 2 * eps ^ (-βU) * (1 + Real.log eps) ^ 2 * (vlo / b₀) ^ 2 := by
        rw [show K₃ * (b₀ / vlo) ^ 2 * eps ^ (-βU) * (1 + Real.log eps) ^ 2 * (vlo / b₀) ^ 2 =
          K₃ * eps ^ (-βU) * (1 + Real.log eps) ^ 2 * ((b₀ / vlo) ^ 2 * (vlo / b₀) ^ 2) by ring,
          hbv, mul_one]
    _ ≤ K₃ * (b₀ / vlo) ^ 2 * eps ^ (-βU) * (1 + Real.log eps) ^ 2 *
          (v * C₀ / eps ^ 2) ^ 2 := by
        have : 0 ≤ K₃ * (b₀ / vlo) ^ 2 * eps ^ (-βU) * (1 + Real.log eps) ^ 2 := by positivity
        gcongr

end

end PGM
