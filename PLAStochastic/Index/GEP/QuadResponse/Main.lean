import PLAStochastic.Index.GEP.QuadResponse.PairContinuation
import PLAStochastic.Index.GEP.QuadResponse.DerivativeAtZero
import PLAStochastic.Index.GEP.QuadResponse.Directions
import PLAStochastic.Index.GEP.PointwiseSmall.CoarseInfluenceBounds

/-!
# WP4 leaf `QuadResponse` from (U) and `SurvivalBound` (PD §7)

`∫ J_φ · quadDir = 2 (∫ J_φ dσ₊ - ∫ J_φ dσ₋)` for the two direction laws of `quad_exists_pair`
(`θσ = 1`), and `∫ J_φ d(σ₊ - σ₋) = ∫ I_φ d(σ₊ - σ₋) - (κ_φ/C) ∫ J_C d(σ₊ - σ₋)`.  The first term
is `(M/η) H'(0)` for the pair continuation `H` of `quad_pair_H`, which is `O(1)` by
`quad_deriv_zero_bound`; the second is `O(M)` by `KappaBound` and row A
(`|∫ J_C d(σ - ν)/C + (v_σ - v)/v| ≤ K ε^{-βU} log² ε ≤ K`).
-/

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

theorem quad_Dj_bound {a b P Q B c : ℝ} (h1 : |a + P| ≤ B) (h2 : |b + Q| ≤ B)
    (h3 : |P - Q| ≤ c) : |a - b| ≤ 2 * B + c := by
  calc |a - b| = |((a + P) - (b + Q)) - (P - Q)| := by ring_nf
    _ ≤ |(a + P) - (b + Q)| + |P - Q| := abs_sub _ _
    _ ≤ (|a + P| + |b + Q|) + |P - Q| := by gcongr; exact abs_sub _ _
    _ ≤ 2 * B + c := by linarith

theorem quad_final {X κ Y a b c : ℝ} (hX : |X| ≤ a) (hκ : |κ| ≤ b) (hY : |Y| ≤ c)
    (hb : 0 ≤ b) : |X - κ * Y| ≤ a + b * c := by
  calc |X - κ * Y| ≤ |X| + |κ * Y| := abs_sub _ _
    _ = |X| + |κ| * |Y| := by rw [abs_mul]
    _ ≤ a + b * c := by gcongr

/-- **Leaf 4A-Q from (U) and the survival bound.** -/
theorem quadResponse_of_univ (hU : GEPUniversality) (hS : SurvivalBound) : QuadResponse := by
  obtain ⟨βU, hβU, hUM⟩ := pwUnivMix_of_univ hU
  have hβU0 : 0 ≤ βU := by linarith
  intro D θ vlo vhi hD hθ hvlo hv
  obtain ⟨σp, σm, hσp, hσm, hquad⟩ := quad_exists_pair (θσ := 1) one_pos
  obtain ⟨ηQ, R, Kb, Kd, Kq, e0, p, hηQ, hR, hR1, hKb, hKd, hKq, he0, hpair⟩ :=
    quad_pair_H hS hUM hD hθ hvlo hv (A := 1 + Real.exp (1 * 3)) (θσ := 1) one_pos
  obtain ⟨Kz, ez, hKz, hez, hderiv⟩ :=
    quad_deriv_zero_bound discInterp p hR hR1 hKb hKd hKq (by linarith : 0 < βU)
  obtain ⟨ηJ, κ₀, KJ', eJ, hηJ, hκ₀, hKJ', heJ, hJb⟩ := pw_outJ_bound hD hθ hvlo hv
  obtain ⟨ηk, hηk, Kk, ek, hkap⟩ := kappaBound D θ vlo vhi hD hθ hvlo hv
  obtain ⟨KA, eA, hKA, heA, hrowA⟩ := pw_rowA hS hβU0 hUM hD hθ hvlo hv
    (1 + Real.exp (1 * 3)) 1 one_pos
  obtain ⟨KJ, eJ', hKJ, heJ', hJC⟩ := pw_lawJC_integrable hD hθ hvlo hv
  have hks := kapSig_nonneg (1 + Real.exp (1 * 3)) 1 one_pos
  set m : ℝ := max 1 (2 / βU) with hm
  set KD : ℝ := 2 * KA * (4 * m ^ 2) + kapSig (1 + Real.exp (1 * 3)) 1 / vlo with hKD
  have hKD0 : 0 ≤ KD := by rw [hKD]; positivity
  set K : ℝ := 2 * (Kz / ηQ + |Kk| * KD) with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  refine ⟨min (min ηQ ηJ) ηk, by positivity, K,
    max (max e0 ez) (max (max eJ ek) (max eA eJ')), ?_⟩
  intro eps heps ν hν M ψ hψ
  have hle1 : ∀ {a : ℝ}, a ≤ max (max e0 ez) (max (max eJ ek) (max eA eJ')) → a ≤ eps :=
    fun h => h.trans heps
  have he0' : e0 ≤ eps := hle1 ((le_max_left _ _).trans (le_max_left _ _))
  have hez' : ez ≤ eps := hle1 ((le_max_right _ _).trans (le_max_left _ _))
  have heJ1 : eJ ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have hek' : ek ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_left _ _).trans
    (le_max_right _ _)))
  have heA' : eA ≤ eps := hle1 ((le_max_left _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heJ2 : eJ' ≤ eps := hle1 ((le_max_right _ _).trans ((le_max_right _ _).trans
    (le_max_right _ _)))
  have heps1 : 1 ≤ eps := he0.trans he0'
  have heps0 : 0 < eps := by linarith only [heps1]
  have hψQ : OutTest ηQ M ψ := hψ.mono_eta ((min_le_left _ _).trans (min_le_left _ _))
  have hψJ : OutTest ηJ M ψ := hψ.mono_eta ((min_le_left _ _).trans (min_le_right _ _))
  have hψk : OutTest ηk M ψ := hψ.mono_eta (min_le_right _ _)
  have hM := hψ.nonneg'
  -- the rate factor
  have hrate : eps ^ (-βU) * (1 + Real.log eps) ^ 2 ≤ 4 * m ^ 2 := by
    have h := pw_log_sq_le_rpow (a := βU) (by linarith) heps1
    rw [← hm] at h
    have e : eps ^ (-βU) * eps ^ βU = 1 := by
      rw [← Real.rpow_add heps0, neg_add_cancel, Real.rpow_zero]
    calc eps ^ (-βU) * (1 + Real.log eps) ^ 2 ≤ eps ^ (-βU) * (4 * m ^ 2 * eps ^ βU) := by
          gcongr
      _ = 4 * m ^ 2 * (eps ^ (-βU) * eps ^ βU) := by ring
      _ = 4 * m ^ 2 := by rw [e, mul_one]
  -- the coarse bound of `J_φ` and the quadratic direction
  obtain ⟨hJm, hJbd⟩ := hJb eps heJ1 ν hν M ψ hψJ
  have hJint : IntegrableOn (outJ eps ν ψ) (Icc (0 : ℝ) 3) :=
    integrableOn_Icc_of_exp hJm hκ₀ hJbd le_rfl
  rw [hquad (outJ eps ν ψ) hJint]
  -- `J_C` and the identification
  obtain ⟨-, -, hJi⟩ := hJC eps heJ2 ν hν
  have hvσp := hσp.lawVar_le one_pos
  have hvσm := hσm.lawVar_le one_pos
  have hvσp0 := hσp.lawVar_nonneg
  have hvσm0 := hσm.lawVar_nonneg
  have hv0 : vlo ≤ lawVar ν := hν.var_ge
  have hvpos : 0 < lawVar ν := hvlo.trans_le hv0
  have hA1 := hrowA eps heA' ν σp hν hσp
  have hA2 := hrowA eps heA' ν σm hν hσm
  -- the `J_C` difference
  have hDj : |((∫ x, lawJC eps ν x ∂(σp : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) /
      lawC eps ν - ((∫ x, lawJC eps ν x ∂(σm : Measure ℝ)) -
        ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) / lawC eps ν| ≤ KD := by
    have hvσ : |(lawVar σp - lawVar ν) / lawVar ν - (lawVar σm - lawVar ν) / lawVar ν| ≤
        kapSig (1 + Real.exp (1 * 3)) 1 / vlo := by
      rw [← sub_div, show lawVar σp - lawVar ν - (lawVar σm - lawVar ν) =
        lawVar σp - lawVar σm by ring, abs_div, abs_of_pos hvpos]
      have h1 : |lawVar σp - lawVar σm| ≤ kapSig (1 + Real.exp (1 * 3)) 1 := by
        rw [abs_le]; constructor <;> linarith only [hvσp, hvσm, hvσp0, hvσm0]
      calc |lawVar σp - lawVar σm| / lawVar ν ≤ |lawVar σp - lawVar σm| / vlo :=
            div_le_div_of_nonneg_left (abs_nonneg _) hvlo hv0
        _ ≤ kapSig (1 + Real.exp (1 * 3)) 1 / vlo := by gcongr
    have hδ : KA * eps ^ (-βU) * (1 + Real.log eps) ^ 2 ≤ KA * (4 * m ^ 2) := by
      rw [mul_assoc]; gcongr
    refine (quad_Dj_bound hA1 hA2 hvσ).trans ?_
    rw [hKD]
    linarith only [hδ]
  -- `κ_φ`
  have hκb : |outKappa eps ν ψ| ≤ M * |Kk| := by
    have h := hkap eps hek' ν hν M ψ hψk
    exact h.trans (by gcongr; exact le_abs_self _)
  -- the case `M = 0` is the limit of `M > 0`
  have hmain : ∀ M' : ℝ, 0 < M' → OutTest ηQ M' ψ → |outKappa eps ν ψ| ≤ M' * |Kk| →
      |2 * ((∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ))| ≤
        M' * K := by
    intro M' hM' hψ' hκ'
    obtain ⟨hIp, hIm, hIν, H, hHd, hHb, hHs, hHeq⟩ :=
      hpair eps he0' ν σp σm hν hσp hσm M' ψ hM' hψ'
    have hH0 := hderiv H eps hez' hHd hHb hHs
    have hIns : |(∫ x, outIns eps ν ψ x ∂(σp : Measure ℝ)) -
        ∫ x, outIns eps ν ψ x ∂(σm : Measure ℝ)| ≤ M' / ηQ * Kz := by
      rw [hHeq]; gcongr
    have hJp := pw_integral_outJ_sub hIp hIν (hJi σp) (hJi ν)
    have hJm' := pw_integral_outJ_sub hIm hIν (hJi σm) (hJi ν)
    have hid : (∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ) =
        ((∫ x, outIns eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outIns eps ν ψ x ∂(σm : Measure ℝ)) -
        outKappa eps ν ψ *
          (((∫ x, lawJC eps ν x ∂(σp : Measure ℝ)) - ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) /
            lawC eps ν - ((∫ x, lawJC eps ν x ∂(σm : Measure ℝ)) -
              ∫ x, lawJC eps ν x ∂(ν : Measure ℝ)) / lawC eps ν) := by
      have e : (∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ) =
          ((∫ x, outJ eps ν ψ x ∂(σp : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(ν : Measure ℝ)) -
          ((∫ x, outJ eps ν ψ x ∂(σm : Measure ℝ)) - ∫ x, outJ eps ν ψ x ∂(ν : Measure ℝ)) := by
        ring
      rw [e, hJp, hJm']
      ring
    rw [hid, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := quad_final hIns hκ' hDj (by positivity)
    refine (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)).trans (le_of_eq ?_)
    rw [hK]
    ring
  rcases hM.eq_or_lt with hM0 | hMpos
  · subst hM0
    rw [zero_mul]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε' : 0 < ε / (K + 1) := by positivity
    have hb := hmain _ hε' (pw_outTest_of_le hψQ le_rfl hε'.le) (by
      rw [zero_mul] at hκb
      exact hκb.trans (by positivity))
    refine hb.trans ?_
    rw [zero_add, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith only [hε]
  · exact hmain M hMpos hψQ hκb

end

end PGM
