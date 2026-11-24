import PLAStochastic.Index.KEP.ReferenceScale.ActualFiniteGraphSecondBudget

/-!
# One polynomial for every coefficient in the finite second graph

The coefficient is linear in the first input budget. In particular it does not
square that budget while absorbing the boundary pins. The separate original
second-kernel coefficient has degree three in the total size.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

theorem kep_unit_monomial_le {C S J : ℝ} (hC : 1 ≤ C) (hS : 1 ≤ S)
    (hJ : 1 ≤ J) {a b e p q : ℕ} (ha : a ≤ p) (hb : b ≤ q) (he : e ≤ 1) :
    C ^ a * S ^ b * J ^ e ≤ C ^ p * S ^ q * J := by
  have hCa := pow_le_pow_right₀ hC ha
  have hSb := pow_le_pow_right₀ hS hb
  have hJe : J ^ e ≤ J := by simpa only [pow_one] using pow_le_pow_right₀ hJ he
  gcongr

theorem kepBridgeSecondRemainderBudget_polynomial {C J w S : ℝ} (hC : 1 ≤ C)
    (hJ : 1 ≤ J) (hw : 0 ≤ w) (hS : 1 ≤ S) (n : ℕ)
    (hn : (n : ℝ) ≤ S) (hlen : w + (n + 1 : ℕ) ≤ S) :
    kepBridgeSecondRemainderBudget C J w n ≤ 43 * C ^ 3 * S ^ 4 * J := by
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h1 := kep_unit_monomial_le hC hS hJ (a := 1) (b := 0) (e := 0)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 := kep_unit_monomial_le hC hS hJ (a := 1) (b := 1) (e := 1)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  have h3 := kep_unit_monomial_le hC hS hJ (a := 2) (b := 2) (e := 0)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  have h4 := kep_unit_monomial_le hC hS hJ (a := 2) (b := 3) (e := 1)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at h1 h2 h3 h4
  calc
    _ ≤ 2 * C + 3 * S * C * J + 4 * S * S * C ^ 2 +
        2 * S * S ^ 2 * C ^ 2 * J + 32 * S * S ^ 3 * C ^ 3 * J := by
      dsimp only [kepBridgeSecondRemainderBudget]
      gcongr
    _ ≤ _ := by nlinarith only [h1, h2, h3, h4]

theorem kepCertificateScalarFirstBudget_polynomial {C J w S d A : ℝ}
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hw : 0 ≤ w) (hS : 1 ≤ S)
    (_hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A) (n : ℕ)
    (hlen : w + (n + 1 : ℕ) ≤ S) :
    d * A * (2 * C + 8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J) ≤
      10 * A * C ^ 2 * S ^ 3 * J := by
  have h1 := kep_unit_monomial_le hC hS hJ (a := 1) (b := 0) (e := 0)
    (p := 2) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at h1
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hS0 : 0 ≤ S := by linarith
  calc
    _ ≤ S * A * (2 * C + 8 * C ^ 2 * S ^ 2 * J) := by gcongr
    _ ≤ S * A * (10 * C ^ 2 * S ^ 2 * J) := by
      gcongr
      nlinarith only [h1]
    _ = _ := by ring

theorem kepCertificateScalarSecondBudget_polynomial {C J w S d A : ℝ}
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hw : 0 ≤ w) (hS : 1 ≤ S)
    (_hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A) (n : ℕ)
    (hn : (n : ℝ) ≤ S) (hlen : w + (n + 1 : ℕ) ≤ S) :
    d * A * (2 * C + 16 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J +
      kepBridgeSecondRemainderBudget C J w n) ≤ 61 * A * C ^ 3 * S ^ 5 * J := by
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h1 := kep_unit_monomial_le hC hS hJ (a := 1) (b := 0) (e := 0)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  have h2 := kep_unit_monomial_le hC hS hJ (a := 2) (b := 2) (e := 1)
    (p := 3) (q := 4) (by norm_num) (by norm_num) (by norm_num)
  simp only [pow_zero, pow_one, mul_one] at h1 h2
  have hrem := kepBridgeSecondRemainderBudget_polynomial hC hJ hw hS n hn hlen
  have hrem0 : 0 ≤ kepBridgeSecondRemainderBudget C J w n := by
    unfold kepBridgeSecondRemainderBudget
    positivity
  calc
    _ ≤ S * A * (2 * C + 16 * C ^ 2 * S ^ 2 * J + 43 * C ^ 3 * S ^ 4 * J) := by
      gcongr
    _ ≤ S * A * (61 * C ^ 3 * S ^ 4 * J) := by
      gcongr
      nlinarith only [h1, h2]
    _ = _ := by ring

theorem kepGraphSecondBudget_polynomial {C J w S d A : ℝ}
    (hC : 1 ≤ C) (hJ : 1 ≤ J) (hw : 0 ≤ w) (hS : 1 ≤ S)
    (hd : 0 ≤ d) (hdS : d ≤ S) (hA : 0 ≤ A) (n i r : ℕ)
    (hn : (n : ℝ) ≤ S) (hlen : w + (n + 1 : ℕ) ≤ S)
    (hext : (i + r : ℕ) ≤ S) (hwe : w + (i + r : ℕ) ≤ S) :
    kepGraphSecondBudget C J w S (d * A * C)
      (d * A * (2 * C + 8 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J))
      (d * A * (2 * C + 16 * C ^ 2 * (w + (n + 1 : ℕ)) ^ 2 * J +
        kepBridgeSecondRemainderBudget C J w n)) i r ≤ 684 * A * C ^ 3 * S ^ 5 * J := by
  have hC0 : 0 ≤ C := by linarith
  have hJ0 : 0 ≤ J := by linarith
  have hS0 : 0 ≤ S := by linarith
  have h0 : d * A * C ≤ A * C * S := by nlinarith only [hdS, mul_nonneg hA hC0]
  have h1 := kepCertificateScalarFirstBudget_polynomial hC hJ hw hS hd hdS hA n hlen
  have h2 := kepCertificateScalarSecondBudget_polynomial hC hJ hw hS hd hdS hA n hn hlen
  have hm1 := mul_le_mul_of_nonneg_left (kep_unit_monomial_le hC hS hJ
    (a := 1) (b := 1) (e := 0) (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num)) hA
  have hm2 := mul_le_mul_of_nonneg_left (kep_unit_monomial_le hC hS hJ
    (a := 2) (b := 3) (e := 1) (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num)) hA
  have hm3 := mul_le_mul_of_nonneg_left (kep_unit_monomial_le hC hS hJ
    (a := 2) (b := 3) (e := 0) (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num)) hA
  have hm4 := mul_le_mul_of_nonneg_left (kep_unit_monomial_le hC hS hJ
    (a := 3) (b := 5) (e := 0) (p := 3) (q := 5)
    (by norm_num) (by norm_num) (by norm_num)) hA
  simp only [pow_zero, pow_one, mul_one] at hm1 hm2 hm3 hm4
  calc
    _ ≤ 4 * (4 * (A * C * S) + 3 * (10 * A * C ^ 2 * S ^ 3 * J) +
        61 * A * C ^ 3 * S ^ 5 * J) +
        8 * S * S * C * (2 * (A * C * S) + 10 * A * C ^ 2 * S ^ 3 * J) +
        2 * S * (8 * S * (A * C * S) * C +
          4 * S * ((2 * (A * C * S) + 10 * A * C ^ 2 * S ^ 3 * J) * C +
            (A * C * S) * 8 * C ^ 2 * S ^ 2 * J) +
          16 * S * S * S * (A * C * S) * C ^ 2) := by
      unfold kepGraphSecondBudget kepGraphUniformPinBudget
      gcongr
    _ ≤ _ := by nlinarith only [hm1, hm2, hm3, hm4]

end

end PGM
