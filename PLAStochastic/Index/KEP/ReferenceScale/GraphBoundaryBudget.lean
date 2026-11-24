import PLAStochastic.Index.KEP.ReferenceScale.GraphScalarTransferBounds

/-!
# A common coefficient for the entire exterior pin sum

All first exterior pins preserve the original output and the sum of physical
lengths. Their complete remainders share one polynomial coefficient, including
all further pins already paid by the exterior flux bound.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory Set

def kepGraphUniformPinBudget (C J S A A' : ℝ) : ℝ :=
  8 * S * A * C + 4 * S * ((2 * A + A') * C + A * 8 * C ^ 2 * S ^ 2 * J) +
    16 * S * S * S * A * C ^ 2

theorem kepGraphPinRemainderBudget_le_uniform {C J w S A A' : ℝ}
    (_hC : 0 ≤ C) (hJ : 0 ≤ J) (hw : 0 ≤ w) (hS : 0 ≤ S)
    (hA : 0 ≤ A) (_hA' : 0 ≤ A') (l i r : ℕ)
    (hl : w + (l + 1 : ℕ) ≤ S) (hi : (i + r : ℕ) ≤ S)
    (hir : w + (i + r : ℕ) ≤ S) :
    kepGraphPinRemainderBudget C J w S A A' l i r ≤ kepGraphUniformPinBudget C J S A A' := by
  unfold kepGraphPinRemainderBudget kepGraphUniformPinBudget
  gcongr

theorem kepGraphLeftPinRemainder_uniform_bound {w C J rate D S A A' B : ℝ}
    {pA pA' qA pB pB' qB : ℝ → ℝ → ℝ}
    (HA : KepKilledBridgeBudget (-1) pA pA' qA w C J rate)
    (HB : KepKilledBridgeBudget 1 pB pB' qB w C J rate)
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hA' : 0 ≤ A') (hB : 0 ≤ B)
    (L i r l : ℕ) (hl : l < i) (hSlen : w + (i + r + 1 : ℕ) ≤ S)
    {b : ℝ} (hb : b = 0 ∨ b = w)
    {R R' φ : ℝ → ℝ} (hcR : Continuous R) (hcR' : Continuous R') (hφ : Continuous φ)
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |R s| ≤ A * Real.exp (-rate * (L : ℝ)))
    (hR' : kepLogSlopeNorm R' ≤ A' * Real.exp (-rate * (L : ℝ)))
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput D i r 0 w s u v)| ≤ B) :
    |kepGraphLeftPinRemainder pA qA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ l b| ≤
      (1 + C * w) ^ 2 * B * kepGraphUniformPinBudget C J S A A' *
        Real.exp (-rate * (L + i + r : ℕ)) := by
  have hw := HA.width_nonneg
  have hC : 0 ≤ C := by have := HA.constant_ge_one; linarith
  have hJ : 0 ≤ J := by have := HA.first_ge_one; linarith
  have hbband : b ∈ Icc 0 w := by rcases hb with rfl | rfl <;> constructor <;> first | rfl | exact hw
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hwb : w ∈ Icc 0 w := ⟨hw, le_rfl⟩
  have hS : 0 ≤ S := by have hn := Nat.cast_nonneg (α := ℝ) (i + r + 1); linarith
  have hpin : w + (l + 1 : ℕ) ≤ S := by
    have hh : (l + 1 : ℕ) ≤ (i + r + 1 : ℕ) := by omega
    have hh' : (l + 1 : ℕ) ≤ (i + r + 1 : ℝ) := by exact_mod_cast hh
    push_cast at hh' hSlen ⊢
    linarith
  have htail : w + (i - 1 - l + r : ℕ) ≤ S := by
    have hh : i - 1 - l + r ≤ i + r + 1 := by omega
    have hh' : (i - 1 - l + r : ℕ) ≤ (i + r + 1 : ℝ) := by exact_mod_cast hh
    push_cast at hh' hSlen ⊢
    linarith
  have htail' : (i - 1 - l + r : ℕ) ≤ S := by linarith
  have hn := kepCertificate_exterior_pin_numerators hbband l
  have hPinS := hn.2.1.trans hpin
  have hTestPin : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput (D + kepGapNumerator (-1) (l + 1) 0 b)
        (i - 1 - l) r b w s u v)| ≤ B := by
    intro s hs u hu v hv
    have he := kepGraphOutput_left_pin D i r (l + 1) (by omega) 0 w b s u v
    rw [show i - (l + 1) = i - 1 - l by omega] at he
    rw [he]
    exact hTest s hs u hu v hv
  have hh := kepGraphPinRemainder_killed_bound HA HB HA hD
    (by linarith [hn.1]) hPinS hA hA' hB L l (i - 1 - l) r (Or.inl rfl) hb
    hbband hwb hcR hcR' hφ hR hR' hTestPin
  change |kepGraphLeftPinRemainder pA qA pB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ l b| ≤ _ at hh
  have hlen : L + (l + 1) + (i - 1 - l + r) = L + i + r := by omega
  rw [hlen] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (kepGraphPinRemainderBudget_le_uniform hC hJ hw hS hA hA' l (i - 1 - l) r hpin htail' htail)
    (by positivity)) (Real.exp_pos _).le

theorem kepGraphRightPinRemainder_uniform_bound {w C J rate D S A A' B : ℝ}
    {pA pA' qA pB pB' qB : ℝ → ℝ → ℝ}
    (HA : KepKilledBridgeBudget (-1) pA pA' qA w C J rate)
    (HB : KepKilledBridgeBudget 1 pB pB' qB w C J rate)
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hA' : 0 ≤ A') (hB : 0 ≤ B)
    (L i r l : ℕ) (hl : l < r) (hSlen : w + (i + r + 1 : ℕ) ≤ S)
    {b : ℝ} (hb : b = 0 ∨ b = w)
    {R R' φ : ℝ → ℝ} (hcR : Continuous R) (hcR' : Continuous R') (hφ : Continuous φ)
    (hR : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      |R s| ≤ A * Real.exp (-rate * (L : ℝ)))
    (hR' : kepLogSlopeNorm R' ≤ A' * Real.exp (-rate * (L : ℝ)))
    (hTest : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput D i r 0 w s u v)| ≤ B) :
    |kepGraphRightPinRemainder pA pB qB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ l b| ≤
      (1 + C * w) ^ 2 * B * kepGraphUniformPinBudget C J S A A' *
        Real.exp (-rate * (L + i + r : ℕ)) := by
  have hw := HA.width_nonneg
  have hC : 0 ≤ C := by have := HA.constant_ge_one; linarith
  have hJ : 0 ≤ J := by have := HA.first_ge_one; linarith
  have hbband : b ∈ Icc 0 w := by rcases hb with rfl | rfl <;> constructor <;> first | rfl | exact hw
  have h0 : (0 : ℝ) ∈ Icc 0 w := ⟨le_rfl, hw⟩
  have hS : 0 ≤ S := by have hn := Nat.cast_nonneg (α := ℝ) (i + r + 1); linarith
  have hpin : w + (l + 1 : ℕ) ≤ S := by
    have hh : l + 1 ≤ i + r + 1 := by omega
    have hh' : (l + 1 : ℕ) ≤ (i + r + 1 : ℝ) := by exact_mod_cast hh
    push_cast at hh' hSlen ⊢
    linarith
  have htail : w + (i + (r - 1 - l) : ℕ) ≤ S := by
    have hh : i + (r - 1 - l) ≤ i + r + 1 := by omega
    have hh' : (i + (r - 1 - l) : ℕ) ≤ (i + r + 1 : ℝ) := by exact_mod_cast hh
    push_cast at hh' hSlen ⊢
    linarith
  have htail' : (i + (r - 1 - l) : ℕ) ≤ S := by linarith
  have hn := kepCertificate_exterior_pin_numerators hbband l
  have hPinS := hn.2.2.2.trans hpin
  have hTestPin : ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput (D + kepGapNumerator 1 (l + 1) w b)
        i (r - 1 - l) 0 b s u v)| ≤ B := by
    intro s hs u hu v hv
    have he := kepGraphOutput_right_pin D i r (l + 1) (by omega) 0 w b s u v
    rw [show r - (l + 1) = r - 1 - l by omega] at he
    rw [he]
    exact hTest s hs u hu v hv
  have hh := kepGraphPinRemainder_killed_bound HA HB HB hD
    (by linarith [hn.2.2.1]) hPinS hA hA' hB L l i (r - 1 - l) (Or.inr rfl) hb
    h0 hbband hcR hcR' hφ hR hR' hTestPin
  change |kepGraphRightPinRemainder pA pB qB w (Real.log (1 / 2)) (Real.log 2) D i r 0 w R R' φ l b| ≤ _ at hh
  have hlen : L + (l + 1) + (i + (r - 1 - l)) = L + i + r := by omega
  rw [hlen] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (kepGraphPinRemainderBudget_le_uniform hC hJ hw hS hA hA' l i (r - 1 - l) hpin htail' htail)
    (by positivity)) (Real.exp_pos _).le

theorem kep_abs_neg_add_add_sub (a b c d : ℝ) :
    |-a + b + c - d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (-a) b
  have h2 := abs_add_le (-a + b) c
  have h3 := abs_sub_le (-a + b + c) 0 d
  simp only [abs_neg] at h1
  simp only [sub_zero, zero_sub, abs_neg] at h3
  linarith

theorem kepGraphBoundarySum_uniform_bound {i r : ℕ} {w V : ℝ} {FL FR : ℕ → ℝ → ℝ}
    (hL : ∀ l < i, ∀ b : ℝ, (b = 0 ∨ b = w) → |FL l b| ≤ V)
    (hR : ∀ l < r, ∀ b : ℝ, (b = 0 ∨ b = w) → |FR l b| ≤ V) :
    |kepGraphBoundarySum i r w FL FR| ≤ 2 * (i + r : ℕ) * V := by
  have hs {n : ℕ} {F : ℕ → ℝ} (hF : ∀ l < n, |F l| ≤ V) :
      |∑ l ∈ Finset.range n, F l| ≤ (n : ℝ) * V := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hh := Finset.sum_le_sum (s := Finset.range n)
      (fun l hl => hF l (Finset.mem_range.mp hl))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hLw := hs (fun l hl => hL l hl w (Or.inr rfl))
  have hL0 := hs (fun l hl => hL l hl 0 (Or.inl rfl))
  have hRw := hs (fun l hl => hR l hl w (Or.inr rfl))
  have hR0 := hs (fun l hl => hR l hl 0 (Or.inl rfl))
  unfold kepGraphBoundarySum
  apply (kep_abs_neg_add_add_sub _ _ _ _).trans
  push_cast
  linarith

end

end PGM
