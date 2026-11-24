import PLAStochastic.Index.KEP.ReferenceScale.GraphKilledBounds
import PLAStochastic.Index.KEP.ReferenceScale.CertificateCutoffBounds
import PLAStochastic.Index.KEP.ReferenceScale.GraphPins

/-!
# Physical output weights on the original certificate and all exterior pins

Every exterior pin preserves the original physical output. The compact slope
band therefore gives one common output weight for the original graph and every
remainder, including terminal pins. Their first updated numerator is positive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open Set

theorem kepCertificateGraphOutput_bounds {w d s u v : ℝ} {i r n k : ℕ}
    (_hw : 0 ≤ w) (hk : w ≤ (k : ℝ)) (hd : d = (n + 1 : ℕ) - w)
    (hlen : i + r + (n + 1) = k)
    (hs : s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2))
    (hu : u ∈ Icc 0 w) (hv : v ∈ Icc 0 w) :
    0 ≤ kepGraphOutput d i r 0 w s u v ∧
      kepGraphOutput d i r 0 w s u v ≤ 2 * ((k : ℝ) + w) := by
  have he : kepGraphOutput d i r 0 w s u v = Real.exp (-s) * ((k : ℝ) + u - v) := by
    have hl : (i : ℝ) + r + (n + 1 : ℕ) = k := by exact_mod_cast hlen
    dsimp [kepGraphOutput]
    rw [hd]
    congr 1
    linarith
  have ht : 0 ≤ (k : ℝ) + u - v := by linarith [hu.1, hv.2]
  have ht' : (k : ℝ) + u - v ≤ (k : ℝ) + w := by linarith [hu.2, hv.1]
  rw [he]
  refine ⟨mul_nonneg (Real.exp_pos _).le ht, ?_⟩
  exact mul_le_mul (kep_logSlope_exp_bounds hs).2.2.2 ht' ht (by norm_num)

theorem kepCertificateGraphOutput_weight {w d theta C B : ℝ} {i r n k : ℕ}
    (hw : 0 ≤ w) (hk : w ≤ (k : ℝ)) (hd : d = (n + 1 : ℕ) - w)
    (hlen : i + r + (n + 1) = k) (htheta : 0 ≤ theta) (hC : 0 < C)
    {φ : ℝ → ℝ} (hφ : ∀ t, 0 ≤ t → |φ t| ≤ B * Real.exp (theta * t / C)) :
    ∀ s ∈ Ioc (Real.log (1 / 2 : ℝ)) (Real.log 2),
      ∀ u ∈ Icc (0 : ℝ) w, ∀ v ∈ Icc (0 : ℝ) w,
      |φ (kepGraphOutput d i r 0 w s u v)| ≤
        B * Real.exp (2 * theta * ((k : ℝ) + w) / C) := by
  intro s hs u hu v hv
  have ho := kepCertificateGraphOutput_bounds hw hk hd hlen hs hu hv
  have hB : 0 ≤ B := by
    have hh := hφ 0 le_rfl
    simp only [mul_zero, zero_div, Real.exp_zero, mul_one] at hh
    exact (abs_nonneg _).trans hh
  apply (hφ _ ho.1).trans
  apply mul_le_mul_of_nonneg_left _ hB
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ho.2 htheta) hC.le
  convert hh using 1 <;> first | rfl | ring

theorem kepCertificate_exterior_pin_numerators {w b : ℝ} (hb : b ∈ Icc 0 w) (l : ℕ) :
    1 ≤ kepGapNumerator (-1) (l + 1) 0 b ∧
      kepGapNumerator (-1) (l + 1) 0 b ≤ w + (l + 1 : ℕ) ∧
    1 ≤ kepGapNumerator 1 (l + 1) w b ∧
      kepGapNumerator 1 (l + 1) w b ≤ w + (l + 1 : ℕ) := by
  dsimp [kepGapNumerator]
  push_cast
  constructor
  · nlinarith [hb.1, Nat.cast_nonneg (α := ℝ) l]
  constructor
  · linarith [hb.2]
  constructor
  · nlinarith [hb.2, Nat.cast_nonneg (α := ℝ) l]
  · linarith [hb.1]

end

end PGM
