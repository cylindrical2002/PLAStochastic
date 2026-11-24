import PLAStochastic.ForMathlib.Analysis.Complex.QuadraticNewtonJets

/-! # Genuine quadratic Newton residual and norm budgets -/

noncomputable section
open Complex
namespace PGM

theorem quadraticNewtonStep_sub_base {P g : ℂ → ℂ} {v lam z r gap b : ℂ}
    (hgap : gap = lam + v * r) (hne : gap ≠ 0)
    (hbase : r ^ 2 * (v / 2) + lam * r = z) :
    quadraticNewtonStep P g lam z gap b - r =
      (-(v / 2) * (g b - r) ^ 2 - (g b) ^ 2 * (P (b * g b) - v / 2) + b * lam * z) / gap := by
  unfold quadraticNewtonStep
  field_simp [hne]
  rw [hgap, ← hbase]
  ring

/-- The first-order residual at the base root is separated from the quadratic error.
No probability-law or realization assumption is used. -/
theorem quadraticNewtonStep_sub_base_norm_le {P g : ℂ → ℂ} {v lam z r gap b : ℂ}
    (hgap : gap = lam + v * r) (hne : gap ≠ 0)
    (hbase : r ^ 2 * (v / 2) + lam * r = z) :
    ‖quadraticNewtonStep P g lam z gap b - r‖ ≤
      (‖v‖ / 2 * ‖g b - r‖ ^ 2 + ‖g b‖ ^ 2 * ‖P (b * g b) - v / 2‖ +
        ‖b‖ * ‖lam‖ * ‖z‖) / ‖gap‖ := by
  rw [quadraticNewtonStep_sub_base hgap hne hbase, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  have h := (norm_add_le (-(v / 2) * (g b - r) ^ 2 -
    (g b) ^ 2 * (P (b * g b) - v / 2)) (b * lam * z)).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
  simpa only [norm_mul, norm_neg, norm_div, norm_ofNat, norm_pow] using h

theorem quadraticNewtonStep_scaled_error_le {P g : ℂ → ℂ} {v lam z r gap b : ℂ}
    {A c L K δ F : ℝ} (hA : 0 < A) (hc : 0 < c) (hL : 0 ≤ L) (hK : 0 ≤ K)
    (hδ : 0 ≤ δ) (hF : 0 < F) (hsmall : ‖b‖ * F ≤ δ) (hKA : K * δ ≤ A)
    (hstable : (‖v‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) / c ≤ K)
    (hr : ‖r‖ ≤ A * F) (hl : ‖lam‖ ≤ F) (hz : ‖z‖ ≤ F ^ 2)
    (hgap : gap = lam + v * r) (hgapnorm : c * F ≤ ‖gap‖)
    (hbase : r ^ 2 * (v / 2) + lam * r = z)
    (hg : ‖g b - r‖ ≤ K * ‖b‖ * F ^ 2)
    (hP : ‖P (b * g b) - v / 2‖ ≤ L * ‖b‖ * ‖g b‖) :
    ‖quadraticNewtonStep P g lam z gap b - r‖ ≤ K * ‖b‖ * F ^ 2 := by
  have hne : gap ≠ 0 := norm_pos_iff.mp ((mul_pos hc hF).trans_le hgapnorm)
  have herror : K * ‖b‖ * F ^ 2 ≤ A * F := by
    calc
      _ = K * (‖b‖ * F) * F := by ring
      _ ≤ K * δ * F := by gcongr
      _ ≤ A * F := mul_le_mul_of_nonneg_right hKA hF.le
  have hG : ‖g b‖ ≤ 2 * A * F := by
    have ht := norm_add_le (g b - r) r
    rw [sub_add_cancel] at ht
    exact ht.trans ((add_le_add (hg.trans herror) hr).trans_eq (by ring))
  have hE : ‖v‖ / 2 * ‖g b - r‖ ^ 2 ≤ ‖v‖ / 2 * K ^ 2 * δ * ‖b‖ * F ^ 3 := by
    calc
      _ ≤ ‖v‖ / 2 * (K * ‖b‖ * F ^ 2) ^ 2 := by gcongr
      _ = (‖v‖ / 2 * K ^ 2) * (‖b‖ * F) * (‖b‖ * F ^ 3) := by ring
      _ ≤ (‖v‖ / 2 * K ^ 2) * δ * (‖b‖ * F ^ 3) := by gcongr
      _ = _ := by ring
  have hT : ‖g b‖ ^ 2 * ‖P (b * g b) - v / 2‖ ≤ 8 * A ^ 3 * L * ‖b‖ * F ^ 3 := by
    have hP' : ‖P (b * g b) - v / 2‖ ≤ L * ‖b‖ * (2 * A * F) :=
      hP.trans (mul_le_mul_of_nonneg_left hG (by positivity))
    calc
      _ ≤ (2 * A * F) ^ 2 * (L * ‖b‖ * (2 * A * F)) := by gcongr
      _ = _ := by ring
  have hZ : ‖b‖ * ‖lam‖ * ‖z‖ ≤ ‖b‖ * F ^ 3 := by
    calc
      _ ≤ ‖b‖ * F * F ^ 2 := by gcongr
      _ = _ := by ring
  have hnum := add_le_add (add_le_add hE hT) hZ
  have hnum' : ‖v‖ / 2 * ‖g b - r‖ ^ 2 + ‖g b‖ ^ 2 * ‖P (b * g b) - v / 2‖ +
      ‖b‖ * ‖lam‖ * ‖z‖ ≤
        (‖v‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) * ‖b‖ * F ^ 3 :=
    hnum.trans_eq (by ring)
  calc
    _ ≤ _ := quadraticNewtonStep_sub_base_norm_le hgap hne hbase
    _ ≤ ((‖v‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) * ‖b‖ * F ^ 3) / ‖gap‖ :=
      div_le_div_of_nonneg_right hnum' (norm_nonneg _)
    _ ≤ ((‖v‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) * ‖b‖ * F ^ 3) / (c * F) :=
      div_le_div_of_nonneg_left (by positivity) (mul_pos hc hF) hgapnorm
    _ = ((‖v‖ / 2 * K ^ 2 * δ + 8 * A ^ 3 * L + 1) / c) * ‖b‖ * F ^ 2 := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hstable (norm_nonneg _)) (by positivity)

end PGM
