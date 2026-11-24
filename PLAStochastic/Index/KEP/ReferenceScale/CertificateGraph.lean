import PLAStochastic.Index.KEP.ReferenceScale.CertificateExterior

/-!
# Exact identification of an original certificate with its two-tail graph

The scalar in logarithmic slope is precisely `d χ(exp s) k_L(0,w)`.
The gap test is at the original physical prefix sum, and both zero-length
exteriors are retained. This closes the finite certificate-to-graph bridge.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PGM

noncomputable section

open MeasureTheory ProbabilityTheory Set

theorem kepCertificate_graphOutput {eps : ℝ} {k i j L : ℕ}
    (hL : i + L = j) (hjk : j ≤ k) (s u v : ℝ) :
    kepGraphOutput ((L : ℝ) - 2 * eps) i (k - j) 0 (2 * eps) s u v =
      ((k : ℝ) + u - v) / Real.exp s := by
  have hLr := congrArg (Nat.cast (R := ℝ)) hL
  push_cast at hLr
  unfold kepGraphOutput
  rw [Real.exp_neg, Nat.cast_sub hjk]
  field_simp
  linarith

/-- Exact graph formula for one original iid certificate with a compact
physical slope cutoff. All coarea and exterior-identification inputs are paid. -/
theorem kepCertificateTerm_eq_graph (ν : ProbabilityMeasure ℝ) {f : ℝ → ℝ}
    {D eps : ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hfD : ∀ x, f x ≤ D)
    (hν : (ν : Measure ℝ) = volume.withDensity (fun x => ENNReal.ofReal (f x)))
    (hνpos : (ν : Measure ℝ) (Iic 0) = 0) (heps : 0 ≤ eps)
    {k i j L : ℕ} (hij : i < j) (hL : i + L = j) (hjk : j ≤ k)
    (hd : 0 < (L : ℝ) - 2 * eps) {χ φ : ℝ → ℝ}
    (hχ : Measurable χ) (hφ : Measurable φ)
    (hχb : ∀ a, |χ a| ≤ 1) (hχ0 : ∀ a, a ∉ Icc (1 / 2 : ℝ) 2 → χ a = 0)
    {B : ℝ} (hB : 0 ≤ B) (hφb : ∀ x, |φ x| ≤ B) (n : ℕ) (hn : L = n + 1) :
    kepCertificateTerm eps ν k i j χ φ =
      kepLogGraphIntegral (kepLogStep f (-1)) (kepLogStep f 1) (2 * eps)
        (Real.log (1 / 2)) (Real.log 2) ((L : ℝ) - 2 * eps) i (k - j) 0 (2 * eps)
        (fun s => ((L : ℝ) - 2 * eps) * χ (Real.exp s) *
          kepFixedBridge (kepLogStep f 1) (2 * eps) s n 0 (2 * eps)) φ := by
  let d := (L : ℝ) - 2 * eps
  let Ψ := fun a => χ a * kepCertificateExterior eps ν k i j φ a
  have hΨm : Measurable Ψ := hχ.mul (measurable_kepCertificateExterior eps ν k i j hφ)
  have hΨb (a : ℝ) : |Ψ a| ≤ B := by
    dsimp only [Ψ]
    rw [abs_mul]
    exact (mul_le_mul (hχb a) (abs_kepCertificateExterior_le heps ν k i j hB hφb a)
      (abs_nonneg _) zero_le_one).trans_eq (one_mul B)
  have hΨ0 (a : ℝ) (ha : a ∉ Icc (1 / 2 : ℝ) 2) : Ψ a = 0 := by
    simp only [Ψ, hχ0 a ha, zero_mul]
  rw [kepCertificateTerm_eq_middle heps ν hνpos hij hL hjk hχ hφ hχb hχ0 hB hφb n hn,
    integral_kepCertificateMiddle_eq_logBridge ν hf hf0 hfD hν heps hd n
      (by rw [← hn]) hΨm hΨb hΨ0]
  let G := fun s => (d * χ (Real.exp s) *
      kepFixedBridge (kepLogStep f 1) (2 * eps) s n 0 (2 * eps)) *
    kepTailPairTest (kepLogStep f (-1)) (kepLogStep f 1) (2 * eps) s i (k - j) 0 (2 * eps)
      (fun u v => φ (kepGraphOutput d i (k - j) 0 (2 * eps) s u v))
  have he : (∫ s, d * Ψ (Real.exp s) *
      kepFixedBridge (kepLogStep f 1) (2 * eps) s n 0 (2 * eps)) = ∫ s, G s := by
    apply integral_congr_ae
    exact ae_of_all _ fun s => by
      dsimp only [G, Ψ]
      by_cases ha : Real.exp s ∈ Icc (1 / 2 : ℝ) 2
      · rw [kepCertificateExterior_eq_tailPair ν hf hf0 hfD hν heps k i j hφ hB hφb ha,
          Real.log_exp]
        have htest : (fun u v => φ (((k : ℝ) + u - v) / Real.exp s)) =
            fun u v => φ (kepGraphOutput d i (k - j) 0 (2 * eps) s u v) := by
          funext u v
          rw [kepCertificate_graphOutput hL hjk]
        rw [htest]
        ring
      · rw [hχ0 _ ha]
        ring
  change (∫ s, d * Ψ (Real.exp s) *
    kepFixedBridge (kepLogStep f 1) (2 * eps) s n 0 (2 * eps)) = _
  rw [he]
  have hs : ∀ s, s ∉ Icc (Real.log (1 / 2)) (Real.log 2) → G s = 0 := by
    intro s hs
    have ha : Real.exp s ∉ Icc (1 / 2 : ℝ) 2 := by
      intro ha
      apply hs
      have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) ha.1
      have hu := Real.log_le_log (Real.exp_pos s) ha.2
      rw [Real.log_exp] at hl hu
      exact ⟨hl, hu⟩
    simp only [G, hχ0 _ ha, mul_zero, zero_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs, integral_Icc_eq_integral_Ioc]
  rfl

end

end PGM
