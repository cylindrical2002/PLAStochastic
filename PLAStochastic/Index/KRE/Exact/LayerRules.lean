import PLAStochastic.Index.KRE.Exact.Curvature
import PLAStochastic.Index.KRE.Exact.Noise

/-! # Large and small layers on the canonical Model K good event -/

namespace PGM
noncomputable section

theorem kre_curv_delta_sq {eps : ℝ} {p : ℕ → ℝ} {n ℓ : ℕ}
    (he : 1 ≤ eps) (hn : 1 ≤ n) (hY : 1 ≤ Real.log n)
    (hgrowth : 3 * Real.log eps + 2 * Real.log (Real.log n) ≤ Real.log n)
    (hcurv : UCurv eps p n 1 ℓ) : Real.log n ^ 2 ≤ (reDelta eps p n ℓ : ℝ) := by
  have he0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hY0 : 0 < Real.log n := by linarith
  have hΔ := reDelta_pos (p := p) he hn ℓ
  unfold UCurv at hcurv
  rw [kre_effDelta_one hn, one_mul] at hcurv
  have hl := Real.log_le_log (by positivity) hcurv
  rw [Real.log_mul hn0.ne' (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  apply (Real.log_le_log_iff (by positivity) hΔ).mp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

theorem kre_exact_layer_rules {d : DensityClassParams} {n : ℕ} {eps : ℝ}
    {f : ℝ → ℝ} {ω : ℕ → ℝ} {cN CN Cu C0 c1 c2 c3 KL c G C A : ℝ}
    (hf : d.Mem 1 f) (hd : UnifCond d n eps)
    (hω : ω ∉ kreBad expCoord n eps (tRE n) (jK n))
    (hF : UniformLayerFacts (renyiKeys f n ω) n eps 1 cN CN Cu C0 c1 c2 c3 KL)
    (hbig : 102400 * Real.log n ≤ (n : ℝ))
    (hgrowth : 3 * Real.log eps + 2 * Real.log (Real.log n) ≤ Real.log n)
    (hc : 0 < c) (h1 : c ≤ c1) (h2 : c ≤ c2) (h3 : c ≤ c3)
    (hCu : 0 < Cu) (hC0 : 0 ≤ C0) (hG : 2 * (Cu + C0) ≤ G)
    (hC : 1 ≤ C) (hCc : 16 ≤ c ^ 2 * C) (hCK : KL ≤ C)
    (hAl : -A ≤ Real.log (c / 2)) (hAu : Real.log G ≤ A)
    (hAC : Real.log C ≤ A) (hAB : Real.log (1 + 24 * unifKappa d) ≤ A) :
    (∀ ℓ, UCurv eps (renyiKeys f n ω) n 1 ℓ → 2 ≤ reSize eps (renyiKeys f n ω) n ℓ →
      2 * Real.log eps + A ≤ Real.log (eps * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ)) →
      2 ≤ reSize eps (renyiKeys f n ω) n (ℓ + 1) ∧
        |Real.log (eps * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n (ℓ + 1))) -
          Real.log (eps * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ)) / 2| ≤ A) ∧
    (∀ ℓ, 2 ≤ reSize eps (renyiKeys f n ω) n ℓ →
      Real.log (eps * ((n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ)) ≤ 2 * Real.log eps - A →
      reSize eps (renyiKeys f n ω) n (ℓ + 1) = 1) := by
  have he := hd.one_le_eps
  have hn := hd.one_le
  have hY := hd.one_le_log
  have he0 : 0 < eps := by linarith
  have hCp : 0 < C := by linarith
  have hκ := unifKappa_pos d
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  constructor
  · intro ℓ hcurv hN hlarge
    have hs0 : 0 < (n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ :=
      div_pos hn0 (reDelta_pos he hn ℓ)
    have hs : C * eps ≤ (n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ := by
      apply (Real.log_le_log_iff (by positivity) hs0).mp
      rw [Real.log_mul (by positivity) he0.ne']
      rw [Real.log_mul he0.ne' hs0.ne'] at hlarge
      linarith
    obtain ⟨hN', hl, hu⟩ := kre_exact_curvature_step hF he hn hY hc h1 h2 h3 hCu hC0 hG
      hC hCc hCK hN hcurv (kre_curv_delta_sq he hn hY hgrowth hcurv) hs
    exact ⟨hN', abs_le.mpr ⟨hAl.trans hl, hu.trans hAu⟩⟩
  · intro ℓ hN hsmall
    have hs0 : 0 < (n : ℝ) / reDelta eps (renyiKeys f n ω) n ℓ :=
      div_pos hn0 (reDelta_pos he hn ℓ)
    apply kre_exact_small_layer hf hd hω hbig hN
    apply (Real.log_le_log_iff (by positivity) he0).mp
    rw [Real.log_mul (by positivity) hs0.ne']
    rw [Real.log_mul he0.ne' hs0.ne'] at hsmall
    linarith

end
end PGM
