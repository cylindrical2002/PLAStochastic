import PLAStochastic.Index.KRE.Exact.Noise
import PLAStochastic.Index.KRE.Exact.Recursion
import PLAStochastic.Index.KRE.Exact.Window

/-! # Joining the doubling and halving phases -/

namespace PGM
noncomputable section
set_option maxHeartbeats 600000

/-- The two phase bounds determine the exact integer height.  The large
and small curvature-layer hypotheses are discharged for Model K in `Main`. -/
theorem kre_exact_from_layers {eps : ℝ} {p : ℕ → ℝ} {n : ℕ}
    {cN CN Cu C0 c1 c2 c3 KL A q w : ℝ}
    (hF : UniformLayerFacts p n eps 1 cN CN Cu C0 c1 c2 c3 KL)
    (he : 1 ≤ eps) (hn : 2 ≤ n) (hY : 1 ≤ Real.log n)
    (hcN : 0 < cN) (hCN : 0 < CN) (hA : 0 ≤ A)
    (hρ : A ≤ 2 * Real.log eps) (hlo : -A ≤ Real.log cN) (hhi : Real.log CN ≤ A)
    (hq : 1 < q) (hqeq : Real.log n + 3 * Real.log eps = 3 * (2 * Real.log eps) * q)
    (hw : 0 < w) (hw1 : w ≤ 1) (hwin : KREOutside (Real.logb 2 q) w)
    (hm : A * (2 : ℝ) ^ Nat.ceil (Real.logb 2 q) + 4 / 3 * Real.log (Real.log n) ≤
      w / 16 * (2 * Real.log eps) * (2 : ℝ) ^ Nat.ceil (Real.logb 2 q))
    (hsep : 10 * A ≤ w / 16 * (2 * Real.log eps))
    (hρpos : 0 < 2 * Real.log eps)
    (hstep : ∀ ℓ, UCurv eps p n 1 ℓ → 2 ≤ reSize eps p n ℓ →
      2 * Real.log eps + A ≤ Real.log (eps * ((n : ℝ) / reDelta eps p n ℓ)) →
      2 ≤ reSize eps p n (ℓ + 1) ∧
        |Real.log (eps * ((n : ℝ) / reDelta eps p n (ℓ + 1))) -
          Real.log (eps * ((n : ℝ) / reDelta eps p n ℓ)) / 2| ≤ A)
    (hstop : ∀ ℓ, 2 ≤ reSize eps p n ℓ →
      Real.log (eps * ((n : ℝ) / reDelta eps p n ℓ)) ≤ 2 * Real.log eps - A →
      reSize eps p n (ℓ + 1) = 1) :
    reHeight eps p n = kreExactHeight (Real.logb 2 q) := by
  let P := Nat.ceil (Real.logb 2 q)
  let u := (2 : ℝ) ^ P
  let ρ := 2 * Real.log eps
  let η := w / 16
  let V : ℕ → ℝ := fun k => Real.log (eps * ((n : ℝ) / reDelta eps p n (P + k)))
  have hn1 : 1 ≤ n := by omega
  have he0 : 0 < eps := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨hP, hleft, hright, hmid⟩ := kre_window_margins hq hw hw1 hwin
  change 1 ≤ P at hP
  change u / 2 + η * u ≤ q at hleft
  change q + η * u ≤ u at hright
  change q + η * u ≤ 2 * u / 3 ∨ 2 * u / 3 + η * u ≤ q at hmid
  change A * u + 4 / 3 * Real.log (Real.log n) ≤ η * ρ * u at hm
  change 10 * A ≤ η * ρ at hsep
  have hηu : 0 < η * u := by dsimp [η, u]; positivity
  have hηuρ : 0 ≤ η * u * ρ := mul_nonneg hηu.le hρpos.le
  have hAu : 0 ≤ A * u := mul_nonneg hA (by dsimp [u]; positivity)
  have hmlo : (u / 2 - 1) * (ρ + A) ≤
      ρ * (q - 1) - 4 / 3 * Real.log (Real.log n) := by
    have := mul_le_mul_of_nonneg_left hleft hρpos.le
    nlinarith
  have hmhi : ρ * (q - 1) + 4 / 3 * Real.log (Real.log n) ≤
      (u - 1) * (ρ - A) := by
    have := mul_le_mul_of_nonneg_left hright hρpos.le
    nlinarith
  obtain ⟨_, hNP, hCP, hb⟩ := kre_exact_noise_start hF he hn hY hcN hCN hA hρ hlo hhi
    hqeq hmlo hmhi
  have hΔ0 := reDelta_pos (p := p) he hn1 P
  have hs0 : 0 < (n : ℝ) / reDelta eps p n P := div_pos hn0 hΔ0
  have hV : ρ * (3 * q - u) - A * u ≤ V 0 ∧
      V 0 ≤ ρ * (3 * q - u) + A * u := by
    dsimp only [V]
    rw [Nat.add_zero, Real.log_mul he0.ne' hs0.ne',
      Real.log_div hn0.ne' (reDelta_pos he hn1 P).ne']
    change (u - 1) * (ρ - A) ≤ _ ∧ _ ≤ (u - 1) * (ρ + A) at hb
    dsimp [ρ] at *
    constructor <;> nlinarith [hb.1, hb.2]
  have hrun : ∀ J, 1 ≤ J → ρ + 3 * A ≤ V 0 / (2 : ℝ) ^ (J - 1) →
      V 0 / (2 : ℝ) ^ J ≤ ρ - 3 * A → reHeight eps p n = P + J + 1 := by
    intro J hJ hl hu
    apply kre_exact_halving he hn1 hA hρpos hJ hNP hl hu
    · intro k hk hN hlarge
      simpa only [V, Nat.add_assoc] using hstep (P + k)
        (hCP.mono he hn1 (by omega)) hN hlarge
    · intro hN hsmall
      simpa only [V, Nat.add_assoc] using hstop (P + J) hN hsmall
  have hpred : (2 : ℝ) ^ (P - 1) = u / 2 := by
    have h := pow_succ (2 : ℝ) (P - 1)
    rw [Nat.sub_add_cancel hP] at h
    dsimp [u]
    linarith
  have hsepU : 10 * A * u ≤ η * ρ * u :=
    mul_le_mul_of_nonneg_right hsep (by dsimp [u]; positivity)
  have hqp : 0 < q := by linarith
  have hbranchEq := kre_exact_branch hqp
  dsimp only at hbranchEq
  rcases hmid with hmid | hmid
  · have hl : ρ + 3 * A ≤ V 0 / (2 : ℝ) ^ (P - 1) := by
      rw [hpred, le_div_iff₀ (by dsimp [u]; positivity)]
      have := mul_le_mul_of_nonneg_left hleft hρpos.le
      nlinarith [hV.1]
    have hu : V 0 / (2 : ℝ) ^ P ≤ ρ - 3 * A := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hmid hρpos.le
      change V 0 ≤ (ρ - 3 * A) * u
      nlinarith [hV.2]
    have hbranch : ¬ (P : ℝ) - Real.logb 2 q < Real.logb 2 (3 / 2) := by
      rw [hbranchEq]
      dsimp only [P] at *
      change ¬ u * (2 / 3) < q
      nlinarith
    rw [kreExactHeight, if_neg hbranch]
    have h := hrun P hP hl hu
    dsimp [P] at h
    omega
  · have hl : ρ + 3 * A ≤ V 0 / (2 : ℝ) ^ ((P + 1) - 1) := by
      simp only [Nat.add_sub_cancel]
      rw [le_div_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hmid hρpos.le
      change (ρ + 3 * A) * u ≤ V 0
      nlinarith [hV.1]
    have hu : V 0 / (2 : ℝ) ^ (P + 1) ≤ ρ - 3 * A := by
      rw [pow_succ, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hright hρpos.le
      change V 0 ≤ (ρ - 3 * A) * (u * 2)
      nlinarith [hV.2]
    have hbranch : (P : ℝ) - Real.logb 2 q < Real.logb 2 (3 / 2) := by
      rw [hbranchEq]
      change u * (2 / 3) < q
      nlinarith
    rw [kreExactHeight, if_pos hbranch]
    have h := hrun (P + 1) (by omega) hl hu
    dsimp [P] at h
    omega

end
end PGM
