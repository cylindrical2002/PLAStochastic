import PLAStochastic.Swing.FrozenCarry.MeanLimit.OmittedRanges

/-! The mean differs from the interior tail sum only by the two short logarithmic
ranges and an order-E continuation term. -/
noncomputable section
open MeasureTheory ProbabilityTheory BrownianAffine Filter Set Finset
open scoped ENNReal NNReal Topology
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℕ → Ω → ℝ}

theorem frozenMeanLimit_remainder_bound
    (hX : ∀ n, Measurable (X n)) (hi : iIndepFun X μ)
    (hG : ∀ n, μ.map (X n) = gaussianReal 0 1)
    (w : ℝ) {δ E : ℝ} (hδ : 0 ≤ δ) (hδ4 : δ ≤ 1/4) (hE : 1 ≤ E) :
    (∫ ω, frozenPrefixLengthReal X w E ω ∂μ) -
        (∑ n ∈ Finset.Ico (frozenInteriorLow δ E) (frozenInteriorHigh δ E),
          μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}) ≤
      E*(2+frozenHarmonicTailConstant*(1+max w 0)*
        (2*δ*Real.log E+5+18/(1-gaussianBlockPass.toReal))) := by
  have := hi.isProbabilityMeasure
  have hEp : 0 < E := by linarith
  let p : ℕ → ℝ := fun n => μ.real {ω | (n : WithTop ℕ) ≤ frozenPrefixLength X w E ω}
  let c : ℕ := ⌈E⌉₊
  let a : ℕ := frozenInteriorLow δ E
  let b : ℕ := frozenInteriorHigh δ E
  let d : ℕ := ⌈E^2⌉₊+1
  let B : ℝ := frozenHarmonicTailConstant*(1+max w 0)
  have hB : 0 ≤ B := by
    dsimp [B]
    have := frozenHarmonicTailConstant_pos
    have := le_max_right w 0
    positivity
  obtain ⟨hc, hca, hab, hbd⟩ := frozenMeanLimit_endpoint_order hδ hδ4 hE
  obtain ⟨hloga, hlogb⟩ := frozenMeanLimit_outer_log_width hδ hδ4 hE
  have hhead : (∑ n ∈ Finset.Ico 1 c, p n) ≤ 2*E := by
    calc
      _ ≤ ∑ _n ∈ Finset.Ico 1 c, (1 : ℝ) :=
        Finset.sum_le_sum (fun _ _ => measureReal_le_one)
      _ ≤ (c : ℝ) := by simp only [sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico]; exact_mod_cast Nat.sub_le c 1
      _ ≤ 2*E := by
        have hh := (Nat.ceil_lt_add_one hEp.le).le
        dsimp [c]
        linarith
  have hout (u v : ℕ) (hu : 1 ≤ u) (huv : u ≤ v) (hvd : v ≤ d) :
      (∑ n ∈ Finset.Ico u v, p n) ≤ B*E*(|Real.log v-Real.log u|+1) := by
    apply sum_of_dominated_range hEp hB hu huv
    intro n hn
    have hn1 : 0 < n := lt_of_lt_of_le (by omega : 0 < u) (mem_Ico.mp hn).1
    have hnN : n ≤ ⌈E^2⌉₊ := by
      have hnv := (mem_Ico.mp hn).2
      dsimp [d] at hvd
      omega
    have hnE : (n : ℝ) ≤ E^2+1 :=
      (by exact_mod_cast hnN : (n : ℝ) ≤ (⌈E^2⌉₊ : ℝ)).trans (frozen_cutoff_le hE)
    simpa only [p, B, div_eq_mul_inv] using frozenPrefixLength_harmonic_tail hX hi hG w hE hn1 hnE
  have hleft : (∑ n ∈ Finset.Ico c a, p n) ≤ B*E*(δ*Real.log E+2) :=
    (hout c a hc hca (hab.trans hbd)).trans
      (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hB hEp.le))
  have hright : (∑ n ∈ Finset.Ico b d, p n) ≤ B*E*(δ*Real.log E+3) :=
    (hout b d ((hc.trans hca).trans hab) hbd le_rfl).trans
      (mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hB hEp.le))
  have hq : 0 < 1-gaussianBlockPass.toReal := sub_pos.mpr frozen_block_ratio_lt_one
  have hn := frozen_cutoff_pos hE
  have hnR : (0 : ℝ) < ⌈E^2⌉₊ := by exact_mod_cast hn
  have htail : 2*(⌈8*E^2⌉₊ : ℝ)*p ⌈E^2⌉₊/(1-gaussianBlockPass.toReal) ≤
      18*(B*E)/(1-gaussianBlockPass.toReal) := by
    have hp := frozenPrefixLength_harmonic_tail hX hi hG w hE hn (frozen_cutoff_le hE)
    calc
      _ ≤ 2*(⌈8*E^2⌉₊ : ℝ)*(B*E/(⌈E^2⌉₊ : ℝ))/(1-gaussianBlockPass.toReal) := by gcongr
      _ = (2*(⌈8*E^2⌉₊ : ℝ)/(⌈E^2⌉₊ : ℝ))*(B*E)/(1-gaussianBlockPass.toReal) := by ring
      _ ≤ _ := by gcongr; exact frozen_block_cutoff_ratio_le hE
  have hsplit := frozenPrefixLength_mean_tail_split hX hi hG w hEp (n := ⌈E^2⌉₊) hn
  have hshift : (∑ j ∈ Finset.range ⌈E^2⌉₊,
      μ.real {ω | j < (frozenPrefixLength X w E ω).untopD 0}) = ∑ n ∈ Finset.Ico 1 d, p n := by
    rw [sum_Ico_eq_sum_range]
    simp only [d, Nat.add_sub_cancel]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [p, Nat.add_comm] using (frozenPrefixLength_tail_measureReal_eq hX hi hG w E j).symm
  rw [hshift] at hsplit
  have hsum : (∑ n ∈ Finset.Ico 1 d, p n) =
      (∑ n ∈ Finset.Ico 1 c, p n)+(∑ n ∈ Finset.Ico c a, p n)+
      (∑ n ∈ Finset.Ico a b, p n)+(∑ n ∈ Finset.Ico b d, p n) := by
    rw [sum_Ico_consecutive _ hc hca, sum_Ico_consecutive _ (hc.trans hca) hab,
      sum_Ico_consecutive _ ((hc.trans hca).trans hab) hbd]
  rw [hsum] at hsplit
  change (∫ ω, frozenPrefixLengthReal X w E ω ∂μ)-(∑ n ∈ Finset.Ico a b, p n) ≤
    E*(2+B*(2*δ*Real.log E+5+18/(1-gaussianBlockPass.toReal)))
  have htotal : (∫ ω, frozenPrefixLengthReal X w E ω ∂μ)-(∑ n ∈ Finset.Ico a b, p n) ≤
      2*E+B*E*(δ*Real.log E+2)+B*E*(δ*Real.log E+3)+18*(B*E)/(1-gaussianBlockPass.toReal) := by
    linarith [hsplit, hhead, hleft, hright, htail]
  convert htotal using 1; ring

end SwingRepair
