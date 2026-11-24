import PLAStochastic.Swing.Algorithm.Cone

/-! Reflection of the finite native cone. -/
namespace SwingRepair

noncomputable section

set_option maxHeartbeats 400000

theorem nativeConeUpper_neg_eq_neg_lower {ι : Type*} (s : Finset ι) (hne : s.Nonempty)
    (t y : ι → ℝ) (a q ε : ℝ) :
    nativeConeUpper s hne t (fun i => -y i) a (-q) ε =
      -nativeConeLower s hne t y a q ε := by
  unfold nativeConeUpper nativeConeLower slopeUpper slopeLower
  apply le_antisymm
  · obtain ⟨i, hi, hs⟩ := Finset.exists_mem_eq_sup' hne
      (fun i => (y i - q - ε) / (t i - a))
    rw [hs]
    exact le_trans (Finset.inf'_le _ hi) (by ring_nf; exact le_rfl)
  · rw [neg_le]
    obtain ⟨i, hi, hs⟩ := Finset.exists_mem_eq_inf' hne
      (fun i => ((-y i) - -q + ε) / (t i - a))
    rw [hs]
    exact le_trans (by ring_nf; exact le_rfl) (Finset.le_sup' _ hi)

end
end SwingRepair
