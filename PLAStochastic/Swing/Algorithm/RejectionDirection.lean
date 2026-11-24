import PLAStochastic.Swing.Algorithm.Cone

/-!
# The native rejection-direction lemma

These inequalities quantify over the actual finite relative samples, including
the rejected observation. A small displacement and a nonnegative inherited
recording error exclude lower rejection; reflection gives the upper version.
-/

namespace SwingRepair

theorem native_lower_lt_new_upper {si sj xi xj η ε d : ℝ}
    (hsi : 0 < si) (hs : si ≤ sj) (hη : 0 ≤ η)
    (hxi : |xi| ≤ d) (hxj : |xj| ≤ d) (hd : d < ε) :
    slopeLower si xi 0 η ε < slopeUpper sj xj 0 η ε := by
  have hsj := hsi.trans_le hs
  have hi := abs_le.mp hxi
  have hj := abs_le.mp hxj
  have hn : xi - η - ε < 0 := by linarith
  have hgap : xi - η - ε < xj - η + ε := by linarith
  unfold slopeLower slopeUpper
  simp only [sub_zero]
  rw [div_lt_div_iff₀ hsi hsj]
  exact (mul_le_mul_of_nonpos_left hs hn.le).trans_lt (mul_lt_mul_of_pos_right hgap hsi)

theorem native_new_lower_lt_upper {si sj xi xj η ε d : ℝ}
    (hsi : 0 < si) (hs : si ≤ sj) (hη : η ≤ 0)
    (hxi : |xi| ≤ d) (hxj : |xj| ≤ d) (hd : d < ε) :
    slopeLower sj xj 0 η ε < slopeUpper si xi 0 η ε := by
  have h := native_lower_lt_new_upper hsi hs (neg_nonneg.mpr hη)
    (by simpa only [abs_neg] using hxi : |-xi| ≤ d)
    (by simpa only [abs_neg] using hxj : |-xj| ≤ d) hd
  unfold slopeLower slopeUpper at *
  simp only [sub_zero] at *
  have hl : (-xi - -η - ε) / si = -((xi - η + ε) / si) := by ring
  have hu : (-xj - -η + ε) / sj = -((xj - η - ε) / sj) := by ring
  rw [hl, hu] at h
  linarith

/-- Lemma A.2, nonnegative inherited error: the new upper bound lies above the actual old lower bound. -/
theorem native_no_lower_rejection {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (s x : ι → ℝ) {sj xj η ε d : ℝ}
    (hs : ∀ i ∈ samples, 0 < s i ∧ s i ≤ sj) (hη : 0 ≤ η)
    (hx : ∀ i ∈ samples, |x i| ≤ d) (hxj : |xj| ≤ d) (hd : d < ε) :
    nativeConeLower samples hne s x 0 η ε < slopeUpper sj xj 0 η ε := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hne (fun i => slopeLower (s i) (x i) 0 η ε)
  unfold nativeConeLower
  rw [heq]
  exact native_lower_lt_new_upper (hs i hi).1 (hs i hi).2 hη (hx i hi) hxj hd

/-- Lemma A.2, nonpositive inherited error: the new lower bound lies below the actual old upper bound. -/
theorem native_no_upper_rejection {ι : Type*} (samples : Finset ι) (hne : samples.Nonempty)
    (s x : ι → ℝ) {sj xj η ε d : ℝ}
    (hs : ∀ i ∈ samples, 0 < s i ∧ s i ≤ sj) (hη : η ≤ 0)
    (hx : ∀ i ∈ samples, |x i| ≤ d) (hxj : |xj| ≤ d) (hd : d < ε) :
    slopeLower sj xj 0 η ε < nativeConeUpper samples hne s x 0 η ε := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hne (fun i => slopeUpper (s i) (x i) 0 η ε)
  unfold nativeConeUpper
  rw [heq]
  exact native_new_lower_lt_upper (hs i hi).1 (hs i hi).2 hη (hx i hi) hxj hd

/-- The paper's literal small-displacement hypothesis needs no supplied common modulus bound. -/
theorem native_no_lower_rejection_of_small_displacements {ι : Type*}
    (samples : Finset ι) (hne : samples.Nonempty) (s x : ι → ℝ) {sj xj η ε : ℝ}
    (hs : ∀ i ∈ samples, 0 < s i ∧ s i ≤ sj) (hη : 0 ≤ η)
    (hx : ∀ i ∈ samples, |x i| < ε) (hxj : |xj| < ε) :
    nativeConeLower samples hne s x 0 η ε < slopeUpper sj xj 0 η ε := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' hne (fun i => slopeLower (s i) (x i) 0 η ε)
  unfold nativeConeLower
  rw [heq]
  exact native_lower_lt_new_upper (hs i hi).1 (hs i hi).2 hη
    (le_max_left |x i| |xj|) (le_max_right |x i| |xj|) (max_lt_iff.mpr ⟨hx i hi, hxj⟩)

theorem native_no_upper_rejection_of_small_displacements {ι : Type*}
    (samples : Finset ι) (hne : samples.Nonempty) (s x : ι → ℝ) {sj xj η ε : ℝ}
    (hs : ∀ i ∈ samples, 0 < s i ∧ s i ≤ sj) (hη : η ≤ 0)
    (hx : ∀ i ∈ samples, |x i| < ε) (hxj : |xj| < ε) :
    slopeLower sj xj 0 η ε < nativeConeUpper samples hne s x 0 η ε := by
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf' hne (fun i => slopeUpper (s i) (x i) 0 η ε)
  unfold nativeConeUpper
  rw [heq]
  exact native_new_lower_lt_upper (hs i hi).1 (hs i hi).2 hη
    (le_max_left |x i| |xj|) (le_max_right |x i| |xj|) (max_lt_iff.mpr ⟨hx i hi, hxj⟩)

end SwingRepair
