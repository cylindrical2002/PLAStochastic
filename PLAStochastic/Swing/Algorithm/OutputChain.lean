import PLAStochastic.Swing.Algorithm.Rendering

/-! # Indexed geometry of the actual native output chain -/
noncomputable section
namespace SwingRepair
set_option backward.isDefEq.respectTransparency false

variable {t y : ℕ → ℝ} {ε : ℝ} {s last : ℕ} {q : ℝ} {segs : List NativeSegment}

theorem NativeChain.finish_eq_start_of_nil (hc : NativeChain t y ε s q last []) : last = s := by
  cases hc
  rfl

theorem NativeChain.getElem_valid (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k < segs.length) : NativeSegmentValid t y ε segs[k] :=
  hc.valid_segments _ (List.getElem_mem hk)

theorem NativeChain.getElem_bounds (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k < segs.length) :
    s ≤ segs[k].start ∧ segs[k].finish ≤ last ∧ segs[k].start < segs[k].finish :=
  hc.segment_bounds _ (List.getElem_mem hk)

theorem NativeChain.getElem_anchor_error (hc : NativeChain t y ε s q last segs)
    (hq : |q - y s| ≤ ε) {k : ℕ} (hk : k < segs.length) :
    |segs[k].anchorValue - y segs[k].start| ≤ ε :=
  hc.anchor_errors hq _ (List.getElem_mem hk)

theorem NativeChain.getElem_zero (hc : NativeChain t y ε s q last segs)
    (h : 0 < segs.length) : segs[0].start = s ∧ segs[0].anchorValue = q := by
  cases hc with
  | empty => simp at h
  | terminal => exact ⟨rfl, rfl⟩
  | cons => exact ⟨rfl, rfl⟩

theorem NativeChain.getElem_succ (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k + 1 < segs.length) :
    segs[k + 1].start = segs[k].finish ∧
    segs[k + 1].anchorValue = nativeSegmentEndpoint t segs[k] := by
  induction hc generalizing k with
  | empty => simp at hk
  | terminal hv => simp only [List.length_singleton] at hk; omega
  | @cons head last tail hv hr hn ih =>
      cases k with
      | zero =>
          simpa only [List.getElem_cons_succ, List.getElem_cons_zero] using
            hn.getElem_zero (by simp only [List.length_cons] at hk; omega)
      | succ k =>
          simpa only [List.getElem_cons_succ] using ih (by simp only [List.length_cons] at hk; omega)

theorem NativeChain.getElem_reject (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k + 1 < segs.length) :
    ¬ nativePrefixFeasible t y ε segs[k].start (segs[k].finish + 1) segs[k].anchorValue := by
  induction hc generalizing k with
  | empty => simp at hk
  | terminal hv => simp only [List.length_singleton] at hk; omega
  | cons hv hr hn ih =>
      cases k with
      | zero => exact hr
      | succ k => simpa only [List.getElem_cons_succ] using ih (by simp only [List.length_cons] at hk; omega)

theorem NativeChain.getElem_last_finish (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k < segs.length) (hkl : k + 1 = segs.length) : segs[k].finish = last := by
  induction hc generalizing k with
  | empty => simp at hk
  | terminal hv =>
      have : k = 0 := by simp only [List.length_singleton] at hk; omega
      subst k
      rfl
  | @cons head last tail hv hr hn ih =>
      cases k with
      | zero =>
          have hz : tail.length = 0 := by simp only [List.length_cons] at hkl; omega
          have he := List.length_eq_zero_iff.mp hz
          subst tail
          exact hn.finish_eq_start_of_nil.symm
      | succ k =>
          simpa only [List.getElem_cons_succ] using ih
            (by simp only [List.length_cons] at hk; omega)
            (by simp only [List.length_cons] at hkl; omega)

theorem NativeChain.getElem_finish_succ_lt (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k + 1 < segs.length) : segs[k].finish < segs[k + 1].finish := by
  rw [← (hc.getElem_succ hk).1]
  exact (hc.getElem_valid hk).positive

theorem NativeChain.getElem_finish_lt (hc : NativeChain t y ε s q last segs)
    {k l : ℕ} (hkl : k < l) (hl : l < segs.length) : segs[k].finish < segs[l].finish := by
  induction l generalizing k with
  | zero => omega
  | succ l ih =>
      by_cases he : k = l
      · subst k
        exact hc.getElem_finish_succ_lt hl
      · exact (ih (by omega) (by omega)).trans (hc.getElem_finish_succ_lt hl)

theorem NativeChain.getElem_finish_eq_last_iff (hc : NativeChain t y ε s q last segs)
    {k : ℕ} (hk : k < segs.length) : segs[k].finish = last ↔ k + 1 = segs.length := by
  constructor
  · intro he
    by_contra hh
    have hn : k + 1 < segs.length := by omega
    have hs := hc.getElem_finish_succ_lt hn
    have hb := (hc.getElem_bounds hn).2.1
    omega
  · exact hc.getElem_last_finish hk

end SwingRepair
