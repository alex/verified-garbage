import VerifiedGarbage.Proof.Rc2.AArch64.KeySetup

/-! # Composing the RC2 key-expansion stages -/

namespace VG.Proof.Rc2.AArch64

open VG VG.AArch64 VG.Impl.Rc2.AArch64

def coreRegs : List Reg := [.x4, .x21, .x25, .x26, .x27, .x28, .x30]

structure CoreFrame (s₀ s : State) : Prop where
  reg : ∀ r ∈ coreRegs, s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Frame [⟨s₀.gpr .x21, 128⟩] s₀.mem s.mem

theorem CoreFrame.of_keep {s s' : State} {rs : List Reg} (keep : Keep rs s s')
    (sep : ∀ r ∈ coreRegs, r ∉ rs) : CoreFrame s s' := by
  refine ⟨fun r hr => keep.reg r (sep r hr), keep.rd, keep.wr, ?_⟩
  rw [keep.mem]; exact Frame.refl _ _

theorem CoreFrame.of_key {s s' : State} (h : KeyFrame s s') : CoreFrame s s' := by
  have sep : ∀ r ∈ coreRegs, r ∉ keyTemps := by decide
  exact ⟨fun r hr => h.reg r (sep r hr), h.rd, h.wr, h.mem⟩

theorem CoreFrame.trans {s₀ s₁ s₂ : State} (h₁ : CoreFrame s₀ s₁) (h₂ : CoreFrame s₁ s₂) :
    CoreFrame s₀ s₂ := by
  refine ⟨fun r hr => (h₂.reg r hr).trans (h₁.reg r hr), h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr, ?_⟩
  have frame₂ := h₂.mem
  rw [h₁.reg .x21 (by decide)] at frame₂
  exact h₁.mem.trans frame₂

theorem expandCopyFill_ok (s : State) (t : Nat) (ht : 1 ≤ t) (ht' : t ≤ 128)
    (len : s.gpr .x20 = BitVec.ofNat 64 t) (zero : s.gpr .x23 = 0)
    (readable : ∀ i < t, InRegions (s.rd ++ s.wr) (s.gpr .x19 + BitVec.ofNat 64 i) 1)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (sep : (Region.mk (s.gpr .x19) t).Disjoint ⟨s.gpr .x21, 128⟩) :
    WP isa expandCopyFill s (fun s' => KeyFrame s s' ∧
      BytesPrefix s'.mem (s.gpr .x21) (fill (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t) (128 - t)) 128) := by
  rw [expandCopyFill]
  apply WP.seq
  apply WP.mono (copyLoop_ok s t ht ht' len zero readable writable sep)
  intro s₁ h₁
  have length : (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t).length = t := by
    simp [Spec.Rc2.bytesAt]
  have ptr₁ := h₁.2.1.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [h₁.2.1.wr, ptr₁]; exact writable
  apply WP.mono (maybeFill_ok s₁ (Spec.Rc2.bytesAt s.mem (s.gpr .x19) t)
    (by rw [length]; exact ht) (by rw [length]; exact ht')
    (by rw [length]; exact (h₁.2.1.reg .x20 (by decide)).trans len)
    (by rw [length]; exact h₁.1) writes (by rw [ptr₁, length]; exact h₁.2.2))
  intro s₂ h₂
  exact ⟨h₁.2.1.trans h₂.2.1, by rw [length, ptr₁] at h₂; exact h₂.2.2⟩

theorem reduceDescend_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (len : s.gpr .x24 = BitVec.ofNat 64 ((bits + 7) / 8))
    (index : s.gpr .x23 = BitVec.ofNat 64 (128 - (bits + 7) / 8))
    (mask : (s.gpr .x2).setWidth 8 = BitVec.ofNat 8 (255 % 2 ^ (8 + bits - 8 * ((bits + 7) / 8))))
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa (.seq (.block reduceKey) (.seq (.block [rr .x10 .x23])
      (.ite (.nonzero .x .x10) (.loop (.block descendKey) (.nonzero .x .x10)) (.block [])))) s (fun s' =>
        KeyFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
          (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  have bound : 1 ≤ (bits + 7) / 8 ∧ (bits + 7) / 8 ≤ 128 := by omega
  have writes : InRegions s.wr (s.gpr .x21 + s.gpr .x23) 1 := by
    rw [index]; exact writable _ (by omega)
  have reads : InRegions (s.rd ++ s.wr) (s.gpr .x21 + s.gpr .x23) 1 := by
    obtain ⟨r, hr, hc⟩ := writes
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  apply WP.seq
  apply WP.mono (reduceKey_ok s reads writes)
  intro s₁ h₁
  have keep₁ := h₁.2
  rw [index, initialPrefix _ (by omega), mask] at keep₁
  have frame₁ := (KeyFrame.refl s).step _ (by omega) _ keep₁
  have ptr₁ := keep₁.reg .x21 (by decide)
  have prefix₁ : BytesPrefix s₁.mem (s.gpr .x21) (reduce l bits) 128 := by
    rw [keep₁.mem]
    exact initialPrefix.write (by decide) (by omega) _
  have write₁ : ∀ i < 128, InRegions s₁.wr (s₁.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [keep₁.wr, ptr₁]; exact writable
  apply WP.mono (maybeDescend_ok s₁ (reduce l bits) ((bits + 7) / 8) bound.1 bound.2
    ((keep₁.reg .x24 (by decide)).trans len) (h₁.1.trans index) write₁
    (by rw [ptr₁]; exact prefix₁))
  intro s₂ h₂
  exact ⟨frame₁.trans h₂.1, by rw [ptr₁] at h₂; exact h₂.2⟩

theorem expandReduce_ok (s : State) (l : KeyBytes) (bits : Nat) (hb : 1 ≤ bits) (hb' : bits ≤ 1024)
    (input : s.gpr .x22 = BitVec.ofNat 64 bits)
    (writable : ∀ i < 128, InRegions s.wr (s.gpr .x21 + BitVec.ofNat 64 i) 1)
    (initialPrefix : BytesPrefix s.mem (s.gpr .x21) l 128) :
    WP isa expandReduce s (fun s' => CoreFrame s s' ∧ BytesPrefix s'.mem (s.gpr .x21)
      (descend (reduce l bits) ((bits + 7) / 8) (128 - (bits + 7) / 8)) 128) := by
  rw [expandReduce]
  apply WP.seq
  obtain ⟨s₁, run₁, len₁, index₁, keep₁⟩ := setReduction_ok s bits hb hb' input
  refine WP.of_runBlock ⟨s₁, run₁, ?_⟩
  apply WP.seq
  apply WP.mono (maskCode_ok s₁ bits hb hb' ((keep₁.reg .x22 (by decide)).trans input))
  intro s₂ h₂
  have frame := (CoreFrame.of_keep keep₁ (by decide)).trans (CoreFrame.of_keep h₂.2 (by decide))
  have ptr₂ := frame.reg .x21 (by decide)
  have writes : ∀ i < 128, InRegions s₂.wr (s₂.gpr .x21 + BitVec.ofNat 64 i) 1 := by
    rw [frame.wr, ptr₂]; exact writable
  apply WP.mono (reduceDescend_ok s₂ l bits hb hb'
    ((h₂.2.reg .x24 (by decide)).trans len₁) ((h₂.2.reg .x23 (by decide)).trans index₁) h₂.1 writes
    (by rw [ptr₂, h₂.2.mem, keep₁.mem]; exact initialPrefix))
  intro s₃ h₃
  exact ⟨frame.trans (CoreFrame.of_key h₃.1), by rw [ptr₂] at h₃; exact h₃.2⟩

end VG.Proof.Rc2.AArch64
