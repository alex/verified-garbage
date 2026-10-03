import VerifiedGarbage.Proof.Rc4.X86.Lookup

/-! # RC4 on x86 (32-bit): our caller's registers, saved in `scratch` -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The memory once `save` has stored `b`, `si`, `di` and `bp` at `S`. -/
def savedMem (m : Mem) (S : BitVec 32) (b si di bp : BitVec 32) : Mem :=
  (((m.writeW (S.setWidth 64 + BitVec.ofNat 64 0) b).writeW (S.setWidth 64 + BitVec.ofNat 64 4) si).writeW
    (S.setWidth 64 + BitVec.ofNat 64 8) di).writeW (S.setWidth 64 + BitVec.ofNat 64 12) bp

/-- Our caller's `ebx`, `esi`, `edi` and `ebp` (of `s₀`) are at `S` in `m`. -/
def Saved (m : Mem) (S : BitVec 32) (s₀ : State) : Prop :=
  m.readW (S.setWidth 64 + BitVec.ofNat 64 0) 32 = s₀.gpr .ebx ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 4) 32 = s₀.gpr .esi ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 8) 32 = s₀.gpr .edi ∧
    m.readW (S.setWidth 64 + BitVec.ofNat 64 12) 32 = s₀.gpr .ebp

theorem save_addr {S : BitVec 32} (hS : S.toNat + 64 ≤ 2 ^ 32) {d : Nat} (hd : d < 64) :
    addr S d = S.setWidth 64 + BitVec.ofNat 64 d := addr_of_fit (by omega)

theorem save_ok (s : State) (S : BitVec 32) (hS : S.toNat + 64 ≤ 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = S)
    (hw : InRegions s.wr (S.setWidth 64) 64) :
    WP isa (.block save) s fun t =>
      t.mem = savedMem s.mem S (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp) ∧
      Keep [.ecx] s t := by
  have w (d : Nat) (hd : d + 4 ≤ 64) : InRegions s.wr (addr S d) 4 := by
    rw [save_addr hS (by omega)]
    exact region_offset _ _ _ _ _ (by omega) hd hw
  have w0 := w 0 (by decide)
  have w4 := w 4 (by decide)
  have w8 := w 8 (by decide)
  have w12 := w 12 (by decide)
  rw [save_addr hS (by decide)] at w0 w4 w8 w12
  refine WP.mono (WP.keep (Q := fun t =>
      t.mem = savedMem s.mem S (s.gpr .ebx) (s.gpr .esi) (s.gpr .edi) (s.gpr .ebp)) [.ecx] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h, hk⟩
  unfold save
  rrun [ha, hv, save_addr hS, w0, w4, w8, w12]
  rfl

theorem saved_sep (S : BitVec 32) {d e : Nat} (h : d + 4 ≤ e ∨ e + 4 ≤ d) (hd : d < 64)
    (he : e < 64) :
    Mem.Sep (S.setWidth 64 + BitVec.ofNat 64 d) (32 / 8) (S.setWidth 64 + BitVec.ofNat 64 e)
      (32 / 8) :=
  Offset.sep _ h (by omega) (by omega)

theorem saved_savedMem (m : Mem) (S : BitVec 32) (s₀ : State) :
    Saved (savedMem m S (s₀.gpr .ebx) (s₀.gpr .esi) (s₀.gpr .edi) (s₀.gpr .ebp)) S s₀ := by
  unfold savedMem Saved
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 12) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 8) (by omega) (by omega)
      (by omega)) (by decide), Mem.readW_writeW_sep (saved_sep S (d := 0) (e := 4) (by omega)
      (by omega) (by omega)) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 4) (e := 12) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_sep (saved_sep S (d := 4) (e := 8) (by omega) (by omega)
      (by omega)) (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_sep (saved_sep S (d := 8) (e := 12) (by omega) (by omega) (by omega))
      (by decide), Mem.readW_writeW_self32]
  · rw [Mem.readW_writeW_self32]

/-- What `save` writes lies within `scratch`. -/
theorem savedMem_frame (m : Mem) (S : BitVec 32) (b si di bp : BitVec 32) :
    Frame [⟨S.setWidth 64, 64⟩] m (savedMem m S b si di bp) := by
  unfold savedMem
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  refine Frame.writeW ?_ (List.mem_singleton_self _) _ (Offset.contains_base _ (by decide) (by decide))
  exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by decide) (by decide))

/-- The saved registers survive writes outside their 16 bytes. -/
theorem Saved.frame {m m' : Mem} {S : BitVec 32} {s₀ : State} {rs : List Region}
    (h : Saved m S s₀) (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨S.setWidth 64, 16⟩ r) : Saved m' S s₀ := by
  have e (d : Nat) (hd' : d + 4 ≤ 16) :
      m'.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 = m.readW (S.setWidth 64 + BitVec.ofNat 64 d) 32 :=
    hf.readW (Offset.contains_base _ hd' (by omega)) hd (by decide)
  obtain ⟨h0, h4, h8, h12⟩ := h
  exact ⟨(e 0 (by decide)).trans h0, (e 4 (by decide)).trans h4, (e 8 (by decide)).trans h8,
    (e 12 (by decide)).trans h12⟩

theorem restore_ok (s₀ s : State) (S : BitVec 32) (hS : S.toNat + 64 ≤ 2 ^ 32)
    (ha : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 16) 4)
    (hv : s.mem.readW (addr (s.gpr .esp) 16) 32 = S)
    (hr : InRegions (s.rd ++ s.wr) (S.setWidth 64) 64) (hs : Saved s.mem S s₀) :
    WP isa (.block restore) s fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
      t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = s.mem ∧ Keep [.ecx, .ebx, .esi, .edi, .ebp] s t := by
  have r (d : Nat) (hd : d + 4 ≤ 64) : InRegions (s.rd ++ s.wr) (addr S d) 4 := by
    rw [save_addr hS (by omega)]
    exact region_offset _ _ _ _ _ (by omega) hd hr
  have r0 := r 0 (by decide)
  have r4 := r 4 (by decide)
  have r8 := r 8 (by decide)
  have r12 := r 12 (by decide)
  rw [save_addr hS (by decide)] at r0 r4 r8 r12
  obtain ⟨h0, h4, h8, h12⟩ := hs
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .ebx = s₀.gpr .ebx ∧ t.gpr .esi = s₀.gpr .esi ∧ t.gpr .edi = s₀.gpr .edi ∧
      t.gpr .ebp = s₀.gpr .ebp ∧ t.mem = s.mem) [.ecx, .ebx, .esi, .edi, .ebp] ?_
    (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hk⟩
  unfold restore
  rrun [ha, hv, save_addr hS, r0, r4, r8, r12, h0, h4, h8, h12]

end VG.Proof.Rc4.X86
