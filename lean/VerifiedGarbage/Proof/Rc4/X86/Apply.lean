import VerifiedGarbage.Proof.Rc4.X86.ApplyLoop

/-! # RC4 on x86 (32-bit): the stream function -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Spec.Rc4 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-- The context is unchanged by writes outside its 258 bytes. -/
theorem contextAt_frame {rs : List Region} {m m' : Mem} {p : Addr} (hf : Frame rs m m')
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, 258⟩ r) : contextAt m' p = contextAt m p := by
  have e (i : Nat) (hi : i < 258) : m' (p + BitVec.ofNat 64 i) = m (p + BitVec.ofNat 64 i) :=
    hf.bytes (R := ⟨p, 258⟩) hd (show (258 : Nat) ≤ 2 ^ 64 by decide) hi
  apply context_ext
  · apply Vector.ext
    intro k hk
    simp only [contextAt, Vector.getElem_ofFn]
    exact e k (by omega)
  · exact e 256 (by decide)
  · exact e 257 (by decide)

theorem apply_entry (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) :
    WP isa (.block entry) s fun a => a.mem = s.mem ∧ Keep [.eax, .ecx, .edx] s a ∧
      a.gpr .eax = (contextAt s.mem (P.setWidth 64)).i.setWidth 32 ∧
      a.zf = some (L &&& L == 0#32) := by
  have h4 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 4) 4 := hp.arg_in (i := 0) (by decide)
  have v4 : s.mem.readW (addr (s.gpr .esp) 4) 32 = P := hp.aP
  have h12 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) 12) 4 := hp.arg_in (i := 2) (by decide)
  have v12 : s.mem.readW (addr (s.gpr .esp) 12) 32 = L := hp.aL
  have a256 : addr P 256 = P.setWidth 64 + 256#64 := addr_of_fit (by have := hp.ctxFit; omega)
  have r256 : InRegions (s.rd ++ s.wr) (P.setWidth 64 + 256#64) 1 := by
    obtain ⟨r, hr, hc⟩ := region_offset _ _ _ 256 1 (by decide) (by decide) hp.ctx
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  refine WP.mono (WP.keep (Q := fun a => a.mem = s.mem ∧
      a.gpr .eax = (contextAt s.mem (P.setWidth 64)).i.setWidth 32 ∧
      a.zf = some (L &&& L == 0#32)) [.eax, .ecx, .edx] ?_ (by decide +kernel))
    fun a ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2⟩
  unfold entry
  rrun [h4, v4, a256, r256, h12, v12, contextAt]
  exact ⟨rfl, rfl⟩

theorem apply_start (b : State) (P : BitVec 32) (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (h4 : InRegions (b.rd ++ b.wr) (addr (b.gpr .esp) 4) 4)
    (v4 : b.mem.readW (addr (b.gpr .esp) 4) 32 = P)
    (h257 : InRegions (b.rd ++ b.wr) (P.setWidth 64 + 257#64) 1) :
    WP isa (.block start) b fun c => c.mem = b.mem ∧ Keep [.esi, .edi, .ebp, .ebx] b c ∧
      c.gpr .esi = b.gpr .eax ∧ c.gpr .edi = P ∧
      c.gpr .ebp = (b.mem (P.setWidth 64 + 257#64)).setWidth 32 ∧ c.gpr .ebx = 0#32 := by
  have a257 : addr P 257 = P.setWidth 64 + 257#64 := addr_of_fit (by omega)
  refine WP.mono (WP.keep (Q := fun c => c.mem = b.mem ∧ c.gpr .esi = b.gpr .eax ∧
      c.gpr .edi = P ∧ c.gpr .ebp = (b.mem (P.setWidth 64 + 257#64)).setWidth 32 ∧
      c.gpr .ebx = 0#32) [.esi, .edi, .ebp, .ebx] ?_ (by decide +kernel))
    fun c ⟨h, hk⟩ => ⟨h.1, hk, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  unfold start
  rrun [h4, v4, a257, h257]

theorem apply_finish (d : State) (i j : Byte) (P : BitVec 32) (hfit : P.toNat + 258 ≤ 2 ^ 32)
    (hsi : d.gpr .esi = i.setWidth 32) (hbp : d.gpr .ebp = j.setWidth 32) (hdi : d.gpr .edi = P)
    (hw : InRegions d.wr (P.setWidth 64) 258) :
    WP isa (.block finish) d fun e =>
      e.mem = (d.mem.write (P.setWidth 64 + 256#64) 1 i).write (P.setWidth 64 + 257#64) 1 j ∧
      Keep [.eax] d e := by
  have a256 : addr P 256 = P.setWidth 64 + 256#64 := addr_of_fit (by omega)
  have a257 : addr P 257 = P.setWidth 64 + 257#64 := addr_of_fit (by omega)
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hw
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hw
  refine WP.mono (WP.keep (Q := fun e =>
      e.mem = (d.mem.write (P.setWidth 64 + 256#64) 1 i).write (P.setWidth 64 + 257#64) 1 j)
    [.eax] ?_ (by decide +kernel)) fun e ⟨h, hk⟩ => ⟨h, hk⟩
  unfold finish
  rrun [hsi, hbp, hdi, a256, a257, h256, h257, writeW_byte8, low_byte32]

theorem saved_spill (Sc : BitVec 32) :
    Region.Disjoint ⟨Sc.setWidth 64, 16⟩ ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩ := by
  intro x h₁ h₂
  exact Offset.sep_base (Sc.setWidth 64) (n := 16) (e := 16) (k := 4) (Nat.le_refl _) (by decide) x
    (by simp only [Region.Contains] at h₁; omega) (by simp only [Region.Contains] at h₂; omega)

/-- The full stream function, including empty input. -/
theorem apply_ok (s : State) {P D L Sc : BitVec 32} (hp : ApplyPre s P D L Sc) :
    WP isa VG.Impl.Rc4.X86.apply s fun t =>
      (contextAt t.mem (P.setWidth 64) = (upd s P D L.toNat).1 ∧
        bytesAt t.mem (D.setWidth 64) L.toNat = (upd s P D L.toNat).2) ∧
      Frame (applyRegions P D L Sc) s.mem t.mem ∧ t.gpr .ebx = s.gpr .ebx ∧
      t.gpr .esi = s.gpr .esi ∧ t.gpr .edi = s.gpr .edi ∧ t.gpr .ebp = s.gpr .ebp := by
  unfold VG.Impl.Rc4.X86.apply
  refine WP.seq (WP.mono (apply_entry s hp) fun a ⟨ham, hak, hax, haz⟩ => ?_)
  have hasp : a.gpr .esp = s.gpr .esp := hak.gpr (by decide)
  refine WP.ite (L == 0#32) (by simp only [eval, haz, BitVec.and_self]) (fun hz => ?_)
    (fun hnz => ?_)
  · have hL : L.toNat = 0 := by rw [beq_iff_eq.mp hz]; rfl
    refine WP.block_nil ?_
    rw [hL, ham]
    exact ⟨⟨rfl, rfl⟩, Frame.refl _ _, hak.gpr (by decide), hak.gpr (by decide),
      hak.gpr (by decide), hak.gpr (by decide)⟩
  have hL0 : L.toNat ≠ 0 := fun h => by
    have : L = 0#32 := BitVec.eq_of_toNat_eq h
    rw [this] at hnz
    exact absurd hnz (by decide)
  refine WP.seq ?_
  rw [WP.block_append_iff]
  have hsc : InRegions a.wr (Sc.setWidth 64) 64 := by rw [hak.2.2]; exact hp.scratch
  refine WP.mono (save_ok a Sc hp.scratchFit
    (by rw [hak.2.1, hak.2.2, hasp]; exact hp.arg_in (i := 3) (by decide))
    (by rw [ham, hasp]; exact hp.aS) hsc) fun b ⟨hbm, hbk⟩ => ?_
  have hsave : Frame [⟨Sc.setWidth 64, 64⟩] s.mem b.mem := by
    rw [hbm, ham]; exact savedMem_frame _ _ _ _ _ _
  have hbf : Frame (applyRegions P D L Sc) s.mem b.mem :=
    hsave.mono fun r hr => by
      simp only [List.mem_singleton] at hr
      subst hr
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hbsp : b.gpr .esp = s.gpr .esp := (hbk.gpr (by decide)).trans hasp
  have hbrd : b.rd = s.rd := hbk.2.1.trans hak.2.1
  have hbwr : b.wr = s.wr := hbk.2.2.trans hak.2.2
  have hsd : ∀ r ∈ [(⟨Sc.setWidth 64, 64⟩ : Region)],
      Region.Disjoint ⟨P.setWidth 64, 258⟩ r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact hp.ctxScratch
  have hctx : contextAt b.mem (P.setWidth 64) = contextAt s.mem (P.setWidth 64) :=
    contextAt_frame hsave hsd
  have r257 : InRegions (b.rd ++ b.wr) (P.setWidth 64 + 257#64) 1 := by
    obtain ⟨r, hr, hc⟩ := region_offset _ _ _ 257 1 (by decide) (by decide) hp.ctx
    exact ⟨r, by rw [hbrd, hbwr]; exact List.mem_append_right _ hr, hc⟩
  refine WP.mono (apply_start b P hp.ctxFit
    (by rw [hbrd, hbwr, hbsp]; exact hp.arg_in (i := 0) (by decide))
    (by rw [hbsp]; exact (hp.arg_eq hbf (i := 0) (by decide)).trans hp.aP) r257)
    fun c ⟨hcm, hck, hcsi, hcdi, hcbp, hcbx⟩ => ?_
  have hinv : LoopInv s P D L Sc b.mem 0 c := by
    have hu0 : upd s P D 0 = (contextAt s.mem (P.setWidth 64), []) := rfl
    refine
      { le := Nat.zero_le _
        table := by rw [hu0, hcm, hctx]
        i := by rw [hu0, hcsi, (hbk.gpr (by decide) : b.gpr .eax = a.gpr .eax), hax]
        j := by
          rw [hu0, hcbp, ← hctx]
          rfl
        data := by rw [hu0]; rfl
        tail := fun x _ hx => by
          rw [hcm]
          exact hsave.bytes (R := ⟨D.setWidth 64, L.toNat⟩) (fun r hr => by
            simp only [List.mem_singleton] at hr
            subst hr
            exact hp.dataScratch) (show L.toNat ≤ 2 ^ 64 by have := L.isLt; omega) hx
        frame := by rw [hcm]; exact Frame.refl _ _
        bx := hcbx
        p := hcdi
        sp := (hck.gpr (by decide)).trans hbsp
        rd := hck.2.1.trans hbrd
        wr := hck.2.2.trans hbwr }
  refine WP.seq (WP.mono (apply_loop s P D L Sc b.mem hp hbf (Nat.pos_of_ne_zero hL0) c hinv)
    fun d hd => ?_)
  rw [WP.block_append_iff]
  refine WP.mono (apply_finish d (upd s P D L.toNat).1.i (upd s P D L.toNat).1.j P hp.ctxFit
    hd.i hd.j hd.p (by rw [hd.wr]; exact hp.ctx)) fun e ⟨hem, hek⟩ => ?_
  have hc258 : (⟨P.setWidth 64, 258⟩ : Region) ∈
      [⟨P.setWidth 64, 258⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩, ⟨D.setWidth 64, L.toNat⟩] :=
    List.mem_cons_self
  have hbe : Frame [⟨P.setWidth 64, 258⟩, ⟨Sc.setWidth 64 + BitVec.ofNat 64 16, 4⟩,
      ⟨D.setWidth 64, L.toNat⟩] b.mem e.mem := by
    rw [hem]
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine Frame.write ?_ hc258 _ (Offset.contains_base _ (by decide) (by decide))
    refine hd.frame.sub fun r hr => ?_
    simp only [loopRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        Region.sub_prefix (Nat.le_refl _)⟩
  have hse : Frame (applyRegions P D L Sc) s.mem e.mem := by
    refine hbf.trans (hbe.sub fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact ⟨_, List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        Offset.sub_base _ (by decide)⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (Nat.le_refl _)⟩
  have hsaved : Saved e.mem Sc a := by
    have h0 := saved_savedMem a.mem Sc a
    rw [← hbm] at h0
    refine h0.frame hbe fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (hp.ctxScratch.symm).sub_left (Region.sub_prefix (by decide))
    · exact saved_spill Sc
    · exact (hp.dataScratch.symm).sub_left (Region.sub_prefix (by decide))
  have hesp : e.gpr .esp = s.gpr .esp := (hek.gpr (by decide)).trans hd.sp
  have herd : e.rd = s.rd := hek.2.1.trans hd.rd
  have hewr : e.wr = s.wr := hek.2.2.trans hd.wr
  refine WP.mono (restore_ok a e Sc hp.scratchFit
    (by rw [herd, hewr, hesp]; exact hp.arg_in (i := 3) (by decide))
    (by rw [hesp]; exact (hp.arg_eq hse (i := 3) (by decide)).trans hp.aS)
    (by rw [herd, hewr]; obtain ⟨r, hr, hc⟩ := hp.scratch; exact ⟨r, List.mem_append_right _ hr, hc⟩)
    hsaved) fun g ⟨gbx, gsi, gdi, gbp, gm, _⟩ => ?_
  have hDP (o : Nat) (ho : o < 258) :
      Mem.Sep (D.setWidth 64) L.toNat (P.setWidth 64 + BitVec.ofNat 64 o) 1 :=
    sep_of_sub hp.ctxData.symm (contains_prefix _ (Nat.le_refl _))
      (Offset.contains_base _ (by omega) (by omega))
  have hLn : L.toNat < 2 ^ 64 := by have := L.isLt; omega
  refine ⟨⟨?_, ?_⟩, by rw [gm]; exact hse, gbx.trans (hak.gpr (by decide)),
    gsi.trans (hak.gpr (by decide)), gdi.trans (hak.gpr (by decide)),
    gbp.trans (hak.gpr (by decide))⟩
  · rw [gm, hem, context_finish]
    exact context_ext hd.table rfl rfl
  · rw [gm, hem, bytes_write_sep _ _ _ _ _ hLn (hDP 257 (by decide)),
      bytes_write_sep _ _ _ _ _ hLn (hDP 256 (by decide))]
    exact hd.data

end VG.Proof.Rc4.X86
