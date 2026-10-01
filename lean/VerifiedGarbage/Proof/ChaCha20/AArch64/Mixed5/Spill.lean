import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Prepare

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev lowBuf (s : State) : Region := ⟨s.gpr .x3,64⟩

/-- Move a public pointer, preserving all other state. -/
theorem move_ok (s : State) (d n : Reg) :
    WP isa (.block [.addImm .x d n 0]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n) ∧ u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n),?_,WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq,BitVec.add_zero] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := 0) (by decide)

structure Spilled (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Neon4.Holds
    (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j)) s
  cnt : source s = ctr (source s₀) 4
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  words : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 4))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  x1 : s.gpr .x1 = s₀.gpr .x3
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,lowBuf s₀] s₀.mem s.mem

theorem spill_ok {s₀ s : State} (hp : CP s₀) (h : Prepared s₀ s 10) :
    WP isa spill s (Spilled s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 := h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 := (h.keep _ nx20 (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_ok s .x1 .x20).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (source s₀) 4)) a := by
    intro k hk
    rw [ha.other _ (by
      intro he; exact VG.Proof.ChaCha20.AArch64.not_words_x1 ⟨k,hk,he.symm⟩)]
    exact h.scalar k hk
  have hpₐ : VG.Proof.ChaCha20.AArch64.Pre a := by
    refine ⟨?_,?_,?_⟩
    · intro k hk
      change InRegions (a.rd ++ a.wr) (a.gpr .x0 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.rd,ha.wr,h.rd,h.wr,ha.other _ (by decide),hx0]
      exact hp.read ⟨k,hk⟩
    · intro k hk
      change InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (4 * k)) 4
      rw [ha.wr,h.wr,ha.gpr,hx20]
      exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Region.sub_prefix (by decide : 256 ≤ 320))
  have hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by
    decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [lowBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : source a = ctr (source s₀) 4 := by
    rw [source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : source b = ctr (source s₀) 4 := by
    rw [source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Region.sub_prefix (by decide : 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,
    hr.trans (ha.rd.trans h.rd),hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Neon4.Holds,hbv,hav] using h.vec
  · intro k hkk
    have he := hb k hkk
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr hr1 h21 h22; rw [hk r hnr,ha.other r hr1,h.keep r hnr h21 h22]
  · rw [hk _ VG.Proof.ChaCha20.AArch64.not_words_x1,ha.gpr,hx20]
  · rw [ha.mem] at hfb
    exact (h.frame.mono (by simp)).trans (hfb.mono (by simp))

theorem Spilled.read16 {s₀ s : State} (h : Spilled s₀ s) (r : Fin 4) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (block (ctr (source s₀) 4))[4 * r.val + e]'(by omega) := by
    intro e he
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega]
    exact h.words _ (by omega)
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.mod_eq_of_lt r.isLt,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed5
