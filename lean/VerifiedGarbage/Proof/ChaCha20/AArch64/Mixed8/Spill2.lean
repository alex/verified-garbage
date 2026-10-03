import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.Second

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Mixed5 (SavedArgs keeps_vectors scalarFinish_ok)
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block)

abbrev scalarBuf (s : State) : Region := ⟨s.gpr .x3,128⟩
abbrev highBuf (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 64,64⟩

theorem move_offset_ok (s : State) (d n : Reg) (offset : Nat) (ho : offset < 4096) :
    WP isa (.block [.addImm .x d n offset]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u d (s.gpr n + BitVec.ofNat 64 offset) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  apply WP.block_cons_iff.mpr
  refine ⟨s.write .x d (s.gpr n + BitVec.ofNat 64 offset),?_,
    WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
  simpa only [State.read,BitVec.setWidth_eq] using
    exec_addImm_x (s := s) (d := d) (n := n) (imm := offset) ho

structure Spilled2 (s₀ s : State) : Prop where
  vec : VG.Proof.ChaCha20.AArch64.Rows6.Holds
    (VG.Proof.ChaCha20.AArch64.Rows6.pack (fun j => Nat.repeat innerBlock 10 (ctr (source s₀) j))) s
  cnt : source s = ctr (source s₀) 7
  saved : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) s
  first : ∀ k (hk : k < 16), s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 6))[k]
  last : ∀ k (hk : k < 16), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 64 + BitVec.ofNat 64 (4 * k)) 32 =
    (block (ctr (source s₀) 7))[k]
  keep : ∀ r, ¬ VG.Proof.ChaCha20.AArch64.Words r → r ≠ .x1 → r ≠ .x19 → r ≠ .x26 →
    s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  frame : Frame [sr s₀,scalarBuf s₀] s₀.mem s.mem

theorem spill2_ok {s₀ s : State} (hp : CP s₀) (h : Second s₀ s 5) :
    WP isa (spill 64) s (Spilled2 s₀) := by
  have hx0 : s.gpr .x0 = s₀.gpr .x0 :=
    h.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0 (by decide) (by decide) (by decide)
  have nx20 : ¬ VG.Proof.ChaCha20.AArch64.Words .x20 := by
    rintro ⟨k,hk,he⟩
    exact (show ∀ k < 16, Reg.x20 ≠ VG.Impl.ChaCha20.AArch64.wreg k by decide) k hk he
  have hx20 : s.gpr .x20 = s₀.gpr .x3 :=
    (h.keep _ nx20 (by decide) (by decide) (by decide)).trans hp.x20
  apply WP.seq
  refine (move_offset_ok s .x1 .x20 64 (by decide)).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hc : VG.Proof.ChaCha20.AArch64.Holds
      (Nat.repeat innerBlock 10 (ctr (source s₀) 7)) a := by
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
      rw [ha.wr,h.wr,ha.gpr,hx20,BitVec.add_assoc,← BitVec.ofNat_add]
      exact hp.buffer _ _ (by omega)
    · change (⟨a.gpr .x1,256⟩ : Region).Disjoint ⟨a.gpr .x0,64⟩
      rw [ha.gpr,hx20,ha.other _ (by decide),hx0]
      exact hp.st_b.symm.sub_left (Offset.sub_base _ (by decide : 64 + 256 ≤ 320))
  have hfinish : ∀ i ∈ VG.Impl.ChaCha20.AArch64.finish, vdstOf i = none := by decide +kernel
  refine (keeps_vectors hfinish (scalarFinish_ok a hpₐ hc)).mono fun b
    ⟨⟨hb,hf,hk⟩,hbv,hsp,hr,hw⟩ => ?_
  have hfb : Frame [highBuf s₀] a.mem b.mem := by simpa only [ha.gpr,hx20] using hf
  have hcntₐ : source a = ctr (source s₀) 7 := by
    rw [source,ha.mem,ha.other _ (by decide)]; exact h.cnt
  have hcntb : source b = ctr (source s₀) 7 := by
    rw [source,hk _ VG.Proof.ChaCha20.AArch64.not_words_x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by
        intro r hr; have he := List.mem_singleton.mp hr; subst r
        rw [ha.other _ (by decide),hx0,ha.gpr,hx20]
        exact hp.st_b.sub_right (Offset.sub_base _ (by decide : 64 + 64 ≤ 320)))]
    exact hcntₐ
  have hsavedb : SavedArgs (s₀.gpr .x2) (s₀.gpr .x1) b := by
    exact ⟨by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.len,
      by rw [hk _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide)),ha.other _ (by decide)]; exact h.saved.data⟩
  refine ⟨?_,hcntb,hsavedb,?_,?_,?_,hr.trans (ha.rd.trans h.rd),
    hw.trans (ha.wr.trans h.wr),hsp.trans (hasp.trans h.sp),?_⟩
  · simpa only [VG.Proof.ChaCha20.AArch64.Rows6.Holds,hbv,hav] using h.vec
  · intro k hk'
    rw [hfb.readW (r := lowBuf s₀) (Offset.contains_base _ (by omega) (by omega))
      (by intro r hr'; have he := List.mem_singleton.mp hr'; subst r
          exact Offset.base_disjoint _ (by decide : 64 ≤ 64) (by decide : 64 + 64 ≤ 2 ^ 64)) (by decide),ha.mem]
    exact h.first k hk'
  · intro k hk'
    have he := hb k hk'
    rw [ha.gpr,hx20] at he
    simpa only [VG.Proof.ChaCha20.AArch64.V,hcntₐ,block,Vector.getElem_zipWith,Fin.getElem_fin] using he
  · intro r hnr h1 h19 h26; rw [hk r hnr,ha.other r h1]; exact h.keep r hnr h1 h19 h26
  · rw [ha.mem] at hfb
    have hf₀ : Frame [sr s₀,scalarBuf s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr'; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr'
      rcases hr' with rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨scalarBuf s₀,by simp,Region.sub_prefix (by decide : 64 ≤ 128)⟩)
    exact hf₀.trans (hfb.sub (by
      intro r hr'; have he := List.mem_singleton.mp hr'; subst r
      exact ⟨scalarBuf s₀,by simp,Offset.sub_base _ (by decide : 64 + 64 ≤ 128)⟩))

theorem Spilled2.words {s₀ s : State} (h : Spilled2 s₀ s) (k : Nat) (hk : k < 32) :
    s.mem.readW (s₀.gpr .x3 + BitVec.ofNat 64 (4 * k)) 32 =
      (block (ctr (source s₀) (6 + k / 16)))[k % 16]'(by omega) := by
  by_cases hk' : k < 16
  · simpa only [Nat.div_eq_of_lt hk',Nat.mod_eq_of_lt hk',Nat.add_zero] using h.first k hk'
  · have he := h.last (k - 16) (by omega)
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 64 + 4 * (k - 16) = 4 * k by omega] at he
    simpa only [show k / 16 = 1 by omega,show k % 16 = k - 16 by omega] using he

theorem Spilled2.read16 {s₀ s : State} (h : Spilled2 s₀ s) (r : Fin 8) :
    s.mem.read (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun j => block (ctr (source s₀) (6 + j))) r := by
  rw [VG.AArch64.read16]
  have hw : ∀ e (he : e < 4), s.mem.readW
      (s₀.gpr .x3 + BitVec.ofNat 64 (16 * r) + BitVec.ofNat 64 (4 * e)) 32 =
        (block (ctr (source s₀) (6 + r.val / 4)))[4 * (r.val % 4) + e]'(by omega) := by
    intro e he
    rw [BitVec.add_assoc,← BitVec.ofNat_add,show 16 * r.val + 4 * e = 4 * (4 * r.val + e) by omega,
      h.words _ (by omega)]
    simp only [show (4 * r.val + e) / 16 = r.val / 4 by omega,
      show (4 * r.val + e) % 16 = 4 * (r.val % 4) + e by omega]
  rw [hw 0 (by decide),hw 1 (by decide),hw 2 (by decide),hw 3 (by decide)]
  simp only [VG.Proof.ChaCha20.AArch64.Neon4.output,Nat.add_zero]

end VG.Proof.ChaCha20.AArch64.Mixed8
