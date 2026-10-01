import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Finish

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20 (ctr)
open VG.Spec.ChaCha20 (stateAt innerBlock block serialize)

abbrev lastR (s : State) : Region := ⟨s.gpr .x1 + BitVec.ofNat 64 256,64⟩

 theorem pointer_ok (s : State) {n : Nat} (hn : n < 4096) (sub : Bool) :
    WP isa (.block [if sub then .subImm .x .x1 .x1 n else .addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1
        (if sub then s.gpr .x1 - BitVec.ofNat 64 n else s.gpr .x1 + BitVec.ofNat 64 n) ∧
      u.v = s.v ∧ u.sp = s.sp := by
  cases sub with
  | false =>
    change WP isa (.block [.addImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 + BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 + BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_addImm_x hn
  | true =>
    change WP isa (.block [.subImm .x .x1 .x1 n]) s fun u =>
      VG.Proof.ChaCha20.AArch64.Xor.Upd s u .x1 (s.gpr .x1 - BitVec.ofNat 64 n) ∧
        u.v = s.v ∧ u.sp = s.sp
    apply WP.block_cons_iff.mpr
    refine ⟨s.write .x .x1 (s.gpr .x1 - BitVec.ofNat 64 n),?_,
      WP.block_nil ⟨VG.Proof.ChaCha20.AArch64.Xor.Upd.write64 _ _ _,rfl,rfl⟩⟩
    simpa only [State.read,BitVec.setWidth_eq] using exec_subImm_x hn

 theorem first_last_disjoint (s : State) : (firstR s).Disjoint (lastR s) := by
  exact Offset.base_disjoint (s.gpr .x1) (e := 256) (n := 64) (k := 256) (by decide) (by decide)

structure Chunked (s₀ s : State) : Prop where
  x0 : s.gpr .x0 = s₀.gpr .x0
  x1 : s.gpr .x1 = s₀.gpr .x1
  x2 : s.gpr .x2 = s₀.gpr .x2
  x3 : s.gpr .x3 = s₀.gpr .x3
  cs : ∀ r ∈ preserved, r ≠ .x19 → r ≠ .x26 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  cnt : source s = source s₀
  data : ∀ k < 320, s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) =
    s₀.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) ^^^
      (serialize (block (ctr (source s₀) (k / 64)))).getD (k % 64) 0
  frame : Frame [sr s₀,lowBuf s₀,dr s₀] s₀.mem s.mem

 theorem last_ok {s₀ s : State} (hp : CP s₀) (h : Finished s₀ s) :
    WP isa last s (Chunked s₀) := by
  apply WP.seq
  refine (pointer_ok s (n := 256) (by decide) false).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have ha1 : a.gpr .x1 = s₀.gpr .x1 + BitVec.ofNat 64 256 := by simpa only [Bool.false_eq_true,ite_false,h.x1] using ha.gpr
  have ha3 : a.gpr .x3 = s₀.gpr .x3 := (ha.other _ (by decide)).trans h.x3
  have hf : ∀ r : Fin 4, a.mem.read (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 =
      VG.Proof.ChaCha20.AArch64.Neon4.output (fun _ => block (ctr (source s₀) 4)) r := by
    intro r; rw [ha.mem,ha3]; exact h.buf r
  have sep : (⟨a.gpr .x3,64⟩ : Region).Disjoint ⟨a.gpr .x1,64⟩ := by
    rw [ha3,ha1]
    exact (hp.d_b.symm.sub_left (Region.sub_prefix (by decide : 64 ≤ 320))).sub_right
      (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
  have hin : ∀ r : Fin 4, InRegions (a.rd ++ a.wr) (a.gpr .x3 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.rd,ha.wr,h.rd,h.wr,ha3]
    obtain ⟨q,hq,hc⟩ := hp.buffer (16 * r.val) 16 (by omega)
    exact ⟨q,List.mem_append_right _ hq,hc⟩
  have hout : ∀ r : Fin 4, InRegions a.wr (a.gpr .x1 + BitVec.ofNat 64 (16 * r)) 16 := by
    intro r; rw [ha.wr,h.wr,ha1,BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.data _ _ (by omega)
  apply WP.seq
  refine (xorLast_ok a (block (ctr (source s₀) 4)) hf sep hin hout).mono fun b ⟨hb,hfb,hab⟩ => ?_
  have hfb' : Frame [lastR s₀] s.mem b.mem := by simpa only [ha1,ha.mem] using hfb
  refine (pointer_ok b (n := 256) (by decide) true).mono fun c ⟨hc,hcv,hcsp⟩ => ?_
  have hc1 : c.gpr .x1 = s₀.gpr .x1 := by
    rw [hc.gpr,hab.gpr,ha.gpr]
    simp only [ite_true,Bool.false_eq_true,ite_false,BitVec.add_sub_cancel,h.x1]
  have hd (r : Reg) (hr : r ≠ .x1) : c.gpr r = s.gpr r := by
    rw [hc.other r hr,hab.gpr,ha.other r hr]
  have hm : c.mem = b.mem := hc.mem
  refine ⟨(hd _ (by decide)).trans h.x0,hc1,(hd _ (by decide)).trans h.x2,
    (hd _ (by decide)).trans h.x3,?_,hc.rd.trans (hab.rd.trans (ha.rd.trans h.rd)),
    hc.wr.trans (hab.wr.trans (ha.wr.trans h.wr)),hcsp.trans (hab.sp.trans (hasp.trans h.sp)),?_,?_,?_⟩
  · intro r hr h21 h22
    have nr : r ≠ .x1 := by intro he; subst r; simp [preserved] at hr
    rw [hd r nr]; exact h.cs r hr h21 h22
  · rw [source,hm,hd _ (by decide),h.x0,
      VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb' (by
        intro r hr; simp only [List.mem_singleton] at hr; subst r
        exact hp.st_d.sub_right (Offset.sub_base _ (by decide : 256 + 64 ≤ 320)))]
    rw [← h.x0]; exact h.cnt
  · intro k hk
    rw [hm]
    by_cases hk' : k < 256
    · have he : b.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) = s.mem (s₀.gpr .x1 + BitVec.ofNat 64 k) :=
        hfb'.bytes (R := firstR s₀) (by
          intro r hr; simp only [List.mem_singleton] at hr; subst r
          exact first_last_disjoint s₀) (by change 256 ≤ 2 ^ 64; decide) hk'
      rw [he]
      exact h.data k hk'
    · have he : a.gpr .x1 + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        rw [ha1,BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega)]
      have hh := hb (k - 256) (by omega)
      rw [he,ha.mem] at hh
      have hh₀ := h.frame.bytes (R := lastR s₀) (by
        intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact hp.st_d.symm.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))
        · exact (hp.d_b.sub_left (Offset.sub_base _ (by decide : 256 + 64 ≤ 320))).sub_right
            (Region.sub_prefix (by decide : 64 ≤ 320))
        · exact (first_last_disjoint s₀).symm)
        (by change 64 ≤ 2 ^ 64; decide) (i := k - 256) (by change k - 256 < 64; omega)
      have he₀ : (lastR s₀).base + BitVec.ofNat 64 (k - 256) = s₀.gpr .x1 + BitVec.ofNat 64 k := by
        change s₀.gpr .x1 + BitVec.ofNat 64 256 + BitVec.ofNat 64 (k - 256) = _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add,Nat.add_sub_cancel' (by omega)]
      rw [he₀] at hh₀
      rw [hh,hh₀,show k / 64 = 4 by omega,show k % 64 = k - 256 by omega]
  · rw [hm]
    have hf₁ : Frame [sr s₀,lowBuf s₀,dr s₀] s₀.mem s.mem := h.frame.sub (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact ⟨sr s₀,by simp,fun _ h => h⟩
      · exact ⟨lowBuf s₀,by simp,fun _ h => h⟩
      · exact ⟨dr s₀,by simp,Region.sub_prefix (by decide : 256 ≤ 320)⟩)
    exact hf₁.trans (hfb'.sub (by
      intro r hr; simp only [List.mem_singleton] at hr; subst r
      exact ⟨dr s₀,by simp,Offset.sub_base _ (by decide : 256 + 64 ≤ 320)⟩))

 theorem chunk_ok (s : State) (hp : CP s) : WP isa chunk s (Chunked s) := by
  apply WP.seq
  refine (prepare_ok s hp).mono fun a h => ?_
  apply WP.seq
  refine (rounds_ok h.vec h.table h.scalar 10).mono fun b ⟨hv,hc,hsp,ht⟩ => ?_
  have h' : Prepared s b 10 := ⟨hv,ht,hc.holds,by
      rw [source,hc.mem,hc.keep _ VG.Proof.ChaCha20.AArch64.not_words_x0]; exact h.cnt,
    ⟨by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.len,
      by rw [hc.keep _ (VG.Proof.ChaCha20.AArch64.not_words_preserved (by decide))]; exact h.saved.data⟩,
    fun r hr h21 h22 => (hc.keep r hr).trans (h.keep r hr h21 h22),hc.rd.trans h.rd,hc.wr.trans h.wr,
    hsp.trans h.sp,by rw [hc.mem]; exact h.frame⟩
  apply WP.seq
  refine (spill_ok hp h').mono fun c hc => ?_
  apply WP.seq
  refine (finish_ok hp hc).mono fun d hd => last_ok hp hd

end VG.Proof.ChaCha20.AArch64.Mixed5
