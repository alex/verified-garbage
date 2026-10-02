import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed8.SaveGP
import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Save

namespace VG.Proof.ChaCha20.AArch64.Mixed8
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed8
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

abbrev saveV : List Instr := [.strq .v8 .x3 128,.strq .v9 .x3 144]
abbrev restoreV : List Instr := [.ldrq .v8 .x3 128,.ldrq .v9 .x3 144]
abbrev savedVR (s : State) : Region := ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩

theorem saveV_ok (s : State)
    (ho0 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (ho1 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 144) 16) :
    WP isa (.block saveV) s fun u =>
      u.gpr = s.gpr ∧ u.v = s.v ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame [savedVR s] s.mem u.mem ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s.v .v8 ∧
      u.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s.v .v9 := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [saveV,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.store,ho0,ho1,Option.bind_some,Option.some.injEq,exists_eq_left',isa,runStep_some]
  refine ⟨trivial,trivial,trivial,trivial,trivial,?_,?_,?_⟩
  · have h0 : (savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 128) 16 := by
      simp only [Region.Contains,BitVec.sub_self]; decide
    have h1 : (savedVR s).Contains (s.gpr .x3 + BitVec.ofNat 64 144) 16 := by
      exact Offset.contains (s.gpr .x3) (by decide : 128 ≤ 144)
        (by decide : 144 + 16 ≤ 128 + 32) (by decide)
    exact ((Frame.refl _ _).write (List.mem_cons_self ..) _ h0).write
      (List.mem_cons_self ..) _ h1
  · rw [Mem.read_write_sep (Offset.sep (s.gpr .x3) (d := 128) (n := 16) (e := 144) (k := 16)
      (by decide) (by decide) (by decide)) (by decide),VG.Proof.ChaCha20.AArch64.Rows6.read_write_self]
  · exact VG.Proof.ChaCha20.AArch64.Rows6.read_write_self _ _ _

theorem restoreV_ok {s : State} (v8 v9 : BitVec 128)
    (hi0 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 128) 16)
    (hi1 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 144) 16)
    (hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = v8)
    (hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = v9) :
    WP isa (.block restoreV) s fun u =>
      u.v .v8 = v8 ∧ u.v .v9 = v9 ∧ u.gpr = s.gpr ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restoreV,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.load,hi0,hi1,State.setV,hm0,hm1,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',isa,runStep_some]
  trivial

theorem gp_same {s₀ s u : State} {t : Nat} (h : GPInv s₀ t s)
    (hg : u.gpr = s.gpr) (hm : u.mem = s.mem) (hr : u.rd = s.rd)
    (hw : u.wr = s.wr) (hsp : u.sp = s.sp) : GPInv s₀ t u := by
  refine ⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,?_⟩,?_,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [hm]; exact h.cnt
  · rw [hm]; exact h.data
  · rw [hm]; exact h.frame
  · rw [hg]; exact h.x20
  · rw [hm]; exact h.saved

theorem enterV_ok {s₀ s : State} (hp : XPre s₀) (h : GPInv s₀ 0 s)
    (hv : s.v = s₀.v) : WP isa (.block saveV) s (BulkInv s₀ 0) := by
  have ho (d : Nat) (hd : d + 16 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  refine (saveV_ok s (ho 128 (by decide)) (ho 144 (by decide))).mono fun u
    ⟨hg,_,hr,hw,hsp,hf,hm0,hm1⟩ => ?_
  have hsub : (savedVR s).Sub (bR s₀) := by
    rw [show savedVR s = ⟨bp s₀ + BitVec.ofNat 64 128,32⟩ by rw [savedVR,h.x3]]
    exact Offset.sub_base _ (by decide)
  have hfb : Frame [bR s₀] s.mem u.mem := hf.sub (by
    intro r hr; have he := List.mem_singleton.mp hr; subst r
    exact ⟨bR s₀,by simp,hsub⟩)
  refine ⟨⟨⟨?_,?_,?_,?_,h.le,?_,hr.trans h.rd,hw.trans h.wr,hsp.trans h.sp,?_,?_,
    h.frame.trans (hfb.mono (by simp))⟩,?_,?_⟩,?_⟩
  · rw [hg]; exact h.x0
  · rw [hg]; exact h.x1
  · rw [hg]; exact h.x2
  · rw [hg]; exact h.x3
  · intro r hr n20 n19 n26; rw [hg]; exact h.cs r hr n20 n19 n26
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hfb (by simpa using hp.st_b)]; exact h.cnt
  · intro k hk
    rw [hfb.bytes (R := dR s₀) (by simpa using hp.d_b)
      (by have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀; change L s₀ ≤ 2 ^ 64; omega) hk]
    exact h.data k hk
  · rw [hg]; exact h.x20
  · intro j
    rw [hf.readW (r := guardR s₀ j) (by simp only [Region.Contains,BitVec.sub_self]; decide)
      (by intro r hr; have he := List.mem_singleton.mp hr; subst r
          change (guardR s₀ j).Disjoint ⟨s.gpr .x3 + BitVec.ofNat 64 128,32⟩
          rw [h.x3]
          exact Offset.disjoint _ (by have hj := j.isLt; omega)
            (by have hj := j.isLt; omega) (by decide)) (by decide),h.saved j]
  · intro j
    have hj : j = 0 ∨ j = 1 := by simp only [Fin.ext_iff]; omega
    rcases hj with rfl | rfl
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 128) 16 = s₀.v .v8
      simpa only [h.x3,hv] using hm0
    · change u.mem.read (bp s₀ + BitVec.ofNat 64 144) 16 = s₀.v .v9
      simpa only [h.x3,hv] using hm1

theorem enter_ok {s₀ s : State} (hp : XPre s₀) (h : LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) (hv : s.v = s₀.v) :
    WP isa (.block enter) s (BulkInv s₀ 0) := by
  unfold enter
  apply WP.block_append_iff.mpr
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.enter,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> rfl) (enterGP_ok hp h hold)).mono fun u ⟨hu,huv,_,_,_⟩ => ?_
  exact enterV_ok hp hu (huv.trans hv)

theorem leaveV_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s) :
    WP isa (.block restoreV) s fun u =>
      GPInv s₀ t u ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  have hi (d : Nat) (hd : d + 16 ≤ 320) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [h.rd,hp.rd,h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  have hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 128) 16 = s₀.v .v8 := by
    rw [h.x3]; exact h.savedV 0
  have hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 144) 16 = s₀.v .v9 := by
    rw [h.x3]; exact h.savedV 1
  refine (restoreV_ok _ _ (hi 128 (by decide)) (hi 144 (by decide)) hm0 hm1).mono fun u
    ⟨hv8,hv9,hg,hm,hr,hw,hsp⟩ => ⟨gp_same h.toGPInv hg hm hr hw hsp,hv8,hv9⟩

theorem leave_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s) :
    WP isa (.block leave) s fun u => LInv s₀ t u ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) ∧ u.v .v8 = s₀.v .v8 ∧ u.v .v9 = s₀.v .v9 := by
  unfold leave
  apply WP.block_append_iff.mpr
  refine (leaveV_ok hp h).mono fun u ⟨hu,hv8,hv9⟩ => ?_
  refine (VG.Proof.ChaCha20.AArch64.Mixed5.keeps_vectors (by
    intro i hi; simp only [VG.Impl.ChaCha20.AArch64.Mixed5.leave,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> rfl) (leaveGP_ok hp hu)).mono fun v ⟨⟨hl,hcs⟩,hv,_,_,_⟩ => ?_
  exact ⟨hl,hcs,by rw [hv]; exact hv8,by rw [hv]; exact hv9⟩
end VG.Proof.ChaCha20.AArch64.Mixed8
