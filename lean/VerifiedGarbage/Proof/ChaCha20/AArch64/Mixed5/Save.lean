import VerifiedGarbage.Proof.ChaCha20.AArch64.Mixed5.Loop

namespace VG.Proof.ChaCha20.AArch64.Mixed5
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Mixed5
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

theorem read_saved (m : Mem) (p : Addr) (a b c : BitVec 64) (j : Fin 3) :
    (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 (256 + 8 * j)) 64 =
        [a,b,c].getD j a := by
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
  rcases hj with rfl | rfl | rfl
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 256) 64 = a
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),
      Mem.readW_writeW_sep (Offset.sep p (d := 256) (n := 8) (e := 264) (k := 8)
        (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · change (((m.writeW (p + BitVec.ofNat 64 256) a).writeW (p + BitVec.ofNat 64 264) b).writeW
      (p + BitVec.ofNat 64 272) c).readW (p + BitVec.ofNat 64 264) 64 = b
    rw [Mem.readW_writeW_sep (Offset.sep p (d := 264) (n := 8) (e := 272) (k := 8)
      (by decide) (by decide) (by decide)) (by decide),Mem.readW_writeW_self64]
  · exact Mem.readW_writeW_self64 _ _ _

 theorem enter_ok {s₀ s : State} (hp : XPre s₀) (h : LInv s₀ 0 s)
    (hold : ∀ r ∈ preserved, s.gpr r = s₀.gpr r) : WP isa (.block enter) s (BulkInv s₀ 0) := by
  have ho (d : Nat) (hd : d + 8 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  unfold enter
  apply WP.block_cons_iff.mpr
  let m₁ := s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 256) (s.gpr .x20)
  refine ⟨{s with mem := m₁},exec_str_x (by decide) (ho 256 (by decide)),?_⟩
  apply WP.block_cons_iff.mpr
  let m₂ := m₁.writeW (s.gpr .x3 + BitVec.ofNat 64 264) (s.gpr .x19)
  refine ⟨{s with mem := m₂},exec_str_x (s := {s with mem := m₁}) (by decide) (ho 264 (by decide)),?_⟩
  apply WP.block_cons_iff.mpr
  let m₃ := m₂.writeW (s.gpr .x3 + BitVec.ofNat 64 272) (s.gpr .x26)
  refine ⟨{s with mem := m₃},exec_str_x (s := {s with mem := m₂}) (by decide) (ho 272 (by decide)),?_⟩
  refine (move_ok _ .x20 .x3).mono fun a ⟨ha,hav,hasp⟩ => ?_
  have hm : a.mem = (((s.mem.writeW (bp s₀ + BitVec.ofNat 64 256) (s₀.gpr .x20)).writeW
      (bp s₀ + BitVec.ofNat 64 264) (s₀.gpr .x19)).writeW
      (bp s₀ + BitVec.ofNat 64 272) (s₀.gpr .x26)) := by
    simpa only [m₃,m₂,m₁,h.x3,hold .x20 (by decide),hold .x19 (by decide),hold .x26 (by decide)] using ha.mem
  have hf : Frame [bR s₀] s.mem a.mem := by
    rw [hm]
    exact (((Frame.refl _ _).writeW (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 256 + 8 ≤ 320) (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 264 + 8 ≤ 320) (by decide))).writeW
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 272 + 8 ≤ 320) (by decide))
  refine ⟨⟨(ha.other _ (by decide)).trans h.x0,(ha.other _ (by decide)).trans h.x1,
    (ha.other _ (by decide)).trans h.x2,(ha.other _ (by decide)).trans h.x3,h.le,?_,
    ha.rd.trans h.rd,ha.wr.trans h.wr,hasp.trans h.sp,?_,?_,
    h.frame.trans (hf.mono (by simp))⟩,ha.gpr.trans h.x3,?_⟩
  · intro r hr nr nr21 nr22; rw [ha.other r nr]; exact h.cs r hr nr nr21 nr22
  · rw [VG.Proof.ChaCha20.AArch64.Xor.stateAt_frame hf (by simpa using hp.st_b)]; exact h.cnt
  · intro k hk
    rw [hf.bytes (R := dR s₀) (by simpa using hp.d_b)
      (by have hL := VG.Proof.ChaCha20.AArch64.Xor.L_lt s₀; change L s₀ ≤ 2 ^ 64; omega) hk]
    exact h.data k hk
  · intro j
    rw [hm,read_saved]
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by simp only [Fin.ext_iff]; omega
    rcases hj with rfl | rfl | rfl <;> rfl

 theorem leave_ok {s₀ s : State} {t : Nat} (hp : XPre s₀) (h : BulkInv s₀ t s) :
    WP isa (.block leave) s fun u => LInv s₀ t u ∧
      (∀ r ∈ preserved, u.gpr r = s₀.gpr r) := by
  have hi (d : Nat) (hd : d + 8 ≤ 320) : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 d) 8 := by
    rw [h.rd,hp.rd,h.wr,hp.wr,h.x3]
    exact ⟨bR s₀,by simp,Offset.contains_base _ hd (by omega)⟩
  have hm₀ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 256) 8 = s₀.gpr .x20 := by
    rw [h.x3]; exact h.saved 0
  have hm₁ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 264) 8 = s₀.gpr .x19 := by
    rw [h.x3]; exact h.saved 1
  have hm₂ : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 272) 8 = s₀.gpr .x26 := by
    rw [h.x3]; exact h.saved 2
  unfold leave
  apply WP.of_runBlock
  simp (config := {decide := true}) only [runBlock_cons,runBlock_nil,exec,addr,Size.bytes,Size.bits,
    ite_true,ite_false,State.load,hi 256 (by decide),hi 264 (by decide),hi 272 (by decide),
    RegUpd.gpr_write,BitVec.setWidth_eq,RegUpd.rd_write,RegUpd.wr_write,RegUpd.mem_write,
    Option.bind_some,Option.map_some,isa,runStep_some,Option.some.injEq,exists_eq_left',
    hm₀,hm₁,hm₂]
  refine ⟨⟨?_,?_,?_,?_,h.le,?_,h.rd,h.wr,h.sp,h.cnt,h.data,h.frame⟩,?_⟩
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x0 ≠ .x26 by decide,
      show Reg.x0 ≠ .x19 by decide,show Reg.x0 ≠ .x20 by decide,ite_false]; exact h.x0
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x1 ≠ .x26 by decide,
      show Reg.x1 ≠ .x19 by decide,show Reg.x1 ≠ .x20 by decide,ite_false]; exact h.x1
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x2 ≠ .x26 by decide,
      show Reg.x2 ≠ .x19 by decide,show Reg.x2 ≠ .x20 by decide,ite_false]; exact h.x2
  · simp only [RegUpd.gpr_write,BitVec.setWidth_eq,show Reg.x3 ≠ .x26 by decide,
      show Reg.x3 ≠ .x19 by decide,show Reg.x3 ≠ .x20 by decide,ite_false]; exact h.x3
  · intro r hr n20 n21 n22
    simp only [RegUpd.gpr_write,n20,n21,n22,ite_false]
    exact h.cs r hr n20 n21 n22
  · intro r hr
    by_cases n20 : r = .x20
    · subst r; simp
    by_cases n21 : r = .x19
    · subst r; simp
    by_cases n22 : r = .x26
    · subst r; simp
    simp only [n20,n21,n22,ite_false]
    exact h.cs r hr n20 n21 n22

end VG.Proof.ChaCha20.AArch64.Mixed5
