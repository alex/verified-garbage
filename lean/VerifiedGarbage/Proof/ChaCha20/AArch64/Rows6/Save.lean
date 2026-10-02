import VerifiedGarbage.Proof.ChaCha20.AArch64.Rows6.Tail

namespace VG.Proof.ChaCha20.AArch64.Rows6
open VG VG.AArch64 VG.Impl.ChaCha20.AArch64.Rows6
open VG.Proof.ChaCha20.AArch64.Xor (XPre st dp L bp stR dR bR)

theorem read_write_self (m : Mem) (p : Addr) (v : BitVec 128) :
    (m.write p 16 v).read p 16 = v := by
  have h := Mem.readW_writeW_self m p 16 v (by decide)
  simpa only [Mem.readW,Mem.writeW,BitVec.setWidth_eq] using h

theorem save_ok (s : State) (hp : XPre s) :
    WP isa (.block save) s fun u =>
      u.gpr = s.gpr ∧ u.v = s.v ∧ u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp ∧
      Frame [bR s] s.mem u.mem ∧
      u.mem.read (bp s + BitVec.ofNat 64 256) 16 = s.v .v8 ∧
      u.mem.read (bp s + BitVec.ofNat 64 272) 16 = s.v .v9 := by
  have ho (d : Nat) (hd : d + 16 ≤ 320) : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 d) 16 := by
    rw [hp.wr]
    exact ⟨bR s,by simp,Offset.contains_base _ hd (by omega)⟩
  apply WP.of_runBlock
  simp (config := {decide := true}) only [save,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.store,ho 256 (by decide),ho 272 (by decide),
    Option.bind_some,Option.some.injEq,exists_eq_left',isa,runStep_some]
  refine ⟨trivial,trivial,trivial,trivial,trivial,?_,?_,?_⟩
  · exact ((Frame.refl _ _).write (List.mem_cons_self ..) _
      (Offset.contains_base _ (by decide : 256 + 16 ≤ 320) (by decide))).write
      (List.mem_cons_self ..) _ (Offset.contains_base _ (by decide : 272 + 16 ≤ 320) (by decide))
  · rw [Mem.read_write_sep (Offset.sep (bp s) (d := 256) (n := 16) (e := 272) (k := 16)
      (by decide) (by decide) (by decide)) (by decide),read_write_self]
  · exact read_write_self _ _ _

theorem restore_ok {s : State} (v8 v9 : BitVec 128)
    (hi0 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 256) 16)
    (hi1 : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 272) 16)
    (hm0 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 256) 16 = v8)
    (hm1 : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 272) 16 = v9) :
    WP isa (.block restore) s fun u =>
      u.v .v8 = v8 ∧ u.v .v9 = v9 ∧ u.gpr = s.gpr ∧ u.mem = s.mem ∧
      u.rd = s.rd ∧ u.wr = s.wr ∧ u.sp = s.sp := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [restore,runBlock_cons,runBlock_nil,exec,addr,
    ite_true,State.load,hi0,hi1,State.setV,hm0,hm1,Option.bind_some,Option.map_some,
    Option.some.injEq,exists_eq_left',isa,runStep_some]
  trivial
end VG.Proof.ChaCha20.AArch64.Rows6
