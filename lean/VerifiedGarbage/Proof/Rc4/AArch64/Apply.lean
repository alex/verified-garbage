import VerifiedGarbage.Proof.Rc4.AArch64.ApplyLoop

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4 RegUpd

theorem apply_finish (s : State) (ctx : Context) (d : Addr) (n : Nat) (hn : n < 2 ^ 64)
    (htable : (contextAt s.mem (s.gpr .x0)).table = ctx.table)
    (hi : s.gpr .x12 = ctx.i.setWidth 64) (hj : s.gpr .x13 = ctx.j.setWidth 64)
    (hp : InRegions s.wr (s.gpr .x0) 258)
    (hs : Mem.Sep d n (s.gpr .x0) 258) :
    WP isa (.block [.strb .x12 .x0 256, .strb .x13 .x0 257]) s fun t =>
      contextAt t.mem (s.gpr .x0) = ctx ∧ bytesAt t.mem d n = bytesAt s.mem d n := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hc (x : Byte) : ((x.setWidth 64).setWidth 32).setWidth 8 = x := by bv_omega
  rrun [State.store, h256, h257, hi, hj, hc]
  constructor
  · rw [context_finish, htable]
  · rw [bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide)),
      bytes_write_sep _ _ _ _ _ hn (sep_offset_right hs (by decide) (by decide))]

theorem apply_start (s : State) (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258) :
    WP isa (.block [.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0]) s fun t =>
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧
      t.gpr .x0 = s.gpr .x0 ∧ t.gpr .x1 = s.gpr .x1 ∧ t.gpr .x2 = s.gpr .x2 ∧
      t.gpr .x12 = (contextAt s.mem (s.gpr .x0)).i.setWidth 64 ∧
      t.gpr .x13 = (contextAt s.mem (s.gpr .x0)).j.setWidth 64 ∧ t.gpr .x9 = 255#64 := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hc (x : Byte) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  rrun [h256, h257, read_byte, hc, contextAt]

theorem apply_ok (s : State)
    (hp : InRegions s.wr (s.gpr .x0) 258)
    (hd : InRegions s.wr (s.gpr .x1) (s.gpr .x2).toNat)
    (hs : Mem.Sep (s.gpr .x0) 258 (s.gpr .x1) (s.gpr .x2).toNat) :
    WP isa VG.Impl.Rc4.AArch64.apply s fun t =>
      let result := update (contextAt s.mem (s.gpr .x0)) (bytesAt s.mem (s.gpr .x1) (s.gpr .x2).toNat)
      contextAt t.mem (s.gpr .x0) = result.1 ∧ bytesAt t.mem (s.gpr .x1) (s.gpr .x2).toNat = result.2 := by
  unfold VG.Impl.Rc4.AArch64.apply
  refine WP.ite (s.gpr .x2 == 0#64) (by simp only [eval, State.read, BitVec.setWidth_eq]; rfl)
    (fun hz => ?_) (fun hnz => ?_)
  · have hz' : s.gpr .x2 = 0#64 := beq_iff_eq.mp hz
    refine WP.block_nil ?_
    simp only [hz']
    exact ⟨rfl, rfl⟩
  · have hnz' : s.gpr .x2 ≠ 0#64 := beq_eq_false_iff_ne.mp hnz
    have hn : 0 < (s.gpr .x2).toNat := by
      by_contra h
      have hz : (s.gpr .x2).toNat = 0 := by omega
      exact hnz' (BitVec.eq_of_toNat_eq hz)
    obtain ⟨n, hnEq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : (s.gpr .x2).toNat ≠ 0)
    change (s.gpr .x2).toNat = n + 1 at hnEq
    have hbound : n + 1 < 2 ^ 64 := by rw [← hnEq]; exact (s.gpr .x2).isLt
    have hpRead : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258 := by
      obtain ⟨region, hr, hc⟩ := hp
      exact ⟨region, List.mem_append_right _ hr, hc⟩
    refine WP.seq (WP.mono (apply_start s hpRead) fun a ha => ?_)
    obtain ⟨ham, har, haw, ha0, ha1, ha2, ha12, ha13, ha9⟩ := ha
    have hpa : InRegions a.wr (a.gpr .x0) 256 := by
      rw [haw, ha0]
      have hh := region_offset _ _ _ 0 256 (by decide) (by decide) hp
      simpa only [BitVec.add_zero] using hh
    have hda : InRegions a.wr (a.gpr .x1) (n + 1) := by rw [haw, ha1, ← hnEq]; exact hd
    have hsa : Mem.Sep (a.gpr .x0) 256 (a.gpr .x1) (n + 1) := by
      rw [ha0, ha1, ← hnEq]
      exact fun x hx hy => hs x (by omega) hy
    have htable : (contextAt a.mem (a.gpr .x0)).table = (contextAt s.mem (s.gpr .x0)).table := by rw [ham, ha0]
    have hlen : a.gpr .x2 = BitVec.ofNat 64 (n + 1) := by
      rw [ha2, ← hnEq, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    refine WP.seq (WP.mono (apply_loop n a (contextAt s.mem (s.gpr .x0)) hbound htable ha12 ha13 ha9 hlen hpa hda hsa)
      fun b hb => ?_)
    have hpb : InRegions b.wr (b.gpr .x0) 258 := by rw [hb.wr, hb.p, haw, ha0]; exact hp
    have hsb : Mem.Sep (s.gpr .x1) (n + 1) (b.gpr .x0) 258 := by
      rw [hb.p, ha0, ← hnEq]
      exact sep_symm hs
    have htab : (contextAt b.mem (b.gpr .x0)).table =
        (update (contextAt s.mem (s.gpr .x0)) (bytesAt a.mem (a.gpr .x1) (n + 1))).1.table := by
      rw [hb.p]; exact hb.table
    refine WP.mono (apply_finish b _ (s.gpr .x1) (n + 1) (by omega) htab hb.i hb.j hpb hsb)
      fun t ht => ?_
    rw [hb.p, ha0] at ht
    have hdata := hb.data
    rw [ha1] at hdata
    rw [ham, ha1] at ht
    rw [ham] at hdata
    dsimp only
    rw [hnEq]
    exact ⟨ht.1, ht.2.trans hdata⟩

end VG.Proof.Rc4.AArch64
