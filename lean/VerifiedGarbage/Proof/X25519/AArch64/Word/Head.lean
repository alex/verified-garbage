import VerifiedGarbage.Proof.X25519.AArch64.Word.Memory
import Mathlib.Tactic.Tauto

/-! Load a scalar bit and turn the old/new swap XOR into a selection mask. -/
namespace VG.Proof.X25519.AArch64.Word
open VG VG.AArch64 VG.Impl.Ed25519.AArch64
open VG.Proof.Ed25519.AArch64
open VG.Proof.Ed25519.Word64

abbrev bitOffset := VG.Impl.X25519.AArch64.Word.BITS

theorem bitOffset_lt : bitOffset + 255 < 4096 := by decide

theorem bitAddress (base : Addr) (i : Nat) :
    base + BitVec.ofNat 64 i + BitVec.ofNat 64 bitOffset = off base (bitOffset+i) := by
  rw [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat, Nat.add_comm]

theorem loadBit_ok {base : Addr} {s : State} (hs : Scratch s base) {i kt : Nat}
    (hi : i < 255) (hkt : kt ≤ 1) (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 kt) :
    WP isa (.block [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19,
      .ldrb .x2 .x8 bitOffset]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x2 = BitVec.ofNat 64 kt ∧
      Keeps [.x19,.x8,.x2] s t := by
  have hdec : s.gpr .x19 - BitVec.ofNat 64 1 = BitVec.ofNat 64 i := by
    rw [hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  have hpre : WP isa (.block [.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19]) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x8 = base + BitVec.ofNat 64 i ∧
      Keeps [.x19,.x8] s t := by
    apply WP.of_runBlock
    simp only [runBlock_cons, runStep_some, runBlock_nil, exec_subImm_x (d := .x19) (n := .x19) (imm := 1) (by decide),
      exec_add, read_x, RegUpd.gpr_write, BitVec.setWidth_eq, hdec, hs.x0,
      ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
    refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]
  change WP isa (.block (([.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19] : List Instr) ++
    [.ldrb .x2 .x8 bitOffset])) s _
  rw [WP.block_append_iff]
  refine WP.mono hpre fun t ⟨ht, ha, hk⟩ => ?_
  have hr : InRegions (t.rd ++ t.wr) (t.gpr .x8 + BitVec.ofNat 64 bitOffset) 1 := by
    rw [ha, bitAddress]
    exact ⟨⟨base,4096⟩, List.mem_append_right _ (hk.wr ▸ hs.wr),
      Offset.contains_base base (d := bitOffset+i) (n := 1) (by have := bitOffset_lt; omega) (by have := bitOffset_lt; omega)⟩
  apply WP.of_runBlock
  have he := VG.Proof.X25519.AArch64.exec_ldrb (s := t) (t := .x2) (n := .x8)
    (off := bitOffset) (by decide) hr
  rw [runBlock_cons, he, runStep_some]
  have hv : ((t.mem.read (t.gpr .x8 + BitVec.ofNat 64 bitOffset) 1).setWidth 32).setWidth 64 =
      BitVec.ofNat 64 kt := by
    rw [ha, bitAddress, VG.Proof.X25519.AArch64.read1_toNat, hk.mem, hb]
    rcases (by omega : kt=0 ∨ kt=1) with rfl | rfl <;> rfl
  simp only [runBlock_nil, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (hk.mono (by decide)).trans ?_⟩
  · rw [RegUpd.gpr_write_of_ne _ _ _ (by decide), ht]
  · exact RegUpd.gpr_write_self _ _ _ _ |>.trans hv
  · refine ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩
    exact RegUpd.gpr_write_of_ne _ _ _ (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; tauto)


theorem storeSwap_ok {base : Addr} {s : State} (hs : Scratch s base) :
    WP isa (.block [VG.Impl.Ed25519.AArch64.st .x2 768]) s fun t =>
      LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
      word t.mem base 768 = s.gpr .x2 ∧ t.gpr = s.gpr := by
  refine WP.block_cons_iff.mpr ⟨_, store_sc hs (d := 768) (by decide) (by decide) .x2, WP.block_nil ?_⟩
  exact ⟨⟨fun _ _ _ => rfl, rfl, rfl, rfl,
    (writeW_outside s.mem base (s.gpr .x2) (by decide : 768+8<2^64)).mono (by decide) (by decide)⟩,
    env_swap_store _ _ _, Mem.readW_writeW_self64 _ _ _, rfl⟩

theorem swapMask_ok {s : State} {sw kt : Nat} (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (h3 : s.gpr .x3 = BitVec.ofNat 64 sw) (h2 : s.gpr .x2 = BitVec.ofNat 64 kt) :
    WP isa (.block [.logic .eor .x .x3 .x3 .x2, .movz .x .x10 0 0,
      .sub .x .x3 .x10 .x3]) s fun t =>
      t.gpr .x3 = mask ((sw ^^^ kt) == 1) ∧ Keeps [.x3,.x10] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil,
    VG.Proof.X25519.AArch64.exec_eor_x, VG.Proof.X25519.AArch64.exec_movz,
    VG.Proof.X25519.AArch64.exec_sub_x, RegUpd.gpr_write, BitVec.setWidth_eq,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [h3, h2, VG.Proof.X25519.AArch64.ofNat_xor hsw hkt]
    exact VG.Proof.X25519.AArch64.maskB_of (VG.Proof.X25519.AArch64.xor_le hsw hkt)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]


theorem prefix_ok {base : Addr} {s : State} (hs : Scratch s base) {i sw kt : Nat}
    (hi : i < 255) (hsw : sw ≤ 1) (hkt : kt ≤ 1)
    (hc : s.gpr .x19 = BitVec.ofNat 64 (i+1))
    (hswap : word s.mem base 768 = BitVec.ofNat 64 sw)
    (hb : s.mem (off base (bitOffset+i)) = BitVec.ofNat 8 kt) :
    WP isa (.block VG.Impl.X25519.AArch64.Word.stepPrefix) s fun t =>
      LoopKeep base s t ∧ env t.mem base = env s.mem base ∧
      t.gpr .x19 = BitVec.ofNat 64 i ∧ t.gpr .x3 = mask ((sw ^^^ kt) == 1) ∧
      word t.mem base 768 = BitVec.ofNat 64 kt := by
  change WP isa (.block (([.subImm .x .x19 .x19 1, .add .x .x8 .x0 .x19,
    .ldrb .x2 .x8 bitOffset] : List Instr) ++
    ([VG.Impl.Ed25519.AArch64.ld .x3 768] ++
    ([VG.Impl.Ed25519.AArch64.st .x2 768] ++
    [.logic .eor .x .x3 .x3 .x2, .movz .x .x10 0 0, .sub .x .x3 .x10 .x3])))) s _
  rw [WP.block_append_iff]
  refine WP.mono (loadBit_ok hs hi hkt hc hb) fun a ⟨ac, ak, ka⟩ => ?_
  have kla : LoopKeep base s a := LoopKeep.of_keeps ka (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (ld_ok (kla.scratch hs) (d := 768) (by decide) (by decide) .x3)
    fun b ⟨bs, kb⟩ => ?_
  have klb : LoopKeep base s b := kla.trans (LoopKeep.of_keeps kb (by decide))
  rw [WP.block_append_iff]
  refine WP.mono (storeSwap_ok (klb.scratch hs)) fun c ⟨klc, ec, sc, gc⟩ => ?_
  have ck : c.gpr .x2 = BitVec.ofNat 64 kt := by rw [gc, kb.gpr _ (by decide), ak]
  have cs : c.gpr .x3 = BitVec.ofNat 64 sw := by rw [gc, bs, ka.mem, hswap]
  refine WP.mono (swapMask_ok hsw hkt cs ck) fun t ⟨tm, km⟩ => ?_
  refine ⟨(klb.trans klc).trans (LoopKeep.of_keeps km (by decide)), ?_, ?_, tm, ?_⟩
  · rw [km.mem, ec, kb.mem, ka.mem]
  · rw [km.gpr _ (by decide), gc, kb.gpr _ (by decide), ac]
  · rw [km.mem, sc, kb.gpr _ (by decide), ak]

end VG.Proof.X25519.AArch64.Word
