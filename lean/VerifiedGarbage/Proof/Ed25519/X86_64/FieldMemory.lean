import VerifiedGarbage.Impl.Ed25519.X86_64.Field
import VerifiedGarbage.Proof.X25519.X86_64.Env

/-! Untrusted: field constants and copies, with the surrounding memory preserved. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Impl.X25519.X86_64 (loads store4)
open VG.Proof.X25519.X86_64 (Scr Outside Op clob F Keeps val4 fe ea_sc readSrc_sc store4_ok fe_st4 st4_outside)

theorem limbs_nat (x : Nat) (hx : x < 2 ^ 256) :
    val4 (BitVec.ofNat 64 x) (BitVec.ofNat 64 (x / 2 ^ 64))
      (BitVec.ofNat 64 (x / 2 ^ 128)) (BitVec.ofNat 64 (x / 2 ^ 192)) = x := by
  simp only [val4, BitVec.toNat_ofNat]
  omega

theorem constWords_ok (s : State) (v : Spec.X25519.Fe) :
    WP isa (.block (constWords v)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = v.val ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  apply WP.of_runBlock
  simp only [constWords, runBlock_cons, runStep_some, runBlock_nil, exec, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨limbs_nat _ (by have := v.isLt; simp only [Spec.X25519.P] at this; omega),
    fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, ite_false]

theorem constField_op {s : State} {base : Addr} (hs : Scr s base) (o : Slot) (v : Spec.X25519.Fe) :
    WP isa (.block (constField o v)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = v := by
  rw [constField, WP.block_append_iff]
  refine WP.mono (constWords_ok s v) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (o := offset o)
    (by simp only [offset]; omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  have op : Op base (offset o) s u :=
    ⟨fun r hr => (hg r).trans ((hk.mono (by decide)).1 r hr), hrd.trans hk.2.2.1,
      hwr.trans hk.2.2.2, by rw [hm, hk.2.1]; exact st4_outside _ _ (by simp only [offset]; omega) _ _ _ _⟩
  refine ⟨op, ?_⟩
  rw [F, hm, fe_st4 _ _ (by simp only [offset]; omega), hv, Proof.X25519.toFe_self]

theorem loadsField_ok {s : State} {base : Addr} (hs : Scr s base) (a : Slot) :
    WP isa (.block (loads (offset a) .r8 .r9 .r10 .r11)) s fun t =>
      val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11) = fe s.mem base (offset a) ∧
      Keeps [.r8, .r9, .r10, .r11] s t := by
  have hr (d : Nat) (hd : d + 8 ≤ 4096) : InRegions (s.rd ++ s.wr) (Proof.X25519.X86_64.off base d) 8 :=
    ⟨_, List.mem_append_right _ hs.wr, Proof.X25519.X86_64.contains_sc hd⟩
  apply WP.of_runBlock
  simp only [loads, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_sc, RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    hs.rdi, hr (offset a) (by simp only [offset]; omega),
    hr (offset a + 8) (by simp only [offset]; omega),
    hr (offset a + 16) (by simp only [offset]; omega),
    hr (offset a + 24) (by simp only [offset]; omega),
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, fun r h => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_setReg, h.1, h.2.1, h.2.2.1, h.2.2.2, ite_false]

theorem copyField_op {s : State} {base : Addr} (hs : Scr s base) (o a : Slot) :
    WP isa (.block (copyField o a)) s fun t =>
      Op base (offset o) s t ∧ F t.mem base (offset o) = F s.mem base (offset a) := by
  rw [copyField, WP.block_append_iff]
  refine WP.mono (loadsField_ok hs a) fun t ⟨hv, hk⟩ => ?_
  refine WP.mono (store4_ok (hs.of_keeps hk (by decide)) (o := offset o)
    (by simp only [offset]; omega)) fun u ⟨hm, hg, hrd, hwr⟩ => ?_
  have op : Op base (offset o) s u :=
    ⟨fun r hr => (hg r).trans ((hk.mono (by decide)).1 r hr), hrd.trans hk.2.2.1,
      hwr.trans hk.2.2.2, by rw [hm, hk.2.1]; exact st4_outside _ _ (by simp only [offset]; omega) _ _ _ _⟩
  refine ⟨op, ?_⟩
  rw [F, hm, fe_st4 _ _ (by simp only [offset]; omega), hv]

end VG.Proof.Ed25519.X86_64
