import VerifiedGarbage.Impl.Ed25519.AArch64.PointLoop
import VerifiedGarbage.Proof.Ed25519.AArch64.Points
import VerifiedGarbage.Proof.Ed25519.ScalarMul

/-! Sixteen exact doublings, preserving the saved accumulator. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64


structure DoubleKeep (base : Addr) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x1 → r ∉ clob → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base 64 704 s.mem t.mem

theorem DoubleKeep.refl (base : Addr) (s : State) : DoubleKeep base s s :=
  ⟨fun _ _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩

theorem DoubleKeep.trans {base : Addr} {s t u : State} (h : DoubleKeep base s t)
    (k : DoubleKeep base t u) : DoubleKeep base s u :=
  ⟨fun r hr hc => (k.gpr r hr hc).trans (h.gpr r hr hc), k.rd.trans h.rd,
    k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem DoubleKeep.scratch {base : Addr} {s t : State} (h : DoubleKeep base s t) (hs : Scr s base) :
    Scr t base := ⟨(h.gpr _ (by decide) (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem point_counter_nonzero : ∀ n < 16,
    (BitVec.ofNat 64 n != 0) = decide (n ≠ 0) := by decide

theorem doubleDec_ok (s : State) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) :
    WP isa (.block [.subImm .x .x1 .x1 1]) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧ Keeps [.x1] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x,
    show (1 : Nat) < 4096 from by decide, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  · rw [RegUpd.gpr_write_self, BitVec.setWidth_eq, hc, BitVec.ofNat_add, BitVec.add_sub_cancel]
  · exact RegUpd.gpr_write_of_ne _ _ _ (by simpa only [List.mem_singleton] using hr)

theorem doubleBody_ok {s : State} {base : Addr} (hs : Scr s base) (n : Nat)
    (hc : s.gpr .x1 = BitVec.ofNat 64 (n + 1)) (hd : env s.mem base 16 = Spec.Ed25519.d) :
    WP isa (.block doubleBody) s fun t =>
      t.gpr .x1 = BitVec.ofNat 64 n ∧
      point (env t.mem base) 0 1 2 3 =
        Spec.Ed25519.pointAdd (point (env s.mem base) 0 1 2 3) (point (env s.mem base) 0 1 2 3) ∧
      (∀ i : Slot, 16 ≤ i.val → env t.mem base i = env s.mem base i) ∧ DoubleKeep base s t := by
  rw [doubleBody, WP.block_append_iff]
  refine WP.mono (pointDouble_ok hs hd) fun t ⟨hk, hv, hi⟩ => ?_
  refine WP.mono (doubleDec_ok t n ((hk.gpr _ (by decide)).trans hc)) fun u ⟨hcu, ku⟩ => ?_
  refine ⟨hcu, ?_, ?_, ?_⟩
  · rw [ku.mem]; exact hv
  · rw [ku.mem]; exact hi
  · exact ⟨fun r hr hc => (ku.gpr r (by simpa using hr)).trans (hk.gpr r hc),
      ku.rd.trans hk.rd, ku.wr.trans hk.wr, ku.sp.trans hk.sp, by rw [ku.mem]; exact hk.mem⟩

end VG.Proof.Ed25519.AArch64
