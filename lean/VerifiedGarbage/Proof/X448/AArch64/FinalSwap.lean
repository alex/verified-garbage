import VerifiedGarbage.Proof.X448.AArch64.Iter

/-!
# X448 on AArch64: the swap after the ladder

The final swap bit selects the coordinates to be converted back to affine
form.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem mask_of : ∀ a < 2, BitVec.setWidth 64 (0 : BitVec 16) - BitVec.ofNat 64 a =
    mask (decide (a = 1)) := by decide

theorem swapMask_ok {s : State} {base : Addr} (hs : Scr s base) {sw : Nat} (hsw : sw < 2)
    (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block [ld .x5 SWAP, .movz .x .x6 0 0, .sub .x .x6 .x6 .x5]) s
      fun t => t.gpr .x6 = mask (decide (sw = 1)) ∧ t.mem = s.mem ∧ Keeps [.x5, .x6] s t := by
  have hr := hs.read (d := SWAP) (n := 8) (by decide)
  have enc : SWAP % 8 = 0 ∧ SWAP < 32768 := by decide
  have hw' : s.mem.readW (off base SWAP) 64 = BitVec.ofNat 64 sw := hw
  apply WP.of_runBlock
  simp only [ld, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    Size.bits, State.read, State.load, RegUpd.gpr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, enc, and_self,
    hs.x3, hr, read8_eq, hw', Nat.reduceMul, Nat.reduceLT, BitVec.shiftLeft_zero,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨mask_of sw hsw, trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem lastSwap_ok {s : State} {base : Addr} (hs : Scr s base) (hb : BoundedEnv s.mem base)
    {sw : Nat} (hsw : sw < 2) (hw : word s.mem base SWAP = BitVec.ofNat 64 sw) :
    WP isa (.block lastSwap) s fun t => Keep base s t ∧ BoundedEnv t.mem base ∧
      E t.mem base = opSwap 2 4 (decide (sw = 1)) (opSwap 1 3 (decide (sw = 1)) (E s.mem base)) := by
  rw [lastSwap, List.append_assoc, WP.block_append_iff]
  refine WP.mono (swapMask_ok hs hsw hw) fun t ⟨tc, tm, tk⟩ => ?_
  have kt : Keep base s t := ⟨tk.mono (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> decide), tm ▸ Outside2.refl _ _ _ _ _ _⟩
  refine WP.mono (swaps_ok (kt.scr hs) (tm ▸ hb) tc) fun u ⟨ku, bu, eu⟩ =>
    ⟨kt.trans ku, bu, by rw [eu, tm]⟩

end VG.Proof.X448.AArch64
