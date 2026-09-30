import VerifiedGarbage.Proof.X448.AArch64.Columns

/-!
# X448 on AArch64: multiplication by a24

Untrusted: everything here is checked by Lean. Each limb is multiplied by
39081 before the common carry passes reduce the result.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (ha8 : a % 8 = 0) (hi : i < 16) (hc : (s.gpr .x6).toNat = 39081) :
    WP isa (.block [ld .x4 (a + 8 * i), .mul .x .x4 .x4 .x6, st .x4 (TMP + 8 * i)]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i)) (BitVec.ofNat 64 (39081 * limbs s.mem base a i)) ∧
      Keeps [.x4, .x5] s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  have ae : (a + 8 * i) % 8 = 0 ∧ a + 8 * i < 32768 := by
    change a + 128 ≤ 3584 at ha; omega
  have oe : (TMP + 8 * i) % 8 = 0 ∧ TMP + 8 * i < 32768 := by simp only [TMP]; omega
  apply WP.of_runBlock
  simp only [ld, st, runBlock_cons, runStep_some, runBlock_nil, exec, addr, Size.bytes,
    State.read, State.load, State.store, RegUpd.gpr_write, RegUpd.mem_write,
    RegUpd.wr_write, BitVec.setWidth_eq, ae, oe, and_self, hs.x3, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, read8_eq, write8_eq,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · apply congrArg (s.mem.writeW (off base (TMP + 8 * i)))
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_mul, hc, Nat.mul_comm _ 39081, BitVec.toNat_ofNat]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem smallInit_ok (s : State) :
    WP isa (.block [.movz .x .x6 39081 0]) s fun t =>
      (t.gpr .x6).toNat = 39081 ∧ t.mem = s.mem ∧ Keeps [.x6] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_write_of_ne _ _ _ hr

theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ho8 : o % 8 = 0) (ha : Slot a) (ha8 : a % 8 = 0) (ab : Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix < 2 ^ 62 := by decide
    exact Nat.lt_of_le_of_lt h hr
  refine WP.mono (columns_normalize hs ho ho8 fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (columns_ok ts (by decide : Reg.x3 ∉ [Reg.x4, Reg.x5] ∧ Reg.x12 ∉ [Reg.x4, Reg.x5]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .x6).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (smallStep_ok us ha ha8 hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, valN_scale]

end VG.Proof.X448.AArch64
