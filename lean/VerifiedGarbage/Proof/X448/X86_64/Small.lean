import VerifiedGarbage.Proof.X448.X86_64.Columns

/-!
# X448 on x86-64: multiplication by a24

Each limb is multiplied by 39081 before the common carry passes reduce the
result.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

theorem smallStep_ok {s : State} {base : Addr} (hs : Scr s base) {a i : Nat}
    (ha : Slot a) (hi : i < 16) (hc : (s.gpr .rcx).toNat = 39081) :
    WP isa (.block [.mov .rax (.mem (sc (a + 8 * i))), .mul .rcx,
      .store (sc (TMP + 8 * i)) .rax]) s fun t =>
      t.mem = s.mem.writeW (off base (TMP + 8 * i)) (BitVec.ofNat 64 (39081 * limbs s.mem base a i)) ∧
      Keeps [.rax, .rdx] s t := by
  have l := hs.read (d := a + 8 * i) (n := 8) (by change a + 128 ≤ 3584 at ha; omega)
  have w := hs.write (d := TMP + 8 * i) (n := 8) (by simp only [TMP]; omega)
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execMul, ea_sc,
    State.load64, State.store64, RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.mem_setReg,
    RegUpd.mem_setFlags, RegUpd.wr_setReg, RegUpd.wr_setFlags, hs.rdi, l, w,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [hc, Nat.mul_comm _ 39081]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr.1, hr.2, ite_false]

theorem smallInit_ok (s : State) :
    WP isa (.block [.mov32 .rcx (.imm 39081)]) s fun t =>
      (t.gpr .rcx).toNat = 39081 ∧ t.mem = s.mem ∧ Keeps [.rcx] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg_self, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  exact RegUpd.gpr_setReg_of_ne _ _ hr

theorem mulSmall_ok {s : State} {base : Addr} (hs : Scr s base) {o a : Nat}
    (ho : Slot o) (ha : Slot a) (ab : Bounded s.mem base a) :
    WP isa (.block (mulSmall o a)) s fun t => Op base o s t ∧ Bounded t.mem base o ∧
      F t.mem base o = Spec.X448.a24 * F s.mem base a := by
  let f := fun i => 39081 * limbs s.mem base a i
  have fb : ∀ i < 16, f i < 2 ^ 62 := by
    intro i hi
    have h := Nat.mul_le_mul_left 39081 (Nat.le_of_lt (ab i hi))
    have hr : 39081 * radix < 2 ^ 62 := by decide
    exact Nat.lt_of_le_of_lt h hr
  refine WP.mono (columns_normalize hs ho fb ?_) fun t ⟨op, tb, tv⟩ => ⟨op, tb, toFe_a24 ?_⟩
  · rw [WP.block_append_iff]
    refine WP.mono (smallInit_ok s) fun t ⟨tc, tm, tk⟩ => ?_
    have ts := hs.of_keeps tk (by decide)
    refine WP.mono (columns_ok ts (by decide : Reg.rdi ∉ [Reg.rax, Reg.rdx]) fb ?_) fun u ⟨uf, um, uk⟩ => ?_
    · intro i hi u us um uk
      have uc : (u.gpr .rcx).toNat = 39081 := by rw [uk.1 _ (by decide), tc]
      refine WP.mono (smallStep_ok us ha hi uc) fun v ⟨vm, vk⟩ => ⟨?_, vk⟩
      rw [input_limb um ha hi, tm] at vm
      exact vm
    · refine ⟨uf, ?_, (tk.mono ?_).trans (uk.mono ?_)⟩
      · rw [← tm]; exact um
      · intro r hr; simp only [List.mem_singleton] at hr; subst r; decide
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl <;> decide
  · rw [tv, valN_scale]

end VG.Proof.X448.X86_64
