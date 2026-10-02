import VerifiedGarbage.Proof.X448.X86_64.Copy
import VerifiedGarbage.Proof.X448.Pairs

/-!
# X448 on x86-64: decoding the u-coordinate

Seven byte loads form each pair of 28-bit limbs; no load extends past the
56-byte input.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
def decodeByte (i j : Nat) : List Instr :=
  [.mul .r9, .movzx8 .r8 (at_ .r10 (7 * i + (6 - j))), .alu .add .rax (.reg .r8)]

theorem decodeByte_ok {s : State} {p : Addr} {i j : Nat}
    (hp : s.gpr .r10 = p) (hc : (s.gpr .r9).toNat = 256) (hb : (s.gpr .rax).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (off p (7 * i + (6 - j))) 1) :
    WP isa (.block (decodeByte i j)) s fun t =>
      (t.gpr .rax).toNat = 256 * (s.gpr .rax).toNat + (s.mem (off p (7 * i + (6 - j)))).toNat ∧
      t.mem = s.mem ∧ Keeps [.rax, .rdx, .r8] s t := by
  have byteb := (s.mem (off p (7 * i + (6 - j)))).isLt
  have mulb : (s.gpr .rax).toNat * 256 < 2 ^ 64 := by omega
  apply WP.of_runBlock
  simp only [decodeByte, runBlock_cons, runStep_some, runBlock_nil, exec, execMul, execAlu, readSrc,
    State.load8, State.ea, at_, BitVec.ofInt_natCast, RegUpd.gpr_setReg, RegUpd.gpr_setFlags,
    RegUpd.gpr_arithFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags, RegUpd.wr_setReg,
    RegUpd.wr_setFlags, RegUpd.mem_setReg, RegUpd.mem_setFlags, hp, hr,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · rw [hc, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt mulb, Nat.mod_eq_of_lt (by omega : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 64)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

def readSeven (i : Nat) : List Instr :=
  [.mov32 .r9 (.imm 256), .mov32 .rax (.imm 0)] ++ (List.range 7).flatMap (decodeByte i)

theorem readSevenInit_ok (s : State) :
    WP isa (.block [.mov32 .r9 (.imm 256), .mov32 .rax (.imm 0)]) s fun t =>
      (t.gpr .rax).toNat = 0 ∧ (t.gpr .r9).toNat = 256 ∧ t.mem = s.mem ∧ Keeps [.rax, .r9] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, Option.map_some,
    State.setReg32, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem readSeven_ok {s : State} {p : Addr} {i : Nat} (hp : s.gpr .r10 = p)
    (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (off p (7 * i + j)) 1) :
    WP isa (.block (readSeven i)) s fun t =>
      (t.gpr .rax).toNat = chunk s.mem p i ∧ t.mem = s.mem ∧ Keeps [.rax, .rdx, .r8, .r9] s t := by
  rw [readSeven, WP.block_append_iff]
  refine WP.mono (readSevenInit_ok s) fun t ⟨tz, tc, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .rax).toNat = suffix s.mem p i n ∧ u.mem = s.mem ∧ Keeps [.rax, .rdx, .r8] t u
  have step : ∀ n u, n < 7 → inv n u → WP isa (.block (decodeByte i n)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr .r10 = p := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hp)
    have uc : (u.gpr .r9).toNat = 256 := by rw [uk.1 _ (by decide), tc]
    have ub : (u.gpr .rax).toNat < 2 ^ 48 := by
      rw [uv]
      have h := suffix_bound s.mem p i n
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (off p (7 * i + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega)
    refine WP.mono (decodeByte_ok up uc ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
    rw [vv, uv, um, suffix_succ _ _ _ hn]
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv step 7 (by decide) t
    ⟨tz, tm, Keeps.refl _ _⟩) fun u ⟨uv, um, uk⟩ => ⟨?_, um, ?_⟩
  · exact uv
  · refine (tk.mono ?_).trans (uk.mono ?_)
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;> decide

end VG.Proof.X448.X86_64
