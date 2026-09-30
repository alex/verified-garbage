import VerifiedGarbage.Proof.X448.AArch64.Copy
import VerifiedGarbage.Proof.X448.Pairs

/-!
# X448 on AArch64: decoding the u-coordinate

Untrusted: everything here is checked by Lean. Seven byte loads form each
pair of 28-bit limbs; no load extends past the 56-byte input.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

/-- Accumulate one byte from the high end of a seven-byte chunk. -/
def decodeByte (i j : Nat) : List Instr :=
  [.lsl .x .x4 .x4 8, .ldrb .x7 .x2 (7 * i + (6 - j)), .add .x .x4 .x4 .x7]

theorem decodeByte_ok {s : State} {p : Addr} {i j : Nat}
    (hp : s.gpr .x2 = p) (hi : i < 8) (hb : (s.gpr .x4).toNat < 2 ^ 48)
    (hr : InRegions (s.rd ++ s.wr) (off p (7 * i + (6 - j))) 1) :
    WP isa (.block (decodeByte i j)) s fun t =>
      (t.gpr .x4).toNat = 256 * (s.gpr .x4).toNat + (s.mem (off p (7 * i + (6 - j)))).toNat ∧
      t.mem = s.mem ∧ Keeps [.x4, .x5, .x7] s t := by
  have byteb := (s.mem (off p (7 * i + (6 - j)))).isLt
  have mulb : (s.gpr .x4).toNat * 256 < 2 ^ 64 := by omega
  have enc : (7 * i + (6 - j)) % 1 = 0 ∧ 7 * i + (6 - j) < 4096 := by omega
  apply WP.of_runBlock
  simp only [decodeByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, hp,
    State.load, hr, read1_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, Nat.shiftLeft_eq]
    change (((s.gpr .x4).toNat * 256) % 2 ^ 64 +
      ((s.mem (off p (7 * i + (6 - j)))).toNat % 2 ^ 32) % 2 ^ 64) % 2 ^ 64 = _
    rw [Nat.mod_eq_of_lt mulb, Nat.mod_eq_of_lt (by omega : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 32),
      Nat.mod_eq_of_lt (by omega : (s.mem (off p (7 * i + (6 - j)))).toNat < 2 ^ 64)]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def readSeven (i : Nat) : List Instr :=
  [.movz .x .x4 0 0] ++ (List.range 7).flatMap (decodeByte i)

theorem readSevenInit_ok (s : State) :
    WP isa (.block [.movz .x .x4 0 0]) s fun t =>
      (t.gpr .x4).toNat = 0 ∧ t.mem = s.mem ∧ Keeps [.x4, .x8] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, Size.bits,
    Nat.reduceMul, Nat.reduceLT, ite_true, BitVec.shiftLeft_zero,
    RegUpd.gpr_write_self, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, ite_false]

theorem readSeven_ok {s : State} {p : Addr} {i : Nat} (hp : s.gpr .x2 = p) (hi : i < 8)
    (hr : ∀ j < 7, InRegions (s.rd ++ s.wr) (off p (7 * i + j)) 1) :
    WP isa (.block (readSeven i)) s fun t =>
      (t.gpr .x4).toNat = chunk s.mem p i ∧ t.mem = s.mem ∧ Keeps [.x4, .x5, .x7, .x8] s t := by
  rw [readSeven, WP.block_append_iff]
  refine WP.mono (readSevenInit_ok s) fun t ⟨tz, tm, tk⟩ => ?_
  let inv := fun n (u : State) =>
    (u.gpr .x4).toNat = suffix s.mem p i n ∧ u.mem = s.mem ∧ Keeps [.x4, .x5, .x7] t u
  have step : ∀ n u, n < 7 → inv n u → WP isa (.block (decodeByte i n)) u (inv (n + 1)) := by
    intro n u hn ⟨uv, um, uk⟩
    have up : u.gpr .x2 = p := (uk.1 _ (by decide)).trans ((tk.1 _ (by decide)).trans hp)
    have ub : (u.gpr .x4).toNat < 2 ^ 48 := by
      rw [uv]
      have h := suffix_bound s.mem p i n
      have hpow : 256 ^ n ≤ 256 ^ 6 := Nat.pow_le_pow_right (by decide) (by omega)
      exact Nat.lt_of_lt_of_le h hpow
    have ur : InRegions (u.rd ++ u.wr) (off p (7 * i + (6 - n))) 1 := by
      rw [uk.2.1, uk.2.2, tk.2.1, tk.2.2]; exact hr _ (by omega)
    refine WP.mono (decodeByte_ok up hi ub ur) fun v ⟨vv, vm, vk⟩ => ⟨?_, vm.trans um, uk.trans vk⟩
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

end VG.Proof.X448.AArch64
