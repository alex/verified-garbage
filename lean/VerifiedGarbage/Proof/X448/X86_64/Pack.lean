import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.X448.Encoding

/-!
# X448 on x86-64: writing seven-byte chunks

Each pair of bounded limbs is combined in a register and written with seven
byte stores.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

abbrev packed (m : Mem) (base : Addr) (i : Nat) : Nat :=
  limbs m base X2 (2 * i) + radix * limbs m base X2 (2 * i + 1)

theorem packed_bound {m : Mem} {base : Addr} (hb : Bounded m base X2) {i : Nat} (hi : i < 8) :
    packed m base i < 2 ^ 56 := by
  have h0 := hb (2 * i) (by omega)
  have h1 := hb (2 * i + 1) (by omega)
  simp only [packed, radix] at h0 h1 ⊢
  omega

def packHead (i : Nat) : List Instr :=
  [.mov32 .rcx (.imm 0x10000000), .mov .rax (.mem (sc (X2 + 16 * i + 8))),
    .mul .rcx, .alu .add .rax (.mem (sc (X2 + 16 * i)))]

theorem packHead_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) :
    WP isa (.block (packHead i)) s fun t =>
      (t.gpr .rax).toNat = packed s.mem base i ∧ t.mem = s.mem ∧ Keeps [.rax, .rcx, .rdx] s t := by
  have lo := hs.read (d := X2 + 16 * i) (n := 8) (by simp only [X2, slot]; omega)
  have lh := hs.read (d := X2 + 16 * i + 8) (n := 8) (by simp only [X2, slot]; omega)
  have b := packed_bound hb hi
  have he0 : X2 + 16 * i = X2 + 8 * (2 * i) := by omega
  have he1 : X2 + 16 * i + 8 = X2 + 8 * (2 * i + 1) := by omega
  apply WP.of_runBlock
  simp only [packHead, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, readSrc32,
    State.setReg32, State.load64, execMul, execAlu, ea_sc, hs.rdi, lo, lh,
    RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags,
    RegUpd.mem_setReg, RegUpd.mem_setFlags, RegUpd.rd_setReg, RegUpd.rd_setFlags,
    RegUpd.wr_setReg, RegUpd.wr_setFlags, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, rfl, (fun r hr => ?_), rfl, rfl⟩
  · rw [he1, he0, BitVec.toNat_add, BitVec.toNat_ofNat]
    change (limbs s.mem base X2 (2 * i + 1) * radix % 2 ^ 64 +
      limbs s.mem base X2 (2 * i)) % 2 ^ 64 = _
    change limbs s.mem base X2 (2 * i) + radix * limbs s.mem base X2 (2 * i + 1) < _ at b
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.add_comm _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2, ite_false]

def packByte (i j : Nat) : List Instr :=
  [.store8 (at_ .rsi (7 * i + j)) .rax, .shift .shr .rax 8]

theorem packByte_ok {s : State} {p : Addr} {i j : Nat} (hp : s.gpr .rsi = p)
    (hw : InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packByte i j)) s fun t =>
      (t.gpr .rax).toNat = (s.gpr .rax).toNat / 256 ∧
      t.mem = s.mem.writeW (off p (7 * i + j)) (BitVec.ofNat 8 (s.gpr .rax).toNat) ∧ Keeps [.rax] s t := by
  apply WP.of_runBlock
  simp only [packByte, runBlock_cons, runStep_some, runBlock_nil, exec, execShift,
    State.store8, State.ea, at_, BitVec.ofInt_natCast, hp, hw,
    show 1 ≤ (8 : Nat) ∧ 8 ≤ 63 by decide, and_self, ite_true, RegUpd.gpr_setReg,
    RegUpd.gpr_setFlags, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · rw [BitVec.ofNat_toNat]; rfl
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, hr, ite_false]

theorem writeSeven_ok {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .rsi = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block ((List.range 7).flatMap (packByte i))) s fun t =>
      (∀ j < 7, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .rax).toNat / 256 ^ j)) ∧
      Outside p (7 * i) 7 s.mem t.mem ∧ Keeps [.rax] s t := by
  let inv := fun n (t : State) =>
    (t.gpr .rax).toNat = (s.gpr .rax).toNat / 256 ^ n ∧
    (∀ j < n, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .rax).toNat / 256 ^ j)) ∧
    Outside p (7 * i) n s.mem t.mem ∧ Keeps [.rax] s t
  have st : ∀ n t, n < 7 → inv n t → WP isa (.block (packByte i n)) t (inv (n + 1)) := by
    intro n t hn ⟨ta, tf, tm, tk⟩
    refine WP.mono (packByte_ok ((tk.1 _ (by decide)).trans hp)
      (by rw [tk.2.2]; exact hw n hn)) fun u ⟨ua, um, uk⟩ => ?_
    refine ⟨?_, ?_, ?_, tk.trans uk⟩
    · rw [ua, ta, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    · intro j hj
      rw [um, writeW8_apply]
      simp only [off_eq_iff p (d := 7 * i + j) (e := 7 * i + n) (by omega) (by omega)]
      by_cases h : j = n
      · rw [ite_eq_left (by omega), h, ta]
      · rw [ite_eq_right (by omega)]; exact tf j (by omega)
    · intro q hq
      rw [um, writeW8_outside _ _ _ (by omega) (by omega)]
      exact tm q (by omega)
  refine WP.mono (wp_range_flatMap (M := isa) (N := 7) inv st 7 (by decide) s
    ⟨by rw [Nat.pow_zero, Nat.div_one], fun _ h => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩)
    fun t ⟨_, tf, tm, tk⟩ => ⟨tf, tm, tk⟩

end VG.Proof.X448.X86_64
