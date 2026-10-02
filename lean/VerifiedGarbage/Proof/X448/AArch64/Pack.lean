import VerifiedGarbage.Proof.X448.AArch64.Bits
import VerifiedGarbage.Proof.X448.Encoding

/-!
# X448 on AArch64: writing seven-byte chunks

Each pair of bounded limbs is combined in a register and written with seven
byte stores.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

abbrev packed (m : Mem) (base : Addr) (i : Nat) : Nat :=
  limbs m base X2 (2 * i) + radix * limbs m base X2 (2 * i + 1)

theorem packed_bound {m : Mem} {base : Addr} (hb : Bounded m base X2) {i : Nat} (hi : i < 8) :
    packed m base i < 2 ^ 56 := by
  have h0 := hb (2 * i) (by omega)
  have h1 := hb (2 * i + 1) (by omega)
  simp only [packed, radix] at h0 h1 ⊢
  omega

def packHead (i : Nat) : List Instr :=
  [ld .x4 (X2 + 16 * i + 8), .lsl .x .x4 .x4 28,
    ld .x5 (X2 + 16 * i), .add .x .x4 .x4 .x5]

theorem packHead_ok {s : State} {base : Addr} (hs : Scr s base) (hb : Bounded s.mem base X2)
    {i : Nat} (hi : i < 8) :
    WP isa (.block (packHead i)) s fun t =>
      (t.gpr .x4).toNat = packed s.mem base i ∧ t.mem = s.mem ∧ Keeps [.x4, .x6, .x5] s t := by
  have lo := hs.read (d := X2 + 16 * i) (n := 8) (by simp only [X2, slot]; omega)
  have lh := hs.read (d := X2 + 16 * i + 8) (n := 8) (by simp only [X2, slot]; omega)
  have b := packed_bound hb hi
  have he0 : X2 + 16 * i = X2 + 8 * (2 * i) := by omega
  have he1 : X2 + 16 * i + 8 = X2 + 8 * (2 * i + 1) := by omega
  have le : (X2 + 16 * i) % 8 = 0 ∧ X2 + 16 * i < 32768 := by simp only [X2, slot]; omega
  have he : (X2 + 16 * i + 8) % 8 = 0 ∧ X2 + 16 * i + 8 < 32768 := by simp only [X2, slot]; omega
  apply WP.of_runBlock
  simp only [packHead, ld, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Size.bytes, Nat.reduceLT, BitVec.setWidth_eq, addr, le, he, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hs.x3, State.load, lo, lh, read8_eq, ite_true, ite_false, reduceCtorEq,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, trivial, (fun r hr => ?_), rfl, rfl⟩
  · rw [he1, he0, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
    change (limbs s.mem base X2 (2 * i + 1) * radix % 2 ^ 64 +
      limbs s.mem base X2 (2 * i)) % 2 ^ 64 = _
    change limbs s.mem base X2 (2 * i) + radix * limbs s.mem base X2 (2 * i + 1) < _ at b
    rw [Nat.mul_comm, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    exact Nat.add_comm _ _
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_write, hr.1, hr.2.2, ite_false]

def packByte (i j : Nat) : List Instr :=
  [.strb .x4 .x1 (7 * i + j), .lsr .x .x4 .x4 8]

theorem packByte_ok {s : State} {p : Addr} {i j : Nat} (hp : s.gpr .x1 = p) (hi : i < 8) (hj : j < 7)
    (hw : InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block (packByte i j)) s fun t =>
      (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ∧
      t.mem = s.mem.writeW (off p (7 * i + j)) (BitVec.ofNat 8 (s.gpr .x4).toNat) ∧ Keeps [.x4] s t := by
  have enc : (7 * i + j) % 1 = 0 ∧ 7 * i + j < 4096 := by omega
  apply WP.of_runBlock
  simp only [packByte, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    Size.bits, Nat.reduceLT, BitVec.setWidth_eq, addr, enc, and_self,
    State.store, hp, hw, ite_true, Option.bind_some, write1_eq,
    RegUpd.gpr_write, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, (fun r hr => ?_), rfl, rfl⟩
  · rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  · apply congrArg (s.mem.writeW (off p (7 * i + j)))
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · simp only [List.mem_singleton] at hr
    simp only [RegUpd.gpr_write, hr, ite_false]

theorem writeSeven_ok {s : State} {p : Addr} {i : Nat} (hi : i < 8) (hp : s.gpr .x1 = p)
    (hw : ∀ j < 7, InRegions s.wr (off p (7 * i + j)) 1) :
    WP isa (.block ((List.range 7).flatMap (packByte i))) s fun t =>
      (∀ j < 7, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
      Outside p (7 * i) 7 s.mem t.mem ∧ Keeps [.x4] s t := by
  let inv := fun n (t : State) =>
    (t.gpr .x4).toNat = (s.gpr .x4).toNat / 256 ^ n ∧
    (∀ j < n, t.mem (off p (7 * i + j)) = BitVec.ofNat 8 ((s.gpr .x4).toNat / 256 ^ j)) ∧
    Outside p (7 * i) n s.mem t.mem ∧ Keeps [.x4] s t
  have st : ∀ n t, n < 7 → inv n t → WP isa (.block (packByte i n)) t (inv (n + 1)) := by
    intro n t hn ⟨ta, tf, tm, tk⟩
    refine WP.mono (packByte_ok ((tk.1 _ (by decide)).trans hp) hi hn
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

end VG.Proof.X448.AArch64
