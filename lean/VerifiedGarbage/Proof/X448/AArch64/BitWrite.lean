import VerifiedGarbage.Proof.X448.AArch64.Iter
import VerifiedGarbage.Proof.X448.Bytes

/-!
# X448 on AArch64: expanding scalar bytes

Untrusted: everything here is checked by Lean. Each byte is expanded into
eight bytes holding its bits, through public offsets in the working space.
-/

namespace VG.Proof.X448.AArch64

open VG VG.AArch64 VG.Impl.X448.AArch64

theorem sub_toNat_lt_one (x a : Addr) : (x - a).toNat < 1 ↔ x = a := by
  constructor
  · intro h
    have h0 : x - a = 0 := BitVec.eq_of_toNat_eq (by rw [show (0 : Addr).toNat = 0 from rfl]; omega)
    calc x = x - a + a := (BitVec.sub_add_cancel x a).symm
      _ = a := by rw [h0]; exact BitVec.zero_add a
  · rintro rfl; simp

theorem writeW8_apply (m : Mem) (a x : Addr) (v : BitVec 8) :
    (m.writeW a v) x = if x = a then v else m x := by
  by_cases h : x = a
  · subst h; simp [Mem.writeW, Mem.write]
  · simp only [Mem.writeW, Mem.write, Nat.reduceDiv, sub_toNat_lt_one, h, ite_false]

theorem off_eq_iff (base : Addr) {d e : Nat} (hd : d < 2 ^ 64) (he : e < 2 ^ 64) :
    off base d = off base e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (fun x => ofs base x) h
    simp only [ofs_off' base hd, ofs_off' base he] at this
    exact this
  · intro h; rw [h]

theorem writeW8_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 8) (hd : d < 2 ^ 64) {x : Addr}
    (hx : ofs base x ≠ d) : (m.writeW (off base d) v) x = m x := by
  rw [writeW8_apply, ite_eq_right_iff.mpr]
  intro h; subst h; exact absurd (ofs_off' base hd) hx

theorem write1_eq (m : Mem) (p : Addr) (v : BitVec 8) : m.write p 1 v = m.writeW p v := by
  simp only [Mem.writeW, BitVec.setWidth_eq]

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    (((b.setWidth 64 >>> j) &&& (1 : BitVec 64)).setWidth 32).setWidth 8 =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

def bitJ (j : Nat) : List Instr :=
  [.lsr .x .x5 .x4 j, .logic .and .x .x5 .x5 .x8, .strb .x5 .x11 (BITS + j)]

theorem bitJ_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 56)
    (hp : s.gpr .x11 = off base (8 * i)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) {j : Nat} (hj : j < 8) :
    WP isa (.block (bitJ j)) s fun t =>
      t.mem = s.mem.writeW (off base (BITS + (8 * i + j)))
        (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧ Keeps [.x5] s t := by
  have w := hs.write (d := BITS + (8 * i + j)) (n := 1) (by simp only [BITS]; omega)
  have enc : (BITS + j) % 1 = 0 ∧ BITS + j < 4096 := by simp only [BITS]; omega
  have shift : j < 64 := by omega
  apply WP.of_runBlock
  simp only [bitJ, runBlock_cons, runStep_some, runBlock_nil, exec, State.read, Size.bits,
    BitVec.setWidth_eq, shift, addr, enc, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.wr_write, hp, hc, ha, off, Offset.add_add,
    show 8 * i + (BITS + j) = BITS + (8 * i + j) by omega,
    State.store, w, ite_true, ite_false, reduceCtorEq,
    Option.bind_some, write1_eq, bit_byte b j hj, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, (fun r hr => ?_), rfl, rfl⟩
  simp only [List.mem_singleton] at hr
  simp only [RegUpd.gpr_write, hr, ite_false]

/-- Expanding eight bits preserves each byte already written. -/
theorem byteBits_ok {s : State} {base : Addr} (hs : Scr s base) {i : Nat} (hi : i < 56)
    (hp : s.gpr .x11 = off base (8 * i)) (hc : s.gpr .x8 = 1)
    {b : BitVec 8} (ha : s.gpr .x4 = b.setWidth 64) :
    WP isa (.block ((List.range 8).flatMap bitJ)) s fun t =>
      (∀ j < 8, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
      Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t := by
  let inv := fun n (t : State) =>
    (∀ j < n, t.mem (off base (BITS + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) ∧
    Outside base (BITS + 8 * i) 8 s.mem t.mem ∧ Keeps [.x5] s t
  have step : ∀ n t, n < 8 → inv n t → WP isa (.block (bitJ n)) t (inv (n + 1)) := by
    intro n t hn ⟨tf, tm, tk⟩
    refine WP.mono (bitJ_ok (hs.of_keeps tk (by decide)) hi
      ((tk.1 _ (by decide)).trans hp) ((tk.1 _ (by decide)).trans hc)
      ((tk.1 _ (by decide)).trans ha) hn) fun u ⟨um, uk⟩ => ?_
    refine ⟨?_, tm.trans ?_, tk.trans uk⟩
    · intro j hj
      rw [um, writeW8_apply]
      have eq : off base (BITS + (8 * i + j)) = off base (BITS + (8 * i + n)) ↔ j = n := by
        rw [off_eq_iff base (by simp only [BITS]; omega) (by simp only [BITS]; omega)]
        omega
      by_cases he : j = n
      · rw [ite_eq_left (eq.mpr he), he]
      · rw [ite_eq_right (fun h => he (eq.mp h))]; exact tf j (by omega)
    · intro x hx
      rw [um]
      exact writeW8_outside _ _ _ (by simp only [BITS]; omega) (by omega)
  exact wp_range_flatMap (M := isa) (N := 8) inv step 8 (by decide) s
    ⟨fun _ hj => by omega, Outside.refl _ _ _ _, Keeps.refl _ _⟩

end VG.Proof.X448.AArch64
