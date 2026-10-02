import VerifiedGarbage.Impl.Ed25519.AArch64.Bits
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! Byte stores and expansion of one scalar byte into eight bits. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64 VG.Impl.Ed25519.AArch64

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

theorem bit_byte : ∀ b : BitVec 8, ∀ j < 8,
    ((((b.setWidth 64 >>> j) &&& BitVec.ofNat 64 1).setWidth 32).setWidth 8 : BitVec 8) =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide

theorem expandScalarBit_ok {s : State} {base : Addr} (hs : Scr s base)
    (i j : Nat) (hi : i < 64) (hj : j < 8)
    (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block (expandScalarBit j)) s fun t =>
      (∀ r, r ≠ .x2 → t.gpr r = s.gpr r) ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      t.mem = s.mem.writeW (off base (768 + (8 * i + j))) (BitVec.ofNat 8 ((b.toNat >>> j) &&& 1)) := by
  have hw : InRegions s.wr (off base (768 + (8 * i + j))) 1 :=
    ⟨_, hs.wr, Offset.contains_base _ (by omega) (by omega)⟩
  have he : off base (8 * i) + BitVec.ofNat 64 (768 + j) = off base (768 + (8 * i + j)) := by
    rw [Offset.add_add]; exact congrArg (off base) (by omega)
  apply WP.of_runBlock
  simp only [expandScalarBit, runBlock_cons, runStep_some, runBlock_nil, exec, State.read,
    show j < Size.x.bits from by change j < 64; omega,
    addr, State.store, RegUpd.gpr_write, RegUpd.wr_write, RegUpd.mem_write,
    BitVec.setWidth_eq, hp, hone, hb, he, hw, Nat.mod_one,
    show 768 + j < 4096 * 1 from by omega, and_self,
    ite_true, ite_false, reduceCtorEq, bit_byte b j hj,
    Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨fun r hr => ?_, rfl, True.intro, rfl, ?_⟩
  · simp only [hr, ite_false]
  · rfl

structure BitKeep (base : Addr) (i n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ≠ .x2 → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base (768 + 8 * i) n s.mem t.mem

theorem BitKeep.scratch {base : Addr} {i n : Nat} {s t : State}
    (h : BitKeep base i n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem scalarBitPrefix_ok {s : State} {base : Addr} (hs : Scr s base)
    (i n : Nat) (hi : i < 64) (hn : n ≤ 8) (hp : s.gpr .x9 = off base (8 * i)) (hone : s.gpr .x11 = BitVec.ofNat 64 1)
    (b : BitVec 8) (hb : s.gpr .x8 = b.setWidth 64) :
    WP isa (.block ((List.range n).flatMap expandScalarBit)) s fun t => BitKeep base i n s t ∧
      ∀ j < n, t.mem (off base (768 + (8 * i + j))) = BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by
  induction n generalizing s with
  | zero => exact WP.block_nil ⟨⟨fun _ _ => rfl, rfl, rfl, rfl, Outside.refl _ _ _ _⟩, fun _ h => by omega⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (ih hs (by omega) hp hone hb) fun t ⟨hk, hv⟩ => ?_
    refine WP.mono (expandScalarBit_ok (hk.scratch hs) i n hi (by omega)
      ((hk.gpr _ (by decide)).trans hp) ((hk.gpr _ (by decide)).trans hone) b ((hk.gpr _ (by decide)).trans hb))
      fun u ⟨ug, ur, uw, usp, um⟩ => ?_
    refine ⟨⟨fun r hr => (ug r hr).trans (hk.gpr r hr), ur.trans hk.rd, uw.trans hk.wr, usp.trans hk.sp, ?_⟩, ?_⟩
    · intro p hp
      rw [um, writeW8_outside _ _ _ (by omega) (by omega), hk.mem p (by omega)]
    · intro j hj
      rw [um, writeW8_apply]
      by_cases h : j = n
      · subst j; rw [ite_eq_left rfl]
      · rw [ite_eq_right (fun he => h (by
          have hh := (off_eq_iff base (by omega) (by omega)).mp he
          omega))]
        exact hv j (by omega)

end VG.Proof.Ed25519.AArch64
