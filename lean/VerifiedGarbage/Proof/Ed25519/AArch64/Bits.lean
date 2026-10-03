import VerifiedGarbage.Proof.Ed25519.AArch64.BitByte
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.AArch64.PointPowers

/-! Merged from `Proof.Ed25519.AArch64.BitRead`. -/
section
/-! Load the next scalar byte and calculate its bit-output address. -/
namespace VG.Proof.Ed25519.AArch64
open VG VG.AArch64

theorem scalarByteRead_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i : Nat) (hi : i < 64) (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) :
    WP isa (.block [.add .x .x8 .x1 .x19, .ldrb .x8 .x8 0,
      .lsl .x .x9 .x19 3, .add .x .x9 .x0 .x9]) s fun t =>
      t.gpr .x8 = (s.mem (off k i)).setWidth 64 ∧ t.gpr .x9 = off base (8 * i) ∧
      Keeps [.x8, .x9] s t := by
  have hshift : (BitVec.ofNat 64 i) <<< 3 = BitVec.ofNat 64 (8 * i) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.shiftLeft_eq, BitVec.toNat_ofNat]
    rw [show 2 ^ 3 = 8 from rfl, Nat.mul_comm]
    rw [Nat.mod_eq_of_lt (by omega : i < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 8 * i < 2 ^ 64)]
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, read_x, addr, State.load,
    show (0 : Nat) < 4096 * 1 from by decide, show (0 : Nat) % 1 = 0 from rfl,
    show (3 : Nat) < Size.x.bits from by decide, and_self,
    RegUpd.gpr_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    hp, hc, hs.x0, hshift, BitVec.add_zero, BitVec.setWidth_eq, hr, read_byte,
    ite_true, ite_false, reduceCtorEq, Option.bind_some, Option.map_some,
    Option.some.injEq, exists_eq_left']
  refine ⟨BitVec.setWidth_setWidth (by decide), True.intro, ⟨?_, rfl, rfl, rfl, rfl⟩⟩
  intro r h
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  simp only [RegUpd.gpr_write, h.1, h.2, ite_false]

end VG.Proof.Ed25519.AArch64
end

/-! Expand all scalar bits, without X25519's clamping. -/

namespace VG.Proof.Ed25519.AArch64

open VG VG.AArch64 VG.Impl.Ed25519.AArch64

structure BitsKeep (base : Addr) (o n : Nat) (s t : State) : Prop where
  gpr : ∀ r, r ∉ [Reg.x8, .x9, .x2, .x19, .x11] → t.gpr r = s.gpr r
  rd : t.rd = s.rd
  wr : t.wr = s.wr
  sp : t.sp = s.sp
  mem : Outside base o n s.mem t.mem

theorem BitsKeep.scratch {base : Addr} {o n : Nat} {s t : State}
    (h : BitsKeep base o n s t) (hs : Scr s base) : Scr t base :=
  ⟨(h.gpr _ (by decide)).trans hs.x0, h.wr ▸ hs.wr, hs.nowrap⟩

theorem BitsKeep.trans {base : Addr} {o n : Nat} {s t u : State}
    (h : BitsKeep base o n s t) (k : BitsKeep base o n t u) : BitsKeep base o n s u :=
  ⟨fun r hr => (k.gpr r hr).trans (h.gpr r hr), k.rd.trans h.rd, k.wr.trans h.wr, k.sp.trans h.sp, h.mem.trans k.mem⟩

theorem BitsKeep.mono {base : Addr} {o n o' n' : Nat} {s t : State}
    (h : BitsKeep base o n s t) (ho : o' ≤ o) (hn : o + n ≤ o' + n') : BitsKeep base o' n' s t :=
  ⟨h.gpr, h.rd, h.wr, h.sp, h.mem.mono ho hn⟩

theorem scalarByteBits_ok {s : State} {base k : Addr} (hs : Scr s base)
    (i count : Nat) (hi : i < count) (hn : count ≤ 64)
    (hc : s.gpr .x19 = BitVec.ofNat 64 i) (hp : s.gpr .x1 = k)
    (hr : InRegions (s.rd ++ s.wr) (off k i) 1) (hone : s.gpr .x11 = BitVec.ofNat 64 1) :
    WP isa (.block (scalarByteBits count)) s fun t =>
      t.gpr .x19 = BitVec.ofNat 64 (i + 1) ∧ (t.gpr .x8 != 0) = decide (i + 1 ≠ count) ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧
      BitsKeep base (768 + 8 * i) 8 s t ∧
      ∀ j < 8, t.mem (off base (768 + (8 * i + j))) =
        BitVec.ofNat 8 (((s.mem (off k i)).toNat >>> j) &&& 1) := by
  rw [scalarByteBits, List.append_assoc, WP.block_append_iff]
  refine WP.mono (scalarByteRead_ok hs i (by omega) hc hp hr) fun a ⟨av, ap, ka⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (scalarBitPrefix_ok (hs.of_keeps ka (by decide)) i 8 (by omega) (by decide)
    ap ((ka.gpr _ (by decide)).trans hone) _ av) fun b ⟨kb, bv⟩ => ?_
  refine WP.mono (powersNext_ok b i count hi hn
    ((kb.gpr _ (by decide)).trans ((ka.gpr _ (by decide)).trans hc))) fun t ⟨tc, tz, kt⟩ => ?_
  refine ⟨tc, tz, ?_, ⟨fun r hr => ?_, kt.rd.trans (kb.rd.trans ka.rd),
    kt.wr.trans (kb.wr.trans ka.wr), kt.sp.trans (kb.sp.trans ka.sp), ?_⟩, ?_⟩
  · rw [kt.gpr _ (by decide), kb.gpr _ (by decide), ka.gpr _ (by decide), hone]
  · have h8 : r ≠ .x8 := fun he => hr (by simp [he])
    have h9 : r ≠ .x9 := fun he => hr (by simp [he])
    have h2 : r ≠ .x2 := fun he => hr (by simp [he])
    have h19 : r ≠ .x19 := fun he => hr (by simp [he])
    exact (kt.gpr r (by simp [h8, h19])).trans
      ((kb.gpr r h2).trans (ka.gpr r (by simp [h8, h9])))
  · rw [kt.mem, ← ka.mem]; exact kb.mem
  · rw [kt.mem]; exact bv

structure BitsInv (s₀ : State) (base k : Addr) (count i : Nat) (s : State) : Prop where
  scratch : Scr s base
  ptr : s.gpr .x1 = k
  counter : s.gpr .x19 = BitVec.ofNat 64 i
  one : s.gpr .x11 = BitVec.ofNat 64 1
  keep : BitsKeep base 768 (8 * count) s₀ s
  bits : ∀ t < 8 * i, s.mem (off base (768 + t)) =
    BitVec.ofNat 8 (((s₀.mem (off k (t / 8))).toNat >>> (t % 8)) &&& 1)

theorem scalarBitsLoop_ok {s₀ : State} {base k : Addr} (count : Nat) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s₀.rd ++ s₀.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    ∀ i s, i < count → BitsInv s₀ base k count i s →
      WP isa (.loop (.block (scalarByteBits count)) (.nonzero .x .x8)) s fun t => BitsInv s₀ base k count count t := by
  intro i s hi h
  refine WP.loop (M := isa) (body := .block (scalarByteBits count)) (c := .nonzero .x .x8)
    (Q := fun t => BitsInv s₀ base k count count t)
    (fun n s => ∃ i, n = count - i ∧ i < count ∧ BitsInv s₀ base k count i s) ?_
    (count - i) s ⟨i, rfl, hi, h⟩
  rintro n s ⟨i, rfl, hi, h⟩
  refine WP.mono (scalarByteBits_ok h.scratch i count hi hn h.counter h.ptr
    (by rw [h.keep.rd, h.keep.wr]; exact hr i hi) h.one) fun t ⟨tc, tz, tone, tk, tb⟩ => ?_
  have hbyte : s.mem (off k i) = s₀.mem (off k i) := h.keep.mem _ (by have := hd i hi; omega)
  have inv : BitsInv s₀ base k count (i + 1) t := by
    refine ⟨tk.scratch h.scratch, (tk.gpr _ (by decide)).trans h.ptr, tc, tone,
      h.keep.trans (tk.mono (by omega) (by omega)), fun j hj => ?_⟩
    by_cases hp : j < 8 * i
    · rw [tk.mem _ (by rw [ofs_off' base (by omega)]; omega), h.bits j hp]
    · have e := tb (j - 8 * i) (by omega)
      rw [show 8 * i + (j - 8 * i) = j by omega, hbyte] at e
      rw [e, show j / 8 = i by omega, show j % 8 = j - 8 * i by omega]
  by_cases he : i + 1 = count
  · exact Or.inl ⟨by simp only [eval, read_x, tz, he, show decide (count ≠ count) = false from decide_eq_false (not_not_intro rfl)], he ▸ inv⟩
  · exact Or.inr ⟨by simp only [eval, read_x, tz, decide_eq_true he],
      count - (i + 1), by omega, i + 1, rfl, by omega, inv⟩

theorem input_byte (m : Mem) (k : Addr) (count j : Nat) (hj : j < count) :
    (Spec.Ed25519.bytesAt m k count).getD j 0 = m (off k j) := by
  simp only [Spec.Ed25519.bytesAt, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem scalarBitsInit_ok (s : State) :
    WP isa (.block [.movz .w .x19 0 0, .movz .w .x11 1 0]) s fun t =>
      t.gpr .x19 = 0 ∧ t.gpr .x11 = BitVec.ofNat 64 1 ∧ Keeps [.x19, .x11] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec,
    show 16 * 0 < Size.w.bits from by decide, RegUpd.gpr_write,
    ite_true, ite_false, reduceCtorEq, Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, ⟨fun r hr => ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_write, hr.1, hr.2, ite_false]

theorem expandScalarBits_ok {s : State} {base k : Addr} (hs : Scr s base) (hp : s.gpr .x1 = k)
    (count : Nat) (hn0 : 0 < count) (hn : count ≤ 64)
    (hr : ∀ q < count, InRegions (s.rd ++ s.wr) (off k q) 1)
    (hd : ∀ q < count, 8192 ≤ ofs base (off k q)) :
    WP isa (scalarBits count) s fun t => BitsKeep base 768 (8 * count) s t ∧
      ∀ j < 8 * count, t.mem (off base (768 + j)) =
        BitVec.ofNat 8 ((Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem k count) / 2 ^ j) % 2) := by
  rw [scalarBits]
  refine WP.seq (WP.mono (scalarBitsInit_ok s) fun a ⟨ac, aone, ka⟩ => ?_)
  have init : BitsInv s base k count 0 a := by
    refine ⟨hs.of_keeps ka (by decide), (ka.gpr _ (by decide)).trans hp, ac, aone,
      ⟨fun r hr => ka.gpr r (fun hm => hr ((by decide : [Reg.x19, .x11] ⊆ [Reg.x8, .x9, .x2, .x19, .x11]) hm)), ka.rd, ka.wr, ka.sp, ?_⟩, fun j hj => by omega⟩
    rw [ka.mem]; exact Outside.refl _ _ _ _
  refine WP.mono (scalarBitsLoop_ok count hn hr hd 0 a hn0 init) fun t h => ?_
  refine ⟨h.keep, fun j hj => ?_⟩
  rw [h.bits j hj]
  have hb := Proof.X25519.leNum_bit (Spec.Ed25519.bytesAt s.mem k count) j
  rw [← decodeLE_eq, input_byte _ _ _ _ (by omega)] at hb
  simp only [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod] at hb ⊢
  exact congrArg (BitVec.ofNat 8) hb.symm

end VG.Proof.Ed25519.AArch64
