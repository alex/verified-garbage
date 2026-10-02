import VerifiedGarbage.Proof.X448.X86.Iter
import VerifiedGarbage.Proof.X448.Bytes

/-!
# X448 on x86 (32-bit): expanding scalar bytes

Each byte is expanded into eight bytes holding its bits, through public
offsets in the working space.
-/

namespace VG.Proof.X448.X86

open VG VG.X86 VG.Impl.X448.X86

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
    ((b.setWidth 32 >>> j) &&& (1 : BitVec 32)).setWidth 8 =
      BitVec.ofNat 8 ((b.toNat >>> j) &&& 1) := by decide +kernel

end VG.Proof.X448.X86
