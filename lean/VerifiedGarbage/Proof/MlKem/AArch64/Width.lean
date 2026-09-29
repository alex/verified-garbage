import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.Encode
import VerifiedGarbage.Impl.MlKem.AArch64.Compress

/-!
# ML-KEM on AArch64: the widths of compression

Untrusted: everything here is checked by Lean. What the loops of
`compressEncode` and `decodeDecompress` need of a width (`Width.Ok`), for
each of the three, and the numbers they build digit by digit.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64 VG.Impl.MlKem.AArch64
open VG.Spec.MlKem

/-- A width of `compressWidths`, `c` digits of `d` bits per `nb` bytes. -/
structure WOk (w : Width) : Prop where
  mem : w.d ∈ compressWidths
  dc : w.d * w.c = 8 * w.nb
  cG : w.c * (256 / w.c) = 256
  bytes : w.nb * (256 / w.c) = 32 * w.d
  mul : w.mul = compressMul w.d
  c_pos : 0 < w.c
  c_le : w.c ≤ 8
  nb_pos : 0 < w.nb
  nb_le : w.nb ≤ 5
  d_pos : 0 < w.d
  d_le : w.d ≤ 10
  G_pos : 0 < 256 / w.c
  G_le : 256 / w.c ≤ 128

theorem width1_ok : WOk width1 := ⟨by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

theorem width4_ok : WOk width4 := ⟨by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

theorem width10_ok : WOk width10 := ⟨by decide, rfl, rfl, rfl, rfl, by decide, by decide, by decide,
  by decide, by decide, by decide, by decide, by decide⟩

/-- The digits of the first `e + 1` values of `f`. -/
theorem digits_range_succ (w : Nat) (f : Nat → Nat) (e : Nat) :
    digits w ((List.range (e + 1)).map f) = digits w ((List.range e).map f) + 2 ^ (w * e) * f e := by
  suffices h : ∀ (L : List Nat) (a : Nat), digits w (L ++ [a]) = digits w L + 2 ^ (w * L.length) * a by
    rw [List.range_succ, List.map_append, List.map_singleton, h, List.length_map, List.length_range]
  intro L a
  induction L with
  | nil => simp [digits]
  | cons x L ih =>
    rw [List.cons_append, digits_cons, digits_cons, ih, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have h : 2 ^ w * (2 ^ (w * L.length) * a) = 2 ^ (w * L.length) * 2 ^ w * a := by
      rw [Nat.mul_left_comm, Nat.mul_assoc]
    rw [Nat.mul_add, h]
    omega

/-- The digits of `e` values less than `2ʷ` are less than `2^(w e)`. -/
theorem digits_range_lt {w : Nat} {f : Nat → Nat} (hf : ∀ i, f i < 2 ^ w) (e : Nat) :
    digits w ((List.range e).map f) < 2 ^ (w * e) := by
  have := digits_lt (w := w) (L := (List.range e).map f) fun a ha => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
    exact hf i
  rwa [List.length_map, List.length_range] at this

end VG.Proof.MlKem.AArch64
