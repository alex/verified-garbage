import VerifiedGarbage.Proof.CmacAes.Stream.AArch64.Call
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# Streaming AES-CMAC on AArch64: arithmetic, memory and copying bytes

Untrusted: everything here is checked by Lean. The number of bytes held
back, as the code computes it from `count` (`held_bv`); immediates; branch
conditions; bytes written (`writeBytes`); and `copy`, which copies the `x8`
bytes at `x7` to `x6`, a byte at a time (none if `x8` is 0), changing only
`x6` to `x9`.
-/

namespace VG.Proof.CmacAes.Stream.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.WriteBytes
open VG.Impl.CmacAes.Stream.AArch64 (copy)
open VG.Proof.Cmac.Stream (held held_pos)
open VG.Proof.CmacAes.AArch64 (copyStep_ok succ_ofNat ofNat_ne_zero)

/-! ## Arithmetic -/

theorem mz0 : BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0) = 0 := by decide
theorem mz1 : BitVec.setWidth 64 (1 : BitVec 16) <<< (16 * 0) = 1 := by decide
theorem mz15 : BitVec.setWidth 64 (15 : BitVec 16) <<< (16 * 0) = 15 := by decide
theorem mz16 : BitVec.setWidth 64 (16 : BitVec 16) <<< (16 * 0) = BitVec.ofNat 64 16 := by decide

theorem and15 (x : BitVec 64) : (x &&& 15).toNat = x.toNat % 16 := by
  rw [BitVec.toNat_and, show (15 : BitVec 64).toNat = 2 ^ 4 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]

/-- The number of bytes held back for a nonzero `count`, as `sub 1; and 15; add 1` computes it. -/
theorem held_bv (c : BitVec 64) (h : c ≠ 0) :
    ((c - BitVec.ofNat 64 1) &&& 15) + BitVec.ofNat 64 1 = BitVec.ofNat 64 (held c.toNat) := by
  have hc : c.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq (by simpa using e))
  rw [held_pos (by omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, and15, BitVec.toNat_sub]
  simp only [BitVec.toNat_ofNat]
  have := c.isLt
  omega

theorem toNat_add_lt (p : Addr) {d k : Nat} (h : p.toNat + k ≤ 2 ^ 64) (hd : d < k) :
    (p + BitVec.ofNat 64 d).toNat = p.toNat + d := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : d < 2 ^ 64)]
  exact Nat.mod_eq_of_lt (by omega)

theorem ofNat_toNat_eq {x : BitVec 64} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 64 n :=
  BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ x.isLt)])

/-- The rounds, as `lsr 2; add 6` computes them from the key length. -/
theorem rounds_bv {KL : Nat} (h : KL = 16 ∨ KL = 24 ∨ KL = 32) :
    BitVec.ofNat 64 KL >>> 2 + BitVec.ofNat 64 6 = BitVec.ofNat 64 (KL / 4 + 6) := by
  rcases h with rfl | rfl | rfl <;> decide

/-! ## Branch conditions -/

theorem eval_zero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.zero .x r) s = some (decide (x = 0)) := by
  show some (s.read .x r == 0) = _
  rw [State.read, h, BitVec.setWidth_eq]
  have := ofNat_ne_zero hx
  rw [bne] at this
  cases hb : (BitVec.ofNat 64 x == 0) <;> rw [hb] at this <;> cases hd : decide (x = 0) <;> simp_all

theorem eval_nonzero {s : State} {r : Reg} {x : Nat} (hx : x < 2 ^ 64) (h : s.gpr r = BitVec.ofNat 64 x) :
    isa.eval (.nonzero .x r) s = some !decide (x = 0) := by
  show some (s.read .x r != 0) = _
  rw [State.read, h, BitVec.setWidth_eq, ofNat_ne_zero hx]

/-! ## Bytes written -/

theorem writeBytes_at (m : Mem) (q : Addr) (xs : List Byte) {i : Nat} (hi : i < 2 ^ 64) :
    writeBytes m q xs (q + BitVec.ofNat 64 i) =
      if i < xs.length then xs.getD i 0 else m (q + BitVec.ofNat 64 i) := by
  simp only [writeBytes, Mem.sub_ofNat_toNat q hi]

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} (h : xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m q xs) q xs.length = xs := by
  apply List.ext_getElem (by simp [Spec.Aes.bytesAt])
  intro i h1 _
  simp only [Spec.Aes.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Aes.bytesAt, List.getElem_map, List.getElem_range, writeBytes_at m q xs (by omega : i < 2 ^ 64),
    h1, ↓reduceIte, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

/-- Bytes `[0, r)` from `p` stay, and the bytes `xs` follow them. -/
theorem bytesAt_writeBytes (m : Mem) (p : Addr) (r : Nat) (xs : List Byte) (h : r + xs.length < 2 ^ 64) :
    Spec.Aes.bytesAt (writeBytes m (p + BitVec.ofNat 64 r) xs) p (r + xs.length) =
      Spec.Aes.bytesAt m p r ++ xs := by
  rw [Proof.Cmac.Stream.bytesAt_append, bytesAt_writeBytes_self _ _ (by omega)]
  refine congrArg (· ++ xs) ?_
  simp only [Spec.Aes.bytesAt]
  apply List.map_congr_left
  intro i hi
  exact writeBytes_before m p xs (List.mem_range.mp hi) (by omega)

/-! ## Copying bytes -/

/-- What `copy` leaves. -/
structure Copied (s : State) (C : Addr) (xs : List Byte) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem C xs
  other : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_ok (s : State) {P C : Addr} {L : Nat} (hL : L < 2 ^ 64) (h7 : s.gpr .x7 = P)
    (h6 : s.gpr .x6 = C) (h8 : s.gpr .x8 = BitVec.ofNat 64 L)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (P + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < L, InRegions s.wr (C + BitVec.ofNat 64 i) 1)
    (hdis : (⟨P, L⟩ : Region).Disjoint ⟨C, L⟩) :
    WP isa copy s (Copied s C (Spec.Aes.bytesAt s.mem P L)) := by
  by_cases hL0 : L = 0
  · subst hL0
    refine WP.ite true (by rw [eval_zero hL h8]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  refine WP.ite false (by rw [eval_zero hL h8]; simp [hL0]) (fun h => by cases h) fun _ => ?_
  refine WP.loop (M := isa) (body := .block Proof.CmacAes.AArch64.copyBody) (c := .nonzero .x .x8)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .x7 = P + BitVec.ofNat 64 i ∧
      t.gpr .x6 = C + BitVec.ofNat 64 i ∧ t.gpr .x8 = BitVec.ofNat 64 (L - i) ∧
      t.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) ∧
      (∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, by omega, by rw [h7]; simp, by rw [h6]; simp, by rw [h8, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  obtain ⟨t', run', mem', x7', x6', x8', g', sp', rd', wr'⟩ := copyStep_ok t
    (A := P + BitVec.ofNat 64 i) (B := C + BitVec.ofNat 64 i) (by rw [x7, BitVec.add_zero])
    (by rw [x6, BitVec.add_zero]) (by rw [rd, wr]; exact hr i hi) (by rw [wr]; exact hw i hi)
  refine WP.of_runBlock ⟨t', run', ?_⟩
  have hlen : (Spec.Aes.bytesAt s.mem P i).length = i := by simp [Spec.Aes.bytesAt]
  have hx : writeBytes s.mem C (Spec.Aes.bytesAt s.mem P i) (P + BitVec.ofNat 64 i) =
      s.mem (P + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem C _ (R := ⟨C, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hdis _ (Offset.contains_base P (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t'.mem = writeBytes s.mem C (Spec.Aes.bytesAt s.mem P (i + 1)) := by
    rw [mem', mem, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem C (Spec.Aes.bytesAt s.mem P i) (s.mem (P + BitVec.ofNat 64 i)) (by rw [hlen]; omega),
      hlen]
  have x8'' : t'.gpr .x8 = BitVec.ofNat 64 (L - (i + 1)) := by
    rw [x8', x8, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega)]; rfl
  have ev := eval_nonzero (s := t') (x := L - (i + 1)) (by omega) x8''
  have gg : ∀ r, r ≠ .x6 → r ≠ .x7 → r ≠ .x8 → r ≠ .x9 → t'.gpr r = s.gpr r := fun r h₁ h₂ h₃ h₄ => by
    rw [g' r h₁ h₂ h₃ h₄, g r h₁ h₂ h₃ h₄]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], ⟨by rw [hmem, he], gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩⟩
  · right
    refine ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega,
      by rw [x7', x7, BitVec.add_assoc, succ_ofNat], by rw [x6', x6, BitVec.add_assoc, succ_ofNat], x8'', hmem,
      gg, by rw [sp', sp], by rw [rd', rd], by rw [wr', wr]⟩

end VG.Proof.CmacAes.Stream.AArch64
