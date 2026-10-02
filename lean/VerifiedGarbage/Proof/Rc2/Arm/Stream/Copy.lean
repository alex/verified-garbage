import VerifiedGarbage.Impl.Rc2.Arm.Stream
import VerifiedGarbage.Proof.MdStream.Arm.Common
import VerifiedGarbage.Proof.Framework.WriteBytes
import VerifiedGarbage.Proof.Rc2.Stream

/-!
# Streaming RC2-CBC on ARMv7: the byte copy

Untrusted: everything here is checked by Lean. `copy_wp`: the copy of `L`
bytes from `src + so` to `dst + dd` (`Impl.Rc2.Arm.Stream.copy`), for any
registers, offsets and count, writes the source bytes at the destination
(`writeBytes`), advances both pointers by `L`, and changes no other register
but `r12` and the count.
-/

namespace VG.Proof.Rc2.Arm.Stream

open VG VG.Arm VG.Impl.Rc2.Arm.Stream
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldr
  wp_str wp_ldrb wp_strb wp_ldrSp eval_eq eval_ne ofNat_beq_zero sub_ofNat cmp0)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

/-- The address of byte `i` of a buffer at `p + o` that does not wrap around. -/
theorem addr_off {p : BitVec 32} {i o : Nat} (h : p.toNat + o + i < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 i + BitVec.ofNat 32 o) =
      State.addr p + BitVec.ofNat 64 o + BitVec.ofNat 64 i := by
  rw [Offset.add_add, Offset.add_add, Nat.add_comm i o, addr_add (by omega)]

/-- What a copy leaves. -/
structure CopyPost (s : State) (src dst cnt : Reg) (A B : Addr) (L : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A L)
  srcv : s'.gpr src = s.gpr src + BitVec.ofNat 32 L
  dstv : s'.gpr dst = s.gpr dst + BitVec.ofNat 32 L
  keep : ∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem copy_wp {s : State} {src dst cnt : Reg} {so dd L : Nat}
    (h1 : src ≠ dst) (h2 : src ≠ cnt) (h3 : dst ≠ cnt) (h4 : src ≠ .r12) (h5 : dst ≠ .r12)
    (h6 : cnt ≠ .r12) (hso : so < 4096) (hdd : dd < 4096)
    (hc : s.gpr cnt = BitVec.ofNat 32 L) (hL : L < 2 ^ 32)
    (fp : (s.gpr src).toNat + so + L ≤ 2 ^ 32) (fd : (s.gpr dst).toNat + dd + L ≤ 2 ^ 32)
    (hr : 0 < L → Covers [⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, L⟩] (s.rd ++ s.wr))
    (hw : 0 < L → Covers [⟨State.addr (s.gpr dst) + BitVec.ofNat 64 dd, L⟩] s.wr)
    (hd : 0 < L → (⟨State.addr (s.gpr src) + BitVec.ofNat 64 so, L⟩ : Region).Disjoint
      ⟨State.addr (s.gpr dst) + BitVec.ofNat 64 dd, L⟩) :
    WP isa (copy src so dst dd cnt) s (CopyPost s src dst cnt
      (State.addr (s.gpr src) + BitVec.ofNat 64 so) (State.addr (s.gpr dst) + BitVec.ofNat 64 dd) L) := by
  generalize hP : s.gpr src = P at *
  generalize hD : s.gpr dst = D at *
  generalize hA : State.addr P + BitVec.ofNat 64 so = A at *
  generalize hB : State.addr D + BitVec.ofNat 64 dd = B at *
  rw [copy]
  refine WP.seq (wp_cmp (op2_imm (by decide)) fun t₀ f₀ z₀ => WP.block_nil ?_)
  have hz : t₀.z = decide (L = 0) := by rw [z₀, hc, cmp0 (by omega)]
  refine WP.ite (decide (L = 0)) (by rw [← hz]; rfl) (fun hL0 => WP.block_nil ?_) fun hL0 => ?_
  · have hL0 : L = 0 := of_decide_eq_true hL0
    subst hL0
    refine ⟨?_, ?_, ?_, fun r _ _ _ _ => ?_, f₀.sp, f₀.rd, f₀.wr⟩
    · rw [f₀.mem]; simp [Spec.Rc2.bytesAt, writeBytes_nil]
    · rw [f₀.gpr, hP]; exact (BitVec.add_zero P).symm
    · rw [f₀.gpr, hD]; exact (BitVec.add_zero D).symm
    · rw [f₀.gpr]
  have hL₀ : 0 < L := by have := of_decide_eq_false hL0; omega
  have hr := hr hL₀
  have hw := hw hL₀
  have hd := hd hL₀
  refine WP.loop (M := isa) (body := .block (copyBody src so dst dd cnt)) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr src = P + BitVec.ofNat 32 i ∧
      t.gpr dst = D + BitVec.ofNat 32 i ∧ t.gpr cnt = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A i) ∧
      (∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [f₀.gpr, hP]; exact (BitVec.add_zero P).symm,
      by rw [f₀.gpr, hD]; exact (BitVec.add_zero D).symm, by rw [f₀.gpr, hc, Nat.sub_zero],
      by rw [f₀.mem]; simp [Spec.Rc2.bytesAt, writeBytes_nil], fun r _ _ _ _ => by rw [f₀.gpr],
      f₀.sp, f₀.rd, f₀.wr⟩
  rintro n t ⟨i, rfl, hi, xs, xd, xc, mem, g, sp, rd, wr⟩
  refine wp_ldrb (a := A + BitVec.ofNat 64 i) hso (by rw [xs, ← hA]; exact addr_off (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := B + BitVec.ofNat 64 i) hdd
    (by rw [u₁.other _ h5, xd, ← hB]; exact addr_off (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Rc2.bytesAt s.mem A i).length = i := Proof.Rc2.bytesAt_length _ _ _
  have hx : writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A i) (A + BitVec.ofNat 64 i) =
      s.mem (A + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem B _ (R := ⟨B, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem B (Spec.Rc2.bytesAt s.mem A (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Rc2.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have e1 : (1 : BitVec 32) = BitVec.ofNat 32 1 := rfl
  have cs : t₄.gpr cnt = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (Ne.symm h3), u₃.other _ (Ne.symm h2), v₂.gpr, u₁.other _ h6, xc]
  have xc' : t₅.gpr cnt = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cs, e1, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, cs, e1, sub_ofNat (by omega), Nat.sub_sub, ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ src → r ≠ dst → r ≠ cnt → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r a b c d => by
    rw [u₅.other _ c, u₄.other _ b, u₃.other _ a, v₂.gpr, u₁.other _ d, g r a b c d]
  have xd' : t₅.gpr dst = D + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ h3, u₄.gpr, u₃.other _ (Ne.symm h1), v₂.gpr, u₁.other _ h5, xd, e1, Offset.add_add]
  have xs' : t₅.gpr src = P + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ h2, u₄.other _ h1, u₃.gpr, v₂.gpr, u₁.other _ h4, xs, e1, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    refine ⟨by rw [ev]; simp [he], ⟨by rw [hmem, he], by rw [xs', he, hP], by rw [xd', he, hD], gg,
      sp', rd', wr'⟩⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xs', xd', xc', hmem, gg,
      sp', rd', wr'⟩

theorem bytesAt_writeBytes_self (m : Mem) (q : Addr) {xs : List Byte} {n : Nat} (hn : xs.length = n)
    (h : n < 2 ^ 64) : Spec.Rc2.bytesAt (writeBytes m q xs) q n = xs := by
  subst hn
  apply List.ext_getElem (by simp [Spec.Rc2.bytesAt])
  intro i h1 _
  simp only [Spec.Rc2.bytesAt, List.length_map, List.length_range] at h1
  simp only [Spec.Rc2.bytesAt, List.getElem_map, List.getElem_range, writeBytes, Offset.add_sub_cancel_left,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega), h1, ↓reduceIte,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]

end VG.Proof.Rc2.Arm.Stream
