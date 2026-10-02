import VerifiedGarbage.Proof.CmacAes.Stream.Arm.Common

/-!
# Streaming AES-CMAC on ARMv7: copying bytes

`copy` copies the `r1` bytes at `r6` to `r2`, a byte at a time (none if `r1`
is 0), advancing `r6` past them and taking them off `r7`, and changing only
`r1`, `r2`, `r6`, `r7`, `r12` and the flags.
-/

namespace VG.Proof.CmacAes.Stream.Arm

open VG VG.Arm VG.Impl.CmacAes.Stream.Arm VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd op2_imm op2_reg wp_add wp_sub wp_subs wp_cmp wp_ldrb wp_strb eval_ne
  ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.Arm (byte_rt32)

/-- What `copy` leaves. -/
structure Copied (s : State) (p c : BitVec 32) (L x : Nat) (s' : State) : Prop where
  mem : s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L)
  r6 : s'.gpr .r6 = p + BitVec.ofNat 32 L
  r7 : s'.gpr .r7 = BitVec.ofNat 32 (x - L)
  other : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r7 → r ≠ .r12 → s'.gpr r = s.gpr r
  sp : s'.sp = s.sp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

/-- The loop, for `L > 0` bytes. -/
theorem copyLoop_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + L ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, L⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩) :
    WP isa (.loop (.block copyBody) .ne) s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = p + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block copyBody) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r6 = p + BitVec.ofNat 32 i ∧
      t.gpr .r2 = c + BitVec.ofNat 32 i ∧ t.gpr .r1 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h6]; exact (BitVec.add_zero p).symm, by rw [h2]; exact (BitVec.add_zero c).symm,
      by rw [h1, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x6, x2, x1, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x6, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x2, BitVec.add_zero, aC])
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_add (op2_imm (by decide)) fun t₃ u₃ => wp_add (op2_imm (by decide)) fun t₄ u₄ =>
    wp_subs (op2_imm (by decide)) fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (State.addr p) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) (State.addr p + BitVec.ofNat 64 i) =
      s.mem (State.addr p + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (State.addr c) _ (R := ⟨State.addr c, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, u₁.gpr, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have x1' : t₅.gpr .r1 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x1,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r1 → r ≠ .r2 → r ≠ .r6 → r ≠ .r12 → t₅.gpr r = s.gpr r := fun r h₁ h₂ h₆ h₁₂ => by
    rw [u₅.other _ h₁, u₄.other _ h₂, u₃.other _ h₆, v₂.gpr, u₁.other _ h₁₂, g r h₁ h₂ h₆ h₁₂]
  have x2' : t₅.gpr .r2 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x2,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x6' : t₅.gpr .r6 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x6', x2', x1', hmem, gg,
      sp', rd', wr'⟩

/-- What copying `L > 0` bytes from `p` to `c` needs. -/
structure CopyOk (s : State) (p c : BitVec 32) (L : Nat) : Prop where
  fp : p.toNat + L ≤ 2 ^ 32
  fc : c.toNat + L ≤ 2 ^ 32
  hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)
  hw : Covers [⟨State.addr c, L⟩] s.wr
  hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, L⟩

theorem copy_wp {s : State} {p c : BitVec 32} {L x : Nat} (hLx : L ≤ x) (hx : x < 2 ^ 32)
    (h6 : s.gpr .r6 = p) (h2 : s.gpr .r2 = c) (h1 : s.gpr .r1 = BitVec.ofNat 32 L)
    (h7 : s.gpr .r7 = BitVec.ofNat 32 x) (ok : 0 < L → CopyOk s p c L) :
    WP isa copy s (Copied s p c L x) := by
  refine WP.seq (wp_sub (op2_reg _ _) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .r7 → s₂.gpr r = s.gpr r := fun r hr => by rw [f₂.gpr, u₁.other _ hr]
  have r7₂ : s₂.gpr .r7 = BitVec.ofNat 32 (x - L) := by rw [f₂.gpr, u₁.gpr, h7, h1, sub_ofNat hLx]
  rw [show s₁.gpr .r1 = BitVec.ofNat 32 L by rw [u₁.other _ (by decide), h1]] at z₂
  have ev := eq_iff s₂ z₂ (by omega)
  have sp₂ : s₂.sp = s.sp := by rw [f₂.sp, u₁.sp]
  have rd₂ : s₂.rd = s.rd := by rw [f₂.rd, u₁.rd]
  have wr₂ : s₂.wr = s.wr := by rw [f₂.wr, u₁.wr]
  have m₂ : s₂.mem = s.mem := by rw [f₂.mem, u₁.mem]
  by_cases hL : L = 0
  · subst hL
    refine WP.ite true (by rw [ev]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
    exact ⟨by rw [m₂]; simp [Spec.Aes.bytesAt, writeBytes_nil],
      (by rw [g₂ _ (by decide), h6]; exact (BitVec.add_zero p).symm), r7₂, fun r _ _ _ h₇ _ => g₂ r h₇, sp₂, rd₂,
      wr₂⟩
  · obtain ⟨fp, fc, hr, hw, hd⟩ := ok (by omega)
    refine WP.ite false (by rw [ev]; simp [hL]) (fun h => by cases h) fun _ => ?_
    refine WP.mono (copyLoop_wp (by omega) (by rw [g₂ _ (by decide), h6]) (by rw [g₂ _ (by decide), h2])
      (by rw [g₂ _ (by decide), h1]) fp fc (by rw [rd₂, wr₂]; exact hr) (by rw [wr₂]; exact hw) hd)
      fun s' ⟨mm, r6, g, sp, rd, wr⟩ => ⟨by rw [mm, m₂], r6, by rw [g _ (by decide) (by decide) (by decide)
        (by decide), r7₂], fun r h₁ h₂ h₆ h₇ h₁₂ => by rw [g r h₁ h₂ h₆ h₁₂, g₂ r h₇], by rw [sp, sp₂],
        by rw [rd, rd₂], by rw [wr, wr₂]⟩

end VG.Proof.CmacAes.Stream.Arm
