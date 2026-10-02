import VerifiedGarbage.Proof.CmacTripleDes.Arm.Update
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# TDEA-CMAC on ARMv7: `vg_cmac_triple_des_finalize`, the last block

Untrusted: everything here is checked by Lean. The steps that form the last
block `Mₙ` (§6.2 step 4) in `r4:r5` as little-endian words (`BPost`):
`Mₙ* ⊕ K1` for a complete last block, else `Mₙ*` copied a byte at a time
onto the zeroed bytes `[124, 132)` of the scratch buffer, `0x80` after it,
XORed with `K2`.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Impl.CmacTripleDes.Arm VG.Proof.CmacTripleDes VG.Proof.Cmac VG.WriteBytes
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_sub wp_subs wp_cmp wp_ldrSp wp_ldr
  wp_str wp_rev wp_ldrb wp_strb saveMem saveList_ok cmp0 ofNat_beq_zero sub_ofNat)

section
variable (s₀ : State)

abbrev FW : BitVec 32 := s₀.gpr .r0
abbrev FSt : BitVec 32 := s₀.gpr .r1
abbrev FP : BitVec 32 := s₀.gpr .r2
abbrev FL : Nat := (s₀.gpr .r3).toNat
abbrev FS : BitVec 32 := stackArg s₀ 0

abbrev keyR : Region := ⟨State.addr (FW s₀), 400⟩
abbrev fstR : Region := ⟨State.addr (FSt s₀), 8⟩
abbrev lastR : Region := ⟨State.addr (FP s₀), FL s₀⟩
abbrev fscrR : Region := ⟨State.addr (FS s₀), 640⟩
abbrev fargsR : Region := ⟨stackArgAddr s₀ 0, 4⟩

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, lastR s₀, fargsR s₀]
  wr : s₀.wr = [fstR s₀, fscrR s₀]
  key_st : (keyR s₀).Disjoint (fstR s₀)
  key_scr : (keyR s₀).Disjoint (fscrR s₀)
  last_st : (lastR s₀).Disjoint (fstR s₀)
  last_scr : (lastR s₀).Disjoint (fscrR s₀)
  st_scr : (fstR s₀).Disjoint (fscrR s₀)
  st_args : (fstR s₀).Disjoint (fargsR s₀)
  scr_args : (fscrR s₀).Disjoint (fargsR s₀)
  key_fit : (FW s₀).toNat + 400 ≤ 2 ^ 32
  st_fit : (FSt s₀).toNat + 8 ≤ 2 ^ 32
  last_fit : (FP s₀).toNat + FL s₀ ≤ 2 ^ 32
  scr_fit : (FS s₀).toNat + 640 ≤ 2 ^ 32
  sp_fit : s₀.sp.toNat + 4 ≤ 2 ^ 32
  len : FL s₀ ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- The bytes where a partial last block is formed. -/
abbrev mnR (s₀ : State) : Region := ⟨State.addr (FS s₀) + BitVec.ofNat 64 124, 8⟩

/-- What the first block leaves. -/
structure P1 (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = FS s₀
  r9 : s.gpr .r9 = FW s₀
  r1 : s.gpr .r1 = FSt s₀
  r2 : s.gpr .r2 = FP s₀
  r3 : s.gpr .r3 = s₀.gpr .r3
  sp : s.sp = s₀.sp
  mem : s.mem = savedMem s₀ (FS s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the branch on the length leaves: `Mₙ` in `r4:r5`. -/
structure BPost (s₀ s : State) : Prop where
  r10 : s.gpr .r10 = FS s₀
  r9 : s.gpr .r9 = FW s₀
  r1 : s.gpr .r1 = FSt s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [mnR s₀] (savedMem s₀ (FS s₀)) s.mem
  blk : le8 (s.gpr .r5 ++ s.gpr .r4) = mn s₀.mem (State.addr (FW s₀)) (State.addr (FP s₀)) (FL s₀)

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr (State.addr (FS s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (FW s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := keyR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ FL s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (State.addr (FP s₀) + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := lastR s₀) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

theorem FPre.scrAddr {d : Nat} (h : d < 640) :
    State.addr (FS s₀ + BitVec.ofNat 32 d) = State.addr (FS s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.scr_fit; omega)

theorem FPre.keyAddr {d : Nat} (h : d < 400) :
    State.addr (FW s₀ + BitVec.ofNat 32 d) = State.addr (FW s₀) + BitVec.ofNat 64 d :=
  addr_add (by have := hp.key_fit; omega)

theorem FPre.arg_in : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ 0) 4 := by
  rw [hp.rd]; exact in_rw (r := fargsR s₀) (by simp) (Region.contains_self _ _)

/-- Saving the registers leaves the key unchanged. -/
theorem FPre.keyBytes {d : Nat} (h : d + 8 ≤ 400) :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) (State.addr (FW s₀) + BitVec.ofNat 64 d) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 d) 8 :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))) (by decide)

theorem FPre.lastBytes :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) (State.addr (FP s₀)) (FL s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))) (by have := hp.len; omega)

end

/-! ## The prologue -/

theorem fpre1_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.ldrSp .r12 0] : List Instr) ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)))
      s₀ fun s => P1 s₀ s ∧ s.z = decide (FL s₀ = 8) := by
  have hsc := hp.scr_fit
  have hL := hp.len
  rw [show [Instr.ldrSp .r12 0] ++ save .r12 ++ ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr) =
    .ldrSp .r12 0 :: (saved.map (fun p => Instr.str p.1 .r12 p.2) ++
      ([mov .r10 .r12, mov .r9 .r0, .cmp .r3 (.imm 8)] : List Instr)) from rfl]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl hp.arg_in fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = FS s₀ := u₁.gpr
  refine saveList_ok saved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb := saved_bound p hp'
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, hp.inScr (by omega) (by decide)⟩
  have hm₂ : s₂.mem = savedMem s₀ (FS s₀) := by
    rw [m₂, u₁.mem, h12, savedMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (saved_ne_r12 p hp')
  simp only [mov]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [f₅.gpr, u₄.gpr, u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide)]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  · rw [z₅, u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide),
      show s₀.gpr .r3 = BitVec.ofNat 32 (FL s₀) by simp [FL], show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl,
      MdStream.Arm.sub_beq (by omega) (by decide)]

/-! ## A complete last block -/

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ = 8) {s : State} (h : P1 s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  simp only [full]
  refine wp_ldr (by decide) (by rw [h.r2, add0]) (by rw [hrw]; simpa using hp.inLast (d := 0) (n := 4) (by omega) (by decide))
    fun s₁ u₁ => ?_
  refine wp_ldr (a := State.addr (FP s₀) + BitVec.ofNat 64 4) (by decide)
    (by rw [u₁.other _ (by decide), h.r2]; exact addr_add (by omega))
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.inLast (d := 4) (n := 4) (by omega) (by decide)) fun s₂ u₂ => ?_
  refine wp_ldr (by decide) (by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₃ u₃ => ?_
  refine wp_ldr (by decide) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.r9,
      hp.keyAddr (by decide)])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inKey (by decide) (by decide)) fun s₄ u₄ => ?_
  refine wp_eor (op2_reg _ _) fun s₅ u₅ => wp_eor (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7] → s₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₆.other _ hr.2.1, u₅.other _ hr.1, u₄.other _ hr.2.2.2, u₃.other _ hr.2.2.1, u₂.other _ hr.2.1,
      u₁.other _ hr.1]
  have mem : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [g _ (by decide), h.r10], by rw [g _ (by decide), h.r9], by rw [g _ (by decide), h.r1],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, u₁.sp, h.sp], by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd],
    by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr], by rw [mem, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [u₆.gpr, u₆.other .r4 (by decide), u₅.gpr, u₅.other .r5 (by decide), u₅.other .r7 (by decide), u₄.gpr,
    u₄.other .r4 (by decide), u₄.other .r5 (by decide), u₄.other .r6 (by decide), u₃.gpr, u₃.other .r4 (by decide),
    u₃.other .r5 (by decide), u₂.gpr, u₂.other .r4 (by decide), u₁.gpr, u₃.mem, u₂.mem, u₁.mem,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (FW s₀) + BitVec.ofNat 64 388 = State.addr (FW s₀) + BitVec.ofNat 64 384 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 384 4).symm, ← readW64_split, h.mem, le8_xor, le8_readW, le8_readW,
    hp.keyBytes (by decide)]
  have lb := hp.lastBytes
  rw [hL] at lb
  rw [lb]
  simp only [mn, Spec.Cmac.lastBlock, Proof.Cmac.bytesAt_length, hL, ite_true]
  exact Proof.Cmac.xor_comm _ _

/-! ## Copying the last bytes -/

theorem byte_rt32 (b : BitVec 8) : (b.setWidth 32).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth]
  omega

theorem eval_ne' (s : State) : isa.eval .ne s = some !s.z := rfl

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 8)
    (h7 : s.gpr .r7 = p) (h6 : s.gpr .r6 = c) (h8 : s.gpr .r8 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 8 ≤ 2 ^ 32)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (State.addr p + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (State.addr c + BitVec.ofNat 64 i) 1)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 8⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .r6 = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r4 .r7 0, .strb .r4 .r6 0, .dp .add .r7 .r7 (.imm 1),
      .dp .add .r6 .r6 (.imm 1), .subs .r8 .r8 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r7 = p + BitVec.ofNat 32 i ∧
      t.gpr .r6 = c + BitVec.ofNat 32 i ∧ t.gpr .r8 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h7]; exact (BitVec.add_zero p).symm, by rw [h6]; exact (BitVec.add_zero c).symm,
      by rw [h8, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x7, x6, x8, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x7, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), x6, BitVec.add_zero, aC]) (by rw [u₁.wr, wr]; exact hw i (by omega))
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
  have x8' : t₅.gpr .r8 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    rw [eval_ne', z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x8,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r4 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → t₅.gpr r = s.gpr r := fun r h₄ h₆ h₇ h₈ => by
    rw [u₅.other _ h₈, u₄.other _ h₆, u₃.other _ h₇, v₂.gpr, u₁.other _ h₄, g r h₄ h₆ h₇ h₈]
  have x6' : t₅.gpr .r6 = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x6,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x7' : t₅.gpr .r7 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x7,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [x6', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x7', x6', x8', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ < 8) {s : State} (h : P1 s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  let C : Addr := State.addr (FS s₀) + BitVec.ofNat 64 124
  have hC : State.addr (FS s₀ + BitVec.ofNat 32 124) = C := hp.scrAddr (by decide)
  have hC4 : State.addr (FS s₀ + BitVec.ofNat 32 128) = C + BitVec.ofNat 64 4 := by
    rw [hp.scrAddr (by decide)]; exact (Offset.add_add _ 124 4).symm
  have cIn : ∀ i < 8, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [Offset.add_add]; exact hp.inScr (by omega) (by decide)
  -- Zero the bytes.
  refine WP.seq ?_
  simp only [zero, mov]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine wp_str (by decide) (by rw [u₁.other _ (by decide), h.r10, hC])
    (by rw [u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₂ w₂ => ?_
  refine wp_str (by decide) (by rw [w₂.gpr, u₁.other _ (by decide), h.r10, hC4])
    (by rw [w₂.wr, u₁.wr, h.wr]; rw [Offset.add_add]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  refine wp_add (op2_imm (by decide)) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _)
    fun s₆ u₆ => wp_cmp (op2_imm (by decide)) fun s₇ f₇ z₇ => WP.block_nil ?_
  let m₁ := ((savedMem s₀ (FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
  have mem₇ : s₇.mem = m₁ := by
    rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, w₃.mem, w₂.mem, w₂.gpr, u₁.gpr, u₁.mem, h.mem]
  have g₇ : ∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → s₇.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₇.gpr, u₆.other _ hr.2.2.2, u₅.other _ hr.2.2.1, u₄.other _ hr.2.1, w₃.gpr, w₂.gpr, u₁.other _ hr.1]
  have r6₇ : s₇.gpr .r6 = FS s₀ + BitVec.ofNat 32 124 := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r10]; rfl
  have r7₇ : s₇.gpr .r7 = FP s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r2]
  have r8₇ : s₇.gpr .r8 = BitVec.ofNat 32 (FL s₀) := by
    rw [f₇.gpr, u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide),
      h.r3]; simp [FL]
  have z7 : s₇.z = decide (FL s₀ = 0) := by
    rw [z₇, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr,
      u₁.other _ (by decide), h.r3, show s₀.gpr .r3 = BitVec.ofNat 32 (FL s₀) by simp [FL]]
    exact cmp0 (by omega)
  have rd₇ : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, w₃.rd, w₂.rd, u₁.rd, h.rd]
  have wr₇ : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, w₃.wr, w₂.wr, u₁.wr, h.wr]
  have sp₇ : s₇.sp = s₀.sp := by rw [f₇.sp, u₆.sp, u₅.sp, u₄.sp, w₃.sp, w₂.sp, u₁.sp, h.sp]
  have dPC : (lastR s₀).Disjoint ⟨C, 8⟩ := hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have lastM₁ : Spec.Aes.bytesAt m₁ (State.addr (FP s₀)) (FL s₀) = Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) := by
    rw [← hp.lastBytes]
    refine bytesAt_frame (rs := [⟨C, 8⟩]) ?_ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
    refine ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by decide) (by decide))
    simpa using Offset.contains_base C (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (t : State) =>
      t.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)) ∧
      t.gpr .r6 = FS s₀ + BitVec.ofNat 32 124 + BitVec.ofNat 32 (FL s₀) ∧
      (∀ r, r ∉ [Reg.r4, .r6, .r7, .r8] → t.gpr r = s.gpr r) ∧
      t.sp = s₀.sp ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr) ?_ fun t ht => ?_)
  · by_cases hL0 : FL s₀ = 0
    · refine WP.ite true (by show some s₇.z = _; rw [z7, hL0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₇, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [r6₇, hL0]; exact (BitVec.add_zero _).symm, g₇, sp₇, rd₇, wr₇⟩
    · refine WP.ite false (by show some s₇.z = _; rw [z7]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp (p := FP s₀) (c := FS s₀ + BitVec.ofNat 32 124) (by omega) (by omega) r7₇ r6₇ r8₇
        (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (fun i hi => by rw [rd₇, wr₇]; exact hp.inLast (by omega) (by decide))
        (fun i hi => by rw [wr₇, hC]; exact cIn i hi) (by rw [hC]; exact dPC)) ?_
      rintro t ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, mem₇, hC, lastM₁], r6₂, fun r hr => by
        rw [g₂ r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
          (fun h => hr (by simp [h])), g₇ r hr], by rw [sp₂, sp₇], by rw [rd₂, rd₇], by rw [wr₂, wr₇]⟩
  obtain ⟨m₂, r6₂, g₂, sp₂, rd₂, wr₂⟩ := ht
  have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)).length = FL s₀ := Proof.Cmac.bytesAt_length _ _ _
  have cL : State.addr (t.gpr .r6 + BitVec.ofNat 32 0) = C + BitVec.ofNat 64 (FL s₀) := by
    rw [r6₂, add0, Straight.add_ofNat_ofNat, addr_add (by omega)]
    show _ = State.addr (FS s₀) + BitVec.ofNat 64 124 + BitVec.ofNat 64 (FL s₀)
    rw [Offset.add_add]
  have trw : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂]
  simp only [padK2]
  refine wp_mov (op2_imm (by decide)) fun t₁ v₁ => ?_
  refine wp_strb (by decide) (by rw [v₁.other _ (by decide), cL]) (by rw [v₁.wr, wr₂]; exact cIn _ hL)
    fun t₂ v₂ => ?_
  refine wp_ldr (by decide) (by rw [v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10, hC])
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact wr_in (hp.inScr (by decide) (by decide))) fun t₃ v₃ => ?_
  refine wp_ldr (by decide) (by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), g₂ _ (by decide), h.r10,
      hC4])
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw, Offset.add_add]
        exact wr_in (hp.inScr (by decide) (by decide))) fun t₄ v₄ => ?_
  refine wp_ldr (by decide) (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide),
      g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact hp.inKey (by decide) (by decide))
    fun t₅ v₅ => ?_
  refine wp_ldr (by decide) (by rw [v₅.other _ (by decide), v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr,
      v₁.other _ (by decide), g₂ _ (by decide), h.r9, hp.keyAddr (by decide)])
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]
        exact hp.inKey (by decide) (by decide)) fun t₆ v₆ => ?_
  refine wp_eor (op2_reg _ _) fun t₇ v₇ => wp_eor (op2_reg _ _) fun t₈ v₈ => WP.block_nil ?_
  let m₃ := (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀))).writeW
    (C + BitVec.ofNat 64 (FL s₀)) (0x80 : Byte)
  have mem₂ : t₂.mem = m₃ := by rw [v₂.mem, v₁.mem, m₂, v₁.gpr, b80]
  have g₈ : ∀ r, r ∉ [Reg.r4, .r5, .r6, .r7, .r8] → t₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₈.other _ hr.2.1, v₇.other _ hr.1, v₆.other _ hr.2.2.2.1, v₅.other _ hr.2.2.1, v₄.other _ hr.2.1,
      v₃.other _ hr.1, v₂.gpr, v₁.other _ hr.1, g₂ r (by simp [hr.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2])]
  -- The frame.
  have cR : ∀ d n, d + n ≤ 8 → (mnR s₀).Contains (C + BitVec.ofNat 64 d) n := fun d n h =>
    Offset.contains_base _ h (by omega)
  have fr : Frame [mnR s₀] (savedMem s₀ (FS s₀)) m₃ := by
    refine ((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ ?_).writeW (List.mem_singleton_self _) _
      (cR 4 4 (by decide))).trans (writeBytes_frame _ _ _ ?_)).writeW (List.mem_singleton_self _) _
      (cR _ 1 (by omega))
    · simpa using cR 0 4 (by decide)
    · rw [hlen]; simpa using cR 0 (FL s₀) (by omega)
  -- The block.
  have kD : (⟨State.addr (FW s₀) + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint (mnR s₀) :=
    (hp.key_scr.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
  have k2 : Spec.Aes.bytesAt m₃ (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FW s₀) + BitVec.ofNat 64 392) 8 := by
    rw [bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
      hp.keyBytes (by decide)]
  have pad : Spec.Aes.bytesAt m₃ C 8 =
      Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀) ++ [0x80] ++ Spec.Cmac.zeros (8 - FL s₀ - 1) := by
    have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
      rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi]; decide
    have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem (State.addr (FP s₀)) (FL s₀)) (by rw [hlen]; exact hL) hz
    rw [hlen] at this
    exact this
  refine ⟨by rw [g₈ _ (by decide), h.r10], by rw [g₈ _ (by decide), h.r9], by rw [g₈ _ (by decide), h.r1],
    by rw [v₈.sp, v₇.sp, v₆.sp, v₅.sp, v₄.sp, v₃.sp, v₂.sp, v₁.sp, sp₂],
    by rw [v₈.rd, v₇.rd, v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₂],
    by rw [v₈.wr, v₇.wr, v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₂],
    by rw [v₈.mem, v₇.mem, v₆.mem, v₅.mem, v₄.mem, v₃.mem, mem₂]; exact fr, ?_⟩
  rw [v₈.gpr, v₈.other .r4 (by decide), v₇.gpr, v₇.other .r5 (by decide), v₇.other .r7 (by decide), v₆.gpr,
    v₆.other .r4 (by decide), v₆.other .r5 (by decide), v₆.other .r6 (by decide), v₅.gpr, v₅.other .r4 (by decide),
    v₅.other .r5 (by decide), v₄.gpr, v₄.other .r4 (by decide), v₃.gpr, v₅.mem, v₄.mem, v₃.mem, mem₂,
    ← BitVec.xor_append, ← readW64_split,
    show State.addr (FW s₀) + BitVec.ofNat 64 396 = State.addr (FW s₀) + BitVec.ofNat 64 392 + BitVec.ofNat 64 4 from
      (Offset.add_add _ 392 4).symm, ← readW64_split, le8_xor, le8_readW, le8_readW, pad, k2]
  simp only [mn, Spec.Cmac.lastBlock, hlen, show FL s₀ ≠ 8 by omega, ite_false]
  exact Proof.Cmac.xor_comm _ _

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (BPost s₀) := by
  refine WP.seq (WP.mono (fpre1_wp hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  by_cases hL : FL s₀ = 8
  · exact WP.ite true (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by show some s₁.z = _; rw [z₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

end VG.Proof.CmacTripleDes.Arm
