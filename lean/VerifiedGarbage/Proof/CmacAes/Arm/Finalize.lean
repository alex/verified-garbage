import VerifiedGarbage.Proof.CmacAes.Arm.Subkeys
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-CMAC on ARMv7: `vg_cmac_aes_finalize`, the last block

Untrusted: everything here is checked by Lean. The steps that form the last
block `Mₙ` (§6.2 step 4) in the counter block, before the chaining value is
XORed in: `Mₙ* ⊕ K1` for a complete block (`full_wp`), else `Mₙ*` copied a
byte at a time onto zeros (`copy_wp`), `0x80` after it, and the block XORed
with `K2` (`partial_wp`).
-/

namespace VG.Proof.CmacAes.Arm

open VG VG.Arm VG.Impl.CmacAes.Arm
open VG.Proof.MdStream.Arm (Upd Mupd Fupd op2_imm op2_reg wp_mov wp_add wp_subs wp_cmp wp_ldr wp_ldrb wp_strb
  wp_ldrSp saveMem saveList_ok saveMem_frame readW_writeW_save eval_eq eval_ne sub_beq ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨State.addr (W s₀), 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨State.addr (Dp s₀), N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀))

/-- The counter block. -/
abbrev Ca : Addr := State.addr (S s₀) + BitVec.ofNat 64 2048

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, lastR s₀, argsR s₀]
  wr : s₀.wr = [stR s₀, scrR s₀]
  key_st : (keyR s₀).Disjoint (stR s₀)
  key_scr : (keyR s₀).Disjoint (scrR s₀)
  last_st : (lastR s₀).Disjoint (stR s₀)
  last_scr : (lastR s₀).Disjoint (scrR s₀)
  st_scr : (stR s₀).Disjoint (scrR s₀)
  st_args : (stR s₀).Disjoint (argsR s₀)
  scr_args : (scrR s₀).Disjoint (argsR s₀)
  b_key : (belowR s₀).Disjoint (keyR s₀)
  b_last : (belowR s₀).Disjoint (lastR s₀)
  b_st : (belowR s₀).Disjoint (stR s₀)
  b_scr : (belowR s₀).Disjoint (scrR s₀)
  key_fit : (W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  sp8 : 8 ≤ s₀.sp.toNat
  sp_fit : s₀.sp.toNat + 8 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14
  len : N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeArm.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v⟩

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.arg1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.sp_fit
  simp only [stackArgAddr]
  rw [addr_add (by omega), addr_add (by omega)]
  simp

theorem FPre.arg_in {k : Nat} (hk : k < 2) : InRegions (s₀.rd ++ s₀.wr) (stackArgAddr s₀ k) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
  · simpa using Offset.contains_base (stackArgAddr s₀ 0) (d := 0) (n := 4) (k := 8) (by decide) (by decide)
  · rw [hp.arg1]; exact Offset.contains_base _ (by decide) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨State.addr (S s₀) + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨State.addr (W s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ N s₀) :
    Covers [⟨State.addr (Dp s₀) + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨Ca s₀, 16⟩ : Region).Disjoint ⟨State.addr (W s₀) + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨Ca s₀, 16⟩ : Region).Disjoint (lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

end

theorem in_of_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

theorem cov_mono {rs rs' : List Region} {r : Region} (h : Covers [r] rs) (e : rs = rs') : Covers [r] rs' := e ▸ h

/-! ## Saving the registers -/

/-- The registers `finalize` saves, and where. -/
def fsaved : List (Reg × Nat) := [(.r4, 2064), (.r5, 2068), (.lr, 2072)]

/-- The memory after saving them. -/
def fsMem (s₀ : State) : Mem := saveMem s₀.mem (State.addr (S s₀)) s₀.gpr fsaved

theorem finSave_eq : finSave = .ldrSp .r12 4 :: (fsaved.map (fun p => Instr.str p.1 .r12 p.2) ++
    [.mov .r5 (.reg .r12), .ldrSp .r4 0, .cmp .r4 (.imm 16)]) := rfl

theorem fsMem_frame (s₀ : State) : Frame [scrR s₀] s₀.mem (fsMem s₀) :=
  saveMem_frame _ _ _ (by decide) fsaved (by decide)

set_option simprocs false in
theorem fsMem_slot (s₀ : State) {r : Reg} {d : Nat} (h : (r, d) ∈ fsaved) :
    (fsMem s₀).readW (State.addr (S s₀) + BitVec.ofNat 64 d) 32 = s₀.gpr r := by
  simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  simp (disch := decide) only [fsMem, fsaved, saveMem, Mem.readW_writeW_self32, readW_writeW_save]

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → s.gpr r = s₀.gpr r
  r4 : s.gpr .r4 = BitVec.ofNat 32 (N s₀)
  r5 : s.gpr .r5 = S s₀
  z : s.z = decide (N s₀ = 16)
  mem : s.mem = fsMem s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finSave) s₀ (FS s₀) := by
  have hsc := hp.scr_fit
  rw [finSave_eq]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl (hp.arg_in (by decide)) fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = S s₀ := u₁.gpr
  refine saveList_ok fsaved s₁ _ (fun p hp' => ?_) fun s₂ g₂ rd₂ wr₂ sp₂ m₂ => ?_
  · have hb : 2064 ≤ p.2 ∧ p.2 + 4 ≤ 2076 := by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide
    rw [h12, u₁.wr]
    exact ⟨by omega, by omega, in_of_cov (hp.cS (d := p.2) (n := 4) (by omega))⟩
  have hm₂ : s₂.mem = fsMem s₀ := by
    rw [m₂, u₁.mem, h12, fsMem]
    exact saveMem_congr _ _ _ fun p hp' => u₁.other _ (by
      simp only [fsaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
      rcases hp' with rfl | rfl | rfl <;> decide)
  have harg : s₂.mem.readW (stackArgAddr s₀ 0) 32 = stackArg s₀ 0 := by
    rw [hm₂]
    exact (fsMem_frame s₀).readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.scr_args.symm.sub_left UPre.arg_sub) (by decide)
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => ?_
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₃.sp, sp₂, u₁.sp]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact hp.arg_in (by decide)) fun s₄ u₄ => ?_
  refine wp_cmp (op2_imm (by decide)) fun s₅ f₅ z₅ => WP.block_nil ?_
  have a0 : stackArg s₀ 0 = BitVec.ofNat 32 (N s₀) := by simp [N]
  have r4 : s₅.gpr .r4 = BitVec.ofNat 32 (N s₀) := by rw [f₅.gpr, u₄.gpr, u₃.mem, harg, a0]
  refine ⟨fun r h4 h5 h12' => ?_, r4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ h4, u₃.other _ h5, g₂, u₁.other _ h12']
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, g₂, h12]
  · rw [z₅, show s₄.gpr .r4 = s₅.gpr .r4 from (congrFun f₅.gpr _).symm, r4,
      show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl, sub_beq (by have := hp.len; omega) (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  · rw [f₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r5 → r ≠ .r12 → r ≠ .lr → s.gpr r = s₀.gpr r
  r5 : s.gpr .r5 = S s₀
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 = mn s₀

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (fsMem s₀) (State.addr (W s₀) + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (fsMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (fsMem s₀) (State.addr (Dp s₀)) (N s₀) =
    Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) :=
  Proof.Cmac.bytesAt_frame (fsMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega)

end

theorem full_eq : full = xorBlk .r12 .lr .r3 .r0 .r5 0 240 2048 ++ [] := rfl

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ = 16) {s : State} (h : FS s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have r3 : s.gpr .r3 = Dp s₀ := h.keep _ (by decide) (by decide) (by decide)
  have r0 : s.gpr .r0 = W s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [full_eq]
  refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [r3]; omega) (by rw [r0]; omega) (by rw [h.r5]; omega)
    (by rw [r3, add0, hrw]; exact hp.cLast (d := 0) (n := 16) (by omega) |> fun c => by simpa using c)
    (by rw [r0, hrw]; exact hp.cKey (by decide)) (by rw [h.r5, h.wr]; exact hp.cS (by decide))
    fun s' g' => WP.block_nil ?_
  refine ⟨fun r h3 h4 h5 h12 hlr => by rw [g'.gpr r h12 hlr, h.keep r h4 h5 h12], by rw [g'.gpr _ (by decide)
    (by decide), h.r5], by rw [g'.sp, h.sp], by rw [g'.rd, h.rd], by rw [g'.wr, h.wr], ?_, ?_⟩
  · rw [g'.mem, h.mem, h.r5]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g'.mem, h.mem, h.r5, r3, r0, add0, Proof.Cmac.xor4Mem_bytes _
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_last.sub_right (Region.sub_prefix (by omega))))
      (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), hp.key_bytes (by decide)]
    have lb := hp.last_bytes
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

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (h3 : s.gpr .r3 = p) (hlr : s.gpr .lr = c) (h4 : s.gpr .r4 = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨State.addr p, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨State.addr c, 16⟩] s.wr)
    (hd : (⟨State.addr p, L⟩ : Region).Disjoint ⟨State.addr c, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) L) ∧
      s'.gpr .lr = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.ldrb .r12 .r3 0, .strb .r12 .lr 0, .dp .add .r3 .r3 (.imm 1),
      .dp .add .lr .lr (.imm 1), .subs .r4 .r4 (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .r3 = p + BitVec.ofNat 32 i ∧
      t.gpr .lr = c + BitVec.ofNat 32 i ∧ t.gpr .r4 = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (State.addr c) (Spec.Aes.bytesAt s.mem (State.addr p) i) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t.gpr r = s.gpr r) ∧
      t.sp = s.sp ∧ t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [h3]; exact (BitVec.add_zero p).symm, by rw [hlr]; exact (BitVec.add_zero c).symm, by rw [h4, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, x3, xlr, x4, mem, g, sp, rd, wr⟩
  have aP : State.addr (p + BitVec.ofNat 32 i) = State.addr p + BitVec.ofNat 64 i := addr_add (by omega)
  have aC : State.addr (c + BitVec.ofNat 32 i) = State.addr c + BitVec.ofNat 64 i := addr_add (by omega)
  refine wp_ldrb (a := State.addr p + BitVec.ofNat 64 i) (by decide) (by rw [x3, BitVec.add_zero, aP])
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_strb (a := State.addr c + BitVec.ofNat 64 i) (by decide)
    (by rw [u₁.other _ (by decide), xlr, BitVec.add_zero, aC])
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
  have x4' : t₅.gpr .r4 = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.Arm.eval .ne t₅ = _
    rw [eval_ne, z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), x4,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
  have gg : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → t₅.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
    rw [u₅.other _ h₄, u₄.other _ hl, u₃.other _ h₃, v₂.gpr, u₁.other _ h₁₂, g r h₃ h₄ h₁₂ hl]
  have xlr' : t₅.gpr .lr = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xlr,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have x3' : t₅.gpr .r3 = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), x3,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have sp' : t₅.sp = s.sp := by rw [u₅.sp, u₄.sp, u₃.sp, v₂.sp, u₁.sp, sp]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xlr', he], gg, sp', rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, x3', xlr', x4', hmem, gg,
      sp', rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = .mov .r12 (.imm 0) :: (zeroBlk .r12 .r5 2048 ++
    [.dp .add .lr .r5 (.imm (BitVec.ofNat 32 2048)), .cmp .r4 (.imm 0)]) := rfl

theorem padK2_eq : padK2 = .mov .r12 (.imm 0x80) :: .strb .r12 .lr 0 ::
    (xorBlk .r12 .lr .r5 .r0 .r5 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ < 16) {s : State} (h : FS s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cA : State.addr (S s₀ + BitVec.ofNat 32 2048) = Ca s₀ := addr_add (by omega)
  -- Zero the counter block.
  refine WP.seq ?_
  rw [zero_eq]
  refine wp_mov (op2_imm (by decide)) fun s₁ u₁ => ?_
  refine Proof.CmacAes.Arm.zeroBlk_ok u₁.gpr (by decide) (by rw [u₁.other _ (by decide), h.r5]; omega)
    (by rw [u₁.other _ (by decide), h.r5, u₁.wr, h.wr]; exact hp.cS (by decide)) fun s₂ G₂ m₂ rd₂ wr₂ sp₂ => ?_
  refine wp_add (op2_imm (by decide)) fun s₃ u₃ => wp_cmp (op2_imm (by decide)) fun s₄ f₄ z₄ => WP.block_nil ?_
  have r5₂ : s₂.gpr .r5 = S s₀ := by rw [G₂, u₁.other _ (by decide), h.r5]
  have mem₄ : s₄.mem = Proof.Cmac.zero4 (fsMem s₀) (Ca s₀) := by
    rw [f₄.mem, u₃.mem, m₂, u₁.other _ (by decide), h.r5, u₁.mem, h.mem]
  have k₄ : ∀ r, r ≠ .r12 → r ≠ .lr → s₄.gpr r = s.gpr r := fun r h12 hlr => by
    rw [f₄.gpr, u₃.other _ hlr, G₂, u₁.other _ h12]
  have lr₄ : s₄.gpr .lr = S s₀ + BitVec.ofNat 32 2048 := by rw [f₄.gpr, u₃.gpr, r5₂]
  have r4₄ : s₄.gpr .r4 = BitVec.ofNat 32 (N s₀) := by
    rw [k₄ _ (by decide) (by decide), h.r4]
  have sp₄ : s₄.sp = s.sp := by rw [f₄.sp, u₃.sp, sp₂, u₁.sp]
  have rd₄ : s₄.rd = s.rd := by rw [f₄.rd, u₃.rd, rd₂, u₁.rd]
  have wr₄ : s₄.wr = s.wr := by rw [f₄.wr, u₃.wr, wr₂, u₁.wr]
  have ev : isa.eval .eq s₄ = some (decide (N s₀ = 0)) := by
    show VG.Arm.eval .eq s₄ = _
    rw [eval_eq, z₄, show s₃.gpr .r4 = s₄.gpr .r4 from (congrFun f₄.gpr _).symm, r4₄,
      MdStream.Arm.cmp0 (by omega)]
  have fz : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (State.addr (Dp s₀)) (N s₀) =
      Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega), hp.last_bytes]
  have keyZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (State.addr (W s₀) + BitVec.ofNat 64 256) 16 =
      Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 := by
    rw [Proof.Cmac.bytesAt_frame16 fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₅ : State) =>
      s₅.mem = writeBytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)) ∧
      s₅.gpr .lr = S s₀ + BitVec.ofNat 32 (2048 + N s₀) ∧
      (∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₅.gpr r = s.gpr r) ∧
      s₅.sp = s.sp ∧ s₅.rd = s.rd ∧ s₅.wr = s.wr) ?_ fun s₅ h₅ => ?_)
  · by_cases hL0 : N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₄, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [lr₄, hL0], fun r h₃ h₄ h₁₂ hl =>
        k₄ r h₁₂ hl, sp₄, rd₄, wr₄⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp (p := Dp s₀) (c := S s₀ + BitVec.ofNat 32 2048) (L := N s₀) (by omega) (by omega)
        (by rw [k₄ _ (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]) lr₄ r4₄ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [rd₄, wr₄, hrw]; simpa using hp.cLast (d := 0) (n := N s₀) (by omega))
        (by rw [cA, wr₄, h.wr]; exact hp.cS (by decide)) (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₅ ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩
      refine ⟨by rw [m₅, mem₄, cA, lastZ], by rw [lr₅, Offset.add_add], fun r h₃ h₄ h₁₂ hl => by
        rw [g₅ r h₃ h₄ h₁₂ hl, k₄ r h₁₂ hl], by rw [sp₅, sp₄], by rw [rd₅, rd₄], by rw [wr₅, wr₄]⟩
  · obtain ⟨m₅, lr₅, g₅, sp₅, rd₅, wr₅⟩ := h₅
    rw [padK2_eq]
    have aL : State.addr (S s₀ + BitVec.ofNat 32 (2048 + N s₀)) = Ca s₀ + BitVec.ofNat 64 (N s₀) := by
      rw [addr_add (by omega), Offset.add_add]
    refine wp_mov (op2_imm (by decide)) fun s₆ u₆ => ?_
    refine wp_strb (a := Ca s₀ + BitVec.ofNat 64 (N s₀)) (by decide)
      (by rw [u₆.other _ (by decide), lr₅, BitVec.add_zero, aL])
      (by
        rw [u₆.wr, wr₅, h.wr]
        show InRegions s₀.wr (State.addr (S s₀) + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)) 1
        rw [Offset.add_add]
        exact in_of_cov (hp.cS (d := 2048 + N s₀) (n := 1) (by omega))) fun s₇ v₇ => ?_
    have g₇ : ∀ r, r ≠ .r3 → r ≠ .r4 → r ≠ .r12 → r ≠ .lr → s₇.gpr r = s.gpr r := fun r h₃ h₄ h₁₂ hl => by
      rw [v₇.gpr, u₆.other _ h₁₂, g₅ r h₃ h₄ h₁₂ hl]
    have r5₇ : s₇.gpr .r5 = S s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.r5]
    have r0₇ : s₇.gpr .r0 = W s₀ := by
      rw [g₇ _ (by decide) (by decide) (by decide) (by decide), h.keep _ (by decide) (by decide) (by decide)]
    have hlen : (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)).length = N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have m₇ : s₇.mem = (writeBytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀))).writeW (Ca s₀ + BitVec.ofNat 64 (N s₀))
        (0x80 : Byte) := by
      rw [v₇.mem, u₆.gpr, u₆.mem, m₅, b80]
    refine xorBlk_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by rw [r5₇]; omega) (by rw [r0₇]; omega) (by rw [r5₇]; omega)
      (by rw [r5₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]
          exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
            fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [r0₇, v₇.rd, v₇.wr, u₆.rd, u₆.wr, rd₅, wr₅, hrw]; exact hp.cKey (by decide))
      (by rw [r5₇, v₇.wr, u₆.wr, wr₅, h.wr]; exact hp.cS (by decide)) fun s₈ g₈ => WP.block_nil ?_
    have fW : Frame [⟨Ca s₀, 16⟩] (fsMem s₀) s₇.mem := by
      rw [m₇]
      refine (fz.trans (writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)))
      rw [hlen]; simpa using Offset.contains_base (Ca s₀) (d := 0) (n := N s₀) (k := 16) (by omega) (by decide)
    have pad : Spec.Aes.bytesAt s₇.mem (Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (fsMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem (State.addr (Dp s₀)) (N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₇]; exact this
    have k2 : Spec.Aes.bytesAt s₇.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem (State.addr (W s₀) + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨fun r h₃ h₄ h₅ h₁₂ hl => by rw [g₈.gpr r h₁₂ hl, g₇ r h₃ h₄ h₁₂ hl, h.keep r h₄ h₅ h₁₂],
      by rw [g₈.gpr _ (by decide) (by decide), r5₇], by rw [g₈.sp, v₇.sp, u₆.sp, sp₅, h.sp],
      by rw [g₈.rd, v₇.rd, u₆.rd, rd₅, h.rd], by rw [g₈.wr, v₇.wr, u₆.wr, wr₅, h.wr], ?_, ?_⟩
    · rw [g₈.mem, r5₇]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₈.mem, r5₇, r0₇, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [mn, Spec.Cmac.lastBlock, hlen, show N s₀ ≠ 16 by omega, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.Arm
