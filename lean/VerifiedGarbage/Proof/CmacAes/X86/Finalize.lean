import VerifiedGarbage.Proof.CmacAes.X86.UpdateCorrect
import VerifiedGarbage.Proof.Cmac.Block
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# AES-CMAC on x86: `vg_cmac_aes_finalize`, the last block

The steps that form the last block `Mₙ` (§6.2 step 4) in the counter block,
before the chaining value is XORed in: `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros (`copy_wp`), `0x80`
after it, and the block XORed with `K2` (`partial_wp`). The arguments are
those of `vg_cmac_aes_update` but `last` (`Dp`) and `last_len` (`N`), so its
abbreviations serve.
-/

namespace VG.Proof.CmacAes.X86

open VG VG.X86 VG.Impl.CmacAes.X86
open VG.Proof.Aes.X86 (Ctr32Impl)

variable (v : Ctr32Impl)
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_subi wp_cmpi wp_test wp_movzx8 wp_store8
  eval_e eval_ne ofNat_beq_zero sub_ofNat)
open VG.WriteBytes (writeBytes writeBytes_nil writeBytes_snoc writeBytes_frame)

section
variable (s₀ : State)

/-- The key: the schedule and the subkeys `K1` and `K2` after it. -/
abbrev keyR : Region := ⟨(W s₀).setWidth 64, 272⟩
/-- The last bytes `Mₙ*`. -/
abbrev lastR : Region := ⟨(Dp s₀).setWidth 64, N s₀⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes. -/
abbrev mn : List Byte :=
  Spec.Cmac.lastBlock 16 (Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 240) 16)
    (Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16)
    (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀))

/-- The counter block. -/
abbrev Ca : Addr := (S s₀).setWidth 64 + BitVec.ofNat 64 2048

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
  args_st : (argsR s₀).Disjoint (stR s₀)
  args_scr : (argsR s₀).Disjoint (scrR s₀)
  ret_st : (retR s₀).Disjoint (stR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  b_key : (stkR s₀).Disjoint (keyR s₀)
  b_last : (stkR s₀).Disjoint (lastR s₀)
  b_st : (stkR s₀).Disjoint (stR s₀)
  b_scr : (stkR s₀).Disjoint (scrR s₀)
  key_fit : (W s₀).toNat + 272 ≤ 2 ^ 32
  st_fit : (St s₀).toNat + 16 ≤ 2 ^ 32
  last_fit : (Dp s₀).toNat + N s₀ ≤ 2 ^ 32
  scr_fit : (S s₀).toNat + 2176 ≤ 2 ^ 32
  esp28 : 28 ≤ (E s₀).toNat
  esp_fit : (E s₀).toNat + 28 ≤ 2 ^ 32
  rounds : R s₀ = 10 ∨ R s₀ = 12 ∨ R s₀ = 14
  len : N s₀ ≤ 16

theorem FPre.of {s₀ : State} (h : finalizeX86.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r, t, u, v, w, x⟩

theorem in_cov {rs : List Region} {a : Addr} {n : Nat} (h : Covers [⟨a, n⟩] rs) : InRegions rs a n :=
  h _ _ ⟨_, List.mem_singleton_self _, Region.contains_self _ _⟩

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.below_eq : below (E s₀) 28 = stkR s₀ := by
  simp only [below]; rw [Taint.sub_setWidth hp.esp28]

theorem FPre.argA {i : Nat} (hi : i < 6) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  simp only [argAddr]
  rw [show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * i)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * i) from rfl,
    show (s₀.gpr .esp + BitVec.ofNat 32 (4 + 4 * 0)).setWidth 64 = addr (s₀.gpr .esp) (4 + 4 * 0) from rfl,
    addr_eq (by omega), addr_eq (by omega), Offset.add_add]

theorem FPre.arg_sub {i : Nat} (hi : i < 6) : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
  rw [hp.argA hi]; exact Offset.sub_base _ (by omega)

theorem FPre.arg_in {i : Nat} (hi : i < 6) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 := by
  refine ⟨argsR s₀, by simp [hp.rd], ?_⟩
  rw [hp.argA hi]; exact Offset.contains_base _ (by omega) (by omega)

theorem FPre.args_stk : (argsR s₀).Disjoint (stkR s₀) := by
  have : (s₀.gpr .esp).toNat + 28 ≤ 2 ^ 32 := hp.esp_fit
  have e : argAddr s₀ 0 = (E s₀).setWidth 64 + BitVec.ofNat 64 4 := addr_eq (by omega)
  show Region.Disjoint ⟨argAddr s₀ 0, 24⟩ _
  rw [e]; exact (Offset.disjoint_below_above _ (by decide)).symm

/-- The stack arguments are unchanged where only `Big` changes. -/
theorem FPre.arg_keep {m : Mem} (hf : Frame (Big s₀) s₀.mem m) {i : Nat} (hi : i < 6) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  hf.readW (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.args_st.sub_left (hp.arg_sub hi)
    · exact hp.args_scr.sub_left (hp.arg_sub hi)
    · exact hp.args_stk.sub_left (hp.arg_sub hi)) (by decide)

theorem FPre.cS {d n : Nat} (h : d + n ≤ 2176) :
    Covers [⟨(S s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] s₀.wr := by
  rw [hp.wr]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨scrR s₀, by simp, d, rfl, h⟩

theorem FPre.cKey {d n : Nat} (h : d + n ≤ 272) :
    Covers [⟨(W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨keyR s₀, by simp, d, rfl, h⟩

theorem FPre.cLast {d n : Nat} (h : d + n ≤ N s₀) :
    Covers [⟨(Dp s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩] (s₀.rd ++ s₀.wr) := by
  rw [hp.rd]
  exact Covers.of_sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨lastR s₀, by simp, d, rfl, h⟩

theorem FPre.ca_key {d n : Nat} (h : d + n ≤ 272) :
    (⟨Ca s₀, 16⟩ : Region).Disjoint ⟨(W s₀).setWidth 64 + BitVec.ofNat 64 d, n⟩ :=
  (hp.key_scr.symm.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ h)

theorem FPre.ca_last : (⟨Ca s₀, 16⟩ : Region).Disjoint (lastR s₀) :=
  hp.last_scr.symm.sub_left (Offset.sub_base _ (by decide))

theorem FPre.cA : (S s₀ + BitVec.ofNat 32 2048).setWidth 64 = Ca s₀ :=
  addr_eq (by have := hp.scr_fit; omega)

theorem FPre.key_bytes {d : Nat} (h : d + 16 ≤ 272) :
    Spec.Aes.bytesAt (savedMem s₀) ((W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 =
      Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 d) 16 :=
  Proof.Cmac.bytesAt_frame16 (savedMem_frame s₀) fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ h)

theorem FPre.last_bytes : Spec.Aes.bytesAt (savedMem s₀) ((Dp s₀).setWidth 64) (N s₀) =
    Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) :=
  Proof.Cmac.bytesAt_frame (savedMem_frame s₀) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact hp.last_scr) (by have := hp.len; omega)

end

/-! ## Saving the registers -/

theorem finSave_eq : finSave = .mov .eax (argOp 5) :: (saved.map (fun p => Instr.store (at_ .eax p.2) p.1) ++
    ([.mov .ebp (.reg .eax), .mov .ecx (argOp 4), .alu .cmp .ecx (.imm 16)] : List Instr)) := rfl

/-- What `finSave` leaves. -/
structure FS (s₀ s : State) : Prop where
  keep : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .ebp → s.gpr r = s₀.gpr r
  ecx : s.gpr .ecx = BitVec.ofNat 32 (N s₀)
  ebp : s.gpr .ebp = S s₀
  zf : s.zf = some (decide (N s₀ = 16))
  mem : s.mem = savedMem s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem finSave_wp {s₀ : State} (hp : FPre s₀) : WP isa (.block finSave) s₀ (FS s₀) := by
  have hsc := hp.scr_fit
  rw [finSave_eq]
  refine wp_arg (s₀ := s₀) rfl (hp.arg_in (by decide)) rfl fun s₁ u₁ => ?_
  have h₁ : s₁.gpr .eax = S s₀ := u₁.gpr
  refine Spill.save_ofNat_ok saved saved_fits (by rw [h₁]; omega) (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    rw [h₁, u₁.wr, hp.wr]
    exact ⟨scrR s₀, by simp, Offset.contains_base _ (by omega) (by omega)⟩
  have hm₂ : s₂.mem = savedMem s₀ := by
    rw [u₂.mem, u₁.mem, h₁, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have esp₂ : s₂.gpr .esp = s₀.gpr .esp := by rw [u₂.gpr, u₁.other _ (by decide)]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), esp₂])
    (by rw [u₃.rd, u₃.wr, rw₂]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₄ u₄ => ?_
  refine wp_cmpi fun s₅ f₅ _ z₅ => WP.block_nil ⟨fun r ha hc hb => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f₅.gpr, u₄.other _ hc, u₃.other _ hb, u₂.gpr, u₁.other _ ha]
  · rw [f₅.gpr, u₄.gpr]; exact arg_ofNat s₀ 4
  · rw [f₅.gpr, u₄.other _ (by decide), u₃.gpr, u₂.gpr, h₁]
  · rw [z₅, u₄.gpr, arg_ofNat s₀ 4, show (16 : BitVec 32) = BitVec.ofNat 32 16 from rfl,
      MdStream.X86.sub_beq (arg s₀ 4).isLt (by decide)]
  · rw [f₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  · rw [f₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]

/-! ## The last block -/

/-- What the branch on the length leaves: `Mₙ` in the counter block. -/
structure BPost (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = S s₀
  esp : s.gpr .esp = E s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) s.mem
  blk : Spec.Aes.bytesAt s.mem (Ca s₀) 16 = mn s₀

theorem full_eq : full = .mov .ebx (argOp 3) :: .mov .edx (argOp 0) :: (xor4 .ebx .edx .ebp 0 240 2048 ++ []) := rfl

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ = 16) {s : State} (h : FS s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have esp : s.gpr .esp = E s₀ := h.keep _ (by decide) (by decide) (by decide)
  rw [full_eq]
  refine wp_arg (s₀ := s₀) esp (by rw [hrw]; exact hp.arg_in (by decide))
    (by rw [h.mem]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₁ u₁ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₁.other _ (by decide), esp])
    (by rw [u₁.rd, u₁.wr, hrw]; exact hp.arg_in (by decide))
    (by rw [u₁.mem, h.mem]; exact hp.arg_keep (savedMem_big s₀) (by decide)) fun s₂ u₂ => ?_
  have b₂ : s₂.gpr .ebx = Dp s₀ := by rw [u₂.other _ (by decide), u₁.gpr]
  have d₂ : s₂.gpr .edx = W s₀ := u₂.gpr
  have p₂ : s₂.gpr .ebp = S s₀ := by rw [u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
  have rw₂ : s₂.rd ++ s₂.wr = s₀.rd ++ s₀.wr := by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]
  have w₂ : s₂.wr = s₀.wr := by rw [u₂.wr, u₁.wr, h.wr]
  have lf' : (Dp s₀).toNat + 16 ≤ 2 ^ 32 := by rw [← hL]; exact lf
  refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rw [b₂]; omega) (by rw [d₂]; omega) (by rw [p₂]; omega)
    (by rw [b₂, rw₂]; exact hp.cLast (by omega)) (by rw [d₂, rw₂]; exact hp.cKey (by decide))
    (by rw [p₂, w₂]; exact hp.cS (by decide)) fun s₃ g₃ => WP.block_nil ?_
  refine ⟨by rw [g₃.gpr _ (by decide) (by decide), p₂],
    by rw [g₃.gpr _ (by decide) (by decide), u₂.other _ (by decide), u₁.other _ (by decide), esp],
    by rw [g₃.rd, u₂.rd, u₁.rd, h.rd], by rw [g₃.wr, w₂], ?_, ?_⟩
  · rw [g₃.mem, p₂, u₂.mem, u₁.mem, h.mem]; exact Proof.Cmac.xor4Mem_frame _ _ _ _
  · rw [g₃.mem, p₂, b₂, d₂, u₂.mem, u₁.mem, h.mem, add0, Proof.Cmac.xor4Mem_bytes _
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

theorem addr_at {p : BitVec 32} {i : Nat} (h : p.toNat + i < 2 ^ 32) :
    addr (p + BitVec.ofNat 32 i) 0 = p.setWidth 64 + BitVec.ofNat 64 i := by
  simp only [addr, add0']; exact addr_eq h

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 16)
    (hsi : s.gpr .esi = p) (hdi : s.gpr .edi = c) (hcx : s.gpr .ecx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 16 ≤ 2 ^ 32)
    (hr : Covers [⟨p.setWidth 64, L⟩] (s.rd ++ s.wr)) (hw : Covers [⟨c.setWidth 64, 16⟩] s.wr)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, 16⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      s'.gpr .edi = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .esi 0), .store8 (at_ .edi 0) .al,
      .alu .add .esi (.imm 1), .alu .add .edi (.imm 1), .alu .sub .ecx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .esi = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .ecx = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hsi, add0'], by rw [hdi, add0'], by rw [hcx, Nat.sub_zero],
      by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xsi, xdi, xcx, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at', xsi]; exact addr_at (by omega))
    (by rw [rd, wr]; exact hr _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [ea_at', u₁.other _ (by decide), xdi]; exact addr_at (by omega))
    (by rw [u₁.wr, wr]; exact hw _ _ ⟨_, List.mem_singleton_self _, Offset.contains_base _ (by omega) (by omega)⟩)
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have al : t₁.gpr Reg8.al.reg = (t.mem (p.setWidth 64 + BitVec.ofNat 64 i)).setWidth 32 := u₁.gpr
  have hmem : t₅.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, al, u₁.mem, mem, byte_rt32, hx, Proof.Cmac.bytesAt_succ,
      writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have cx₄ : t₄.gpr .ecx = BitVec.ofNat 32 (L - i) := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xcx]
  have xcx' : t₅.gpr .ecx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub]
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    show VG.X86.eval .ne t₅ = _
    rw [eval_ne, z₅, cx₄, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, sub_ofNat (by omega), Nat.sub_sub,
      ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → t₅.gpr r = s.gpr r := fun r ha hc hs hd' => by
    rw [u₅.other _ hc, u₄.other _ hd', u₃.other _ hs, v₂.gpr, u₁.other _ ha, g r ha hc hs hd']
  have xdi' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xdi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xsi' : t₅.gpr .esi = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xsi,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xdi', he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xsi', xdi', xcx', hmem, gg,
      rd', wr'⟩

/-! ## A partial last block -/

theorem zero_eq : zero = zero4 .ebp 2048 ++ ([.mov .edi (.reg .ebp), .alu .add .edi (.imm (BitVec.ofNat 32 2048)),
    .mov .esi (argOp 3), .mov .ecx (argOp 4), .alu .test .ecx (.reg .ecx)] : List Instr) := rfl

theorem padK2_eq : padK2 = .mov .eax (.imm 0x80) :: .store8 (at_ .edi 0) .al :: .mov .edx (argOp 0) ::
    (xor4 .ebp .edx .ebp 2048 256 2048 ++ []) := rfl

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : N s₀ < 16) {s : State} (h : FS s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have sf' : (arg s₀ 5).toNat + 2176 ≤ 2 ^ 32 := sf
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have cA := hp.cA
  -- Zero the counter block.
  refine WP.seq ?_
  rw [zero_eq]
  refine zero4_ok (b := .ebp) (d := 2048) (by decide) (by rw [h.ebp]; omega)
    (by rw [h.ebp, h.wr]; exact hp.cS (by decide)) fun s₁ g₁ m₁ rd₁ wr₁ => ?_
  have p₁ : s₁.gpr .ebp = S s₀ := by rw [g₁ _ (by decide), h.ebp]
  have esp₁ : s₁.gpr .esp = E s₀ := by rw [g₁ _ (by decide), h.keep _ (by decide) (by decide) (by decide)]
  have fz : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) :=
    Proof.Cmac.frame_store4 _ _ _ _ _
  have mem₁ : s₁.mem = Proof.Cmac.zero4 (savedMem s₀) (Ca s₀) := by rw [m₁, h.ebp, h.mem]
  have big₁ : Frame (Big s₀) s₀.mem s₁.mem := by
    rw [mem₁]
    exact (savedMem_big s₀).trans (fz.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
  have rw₁ : s₁.rd ++ s₁.wr = s₀.rd ++ s₀.wr := by rw [rd₁, wr₁, hrw]
  refine wp_mov fun s₂ u₂ => wp_addi fun s₃ u₃ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) (by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), esp₁])
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, rw₁]; exact hp.arg_in (by decide))
    (by rw [u₄.mem, u₃.mem, u₂.mem]; exact hp.arg_keep big₁ (by decide)) fun s₅ u₅ => ?_
  refine wp_test fun s₆ f₆ z₆ => WP.block_nil ?_
  have k₆ : ∀ r, r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₆.gpr r = s₁.gpr r := fun r hc hs hd => by
    rw [f₆.gpr, u₅.other _ hc, u₄.other _ hs, u₃.other _ hd, u₂.other _ hd]
  have edi₆ : s₆.gpr .edi = S s₀ + BitVec.ofNat 32 2048 := by
    rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, p₁]
  have esi₆ : s₆.gpr .esi = Dp s₀ := by rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]
  have ecx₆ : s₆.gpr .ecx = BitVec.ofNat 32 (N s₀) := by rw [f₆.gpr, u₅.gpr]; exact arg_ofNat s₀ 4
  have mem₆ : s₆.mem = Proof.Cmac.zero4 (savedMem s₀) (Ca s₀) := by
    rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, mem₁]
  have rd₆ : s₆.rd = s₀.rd := by rw [f₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, h.rd]
  have wr₆ : s₆.wr = s₀.wr := by rw [f₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, h.wr]
  have ev : isa.eval .e s₆ = some (decide (N s₀ = 0)) := by
    show VG.X86.eval .e s₆ = _
    rw [eval_e, z₆, u₅.gpr, arg_ofNat s₀ 4, ofNat_and_self_beq (arg s₀ 4).isLt]
  have lastZ : Spec.Aes.bytesAt (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) ((Dp s₀).setWidth 64) (N s₀) =
      Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) := by
    rw [Proof.Cmac.bytesAt_frame fz (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.ca_last.symm) (by omega), hp.last_bytes]
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (s₇ : State) =>
      s₇.mem = writeBytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)) ∧
      s₇.gpr .edi = S s₀ + BitVec.ofNat 32 (2048 + N s₀) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₇.gpr r = s₆.gpr r) ∧
      s₇.rd = s₀.rd ∧ s₇.wr = s₀.wr) ?_ fun s₇ h₇ => ?_)
  · by_cases hL0 : N s₀ = 0
    · refine WP.ite true (by rw [ev]; simp [hL0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₆, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil], by rw [edi₆, hL0],
        fun _ _ _ _ _ => rfl, rd₆, wr₆⟩
    · refine WP.ite false (by rw [ev]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      have hr := hp.cLast (d := 0) (n := N s₀) (by omega)
      rw [add0] at hr
      refine WP.mono (copy_wp (p := Dp s₀) (c := S s₀ + BitVec.ofNat 32 2048) (L := N s₀) (by omega) (by omega)
        esi₆ edi₆ ecx₆ lf
        (by rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 2048) (by decide),
          Nat.mod_eq_of_lt (by omega)]; omega)
        (by rw [rd₆, wr₆]; exact hr) (by rw [cA, wr₆]; exact hp.cS (by decide))
        (by rw [cA]; exact hp.ca_last.symm)) ?_
      rintro s₇ ⟨m₇, di₇, g₇, rd₇, wr₇⟩
      exact ⟨by rw [m₇, mem₆, cA, lastZ], by rw [di₇, Offset.add_add], g₇, by rw [rd₇, rd₆], by rw [wr₇, wr₆]⟩
  · obtain ⟨m₇, di₇, g₇, rd₇, wr₇⟩ := h₇
    rw [padK2_eq]
    refine wp_movi fun s₈ u₈ => ?_
    refine wp_store8 (a := Ca s₀ + BitVec.ofNat 64 (N s₀))
      (by
        rw [ea_at', u₈.other _ (by decide), di₇, addr_at (by omega)]
        show _ = (S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)
        rw [Offset.add_add])
      (by
        rw [u₈.wr, wr₇]
        show InRegions s₀.wr ((S s₀).setWidth 64 + BitVec.ofNat 64 2048 + BitVec.ofNat 64 (N s₀)) 1
        rw [Offset.add_add]
        exact in_cov (hp.cS (d := 2048 + N s₀) (n := 1) (by omega))) fun s₉ v₉ => ?_
    have g₉ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → r ≠ .edi → s₉.gpr r = s₁.gpr r := fun r ha hc hs hd => by
      rw [v₉.gpr, u₈.other _ ha, g₇ r ha hc hs hd, k₆ r hc hs hd]
    have esp₉ : s₉.gpr .esp = E s₀ := by
      rw [g₉ _ (by decide) (by decide) (by decide) (by decide), esp₁]
    have rw₉ : s₉.rd ++ s₉.wr = s₀.rd ++ s₀.wr := by rw [v₉.rd, v₉.wr, u₈.rd, u₈.wr, rd₇, wr₇]
    have hlen : (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)).length = N s₀ :=
      Proof.Cmac.bytesAt_length _ _ _
    have m₉ : s₉.mem = (writeBytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀))).writeW (Ca s₀ + BitVec.ofNat 64 (N s₀))
        (0x80 : Byte) := by
      have : s₈.gpr Reg8.al.reg = 0x80 := u₈.gpr
      rw [v₉.mem, this, u₈.mem, m₇, b80]
    have fW : Frame [⟨Ca s₀, 16⟩] (savedMem s₀) s₉.mem := by
      rw [m₉]
      refine (fz.trans (writeBytes_frame _ _ _ ?_)).trans
        ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega)))
      rw [hlen]; simpa using Offset.contains_base (Ca s₀) (d := 0) (n := N s₀) (k := 16) (by omega) (by decide)
    have big₉ : Frame (Big s₀) s₀.mem s₉.mem :=
      (savedMem_big s₀).trans (fW.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩)
    refine wp_arg (s₀ := s₀) esp₉ (by rw [rw₉]; exact hp.arg_in (by decide)) (hp.arg_keep big₉ (by decide))
      fun s₁₀ u₁₀ => ?_
    have p₁₀ : s₁₀.gpr .ebp = S s₀ := by
      rw [u₁₀.other _ (by decide), g₉ _ (by decide) (by decide) (by decide) (by decide), p₁]
    have d₁₀ : s₁₀.gpr .edx = W s₀ := u₁₀.gpr
    have rw₁₀ : s₁₀.rd ++ s₁₀.wr = s₀.rd ++ s₀.wr := by rw [u₁₀.rd, u₁₀.wr, rw₉]
    have w₁₀ : s₁₀.wr = s₀.wr := by rw [u₁₀.wr, v₉.wr, u₈.wr, wr₇]
    refine xor4_ok (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [p₁₀]; omega) (by rw [d₁₀]; omega) (by rw [p₁₀]; omega)
      (by
        rw [p₁₀, rw₁₀]
        exact fun a n hi => (hp.cS (d := 2048) (n := 16) (by decide)) a n hi |>
          fun ⟨r, hr, hc⟩ => ⟨r, List.mem_append_right _ hr, hc⟩)
      (by rw [d₁₀, rw₁₀]; exact hp.cKey (by decide)) (by rw [p₁₀, w₁₀]; exact hp.cS (by decide))
      fun s₁₁ g₁₁ => WP.block_nil ?_
    have pad : Spec.Aes.bytesAt s₉.mem (Ca s₀) 16 =
        Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀) ++ [0x80] ++ Spec.Cmac.zeros (16 - N s₀ - 1) := by
      have := Proof.Cmac.padded_bytes (Proof.Cmac.zero4 (savedMem s₀) (Ca s₀)) (Ca s₀)
        (Spec.Aes.bytesAt s₀.mem ((Dp s₀).setWidth 64) (N s₀)) (by rw [hlen]; exact hL)
        (Proof.Cmac.zero4_bytes _ _)
      rw [hlen] at this
      rw [m₉]; exact this
    have k2 : Spec.Aes.bytesAt s₉.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 =
        Spec.Aes.bytesAt s₀.mem ((W s₀).setWidth 64 + BitVec.ofNat 64 256) 16 := by
      rw [Proof.Cmac.bytesAt_frame16 fW (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact (hp.ca_key (by decide)).symm), hp.key_bytes (by decide)]
    refine ⟨by rw [g₁₁.gpr _ (by decide) (by decide), p₁₀],
      by rw [g₁₁.gpr _ (by decide) (by decide), u₁₀.other _ (by decide), esp₉],
      by rw [g₁₁.rd, u₁₀.rd, v₉.rd, u₈.rd, rd₇], by rw [g₁₁.wr, w₁₀], ?_, ?_⟩
    · rw [g₁₁.mem, p₁₀, u₁₀.mem]; exact fW.trans (Proof.Cmac.xor4Mem_frame _ _ _ _)
    · rw [g₁₁.mem, p₁₀, d₁₀, u₁₀.mem, Proof.Cmac.xor4Mem_bytes _ (Proof.Cmac.Sep4.self _)
        (Proof.Cmac.Sep4.of_disjoint (hp.ca_key (by decide))), pad, k2]
      simp only [mn, Spec.Cmac.lastBlock, hlen, show N s₀ ≠ 16 by omega, ite_false]
      exact Proof.Cmac.xor_comm _ _

end VG.Proof.CmacAes.X86
