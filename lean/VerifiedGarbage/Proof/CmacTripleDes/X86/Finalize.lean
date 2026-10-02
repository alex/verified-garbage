import VerifiedGarbage.Proof.CmacTripleDes.X86.Update
import VerifiedGarbage.Proof.Framework.WriteBytes

/-!
# TDEA-CMAC on x86: `vg_cmac_triple_des_finalize`, up to the last block

Untrusted: everything here is checked by Lean. After saving the registers,
the function forms the last block `Mₙ` (SP 800-38B §6.2 step 4) in
`eax:edx`, as little-endian words (`BPost`): `Mₙ* ⊕ K1` for a complete block
(`full_wp`), else `Mₙ*` copied a byte at a time onto zeros at bytes
`[136, 144)` of the scratch buffer, `0x80` after it, and XORed with `K2`
(`partial_wp`).
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.Impl.CmacTripleDes.X86 VG.Proof.CmacTripleDes VG.Proof.Cmac VG.WriteBytes
open VG.Proof.MdStream.X86 (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_subi wp_cmpi wp_bswap
  wp_movzx8 wp_store8)

section
variable (s₀ : State)

abbrev FW : BitVec 32 := arg s₀ 0
abbrev FSt : BitVec 32 := arg s₀ 1
abbrev FP : BitVec 32 := arg s₀ 2
abbrev FL : Nat := (arg s₀ 3).toNat
abbrev FS : BitVec 32 := arg s₀ 4

abbrev keyR : Region := ⟨(FW s₀).setWidth 64, 400⟩
abbrev fstR : Region := ⟨(FSt s₀).setWidth 64, 8⟩
abbrev lastR : Region := ⟨(FP s₀).setWidth 64, FL s₀⟩
abbrev fscrR : Region := ⟨(FS s₀).setWidth 64, 640⟩

end

/-- The precondition, by name. -/
structure FPre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, lastR s₀, argsR s₀]
  wr : s₀.wr = [fstR s₀, fscrR s₀]
  key_st : (keyR s₀).Disjoint (fstR s₀)
  key_scr : (keyR s₀).Disjoint (fscrR s₀)
  last_st : (lastR s₀).Disjoint (fstR s₀)
  last_scr : (lastR s₀).Disjoint (fscrR s₀)
  st_scr : (fstR s₀).Disjoint (fscrR s₀)
  args_st : (argsR s₀).Disjoint (fstR s₀)
  args_scr : (argsR s₀).Disjoint (fscrR s₀)
  ret_st : (retR s₀).Disjoint (fstR s₀)
  ret_scr : (retR s₀).Disjoint (fscrR s₀)
  key_fit : (FW s₀).toNat + 400 ≤ 2 ^ 32
  st_fit : (FSt s₀).toNat + 8 ≤ 2 ^ 32
  last_fit : (FP s₀).toNat + FL s₀ ≤ 2 ^ 32
  scr_fit : (FS s₀).toNat + 640 ≤ 2 ^ 32
  esp_fit : (s₀.gpr .esp).toNat + 24 ≤ 2 ^ 32
  len : FL s₀ ≤ 8

theorem FPre.of {s₀ : State} (h : finalizeX86.pre s₀) : FPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q⟩

/-- The last block `Mₙ` (§6.2 step 4), from the key and the last bytes in `m`. -/
abbrev mn (m : Mem) (W P : Addr) (L : Nat) : List Byte :=
  Spec.Cmac.lastBlock 8 (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 384) 8)
    (Spec.Aes.bytesAt m (W + BitVec.ofNat 64 392) 8) (Spec.Aes.bytesAt m P L)

/-- The bytes where a partial last block is formed. -/
abbrev mnR (s₀ : State) : Region := ⟨(FS s₀).setWidth 64 + BitVec.ofNat 64 136, 8⟩

/-- What the prologue leaves. -/
structure P1 (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = FS s₀
  esi : s.gpr .esi = FW s₀
  esp : s.gpr .esp = s₀.gpr .esp
  mem : s.mem = savedMem s₀ (FS s₀)
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- What the branch on the length leaves: `Mₙ` in `eax:edx`. -/
structure BPost (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = FS s₀
  esi : s.gpr .esi = FW s₀
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [mnR s₀] (savedMem s₀ (FS s₀)) s.mem
  blk : le8 (s.gpr .edx ++ s.gpr .eax) = mn s₀.mem ((FW s₀).setWidth 64) ((FP s₀).setWidth 64) (FL s₀)

section
variable {s₀ : State} (hp : FPre s₀)
include hp

theorem FPre.inScr {d n : Nat} (h : d + n ≤ 640) (hn : 0 < n) :
    InRegions s₀.wr ((FS s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := fscrR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inKey {d n : Nat} (h : d + n ≤ 400) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((FW s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := keyR s₀) (by simp) (Offset.contains_base _ h (by omega))

theorem FPre.inLast {d n : Nat} (h : d + n ≤ FL s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) ((FP s₀).setWidth 64 + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := lastR s₀) (by simp) (Offset.contains_base _ h (by have := hp.len; omega))

theorem FPre.scrEa {s : State} (h : s.gpr .ebp = FS s₀) {d : Nat} (hd : d < 640) :
    s.ea (at_ .ebp d) = (FS s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [ea_at', h]; exact addr_eq (by have := hp.scr_fit; omega)

theorem FPre.keyEa {s : State} (h : s.gpr .esi = FW s₀) {d : Nat} (hd : d < 400) :
    addr (s.gpr .esi) d = (FW s₀).setWidth 64 + BitVec.ofNat 64 d := by
  rw [h]; exact addr_eq (by have := hp.key_fit; omega)

theorem FPre.argAddr_eq {i : Nat} (hi : i < 5) : argAddr s₀ i = argAddr s₀ 0 + BitVec.ofNat 64 (4 * i) := by
  have := hp.esp_fit
  show addr (s₀.gpr .esp) (4 + 4 * i) = addr (s₀.gpr .esp) (4 + 4 * 0) + _
  rw [addr_eq (by omega), addr_eq (by omega), Offset.add_add, show 4 + 4 * 0 + 4 * i = 4 + 4 * i by omega]

theorem FPre.argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd, hp.argAddr_eq hi]
  exact in_rw (r := argsR s₀) (by simp) (Offset.contains_base _ (by omega) (by omega))

/-- The arguments, unchanged outside the state and the scratch buffer. -/
theorem FPre.arg_eq {rs : List Region} {m : Mem} (hf : Frame rs (savedMem s₀ (FS s₀)) m)
    (hd : ∀ r ∈ rs, Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀)) {i : Nat} (hi : i < 5) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have hsub : Region.Sub ⟨argAddr s₀ i, 4⟩ (argsR s₀) := by
    rw [hp.argAddr_eq hi]; exact Offset.sub_base _ (by omega)
  rw [hf.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)]
  · exact (savedMem_frame s₀ (FS s₀)).readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (hp.args_scr.sub_left hsub).sub_right (Offset.sub_base _ (by decide))) (by decide)
  · rcases hd r hr with h | h
    · exact (hp.args_st.sub_left hsub).sub_right h
    · exact (hp.args_scr.sub_left hsub).sub_right h

/-- Saving the registers leaves the key unchanged. -/
theorem FPre.keyBytes {d : Nat} (h : d + 8 ≤ 400) :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) ((FW s₀).setWidth 64 + BitVec.ofNat 64 d) 8 =
      Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 d) 8 :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.key_scr.sub_left (Offset.sub_base _ h)).sub_right (Offset.sub_base _ (by decide))) (by decide)

theorem FPre.lastBytes :
    Spec.Aes.bytesAt (savedMem s₀ (FS s₀)) ((FP s₀).setWidth 64) (FL s₀) =
      Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀) :=
  bytesAt_frame (savedMem_frame s₀ (FS s₀)) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.last_scr.sub_right (Offset.sub_base _ (by decide))) (by have := hp.len; omega)

end

/-! ## The prologue -/

theorem fpre1_wp {s₀ : State} (hp : FPre s₀) :
    WP isa (.block (([.mov .eax (stk 20)] : List Instr) ++ save ++
      ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr)))
      s₀ fun s => P1 s₀ s ∧ s.zf = some (decide (FL s₀ = 8)) := by
  have hsc := hp.scr_fit
  have hL := hp.len
  rw [show ([.mov .eax (stk 20)] : List Instr) ++ save ++
    ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr) =
    .mov .eax (stk 20) :: (Spill.saveCode .eax saved ++
      ([.mov .ebp (.reg .eax), .mov .esi (stk 4), .mov .eax (stk 16), .alu .cmp .eax (.imm 8)] : List Instr)) from rfl]
  simp only [stk]
  refine wp_arg (s₀ := s₀) 4 rfl rfl (hp.argIn rfl rfl (by decide)) rfl fun s₁ u₁ => ?_
  refine Spill.save_ofNat_ok saved saved_fits (by rw [u₁.gpr]; exact fits_of hp.scr_fit (by decide))
    (fun p hp' => ?_) fun s₂ u₂ => ?_
  · have hb := saved_bound p hp'
    have hsc' : (arg s₀ 4).toNat + 640 ≤ 2 ^ 32 := hp.scr_fit
    rw [u₁.gpr, u₁.wr]
    exact hp.inScr (by omega) (by decide)
  have hm₂ : s₂.mem = savedMem s₀ (FS s₀) := by
    rw [u₂.mem, u₁.mem, u₁.gpr, savedMem]
    exact Spill.saveMem_congr _ _ (fun _ _ => rfl) fun p hp' => u₁.other _ (saved_ne_eax p hp')
  have nf : ∀ r ∈ ([] : List Region), Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun _ h => by cases h
  refine wp_mov fun s₃ u₃ => ?_
  have rd₃ : s₃.rd = s₀.rd := by rw [u₃.rd, u₂.rd, u₁.rd]
  have wr₃ : s₃.wr = s₀.wr := by rw [u₃.wr, u₂.wr, u₁.wr]
  have esp₃ : s₃.gpr .esp = s₀.gpr .esp := by rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide)]
  refine wp_arg (s₀ := s₀) 0 rfl esp₃ (hp.argIn rd₃ wr₃ (by decide))
    (by rw [u₃.mem, hm₂]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₄ u₄ => ?_
  refine wp_arg (s₀ := s₀) 3 rfl (by rw [u₄.other _ (by decide), esp₃])
    (hp.argIn (by rw [u₄.rd, rd₃]) (by rw [u₄.wr, wr₃]) (by decide))
    (by rw [u₄.mem, u₃.mem, hm₂]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₅ u₅ =>
    wp_cmpi fun s₆ f₆ _ z₆ => WP.block_nil ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.gpr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.gpr]
  · rw [f₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), esp₃]
  · rw [f₆.mem, u₅.mem, u₄.mem, u₃.mem, hm₂]
  · rw [f₆.rd, u₅.rd, u₄.rd, rd₃]
  · rw [f₆.wr, u₅.wr, u₄.wr, wr₃]
  · rw [z₆, u₅.gpr, show arg s₀ 3 = BitVec.ofNat 32 (FL s₀) by simp [FL],
      show (8 : BitVec 32) = BitVec.ofNat 32 8 from rfl, MdStream.X86.sub_beq (by omega) (by decide)]

/-! ## A complete last block -/

theorem full_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ = 8) {s : State} (h : P1 s₀ s) :
    WP isa (.block full) s (BPost s₀) := by
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  have nf : ∀ r ∈ ([] : List Region), Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun _ h => by cases h
  have lf8 : (arg s₀ 2).toNat + 8 ≤ 2 ^ 32 := by have := hp.last_fit; rw [hL] at this; exact this
  simp only [full, stk]
  refine wp_arg (s₀ := s₀) 2 rfl h.esp (hp.argIn h.rd h.wr (by decide))
    (by rw [h.mem]; exact hp.arg_eq (Frame.refl _ _) nf (by decide)) fun s₁ u₁ => ?_
  refine wp_movm (a := (FP s₀).setWidth 64) (by rw [ea_at', u₁.gpr, addr_zero])
    (by rw [u₁.rd, u₁.wr, hrw]; simpa [add0] using hp.inLast (d := 0) (n := 4) (by omega) (by decide))
    fun s₂ u₂ => ?_
  refine wp_movm (a := (FP s₀).setWidth 64 + BitVec.ofNat 64 4)
    (by rw [ea_at', u₂.other _ (by decide), u₁.gpr]; exact addr_eq (by omega))
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact hp.inLast (d := 4) (n := 4) (by omega) (by decide))
    fun s₃ u₃ => ?_
  have esi₃ : s₃.gpr .esi = FW s₀ := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h.esi]
  have k384 := hp.inKey (d := 384) (n := 4) (by decide) (by decide)
  have k388 := hp.inKey (d := 388) (n := 4) (by decide) (by decide)
  refine wp_xorma (hp.keyEa (d := 384) esi₃ (by decide))
    (by rw [u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact k384) fun s₄ u₄ => ?_
  refine wp_xorma (hp.keyEa (d := 388) (by rw [u₄.other _ (by decide), esi₃]) (by decide))
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr, hrw]; exact k388)
    fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ∉ [Reg.eax, .ecx, .edx] → s₅.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [u₅.other _ hr.2.2, u₄.other _ hr.1, u₃.other _ hr.2.2, u₂.other _ hr.1, u₁.other _ hr.2.1]
  have mem : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨by rw [g _ (by decide), h.ebp], by rw [g _ (by decide), h.esi], by rw [g _ (by decide), h.esp],
    by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd, h.rd], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr, h.wr],
    by rw [mem, h.mem]; exact Frame.refl _ _, ?_⟩
  rw [u₅.gpr, u₅.other .eax (by decide), u₄.gpr, u₄.other .edx (by decide), u₃.gpr, u₃.other .eax (by decide),
    u₂.gpr, u₄.mem, u₃.mem, u₂.mem, u₁.mem, ← BitVec.xor_append, ← readW64_split,
    show (FW s₀).setWidth 64 + BitVec.ofNat 64 388 =
      (FW s₀).setWidth 64 + BitVec.ofNat 64 384 + BitVec.ofNat 64 4 from (Offset.add_add _ 384 4).symm,
    ← readW64_split, h.mem, le8_xor, le8_readW, le8_readW, hp.keyBytes (by decide)]
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

theorem copy_wp {s : State} {p c : BitVec 32} {L : Nat} (hL₀ : 0 < L) (hL : L ≤ 8)
    (hcx : s.gpr .ecx = p) (hdi : s.gpr .edi = c) (hdx : s.gpr .edx = BitVec.ofNat 32 L)
    (fp : p.toNat + L ≤ 2 ^ 32) (fc : c.toNat + 8 ≤ 2 ^ 32)
    (hr : ∀ i < L, InRegions (s.rd ++ s.wr) (p.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hw : ∀ i < 8, InRegions s.wr (c.setWidth 64 + BitVec.ofNat 64 i) 1)
    (hd : (⟨p.setWidth 64, L⟩ : Region).Disjoint ⟨c.setWidth 64, 8⟩) :
    WP isa copy s fun s' =>
      s'.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) L) ∧
      s'.gpr .edi = c + BitVec.ofNat 32 L ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.loop (M := isa) (body := .block [.movzx8 .eax (at_ .ecx 0), .store8 (at_ .edi 0) .al,
      .alu .add .ecx (.imm 1), .alu .add .edi (.imm 1), .alu .sub .edx (.imm 1)]) (c := .ne)
    (fun (n : Nat) (t : State) => ∃ i, n = L - i ∧ i < L ∧ t.gpr .ecx = p + BitVec.ofNat 32 i ∧
      t.gpr .edi = c + BitVec.ofNat 32 i ∧ t.gpr .edx = BitVec.ofNat 32 (L - i) ∧
      t.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i) ∧
      (∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → t.gpr r = s.gpr r) ∧
      t.rd = s.rd ∧ t.wr = s.wr) ?_ (L - 0) _
    ⟨0, rfl, hL₀, by rw [hcx]; exact (BitVec.add_zero p).symm, by rw [hdi]; exact (BitVec.add_zero c).symm,
      by rw [hdx, Nat.sub_zero], by simp [Spec.Aes.bytesAt, writeBytes_nil], fun _ _ _ _ _ => rfl, rfl, rfl⟩
  rintro n t ⟨i, rfl, hi, xc, xd, xn, mem, g, rd, wr⟩
  refine wp_movzx8 (a := p.setWidth 64 + BitVec.ofNat 64 i) (by rw [ea_at', xc, addr_off2 (by omega), add0])
    (by rw [rd, wr]; exact hr i hi) fun t₁ u₁ => ?_
  refine wp_store8 (a := c.setWidth 64 + BitVec.ofNat 64 i)
    (by rw [ea_at', u₁.other _ (by decide), xd, addr_off2 (by omega), add0]) (by rw [u₁.wr, wr]; exact hw i (by omega))
    fun t₂ v₂ => ?_
  refine wp_addi fun t₃ u₃ => wp_addi fun t₄ u₄ => wp_subi fun t₅ u₅ z₅ => WP.block_nil ?_
  have hlen : (Spec.Aes.bytesAt s.mem (p.setWidth 64) i).length = i := Proof.Cmac.bytesAt_length _ _ _
  have hx : writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) i)
      (p.setWidth 64 + BitVec.ofNat 64 i) = s.mem (p.setWidth 64 + BitVec.ofNat 64 i) :=
    (writeBytes_frame s.mem (c.setWidth 64) _ (R := ⟨c.setWidth 64, i⟩) (by rw [hlen]; exact Region.contains_self _ _)) _
      fun r hr hcon => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hd _ (Offset.contains_base _ (by omega) (by omega)) (Region.sub_prefix (by omega) _ hcon)
  have hmem : t₅.mem = writeBytes s.mem (c.setWidth 64) (Spec.Aes.bytesAt s.mem (p.setWidth 64) (i + 1)) := by
    rw [u₅.mem, u₄.mem, u₃.mem, v₂.mem, show Reg8.al.reg = .eax from rfl, u₁.gpr, u₁.mem, mem, byte_rt32, hx,
      Proof.Cmac.bytesAt_succ, writeBytes_snoc s.mem _ _ _ (by rw [hlen]; omega), hlen]
  have xn' : t₅.gpr .edx = BitVec.ofNat 32 (L - (i + 1)) := by
    rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xn,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega)]; rfl
  have ev : isa.eval .ne t₅ = some !decide (L - (i + 1) = 0) := by
    rw [eval_ne', z₅, u₄.other _ (by decide), u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xn,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, MdStream.X86.sub_ofNat (by omega), Nat.sub_sub,
      Wp.ofNat_beq_zero (by omega)]
    rfl
  have gg : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edi → r ≠ .edx → t₅.gpr r = s.gpr r := fun r ha hc hdi hdx => by
    rw [u₅.other _ hdx, u₄.other _ hdi, u₃.other _ hc, v₂.gpr, u₁.other _ ha, g r ha hc hdi hdx]
  have xd' : t₅.gpr .edi = c + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), v₂.gpr, u₁.other _ (by decide), xd,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have xc' : t₅.gpr .ecx = p + BitVec.ofNat 32 (i + 1) := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, v₂.gpr, u₁.other _ (by decide), xc,
      show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, Offset.add_add]
  have rd' : t₅.rd = s.rd := by rw [u₅.rd, u₄.rd, u₃.rd, v₂.rd, u₁.rd, rd]
  have wr' : t₅.wr = s.wr := by rw [u₅.wr, u₄.wr, u₃.wr, v₂.wr, u₁.wr, wr]
  by_cases he : i + 1 = L
  · left
    exact ⟨by rw [ev]; simp [he], by rw [hmem, he], by rw [xd', he], gg, rd', wr'⟩
  · right
    exact ⟨by rw [ev]; simp; omega, L - (i + 1), by omega, i + 1, rfl, by omega, xc', xd', xn', hmem, gg, rd', wr'⟩

/-! ## A partial last block -/

theorem wr_in {s : State} {a : Addr} {n : Nat} (h : InRegions s.wr a n) : InRegions (s.rd ++ s.wr) a n := by
  obtain ⟨r, hr, hc⟩ := h; exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem b80 : ((0x80 : BitVec 32).setWidth 8 : Byte) = 0x80 := by decide

theorem partial_wp {s₀ : State} (hp : FPre s₀) (hL : FL s₀ < 8) {s : State} (h : P1 s₀ s) :
    WP isa partialBlock s (BPost s₀) := by
  have sf := hp.scr_fit
  have kf := hp.key_fit
  have lf := hp.last_fit
  have hN : FL s₀ < 2 ^ 32 := (arg s₀ 3).isLt
  have hrw : s.rd ++ s.wr = s₀.rd ++ s₀.wr := by rw [h.rd, h.wr]
  let C : Addr := (FS s₀).setWidth 64 + BitVec.ofNat 64 136
  have cIn : ∀ i < 8, InRegions s₀.wr (C + BitVec.ofNat 64 i) 1 := fun i hi => by
    rw [Offset.add_add]; exact hp.inScr (by omega) (by decide)
  have cR : ∀ d n, d + n ≤ 8 → (mnR s₀).Contains (C + BitVec.ofNat 64 d) n := fun d n h =>
    Offset.contains_base _ h (by omega)
  have mnS : ∀ r ∈ [mnR s₀], Region.Sub r (fstR s₀) ∨ Region.Sub r (fscrR s₀) := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact Or.inr (Offset.sub_base _ (by decide))
  -- Zero the bytes.
  refine WP.seq ?_
  simp only [zero, stk]
  refine wp_movi fun s₁ u₁ => ?_
  refine wp_store (hp.scrEa (by rw [u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₂ w₂ => ?_
  refine wp_store (hp.scrEa (by rw [w₂.gpr, u₁.other _ (by decide), h.ebp]) (by decide))
    (by rw [w₂.wr, u₁.wr, h.wr]; exact hp.inScr (by decide) (by decide)) fun s₃ w₃ => ?_
  let m₁ := ((savedMem s₀ (FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
  have mem₃ : s₃.mem = m₁ := by
    rw [w₃.mem, w₂.mem, w₂.gpr, u₁.gpr, u₁.mem, h.mem]
    show _ = ((savedMem s₀ (FS s₀)).writeW C (0 : BitVec 32)).writeW (C + BitVec.ofNat 64 4) (0 : BitVec 32)
    rw [Offset.add_add]
  have fm₁ : Frame [mnR s₀] (savedMem s₀ (FS s₀)) m₁ :=
    ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (by simpa [add0] using cR 0 4 (by decide))).writeW
      (List.mem_singleton_self _) _ (cR 4 4 (by decide))
  refine wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => ?_
  have rd₅ : s₅.rd = s₀.rd := by rw [u₅.rd, u₄.rd, w₃.rd, w₂.rd, u₁.rd, h.rd]
  have wr₅ : s₅.wr = s₀.wr := by rw [u₅.wr, u₄.wr, w₃.wr, w₂.wr, u₁.wr, h.wr]
  have esp₅ : s₅.gpr .esp = s₀.gpr .esp := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), w₃.gpr, w₂.gpr, u₁.other _ (by decide), h.esp]
  have mem₅ : s₅.mem = m₁ := by rw [u₅.mem, u₄.mem, mem₃]
  refine wp_arg (s₀ := s₀) 2 rfl esp₅ (hp.argIn rd₅ wr₅ (by decide))
    (by rw [mem₅]; exact hp.arg_eq fm₁ mnS (by decide)) fun s₆ u₆ => ?_
  refine wp_arg (s₀ := s₀) 3 rfl (by rw [u₆.other _ (by decide), esp₅])
    (hp.argIn (by rw [u₆.rd, rd₅]) (by rw [u₆.wr, wr₅]) (by decide))
    (by rw [u₆.mem, mem₅]; exact hp.arg_eq fm₁ mnS (by decide)) fun s₇ u₇ =>
    wp_cmpi fun s₈ f₈ _ z₈ => WP.block_nil ?_
  have mem₈ : s₈.mem = m₁ := by rw [f₈.mem, u₇.mem, u₆.mem, mem₅]
  have g₈ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → s₈.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [f₈.gpr, u₇.other _ hr.2.2.1, u₆.other _ hr.2.1, u₅.other _ hr.2.2.2, u₄.other _ hr.2.2.2, w₃.gpr, w₂.gpr,
      u₁.other _ hr.1]
  have di₈ : s₈.gpr .edi = FS s₀ + BitVec.ofNat 32 136 := by
    rw [f₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, w₃.gpr, w₂.gpr,
      u₁.other _ (by decide), h.ebp]; rfl
  have cx₈ : s₈.gpr .ecx = FP s₀ := by rw [f₈.gpr, u₇.other _ (by decide), u₆.gpr]
  have dx₈ : s₈.gpr .edx = BitVec.ofNat 32 (FL s₀) := by rw [f₈.gpr, u₇.gpr]; simp [FL]
  have z8 : s₈.zf = some (decide (FL s₀ = 0)) := by
    rw [z₈, u₇.gpr, show ∀ x : BitVec 32, x - 0 = x from fun x => by simp,
      show arg s₀ 3 = BitVec.ofNat 32 (FL s₀) by simp [FL], Wp.ofNat_beq_zero hN]
  have rd₈ : s₈.rd = s₀.rd := by rw [f₈.rd, u₇.rd, u₆.rd, rd₅]
  have wr₈ : s₈.wr = s₀.wr := by rw [f₈.wr, u₇.wr, u₆.wr, wr₅]
  have hcA : (FS s₀ + BitVec.ofNat 32 136).setWidth 64 = C := by
    rw [← addr_zero, addr_off2 (by omega), add0]
  have dPC : (lastR s₀).Disjoint ⟨C, 8⟩ := hp.last_scr.sub_right (Offset.sub_base _ (by decide))
  have lastM₁ : Spec.Aes.bytesAt m₁ ((FP s₀).setWidth 64) (FL s₀) =
      Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀) := by
    rw [← hp.lastBytes]
    exact bytesAt_frame fm₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact dPC) (by omega)
  -- Copy the last bytes.
  refine WP.seq (WP.mono (Q := fun (t : State) =>
      t.mem = writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀)) ∧
      t.gpr .edi = FS s₀ + BitVec.ofNat 32 136 + BitVec.ofNat 32 (FL s₀) ∧
      (∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → t.gpr r = s.gpr r) ∧ t.rd = s₀.rd ∧ t.wr = s₀.wr) ?_ fun t ht => ?_)
  · by_cases hL0 : FL s₀ = 0
    · refine WP.ite true (by rw [eval_e', z8, hL0]; rfl) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      refine ⟨by rw [mem₈, hL0]; simp [Spec.Aes.bytesAt, writeBytes_nil],
        by rw [di₈, hL0]; exact (BitVec.add_zero _).symm, g₈, rd₈, wr₈⟩
    · refine WP.ite false (by rw [eval_e', z8]; simp [hL0]) (fun h => by cases h) fun _ => ?_
      refine WP.mono (copy_wp (p := FP s₀) (c := FS s₀ + BitVec.ofNat 32 136) (by omega) (by omega) cx₈ di₈ dx₈
        (by omega) (by rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega)
        (fun i hi => by rw [rd₈, wr₈]; exact hp.inLast (by omega) (by decide))
        (fun i hi => by rw [wr₈, hcA]; exact cIn i hi) (by rw [hcA]; exact dPC)) ?_
      rintro t ⟨m₂, di₂, g₂, rd₂, wr₂⟩
      refine ⟨by rw [m₂, mem₈, hcA, lastM₁], di₂, fun r hr => by
        rw [g₂ r (fun h => hr (by simp [h])) (fun h => hr (by simp [h])) (fun h => hr (by simp [h]))
          (fun h => hr (by simp [h])), g₈ r hr], by rw [rd₂, rd₈], by rw [wr₂, wr₈]⟩
  obtain ⟨m₂, di₂, g₂, rd₂, wr₂⟩ := ht
  have hlen : (Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀)).length = FL s₀ :=
    Proof.Cmac.bytesAt_length _ _ _
  have cL : t.ea (at_ .edi 0) = C + BitVec.ofNat 64 (FL s₀) := by
    rw [ea_at', di₂, Offset.add_add, addr_off2 (by omega), add0, Offset.add_add]
  have trw : t.rd ++ t.wr = s₀.rd ++ s₀.wr := by rw [rd₂, wr₂]
  have ebpt : t.gpr .ebp = FS s₀ := by rw [g₂ _ (by decide), h.ebp]
  have esit : t.gpr .esi = FW s₀ := by rw [g₂ _ (by decide), h.esi]
  simp only [padK2]
  refine wp_movi fun t₁ v₁ => ?_
  refine wp_store8 (by rw [show t₁.ea (at_ .edi 0) = t.ea (at_ .edi 0) by rw [ea_at', ea_at', v₁.other _ (by decide)],
      cL]) (by rw [v₁.wr, wr₂]; exact cIn _ hL) fun t₂ v₂ => ?_
  refine wp_movm (hp.scrEa (by rw [v₂.gpr, v₁.other _ (by decide), ebpt]) (by decide))
    (by rw [v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact wr_in (hp.inScr (by decide) (by decide))) fun t₃ v₃ => ?_
  refine wp_movm (hp.scrEa (by rw [v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), ebpt]) (by decide))
    (by rw [v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact wr_in (hp.inScr (by decide) (by decide)))
    fun t₄ v₄ => ?_
  have k392 := hp.inKey (d := 392) (n := 4) (by decide) (by decide)
  have k396 := hp.inKey (d := 396) (n := 4) (by decide) (by decide)
  refine wp_xorma (hp.keyEa (d := 392) (by rw [v₄.other _ (by decide), v₃.other _ (by decide), v₂.gpr,
      v₁.other _ (by decide), esit]) (by decide))
    (by rw [v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact k392) fun t₅ v₅ => ?_
  refine wp_xorma (hp.keyEa (d := 396) (by rw [v₅.other _ (by decide), v₄.other _ (by decide),
      v₃.other _ (by decide), v₂.gpr, v₁.other _ (by decide), esit]) (by decide))
    (by rw [v₅.rd, v₅.wr, v₄.rd, v₄.wr, v₃.rd, v₃.wr, v₂.rd, v₂.wr, v₁.rd, v₁.wr, trw]; exact k396)
    fun t₆ v₆ => WP.block_nil ?_
  let m₃ := (writeBytes m₁ C (Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀))).writeW
    (C + BitVec.ofNat 64 (FL s₀)) (0x80 : Byte)
  have mem₂ : t₂.mem = m₃ := by rw [v₂.mem, v₁.mem, m₂, show Reg8.al.reg = .eax from rfl, v₁.gpr, b80]
  have g₆ : ∀ r, r ∉ [Reg.eax, .ecx, .edx, .edi] → t₆.gpr r = s.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [v₆.other _ hr.2.2.1, v₅.other _ hr.1, v₄.other _ hr.2.2.1, v₃.other _ hr.1, v₂.gpr, v₁.other _ hr.1,
      g₂ r (by simp [hr.1, hr.2.1, hr.2.2.1, hr.2.2.2])]
  -- The frame.
  have fr : Frame [mnR s₀] (savedMem s₀ (FS s₀)) m₃ := by
    refine (fm₁.trans (writeBytes_frame _ _ _ ?_)).writeW (List.mem_singleton_self _) _ (cR _ 1 (by omega))
    rw [hlen]; simpa [add0] using cR 0 (FL s₀) (by omega)
  -- The block.
  have kD : (⟨(FW s₀).setWidth 64 + BitVec.ofNat 64 392, 8⟩ : Region).Disjoint (mnR s₀) :=
    (hp.key_scr.sub_left (Offset.sub_base _ (by decide))).sub_right (Offset.sub_base _ (by decide))
  have k2 : Spec.Aes.bytesAt m₃ ((FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 =
      Spec.Aes.bytesAt s₀.mem ((FW s₀).setWidth 64 + BitVec.ofNat 64 392) 8 := by
    rw [bytesAt_frame fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact kD) (by decide),
      hp.keyBytes (by decide)]
  have pad : Spec.Aes.bytesAt m₃ C 8 =
      Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀) ++ [0x80] ++ Spec.Cmac.zeros (8 - FL s₀ - 1) := by
    have hz : Spec.Aes.bytesAt m₁ C 8 = Spec.Cmac.zeros 8 := by
      rw [← le8_readW, readW64_split, Mem.readW_writeW_self32, readW_lo_of_hi]; decide
    have := padded_bytes8 m₁ C (Spec.Aes.bytesAt s₀.mem ((FP s₀).setWidth 64) (FL s₀)) (by rw [hlen]; exact hL) hz
    rw [hlen] at this
    exact this
  refine ⟨by rw [g₆ _ (by decide), h.ebp], by rw [g₆ _ (by decide), h.esi], by rw [g₆ _ (by decide), h.esp],
    by rw [v₆.rd, v₅.rd, v₄.rd, v₃.rd, v₂.rd, v₁.rd, rd₂],
    by rw [v₆.wr, v₅.wr, v₄.wr, v₃.wr, v₂.wr, v₁.wr, wr₂],
    by rw [v₆.mem, v₅.mem, v₄.mem, v₃.mem, mem₂]; exact fr, ?_⟩
  rw [v₆.gpr, v₆.other .eax (by decide), v₅.gpr, v₅.other .edx (by decide), v₄.gpr, v₄.other .eax (by decide),
    v₃.gpr, v₅.mem, v₄.mem, v₃.mem, mem₂, ← BitVec.xor_append,
    show (FS s₀).setWidth 64 + BitVec.ofNat 64 140 = C + BitVec.ofNat 64 4 from (Offset.add_add _ 136 4).symm,
    ← readW64_split,
    show (FW s₀).setWidth 64 + BitVec.ofNat 64 396 =
      (FW s₀).setWidth 64 + BitVec.ofNat 64 392 + BitVec.ofNat 64 4 from (Offset.add_add _ 392 4).symm,
    ← readW64_split, le8_xor, le8_readW, le8_readW, pad, k2]
  simp only [mn, Spec.Cmac.lastBlock, hlen, show FL s₀ ≠ 8 by omega, ite_false]
  exact Proof.Cmac.xor_comm _ _

theorem finPre_wp {s₀ : State} (hp : FPre s₀) : WP isa finPre s₀ (BPost s₀) := by
  refine WP.seq (WP.mono (fpre1_wp hp) fun s₁ ⟨h₁, z₁⟩ => ?_)
  by_cases hL : FL s₀ = 8
  · exact WP.ite true (by rw [eval_e', z₁]; simp [hL]) (fun _ => full_wp hp hL h₁) (fun h => by cases h)
  · exact WP.ite false (by rw [eval_e', z₁]; simp [hL]) (fun h => by cases h)
      (fun _ => partial_wp hp (by have := hp.len; omega) h₁)

end VG.Proof.CmacTripleDes.X86
