import VerifiedGarbage.Proof.Hmac.Generic.X86.Save

/-!
# HMAC over any streaming hash function on x86 (32-bit): `init`, correct

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/Init.lean`). The arguments are on the stack:
`scratch`, then `key` and `key_len` are loaded first (after our caller's
registers are saved in `scratch`), and `inner` and `outer` once the keys are
written. The functions we call keep `ebx`, `esi`, `edi` and `ebp`, which
hold `inner`, `outer`, the low word of `update`'s count and `scratch`.
-/

namespace VG.Proof.Hmac.Generic.X86.Init

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Hmac.Generic.X86
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd Fupd wp_mov wp_movi wp_movm wp_add wp_addi wp_test sub_offset)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length
  off_disj off_disj0 sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev out : BitVec 32 := arg s₀ 1
abbrev kp : BitVec 32 := arg s₀ 2
abbrev kl : Nat := (arg s₀ 3).toNat
abbrev scr : BitVec 32 := arg s₀ 4
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.S⟩
abbrev outR : Region := ⟨(out s₀).setWidth 64, H.S⟩
abbrev keyR : Region := ⟨(kp s₀).setWidth 64, kl s₀⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 20⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- The padded keys. -/
abbrev P : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨(scr s₀).setWidth 64, hH.Wb⟩
/-- Byte `o` of `scratch`, as a register holds it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

end

theorem kl_lt (s₀ : State) : kl s₀ < 2 ^ 32 := (arg s₀ 3).isLt

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_o : (retR s₀).Disjoint (outR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hB0 : 0 < H.B
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20,
    h21, h22, h23, h24⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, hB, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22,
    h23, h24, hfit, hH.hBB, hH.hB0, hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨(scr s₀).setWidth 64 + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; simp only [Hash.buf] at this; exact sub_sc hp (by omega)

theorem buf_sub : Region.Sub (bufR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw
  exact sub_offset hp.fits (by omega)

omit hp in
theorem padI_sub : Region.Sub ⟨P (H := H) s₀, H.B⟩ (bufR (H := H) s₀) := Region.sub_prefix (by omega)

theorem padO_sub : Region.Sub ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (bufR (H := H) s₀) :=
  sub_offset (by omega) (by have := hp.hB; omega)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 16) (by omega) (by omega)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hB
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 16) (n := 2 * H.B) (by omega) (by omega)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.hW; have := hp.hB
  exact off_disj _ (a := 8 * H.W) (m := 16) (b := 8 * H.W + 16) (n := 2 * H.B) (by omega) (by omega)
    (by omega)

theorem addr_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) :
    (dO s₀ o).setWidth 64 = (scr s₀).setWidth 64 + BitVec.ofNat 64 o :=
  setWidth_add (by have := hp.nw; omega)

theorem toNat_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) : (dO s₀ o).toNat = (scr s₀).toNat + o :=
  toNat_add_ofNat (by have := hp.nw; omega)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide

section
variable {sc : Nat}

/-- `KR` survives changes to other registers, and to memory in our buffers
(away from the save area) and the stack. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

/-- The arguments, while `KR` holds. -/
theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) : VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 20) (by have := hp.spf; omega) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_o
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega)

/-- The return address, while `KR` holds. -/
theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_o
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

/-- `KR` after a call that writes `rs`, parts of our buffers. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [show stk s = stkR s₀ by rw [stk, hk.esp]] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hsub r hr
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

omit hp in
theorem argW {s : State} (hs : s.gpr .esp = E s₀) (i : Nat) :
    s.ea (at_ .esp (4 + 4 * i)) = argAddr s₀ i := by
  rw [ea_at, hs]; rfl

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

/-- An argument, read from memory while `KR` holds. -/
theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

end

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem ((kp s₀).setWidth 64) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) sc s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) sc s₀) := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  have hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  have dA : ∀ r ∈ [saveR H (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  refine WP.seq ?_
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 4) (argW rfl 4) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 5, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega) (by have := hp.spf; omega))) (by decide)
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl (by decide))
    fun s₅ u₅ => ?_
  refine wp_movi fun s₆ u₆ => wp_test fun s₇ f₇ z₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = s₂.mem := by rw [f₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hrd : s₇.rd = s₀.rd := by rw [f₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have hwr : s₇.wr = s₀.wr := by rw [f₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have hbp : s₇.gpr .ebp = scr s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl
  have hsi : s₇.gpr .esi = kp s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 2 (by decide)]
  have hdi : s₇.gpr .edi = BitVec.ofNat 32 (kl s₀) := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 3 (by decide), BitVec.ofNat_toNat,
      BitVec.setWidth_eq]
  have hbx : s₇.gpr .ebx = BitVec.ofNat 32 0 := by rw [f₇.gpr, u₆.gpr]; rfl
  have hsp : s₇.gpr .esp = E s₀ := by
    rw [f₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)]
  have hz : s₇.zf = some (decide (kl s₀ = 0)) := by
    rw [z₇, u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 3 (by decide), test_z]
  have hr : LoopRegs (scr s₀) (kp s₀) (kl s₀) s₇ := ⟨hbp, hsi, hdi⟩
  have hm : LoopMem H (scr s₀) (kp s₀) (kl s₀) s₇ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (Nat.lt_trans (kl_lt s₀) (by decide))
          hk |>.elim fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by
        rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega, hp.nk⟩
  refine WP.seq (WP.mono (key_ok H hr hm hbx hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₇.mem := by rw [hm₇]; exact f₂'
  have eK : K0 s₇.mem ((kp s₀).setWidth 64) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp)))
      (Nat.le_of_lt (Nat.lt_trans (kl_lt s₀) (by decide))) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₇.gpr r := ht.other
  have sv : SavedRegs H (scr s₀) s₀ s₇.mem := hm₇ ▸ sv₂.of_eq H fun r hr => u₁.other r (by
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> decide)
  have ft : Frame [bufR (H := H) s₀] s₇.mem t.mem := ht.mem.frame
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [hg _ (by decide), hsp], by rw [hg _ (by decide), hbp],
    sv.frame H ft (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp),
    (fk.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩).trans
      (ft.sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, buf_sub hp⟩)⟩, ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

/-- `KR`, with `inner` in `ebx` and `outer` in `esi`. -/
structure KS (s₀ s : State) : Prop extends KR (H := H) sc s₀ s where
  ebx : s.gpr .ebx = inn s₀
  esi : s.gpr .esi = out s₀

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem states_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block Hash.initStates) s fun t => KS (H := H) sc s₀ t ∧ t.mem = s.mem := by
  refine wp_movm (a := argAddr s₀ 0) (argW hk.esp 0) (argIn hp hk.rd hk.wr (by decide)) fun t₁ u₁ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by rw [ea_at, u₁.other _ (by decide), hk.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact argIn hp hk.rd hk.wr (by decide)) fun t₂ u₂ => WP.block_nil ?_
  exact ⟨⟨(hk.upd (by decide) u₁).upd (by decide) u₂, by rw [u₂.other _ (by decide), u₁.gpr, hk.readArg hp (by decide)],
    by rw [u₂.gpr, u₁.mem, hk.readArg hp (by decide)]⟩, by rw [u₂.mem, u₁.mem]⟩

theorem state_disj {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p.setWidth 64, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p.setWidth 64, H.S⟩ ∧
      (saveR H (scr s₀)).Disjoint ⟨p.setWidth 64, H.S⟩ ∧ p.toNat + H.S ≤ 2 ^ 32 := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.i_s.symm.sub_left (save_sub hp), hp.ni⟩
  · exact ⟨hp.o_s, hp.b_o, hp.o_s.symm.sub_left (save_sub hp), hp.no⟩

theorem state_in {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p.setWidth 64, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem state_wrs {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub ⟨p.setWidth 64, H.S⟩ r' := by
  rcases hpR with rfl | rfl
  · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
  · exact ⟨outR (H := H) s₀, by simp, fun _ h => h⟩

omit hp in
theorem stk_eq {s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

/-- `KS` after a call that writes `rs`. -/
theorem KS.call {s s' : State} (hk : KS (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') :
    KS (H := H) sc s₀ s' :=
  ⟨hk.toKR.call hp ha hs hsub, by rw [ha.cs .ebx (by simp [calleeSaved]), hk.ebx],
    by rw [ha.cs .esi (by simp [calleeSaved]), hk.esi]⟩

theorem callInit_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, stkR s₀] s.mem s'.mem →
      hH.SH.Repr s'.mem (p.setWidth 64) [] → Q s') :
    WP isa (H.callInit st) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  have hsp := hk.esp
  refine init_frame hH (st := p)
    { hst := by rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [hk.ebx, hk.esi]
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      sp48 := by rw [hsp]; exact hp.sp48
      cw := by rw [hk.wr]; exact covers_one (state_in hp hpR)
      b_st := by rw [stk_eq hk.toKR]; exact dK
      nst := np } fun s' ha hr => ?_
  have f := ha.frame
  rw [stk_eq hk.toKR] at f
  exact hQ s' (hk.call hp ha (by simp only [List.mem_singleton]; rintro r rfl; exact dV)
    (by simp only [List.mem_singleton]; rintro r rfl; exact state_wrs hpR)) f hr

/-- The block before `update`'s frame, from `st` at offset `o`. -/
abbrev updBlock (H : Hash) (o : Nat) : List Instr :=
  [] ++ [.mov .eax (.imm 0), .mov .edi (.imm (BitVec.ofNat 32 0)), .mov .ecx (.imm (BitVec.ofNat 32 H.B))] ++
    Impl.Hmac.Generic.X86.scr .edx o

theorem updArgs_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block (updBlock H o)) s fun t =>
      KS (H := H) sc s₀ t ∧ UpdArgs hH t .edi st p (dO s₀ o) (scr s₀) (BitVec.ofNat 32 0) H.B ∧ t.mem = s.mem := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  have hB := hp.hB; have hB0 := hp.hB0; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o + H.B ≤ 8 * sc := by omega
  have ea := addr_dO hp (o := o) (by omega)
  have dsub : Region.Sub ⟨(dO s₀ o).setWidth 64, H.B⟩ (bufR (H := H) s₀) := by
    rw [ea]
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨(dO s₀ o).setWidth 64, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [updBlock, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_movi fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_movi fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    wp_addi fun s₅ u₅ => WP.block_nil ?_
  have g : ∀ r, r ≠ .eax → r ≠ .edi → r ≠ .ecx → r ≠ .edx → s₅.gpr r = s.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have k₅ : KS (H := H) sc s₀ s₅ :=
    ⟨((((hk.toKR.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅, by rw [g _ (by decide) (by decide) (by decide) (by decide), hk.ebx],
      by rw [g _ (by decide) (by decide) (by decide) (by decide), hk.esi]⟩
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₅, ?_, hm⟩
  exact
    { hst := by
        rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact k₅.ebx
        · exact k₅.esi
      hlo := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
      eax := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.gpr]
      ecx := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
      edx := by rw [u₅.gpr, u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide),
          hk.ebp]
      ebp := k₅.ebp
      hr := by rcases hst with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      hl := by decide
      hlen := by omega
      sp48 := by rw [k₅.esp]; exact hp.sp48
      cd := by
        rw [k₅.rd, k₅.wr, ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.rd, hp.wr]; simp) ho'
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p.setWidth 64, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      b_st := by rw [stk_eq k₅.toKR]; exact dK
      b_d := by rw [stk_eq k₅.toKR]; exact hp.b_s.sub_right dsc
      b_sc := by rw [stk_eq k₅.toKR]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := np
      nd := by rw [toNat_dO hp (by omega)]; omega
      nsc := by have := hH.hWb; omega }

theorem updCall_ok {t : State} (hk : KS (H := H) sc s₀ t) {st : Reg} {p d : BitVec 32}
    (hpR : p = inn s₀ ∨ p = out s₀) (ha : UpdArgs hH t .edi st p d (scr s₀) (BitVec.ofNat 32 0) H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem (p.setWidth 64) [] →
        hH.SH.Repr s'.mem (p.setWidth 64) ([] ++ bytesAt t.mem (d.setWidth 64) H.B)) → Q s') :
    WP isa (.frame (.push (upd6 .edi st)) (.call H.updN H.updC) (.pop .eax (upd6 .edi st).length)) t Q := by
  obtain ⟨dS, dK, dV, np⟩ := state_disj hp hpR
  refine upd_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [stk_eq hk.toKR] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f fun hr => hpost [] hr (by rw [zero_append_ofNat (by decide)]; rfl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dV
    · exact (cal_save hH hp).symm
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact state_wrs hpR
    · exact ⟨scR sc s₀, by simp, cal_sub hH hp⟩

theorem callUpd_ok {s : State} (hk : KS (H := H) sc s₀ s) {st : Reg} {p : BitVec 32}
    (hst : st = .ebx ∧ p = inn s₀ ∨ st = .esi ∧ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KS (H := H) sc s₀ s' → Frame [⟨p.setWidth 64, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem (p.setWidth 64) [] →
        hH.SH.Repr s'.mem (p.setWidth 64) ([] ++ bytesAt s.mem ((scr s₀).setWidth 64 + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [] st .edi 0 o H.B) s Q := by
  have hpR : p = inn s₀ ∨ p = out s₀ := by rcases hst with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [h]
  have hf := hp.fits; have := hp.hB; have := hp.hB0; have ho' := ho; simp only [Hash.buf] at hf ho'
  have ea := addr_dO hp (o := o) (by omega)
  refine WP.seq (WP.mono (updArgs_ok hH hp hk hst ho) fun t ⟨k, a, m⟩ =>
    updCall_ok hH hp k hpR a fun s' k' f r => hQ s' k' (m ▸ f) fun hr => ?_)
  have := r (m ▸ hr)
  rwa [m, ea] at this

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

include hH in
theorem blockKey_eq :
    blockKey hH.SH.H (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega,
    ↓reduceIte]

theorem correct :
    WP isa H.init s₀ fun s' => abiPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits
  simp only [Hash.buf] at hf
  -- Where things are.
  have dIS : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (inR (H := H) s₀) :=
    hp.i_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dIO : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (outR (H := H) s₀) :=
    hp.o_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOS : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (inR (H := H) s₀) :=
    hp.i_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOO : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (outR (H := H) s₀) :=
    hp.o_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dIK : Region.Disjoint ⟨P (H := H) s₀, H.B⟩ (stkR s₀) :=
    hp.b_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOK : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (stkR s₀) :=
    hp.b_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOC : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (calR hH s₀) :=
    (cal_buf hH hp).symm.sub_left (padO_sub hp)
  have eO : (scr s₀).setWidth 64 + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (states_ok hp h₁.kr) fun s₂ ⟨k₂, m₂⟩ => ?_)
  have bI₂ : bytesAt s₂.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad := by rw [m₂]; exact h₁.bufI
  have bO₂ : bytesAt s₂.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad := by
    rw [m₂]; exact h₁.bufO
  refine WP.seq (callInit_ok hH hp k₂ (.inl ⟨rfl, rfl⟩) fun s₃ k₃ f₃ r₃ => ?_)
  have bI₃ := (bytes_keep f₃ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dIS, dIK])
    (by omega)).trans bI₂
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dOS, dOK])
    (by omega)).trans bO₂
  refine WP.seq (callUpd_ok hH hp k₃ (.inl ⟨rfl, rfl⟩) (.inl rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := r₄ r₃
  rw [List.nil_append, show (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf = P (H := H) s₀ from rfl, bI₃] at rI₄
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) ; exacts [dOS, dOC, dOK])
    (by omega)).trans bO₃
  refine WP.seq (callInit_ok hH hp k₄ (.inr ⟨rfl, rfl⟩) fun s₅ k₅ f₅ r₅ => ?_)
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.b_i.symm) rI₄
  have bO₅ := (bytes_keep f₅ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) ; exacts [dOO, dOK])
    (by omega)).trans bO₄
  refine WP.seq (callUpd_ok hH hp k₅ (.inr ⟨rfl, rfl⟩) (.inr rfl) fun s₆ k₆ f₆ r₆ => ?_)
  have rO₆ := r₆ r₅
  rw [List.nil_append, eO, bO₅] at rO₆
  have rI₆ := repr_keep hH f₆ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.b_i.symm) rI₅
  have hsc : ⟨(scr s₀).setWidth 64, 8 * sc⟩ ∈ s₆.wr := by rw [k₆.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₆.ebp k₆.saved hsc (by omega) hp.nw) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, by rw [hm]; exact k₆.toKR.ret hp⟩, ?_⟩
  · by_cases he : r = .esp
    · subst he; rw [ho _ (by decide) (by decide), k₆.esp]
    · exact hg r (callee_saved r hr he)
  · show hH.SH.Repr s'.mem ((inn s₀).setWidth 64) _ ∧ hH.SH.Repr s'.mem ((out s₀).setWidth 64) _
    rw [hm, blockKey_eq hH hp]
    exact ⟨rI₆, rO₆⟩

end

end VG.Proof.Hmac.Generic.X86.Init
