import VerifiedGarbage.Proof.Pbkdf2.Stream.X86.Common
import VerifiedGarbage.Proof.Hmac.Generic.Common
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC on x86 (32-bit): the start of `finalize`

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86.lean`) starts by finalizing the inner
state with the hash function's streaming `finalize`, called with the code of
`Impl/Pbkdf2/Stream/X86.lean`: the prologue (`pro_ok`) loads `scratch`,
`inner`, `outer` and `out` (after our caller's registers are saved in
`scratch`), and the count just before the call, which passes it on
(`fin1Args_ok`, `finCall_ok`). What the rest keeps is `KR`;
`Proof/Pbkdf2/Md/X86/HmacFin.lean` continues from there.
-/

namespace VG.Proof.Pbkdf2.Stream.X86.Finalize

open VG.X86
open VG.Impl.Pbkdf2.Stream.X86 (Hash copy at_)
open VG.Proof.Pbkdf2.Stream.X86
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 sub_of_off sub_of_self bytes_keep
  bytesAt_take bytesAt_writeBytes_self')
open VG.Proof.Sha256.X86 (contains_offset)
open VG.Proof.Sha256.X86.Stream (Upd wp_mov wp_movi wp_movm wp_add wp_addi sub_offset)
open VG.Proof.Hmac.Common (bytesAt_length writeBytes_at bytesAt_getD' xorPad_length)
open Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev E : BitVec 32 := s₀.gpr .esp
abbrev inn : BitVec 32 := arg s₀ 0
abbrev outer : BitVec 32 := arg s₀ 1
abbrev op : BitVec 32 := arg s₀ 4
abbrev scr : BitVec 32 := arg s₀ 5
abbrev inR : Region := ⟨(inn s₀).setWidth 64, H.S⟩
abbrev outerR : Region := ⟨(outer s₀).setWidth 64, H.S⟩
abbrev opR : Region := ⟨(op s₀).setWidth 64, H.D⟩
abbrev scR : Region := ⟨(scr s₀).setWidth 64, 8 * sc⟩
abbrev argR : Region := ⟨addr (E s₀) 4, 24⟩
abbrev retR : Region := ⟨(E s₀).setWidth 64, 4⟩
abbrev stkR : Region := below (E s₀) 48
/-- Where the digests go. -/
abbrev T : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨(scr s₀).setWidth 64, hH.Wb⟩
/-- `T`, as a register holds it. -/
abbrev tO : BitVec 32 := scr s₀ + BitVec.ofNat 32 H.buf

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outerR (H := H) s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outerR (H := H) s₀)
  i_p : (inR (H := H) s₀).Disjoint (opR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_p : (outerR (H := H) s₀).Disjoint (opR (H := H) s₀)
  o_s : (outerR (H := H) s₀).Disjoint (scR sc s₀)
  p_s : (opR (H := H) s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_p : (argR s₀).Disjoint (opR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_p : (retR s₀).Disjoint (opR (H := H) s₀)
  r_s : (retR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  b_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (outer s₀).toNat + H.S ≤ 2 ^ 32
  np : (op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 28 ≤ 2 ^ 32
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h22]; rfl
  simp only [hS, hD, e] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, hfit, ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Hash.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 16) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hD
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.hW; have := hp.hD
  exact off_disj _ (a := 8 * H.W) (m := 16) (b := 8 * H.W + 16) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

theorem addr_tO : (tO (H := H) s₀).setWidth 64 = T (H := H) s₀ :=
  setWidth_add (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem toNat_tO : (tO (H := H) s₀).toNat = (scr s₀).toNat + H.buf :=
  toNat_add_ofNat (by have := hp.nw; have := hp.fits; have := hp.hD; omega_nat)

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega_nat)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega_nat)

end

/-! ## What the pieces keep -/

/-- The regions everything writes: our buffers and the stack below `esp`. -/
abbrev wrs (s₀ : State) : List Region := [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀, stkR s₀]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  ebx : s.gpr .ebx = inn s₀
  edi : s.gpr .edi = op s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame (wrs (H := H) sc s₀) s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.esp, .ebp, .ebx, .edi]

theorem kregs_callee : ∀ r ∈ kregs, r ∈ calleeSaved := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ≠ .esp → r ∉ cclob := by decide

section
variable {sc : Nat}

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) sc s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ wrs (H := H) sc s₀, Region.Sub r r') : KR (H := H) sc s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, (hg _ (by simp)).trans h.edi, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) sc s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) sc s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem stk_eq {s₀ s : State} (hk : KR (H := H) sc s₀ s) : stk s = stkR s₀ := by rw [stk, hk.esp]

end

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem argR_in : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 6) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr]
  exact ⟨argR s₀, argR_in hp, arg_contains rfl (by omega_nat) (by have := hp.spf; omega_nat)⟩

theorem KR.argEq {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    VG.X86.arg s i = VG.X86.arg s₀ i :=
  arg_keep rfl hk.esp (n := 24) (by have := hp.spf; omega_nat) hk.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.a_i
    · exact hp.a_p
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega_nat)

theorem KR.readArg {s : State} (hk : KR (H := H) sc s₀ s) {i : Nat} (hi : i < 6) :
    s.mem.readW (argAddr s₀ i) 32 = VG.X86.arg s₀ i := by
  have := hk.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, hk.esp]] at this

theorem KR.ret {s : State} (hk : KR (H := H) sc s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  hk.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.r_i
    · exact hp.r_p
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

/-- `KR` after a call that writes `rs`, parts of our buffers, and keeps `esi`. -/
theorem KR.call {s s' : State} (hk : KR (H := H) sc s₀ s) {rs : List Region} (ha : After s rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ rs, Region.Sub r (scR sc s₀) ∨ r = inR (H := H) s₀) :
    KR (H := H) sc s₀ s' := by
  have f := ha.frame
  rw [stk_eq hk] at f
  refine hk.keep ha.rd ha.wr (fun r hr => ha.cs r (kregs_callee r hr)) f ?_ ?_
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · exact hs r hr
    · exact hp.b_s.symm.sub_left (save_sub hp)
  · simp only [List.mem_append, List.mem_singleton]
    rintro r (hr | rfl)
    · rcases hsub r hr with h | rfl
      · exact ⟨scR sc s₀, by simp, h⟩
      · exact ⟨inR (H := H) s₀, by simp, fun _ h => h⟩
    · exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-! ## The pieces -/

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) sc s₀ s ∧ s.gpr .esi = outer s₀ ∧
    Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw; have hD := hp.hD
  simp only [Hash.buf] at hf
  obtain ⟨sR, _, _⟩ := wr_mem hp
  have dA : ∀ r ∈ [saveR H (scr s₀)], (argR s₀).Disjoint r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.a_s.sub_right (save_sub hp)
  simp only [Hash.finPrologue, List.singleton_append]
  refine wp_movm (a := argAddr s₀ 5) (argW rfl 5) (argIn hp rfl rfl (by decide)) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega_nat) (by omega_nat)
    fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  have e₂ : ∀ r, r ≠ .eax → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have rA : ∀ i < 6, s₂.mem.readW (argAddr s₀ i) 32 = arg s₀ i := fun i hi =>
    f₂'.readW (r := ⟨argAddr s₀ i, 4⟩) (Region.contains_self _ _) (fun r hr =>
      (dA r hr).sub_left (arg_sub rfl (by omega_nat) (by have := hp.spf; omega_nat))) (by decide)
  have i₂ : ∀ i < 6, InRegions (s₂.rd ++ s₂.wr) (argAddr s₀ i) 4 := fun i hi => by
    rw [rd₂, wr₂, u₁.rd, u₁.wr]; exact argIn hp rfl rfl hi
  refine wp_mov fun s₃ u₃ => ?_
  refine wp_movm (a := argAddr s₀ 0) (by rw [ea_at, u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₃.rd, u₃.wr]; exact i₂ 0 (by decide)) fun s₄ u₄ => ?_
  refine wp_movm (a := argAddr s₀ 1) (by
      rw [ea_at, u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 1 (by decide)) fun s₅ u₅ => ?_
  refine wp_movm (a := argAddr s₀ 4) (by
      rw [ea_at, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]; rfl)
    (by rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr]; exact i₂ 4 (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, u₁.gpr]; rfl,
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.mem, rA 0 (by decide)],
    by rw [u₆.gpr, u₅.mem, u₄.mem, u₃.mem, rA 4 (by decide)],
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> decide),
    (hm ▸ f₂').sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨scR sc s₀, by simp, save_sub hp⟩⟩,
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, rA 1 (by decide)], hm ▸ f₂'⟩

/-- The arguments of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) sc s₀ t) {lo hi : BitVec 32} (hax : t.gpr .eax = lo)
    (hcx : t.gpr .ecx = hi) (hdx : t.gpr .edx = tO (H := H) s₀) :
    FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) lo hi := by
  have hwb := hH.hWb; have hf := hp.fits; have hf' := hp.fits; have hD := hp.hD; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { hst := hk.ebx, eax := hax, ecx := hcx, edx := hdx, ebp := hk.ebp, hr := by decide
      sp48 := by rw [hk.esp]; exact hp.sp48
      cw := by
        rw [hk.wr, addr_tO hp]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := by rw [addr_tO hp]; exact hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := by rw [addr_tO hp]; exact (cal_t hH hp).symm
      b_st := by rw [stk_eq hk]; exact hp.b_i
      b_o := by rw [stk_eq hk, addr_tO hp]; exact hp.b_s.sub_right (t_sub hp)
      b_sc := by rw [stk_eq hk]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := hp.ni
      no := by rw [toNat_tO hp]; omega_nat
      nsc := by omega_nat }

/-- The first call's arguments: the count from the stack. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) sc s₀ s) :
    WP isa (.block ([] ++ Hash.count1 ++ Impl.Pbkdf2.Stream.X86.scr .edx H.buf)) s fun t =>
      KR (H := H) sc s₀ t ∧ FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) (arg s₀ 2) (arg s₀ 3) ∧
        t.gpr .esi = s.gpr .esi ∧ t.mem = s.mem := by
  simp only [Hash.count1, Impl.Pbkdf2.Stream.X86.scr, List.cons_append, List.nil_append]
  refine wp_movm (a := argAddr s₀ 2) (by rw [ea_at, hk.esp]; rfl) (argIn hp hk.rd hk.wr (by decide))
    fun s₁ u₁ => ?_
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, u₁.other _ (by decide), hk.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact argIn hp hk.rd hk.wr (by decide)) fun s₂ u₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
  have k₄ : KR (H := H) sc s₀ s₄ := (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd
    (by decide) u₄
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.readArg hp (by decide)]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.mem, hk.readArg hp (by decide)]
  · rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.ebp]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]

theorem finCall_ok {t : State} (hk : KR (H := H) sc s₀ t) {lo hi : BitVec 32}
    (ha : FinArgs hH t .ebx (inn s₀) (tO (H := H) s₀) (scr s₀) lo hi) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ s' → s'.gpr .esi = t.gpr .esi →
      Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem ((inn s₀).setWidth 64) m → m.length < 2 ^ 64 → hi ++ lo = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push (fin5 .ebx)) (.call H.finN H.finC) (.pop .eax (fin5 .ebx).length)) t Q :=
  fin_frame hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [stk_eq hk, addr_tO hp] at f
    rw [addr_tO hp] at hpost
    refine hQ s' (hk.call hp ha' ?_ ?_) (ha'.cs .esi (by simp [calleeSaved])) f hpost
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (save_sub hp)
      · exact save_t hp
      · exact (cal_save hH hp).symm
    · simp only [List.mem_cons, List.not_mem_nil, or_false]
      rw [addr_tO hp]
      rintro r (rfl | rfl | rfl)
      · exact .inr rfl
      · exact .inl (t_sub hp)
      · exact .inl (cal_sub hH hp)

end

end VG.Proof.Pbkdf2.Stream.X86.Finalize
