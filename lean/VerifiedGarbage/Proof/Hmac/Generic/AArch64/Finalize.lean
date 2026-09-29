import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Init
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Finalize

/-!
# HMAC over any streaming hash function on AArch64: `finalize`, correct

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Finalize.lean`).
-/

namespace VG.Proof.Hmac.Generic.AArch64.Finalize

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash copy)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.AArch64.Init (untouched untouched_clob)
open VG.Proof.Hmac.Generic.X86_64 (inRegions_of_sub)
open VG.Proof.Hmac.Generic.X86_64.Init (off_disj off_disj0 covers_one sub_of_off sub_of_self bytes_keep)
open VG.Proof.Hmac.Generic.X86_64.Finalize (bytesAt_take bytesAt_writeBytes_self' xorPad_length)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.MdStream.AArch64 (Upd wp_mov wp_movz wp_addImm)
open VG.Proof.Hmac.X86_64 (bytesAt_length writeBytes_at bytesAt_getD')
open Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev outer : Addr := s₀.gpr .x1
abbrev op : Addr := s₀.gpr .x3
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outerR : Region := ⟨outer s₀, H.S⟩
abbrev opR : Region := ⟨op s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
/-- Where the digests go. -/
abbrev T : Addr := scr s₀ + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [outerR (H := H) s₀]
  wr : s₀.wr = [inR (H := H) s₀, opR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outerR (H := H) s₀)
  i_p : (inR (H := H) s₀).Disjoint (opR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_p : (outerR (H := H) s₀).Disjoint (opR (H := H) s₀)
  o_s : (outerR (H := H) s₀).Disjoint (scR sc s₀)
  p_s : (opR (H := H) s₀).Disjoint (scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  stk_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hfit,
    ⟨hH.hB0, hH.hBB⟩, hH.hW, ⟨hH.hS0, hH.hSB⟩, ⟨hH.hD0, hH.hDF, hH.hF⟩⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Hash.buf] at *
  exact sub_offset (by omega) (by omega)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega) (by omega)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := H.F) (by omega) (by omega)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Hash.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := H.F) (by omega) (by omega)
    (by omega)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = outer s₀
  x21 : s.gpr .x21 = op s₀
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x21, .x23, .x25, .x26, .x27, .x28, .x29]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ kregs := by decide
theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (untouched_kregs r hr)).trans (h.cs r hr), h.saved.frame H hf hs⟩

theorem KR.regs {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp)

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s s' d v) : KR (H := H) s₀ s' :=
  h.regs u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) u.mem

theorem KR.call {s₀ s s' : State} (h : KR (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws ++ [stkR s₀], (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.sp] at f
  exact h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f hs

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) s₀ s ∧ s.gpr .x0 = inn s₀ ∧
    s.gpr .x2 = s₀.gpr .x2 ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine save_ok H (scr := scr s₀) rfl hp.hW (wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k : ∀ r, r ≠ .x19 → r ≠ .x20 → r ≠ .x21 → r ≠ .x23 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    fun r hr => k r (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide)
      (fun e => by subst e; revert hr; decide) (fun e => by subst e; revert hr; decide),
    hm ▸ sv₁⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) s₀ t) (h0 : t.gpr .x0 = inn s₀)
    (h2 : t.gpr .x2 = T (H := H) s₀) (h3 : t.gpr .x3 = scr s₀) :
    FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; simp only [Hash.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { x0 := h0, x2 := h2, x3 := h3
      cw := by
        rw [hk.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_o := hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := (cal_t hH hp).symm
      sp16 := by rw [hk.sp]; exact hp.sp16
      stk_st := by rw [hk.sp]; exact hp.stk_i
      stk_o := by rw [hk.sp]; exact hp.stk_s.sub_right (t_sub hp)
      stk_sc := by rw [hk.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem buf_lt : H.buf < 4096 := by
  have := hp.hW; simp only [Hash.buf]; omega

/-- The first call's arguments: the count from `x2`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) (h0 : s.gpr .x0 = inn s₀) {c : BitVec 64}
    (h2 : s.gpr .x2 = c) :
    WP isa (.block ([] ++ [mov .x1 .x2] ++ [.addImm .x .x2 .x23 H.buf, mov .x3 .x23])) s fun t =>
      KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm (buf_lt hp) fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  have k₃ : KR (H := H) s₀ s₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine ⟨k₃, finArgs hH hp k₃ ?_ ?_ ?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hk.x23]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2]

/-- The second call's arguments: the state at `x19`, of `B + D` bytes. -/
theorem fin2Args_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (.block ([mov .x0 .x19] ++ [.movz .x .x1 (BitVec.ofNat 16 (H.B + H.D)) 0] ++
      [.addImm .x .x2 .x23 H.buf, mov .x3 .x23])) s fun t =>
        KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
        t.gpr .x1 = BitVec.ofNat 64 (H.B + H.D) ∧ t.mem = s.mem := by
  have hB := hp.hB; have hD := hp.hD
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm (buf_lt hp) fun s₃ u₃ => wp_mov fun s₄ u₄ =>
    WP.block_nil ?_
  have k₄ : KR (H := H) s₀ s₄ :=
    (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.x19]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, movz_ofNat (by omega)]

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.sp] at f
    refine hQ s' (hk.call ha' ?_) f hpost
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact save_t hp
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (.block ([mov .x0 .x19] ++ [.movz .x .x1 (BitVec.ofNat 16 H.B) 0, .addImm .x .x2 .x23 H.buf,
      .movz .x .x3 (BitVec.ofNat 16 H.D) 0, mov .x4 .x23])) s fun t =>
        KR (H := H) s₀ t ∧ UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D ∧
        t.gpr .x1 = BitVec.ofNat 64 H.B ∧ t.mem = s.mem := by
  have hf := hp.fits; have hW := hp.hW; have hB := hp.hB; have hD := hp.hD; have hwb := hH.hWb
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm (buf_lt hp) fun s₃ u₃ => wp_movz fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ : KR (H := H) s₀ s₅ :=
    ((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (tR (H := H) s₀) := Region.sub_prefix hD.2.1
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      movz_ofNat (by omega)], by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, hk.x19]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), hk.x23]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, movz_ofNat (by omega), toNat_ofNat_lt (by omega)]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), hk.x23]
      cd := by
        rw [k₅.rd, k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by simp only [Hash.buf] at hf ⊢; omega)
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self iR (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; simp only [Hash.buf] at hf; omega)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      d_st := (hp.i_s.sub_right (fun a h => t_sub hp a (tsub a h))).symm
      d_sc := (cal_t hH hp).symm.sub_left tsub
      sp16 := by rw [k₅.sp]; exact hp.sp16
      stk_st := by rw [k₅.sp]; exact hp.stk_i
      stk_d := by rw [k₅.sp]; exact hp.stk_s.sub_right (fun a h => t_sub hp a (tsub a h))
      stk_sc := by rw [k₅.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : UpdArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) H.D)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → t.gpr .x1 = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (inn s₀) (m ++ bytesAt t.mem (T (H := H) s₀) H.D)) → Q s') :
    WP isa (.call H.updN H.updC) t Q :=
  upd_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.sp] at f
    refine hQ s' (hk.call ha' ?_) f hpost
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)

/-! ## The copies -/

omit hp in
theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The outer state over the inner one. -/
theorem copy1_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (copy .x20 0 .x19 0 H.S) s fun t => KR (H := H) s₀ t ∧
      t.mem = writeBytes s.mem (inn s₀) (bytesAt s.mem (outer s₀) H.S) := by
  have hS := hp.hS
  obtain ⟨_, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  refine WP.mono (copy_ok (so := 0) (d := 0) (n := H.S) (by decide) (by decide) (by decide) (by decide) hS.1
    (by omega)
    (fun k hk' => by rw [hk.x20, add_zero']; exact inRegions_of_sub oR (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.x19, add_zero', hk.wr]; exact inRegions_of_sub iR (fun _ h => h) (by omega) hk')
    (by rw [hk.x20, hk.x19, add_zero', add_zero']; exact hp.i_o.symm)) fun t c => ?_
  rw [hk.x19, hk.x20, add_zero', add_zero'] at c
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    (c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := inR (H := H) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp)), c.mem⟩

/-- The MAC to `out`. -/
theorem copy2_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (copy .x23 H.buf .x21 0 H.D) s fun t => KR (H := H) s₀ t ∧
      t.mem = writeBytes s.mem (op s₀) (bytesAt s.mem (T (H := H) s₀) H.D) := by
  have hD := hp.hD
  obtain ⟨sR, _, pR⟩ := wr_mem hp
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (scR sc s₀) := fun a h => t_sub hp a (Region.sub_prefix hD.2.1 a h)
  refine WP.mono (copy_ok (so := H.buf) (d := 0) (n := H.D) (by decide) (by decide) (buf_lt hp) (by decide)
    hD.1 (by omega)
    (fun k hk' => by rw [hk.x23, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) tsub (by omega) hk')
    (fun k hk' => by rw [hk.x21, add_zero', hk.wr]; exact inRegions_of_sub pR (fun _ h => h) (by omega) hk')
    (by rw [hk.x23, hk.x21, add_zero']; exact hp.p_s.symm.sub_left tsub)) fun t c => ?_
  rw [hk.x21, hk.x23, add_zero'] at c
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    (c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := opR (H := H) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp)), c.mem⟩

/-! ## Correctness -/

omit hp in
/-- The end: `abiPreserved`, from `KR` and `restore`. -/
theorem abi_of {s s' : State} (hk : KR (H := H) s₀ s) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) (ho : ∀ r, r ∉ savedRegs → s'.gpr r = s.gpr r) :
    abiPreserved s₀ s' := by
  refine ⟨fun r hr => ?_, by rw [hsp, hk.sp]⟩
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact hg _ (by decide)
    | exact (ho _ (by decide)).trans (hk.cs _ (by decide))

theorem correct : WP isa H.finalize s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  have hD := hp.hD; have hS := hp.hS; have hB := hp.hB
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (tR (H := H) s₀) := Region.sub_prefix hD.2.1
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, di₁, dx₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH hp k₁ di₁ dx₁) fun t₁ ⟨kt₁, a₁, si₁, m₁⟩ =>
    finCall_ok hH hp kt₁ a₁ fun s₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (copy1_ok hp k₂) fun s₃ ⟨k₃, m₃⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp k₃) fun t₃ ⟨kt₃, a₃, si₃, mt₃⟩ =>
    updCall_ok hH hp kt₃ a₃ fun s₄ k₄ f₄ r₄ => ?_))
  refine WP.seq (WP.seq (WP.mono (fin2Args_ok hH hp k₄) fun t₄ ⟨kt₄, a₄, si₄, mt₄⟩ =>
    finCall_ok hH hp kt₄ a₄ fun s₅ k₅ f₅ d₅ => ?_))
  refine WP.seq (WP.mono (copy2_ok hp k₅) fun s₆ ⟨k₆, m₆⟩ => ?_)
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine WP.mono (restore_ok H k₆.x23 hp.hW k₆.saved (by rw [k₆.wr]; exact sR) hL)
    fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ⟨abi_of k₆ hsp hg ho, ?_⟩
  -- The functional part.
  intro k0 text hk0 hlen hrI hcnt hrO
  rw [hH.hB] at hk0 hcnt
  have hl0 : (xorPad k0 ipad ++ text).length = H.B + text.length := by
    rw [List.length_append, xorPad_length, hk0]
  -- The outer state is untouched until it is copied.
  have oI : ∀ r ∈ [saveR H (scr s₀)], Region.Disjoint (outerR (H := H) s₀) r := by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.o_s.sub_right (save_sub hp)
  have o₂ : ∀ r ∈ [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀],
      Region.Disjoint (outerR (H := H) s₀) r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_o.symm
    · exact hp.o_s.sub_right (t_sub hp)
    · exact hp.o_s.sub_right (cal_sub hH hp)
    · exact hp.stk_o.symm
  have rO₂ := Init.repr_keep hH f₂ o₂ (m₁ ▸ Init.repr_keep hH f₁ oI hrO)
  -- The inner digest.
  have dig := d₂ _ (m₁ ▸ Init.repr_keep hH f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, hcnt, hl0])
  -- The copy of the outer state.
  have rI₃ : hH.SH.Repr s₃.mem (inn s₀) (xorPad k0 opad) := by
    refine hH.repr _ _ _ _ _ (fun i hi => ?_) rO₂
    rw [m₃, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
      bytesAt_getD' _ _ hi]
  have t₃ : bytesAt s₃.mem (T (H := H) s₀) H.D = bytesAt s₂.mem (T (H := H) s₀) H.D := by
    rw [m₃]
    exact bytes_keep (Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := inR (H := H) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)) (by
        simp only [List.mem_singleton]; rintro r rfl
        exact (hp.i_s.sub_right (t_sub hp)).symm.sub_left tsub) (by omega)
  have rI₄ := r₄ _ (mt₃ ▸ rI₃) (by rw [si₃, xorPad_length, hk0])
  rw [mt₃, t₃] at rI₄
  have hl₄ : (xorPad k0 opad ++ bytesAt s₂.mem (T (H := H) s₀) H.D).length = H.B + H.D := by
    rw [List.length_append, xorPad_length, hk0, bytesAt_length]
  have dig₂ := d₅ _ (mt₄ ▸ rI₄) (by rw [hl₄]; omega) (by rw [si₄, hl₄])
  show bytesAt s'.mem (op s₀) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hD', hm, m₆, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), bytesAt_take _ _ hD.2.1, dig₂,
    bytesAt_take _ _ hD.2.1, dig]
  rfl

end

end VG.Proof.Hmac.Generic.AArch64.Finalize
