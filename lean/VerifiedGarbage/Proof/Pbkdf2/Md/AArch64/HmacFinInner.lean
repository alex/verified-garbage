import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.Common
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any Merkle–Damgård hash function on AArch64: `finalize` up to the inner digest

As on x86-64 (`Proof/Pbkdf2/Md/X86_64/HmacFinInner.lean`): HMAC's `finalize`
(`Impl/Pbkdf2/Md/AArch64.lean`) starts by saving our caller's registers and
our return address (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/AArch64/HmacFin.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.HmacFin

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Stream)
open VG.Impl.MdStream.AArch64 (mov)
open VG.Proof.Pbkdf2.Md.AArch64.Calls
open VG.Proof.Hmac.Generic.Common (inRegions_of_sub off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset contains_offset Upd wp_mov wp_movz wp_addImm)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : StreamOK H) (sc : Nat)

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
  hW : H.W ≤ 134
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
  have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact sub_offset (by omega_nat) (by omega_nat)

theorem t_sub : Region.Sub (tR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hD
  exact sub_offset hp.fits (by omega_nat)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Stream.buf] at this
  exact Region.sub_prefix (by omega_nat)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

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
abbrev kregs : List Reg := [.x19, .x20, .x21, .x23, .x25, .x26, .x27, .x28]

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
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine save_ok H (scr := scr s₀) rfl (Nat.le_trans hp.hW (by decide)) (wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
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
  have hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
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
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega_nat)
      st_o := hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := (cal_t hH hp).symm
      sp16 := by rw [hk.sp]; exact hp.sp16
      stk_st := by rw [hk.sp]; exact hp.stk_i
      stk_o := by rw [hk.sp]; exact hp.stk_s.sub_right (t_sub hp)
      stk_sc := by rw [hk.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem buf_lt : H.buf < 4096 := by
  have := hp.hW; simp only [Stream.buf]; omega_nat

/-- The first call's arguments: the count from `x2`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) (h0 : s.gpr .x0 = inn s₀) {c : BitVec 64}
    (h2 : s.gpr .x2 = c) :
    WP isa (.block ([] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr))) s fun t =>
      KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem := by
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addImm (buf_lt hp) fun s₂ u₂ => wp_mov fun s₃ u₃ => WP.block_nil ?_
  have k₃ : KR (H := H) s₀ s₃ := ((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  refine ⟨k₃, finArgs hH hp k₃ ?_ ?_ ?_, ?_, by rw [u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h0]
  · rw [u₃.other _ (by decide), u₂.gpr, u₁.other _ (by decide), hk.x23]
  · rw [u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.x23]
  · rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h2]

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', VecKept t s' → KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → m.length < 2 ^ 64 → t.gpr .x1 = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.sp] at f
    refine hQ s' ha'.vec (hk.call ha' ?_) f hpost
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact save_t hp
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)

end

/-! ## In two runs -/

/-- The registers `KR` fixes that the code between the calls uses. -/
abbrev pubRegs : List Reg := [.x19, .x20, .x21, .x23]

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ [mov .x1 .x2] ++ ([.addImm .x .x2 .x23 H.buf, mov .x3 .x23] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, outer, outer, hq.x1]
  · rw [h.x21, h'.x21, op, op, hq.x3]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.x0.symm, by show s₀'.gpr .x4 + _ = s₀.gpr .x4 + _; rw [hq.x4], hq.x4.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs pubRegs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → s.sp = s'.sp ∧ ∀ r ∈ pubRegs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .x1 = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .x1 = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .x1 = c)
    pubRegs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, a, x1⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, x1, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, x1⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, x1⟩, ⟨k', a', x1'⟩⟩ => ⟨a, a', by rw [x1, x1'], by rw [k.sp, k'.sp, hq.sp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.AArch64.HmacFin
