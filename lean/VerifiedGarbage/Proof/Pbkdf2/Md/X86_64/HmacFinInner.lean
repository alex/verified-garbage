import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.Common
import VerifiedGarbage.Proof.Framework.OffsetBelow
import VerifiedGarbage.Proof.Framework.OmegaLit

/-!
# HMAC over any Merkle–Damgård hash function on x86-64: `finalize` up to the inner digest

HMAC's `finalize` (`Impl/Pbkdf2/Md/X86_64.lean`) starts by saving our
caller's registers (`pro_ok`) and finalizing the inner state into `scratch`
with the streaming `finalize` (`fin1Args_ok`, `finCall_ok`): what holds from
the prologue on (`KR`), and that call in two runs (`fin_rel'`). The rest is
`Proof/Pbkdf2/Md/X86_64/HmacFin.lean`.
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.HmacFin

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Stream)
open VG.Proof.Pbkdf2.Md.X86_64.Calls
open VG.Proof.Hmac.Generic.Common (off_disj off_disj0 covers_one sub_of_off sub_of_self)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi)
open Spec.Sha256 (bytesAt)

variable {H : Stream} (hH : StreamOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev outer : Addr := s₀.gpr .rsi
abbrev op : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outerR : Region := ⟨outer s₀, H.S⟩
abbrev opR : Region := ⟨op s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
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
  ret_i : (retR s₀).Disjoint (inR (H := H) s₀)
  ret_o : (retR s₀).Disjoint (outerR (H := H) s₀)
  ret_p : (retR s₀).Disjoint (opR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  stk_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 256
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit,
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
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 48) (by omega_nat) (by omega_nat)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hD; simp only [Stream.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 48) (b := 8 * H.W + 48) (n := H.F) (by omega_nat) (by omega_nat)
    (by omega_nat)

omit hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) :=
  Offset.below_disjoint _ (m := 16) (by omega_nat)

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = outer s₀
  r13 : s.gpr .r13 = op s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .r12, .r13, .r15, .rsp]

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15,
    h.saved.frame H hf hs, (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

theorem KR.regs {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) (hm : s'.mem = s.mem) : KR (H := H) s₀ s' :=
  h.keep hrd hwr hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem KR.call {s₀ s s' : State} (h : KR (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws ++ [stkR s₀], (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ ws ++ [stkR s₀], (retR s₀).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [h.rsp] at f
  exact h.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f hs hr

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) s₀ s ∧ s.gpr .rdi = inn s₀ ∧
    s.gpr .rdx = s₀.gpr .rdx ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hL : 8 * H.W + 48 ≤ 8 * sc := by have := hp.fits; simp only [Stream.buf] at this; omega_nat
  refine save_ok H (scr := scr s₀) rfl hp.hW (wr_mem hp).1 hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .rbx → r ≠ .r12 → r ≠ .r13 → r ≠ .r15 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    k _ (by decide) (by decide) (by decide) (by decide),
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    hm ▸ sv₁, ?_⟩, k _ (by decide) (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide) (by decide), hm ▸ f₁⟩
  rw [hm]
  exact (f₁.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_s.sub_right (save_sub hp)) (by decide))

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) s₀ t) (hdi : t.gpr .rdi = inn s₀)
    (hdx : t.gpr .rdx = T (H := H) s₀) (hcx : t.gpr .rcx = scr s₀) :
    FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; simp only [Stream.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { rdi := hdi, rdx := hdx, rcx := hcx
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
      stk_st := by rw [hk.rsp]; exact hp.stk_i
      stk_o := by rw [hk.rsp]; exact hp.stk_s.sub_right (t_sub hp)
      stk_sc := by rw [hk.rsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

/-- The first call's arguments: the count from `rdx`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) (hdi : s.gpr .rdi = inn s₀) {c : BitVec 64}
    (hdx : s.gpr .rdx = c) :
    WP isa (.block ([] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
      ([.mov .rcx (.reg .r15)] : List Instr))) s fun t => KR (H := H) s₀ t ∧
        FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem := by
  have hf := hp.fits; have hW := hp.hW; have hbuf : H.buf = 8 * H.W + 48 := rfl
  simp only [VG.Impl.Pbkdf2.Md.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_addi fun s₃ u₃ => wp_mov fun s₄ u₄ _ _ =>
    WP.block_nil ?_
  have k₄ : KR (H := H) s₀ s₄ := hk.regs (by rw [u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;>
        rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)])
    (by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hdi]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₁.other _ (by decide), hk.r15, sx_ofNat (by omega_nat)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r15]
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hdx]

/-- The second call's arguments: the state at `rbx`, of `B + D` bytes. -/

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (inn s₀) m → m.length < 2 ^ 64 → t.gpr .rsi = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.call H.finN H.finC) t Q :=
  fin_call hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [hk.rsp] at f
    refine hQ s' (hk.call ha' ?_ ?_) f hpost
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.i_s.symm.sub_left (save_sub hp)
      · exact save_t hp
      · exact (cal_save hH hp).symm
      · exact hp.stk_s.symm.sub_left (save_sub hp)
    · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact hp.ret_i
      · exact hp.ret_s.sub_right (t_sub hp)
      · exact hp.ret_s.sub_right (cal_sub hH hp)
      · exact (stk_ret (s₀ := s₀)).symm


end

/-! ## In two runs -/

/-- The block that sets up the first call of `finalize`. -/
abbrev fin1Block (H : Stream) : List Instr :=
  [] ++ ([.mov .rsi (.reg .rdx)] : List Instr) ++ VG.Impl.Pbkdf2.Md.X86_64.scr .rdx H.buf ++
    ([.mov .rcx (.reg .r15)] : List Instr)

variable {sc : Nat}
variable {s₀ s₀' : State} (hp : Pre (H := H) sc s₀) (hp' : Pre (H := H) sc s₀') (hq : PubEq s₀ s₀')

theorem kr_agree {s s' : State} (hq : PubEq s₀ s₀') (h : KR (H := H) s₀ s) (h' : KR (H := H) s₀' s') :
    ∀ r ∈ kregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.r12, h'.r12, outer, outer, hq.rsi]
  · rw [h.r13, h'.r13, op, op, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

include hH hp hp' hq

omit hH hp hp' in
theorem eqs : inn s₀' = inn s₀ ∧ T (H := H) s₀' = T (H := H) s₀ ∧ scr s₀' = scr s₀ :=
  ⟨hq.rdi.symm, by show s₀'.gpr .r8 + _ = s₀.gpr .r8 + _; rw [hq.r8], hq.r8.symm⟩

/-- A call of `finalize` from a block that sets up its arguments. -/
theorem fin_rel' {blk : List Instr} {c : BitVec 64} {F F' : State → Prop}
    (hck : ∃ hc, (Taint.check taint (Taint.ofRegs kregs) (.block blk) hc).isSome = true)
    (hag : ∀ s s', F s → F' s' → ∀ r ∈ kregs, s.gpr r = s'.gpr r)
    (hb : ∀ s, F s → WP isa (.block blk) s fun t => KR (H := H) s₀ t ∧
      FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c ∧ t.mem = s.mem)
    (hb' : ∀ s, F' s → WP isa (.block blk) s fun t => KR (H := H) s₀' t ∧
      FinArgs hH t (inn s₀') (T (H := H) s₀') (scr s₀') ∧ t.gpr .rsi = c ∧ t.mem = s.mem) :
    RelCT isa (fun s s' => F s ∧ F' s') (.seq (.block blk) (.call H.finN H.finC))
      fun s s' => KR (H := H) s₀ s ∧ KR (H := H) s₀' s' := by
  obtain ⟨e1, e2, e3⟩ := eqs hq
  have ha := rel_taint (G := fun t => KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧
      t.gpr .rsi = c)
    (G' := fun t => KR (H := H) s₀' t ∧ FinArgs hH t (inn s₀) (T (H := H) s₀) (scr s₀) ∧ t.gpr .rsi = c)
    kregs hag hck (fun s h => WP.mono (hb s h) fun _ ⟨k, a, si, _⟩ => ⟨k, a, si⟩)
    (fun s h => WP.mono (hb' s h) fun _ ⟨k, a, si, _⟩ => ⟨k, e1 ▸ e2 ▸ e3 ▸ a, si⟩)
  refine ha.seq (rel_wp (fin_rel hH (st := inn s₀) (o := T (H := H) s₀) (sc := scr s₀)
    fun s s' ⟨⟨k, a, si⟩, ⟨k', a', si'⟩⟩ => ⟨a, a', by rw [si, si'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp k a fun _ k' _ _ => k')
    (fun _ ⟨k, a, _⟩ => finCall_ok hH hp' k (e1.symm ▸ e2.symm ▸ e3.symm ▸ a) fun _ k' _ _ => k'))

end VG.Proof.Pbkdf2.Md.X86_64.HmacFin
