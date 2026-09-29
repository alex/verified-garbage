import VerifiedGarbage.Proof.Hmac.Generic.Arm.Init
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Finalize

/-!
# HMAC over any streaming hash function on 32-bit ARM: `finalize`, correct

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Finalize.lean`). `out` and `scratch` are stack
arguments, loaded into `r6` and `r12`; the count stays in `r2:r3` until the
first call.
-/

namespace VG.Proof.Hmac.Generic.Arm.Finalize

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash copy scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Hmac.Generic.X86_64 (inRegions_of_sub)
open VG.Proof.Hmac.Generic.X86_64.Init (off_disj off_disj0 sub_of_off sub_of_self bytes_keep)
open VG.Proof.Hmac.Generic.X86_64.Finalize (bytesAt_take bytesAt_writeBytes_self' xorPad_length)
open VG.Proof.Sha256.Arm (contains_offset)
open VG.Proof.Sha256.Arm.Stream (Upd wp_mov wp_add wp_ldrSp op2_imm op2_reg sub_offset)
open VG.Proof.Hmac.X86_64 (bytesAt_length writeBytes_at bytesAt_getD')
open Spec.Sha256 (bytesAt)
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev outer : BitVec 32 := s₀.gpr .r1
abbrev op : BitVec 32 := stackArg s₀ 0
abbrev scr : BitVec 32 := stackArg s₀ 1
abbrev inR : Region := ⟨State.addr (inn s₀), H.S⟩
abbrev outerR : Region := ⟨State.addr (outer s₀), H.S⟩
abbrev opR : Region := ⟨State.addr (op s₀), H.D⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 8⟩
abbrev stkR : Region := below s₀
/-- Where the digests go. -/
abbrev T : Addr := State.addr (scr s₀) + BitVec.ofNat 64 H.buf
abbrev tR : Region := ⟨T (H := H) s₀, H.F⟩
abbrev calR : Region := ⟨State.addr (scr s₀), hH.Wb⟩
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
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outerR (H := H) s₀)
  b_p : (stkR s₀).Disjoint (opR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (outer s₀).toNat + H.S ≤ 2 ^ 32
  np : (op s₀).toNat + H.D ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 8 ≤ 2 ^ 32
  fits : H.buf + H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (finG hH.SH sc).pre s₀) (hfit : H.buf + H.F ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩ := h
  have hS := hH.hS
  have hD := hH.hD
  simp only [hS, hD] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, hfit,
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
  have := hH.hWb; have := hp.hW
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 36) (by omega) (by omega)

include hH in
theorem cal_t : (calR hH s₀).Disjoint (tR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hD
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 36) (n := H.F) (by omega) (by omega)

theorem save_t : (saveR H (scr s₀)).Disjoint (tR (H := H) s₀) := by
  have := hp.hW; have := hp.hD
  exact off_disj _ (a := 8 * H.W) (m := 36) (b := 8 * H.W + 36) (n := H.F) (by omega) (by omega)
    (by omega)

theorem buf_lt : H.buf < 4096 := by
  have := hp.hW; simp only [Hash.buf]; omega

theorem addr_tO : State.addr (tO (H := H) s₀) = T (H := H) s₀ :=
  addr_add (by have := hp.nw; have := hp.fits; have := hp.hD; omega)

theorem toNat_tO : (tO (H := H) s₀).toNat = (scr s₀).toNat + H.buf := by
  have := hp.nw; have := hp.fits; have := hp.hD; have := buf_lt hp
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := H.buf) (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem sa1 : stackArgAddr s₀ 1 = stackArgAddr s₀ 0 + BitVec.ofNat 64 4 := by
  have := hp.spf
  simp only [stackArgAddr, State.addr]; bv_omega

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = outer s₀
  r6 : s.gpr .r6 = op s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r6, .r11]

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide
theorem kregs_clob : ∀ r ∈ kregs, r ∉ clob := by decide

theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6, (hg _ (by simp)).trans h.r11,
    h.saved.frame H hf hs⟩

theorem KR.upd {s₀ s s' : State} (h : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s s' d v) : KR (H := H) s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

/-! ## The pieces -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem wr_mem : scR sc s₀ ∈ s₀.wr ∧ inR (H := H) s₀ ∈ s₀.wr ∧ opR (H := H) s₀ ∈ s₀.wr := by
  rw [hp.wr]; simp

theorem KR.call {t s' : State} (hk : KR (H := H) s₀ t) {ws : List Region} (ha : After t ws s')
    (hs : ∀ r ∈ ws, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [below_eq hk.sp] at f
  refine hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
  simp only [List.mem_append, List.mem_singleton]
  rintro r (hr | rfl)
  · exact hs r hr
  · exact hp.b_s.symm.sub_left (save_sub hp)

theorem pro_ok : WP isa (.block H.finPrologue) s₀ fun s => KR (H := H) s₀ s ∧ s.gpr .r0 = inn s₀ ∧
    count s = count s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  have hW := hp.hW; have hf := hp.fits; have nw := hp.nw; have hD := hp.hD
  simp only [Hash.buf] at hf
  obtain ⟨sR, _, _⟩ := wr_mem hp
  have aR : argR s₀ ∈ s₀.rd ++ s₀.wr := by rw [hp.rd]; simp
  simp only [Hash.finPrologue, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 1) (by decide) rfl
    ⟨argR s₀, aR, by rw [sa1 hp]; exact contains_offset (by omega) (by omega)⟩ fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact sR) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  have hsp₂ : s₂.sp = s₀.sp := by rw [sp₂, u₁.sp]
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) (by rw [u₄.sp, u₃.sp, hsp₂]; rfl)
      (by rw [u₄.rd, u₄.wr, u₃.rd, u₃.wr, rd₂, wr₂, u₁.rd, u₁.wr]
          exact ⟨argR s₀, aR, by simp [Region.Contains]⟩) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have hm : s₆.mem = s₂.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have f₂' : Frame [saveR H (scr s₀)] s₀.mem s₂.mem := by rw [← u₁.mem]; exact f₂
  have ea : s₂.mem.readW (stackArgAddr s₀ 0) 32 = op s₀ :=
    f₂'.readW (r := ⟨stackArgAddr s₀ 0, 4⟩) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl
      exact (hp.a_s.sub_left (Region.sub_prefix (by omega))).sub_right (save_sub hp)) (by decide)
  have k : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r11 → r ≠ .r12 → s₆.gpr r = s₀.gpr r :=
    fun r h4 h5 h6 h11 h12 => by
      rw [u₆.other r h11, u₅.other r h6, u₄.other r h5, u₃.other r h4, e₂ r h12]
  refine ⟨⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr],
    by rw [u₆.sp, u₅.sp, u₄.sp, u₃.sp, hsp₂],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)],
    by rw [u₆.other _ (by decide), u₅.gpr, u₄.mem, u₃.mem, ea],
    by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl,
    hm ▸ sv₂.of_eq H fun r hr => u₁.other r (by
      simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)⟩,
    k _ (by decide) (by decide) (by decide) (by decide) (by decide),
    by simp only [count, k _ (by decide) (by decide) (by decide) (by decide) (by decide : Reg.r2 ≠ .r12),
      k _ (by decide) (by decide) (by decide) (by decide) (by decide : Reg.r3 ≠ .r12)], hm ▸ f₂'⟩

/-- The regions of a call of `finalize` on `inner`, into `T`. -/
theorem finArgs {t : State} (hk : KR (H := H) s₀ t) (h0 : t.gpr .r0 = inn s₀)
    (h1 : t.gpr .r1 = tO (H := H) s₀) (h12 : t.gpr .r12 = scr s₀) :
    FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) := by
  have hwb := hH.hWb; have hf := hp.fits; have hf' := hp.fits; have hD := hp.hD; have nw := hp.nw
  simp only [Hash.buf] at hf
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  exact
    { r0 := h0, r1 := h1, r12 := h12
      sp16 := by rw [hk.sp]; exact hp.sp16
      cw := by
        rw [hk.wr, addr_tO hp]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_self iR le_rfl
          · exact sub_of_off sR hp.fits
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_o := by rw [addr_tO hp]; exact hp.i_s.sub_right (t_sub hp)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      o_sc := by rw [addr_tO hp]; exact (cal_t hH hp).symm
      b_st := by rw [below_eq hk.sp]; exact hp.b_i
      b_o := by rw [below_eq hk.sp, addr_tO hp]; exact hp.b_s.sub_right (t_sub hp)
      b_sc := by rw [below_eq hk.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := hp.ni
      no := by rw [toNat_tO hp]; omega
      nsc := by omega }

/-- The first call's arguments: the count still in `r2:r3`. -/
theorem fin1Args_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (.block ([.mov .r0 (.reg .r4)] ++ [] ++ scrAt .r1 H.buf ++ [.mov .r12 (.reg .r11)])) s fun t =>
      KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧ count t = count s ∧
        t.mem = s.mem := by
  have hl := buf_lt hp
  simp only [scrAt, List.cons_append, List.nil_append, List.append_nil]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_mov (op2_reg _ _) fun s₄ u₄ => WP.block_nil ?_
  have k₄ : KR (H := H) s₀ s₄ :=
    (((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  refine ⟨k₄, finArgs hH hp k₄ ?_ ?_ ?_, ?_, by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r4]
  · rw [u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.r11,
      movw_ofNat (by omega)]
  · rw [u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r11]
  · simp only [count, u₄.other _ (show Reg.r2 ≠ .r12 by decide), u₃.other _ (show Reg.r2 ≠ .r1 by decide),
      u₂.other _ (show Reg.r2 ≠ .r12 by decide), u₁.other _ (show Reg.r2 ≠ .r0 by decide),
      u₄.other _ (show Reg.r3 ≠ .r12 by decide), u₃.other _ (show Reg.r3 ≠ .r1 by decide),
      u₂.other _ (show Reg.r3 ≠ .r12 by decide), u₁.other _ (show Reg.r3 ≠ .r0 by decide)]

/-- The second call's arguments: the count `B + D`. -/
theorem fin2Args_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (.block ([.mov .r0 (.reg .r4)] ++ [.movw .r2 (BitVec.ofNat 16 (H.B + H.D)), .mov .r3 (.imm 0)] ++
      scrAt .r1 H.buf ++ [.mov .r12 (.reg .r11)])) s fun t =>
        KR (H := H) s₀ t ∧ FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) ∧
        count t = BitVec.ofNat 64 (H.B + H.D) ∧ t.mem = s.mem := by
  have hB := hp.hB; have hD := hp.hD; have hl := buf_lt hp
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_mov (op2_imm (by decide)) fun s₃ u₃ =>
    wp_movw fun s₄ u₄ => wp_add (op2_reg _ _) fun s₅ u₅ => wp_mov (op2_reg _ _) fun s₆ u₆ => WP.block_nil ?_
  have k₆ : KR (H := H) s₀ s₆ :=
    (((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆
  refine ⟨k₆, finArgs hH hp k₆ ?_ ?_ ?_, count_movw (by omega) ?_ ?_,
    by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, hk.r4]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r11, movw_ofNat (by omega)]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hk.r11]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]

theorem finCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : FinArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀))
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, tR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (State.addr (inn s₀)) m → m.length < 2 ^ 64 → count t = BitVec.ofNat 64 m.length →
        (bytesAt s'.mem (T (H := H) s₀) H.F).take H.D = hH.SH.H.hash m) → Q s') :
    WP isa (.frame (.push fin2) (.call H.finN H.finC) (.pop .r1 8)) t Q :=
  fin_frame hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [below_eq hk.sp, addr_tO hp] at f
    rw [addr_tO hp] at hpost
    refine hQ s' (KR.call hp hk ha' ?_) f hpost
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rw [addr_tO hp]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact save_t hp
    · exact (cal_save hH hp).symm

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (.block ([.mov .r0 (.reg .r4)] ++ scrAt .r1 H.buf ++ [.movw .r7 (BitVec.ofNat 16 H.D),
      .mov .r10 (.reg .r11), .movw .r2 (BitVec.ofNat 16 H.B), .mov .r3 (.imm 0)])) s fun t =>
        KR (H := H) s₀ t ∧ UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D ∧
        count t = BitVec.ofNat 64 H.B ∧ t.mem = s.mem := by
  have hf := hp.fits; have hW := hp.hW; have hB := hp.hB; have hD := hp.hD; have hwb := hH.hWb
  have nw := hp.nw; have hl := buf_lt hp; have hf2 := hp.fits; simp only [Hash.buf] at hf2
  obtain ⟨sR, iR, _⟩ := wr_mem hp
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_movw fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_movw fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have k₇ : KR (H := H) s₀ s₇ :=
    ((((((hk.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄).upd
      (by decide) u₅).upd (by decide) u₆).upd (by decide) u₇
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (tR (H := H) s₀) := Region.sub_prefix hD.2.1
  refine ⟨k₇, ?_, count_movw (by omega) (by rw [u₇.other _ (by decide), u₆.gpr]) u₇.gpr,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { r0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hk.r4]
      r1 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hk.r11,
          movw_ofNat (by omega)]
      r7 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
          movw_ofNat (by omega)]
      r10 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r11]
      hlen := by omega
      sp16 := by rw [k₇.sp]; exact hp.sp16
      cd := by
        rw [k₇.rd, k₇.wr, addr_tO hp]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by omega)
      cw := by
        rw [k₇.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self iR le_rfl
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; simp only [Hash.buf] at hf; omega)
      st_sc := hp.i_s.sub_right (cal_sub hH hp)
      d_st := by rw [addr_tO hp]; exact (hp.i_s.sub_right (fun a h => t_sub hp a (tsub a h))).symm
      d_sc := by rw [addr_tO hp]; exact (cal_t hH hp).symm.sub_left tsub
      b_st := by rw [below_eq k₇.sp]; exact hp.b_i
      b_d := by rw [below_eq k₇.sp, addr_tO hp]; exact hp.b_s.sub_right (fun a h => t_sub hp a (tsub a h))
      b_sc := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := hp.ni
      nd := by rw [toNat_tO hp]; omega
      nsc := by omega }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) (ha : UpdArgs hH t (inn s₀) (tO (H := H) s₀) (scr s₀) H.D)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [inR (H := H) s₀, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ m, hH.SH.Repr t.mem (State.addr (inn s₀)) m → count t = BitVec.ofNat 64 m.length →
        hH.SH.Repr s'.mem (State.addr (inn s₀)) (m ++ bytesAt t.mem (T (H := H) s₀) H.D)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) t Q :=
  upd_frame hH ha fun s' ha' hpost => by
    have f := ha'.frame
    rw [below_eq hk.sp] at f
    rw [addr_tO hp] at hpost
    refine hQ s' (KR.call hp hk ha' ?_) f hpost
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_s.symm.sub_left (save_sub hp)
    · exact (cal_save hH hp).symm

/-! ## The copies -/

omit hp in
theorem add_zero' (p : Addr) : p + BitVec.ofNat 64 0 = p := BitVec.add_zero p

/-- The outer state over the inner one. -/
theorem copy1_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (copy .r5 0 .r4 0 H.S) s fun t => KR (H := H) s₀ t ∧
      t.mem = writeBytes s.mem (State.addr (inn s₀)) (bytesAt s.mem (State.addr (outer s₀)) H.S) := by
  have hS := hp.hS; have ni := hp.ni; have no := hp.no
  obtain ⟨_, iR, _⟩ := wr_mem hp
  have oR : outerR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  refine WP.mono (copy_ok (so := 0) (d := 0) (n := H.S) (by decide) (by decide) (by decide) (by decide) hS.1
    (by omega) (by rw [hk.r5]; omega) (by rw [hk.r4]; omega)
    (fun k hk' => by rw [hk.r5, add_zero']; exact inRegions_of_sub oR (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.r4, add_zero', hk.wr]; exact inRegions_of_sub iR (fun _ h => h) (by omega) hk')
    (by rw [hk.r5, hk.r4, add_zero', add_zero']; exact hp.i_o.symm)) fun t c => ?_
  rw [hk.r4, hk.r5, add_zero', add_zero'] at c
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    (c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := inR (H := H) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.symm.sub_left (save_sub hp)), c.mem⟩

/-- The MAC to `out`. -/
theorem copy2_ok {s : State} (hk : KR (H := H) s₀ s) :
    WP isa (copy .r11 H.buf .r6 0 H.D) s fun t => KR (H := H) s₀ t ∧
      t.mem = writeBytes s.mem (State.addr (op s₀)) (bytesAt s.mem (T (H := H) s₀) H.D) := by
  have hD := hp.hD; have np := hp.np; have nw := hp.nw; have hf := hp.fits
  obtain ⟨sR, _, pR⟩ := wr_mem hp
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (scR sc s₀) := fun a h => t_sub hp a (Region.sub_prefix hD.2.1 a h)
  refine WP.mono (copy_ok (so := H.buf) (d := 0) (n := H.D) (by decide) (by decide) (buf_lt hp) (by decide)
    hD.1 (by omega) (by rw [hk.r11]; omega) (by rw [hk.r6]; omega)
    (fun k hk' => by
      rw [hk.r11, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) tsub (by omega) hk')
    (fun k hk' => by rw [hk.r6, add_zero', hk.wr]; exact inRegions_of_sub pR (fun _ h => h) (by omega) hk')
    (by rw [hk.r11, hk.r6, add_zero']; exact hp.p_s.symm.sub_left tsub)) fun t c => ?_
  rw [hk.r6, hk.r11, add_zero'] at c
  refine ⟨hk.keep c.rd c.wr c.sp (fun r hr => c.other r (kregs_clob r hr))
    (c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := opR (H := H) s₀) (by
      rw [bytesAt_length]; exact Region.contains_self _ _)) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.p_s.symm.sub_left (save_sub hp)), c.mem⟩

/-! ## Correctness -/

theorem correct : WP isa H.finalize s₀ fun s' => abiPreserved s₀ s' ∧ (finG hH.SH sc).post s₀ s' := by
  have hD := hp.hD; have hS := hp.hS; have hB := hp.hB
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  obtain ⟨sR, iR, pR⟩ := wr_mem hp
  have tsub : Region.Sub ⟨T (H := H) s₀, H.D⟩ (tR (H := H) s₀) := Region.sub_prefix hD.2.1
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, _, dx₁, f₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (fin1Args_ok hH hp k₁) fun t₁ ⟨kt₁, a₁, si₁, m₁⟩ =>
    finCall_ok hH hp kt₁ a₁ fun s₂ k₂ f₂ d₂ => ?_))
  refine WP.seq (WP.mono (copy1_ok hp k₂) fun s₃ ⟨k₃, m₃⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp k₃) fun t₃ ⟨kt₃, a₃, si₃, mt₃⟩ =>
    updCall_ok hH hp kt₃ a₃ fun s₄ k₄ f₄ r₄ => ?_))
  refine WP.seq (WP.seq (WP.mono (fin2Args_ok hH hp k₄) fun t₄ ⟨kt₄, a₄, si₄, mt₄⟩ =>
    finCall_ok hH hp kt₄ a₄ fun s₅ k₅ f₅ d₅ => ?_))
  refine WP.seq (WP.mono (copy2_ok hp k₅) fun s₆ ⟨k₆, m₆⟩ => ?_)
  have hL : 8 * H.W + 36 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine WP.mono (restore_ok H k₆.r11 hp.hW k₆.saved (by rw [k₆.wr]; exact sR) hL hp.nw)
    fun s' ⟨hm, _, _, hsp, hg, _⟩ =>
      ⟨⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, k₆.sp]⟩, ?_⟩
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
    · exact hp.b_o.symm
  have rO₂ := Init.repr_keep hH f₂ o₂ (m₁ ▸ Init.repr_keep hH f₁ oI hrO)
  -- The inner digest.
  have dig := d₂ _ (m₁ ▸ Init.repr_keep hH f₁ (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.i_s.sub_right (save_sub hp)) hrI)
    (by rw [hl0]; rw [hk0] at hlen; exact hlen)
    (by rw [si₁, dx₁, hcnt, hl0])
  -- The copy of the outer state.
  have rI₃ : hH.SH.Repr s₃.mem (State.addr (inn s₀)) (xorPad k0 opad) := by
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
  show bytesAt s'.mem (State.addr (op s₀)) hH.SH.digestBytes = hmacBlockKey hH.SH.H k0 text
  rw [hD', hm, m₆, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega), bytesAt_take _ _ hD.2.1, dig₂,
    bytesAt_take _ _ hD.2.1, dig]
  rfl

end

end VG.Proof.Hmac.Generic.Arm.Finalize
