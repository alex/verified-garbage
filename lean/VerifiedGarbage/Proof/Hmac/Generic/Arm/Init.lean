import VerifiedGarbage.Proof.Hmac.Generic.Arm.Save
import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Init

/-!
# HMAC over any streaming hash function on 32-bit ARM: `init`, correct

Untrusted: everything here is checked by Lean. As on AArch64
(`Proof/Hmac/Generic/AArch64/Init.lean`). `scratch` is a stack argument,
loaded into `r12` first; every callee-saved register (and `lr`) is saved in
it, and loaded back at the end. The functions we call keep `r4`–`r11`, which
hold our variables.
-/

namespace VG.Proof.Hmac.Generic.Arm.Init

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Sha256.X86_64 (contains_offset)
open VG.Proof.MdStream.Arm (Upd Fupd wp_mov wp_add wp_cmp wp_ldrSp op2_imm op2_reg sub_offset
  ofNat_beq_zero)
open VG.Proof.Hmac.Generic.X86_64 (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length)
open VG.Proof.Hmac.Generic.X86_64.Init (off_disj off_disj0 sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : BitVec 32 := s₀.gpr .r0
abbrev out : BitVec 32 := s₀.gpr .r1
abbrev kp : BitVec 32 := s₀.gpr .r2
abbrev kl : Nat := (s₀.gpr .r3).toNat
abbrev scr : BitVec 32 := stackArg s₀ 0
abbrev inR : Region := ⟨State.addr (inn s₀), H.S⟩
abbrev outR : Region := ⟨State.addr (out s₀), H.S⟩
abbrev keyR : Region := ⟨State.addr (kp s₀), kl s₀⟩
abbrev scR : Region := ⟨State.addr (scr s₀), 8 * sc⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
abbrev stkR : Region := below s₀
/-- The padded keys. -/
abbrev P : Addr := State.addr (scr s₀) + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨State.addr (scr s₀), hH.Wb⟩
/-- Byte `o` of `scratch`, as a register holds it. -/
abbrev dO (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

end

theorem kl_lt (s₀ : State) : kl s₀ < 2 ^ 32 := (s₀.gpr .r3).isLt

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (scR sc s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_s : (stkR s₀).Disjoint (scR sc s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, _, _, h8, h9, h10, h11, h12, h13, _, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h15, h16, h17, h18, h19, h20, h21, hfit, hH.hBB,
    hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) :
    Region.Sub ⟨State.addr (scr s₀) + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
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
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W) (n := 36) (by omega) (by omega)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.hW; have := hp.hB
  exact off_disj0 _ (m := hH.Wb) (b := 8 * H.W + 36) (n := 2 * H.B) (by omega) (by omega)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.hW; have := hp.hB
  exact off_disj _ (a := 8 * H.W) (m := 36) (b := 8 * H.W + 36) (n := 2 * H.B) (by omega) (by omega)
    (by omega)

theorem addr_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) :
    State.addr (dO s₀ o) = State.addr (scr s₀) + BitVec.ofNat 64 o :=
  addr_add (by have := hp.nw; omega)

theorem toNat_dO {o : Nat} (ho : o + 1 ≤ 8 * sc) : (dO s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = out s₀
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.r4, .r5, .r11]

/-- `KR` survives changes to other registers, and to memory away from the
save area. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r11, h.saved.frame H hf hs⟩

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem (State.addr (kp s₀)) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) s₀) := by
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf
  have hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  refine WP.seq ?_
  simp only [Hash.initPrologue, List.singleton_append]
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl (by rw [hp.rd]; exact ⟨argR s₀, by simp,
    Region.contains_self _ _⟩) fun s₁ u₁ => ?_
  refine save_ok H (scr := scr s₀) u₁.gpr hW (by rw [u₁.wr]; exact hsc) (by omega) (by omega)
    fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_imm (by decide)) fun s₇ u₇ => wp_mov (op2_reg _ _) fun s₈ u₈ =>
    wp_cmp (op2_imm (by decide)) fun s₉ f₉ z₉ => WP.block_nil ?_
  have e₂ : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r hr => by rw [g₂, u₁.other r hr]
  have h4 : s₉.gpr .r4 = inn s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, e₂ _ (by decide)]
  have h5 : s₉.gpr .r5 = out s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.gpr, u₃.other _ (by decide), e₂ _ (by decide)]
  have h6 : s₉.gpr .r6 = kp s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr,
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide)]
  have h11 : s₉.gpr .r11 = scr s₀ := by
    rw [f₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.gpr]; rfl
  have h8 : s₉.gpr .r8 = BitVec.ofNat 32 0 := by rw [f₉.gpr, u₈.other _ (by decide), u₇.gpr]; rfl
  have h9 : s₉.gpr .r9 = BitVec.ofNat 32 (kl s₀) := by
    rw [f₉.gpr, u₈.gpr, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.other _ (by decide), e₂ _ (by decide), BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hz : s₉.z = decide (kl s₀ = 0) := by
    have h9' : s₈.gpr .r9 = BitVec.ofNat 32 (kl s₀) := by rw [← f₉.gpr]; exact h9
    rw [z₉, h9', show ∀ x : BitVec 32, x - 0 = x from fun x => BitVec.sub_zero x,
      ofNat_beq_zero (s₀.gpr .r3).isLt]
  have hm₉ : s₉.mem = s₂.mem := by rw [f₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have hrd : s₉.rd = s₀.rd := by rw [f₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd]
  have hwr : s₉.wr = s₀.wr := by rw [f₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr]
  have hsp : s₉.sp = s₀.sp := by rw [f₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp]
  have hr : LoopRegs (scr s₀) (kp s₀) s₉ := ⟨h11, h6⟩
  have hm : LoopMem H (scr s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (Nat.lt_trans (kl_lt s₀) (by decide))
          hk |>.elim fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by
        rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega, by simp only [Hash.buf]; omega,
      hp.nk⟩
  refine WP.seq (WP.mono (key_ok H hr hm h8 h9 hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₉.mem := by rw [hm₉, ← u₁.mem]; exact f₂
  have eK : K0 s₉.mem (State.addr (kp s₀)) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (Nat.le_of_lt (Nat.lt_trans (kl_lt s₀) (by decide))) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₉.gpr r := ht.other
  have sv : SavedRegs H (scr s₀) s₀ s₉.mem := hm₉ ▸ sv₂.of_eq H fun r hr => u₁.other r (by
    simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [ht.sp, hsp],
    by rw [hg _ (by decide), h4], by rw [hg _ (by decide), h5], by rw [hg _ (by decide), h11],
    sv.frame H ht.mem.frame (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)⟩,
    ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨State.addr p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨State.addr p, H.S⟩ ∧
      p.toNat + H.S ≤ 2 ^ 32 := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.b_i, hp.ni⟩
  · exact ⟨hp.o_s, hp.b_o, hp.no⟩

theorem state_in {p : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨State.addr p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem kr_mov {s t : State} (hk : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 32}
    (u : Upd s t d v) : KR (H := H) s₀ t :=
  hk.keep u.rd u.wr u.sp (fun r hr => u.other r fun h => hd (h ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

/-- `KR` after a call that writes `rs`. -/
theorem kr_after {t s' : State} (hk : KR (H := H) s₀ t) {rs : List Region} (ha : After t rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [below_eq hk.sp] at f
  refine hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
  simp only [List.mem_append, List.mem_singleton]
  rintro r (hr | rfl)
  · exact hs r hr
  · exact hp.b_s.symm.sub_left (save_sub hp)

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32} (hs : s.gpr st = p) :
    WP isa (.block [.mov .r0 (.reg st)]) s fun t => KR (H := H) s₀ t ∧ t.gpr .r0 = p ∧ t.mem = s.mem :=
  wp_mov (op2_reg _ _) fun _ u₁ => WP.block_nil ⟨kr_mov hk (by decide) u₁, by rw [u₁.gpr, hs], u₁.mem⟩

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : BitVec 32} (hd : t.gpr .r0 = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, stkR s₀] t.mem s'.mem →
      hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _, np⟩ := state_disj hp hpR
  refine init_call hH hd np (by rw [hk.wr]; exact covers_one (state_in hp hpR)) fun s' ha hr => ?_
  have f := ha.frame
  rw [below_eq hk.sp] at f
  exact hQ s' (kr_after hp hk ha (by
    simp only [List.mem_singleton]; rintro r rfl; exact dS.symm.sub_left (save_sub hp))) f hr

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, stkR s₀] s.mem s'.mem →
      hH.SH.Repr s'.mem (State.addr p) [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (initArgs_ok hk hs) fun _ ⟨k, d, m⟩ =>
    initCall_ok hH hp k d hpR fun s' k' f r => hQ s' k' (m ▸ f) r)

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block ([.mov .r0 (.reg st)] ++ scrAt .r1 o ++ [.movw .r7 (BitVec.ofNat 16 H.B),
        .mov .r10 (.reg .r11), .movw .r2 (BitVec.ofNat 16 0), .mov .r3 (.imm 0)])) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ count t = BitVec.ofNat 64 0 ∧
        t.mem = s.mem := by
  obtain ⟨dS, dK, np⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o + H.B ≤ 8 * sc := by omega
  have ea := addr_dO hp (o := o) (by omega)
  have dsub : Region.Sub ⟨State.addr (dO s₀ o), H.B⟩ (bufR (H := H) s₀) := by
    rw [ea]
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨State.addr (dO s₀ o), H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_movw fun s₂ u₂ => wp_add (op2_reg _ _) fun s₃ u₃ =>
    wp_movw fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ => wp_movw fun s₆ u₆ =>
    wp_mov (op2_imm (by decide)) fun s₇ u₇ => WP.block_nil ?_
  have k₇ : KR (H := H) s₀ s₇ :=
    kr_mov (kr_mov (kr_mov (kr_mov (kr_mov (kr_mov (kr_mov hk (by decide) u₁) (by decide) u₂) (by decide) u₃)
      (by decide) u₄) (by decide) u₅) (by decide) u₆) (by decide) u₇
  have h11 : s.gpr .r11 = scr s₀ := hk.r11
  have hm : s₇.mem = s.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₇, ?_, count_movw (c := 0) (by decide) (by rw [u₇.other _ (by decide), u₆.gpr]) u₇.gpr, hm⟩
  exact
    { r0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs]
      r1 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h11,
          movw_ofNat (by omega)]
      r7 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
          movw_ofNat (by omega)]
      r10 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), h11]
      hlen := by omega
      sp16 := by rw [k₇.sp]; exact hp.sp16
      cd := by
        rw [k₇.rd, k₇.wr, ea]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.rd, hp.wr]; simp) ho'
      cw := by
        rw [k₇.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨State.addr p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      b_st := by rw [below_eq k₇.sp]; exact dK
      b_d := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right dsc
      b_sc := by rw [below_eq k₇.sp]; exact hp.b_s.sub_right (cal_sub hH hp)
      nst := np
      nd := by rw [toNat_dO hp (by omega)]; omega
      nsc := by have := hH.hWb; omega }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : BitVec 32} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hc : count t = BitVec.ofNat 64 0) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem (State.addr p) [] →
        hH.SH.Repr s'.mem (State.addr p) ([] ++ bytesAt t.mem (State.addr d) H.B)) → Q s') :
    WP isa (.frame (.push upd4) (.call H.updN H.updC) (.pop .r1 16)) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine upd_frame hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [below_eq hk.sp] at f
  refine hQ s' (kr_after hp hk ha' ?_) f fun hr => hpost [] hr (by rw [hc]; rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact dS.symm.sub_left (save_sub hp)
  · exact (cal_save hH hp).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : BitVec 32}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨State.addr p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem (State.addr p) [] →
        hH.SH.Repr s'.mem (State.addr p) ([] ++ bytesAt s.mem (State.addr (scr s₀) + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [.mov .r0 (.reg st)] 0 o H.B) s Q := by
  have hf := hp.fits; have := hp.hB; have ho' := ho; simp only [Hash.buf] at hf ho'
  have ea := addr_dO hp (o := o) (by omega)
  exact WP.seq (WP.mono (updArgs_ok hH hp hk hs hpR ho) fun t ⟨k, a, c, m⟩ =>
    updCall_ok hH hp k hpR a c fun s' k' f r => hQ s' k' (m ▸ f) fun hr => by
      have := r (m ▸ hr); rwa [m, ea] at this)

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.X86_64.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega,
    ↓reduceIte]

omit hp in
/-- The end: `abiPreserved`, from `KR` and `restore`. -/
theorem abi_of {s s' : State} (hk : KR (H := H) s₀ s) (hsp : s'.sp = s.sp)
    (hg : ∀ r ∈ savedRegs, s'.gpr r = s₀.gpr r) : abiPreserved s₀ s' :=
  ⟨fun r hr => hg r (preserved_saved r hr), by rw [hsp, hk.sp]⟩

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
  have eO : State.addr (scr s₀) + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .r4) h₁.kr.r4 (.inl rfl) fun s₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ k₂.r4 (.inl rfl) (.inl rfl) fun s₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> assumption)
    (by omega)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .r5) k₃.r5 (.inr rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.b_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ k₄.r5 (.inr rfl) (.inr rfl) fun s₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.b_i.symm) rI₄
  have hsc : ⟨State.addr (scr s₀), 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₅.r11 hW k₅.saved hsc (by omega) hp.nw) fun s' ⟨hm, _, _, hsp, hg, _⟩ => ?_
  refine ⟨abi_of k₅ hsp hg, ?_⟩
  show hH.SH.Repr s'.mem (State.addr (inn s₀)) _ ∧ hH.SH.Repr s'.mem (State.addr (out s₀)) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.Arm.Init
