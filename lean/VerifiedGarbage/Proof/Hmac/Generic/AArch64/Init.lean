import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Save

/-!
# HMAC over any streaming hash function on AArch64: `init`, correct

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/Init.lean`). The return address is in `x30`,
which each call replaces: it is saved in `scratch` with our caller's
registers, and loaded back at the end. The other callee-saved registers
we do not use (`x25`–`x29`) are kept by the calls, and never written.
-/

namespace VG.Proof.Hmac.Generic.AArch64.Init

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt sub_offset contains_offset Upd wp_mov wp_movz wp_addImm)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add bytesAt_prefix_congr inRegions_of_sub K0 K0_length
  BufMem off_disj off_disj0 covers_one sub_of_off sub_of_self bytes_keep take_map_xor)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .x0
abbrev out : Addr := s₀.gpr .x1
abbrev kp : Addr := s₀.gpr .x2
abbrev kl : Nat := (s₀.gpr .x3).toNat
abbrev scr : Addr := s₀.gpr .x4
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev stkR : Region := below s₀.sp 16
/-- The padded keys. -/
abbrev P : Addr := scr s₀ + BitVec.ofNat 64 H.buf
abbrev bufR : Region := ⟨P (H := H) s₀, 2 * H.B⟩
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  kl_le : kl s₀ ≤ H.B
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, scR sc s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (scR sc s₀)
  o_s : (outR (H := H) s₀).Disjoint (scR sc s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (scR sc s₀)
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + 2 * H.B ≤ 8 * sc
  hB : H.B ≤ 128
  hW : H.W ≤ 64
  hS : H.S ≤ 256

theorem pre_of {s₀ : State} (h : (initG hH.SH sc).pre s₀) (hfit : H.buf + 2 * H.B ≤ 8 * sc) :
    Pre (H := H) sc s₀ := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hfit, hH.hBB, hH.hW, hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem sub_sc {o n : Nat} (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; have := hp.fits; simp only [Hash.buf] at this
  exact Region.sub_prefix (by omega)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  have := hp.fits; simp only [Hash.buf] at this; exact sub_sc hp (by omega) (by omega)

theorem buf_sub : Region.Sub (bufR (H := H) s₀) (scR sc s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hB; have := hp.hW
  exact sub_offset hp.fits (by simp only [Hash.buf] at *; omega)

omit hp in
theorem padI_sub : Region.Sub ⟨P (H := H) s₀, H.B⟩ (bufR (H := H) s₀) := Region.sub_prefix (by omega)

theorem padO_sub : Region.Sub ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (bufR (H := H) s₀) :=
  sub_offset (by omega) (by have := hp.hB; omega)

include hH in
theorem cal_save : (calR hH s₀).Disjoint (saveR H (scr s₀)) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 56) (by omega) (by omega)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 56) (n := 2 * H.B) (by omega) (by omega)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 56) (b := 8 * H.W + 56) (n := 2 * H.B) (by omega) (by omega)
    (by omega)

end

/-! ## What the calls keep -/

/-- The callee-saved registers we never write. -/
abbrev untouched : List Reg := [.x25, .x26, .x27, .x28, .x29]

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = out s₀
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.x19, .x20, .x23, .x25, .x26, .x27, .x28, .x29]

theorem untouched_kregs : ∀ r ∈ untouched, r ∈ kregs := by decide
theorem untouched_clob : ∀ r ∈ untouched, r ∉ clob := by decide
theorem untouched_pro : ∀ r ∈ untouched, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x14, .x15, .x24] := by
  decide

/-- `KR` survives changes to other registers, and to memory away from the
save area. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x23,
    fun r hr => (hg r (untouched_kregs r hr)).trans (h.cs r hr),
    h.saved.frame H hf hs⟩

theorem kregs_pres : ∀ r ∈ kregs, r ∈ preserved ∧ r ≠ .x30 := by decide

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) s₀) := by
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  have hL : 8 * H.W + 56 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  have hB := hp.hB
  have hW := hp.hW
  refine WP.seq (save_ok H (scr := scr s₀) rfl hp.hW hsc hL fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_)
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_movz fun s₇ u₇ => wp_movz fun s₈ u₈ => wp_movz fun s₉ u₉ => WP.block_nil ?_
  have k₉ : ∀ r, r ∉ [Reg.x19, .x20, .x21, .x22, .x23, .x14, .x15, .x24] → s₉.gpr r = s₀.gpr r :=
    fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hr
      rw [u₉.other r h8, u₈.other r h7, u₇.other r h6, u₆.other r h5, u₅.other r h4, u₄.other r h3,
        u₃.other r h2, u₂.other r h1, g₁]
  have e : ∀ r, s₉.gpr r = s₆.gpr r ∨ r ∈ [Reg.x14, .x15, .x24] := fun r => by
    by_cases h : r ∈ [Reg.x14, .x15, .x24]
    · exact .inr h
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
      exact .inl (by rw [u₉.other r h.2.2, u₈.other r h.2.1, u₇.other r h.1])
  have e₆ : ∀ r ∈ [Reg.x19, .x20, .x21, .x22, .x23], s₉.gpr r = s₆.gpr r := fun r hr => by
    rcases e r with h | h
    · exact h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr h
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> rcases h with h | h | h <;> cases h
  have h19 : s₉.gpr .x19 = inn s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have h20 : s₉.gpr .x20 = out s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₁]
  have h21 : s₉.gpr .x21 = kp s₀ := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h22 : s₉.gpr .x22 = s₀.gpr .x3 := by
    rw [e₆ _ (by simp), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h23 : s₉.gpr .x23 = scr s₀ := by
    rw [e₆ _ (by simp), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₁]
  have h14 : s₉.gpr .x14 = (0x36 : BitVec 16).setWidth 64 := by
    rw [u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
  have h15 : s₉.gpr .x15 = (0x5c : BitVec 16).setWidth 64 := by
    rw [u₉.other _ (by decide), u₈.gpr]
  have h24 : s₉.gpr .x24 = BitVec.ofNat 64 0 := by rw [u₉.gpr]; rfl
  have hm₉ : s₉.mem = s₁.mem := by
    rw [u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₉.rd = s₀.rd := by rw [u₉.rd, u₈.rd, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₉.wr = s₀.wr := by rw [u₉.wr, u₈.wr, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hsp : s₉.sp = s₀.sp := by rw [u₉.sp, u₈.sp, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]
  have hr : LoopRegs H (P (H := H) s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨by rw [h23], h21, by rw [h22, BitVec.ofNat_toNat, BitVec.setWidth_eq], h14, h15⟩
  have hm : LoopMem H (P (H := H) s₀) (kp s₀) (kl s₀) s₉ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (s₀.gpr .x3).isLt hk |>.elim
          fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega) hk,
      hp.k_s.sub_right (buf_sub hp), hB, by simp only [Hash.buf]; omega⟩
  refine WP.seq (WP.mono (key_ok H hr hm h24) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₉.mem := hm₉ ▸ f₁
  have eK : K0 s₉.mem (kp s₀) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (by
      exact Nat.le_of_lt (s₀.gpr .x3).isLt) hi
  have hg : ∀ r ∉ clob, t.gpr r = s₉.gpr r := ht.other
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [ht.sp, hsp],
    by rw [hg _ (by decide), h19], by rw [hg _ (by decide), h20], by rw [hg _ (by decide), h23],
    fun r hr => by rw [hg r (untouched_clob r hr), k₉ r (untouched_pro r hr)],
    sv₁.frame H (hm₉ ▸ ht.mem.frame) (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)⟩,
    ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p, H.S⟩ := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.stk_i⟩
  · exact ⟨hp.o_s, hp.stk_o⟩

theorem state_in {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem kr_mov {s t : State} (hk : KR (H := H) s₀ s) {d : Reg} (hd : d ∉ kregs) {v : BitVec 64}
    (u : Upd s t d v) : KR (H := H) s₀ t :=
  hk.keep u.rd u.wr u.sp (fun r hr => u.other r fun h => hd (h ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp)

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p) :
    WP isa (.block [VG.Impl.Sha256.AArch64.Stream.mov .x0 st]) s
      fun t => KR (H := H) s₀ t ∧ t.gpr .x0 = p ∧ t.mem = s.mem :=
  wp_mov fun s₁ u₁ => WP.block_nil ⟨kr_mov hk (by decide) u₁, by rw [u₁.gpr, hs], u₁.mem⟩

/-- `KR` after a call that writes `rs`. -/
theorem kr_after {t s' : State} (hk : KR (H := H) s₀ t) {rs : List Region} (ha : After t rs s')
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) : KR (H := H) s₀ s' := by
  have f := ha.frame
  rw [hk.sp] at f
  refine hk.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (kregs_pres r hr).1 (kregs_pres r hr).2) f ?_
  simp only [List.mem_append, List.mem_singleton]
  rintro r (hr | rfl)
  · exact hs r hr
  · exact hp.stk_s.symm.sub_left (save_sub hp)

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hd : t.gpr .x0 = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] t.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine init_call hH hd (by rw [hk.wr]; exact covers_one (state_in hp hpR)) fun s' ha hr => ?_
  have f := ha.frame
  rw [hk.sp] at f
  exact hQ s' (kr_after hp hk ha (by
    simp only [List.mem_singleton]; rintro r rfl; exact dS.symm.sub_left (save_sub hp))) f hr

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (initArgs_ok hk hs) fun _ ⟨k, d, m⟩ =>
    initCall_ok hH hp k d hpR fun s' k' f r => hQ s' k' (m ▸ f) r)

/-- The arguments of `init`'s calls of `update`. -/
abbrev dO (s₀ : State) (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block ([VG.Impl.Sha256.AArch64.Stream.mov .x0 st] ++
        [.movz .x .x1 (BitVec.ofNat 16 0) 0, .addImm .x .x2 .x23 o, .movz .x .x3 (BitVec.ofNat 16 H.B) 0,
          VG.Impl.Sha256.AArch64.Stream.mov .x4 .x23])) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ t.gpr .x1 = 0 ∧ t.mem = s.mem := by
  obtain ⟨dS, dK⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o < 4096 := by omega
  have dsub : Region.Sub ⟨dO s₀ o, H.B⟩ (bufR (H := H) s₀) := by
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [dO, ← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨dO s₀ o, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_movz fun s₂ u₂ => wp_addImm ho' fun s₃ u₃ => wp_movz fun s₄ u₄ =>
    wp_mov fun s₅ u₅ => WP.block_nil ?_
  have k₅ : KR (H := H) s₀ s₅ :=
    kr_mov (kr_mov (kr_mov (kr_mov (kr_mov hk (by decide) u₁) (by decide) u₂) (by decide) u₃)
      (by decide) u₄) (by decide) u₅
  have h23 : s.gpr .x23 = scr s₀ := hk.x23
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₅, ?_, by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl,
    hm⟩
  exact
    { x0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.gpr, hs]
      x2 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
          u₁.other _ (by decide), h23]
      x3 := by rw [u₅.other _ (by decide), u₄.gpr, movz_ofNat (by omega), toNat_ofNat_lt (by omega)]
      x4 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
          u₁.other _ (by decide), h23]
      cd := by
        rw [k₅.rd, k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.wr]; simp) (by omega)
      cw := by
        rw [k₅.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      sp16 := by rw [k₅.sp]; exact hp.sp16
      stk_st := by rw [k₅.sp]; exact dK
      stk_d := by rw [k₅.sp]; exact hp.stk_s.sub_right dsc
      stk_sc := by rw [k₅.sp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : Addr} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hx1 : t.gpr .x1 = 0) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt t.mem d H.B)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨dS, _⟩ := state_disj hp hpR
  refine upd_call hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.sp] at f
  refine hQ s' (kr_after hp hk ha' ?_) f fun hr => hpost [] hr (by rw [hx1]; rfl)
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact dS.symm.sub_left (save_sub hp)
  · exact (cal_save hH hp).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt s.mem (scr s₀ + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [VG.Impl.Sha256.AArch64.Stream.mov .x0 st] 0 o H.B) s Q :=
  WP.seq (WP.mono (updArgs_ok hH hp hk hs hpR ho) fun _ ⟨k, a, x1, m⟩ =>
    updCall_ok hH hp k hpR a x1 fun s' k' f r => hQ s' k' (m ▸ f) (m ▸ r))

/-! ## Correctness -/

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.Common.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega,
    ↓reduceIte]

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
    hp.stk_s.symm.sub_left fun a h => buf_sub hp a (padI_sub a h)
  have dOK : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (stkR s₀) :=
    hp.stk_s.symm.sub_left fun a h => buf_sub hp a (padO_sub hp a h)
  have dOC : Region.Disjoint ⟨P (H := H) s₀ + BitVec.ofNat 64 H.B, H.B⟩ (calR hH s₀) :=
    (cal_buf hH hp).symm.sub_left (padO_sub hp)
  have eO : scr s₀ + BitVec.ofNat 64 (H.buf + H.B) = P (H := H) s₀ + BitVec.ofNat 64 H.B := by
    rw [P, add_ofNat_add]
  refine WP.seq (WP.mono (keys_ok sc hp) fun s₁ h₁ => ?_)
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .x19) h₁.kr.x19 (.inl rfl) fun s₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ k₂.x19 (.inl rfl) (.inl rfl) fun s₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> assumption)
    (by omega)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .x20) k₃.x20 (.inr rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.stk_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ k₄.x20 (.inr rfl) (.inr rfl) fun s₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.stk_i.symm) rI₄
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₅.x23 hW k₅.saved hsc (by omega)) fun s' ⟨hm, _, _, hsp, hg, ho⟩ => ?_
  refine ⟨abi_of k₅ hsp hg ho, ?_⟩
  show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
  rw [hm, blockKey_eq hH hp]
  exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.AArch64.Init
