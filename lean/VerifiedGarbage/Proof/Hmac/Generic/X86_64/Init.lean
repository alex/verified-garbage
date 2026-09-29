import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Save

/-!
# HMAC over any streaming hash function on x86-64: `init`, correct

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Hmac.Generic.X86_64.Init

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi wp_test)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

/-- Parts of a region at offsets `a` and `b` do not overlap. -/
theorem off_disj (p : Addr) {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m < 2 ^ 64)
    (hb : b + n < 2 ^ 64) :
    Region.Disjoint ⟨p + BitVec.ofNat 64 a, m⟩ ⟨p + BitVec.ofNat 64 b, n⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

/-- The start of a region and a part of it at offset `b`. -/
theorem off_disj0 (p : Addr) {m b n : Nat} (h : m ≤ b) (hb : b + n < 2 ^ 64) :
    Region.Disjoint ⟨p, m⟩ ⟨p + BitVec.ofNat 64 b, n⟩ := by
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev inn : Addr := s₀.gpr .rdi
abbrev out : Addr := s₀.gpr .rsi
abbrev kp : Addr := s₀.gpr .rdx
abbrev kl : Nat := (s₀.gpr .rcx).toNat
abbrev scr : Addr := s₀.gpr .r8
abbrev inR : Region := ⟨inn s₀, H.S⟩
abbrev outR : Region := ⟨out s₀, H.S⟩
abbrev keyR : Region := ⟨kp s₀, kl s₀⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
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
  ret_i : (retR s₀).Disjoint (inR (H := H) s₀)
  ret_o : (retR s₀).Disjoint (outR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
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
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  have hB := hH.hB
  simp only [hS, hB] at *
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit, hH.hBB, hH.hW,
    hH.hSB⟩

/-! ## The parts of `scratch` -/

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem buf_le : H.buf + 2 * H.B ≤ 8 * sc := hp.fits

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
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W) (n := 48) (by omega) (by omega)

include hH in
theorem cal_buf : (calR hH s₀).Disjoint (bufR (H := H) s₀) := by
  have := hH.hWb; have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj0 (scr s₀) (m := hH.Wb) (b := 8 * H.W + 48) (n := 2 * H.B) (by omega) (by omega)

theorem save_buf : (saveR H (scr s₀)).Disjoint (bufR (H := H) s₀) := by
  have := hp.fits; have := hp.nw; have := hp.hW; have := hp.hB; simp only [Hash.buf] at *
  exact off_disj (scr s₀) (a := 8 * H.W) (m := 48) (b := 8 * H.W + 48) (n := 2 * H.B) (by omega) (by omega)
    (by omega)

omit hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

end

/-! ## What the calls keep -/

/-- The registers and memory kept from the prologue on. -/
structure KR (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = out s₀
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64

/-- `KR` survives changes to other registers, and to memory away from the
save area and the return address. -/
theorem KR.keep {s₀ s s' : State} (h : KR (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ [Reg.rsp, .rbx, .r12, .r15], s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hr : ∀ r ∈ rs, (retR s₀).Disjoint r) : KR (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r15, h.saved.frame H hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret⟩

/-! ## The keys -/

/-- The key padded to a block, from the initial memory. -/
abbrev K0₀ (s₀ : State) : List Byte := K0 s₀.mem (kp s₀) (kl s₀) H.B

/-- After `initKeys`. -/
structure PhK (s₀ s : State) : Prop where
  kr : KR (H := H) s₀ s
  bufI : bytesAt s.mem (P (H := H) s₀) H.B = xorPad (K0₀ (H := H) s₀) ipad
  bufO : bytesAt s.mem (P (H := H) s₀ + BitVec.ofNat 64 H.B) H.B = xorPad (K0₀ (H := H) s₀) opad

theorem take_map_xor {K : List Byte} {n : Nat} (h : K.length = n) (p : Byte) :
    (K.take n).map (· ^^^ p) = xorPad K p := by
  rw [List.take_of_length_le (by omega)]; rfl

theorem keys_ok {s₀ : State} (hp : Pre (H := H) sc s₀) : WP isa H.initKeys s₀ (PhK (H := H) s₀) := by
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₀.wr := by rw [hp.wr]; simp
  have hL : 8 * H.W + 48 ≤ 8 * sc := by have := hp.fits; simp only [Hash.buf] at this; omega
  refine WP.seq (save_ok H (scr := scr s₀) rfl hp.hW hsc hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_)
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov32i fun s₇ u₇ _ _ => wp_test fun s₈ g₈ m₈ rd₈ wr₈ z₈ => WP.block_nil ?_
  have k₈ : ∀ r, r ∉ [Reg.rbx, .r12, .r15, .rbp, .r13, .r14] → s₈.gpr r = s₀.gpr r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [g₈, u₇.other r hr.2.2.2.2.2, u₆.other r hr.2.2.2.2.1, u₅.other r hr.2.2.2.1, u₄.other r hr.2.2.1,
      u₃.other r hr.2.1, u₂.other r hr.1, g₁]
  have r8 : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → ∀ t : State,
      (∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s₈.gpr r) → t.gpr r = s₈.gpr r :=
    fun r _ _ _ t h => h r ‹_› ‹_› ‹_›
  have hbx : s₈.gpr .rbx = inn s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₁]
  have h12 : s₈.gpr .r12 = out s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₁]
  have h15 : s₈.gpr .r15 = scr s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have hbp : s₈.gpr .rbp = kp s₀ := by
    rw [g₈, u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have h13 : s₈.gpr .r13 = s₀.gpr .rcx := by
    rw [g₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁]
  have h14 : s₈.gpr .r14 = BitVec.ofNat 64 0 := by rw [g₈, u₇.gpr]; rfl
  have hm₈ : s₈.mem = s₁.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have hrd : s₈.rd = s₀.rd := by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]
  have hwr : s₈.wr = s₀.wr := by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁]
  have hz : s₈.zf = some (decide (kl s₀ = 0)) := by
    rw [z₈, u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₁, BitVec.and_self]
    congr 1
    by_cases h : kl s₀ = 0
    · simp [h, BitVec.eq_of_toNat_eq (show (s₀.gpr .rcx).toNat = (0 : BitVec 64).toNat from h)]
    · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
      intro h'; exact h (by show (s₀.gpr .rcx).toNat = 0; rw [h']; rfl)
  have hB := hp.hB
  have hr : LoopRegs H (P (H := H) s₀) (kp s₀) (kl s₀) s₈ :=
    ⟨by rw [h15], hbp, by rw [h13, BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
  have hm : LoopMem H (P (H := H) s₀) (kp s₀) (kl s₀) s₈ :=
    ⟨hp.kl_le, fun k hk => by
        rw [hrd, hwr, hp.rd]
        exact inRegions_of_sub (R := keyR s₀) (by simp) (fun _ h => h) (s₀.gpr .rcx).isLt hk |>.elim
          fun r ⟨hr, hc⟩ => ⟨r, List.mem_append_left _ hr, hc⟩,
      fun k hk => by rw [hwr, hp.wr]; exact inRegions_of_sub (R := scR sc s₀) (by simp) (buf_sub hp) (by omega) hk,
      hp.k_s.sub_right (buf_sub hp), hB⟩
  refine WP.seq (WP.mono (key_ok H hr hm h14 hz) fun t ht => pad_ok H hr hm ht) |>.mono fun t ht => ?_
  -- The key's bytes are those of the initial memory.
  have fk : Frame [saveR H (scr s₀)] s₀.mem s₈.mem := hm₈ ▸ f₁
  have eK : K0 s₈.mem (kp s₀) (kl s₀) H.B = K0₀ (H := H) s₀ := by
    simp only [K0, K0₀]
    congr 1
    refine bytesAt_prefix_congr fun i hi => fk.bytes (R := keyR s₀) (by
      simp only [List.mem_singleton]; rintro r rfl; exact (hp.k_s.sub_right (save_sub hp))) (by
      exact (s₀.gpr .rcx).isLt.le) hi
  have ft : Frame [saveR H (scr s₀), bufR (H := H) s₀] s₀.mem t.mem :=
    (fk.mono (by simp)).trans (ht.mem.frame.mono (by simp))
  have hg : ∀ r, r ≠ .rax → r ≠ .rcx → r ≠ .r14 → t.gpr r = s₈.gpr r := ht.other
  refine ⟨⟨by rw [ht.rd, hrd], by rw [ht.wr, hwr], by rw [hg _ (by decide) (by decide) (by decide),
      k₈ _ (by simp)], by rw [hg _ (by decide) (by decide) (by decide), hbx],
    by rw [hg _ (by decide) (by decide) (by decide), h12], by rw [hg _ (by decide) (by decide) (by decide), h15],
    (sv₁.frame H (hm₈ ▸ ht.mem.frame) (by simp only [List.mem_singleton]; rintro r rfl; exact save_buf hp)),
    ft.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl)
      · exact hp.ret_s.sub_right (save_sub hp)
      · exact hp.ret_s.sub_right (buf_sub hp)) (by decide)⟩, ?_, ?_⟩
  · rw [ht.mem.bufI, eK, take_map_xor (K0_length _ _ hp.kl_le)]
  · rw [ht.mem.bufO, eK, take_map_xor (K0_length _ _ hp.kl_le)]

/-! ## The calls -/

theorem covers_one {rs : List Region} {r : Region} (h : r ∈ rs) : Covers [r] rs :=
  Covers.of_sub fun r' hr' => by
    simp only [List.mem_singleton] at hr'
    exact ⟨r, h, 0, by rw [hr']; simp, by rw [hr']; simp⟩

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem state_disj {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Region.Disjoint ⟨p, H.S⟩ (scR sc s₀) ∧ (stkR s₀).Disjoint ⟨p, H.S⟩ ∧ (retR s₀).Disjoint ⟨p, H.S⟩ := by
  rcases hpR with rfl | rfl
  · exact ⟨hp.i_s, hp.stk_i, hp.ret_i⟩
  · exact ⟨hp.o_s, hp.stk_o, hp.ret_o⟩

theorem state_in {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) : ⟨p, H.S⟩ ∈ s₀.wr := by
  rw [hp.wr]; rcases hpR with rfl | rfl <;> simp

omit hp in
theorem initArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p) :
    WP isa (.block [.mov .rdi (.reg st)]) s fun t => KR (H := H) s₀ t ∧ t.gpr .rdi = p ∧ t.mem = s.mem :=
  wp_mov fun s₁ u₁ _ _ => WP.block_nil ⟨hk.keep (by rw [u₁.rd]) (by rw [u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact u₁.other _ (by decide))
    (rs := []) (by rw [u₁.mem]; exact Frame.refl _ _) (by simp) (by simp), by rw [u₁.gpr, hs], u₁.mem⟩

/-- The regions of `init`'s call, from `KR`. -/
theorem initCall_args {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hpR : p = inn s₀ ∨ p = out s₀) :
    Covers [⟨p, H.S⟩] t.wr ∧ (below (t.gpr .rsp) 16).Disjoint ⟨p, H.S⟩ := by
  obtain ⟨_, dK, _⟩ := state_disj hp hpR
  exact ⟨by rw [hk.wr]; exact covers_one (state_in hp hpR), by rw [hk.rsp]; exact dK⟩

theorem initCall_ok {t : State} (hk : KR (H := H) s₀ t) {p : Addr} (hd : t.gpr .rdi = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] t.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (.call H.initN H.initC) t Q := by
  obtain ⟨dS, _, dR⟩ := state_disj hp hpR
  obtain ⟨c, k⟩ := initCall_args hp hk hpR
  refine init_call hH hd c k fun s' ha hr => ?_
  have f := ha.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_ ?_) f hr
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact (dS.symm.sub_left (save_sub hp))
    · exact (hp.stk_s.symm.sub_left (save_sub hp))
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact dR
    · exact (stk_ret (s₀ := s₀)).symm

theorem callInit_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} {p : Addr} (hs : s.gpr st = p)
    (hpR : p = inn s₀ ∨ p = out s₀) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, stkR s₀] s.mem s'.mem → hH.SH.Repr s'.mem p [] → Q s') :
    WP isa (H.callInit st) s Q :=
  WP.seq (WP.mono (initArgs_ok hk hs) fun _ ⟨k, d, m⟩ =>
    initCall_ok hH hp k d hpR fun s' k' f r => hQ s' k' (m ▸ f) r)

omit hp in
theorem sub_of_off {rs : List Region} {base : Addr} {L : Nat} (h : ⟨base, L⟩ ∈ rs) {o n : Nat}
    (hn : o + n ≤ L) : ∃ r' ∈ rs, ∃ off, (⟨base + BitVec.ofNat 64 o, n⟩ : Region).base =
      r'.base + BitVec.ofNat 64 off ∧ off + (⟨base + BitVec.ofNat 64 o, n⟩ : Region).len ≤ r'.len :=
  ⟨_, h, o, rfl, hn⟩

omit hp in
theorem sub_of_self {rs : List Region} {r : Region} (h : r ∈ rs) {n : Nat} (hn : n ≤ r.len) :
    ∃ r' ∈ rs, ∃ off, (⟨r.base, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨r.base, n⟩ : Region).len ≤ r'.len :=
  ⟨r, h, 0, by simp, by simpa using hn⟩

/-- The arguments of `init`'s calls of `update`. -/
abbrev dO (s₀ : State) (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o

theorem updArgs_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} (hst : st = .rbx ∨ st = .r12) {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B) :
    WP isa (.block ([.mov .rdi (.reg st)] ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 0))] ++
        VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++
        [.mov32 .rcx (.imm (BitVec.ofNat 32 H.B)), .mov .r8 (.reg .r15)])) s fun t =>
      KR (H := H) s₀ t ∧ UpdArgs hH t p (dO s₀ o) (scr s₀) H.B ∧ t.gpr .rsi = 0 ∧ t.mem = s.mem := by
  obtain ⟨dS, dK, _⟩ := state_disj hp hpR
  have hB := hp.hB; have hW := hp.hW; have hf := hp.fits; have nw := hp.nw
  simp only [Hash.buf] at hf ho
  have ho' : o < 2 ^ 31 := by omega
  have dsub : Region.Sub ⟨dO s₀ o, H.B⟩ (bufR (H := H) s₀) := by
    rcases ho with rfl | rfl
    · exact padI_sub
    · rw [dO, ← add_ofNat_add]; exact padO_sub hp
  have dsc : Region.Sub ⟨dO s₀ o, H.B⟩ (scR sc s₀) := fun a h => buf_sub hp a (dsub a h)
  have hstr : st ≠ .rdi ∧ st ≠ .rsi ∧ st ≠ .rdx ∧ st ≠ .rcx ∧ st ≠ .r8 := by
    rcases hst with rfl | rfl <;> decide
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov32i fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_addi fun s₄ u₄ =>
    wp_mov32i fun s₅ u₅ _ _ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have g : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → s₆.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₆.other r h5, u₅.other r h4, u₄.other r h3, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  have hsp : s₆.gpr .rsp = s₀.gpr .rsp := by rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), hk.rsp]
  have h15 : s.gpr .r15 = scr s₀ := hk.r15
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have k₆ : KR (H := H) s₀ s₆ := hk.keep (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> exact g _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)
  refine ⟨k₆, ?_, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr]; rfl, hm⟩
  exact
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, hs]
      rdx := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr,
          u₂.other _ (by decide), u₁.other _ (by decide), h15, sx_ofNat ho']
      rcx := by rw [u₆.other _ (by decide), u₅.gpr, zx_ofNat (by omega), toNat_ofNat_lt (by omega)]
      r8 := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), h15]
      cd := by
        rw [k₆.rd, k₆.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (L := 8 * sc) (by rw [hp.wr]; simp) (by omega)
      cw := by
        rw [k₆.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_self (r := ⟨p, H.S⟩) (state_in hp hpR) (Nat.le_refl _)
          · exact sub_of_self (r := scR sc s₀) (by rw [hp.wr]; simp) (by
              have := hH.hWb; show hH.Wb ≤ 8 * sc; omega)
      st_sc := dS.sub_right (cal_sub hH hp)
      d_st := dS.symm.sub_left dsc
      d_sc := (cal_buf hH hp).symm.sub_left dsub
      stk_st := by rw [hsp]; exact dK
      stk_d := by rw [hsp]; exact hp.stk_s.sub_right dsc
      stk_sc := by rw [hsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {t : State} (hk : KR (H := H) s₀ t) {p d : Addr} (hpR : p = inn s₀ ∨ p = out s₀)
    (ha : UpdArgs hH t p d (scr s₀) H.B) (hsi : t.gpr .rsi = 0) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (hH.SH.Repr t.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt t.mem d H.B)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨dS, _, dR⟩ := state_disj hp hpR
  have hB := hp.hB
  refine upd_call hH ha (by omega) fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.keep ha'.rd ha'.wr (fun r hr => ha'.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_ ?_) f
    fun hr => hpost [] hr (by rw [hsi]; rfl)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact dS.symm.sub_left (save_sub hp)
    · exact (cal_save hH hp).symm
    · exact hp.stk_s.symm.sub_left (save_sub hp)
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact dR
    · exact hp.ret_s.sub_right (cal_sub hH hp)
    · exact (stk_ret (s₀ := s₀)).symm

theorem callUpd_ok {s : State} (hk : KR (H := H) s₀ s) {st : Reg} (hst : st = .rbx ∨ st = .r12) {p : Addr}
    (hs : s.gpr st = p) (hpR : p = inn s₀ ∨ p = out s₀) {o : Nat} (ho : o = H.buf ∨ o = H.buf + H.B)
    {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) s₀ s' → Frame [⟨p, H.S⟩, calR hH s₀, stkR s₀] s.mem s'.mem →
      (hH.SH.Repr s.mem p [] → hH.SH.Repr s'.mem p ([] ++ bytesAt s.mem (scr s₀ + BitVec.ofNat 64 o) H.B)) →
      Q s') :
    WP isa (H.callUpd [.mov .rdi (.reg st)] 0 o H.B) s Q :=
  WP.seq (WP.mono (updArgs_ok hH hp hk hst hs hpR ho) fun _ ⟨k, a, si, m⟩ =>
    updCall_ok hH hp k hpR a si fun s' k' f r => hQ s' k' (m ▸ f) (m ▸ r))

/-! ## Memory kept by the calls -/

omit hp in
theorem bytes_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {n : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, n⟩ r) (hn : n ≤ 2 ^ 64) : bytesAt m' p n = bytesAt m p n :=
  bytesAt_prefix_congr fun _ hi => hf.bytes (R := ⟨p, n⟩) hd hn hi

omit hp in
include hH in
theorem repr_keep {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨p, H.S⟩ r) {msg : List Byte} (hr : hH.SH.Repr m p msg) :
    hH.SH.Repr m' p msg :=
  hH.repr _ _ _ _ _ (fun i hi => hf.bytes (R := ⟨p, H.S⟩) hd (by show H.S ≤ 2 ^ 64; have := hH.hSB; omega) hi) hr

theorem blockKey_eq : blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀)) = K0₀ (H := H) s₀ := by
  have := hp.kl_le
  have hb := hH.hB
  simp only [blockKey, K0₀, K0, Proof.Hmac.X86_64.bytesAt_length, hb, show ¬ (H.B < kl s₀) by omega,
    ↓reduceIte]

/-! ## Correctness -/

theorem correct :
    WP isa H.init s₀ fun s' => gprPreserved s₀ s' ∧ (initG hH.SH sc).post s₀ s' := by
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
  refine WP.seq (callInit_ok hH hp h₁.kr (st := .rbx) h₁.kr.rbx (.inl rfl) fun s₂ k₂ f₂ r₂ => ?_)
  have bI₂ := (bytes_keep f₂ (p := P (H := H) s₀) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufI
  have bO₂ := (bytes_keep f₂ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans h₁.bufO
  refine WP.seq (callUpd_ok hH hp k₂ (.inl rfl) k₂.rbx (.inl rfl) (.inl rfl) fun s₃ k₃ f₃ r₃ => ?_)
  have rI₃ := r₃ r₂
  rw [List.nil_append, bI₂] at rI₃
  have bO₃ := (bytes_keep f₃ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl | rfl) <;> assumption)
    (by omega)).trans bO₂
  refine WP.seq (callInit_ok hH hp k₃ (st := .r12) k₃.r12 (.inr rfl) fun s₄ k₄ f₄ r₄ => ?_)
  have rI₄ := repr_keep hH f₄ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.i_o
    · exact hp.stk_i.symm) rI₃
  have bO₄ := (bytes_keep f₄ (p := P (H := H) s₀ + BitVec.ofNat 64 H.B) (n := H.B) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro r (rfl | rfl) <;> assumption)
    (by omega)).trans bO₃
  refine WP.seq (callUpd_ok hH hp k₄ (.inr rfl) k₄.r12 (.inr rfl) (.inr rfl) fun s₅ k₅ f₅ r₅ => ?_)
  have rO₅ := r₅ r₄
  rw [List.nil_append, eO, bO₄] at rO₅
  have rI₅ := repr_keep hH f₅ (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact hp.i_o
    · exact hp.i_s.sub_right (cal_sub hH hp)
    · exact hp.stk_i.symm) rI₄
  have hsc : ⟨scr s₀, 8 * sc⟩ ∈ s₅.wr := by rw [k₅.wr, hp.wr]; simp
  refine WP.mono (restore_ok H k₅.r15 hW k₅.saved hsc (by omega)) fun s' ⟨hm, _, _, hg, ho⟩ => ?_
  refine ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  · rw [hm, k₅.ret]
  · show hH.SH.Repr s'.mem (inn s₀) _ ∧ hH.SH.Repr s'.mem (out s₀) _
    rw [hm, blockKey_eq hH hp]
    exact ⟨rI₅, rO₅⟩

end

end VG.Proof.Hmac.Generic.X86_64.Init
