import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Finalize

/-!
# PBKDF2-HMAC over any streaming hash function on x86-64: `iterate`, correct

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Pbkdf2.Generic.X86_64

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash copy)
open VG.Impl.Pbkdf2.Generic.X86_64 (stO tmpO uO xorLoop count2 body prologue iterate)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Hmac.Generic.X86_64.Init (off_disj off_disj0 covers_one sub_of_off sub_of_self bytes_keep repr_keep)
open VG.Proof.Hmac.Generic.X86_64.Finalize (add_zero' bytesAt_take bytesAt_writeBytes_self' xorPad_length)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt sub_offset contains_offset)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi wp_subi wp_test ofNat_pred ofNat_beq_zero)
open VG.Proof.Hmac.X86_64 (bytesAt_length writeBytes_at bytesAt_getD')
open VG.Proof.Hmac.Generic.X86_64 (xorBytes_length')
open VG.Proof.Sha256.Stream (writeBytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad hmacBlockKey)

variable {H : Hash} (hH : HashOK H) (sc : Nat)

section
variable (s₀ : State)

abbrev key : Addr := s₀.gpr .rdi
abbrev up : Addr := s₀.gpr .rsi
abbrev tp : Addr := s₀.gpr .rcx
abbrev scr : Addr := s₀.gpr .r8
/-- The number of steps. -/
abbrev nn : Nat := ((s₀.gpr .rdx).setWidth 32).toNat
abbrev keyR : Region := ⟨key s₀, 2 * H.S⟩
abbrev uR : Region := ⟨up s₀, H.D⟩
abbrev tR : Region := ⟨tp s₀, H.D⟩
abbrev scR : Region := ⟨scr s₀, 8 * sc⟩
abbrev retR : Region := ⟨s₀.gpr .rsp, 8⟩
abbrev stkR : Region := below (s₀.gpr .rsp) 16
/-- The state being hashed, the inner digest and `U`, in `scratch`. -/
abbrev ST : Addr := scr s₀ + BitVec.ofNat 64 (stO H)
abbrev TM : Addr := scr s₀ + BitVec.ofNat 64 (tmpO H)
abbrev UA : Addr := scr s₀ + BitVec.ofNat 64 (uO H)
abbrev calR : Region := ⟨scr s₀, hH.Wb⟩

end

/-- The precondition, with the sizes of `H`. -/
structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [keyR (H := H) s₀, uR (H := H) s₀]
  wr : s₀.wr = [tR (H := H) s₀, scR sc s₀]
  k_t : (keyR (H := H) s₀).Disjoint (tR (H := H) s₀)
  k_s : (keyR (H := H) s₀).Disjoint (scR sc s₀)
  u_t : (uR (H := H) s₀).Disjoint (tR (H := H) s₀)
  u_s : (uR (H := H) s₀).Disjoint (scR sc s₀)
  t_s : (tR (H := H) s₀).Disjoint (scR sc s₀)
  ret_k : (retR s₀).Disjoint (keyR (H := H) s₀)
  ret_u : (retR s₀).Disjoint (uR (H := H) s₀)
  ret_t : (retR s₀).Disjoint (tR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (scR sc s₀)
  stk_k : (stkR s₀).Disjoint (keyR (H := H) s₀)
  stk_u : (stkR s₀).Disjoint (uR (H := H) s₀)
  stk_t : (stkR s₀).Disjoint (tR (H := H) s₀)
  stk_s : (stkR s₀).Disjoint (scR sc s₀)
  knw : (key s₀).toNat + 2 * H.S ≤ 2 ^ 64
  nw : (scr s₀).toNat + 8 * sc ≤ 2 ^ 64
  fits : H.buf + H.S + 2 * H.F ≤ 8 * sc
  hB : 0 < H.B ∧ H.B ≤ 128
  hW : H.W ≤ 64
  hS : 0 < H.S ∧ H.S ≤ 256
  hD : 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64

theorem pre_of {s₀ : State} (h : (iterG hH.SH sc).pre s₀) (hfit : H.buf + H.S + 2 * H.F ≤ 8 * sc) :
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

theorem bounds : H.buf = 8 * H.W + 48 ∧ H.buf + H.S + 2 * H.F ≤ 8 * sc ∧ (scr s₀).toNat + 8 * sc ≤ 2 ^ 64 ∧
    H.W ≤ 64 ∧ 0 < H.S ∧ H.S ≤ 256 ∧ 0 < H.D ∧ H.D ≤ H.F ∧ H.F ≤ 64 ∧ 0 < H.B ∧ H.B ≤ 128 :=
  ⟨rfl, hp.fits, hp.nw, hp.hW, hp.hS.1, hp.hS.2, hp.hD.1, hp.hD.2.1, hp.hD.2.2, hp.hB.1, hp.hB.2⟩

theorem off_sub {o n : Nat} (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ (scR sc s₀) :=
  sub_offset h (by have := hp.nw; omega)

theorem save_sub : Region.Sub (saveR H (scr s₀)) (scR sc s₀) := by
  obtain ⟨hb, hf, -⟩ := bounds hp; exact off_sub hp (by omega) (by omega)

theorem st_sub : Region.Sub ⟨ST (H := H) s₀, H.S⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, h0, -⟩ := bounds hp; exact off_sub hp (by simp only [stO]; omega) h0

theorem tm_sub : Region.Sub ⟨TM (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, -, -, h0, h1, -⟩ := bounds hp; exact off_sub hp (by simp only [tmpO]; omega) (by omega)

theorem ua_sub : Region.Sub ⟨UA (H := H) s₀, H.F⟩ (scR sc s₀) := by
  obtain ⟨hb, hf, -, -, -, -, h0, h1, -⟩ := bounds hp; exact off_sub hp (by simp only [uO]; omega) (by omega)

include hH in
theorem cal_sub : Region.Sub (calR hH s₀) (scR sc s₀) := by
  have := hH.hWb; obtain ⟨hb, hf, -⟩ := bounds hp
  exact Region.sub_prefix (by omega)

/-- The parts of `scratch` do not overlap. -/
theorem part_disj {a m b n : Nat} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ 8 * sc) (hb : b + n ≤ 8 * sc)
    (hm : 0 < m) (hn : 0 < n) :
    Region.Disjoint ⟨scr s₀ + BitVec.ofNat 64 a, m⟩ ⟨scr s₀ + BitVec.ofNat 64 b, n⟩ := by
  have := hp.nw
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have ta : (BitVec.ofNat 64 a).toNat = a := toNat_ofNat_lt (by omega)
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

include hH in
theorem cal_disj {b n : Nat} (h : 8 * H.W ≤ b) (hb : b + n ≤ 8 * sc) :
    (calR hH s₀).Disjoint ⟨scr s₀ + BitVec.ofNat 64 b, n⟩ := by
  have := hH.hWb; have := hp.nw
  intro x h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have tb : (BitVec.ofNat 64 b).toNat = b := toNat_ofNat_lt (by omega)
  bv_omega

omit hp in
theorem stk_ret : (stkR s₀).Disjoint (retR s₀) := by
  intro a h₁ h₂; simp only [Region.Contains] at h₁ h₂; bv_omega

end

/-! ## What the pieces keep -/

/-- The registers and memory kept from the prologue on, with `m` steps left:
everything written is in `T`, `scratch` or the stack. -/
structure KR (s₀ : State) (m : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = key s₀
  r12 : s.gpr .r12 = tp s₀
  r13 : s.gpr .r13 = BitVec.ofNat 64 m
  r15 : s.gpr .r15 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  frame : Frame [tR (H := H) s₀, scR sc s₀, stkR s₀] s₀.mem s.mem

/-- The registers `KR` fixes. -/
abbrev kregs : List Reg := [.rbx, .r12, .r13, .r15, .rsp]

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

/-- `KR` survives changes to other registers, and to memory in `T`,
`scratch` (away from the save area) and the stack. -/
theorem KR.keep {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ kregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [tR (H := H) s₀, scR sc s₀, stkR s₀], Region.Sub r r') :
    KR (H := H) sc s₀ m s' := by
  have hr : ∀ r ∈ rs, (retR s₀).Disjoint r := fun r hr => by
    obtain ⟨r', hr', hs'⟩ := hsub r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl
    · exact hp.ret_t.sub_right hs'
    · exact hp.ret_s.sub_right hs'
    · exact (stk_ret (s₀ := s₀)).symm.sub_right hs'
  exact ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r13, (hg _ (by simp)).trans h.r15,
    h.saved.frame H hf hs, (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret,
    h.frame.trans (hf.sub hsub)⟩

theorem KR.call {m : Nat} {s s' : State} (h : KR (H := H) sc s₀ m s) {ws : List Region} (ha : After s ws s')
    (hs : ∀ r ∈ ws, (saveR H (scr s₀)).Disjoint r) (hsub : ∀ r ∈ ws, Region.Sub r (scR sc s₀)) :
    KR (H := H) sc s₀ m s' := by
  have f := ha.frame
  rw [h.rsp] at f
  refine h.keep hp ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f (fun r hr => ?_) (fun r hr => ?_)
  · rcases List.mem_append.mp hr with hr | hr
    · exact hs r hr
    · simp only [List.mem_singleton] at hr; subst hr; exact hp.stk_s.symm.sub_left (save_sub hp)
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨scR sc s₀, by simp, hsub r hr⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact ⟨stkR s₀, by simp, fun _ h => h⟩

theorem mem_wr : scR sc s₀ ∈ s₀.wr ∧ tR (H := H) s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem save_off {o n : Nat} (ho : 8 * H.W + 48 ≤ o) (h : o + n ≤ 8 * sc) (hn : 0 < n) :
    (saveR H (scr s₀)).Disjoint ⟨scr s₀ + BitVec.ofNat 64 o, n⟩ :=
  part_disj hp (a := 8 * H.W) (m := 48) (by omega) (by have := hp.fits; simp only [Hash.buf] at this; omega)
    h (by omega) hn

/-! ## The copies of the key's states -/

theorem copyKey_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = 0 ∨ o = H.S) :
    WP isa (copy .rbx o .r15 (stO H) H.S) s fun t => KR (H := H) sc s₀ m t ∧
      Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem ∧
      ∀ msg, hH.SH.Repr s₀.mem (key s₀ + BitVec.ofNat 64 o) msg → hH.SH.Repr t.mem (ST (H := H) s₀) msg := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, -⟩ := bounds hp
  have hkn := hp.knw
  have ksub : Region.Sub ⟨key s₀ + BitVec.ofNat 64 o, H.S⟩ (keyR (H := H) s₀) :=
    sub_offset (by rcases ho with rfl | rfl <;> omega) (by rcases ho with rfl | rfl <;> omega)
  have kR : keyR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have sR : scR sc s₀ ∈ s.wr := by rw [hk.wr]; exact (mem_wr hp).1
  have stsub := st_sub hp
  refine WP.mono (copy_ok (so := o) (d := stO H) (n := H.S) (by decide) (by decide) hS0 (by omega)
    (fun k hk' => by rw [hk.rbx]; exact inRegions_of_sub kR ksub (by omega) hk')
    (fun k hk' => by rw [hk.r15]; exact inRegions_of_sub sR stsub (by omega) hk')
    (by rw [hk.rbx, hk.r15]; exact (hp.k_s.sub_left ksub).sub_right stsub)) fun t c => ?_
  rw [hk.rbx, hk.r15] at c
  have fr : Frame [⟨ST (H := H) s₀, H.S⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  have sd : (saveR H (scr s₀)).Disjoint ⟨ST (H := H) s₀, H.S⟩ :=
    save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega) hS0
  refine ⟨hk.keep hp c.rd c.wr (fun r hr => c.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    fr (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact sd)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, stsub⟩),
    fr, fun msg hr => ?_⟩
  refine hH.repr _ _ _ _ _ (fun i hi => ?_) hr
  rw [c.mem, writeBytes_at _ _ _ (by rw [bytesAt_length]; exact hi) (by rw [bytesAt_length]; omega),
    bytesAt_getD' _ _ hi]
  -- The key's bytes are those of the initial memory.
  refine hk.frame.bytes (R := ⟨key s₀ + BitVec.ofNat 64 o, H.S⟩) ?_ (by show H.S ≤ 2 ^ 64; omega) hi
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp.k_t.sub_left ksub
  · exact hp.k_s.sub_left ksub
  · exact hp.stk_k.symm.sub_left ksub

/-! ## The calls -/

/-- An argument block's registers: the ones it sets, then `KR`. -/
theorem kr_regs {m : Nat} {s t : State} (hk : KR (H := H) sc s₀ m s) (hrd : t.rd = s.rd) (hwr : t.wr = s.wr)
    (hg : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .rdx → r ≠ .rcx → r ≠ .r8 → t.gpr r = s.gpr r) (hm : t.mem = s.mem) :
    KR (H := H) sc s₀ m t :=
  hk.keep hp hrd hwr (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact hg _ (by decide) (by decide) (by decide) (by decide) (by decide))
    (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp)

theorem updArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H) ++ [.mov32 .rsi (.imm (BitVec.ofNat 32 H.B))] ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++
      [.mov32 .rcx (.imm (BitVec.ofNat 32 H.D)), .mov .r8 (.reg .r15)])) s fun t =>
        KR (H := H) sc s₀ m t ∧ UpdArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) H.D ∧
        t.gpr .rsi = BitVec.ofNat 64 H.B ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  have et : tmpO H = 8 * H.W + 48 + H.S := rfl
  have es : stO H = 8 * H.W + 48 := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by
    simp only [uO, tmpO, stO] at ho ⊢; rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have dsub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
    wp_addi fun s₅ u₅ => wp_mov32i fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := kr_regs hp hk (by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r h1 h2 h3 h4 h5 => by
      rw [u₇.other r h5, u₆.other r h4, u₅.other r h3, u₄.other r h3, u₃.other r h2, u₂.other r h1,
        u₁.other r h1]) (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, zx_ofNat (by omega)],
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₁.gpr, hk.r15,
          sx_ofNat (by simp only [stO]; omega)]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), hk.r15, sx_ofNat (by omega)]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, zx_ofNat (by omega), toNat_ofNat_lt (by omega)]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide), hk.r15]
      cd := by
        rw [k₇.rd, k₇.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_singleton] at hr; subst hr
          exact sub_of_off (List.mem_append_right _ sR) (by omega)
      cw := by
        rw [k₇.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · exact sub_of_off sR (by simp only [stO]; omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_sc := (cal_disj hH hp (by simp only [stO]; omega) (by simp only [stO]; omega)).symm
      d_st := part_disj hp (by omega) (by omega) (by simp only [stO]; omega) hD0 hS0
      d_sc := (cal_disj hH hp (by simp only [stO] at ho'; omega) (by omega)).symm
      stk_st := by rw [k₇.rsp]; exact hp.stk_s.sub_right (st_sub hp)
      stk_d := by rw [k₇.rsp]; exact hp.stk_s.sub_right dsub
      stk_sc := by rw [k₇.rsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem updCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {d : Addr}
    (ha : UpdArgs hH t (ST (H := H) s₀) d (scr s₀) H.D) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' → Frame [⟨ST (H := H) s₀, H.S⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → t.gpr .rsi = BitVec.ofNat 64 msg.length →
        hH.SH.Repr s'.mem (ST (H := H) s₀) (msg ++ bytesAt t.mem d H.D)) → Q s') :
    WP isa (.call H.updN H.updC) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  refine upd_call hH ha (by omega) fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega) hS0
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 48) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact st_sub hp
    · exact cal_sub hH hp

theorem finArgs_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) {o : Nat} (ho : o = uO H ∨ o = tmpO H) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi (stO H) ++ count2 H ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx o ++ [.mov .rcx (.reg .r15)])) s fun t =>
        KR (H := H) sc s₀ m t ∧ FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀) ∧
        t.gpr .rsi = BitVec.ofNat 64 (H.B + H.D) ∧ t.mem = s.mem := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  have et : tmpO H = 8 * H.W + 48 + H.S := rfl
  have es : stO H = 8 * H.W + 48 := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by
    simp only [uO, tmpO, stO] at ho ⊢; rcases ho with rfl | rfl <;> omega
  have sR : scR sc s₀ ∈ s₀.wr := (mem_wr hp).1
  have osub : Region.Sub ⟨scr s₀ + BitVec.ofNat 64 o, H.F⟩ (scR sc s₀) := off_sub hp (by omega) (by omega)
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, count2, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => wp_mov32i fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ =>
    wp_addi fun s₅ u₅ => wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have k₆ := kr_regs hp hk (by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd])
    (by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]) (fun r h1 h2 h3 h4 _ => by
      rw [u₆.other r h4, u₅.other r h3, u₄.other r h3, u₃.other r h2, u₂.other r h1,
        u₁.other r h1]) (by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
  refine ⟨k₆, ?_, by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, zx_ofNat (by omega)], by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]⟩
  exact
    { rdi := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), u₂.gpr, u₁.gpr, hk.r15, sx_ofNat (by simp only [stO]; omega)]
      rdx := by rw [u₆.other _ (by decide), u₅.gpr, u₄.gpr, u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), hk.r15, sx_ofNat (by omega)]
      rcx := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), u₁.other _ (by decide), hk.r15]
      cw := by
        rw [k₆.wr]
        exact Covers.of_sub fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl
          · exact sub_of_off sR (by simp only [stO]; omega)
          · exact sub_of_off sR (by omega)
          · exact sub_of_self (r := scR sc s₀) sR (by show hH.Wb ≤ 8 * sc; omega)
      st_o := part_disj hp (by omega) (by simp only [stO]; omega) (by omega) hS0 (by omega)
      st_sc := (cal_disj hH hp (by simp only [stO]; omega) (by simp only [stO]; omega)).symm
      o_sc := (cal_disj hH hp (by simp only [stO] at ho'; omega) (by omega)).symm
      stk_st := by rw [k₆.rsp]; exact hp.stk_s.sub_right (st_sub hp)
      stk_o := by rw [k₆.rsp]; exact hp.stk_s.sub_right osub
      stk_sc := by rw [k₆.rsp]; exact hp.stk_s.sub_right (cal_sub hH hp) }

theorem finCall_ok {m : Nat} {t : State} (hk : KR (H := H) sc s₀ m t) {o : Nat} (ho : o = uO H ∨ o = tmpO H)
    (ha : FinArgs hH t (ST (H := H) s₀) (scr s₀ + BitVec.ofNat 64 o) (scr s₀)) {Q : State → Prop}
    (hQ : ∀ s', KR (H := H) sc s₀ m s' →
      Frame [⟨ST (H := H) s₀, H.S⟩, ⟨scr s₀ + BitVec.ofNat 64 o, H.F⟩, calR hH s₀, stkR s₀] t.mem s'.mem →
      (∀ msg, hH.SH.Repr t.mem (ST (H := H) s₀) msg → msg.length < 2 ^ 64 →
        t.gpr .rsi = BitVec.ofNat 64 msg.length →
        (bytesAt s'.mem (scr s₀ + BitVec.ofNat 64 o) H.F).take H.D = hH.SH.H.hash msg) → Q s') :
    WP isa (.call H.finN H.finC) t Q := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have hwb := hH.hWb
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  have et : tmpO H = 8 * H.W + 48 + H.S := rfl
  have es : stO H = 8 * H.W + 48 := rfl
  have ho' : stO H + H.S ≤ o ∧ o + H.F ≤ 8 * sc := by
    simp only [uO, tmpO, stO] at ho ⊢; rcases ho with rfl | rfl <;> omega
  refine fin_call hH ha fun s' ha' hpost => ?_
  have f := ha'.frame
  rw [hk.rsp] at f
  refine hQ s' (hk.call hp ha' ?_ ?_) f hpost
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact save_off hp (by simp only [stO]; omega) (by simp only [stO]; omega) hS0
    · exact save_off hp (by simp only [stO] at ho'; omega) (by omega) (by omega)
    · exact ((cal_disj hH hp (b := 8 * H.W) (n := 48) (Nat.le_refl _) (by omega))).symm
  · simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl | rfl)
    · exact st_sub hp
    · exact off_sub hp (by omega) (by omega)
    · exact cal_sub hH hp

/-! ## `T ← T ⊕ U` and the count -/

theorem xor'_ok {m : Nat} {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (xorLoop H) s fun t => KR (H := H) sc s₀ m t ∧
      t.mem = writeBytes s.mem (tp s₀) (Spec.Pbkdf2.xorBytes (bytesAt s.mem (tp s₀) H.D)
        (bytesAt s.mem (UA (H := H) s₀) H.D)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  refine WP.mono (xor_ok (uo := uO H) (n := H.D) hD0 (by omega)
    (fun k hk' => by
      rw [hk.r15, hk.rd, hk.wr]; exact inRegions_of_sub (List.mem_append_right _ sR) usub (by omega) hk')
    (fun k hk' => by rw [hk.r12, add_zero', hk.wr]; exact inRegions_of_sub tR' (fun _ h => h) (by omega) hk')
    (by rw [hk.r15, hk.r12]; exact hp.t_s.symm.sub_left usub)) fun t x => ?_
  rw [hk.r15, hk.r12] at x
  refine ⟨hk.keep hp x.rd x.wr (fun r hr => x.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    (x.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]; exact Region.contains_self _ _))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact hp.t_s.symm.sub_left (save_sub hp))
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, fun _ h => h⟩), x.mem⟩

omit hp in
theorem dec_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (hk : KR (H := H) sc s₀ m s) :
    WP isa (.block [.alu .sub .r13 (.imm 1)]) s fun t => KR (H := H) sc s₀ (m - 1) t ∧
      t.zf = some (decide (m - 1 = 0)) ∧ t.mem = s.mem := by
  refine wp_subi fun t u z => WP.block_nil ⟨⟨by rw [u.rd, hk.rd], by rw [u.wr, hk.wr],
    by rw [u.other _ (by decide), hk.rsp], by rw [u.other _ (by decide), hk.rbx],
    by rw [u.other _ (by decide), hk.r12], by rw [u.gpr, hk.r13, sx_one, ofNat_pred hm],
    by rw [u.other _ (by decide), hk.r15], u.mem ▸ hk.saved, by rw [u.mem, hk.ret], u.mem ▸ hk.frame⟩, ?_,
    u.mem⟩
  rw [z, hk.r13, sx_one, ofNat_pred hm, ofNat_beq_zero (by omega)]

end

/-! ## One step -/

/-- The key's states represent `K₀ ⊕ ipad` and `K₀ ⊕ opad`. -/
def KeyOK (s₀ : State) (k0 : List Byte) : Prop :=
  k0.length = H.B ∧ hH.SH.Repr s₀.mem (key s₀) (xorPad k0 ipad) ∧
    hH.SH.Repr s₀.mem (key s₀ + BitVec.ofNat 64 H.S) (xorPad k0 opad)

/-- With `m` steps left, what is left to compute is the rest of the whole. -/
structure Inv (s₀ : State) (m : Nat) (s : State) : Prop where
  kr : KR (H := H) sc s₀ m s
  it : ∀ k0, KeyOK hH s₀ k0 →
    Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (nn s₀) (bytesAt s₀.mem (up s₀) H.D)
        (bytesAt s₀.mem (tp s₀) H.D) =
      Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) m (bytesAt s.mem (UA (H := H) s₀) H.D)
        (bytesAt s.mem (tp s₀) H.D)

section
variable {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀)
include hp

theorem body_ok {m : Nat} (hm : 1 ≤ m) (hn : m < 2 ^ 64) {s : State} (h : Inv hH sc s₀ m s) :
    WP isa (body H) s fun t => Inv hH sc s₀ (m - 1) t ∧ t.zf = some (decide (m - 1 = 0)) := by
  obtain ⟨hb, hf, hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  have et : tmpO H = 8 * H.W + 48 + H.S := rfl
  have es : stO H = 8 * H.W + 48 := rfl
  have hwb := hH.hWb
  -- Where things are.
  have stk := hp.stk_s
  have ua : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  have tmD : Region.Sub ⟨TM (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  have dU₁ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega) hD0 hS0
  have dU₂ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ ⟨TM (H := H) s₀, H.F⟩ :=
    part_disj hp (by omega) (by omega) (by omega) hD0 (by omega)
  have dU₃ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ (calR hH s₀) := (cal_disj hH hp (by omega) (by omega)).symm
  have dU₄ : Region.Disjoint ⟨UA (H := H) s₀, H.D⟩ (stkR s₀) := stk.symm.sub_left ua
  have dM₁ : Region.Disjoint ⟨TM (H := H) s₀, H.D⟩ ⟨ST (H := H) s₀, H.S⟩ :=
    part_disj hp (by omega) (by omega) (by omega) hD0 hS0
  have dM₃ : Region.Disjoint ⟨TM (H := H) s₀, H.D⟩ (calR hH s₀) := (cal_disj hH hp (by omega) (by omega)).symm
  have dM₄ : Region.Disjoint ⟨TM (H := H) s₀, H.D⟩ (stkR s₀) := stk.symm.sub_left tmD
  have dT : ∀ r : Region, Region.Sub r (scR sc s₀) → Region.Disjoint (tR (H := H) s₀) r :=
    fun r hr => hp.t_s.sub_right hr
  have dT₄ : Region.Disjoint (tR (H := H) s₀) (stkR s₀) := hp.stk_t.symm
  have hSn : H.S ≤ 2 ^ 64 := by omega
  have hDn : H.D ≤ 2 ^ 64 := by omega
  -- The pieces.
  refine WP.seq (WP.mono (copyKey_ok hH hp h.kr (.inl rfl)) fun c₁ ⟨kc₁, fc₁, rc₁⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₁ (.inl rfl)) fun a₁ ⟨ka₁, aa₁, sa₁, ma₁⟩ =>
    updCall_ok hH hp ka₁ aa₁ fun u₁ ku₁ fu₁ ru₁ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₁ (.inr rfl)) fun b₁ ⟨kb₁, ab₁, sb₁, mb₁⟩ =>
    finCall_ok hH hp kb₁ (.inr rfl) ab₁ fun f₁ kf₁ ff₁ rf₁ => ?_))
  refine WP.seq (WP.mono (copyKey_ok hH hp kf₁ (.inr rfl)) fun c₂ ⟨kc₂, fc₂, rc₂⟩ => ?_)
  refine WP.seq (WP.seq (WP.mono (updArgs_ok hH hp kc₂ (.inr rfl)) fun a₂ ⟨ka₂, aa₂, sa₂, ma₂⟩ =>
    updCall_ok hH hp ka₂ aa₂ fun u₂ ku₂ fu₂ ru₂ => ?_))
  refine WP.seq (WP.seq (WP.mono (finArgs_ok hH hp ku₂ (.inl rfl)) fun b₂ ⟨kb₂, ab₂, sb₂, mb₂⟩ =>
    finCall_ok hH hp kb₂ (.inl rfl) ab₂ fun f₂ kf₂ ff₂ rf₂ => ?_))
  refine WP.seq (WP.mono (xor'_ok hp kf₂) fun x ⟨kx, mx⟩ => ?_)
  refine WP.mono (dec_ok hm hn kx) fun t ⟨kt, zt, mt⟩ => ⟨⟨kt, fun k0 hk => ?_⟩, zt⟩
  -- The bytes of `U` and `T` at each point.
  obtain ⟨hl0, hrI, hrO⟩ := hk
  have U₁ : bytesAt c₁.mem (UA (H := H) s₀) H.D = bytesAt s.mem (UA (H := H) s₀) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dU₁) hDn
  have T₁ : bytesAt c₁.mem (tp s₀) H.D = bytesAt s.mem (tp s₀) H.D :=
    bytes_keep fc₁ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₂ : bytesAt u₁.mem (tp s₀) H.D = bytesAt c₁.mem (tp s₀) H.D := by
    rw [← ma₁]; exact bytes_keep fu₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₃ : bytesAt f₁.mem (tp s₀) H.D = bytesAt u₁.mem (tp s₀) H.D := by
    rw [← mb₁]; exact bytes_keep ff₁ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (tm_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₄ : bytesAt c₂.mem (tp s₀) H.D = bytesAt f₁.mem (tp s₀) H.D :=
    bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dT _ (st_sub hp)) hDn
  have T₅ : bytesAt u₂.mem (tp s₀) H.D = bytesAt c₂.mem (tp s₀) H.D := by
    rw [← ma₂]; exact bytes_keep fu₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have T₆ : bytesAt f₂.mem (tp s₀) H.D = bytesAt u₂.mem (tp s₀) H.D := by
    rw [← mb₂]; exact bytes_keep ff₂ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro r (rfl | rfl | rfl | rfl)
      · exact dT _ (st_sub hp)
      · exact dT _ (ua_sub hp)
      · exact dT _ (cal_sub hH hp)
      · exact dT₄) hDn
  have M₄ : bytesAt c₂.mem (TM (H := H) s₀) H.D = bytesAt f₁.mem (TM (H := H) s₀) H.D :=
    bytes_keep fc₂ (by simp only [List.mem_singleton]; rintro r rfl; exact dM₁) hDn
  -- The inner hash.
  have rI₁ := rc₁ _ (by rw [add_zero']; exact hrI)
  have rU₁ := ru₁ _ (ma₁ ▸ rI₁) (by rw [sa₁, xorPad_length, hl0])
  rw [ma₁, U₁] at rU₁
  have hl₁ : (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D).length = H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, bytesAt_length]
  have dig₁ := rf₁ _ (mb₁ ▸ rU₁) (by rw [hl₁]; omega) (by rw [sb₁, hl₁])
  -- The outer hash.
  have rO₂ := rc₂ _ hrO
  have rU₂ := ru₂ _ (ma₂ ▸ rO₂) (by rw [sa₂, xorPad_length, hl0])
  rw [ma₂, M₄, bytesAt_take _ _ hDF, dig₁] at rU₂
  have hl₂ : (xorPad k0 opad ++ hH.SH.H.hash (xorPad k0 ipad ++ bytesAt s.mem (UA (H := H) s₀) H.D)).length =
      H.B + H.D := by
    rw [List.length_append, xorPad_length, hl0, ← dig₁, List.length_take, bytesAt_length, Nat.min_eq_left hDF]
  have dig₂ := rf₂ _ (mb₂ ▸ rU₂) (by rw [hl₂]; omega) (by rw [sb₂, hl₂])
  rw [← bytesAt_take _ _ hDF] at dig₂
  -- `T ← T ⊕ U`.
  have hx : (Spec.Pbkdf2.xorBytes (bytesAt f₂.mem (tp s₀) H.D) (bytesAt f₂.mem (UA (H := H) s₀) H.D)).length =
      H.D := by rw [xorBytes_length' _ _ (by simp [bytesAt_length]), bytesAt_length]
  have Ux : bytesAt t.mem (UA (H := H) s₀) H.D = bytesAt f₂.mem (UA (H := H) s₀) H.D := by
    rw [mt, mx]
    exact bytes_keep (Proof.Sha256.Stream.writeBytes_frame _ _ _ (R := tR (H := H) s₀) (by
      rw [hx]; exact Region.contains_self _ _)) (by
        simp only [List.mem_singleton]; rintro r rfl; exact (dT _ ua).symm) hDn
  have Tx : bytesAt t.mem (tp s₀) H.D = Spec.Pbkdf2.xorBytes (bytesAt f₂.mem (tp s₀) H.D)
      (bytesAt f₂.mem (UA (H := H) s₀) H.D) := by
    rw [mt, mx]; exact bytesAt_writeBytes_self' hx (by omega)
  rw [h.it k0 ⟨hl0, hrI, hrO⟩, show m = (m - 1) + 1 by omega, Ux, Tx, dig₂, T₆, T₅, T₄, T₃, T₂, T₁,
    Nat.add_sub_cancel]
  rfl

/-! ## The prologue and the loop -/

omit hp in
theorem zx32 (x : BitVec 64) : (x.setWidth 32).setWidth 64 = BitVec.ofNat 64 (x.setWidth 32).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]

omit hp in
theorem nn_lt : nn s₀ < 2 ^ 32 := ((s₀.gpr .rdx).setWidth 32).isLt

theorem pro_ok : WP isa (.block (prologue H)) s₀ fun s => KR (H := H) sc s₀ (nn s₀) s ∧
    s.gpr .rsi = up s₀ ∧ Frame [saveR H (scr s₀)] s₀.mem s.mem := by
  obtain ⟨hb, hf, -⟩ := bounds hp
  have hL : 8 * H.W + 48 ≤ 8 * sc := by omega
  refine save_ok H (scr := scr s₀) rfl hp.hW (mem_wr hp).1 hL fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov32r fun s₂ u₂ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    WP.block_nil ?_
  have k : ∀ r, r ≠ .r13 → r ≠ .rbx → r ≠ .r12 → r ≠ .r15 → s₅.gpr r = s₀.gpr r := fun r h1 h2 h3 h4 => by
    rw [u₅.other r h4, u₄.other r h3, u₃.other r h2, u₂.other r h1, g₁]
  have hm : s₅.mem = s₁.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have fs : Frame [saveR H (scr s₀)] s₀.mem s₅.mem := hm ▸ f₁
  refine ⟨⟨by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁], by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁],
    k _ (by decide) (by decide) (by decide) (by decide),
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, g₁, zx32],
    by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), g₁],
    hm ▸ sv₁, fs.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.ret_s.sub_right (save_sub hp)) (by decide),
    fs.sub (by simp only [List.mem_singleton]; rintro r rfl; exact ⟨scR sc s₀, by simp, save_sub hp⟩)⟩,
    k _ (by decide) (by decide) (by decide) (by decide), fs⟩

/-- `U` into `scratch`. -/
theorem copyU_ok {s : State} (hk : KR (H := H) sc s₀ (nn s₀) s) (hsi : s.gpr .rsi = up s₀)
    (hf : Frame [saveR H (scr s₀)] s₀.mem s.mem) :
    WP isa (copy .rsi 0 .r15 (uO H) H.D) s (Inv hH sc s₀ (nn s₀)) := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  have eu : uO H = 8 * H.W + 48 + H.S + H.F := rfl
  obtain ⟨sR, tR'⟩ := mem_wr hp
  have uR' : uR (H := H) s₀ ∈ s.rd ++ s.wr := by rw [hk.rd, hp.rd]; simp
  have usub : Region.Sub ⟨UA (H := H) s₀, H.D⟩ (scR sc s₀) := off_sub hp (by omega) hD0
  refine WP.mono (copy_ok (so := 0) (d := uO H) (n := H.D) (by decide) (by decide) hD0 (by omega)
    (fun k hk' => by rw [hsi, add_zero']; exact inRegions_of_sub uR' (fun _ h => h) (by omega) hk')
    (fun k hk' => by rw [hk.r15, hk.wr]; exact inRegions_of_sub sR usub (by omega) hk')
    (by rw [hsi, hk.r15, add_zero']; exact hp.u_s.sub_right usub)) fun t c => ?_
  rw [hsi, hk.r15, add_zero'] at c
  have fc : Frame [⟨UA (H := H) s₀, H.D⟩] s.mem t.mem :=
    c.mem ▸ Proof.Sha256.Stream.writeBytes_frame _ _ _ (by rw [bytesAt_length]; exact Region.contains_self _ _)
  refine ⟨hk.keep hp c.rd c.wr (fun r hr => c.other r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide))
    fc (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact save_off hp (by omega) (by omega) hD0)
    (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, by simp, usub⟩), fun k0 _ => ?_⟩
  congr 1
  · rw [c.mem, bytesAt_writeBytes_self' (bytesAt_length _ _ _) (by omega)]
    exact (bytes_keep hf (by
      simp only [List.mem_singleton]; rintro r rfl; exact hp.u_s.sub_right (save_sub hp)) (by omega)).symm
  · exact ((bytes_keep fc (by simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right usub)
      (by omega)).trans (bytes_keep hf (by
        simp only [List.mem_singleton]; rintro r rfl; exact hp.t_s.sub_right (save_sub hp)) (by omega))).symm

omit hp in
theorem test_ok {t : State} (h : Inv hH sc s₀ (nn s₀) t) :
    WP isa (.block [.alu .test .r13 (.reg .r13)]) t fun t' =>
      Inv hH sc s₀ (nn s₀) t' ∧ t'.zf = some (decide (nn s₀ = 0)) := by
  refine wp_test fun t' g m rd wr z => WP.block_nil ⟨⟨?_, fun k0 hk => by rw [m]; exact h.it k0 hk⟩, ?_⟩
  · have k := h.kr
    exact ⟨rd.trans k.rd, wr.trans k.wr, by rw [g, k.rsp], by rw [g, k.rbx], by rw [g, k.r12], by rw [g, k.r13],
      by rw [g, k.r15], m ▸ k.saved, by rw [m, k.ret], m ▸ k.frame⟩
  · have := nn_lt (s₀ := s₀)
    rw [z, h.kr.r13, BitVec.and_self, ofNat_beq_zero (by omega)]

theorem loop_ok {s : State} (h : Inv hH sc s₀ (nn s₀) s) (hz : s.zf = some (decide (nn s₀ = 0))) :
    WP isa (.ite .e (.block []) (.loop (body H) .ne)) s (Inv hH sc s₀ 0) := by
  have hlt := nn_lt (s₀ := s₀)
  refine WP.ite (decide (nn s₀ = 0)) (by simp [eval, hz]) (fun h0 => WP.block_nil ?_) fun h0 => ?_
  · have e : nn s₀ = 0 := by simpa using h0
    exact e ▸ h
  · have hpos : 1 ≤ nn s₀ := by have := of_decide_eq_false h0; omega
    refine WP.loop (M := isa) (fun k t => ∃ m, k = m ∧ 1 ≤ m ∧ m ≤ nn s₀ ∧ Inv hH sc s₀ m t) ?_ (nn s₀) s
      ⟨nn s₀, rfl, hpos, (Nat.le_refl _), h⟩
    rintro k t ⟨m, hkm, h1, h2, ht⟩
    refine WP.mono (body_ok hH hp h1 (by omega) ht) fun t' ⟨ht', hz'⟩ => ?_
    by_cases hl : m - 1 = 0
    · exact .inl ⟨by simp [eval, hz', hl], hl ▸ ht'⟩
    · exact .inr ⟨by simp [eval, hz', hl], m - 1, by omega, m - 1, rfl, by omega, by omega, ht'⟩

theorem correct : WP isa (iterate H) s₀ fun s' => gprPreserved s₀ s' ∧ (iterG hH.SH sc).post s₀ s' := by
  obtain ⟨hb, hf', hnw, hW, hS0, hS, hD0, hDF, hF, hB0, hB⟩ := bounds hp
  refine WP.seq (WP.mono (pro_ok hp) fun s₁ ⟨k₁, si₁, f₁⟩ => ?_)
  refine WP.seq (WP.mono (copyU_ok hH hp k₁ si₁ f₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (test_ok hH h₂) fun s₃ ⟨h₃, z₃⟩ => ?_)
  refine WP.seq (WP.mono (loop_ok hH hp h₃ z₃) fun s₄ h₄ => ?_)
  have k₄ := h₄.kr
  refine WP.mono (restore_ok H k₄.r15 hW k₄.saved (by rw [k₄.wr]; exact (mem_wr hp).1) (by omega))
    fun s' ⟨hm, _, _, hg, ho⟩ => ⟨⟨fun r hr => ?_, by rw [hm, k₄.ret]⟩, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · rw [ho _ (by simp), k₄.rsp]
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
    · exact hg _ (by simp)
  intro k0 hl hrI hrO
  have hS' := hH.hS; have hD' := hH.hD; have hB' := hH.hB
  rw [hB'] at hl
  rw [hS'] at hrO
  show bytesAt s'.mem (tp s₀) hH.SH.digestBytes = _
  rw [hD', hm, h₄.it k0 ⟨hl, hrI, hrO⟩]
  rfl

end

end VG.Proof.Pbkdf2.Generic.X86_64
