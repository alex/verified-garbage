import VerifiedGarbage.Proof.Hmac.Generic.X86_64.Instances
import VerifiedGarbage.Proof.Framework.Narrow

/-!
# HMAC over any streaming hash function on x86-64: `init` for a key of any length

Untrusted: everything here is checked by Lean. `initAny` compares `key_len`
with the block size; a longer key is replaced by its digest (`hashKey`, with
the hash function's streaming functions, in `scratch` after `init`'s
buffers), and `init` (`Init.lean`) runs on the key or the digest. `init` is
proven against `initG` with its working space (`nw0`) and the key's region
for the regions its state permits; it runs from a state permitting more
(`WP.of_narrow`, `RelCT.of_narrow`), with the same trace.

`initAny` is verified against `initAnyG`, the contract for a key of any
length, and also against `initG`, for a key of at most a block, with the
working space `init` has: PBKDF2's `pbkdf2` calls it so.
-/

namespace VG.Proof.Hmac.Generic.X86_64

open VG.X86_64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length:
`VG.Spec.Hmac.initAnyKeyContract`. -/
def initAnyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .rdi, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .rsi, S.stateBytes⟩
    let key : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat⟩
    let scratch : Region := ⟨s.gpr .r8, 8 * W⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    let stack : Region := ⟨s.gpr .rsp - 16, 16⟩
    s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (s.gpr .r8).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat)
    S.Repr s'.mem (s.gpr .rdi) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .rsi) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .rdi = s₂.gpr .rdi ∧ s₁.gpr .rsi = s₂.gpr .rsi ∧ s₁.gpr .rdx = s₂.gpr .rdx ∧
    s₁.gpr .rcx = s₂.gpr .rcx ∧ s₁.gpr .r8 = s₂.gpr .r8 ∧ s₁.gpr .rsp = s₂.gpr .rsp

end VG.Proof.Hmac.Generic.X86_64

namespace VG.Proof.Hmac.Generic.X86_64.InitAny

open VG.X86_64
open VG.Impl.Hmac.Generic.X86_64 (Hash)
open VG.Proof.Hmac.Generic.X86_64
open VG.Proof.Hmac.Generic.X86_64.Init (Pre inn out kp kl scr inR outR keyR scR retR stkR)
open VG.Proof.Hmac.Generic.Common (add_ofNat_add covers_one sub_of_off sub_of_self bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.Sha256.X86_64 (toNat_ofNat_lt)
open VG.Proof.Sha256.X86_64.Stream (Upd wp_mov wp_mov32i wp_addi wp_cmpi)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash}

/-! ## Sizes -/

/-- The words of working space `init` gets: its buffers, rounded up. -/
abbrev nw0 (H : Hash) : Nat := (H.buf + 2 * H.B + 7) / 8

theorem ext_eq : H.ext = 8 * nw0 H := rfl

theorem fits0 : H.buf + 2 * H.B ≤ 8 * nw0 H := by simp only [nw0]; omega

theorem save_le_ext : 8 * H.W + 48 ≤ H.ext := by
  have := fits0 (H := H); simp only [Hash.buf] at this; rw [ext_eq]; omega

section
variable (Wt : Nat) (s₀ : State)

/-- All of `scratch`. -/
abbrev wsR : Region := ⟨scr s₀, 8 * Wt⟩

/-- An address in `scratch`. -/
abbrev A (o : Nat) : Addr := scr s₀ + BitVec.ofNat 64 o

end

/-- The precondition of `initAny`, with the sizes of `H`. -/
structure PreA (Wt : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, wsR Wt s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (wsR Wt s₀)
  o_s : (outR (H := H) s₀).Disjoint (wsR Wt s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (wsR Wt s₀)
  ret_i : (retR s₀).Disjoint (inR (H := H) s₀)
  ret_o : (retR s₀).Disjoint (outR (H := H) s₀)
  ret_s : (retR s₀).Disjoint (wsR Wt s₀)
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (wsR Wt s₀)
  nw : (scr s₀).toNat + 8 * Wt ≤ 2 ^ 64
  fits : H.ext + H.S + H.F ≤ 8 * Wt
  hDB : H.D ≤ H.B

theorem preA_of (hH : HashOK H) {Wt : Nat} {s₀ : State} (h : (initAnyG hH.SH Wt).pre s₀)
    (hfit : H.ext + H.S + H.F ≤ 8 * Wt) (hDB : H.D ≤ H.B) : PreA (H := H) Wt s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  have hS := hH.hS
  simp only [hS] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hfit, hDB⟩

/-! ## Running `init` from a state that permits more -/

/-- `s`, permitted only what `init` needs: the key, the states and its
working space. -/
abbrev nar (H : Hash) (s : State) : State :=
  s.withRegions [keyR s] [inR (H := H) s, outR (H := H) s, scR (nw0 H) s]

/-- A state from which `init` runs: its precondition, narrowed, and the
narrowed regions within those of the state. -/
structure Ready (s : State) : Prop where
  pre : Pre (H := H) (nw0 H) (nar H s)
  cr : Covers ([keyR s] ++ [inR (H := H) s, outR (H := H) s, scR (nw0 H) s]) (s.rd ++ s.wr)
  cw : Covers [inR (H := H) s, outR (H := H) s, scR (nw0 H) s] s.wr

/-- `Ready` depends only on the registers and the regions. -/
theorem Ready.congr {s t : State} (h : Ready (H := H) s) (hg : t.gpr = s.gpr) (hr : t.rd = s.rd)
    (hw : t.wr = s.wr) : Ready (H := H) t := by
  obtain ⟨p, c, w⟩ := h
  obtain ⟨tg, tcf, tzf, tsf, tof, txmm, tymm, tzmm, tmx, tmem, trd, twr, tu⟩ := t
  obtain ⟨sg, scf, szf, ssf, sof, sxmm, symm, szmm, smx, smem, srd, swr, su⟩ := s
  simp only at hg hr hw
  subst hg hr hw
  exact ⟨⟨p.1, p.2, p.3, p.4, p.5, p.6, p.7, p.8, p.9, p.10, p.11, p.12, p.13, p.14, p.15, p.16, p.17,
    p.18, p.19, p.20, p.21⟩, c, w⟩

variable (hH : HashOK H)

/-- The trace of `init` from a `Ready` state is that from its narrowed state. -/
theorem init_exec {s : State} (hr : Ready (H := H) s) {t : List Leak} {s₁ : State}
    (he : Exec isa H.init (nar H s) t s₁) : Exec isa H.init s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hr.cr) (by simpa using hr.cw)
  simpa using this

/-- `init` from a `Ready` state. -/
theorem init_ok {s : State} (hr : Ready (H := H) s) :
    WP isa H.init s fun s' => gprPreserved s s' ∧
      hH.SH.Repr s'.mem (inn s) (xorPad (blockKey hH.SH.H (bytesAt s.mem (kp s) (kl s))) ipad) ∧
      hH.SH.Repr s'.mem (out s) (xorPad (blockKey hH.SH.H (bytesAt s.mem (kp s) (kl s))) opad) := by
  have h := Init.correct hH hr.pre
  refine WP.mono (WP.of_narrow (n := nar H s) (fun s₁ : State => s₁.withRegions s.rd s.wr)
    (fun t s₁ he => init_exec hr he) h) fun s' hs' => ?_
  obtain ⟨s₁, rfl, hg, hq⟩ := hs'
  exact ⟨hg, hq⟩

/-! ## A key of at most a block -/

section
variable {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀)
include hp

theorem nw_lt : 8 * Wt ≤ 2 ^ 64 := by have := hp.nw; omega

theorem ext_le : H.ext + H.S + H.F ≤ 8 * Wt := hp.fits

theorem ws_sub0 : Region.Sub (scR (nw0 H) s₀) (wsR Wt s₀) := by
  have := hp.fits; rw [ext_eq] at this; exact Region.sub_prefix (by omega)

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ 8 * Wt) : Region.Sub ⟨A s₀ o, n⟩ (wsR Wt s₀) :=
  Offset.sub_base _ h

theorem ws_mem : wsR Wt s₀ ∈ s₀.wr := by rw [hp.wr]; simp

include hH in
/-- A key of at most a block: `init` runs on it. -/
theorem ready_short (hk : kl s₀ ≤ H.B) : Ready (H := H) s₀ := by
  have sub := ws_sub0 hp
  refine ⟨⟨hk, rfl, rfl, hp.i_o, hp.i_s.sub_right sub, hp.o_s.sub_right sub, hp.k_i, hp.k_o,
    hp.k_s.sub_right sub, hp.ret_i, hp.ret_o, hp.ret_s.sub_right sub, hp.stk_i, hp.stk_o, hp.stk_k,
    hp.stk_s.sub_right sub, ?_, fits0, hH.hBB, hH.hW, hH.hSB⟩, ?_, ?_⟩
  · show (scr s₀).toNat + 8 * nw0 H ≤ 2 ^ 64
    have := hp.nw; have := hp.fits; rw [ext_eq] at this; omega
  · rw [hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_of_self (r := keyR s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) (by
          have := hp.fits; rw [ext_eq] at this; show 8 * nw0 H ≤ 8 * Wt; omega)
  · rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) (by
          have := hp.fits; rw [ext_eq] at this; show 8 * nw0 H ≤ 8 * Wt; omega)

end

/-! ## Hashing a longer key -/

/-- What `hashKey` keeps, from its prologue on. -/
structure HK (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rbx : s.gpr .rbx = inn s₀
  r12 : s.gpr .r12 = out s₀
  r15 : s.gpr .r15 = scr s₀
  rbp : s.gpr .rbp = kp s₀
  r13 : s.gpr .r13 = s₀.gpr .rcx
  saved : SavedRegs H (scr s₀) s₀ s.mem
  ret : s.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  key : bytesAt s.mem (kp s₀) (kl s₀) = bytesAt s₀.mem (kp s₀) (kl s₀)

/-- The registers `HK` fixes. -/
abbrev hregs : List Reg := [.rbx, .rbp, .r12, .r13, .r15, .rsp]

section
variable {Wt : Nat} {s₀ : State}

omit hH in
theorem HK.keep {s s' : State} (h : HK (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ hregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r) (hr : ∀ r ∈ rs, (retR s₀).Disjoint r)
    (hk : ∀ r ∈ rs, (keyR s₀).Disjoint r) : HK (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.rsp, (hg _ (by simp)).trans h.rbx,
    (hg _ (by simp)).trans h.r12, (hg _ (by simp)).trans h.r15, (hg _ (by simp)).trans h.rbp,
    (hg _ (by simp)).trans h.r13, h.saved.frame H hf hs,
    (hf.readW (r := retR s₀) (Region.contains_self _ _) hr (by decide)).trans h.ret,
    (bytes_keep hf hk (Nat.le_of_lt (s₀.gpr .rcx).isLt)).trans h.key⟩

omit hH in
theorem HK.upd {s s' : State} (h : HK (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ hregs) : HK (H := H) s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := []) (by rw [u.mem]; exact Frame.refl _ _)
    (by simp) (by simp) (by simp)

variable (hp : PreA (H := H) Wt s₀)
include hp

omit hH in
/-- A region a call writes: the working space of the functions we call, or
a part of `scratch` after the save area. -/
theorem HK.call {s s' : State} (h : HK (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = ⟨A s₀ o, k⟩ ∧ 8 * H.W + 48 ≤ o ∧ o + k ≤ 8 * Wt) : HK (H := H) s₀ s' := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have f := ha.frame
  rw [h.rsp] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [calleeSaved])) f ?_ ?_ ?_
  all_goals intro r hr; rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact Offset.disjoint_base _ hk (by omega)
    · exact Offset.disjoint _ (Or.inl h₁) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_s.sub_right ssub).symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact hp.ret_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.ret_s.sub_right (part_sub h₂)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (Init.stk_ret (s₀ := s₀)).symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact hp.k_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.k_s.sub_right (part_sub h₂)
  · simp only [List.mem_singleton] at hr; subst hr
    exact hp.stk_k.symm

omit hp in
theorem scr_ok {s : State} {d : Reg} {p : Addr} (h15 : s.gpr .r15 = p) {o : Nat} (ho : o < 2 ^ 31)
    {rest : List Instr} {Q : State → Prop} (k : ∀ s', Upd s s' d (p + BitVec.ofNat 64 o) → WP isa (.block rest) s' Q) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr d o ++ rest)) s Q := by
  simp only [VG.Impl.Hmac.Generic.X86_64.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_addi fun s₂ u₂ => k s₂ ⟨?_, fun r hr => by rw [u₂.other r hr, u₁.other r hr],
    by rw [u₂.mem, u₁.mem], by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr]⟩
  rw [u₂.gpr, u₁.gpr, h15, sx_ofNat ho]

omit hp in
theorem ext_lt (hH : HashOK H) : H.ext + H.S + H.F < 2 ^ 31 := by
  have := hH.hW; have := hH.hBB; have := hH.hSB; have := hH.hF
  simp only [ext_eq, nw0, Hash.buf]; omega

include hH in
/-- The prologue: our caller's registers saved, ours set. -/
theorem pro_ok {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) :
    WP isa (.block (H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8),
      .mov .rbp (.reg .rdx), .mov .r13 (.reg .rcx)])) s (HK (H := H) s₀) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  refine save_ok H (scr := scr s₀) (by rw [hg]) hH.hW (by rw [hw]; exact ws_mem hp) (L := 8 * Wt) (by omega)
    fun s₁ g₁ rd₁ wr₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => wp_mov fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => WP.block_nil ?_
  have hm₆ : s₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g₀ : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [g₁, hg]
  refine ⟨by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, hr], by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, hw],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₀]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.gpr, g₀]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
      u₂.other _ (by decide), g₀]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
      u₂.other _ (by decide), g₀]
  · rw [u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₀]
  · rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), g₀]
  · rw [hm₆]
    exact ⟨by rw [sv₁.rbx, hg], by rw [sv₁.rbp, hg], by rw [sv₁.r12, hg], by rw [sv₁.r13, hg],
      by rw [sv₁.r14, hg], by rw [sv₁.r15, hg]⟩
  · rw [hm₆, ← hm]
    exact f₁.readW (r := retR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.ret_s.sub_right (part_sub (by omega))) (by decide)
  · rw [hm₆, ← hm]
    exact bytes_keep f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_s.sub_right (part_sub (by omega))) (Nat.le_of_lt (s₀.gpr .rcx).isLt)

/-- The streaming state of the key, and the digest. -/
abbrev stA (H : Hash) (s₀ : State) : Addr := A s₀ H.ext
abbrev dgA (H : Hash) (s₀ : State) : Addr := A s₀ (H.ext + H.S)

theorem stk_part {s : State} (h : HK (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ 8 * Wt) :
    (below (s.gpr .rsp) 16).Disjoint ⟨A s₀ o, n⟩ := by
  rw [h.rsp]; exact hp.stk_s.sub_right (part_sub hon)

theorem cov_part {s : State} (h : HK (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ 8 * Wt) :
    ∃ r' ∈ s.wr, ∃ off, (⟨A s₀ o, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨A s₀ o, n⟩ : Region).len ≤ r'.len :=
  sub_of_off (rs := s.wr) (by rw [h.wr]; exact ws_mem hp) hon

theorem cov_low {s : State} (h : HK (H := H) s₀ s) {n : Nat} (hn : n ≤ 8 * Wt) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (rs := s.wr) (r := wsR Wt s₀) (by rw [h.wr]; exact ws_mem hp) hn

omit hp in
include hH in
/-- `init`'s argument: the streaming state of the key. -/
theorem hk0_ok {s : State} (h : HK (H := H) s₀ s) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext)) s fun t =>
      HK (H := H) s₀ t ∧ t.gpr .rdi = stA H s₀ := by
  have hl := ext_lt hH
  rw [← List.append_nil (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext)]
  exact scr_ok h.r15 (by omega) fun s₁ u₁ => WP.block_nil ⟨h.upd u₁ (by decide), u₁.gpr⟩

/-- The streaming state of the key, started. -/
theorem hk1_ok {s : State} (h : HK (H := H) s₀ s) (hd : s.gpr .rdi = stA H s₀) :
    WP isa (.call H.initN H.initC) s fun t => HK (H := H) s₀ t ∧ hH.SH.Repr t.mem (stA H s₀) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  exact init_call hH (st := stA H s₀) hd (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h (by omega))
    (stk_part hp h (by omega)) fun s₂ a₂ r₂ =>
      ⟨h.call hp a₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, hx, by omega⟩, r₂⟩

/-- `update`'s arguments: the key. -/
theorem hk2_ok {s : State} (h : HK (H := H) s₀ s) (hr : hH.SH.Repr s.mem (stA H s₀) []) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbp),
      .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr))) s fun t => HK (H := H) s₀ t ∧
      UpdArgs hH t (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧ t.gpr .rsi = BitVec.ofNat 64 0 ∧
      hH.SH.Repr t.mem (stA H s₀) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  refine scr_ok h.r15 (by omega) fun s₃ u₃ => wp_mov32i fun s₄ u₄ _ _ => wp_mov fun s₅ u₅ _ _ =>
    wp_mov fun s₆ u₆ _ _ => wp_mov fun s₇ u₇ _ _ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { rdi := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr]
      rdx := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.rbp]
      rcx := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.r13]
      r8 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.r15]
      cd := covers_one (List.mem_append_left _ (by rw [k₇.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇ (by omega)
        · exact cov_low hp k₇ (by omega)
      st_sc := Offset.disjoint_base _ (by omega) (by omega)
      d_st := hp.k_s.sub_right (part_sub (by omega))
      d_sc := hp.k_s.sub_right (Region.sub_prefix (by omega))
      stk_st := stk_part hp k₇ (by omega)
      stk_d := by rw [k₇.rsp]; exact hp.stk_k
      stk_sc := by rw [k₇.rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by omega)) }

/-- The key absorbed. -/
theorem hk3_ok {s : State} (h : HK (H := H) s₀ s) (ua : UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀))
    (hsi : s.gpr .rsi = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (stA H s₀) []) :
    WP isa (.call H.updN H.updC) s fun t => HK (H := H) s₀ t ∧
      hH.SH.Repr t.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  refine upd_call hH ua (Nat.le_of_lt (s₀.gpr .rcx).isLt) fun s₈ a₈ r₈ =>
    ⟨h.call hp a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hsi
    rwa [List.nil_append, h.key] at this

/-- `finalize`'s arguments: the digest after the state. -/
theorem hk4_ok {s : State} (h : HK (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext ++ ([.mov .rsi (.reg .r13)] : List Instr) ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx (H.ext + H.S) ++ ([.mov .rcx (.reg .r15)] : List Instr))) s fun t =>
      HK (H := H) s₀ t ∧ FinArgs hH t (stA H s₀) (dgA H s₀) (scr s₀) ∧ t.gpr .rsi = s₀.gpr .rcx ∧
      hH.SH.Repr t.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  simp only [List.append_assoc]
  refine scr_ok h.r15 (by omega) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ _ _ => ?_
  refine scr_ok (by rw [u₁₀.other _ (by decide), u₉.other _ (by decide), h.r15]) (by omega)
    fun s₁₁ u₁₁ => wp_mov fun s₁₂ u₁₂ _ _ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.r13], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { rdi := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr]
      rdx := by rw [u₁₂.other _ (by decide), u₁₁.gpr]
      rcx := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.r15]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂ (by omega)
        · exact cov_part hp k₁₂ (by omega)
        · exact cov_low hp k₁₂ (by omega)
      st_o := Offset.disjoint _ (Or.inl (Nat.le_refl _)) (by omega) (by omega)
      st_sc := Offset.disjoint_base _ (by omega) (by omega)
      o_sc := Offset.disjoint_base _ (by omega) (by omega)
      stk_st := stk_part hp k₁₂ (by omega)
      stk_o := stk_part hp k₁₂ (by omega)
      stk_sc := by rw [k₁₂.rsp]; exact hp.stk_s.sub_right (Region.sub_prefix (by omega)) }

/-- The digest. -/
theorem hk5_ok {s : State} (h : HK (H := H) s₀ s) (fa : FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀))
    (hsi : s.gpr .rsi = s₀.gpr .rcx) (hr : hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => HK (H := H) s₀ t ∧
      bytesAt t.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  refine fin_call hH fa fun s₁₃ a₁₃ r₁₃ => ⟨h.call hp a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ hH.hDF]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .rcx).isLt)
      (by rw [hsi, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- What `hashKey` leaves: `init`'s arguments, with the digest as the key,
and our caller's registers. -/
structure Hashed (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  cs : ∀ r ∈ calleeSaved, t.gpr r = s₀.gpr r
  rdi : t.gpr .rdi = inn s₀
  rsi : t.gpr .rsi = out s₀
  r8 : t.gpr .r8 = scr s₀
  rdx : t.gpr .rdx = dgA H s₀
  rcx : t.gpr .rcx = BitVec.ofNat 64 H.D
  ret : t.mem.readW (s₀.gpr .rsp) 64 = s₀.mem.readW (s₀.gpr .rsp) 64
  dg : bytesAt t.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))

/-- The epilogue: `init`'s arguments, and our caller's registers back. -/
theorem hk6_ok {s : State} (h : HK (H := H) s₀ s)
    (hd : bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.block (([.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .r8 (.reg .r15)] : List Instr) ++
      VG.Impl.Hmac.Generic.X86_64.scr .rdx (H.ext + H.S) ++
      ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr) ++ H.restore)) s (Hashed hH s₀) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ _ _ => wp_mov fun s₂ u₂ _ _ => wp_mov fun s₃ u₃ _ _ => ?_
  have k₃ := ((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)
  refine scr_ok k₃.r15 (by omega) fun s₄ u₄ => wp_mov32i fun s₅ u₅ _ _ => ?_
  have k₅ := (k₃.upd u₄ (by decide)).upd u₅ (by decide)
  refine WP.mono (restore_ok H k₅.r15 hH.hW k₅.saved (by rw [k₅.wr]; exact ws_mem hp) (L := 8 * Wt)
    (by omega)) fun t ⟨hm, hrd, hwr, hcs, ho⟩ => ?_
  have g₅ : ∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r8 → r ≠ .rdx → r ≠ .rcx → s₅.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 h5 => by
      rw [u₅.other r h5, u₄.other r h4, u₃.other r h3, u₂.other r h2, u₁.other r h1]
  refine ⟨by rw [hrd, k₅.rd], by rw [hwr, k₅.wr], fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · rw [ho _ (by simp), k₅.rsp]
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
    · exact hcs _ (by simp)
  · rw [ho _ (by simp), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h.rbx]
  · rw [ho _ (by simp), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.r12]
  · rw [ho _ (by simp), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.r15]
  · rw [ho _ (by simp), u₅.other _ (by decide), u₄.gpr]
  · rw [ho _ (by simp), u₅.gpr, zx_ofNat (by have := hH.hDF; have := hH.hF; omega)]
  · rw [hm, k₅.ret]
  · rw [hm, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hd

theorem hashKey_ok {s : State} (hg : s.gpr = s₀.gpr) (hm : s.mem = s₀.mem) (hr : s.rd = s₀.rd)
    (hw : s.wr = s₀.wr) : WP isa H.hashKey s (Hashed hH s₀) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (pro_ok hH hp hg hm hr hw) fun s₁ k₁ => ?_)
  refine WP.seq (WP.seq (WP.mono (hk0_ok hH k₁) fun s₁' ⟨k₁', d₁⟩ =>
    WP.mono (hk1_ok hH hp k₁' d₁) fun s₂ ⟨k₂, r₂⟩ => ?_))
  refine WP.seq (WP.mono (hk2_ok hH hp k₂ r₂) fun s₃ ⟨k₃, a₃, i₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hH hp k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hH hp k₄ r₄) fun s₅ ⟨k₅, a₅, i₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hH hp k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact hk6_ok hH hp k₆ b₆

/-- After `hashKey`, `init` runs on the digest. -/
theorem ready_long {t : State} (h : Hashed hH s₀ t) : Ready (H := H) t := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hD := hp.hDB; have := hH.hDF; have := hH.hF; have := hH.hBB
  have hsp : t.gpr .rsp = s₀.gpr .rsp := h.cs _ (by simp [calleeSaved])
  have hk : keyR t = ⟨dgA H s₀, H.D⟩ := by
    simp only [keyR, kp, kl, h.rdx, h.rcx, toNat_ofNat_lt (show H.D < 2 ^ 64 by omega)]
  have hi : inR (H := H) t = inR (H := H) s₀ := by simp only [inR, inn, h.rdi]
  have ho : outR (H := H) t = outR (H := H) s₀ := by simp only [outR, out, h.rsi]
  have hs : scR (nw0 H) t = scR (nw0 H) s₀ := by simp only [scR, scr, h.r8]
  have hR : retR t = retR s₀ := by simp only [retR, hsp]
  have hK : stkR t = stkR s₀ := by simp only [stkR, hsp]
  have sub := ws_sub0 hp
  have dsub : Region.Sub ⟨dgA H s₀, H.D⟩ (wsR Wt s₀) := part_sub (by omega)
  have d0 : Region.Disjoint ⟨dgA H s₀, H.D⟩ (scR (nw0 H) s₀) := Offset.disjoint_base _ (by
    rw [← ext_eq]; omega) (by omega)
  refine ⟨⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fits0, hH.hBB, hH.hW,
    hH.hSB⟩, ?_, ?_⟩
  · show (t.gpr .rcx).toNat ≤ H.B
    rw [h.rcx, toNat_ofNat_lt (by omega)]; exact hD
  · show (inR (H := H) t).Disjoint (outR (H := H) t); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) t).Disjoint (scR (nw0 H) t); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) t).Disjoint (scR (nw0 H) t); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR t).Disjoint (inR (H := H) t); rw [hk, hi]; exact hp.i_s.symm.sub_left dsub
  · show (keyR t).Disjoint (outR (H := H) t); rw [hk, ho]; exact hp.o_s.symm.sub_left dsub
  · show (keyR t).Disjoint (scR (nw0 H) t); rw [hk, hs]; exact d0
  · show (retR t).Disjoint (inR (H := H) t); rw [hR, hi]; exact hp.ret_i
  · show (retR t).Disjoint (outR (H := H) t); rw [hR, ho]; exact hp.ret_o
  · show (retR t).Disjoint (scR (nw0 H) t); rw [hR, hs]; exact hp.ret_s.sub_right sub
  · show (stkR t).Disjoint (inR (H := H) t); rw [hK, hi]; exact hp.stk_i
  · show (stkR t).Disjoint (outR (H := H) t); rw [hK, ho]; exact hp.stk_o
  · show (stkR t).Disjoint (keyR t); rw [hK, hk]; exact hp.stk_s.sub_right dsub
  · show (stkR t).Disjoint (scR (nw0 H) t); rw [hK, hs]; exact hp.stk_s.sub_right sub
  · show (t.gpr .r8).toNat + 8 * nw0 H ≤ 2 ^ 64
    have := hp.nw; rw [h.r8]; rw [ext_eq] at he; omega
  · rw [hk, hi, ho, hs, h.rd, h.wr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_of_off (L := 8 * Wt) (by simp) (by omega)
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) (by rw [ext_eq] at he; show 8 * nw0 H ≤ 8 * Wt; omega)
  · rw [hi, ho, hs, h.wr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) (by rw [ext_eq] at he; show 8 * nw0 H ≤ 8 * Wt; omega)

end

/-! ## Correctness -/

section
variable {Wt : Nat} {s₀ : State}

/-- What `initAny` leaves: the calling convention's registers, and the
states for the key. -/
abbrev Post (s₀ s' : State) : Prop :=
  gprPreserved s₀ s' ∧
    hH.SH.Repr s'.mem (inn s₀) (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀))) ipad) ∧
    hH.SH.Repr s'.mem (out s₀) (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀))) opad)

/-- What the comparison leaves. -/
structure Cmp (s₀ s : State) : Prop where
  gpr : s.gpr = s₀.gpr
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  cf : s.cf = some (decide (kl s₀ < H.B + 1))

include hH in
theorem cmp_ok : WP isa (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 (H.B + 1)))]) s₀ (Cmp (H := H) s₀) := by
  have := hH.hBB
  exact wp_cmpi fun s g m rd wr cf _ => WP.block_nil ⟨g, m, rd, wr, by
    rw [cf, sx_ofNat (by omega), toNat_ofNat_lt (by omega)]⟩

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : H.B < k.length) (hl : (hH.SH.H.hash k).length ≤ H.B) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB
  simp only [blockKey, hB, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.B < (hH.SH.H.hash k).length by omega))]

theorem correct_gen (hS : kl s₀ ≤ H.B → Ready (H := H) s₀) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀) :
    WP isa H.initAny s₀ (Post hH s₀) := by
  unfold Hash.initAny
  refine WP.seq (WP.mono (cmp_ok hH) fun s₁ c => WP.seq ?_)
  refine WP.ite (decide (kl s₀ < H.B + 1)) (by simp only [eval, c.cf]) (fun hT => ?_) fun hF => ?_
  · have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT; omega
    have hg : ∀ r, s₁.gpr r = s₀.gpr r := fun r => by rw [c.gpr]
    refine WP.block_nil (WP.mono (init_ok hH ((hS hk).congr c.gpr c.rd c.wr)) fun s' ⟨⟨hcs, hret⟩, hi, ho⟩ =>
      ⟨⟨fun r hr => (hcs r hr).trans (hg r), by rw [← hg, hret, c.mem]⟩, ?_, ?_⟩)
    · simp only [inn, kp, kl, hg, c.mem] at hi; exact hi
    · simp only [out, kp, kl, hg, c.mem] at ho; exact ho
  · have hk : H.B < kl s₀ := by have := of_decide_eq_false hF; omega
    have hp := hL hk
    refine WP.mono (hashKey_ok hH hp c.gpr c.mem c.rd c.wr) fun s₂ h₂ =>
      WP.mono (init_ok hH (ready_long hH hp h₂)) fun s' ⟨⟨hcs, hret⟩, hi, ho⟩ => ?_
    have hsp : s₂.gpr .rsp = s₀.gpr .rsp := h₂.cs _ (by simp [calleeSaved])
    have hkey : bytesAt s₂.mem (kp s₂) (kl s₂) = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
      have hD := hp.hDB; have := hH.hBB
      simp only [kp, kl, h₂.rdx, h₂.rcx, toNat_ofNat_lt (show H.D < 2 ^ 64 by omega)]; exact h₂.dg
    have hlen : (hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))).length ≤ H.B := by
      rw [← h₂.dg, bytesAt_length]; exact hp.hDB
    have hk0 := blockKey_hash hH (by rw [bytesAt_length]; exact hk) hlen
    refine ⟨⟨fun r hr => (hcs r hr).trans (h₂.cs r hr), by rw [← hsp, hret, hsp, h₂.ret]⟩, ?_, ?_⟩
    · simp only [inn, h₂.rdi, hkey, hk0] at hi; exact hi
    · simp only [out, h₂.rsi, hkey, hk0] at ho; exact ho

end

/-! ## Constant time -/

/-- The block before `init`'s call in `hashKey`. -/
abbrev proBlock (H : Hash) : List Instr :=
  H.save ++ [.mov .rbx (.reg .rdi), .mov .r12 (.reg .rsi), .mov .r15 (.reg .r8), .mov .rbp (.reg .rdx),
    .mov .r13 (.reg .rcx)]

abbrev argU (H : Hash) : List Instr :=
  VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext ++ ([.mov32 .rsi (.imm 0), .mov .rdx (.reg .rbp),
    .mov .rcx (.reg .r13), .mov .r8 (.reg .r15)] : List Instr)

abbrev argF (H : Hash) : List Instr :=
  VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext ++ ([.mov .rsi (.reg .r13)] : List Instr) ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx (H.ext + H.S) ++ ([.mov .rcx (.reg .r15)] : List Instr)

abbrev epi (H : Hash) : List Instr :=
  ([.mov .rdi (.reg .rbx), .mov .rsi (.reg .r12), .mov .r8 (.reg .r15)] : List Instr) ++
    VG.Impl.Hmac.Generic.X86_64.scr .rdx (H.ext + H.S) ++
    ([.mov32 .rcx (.imm (BitVec.ofNat 32 H.D))] : List Instr) ++ H.restore

/-- The taint checks of the comparison and of `hashKey`'s pieces between its
calls. -/
structure Checks (H : Hash) : Prop where
  cmp : ∃ hc, (Taint.check taint (Taint.ofRegs Init.args)
    (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 (H.B + 1)))]) hc).isSome = true
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs Init.args) (.block (proBlock H)) hc).isSome = true
  argI : ∃ hc, (Taint.check taint (Taint.ofRegs hregs)
    (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext)) hc).isSome = true
  argU : ∃ hc, (Taint.check taint (Taint.ofRegs hregs) (.block (argU H)) hc).isSome = true
  argF : ∃ hc, (Taint.check taint (Taint.ofRegs hregs) (.block (argF H)) hc).isSome = true
  epi : ∃ hc, (Taint.check taint (Taint.ofRegs hregs) (.block (epi H)) hc).isSome = true

theorem rel_nil {P Q : State → State → Prop} (h : ∀ s s', P s s' → Q s s') : RelCT isa P (.block []) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, h _ _ hp⟩

section
variable {Wt : Nat} {s₀ s₀' : State} (hq : Init.PubEq s₀ s₀')

include hq in
theorem hk_agree {s s' : State} (h : HK (H := H) s₀ s) (h' : HK (H := H) s₀' s') :
    ∀ r ∈ hregs, s.gpr r = s'.gpr r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [h.rbx, h'.rbx, inn, inn, hq.rdi]
  · rw [h.rbp, h'.rbp, kp, kp, hq.rdx]
  · rw [h.r12, h'.r12, out, out, hq.rsi]
  · rw [h.r13, h'.r13, hq.rcx]
  · rw [h.r15, h'.r15, scr, scr, hq.r8]
  · rw [h.rsp, h'.rsp, hq.rsp]

variable (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
include hp hp' hq

theorem hashKey_rel (hca : Checks H) :
    RelCT isa (fun s s' => Cmp (H := H) s₀ s ∧ Cmp (H := H) s₀' s') H.hashKey
      fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' := by
  have eS : stA H s₀' = stA H s₀ := by simp only [stA, A, scr, hq.r8]
  have eD : dgA H s₀' = dgA H s₀ := by simp only [dgA, A, scr, hq.r8]
  have eK : kp s₀' = kp s₀ := hq.rdx.symm
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.rcx]
  have e8 : scr s₀' = scr s₀ := hq.r8.symm
  unfold Hash.hashKey
  -- The prologue.
  have pro : RelCT isa (fun s s' => Cmp (H := H) s₀ s ∧ Cmp (H := H) s₀' s') (.block (proBlock H))
      fun s s' => HK (H := H) s₀ s ∧ HK (H := H) s₀' s' :=
    rel_taint Init.args (fun s s' c c' r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rw [c.gpr, c'.gpr]
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hca.pro
      (fun _ c => pro_ok hH hp c.gpr c.mem c.rd c.wr) (fun _ c => pro_ok hH hp' c.gpr c.mem c.rd c.wr)
  -- `init`'s call.
  have i0 : RelCT isa (fun s s' => HK (H := H) s₀ s ∧ HK (H := H) s₀' s')
      (.block (VG.Impl.Hmac.Generic.X86_64.scr .rdi H.ext))
      fun s s' => (HK (H := H) s₀ s ∧ s.gpr .rdi = stA H s₀) ∧ (HK (H := H) s₀' s' ∧ s'.gpr .rdi = stA H s₀) :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h h') hca.argI (fun _ h => hk0_ok hH h)
      (fun _ h => WP.mono (hk0_ok hH h) fun _ ⟨k, d⟩ => ⟨k, d.trans eS⟩)
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  have i1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ s.gpr .rdi = stA H s₀) ∧
      (HK (H := H) s₀' s' ∧ s'.gpr .rdi = stA H s₀)) (.call H.initN H.initC)
      fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀) []) :=
    rel_wp (init_rel hH (st := stA H s₀) fun s s' ⟨⟨k, d⟩, ⟨k', d'⟩⟩ =>
        ⟨d, d', Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp k (by omega),
          Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← eS]; exact cov_part hp' k' (by omega),
          stk_part hp k (by omega), by rw [← eS]; exact stk_part hp' k' (by omega),
          by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun _ ⟨k, d⟩ => hk1_ok hH hp k d)
      (fun _ ⟨k, d⟩ => WP.mono (hk1_ok hH hp' k (d.trans eS.symm)) fun _ ⟨k, r⟩ => ⟨k, eS ▸ r⟩)
  -- `update`'s call.
  have u0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
      (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀) [])) (.block (argU H))
      fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s'.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (stA H s₀) []) :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argU (fun _ ⟨k, r⟩ => hk2_ok hH hp k r)
      (fun _ ⟨k, r⟩ => WP.mono (hk2_ok hH hp' k (eS ▸ r)) fun _ ⟨k, a, i, r⟩ =>
        ⟨k, eS ▸ eK ▸ e8 ▸ eL ▸ a, i, eS ▸ r⟩)
  have u1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s'.gpr .rsi = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (stA H s₀) [])) (.call H.updN H.updC)
      fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_wp (upd_rel hH fun s s' ⟨⟨k, a, i, _⟩, ⟨k', a', i', _⟩⟩ =>
        ⟨a, a', by rw [i, i'], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun _ ⟨k, a, i, r⟩ => hk3_ok hH hp k a i r)
      (fun _ ⟨k, a, i, r⟩ => hk3_ok hH hp' k (eS.symm ▸ eK.symm ▸ e8.symm ▸ eL.symm ▸ a) i (eS.symm ▸ r))
  -- `finalize`'s call.
  have f0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.block (argF H))
      fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧ s.gpr .rsi = s₀.gpr .rcx ∧
          hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧ s'.gpr .rsi = s₀'.gpr .rcx ∧
          hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argF (fun _ ⟨k, r⟩ => hk4_ok hH hp k r)
      (fun _ ⟨k, r⟩ => hk4_ok hH hp' k r)
  have f1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧
          s.gpr .rsi = s₀.gpr .rcx ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧ s'.gpr .rsi = s₀'.gpr .rcx ∧
          hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.call H.finN H.finC)
      fun s s' => (HK (H := H) s₀ s ∧
          bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (dgA H s₀') H.D = hH.SH.H.hash (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_wp (fin_rel hH (st := stA H s₀) (o := dgA H s₀) (sc := scr s₀) fun s s' ⟨⟨k, a, i, _⟩, ⟨k', a', i', _⟩⟩ =>
        ⟨a, eS ▸ eD ▸ e8 ▸ a', by rw [i, i', hq.rcx], by rw [k.rsp, k'.rsp, hq.rsp]⟩)
      (fun _ ⟨k, a, i, r⟩ => hk5_ok hH hp k a i r)
      (fun _ ⟨k, a, i, r⟩ => hk5_ok hH hp' k a i r)
  -- The epilogue.
  have ep : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧
          bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (dgA H s₀') H.D = hH.SH.H.hash (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.block (epi H)) fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.epi (fun _ ⟨k, d⟩ => hk6_ok hH hp k d)
      (fun _ ⟨k, d⟩ => hk6_ok hH hp' k d)
  exact pro.seq ((i0.seq i1).seq (u0.seq (u1.seq (f0.seq (f1.seq ep)))))

end

section
variable {Wt : Nat} {s₀ s₀' : State} (hc : Init.Checks H) (hq : Init.PubEq s₀ s₀')

/-- Two states from which `init` runs, with the same public arguments. -/
abbrev RR (s s' : State) : Prop := Ready (H := H) s ∧ Ready (H := H) s' ∧ Init.PubEq s s'

include hH hc in
theorem init_rel : RelCT isa (RR (H := H)) H.init fun _ _ => True :=
  RelCT.of_narrow (Ready (H := H)) (nar H) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ h _ _ he => init_exec h he)
    (fun _ h => let ⟨t, s', he, _⟩ := Init.correct hH h.pre; ⟨t, s', he⟩)
    fun _ _ _ _ _ _ ⟨_, _, ⟨r₁, r₂, pq⟩, e₁, e₂⟩ x₁ x₂ =>
      Init.ct hH hc r₁.pre r₂.pre ⟨pq.rdi, pq.rsi, pq.rdx, pq.rcx, pq.r8, pq.rsp⟩ _ _ _ _ _ _ ⟨e₁, e₂⟩ x₁ x₂

include hq in
theorem hashed_rr {s s' : State} (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
    (h : Hashed hH s₀ s) (h' : Hashed hH s₀' s') : RR (H := H) s s' :=
  ⟨ready_long hH hp h, ready_long hH hp' h', by rw [h.rdi, h'.rdi, inn, inn, hq.rdi],
    by rw [h.rsi, h'.rsi, out, out, hq.rsi], by rw [h.rdx, h'.rdx, dgA, dgA, A, A, scr, scr, hq.r8],
    by rw [h.rcx, h'.rcx], by rw [h.r8, h'.r8, scr, scr, hq.r8],
    by rw [h.cs _ (by simp [calleeSaved]), h'.cs _ (by simp [calleeSaved]), hq.rsp]⟩

include hH hc hq in
theorem ct_gen (hca : Checks H) (hS : kl s₀ ≤ H.B → Ready (H := H) s₀) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀)
    (hS' : kl s₀' ≤ H.B → Ready (H := H) s₀') (hL' : H.B < kl s₀' → PreA (H := H) Wt s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initAny fun _ _ => True := by
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.rcx]
  unfold Hash.initAny
  have cmp : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀')
      (.block [.alu .cmp .rcx (.imm (BitVec.ofNat 32 (H.B + 1)))])
      fun s s' => Cmp (H := H) s₀ s ∧ Cmp (H := H) s₀' s' :=
    rel_taint Init.args (fun s s' e e' r hr => by
        subst e e'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
        · exact hq.rdi
        · exact hq.rsi
        · exact hq.rdx
        · exact hq.rcx
        · exact hq.r8
        · exact hq.rsp) hca.cmp
      (fun _ e => by subst e; exact cmp_ok hH) (fun _ e => by subst e; exact cmp_ok hH)
  refine cmp.seq (RelCT.seq (R := RR (H := H)) ?_ (init_rel hH hc))
  refine RelCT.ite (fun s s' ⟨c, c'⟩ => by simp only [eval, c.cf, c'.cf, eL]) ?_ ?_
  · refine rel_nil fun s s' ⟨⟨c, c'⟩, hT⟩ => ?_
    simp only [eval, c.cf, Option.some.injEq] at hT
    have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT; omega
    exact ⟨(hS hk).congr c.gpr c.rd c.wr, (hS' (eL ▸ hk)).congr c'.gpr c'.rd c'.wr,
      by rw [c.gpr, c'.gpr]; exact hq.rdi, by rw [c.gpr, c'.gpr]; exact hq.rsi,
      by rw [c.gpr, c'.gpr]; exact hq.rdx, by rw [c.gpr, c'.gpr]; exact hq.rcx,
      by rw [c.gpr, c'.gpr]; exact hq.r8, by rw [c.gpr, c'.gpr]; exact hq.rsp⟩
  · refine RelCT.mono (P := fun s s' => (Cmp (H := H) s₀ s ∧ Cmp (H := H) s₀' s') ∧ H.B < kl s₀) ?_
      (fun s s' ⟨⟨c, c'⟩, hF⟩ => ⟨⟨c, c'⟩, by
        simp only [eval, c.cf, Option.some.injEq] at hF
        have := of_decide_eq_false hF; omega⟩) fun _ _ h => h
    refine RelCT.exists_ (P := fun (_ : H.B < kl s₀) s s' => Cmp (H := H) s₀ s ∧ Cmp (H := H) s₀' s') ?_
      |>.mono (fun s s' ⟨h, hk⟩ => ⟨hk, h⟩) fun _ _ h => h
    intro hk
    have hp := hL hk
    have hp' := hL' (eL ▸ hk)
    exact (hashKey_rel hH hq hp hp' hca).mono (fun _ _ h => h) fun _ _ ⟨h, h'⟩ => hashed_rr hH hq hp hp' h h'

end

/-! ## Verified -/

/-- `initAny`'s working space at its end holds the streaming state and the
digest of a long key; it is the shared contract's. -/
theorem verifiedAny {Wt : Nat} (hc : Init.Checks H) (hca : Checks H) (hfit : H.ext + H.S + H.F ≤ 8 * Wt)
    (hDB : H.D ≤ H.B) (hmx : H.initAny.allInstrs (fun i => !loadsMxcsr i) = true)
    (hsat : ∃ s, (initAnyG hH.SH Wt).pre s) :
    Verified X86_64.target H.initAny (initAnyG hH.SH Wt) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · have hp := preA_of hH hs hfit hDB
    obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (Wt := Wt) (ready_short hH hp) (fun _ => hp)
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · have hp₁ := preA_of hH h₁ hfit hDB
    have hp₂ := preA_of hH h₂ hfit hDB
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (ct_gen hH hc ⟨p1, p2, p3, p4, p5, p6⟩ hca (ready_short hH hp₁) (fun _ => hp₁) (ready_short hH hp₂)
      (fun _ => hp₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `init`'s precondition, with any working space at least as large as its
own, makes a `Ready` state. -/
theorem ready_of_pre {sc : Nat} {s₀ : State} (hp : Pre (H := H) sc s₀) : Ready (H := H) s₀ := by
  have hf := hp.fits
  have sub : Region.Sub (scR (nw0 H) s₀) (scR sc s₀) := Region.sub_prefix (by simp only [nw0]; omega)
  refine ⟨⟨hp.kl_le, rfl, rfl, hp.i_o, hp.i_s.sub_right sub, hp.o_s.sub_right sub, hp.k_i, hp.k_o,
    hp.k_s.sub_right sub, hp.ret_i, hp.ret_o, hp.ret_s.sub_right sub, hp.stk_i, hp.stk_o, hp.stk_k,
    hp.stk_s.sub_right sub, by show (scr s₀).toNat + 8 * nw0 H ≤ 2 ^ 64; have := hp.nw; simp only [nw0]; omega,
    fits0, hp.hB, hp.hW, hp.hS⟩, ?_, ?_⟩
  · rw [hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_of_self (r := keyR s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := scR sc s₀) (by simp) (by show 8 * nw0 H ≤ 8 * sc; simp only [nw0]; omega)
  · rw [hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := scR sc s₀) (by simp) (by show 8 * nw0 H ≤ 8 * sc; simp only [nw0]; omega)

/-- `initAny` is verified against `init`'s contract too, for a key of at most
a block: it runs `init`. -/
theorem verifiedShort {sc : Nat} (hc : Init.Checks H) (hca : Checks H) (hfit : H.buf + 2 * H.B ≤ 8 * sc)
    (hmx : H.initAny.allInstrs (fun i => !loadsMxcsr i) = true) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified X86_64.target H.initAny (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · have hp := Init.pre_of hH sc hs hfit
    obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (Wt := sc) (fun _ => ready_of_pre hp)
      (fun h => absurd hp.kl_le (by omega))
    exact ⟨t, s', he, abiPreserved_of_exec hmx he hg, hpost⟩
  · have hp₁ := Init.pre_of hH sc h₁ hfit
    have hp₂ := Init.pre_of hH sc h₂ hfit
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (ct_gen hH (Wt := sc) hc ⟨p1, p2, p3, p4, p5, p6⟩ hca (fun _ => ready_of_pre hp₁)
      (fun h => absurd hp₁.kl_le (by omega)) (fun _ => ready_of_pre hp₂) (fun h => absurd hp₂.kl_le (by omega))
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.X86_64.InitAny

namespace VG.Proof.Hmac.Generic.X86_64.Instances

open VG.X86_64
open VG.Proof.Hmac.Generic.X86_64

/-- `initAnyG` implies the shared contract for any hash function and
scratch space (`generic_implies`), given that the shared contract is
satisfiable. -/
theorem initAnyImp (S : Spec.Hmac.StreamingHash) (W : Nat)
    (h : ∃ s, (Spec.Hmac.initAnyKeyContract S W X86_64.abi 16).pre s) :
    (initAnyG S W).Implies (Spec.Hmac.initAnyKeyContract S W X86_64.abi 16) := by
  generic_implies [
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, initAnyG, X86_64.abi, X86_64.argRegs] using h

/-- The checks do not look at the functions `initAny` calls. -/
theorem InitAny.Checks.of_eq {H H' : Impl.Hmac.Generic.X86_64.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S)
    (hD : H.D = H'.D) (hW : H.W = H'.W) (h : InitAny.Checks H) : InitAny.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hD hW; subst hB hS hD hW
  exact ⟨h.cmp, h.pro, h.argI, h.argU, h.argF, h.epi⟩

end VG.Proof.Hmac.Generic.X86_64.Instances
