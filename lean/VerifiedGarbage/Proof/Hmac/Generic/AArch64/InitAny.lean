import VerifiedGarbage.Proof.Hmac.Generic.AArch64.Instances
import VerifiedGarbage.Proof.Framework.Narrow

/-!
# HMAC over any streaming hash function on AArch64: `init` for a key of any length

Untrusted: everything here is checked by Lean. As on x86-64
(`Proof/Hmac/Generic/X86_64/InitAny.lean`): `initAny` tests `key_len`
(`key_len >> log₂ B`, then `key_len - B`); a longer key is replaced by its
digest (`hashKey`, with the hash function's streaming functions, in
`scratch` after `init`'s buffers), and `init` (`Init.lean`) runs on the key
or the digest, from a state permitting more than its narrowed one
(`WP.of_narrow`, `RelCT.of_narrow`).

`initAny` is verified against `initAnyG`, the contract for a key of any
length, and also against `initG`, for a key of at most a block, with the
working space `init` has: PBKDF2's `pbkdf2` calls it so.
-/

namespace VG.Proof.Hmac.Generic.AArch64

open VG.AArch64
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length:
`VG.Spec.Hmac.initAnyKeyContract`. -/
def initAnyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨s.gpr .x0, S.stateBytes⟩
    let outer : Region := ⟨s.gpr .x1, S.stateBytes⟩
    let key : Region := ⟨s.gpr .x2, (s.gpr .x3).toNat⟩
    let scratch : Region := ⟨s.gpr .x4, 8 * W⟩
    s.rd = [key] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    16 ≤ s.sp.toNat ∧ (stk s).Disjoint inner ∧ (stk s).Disjoint outer ∧ (stk s).Disjoint key ∧
    (stk s).Disjoint scratch ∧ (s.gpr .x4).toNat + 8 * W ≤ 2 ^ 64
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (s.gpr .x2) (s.gpr .x3).toNat)
    S.Repr s'.mem (s.gpr .x0) (xorPad k0 ipad) ∧ S.Repr s'.mem (s.gpr .x1) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.gpr .x0 = s₂.gpr .x0 ∧ s₁.gpr .x1 = s₂.gpr .x1 ∧ s₁.gpr .x2 = s₂.gpr .x2 ∧
    s₁.gpr .x3 = s₂.gpr .x3 ∧ s₁.gpr .x4 = s₂.gpr .x4 ∧ s₁.sp = s₂.sp

end VG.Proof.Hmac.Generic.AArch64

namespace VG.Proof.Hmac.Generic.AArch64.InitAny

open VG.AArch64
open VG.Impl.Hmac.Generic.AArch64 (Hash)
open VG.Impl.Sha256.AArch64.Stream (mov)
open VG.Proof.Hmac.Generic.AArch64
open VG.Proof.Hmac.Generic.AArch64.Init (Pre inn out kp kl scr inR outR keyR scR stkR untouched)
open VG.Proof.Hmac.Generic.Common (covers_one sub_of_off sub_of_self bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.MdStream.AArch64 (toNat_ofNat_lt Upd wp_mov wp_movz wp_addImm wp_subImm wp_lsr eval_zero sub_beq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash}

/-! ## Sizes -/

/-- The words of working space `init` gets: its buffers, rounded up. -/
abbrev nw0 (H : Hash) : Nat := (H.buf + 2 * H.B + 7) / 8

theorem ext_eq : H.ext = 8 * nw0 H := rfl

theorem fits0 : H.buf + 2 * H.B ≤ 8 * nw0 H := by simp only [nw0]; omega

theorem save_le_ext : 8 * H.W + 56 ≤ H.ext := by
  have := fits0 (H := H); simp only [Hash.buf] at this; rw [ext_eq]; omega

theorem ext_lt (hH : HashOK H) : H.ext + H.S + H.F < 4096 := by
  have := hH.hW; have := hH.hBB; have := hH.hSB; have := hH.hF
  simp only [ext_eq, nw0, Hash.buf]; omega

/-- A shift right leaves zero exactly when the value is below the power of two. -/
theorem shr_beq_zero (x : BitVec 64) (k : Nat) : (x >>> k == 0) = decide (x.toNat < 2 ^ k) := by
  have hk := Nat.two_pow_pos k
  have e : (x >>> k).toNat = x.toNat / 2 ^ k := by
    rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  by_cases h : x.toNat < 2 ^ k
  · have : x >>> k = 0 := BitVec.eq_of_toNat_eq (by rw [e, Nat.div_eq_of_lt h]; rfl)
    simp [this, h]
  · have hne : (x >>> k == 0) = false := by
      rw [beq_eq_false_iff_ne]
      intro h0
      have h1 : x.toNat / 2 ^ k = 0 := by rw [← e, h0]; rfl
      have h2 : 2 ^ k ≤ x.toNat := by omega
      have := Nat.div_le_div_right (c := 2 ^ k) h2
      rw [Nat.div_self hk] at this
      omega
    rw [hne]; simp [h]

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
  sp16 : 16 ≤ s₀.sp.toNat
  stk_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  stk_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  stk_k : (stkR s₀).Disjoint (keyR s₀)
  stk_s : (stkR s₀).Disjoint (wsR Wt s₀)
  nw : (scr s₀).toNat + 8 * Wt ≤ 2 ^ 64
  fits : H.ext + H.S + H.F ≤ 8 * Wt
  hDB : H.D ≤ H.B
  pow : 2 ^ Nat.log2 H.B = H.B

theorem preA_of (hH : HashOK H) {Wt : Nat} {s₀ : State} (h : (initAnyG hH.SH Wt).pre s₀)
    (hfit : H.ext + H.S + H.F ≤ 8 * Wt) (hDB : H.D ≤ H.B) (hpow : 2 ^ Nat.log2 H.B = H.B) :
    PreA (H := H) Wt s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  have hS := hH.hS
  simp only [hS] at *
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hfit, hDB, hpow⟩

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

variable (hH : HashOK H)

/-- The trace of `init` from a `Ready` state is that from its narrowed state. -/
theorem init_exec {s : State} (hr : Ready (H := H) s) {t : List Leak} {s₁ : State}
    (he : Exec isa H.init (nar H s) t s₁) : Exec isa H.init s t (s₁.withRegions s.rd s.wr) := by
  have := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa using hr.cr) (by simpa using hr.cw)
  simpa using this

/-- `init` from a `Ready` state. -/
theorem init_ok {s : State} (hr : Ready (H := H) s) :
    WP isa H.init s fun s' => abiPreserved s s' ∧
      hH.SH.Repr s'.mem (inn s) (xorPad (blockKey hH.SH.H (bytesAt s.mem (kp s) (kl s))) ipad) ∧
      hH.SH.Repr s'.mem (out s) (xorPad (blockKey hH.SH.H (bytesAt s.mem (kp s) (kl s))) opad) := by
  have h := Init.correct hH hr.pre
  refine WP.mono (WP.of_narrow (n := nar H s) (fun s₁ : State => s₁.withRegions s.rd s.wr)
    (fun t s₁ he => init_exec hr he) h) fun s' hs' => ?_
  obtain ⟨s₁, rfl, hg, hq⟩ := hs'
  exact ⟨hg, hq⟩

/-! ## `Ready` states -/

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
/-- A state with `init`'s arguments, for a key in the key's region or in
`scratch` after `init`'s working space, of at most a block. -/
theorem ready_at {t : State} (hx0 : t.gpr .x0 = inn s₀) (hx1 : t.gpr .x1 = out s₀) (hx4 : t.gpr .x4 = scr s₀)
    (hsp : t.sp = s₀.sp) (hrd : t.rd = s₀.rd) (hwr : t.wr = s₀.wr) (hkl : kl t ≤ H.B)
    (hk : keyR t = keyR s₀ ∨ ∃ o, keyR t = ⟨A s₀ o, kl t⟩ ∧ H.ext ≤ o ∧ o + kl t ≤ 8 * Wt) :
    Ready (H := H) t := by
  have he := ext_le hp; have hL := nw_lt hp
  have hi : inR (H := H) t = inR (H := H) s₀ := by simp only [inR, inn, hx0]
  have ho : outR (H := H) t = outR (H := H) s₀ := by simp only [outR, out, hx1]
  have hs : scR (nw0 H) t = scR (nw0 H) s₀ := by simp only [scR, scr, hx4]
  have hK : stkR t = stkR s₀ := by simp only [stkR, hsp]
  have sub := ws_sub0 hp
  have h8 : 8 * nw0 H ≤ 8 * Wt := by rw [← ext_eq]; omega
  -- The key's region: disjoint from the others, and within the state's.
  have kfacts : (keyR t).Disjoint (inR (H := H) s₀) ∧ (keyR t).Disjoint (outR (H := H) s₀) ∧
      (keyR t).Disjoint (scR (nw0 H) s₀) ∧ (stkR s₀).Disjoint (keyR t) ∧
      ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, (keyR t).base = r'.base + BitVec.ofNat 64 off ∧ off + (keyR t).len ≤ r'.len := by
    rcases hk with e | ⟨o, e, h₁, h₂⟩ <;> rw [e]
    · exact ⟨hp.k_i, hp.k_o, hp.k_s.sub_right sub, hp.stk_k,
        sub_of_self (r := keyR s₀) (List.mem_append_left _ (by rw [hp.rd]; simp)) (Nat.le_refl _)⟩
    · have dsub : Region.Sub ⟨A s₀ o, kl t⟩ (wsR Wt s₀) := part_sub h₂
      exact ⟨hp.i_s.symm.sub_left dsub, hp.o_s.symm.sub_left dsub,
        Offset.disjoint_base _ (by rw [← ext_eq]; omega) (by omega), hp.stk_s.sub_right dsub,
        sub_of_off (List.mem_append_right _ (ws_mem hp)) h₂⟩
  obtain ⟨k_i, k_o, k_s, stk_k, kc⟩ := kfacts
  refine ⟨⟨hkl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fits0, hH.hBB, hH.hW, hH.hSB⟩,
    ?_, ?_⟩
  · show (inR (H := H) t).Disjoint (outR (H := H) t); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) t).Disjoint (scR (nw0 H) t); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) t).Disjoint (scR (nw0 H) t); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR t).Disjoint (inR (H := H) t); rw [hi]; exact k_i
  · show (keyR t).Disjoint (outR (H := H) t); rw [ho]; exact k_o
  · show (keyR t).Disjoint (scR (nw0 H) t); rw [hs]; exact k_s
  · show 16 ≤ t.sp.toNat; rw [hsp]; exact hp.sp16
  · show (stkR t).Disjoint (inR (H := H) t); rw [hK, hi]; exact hp.stk_i
  · show (stkR t).Disjoint (outR (H := H) t); rw [hK, ho]; exact hp.stk_o
  · show (stkR t).Disjoint (keyR t); rw [hK]; exact stk_k
  · show (stkR t).Disjoint (scR (nw0 H) t); rw [hK, hs]; exact hp.stk_s.sub_right sub
  · show (t.gpr .x4).toNat + 8 * nw0 H ≤ 2 ^ 64
    have := hp.nw; rw [hx4]; omega
  · rw [hi, ho, hs, hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact kc
      · exact sub_of_self (r := inR (H := H) s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (List.mem_append_right _ (ws_mem hp)) h8
  · rw [hi, ho, hs, hwr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) h8

end

/-! ## Hashing a longer key -/

/-- What `hashKey` keeps, from its prologue on. -/
structure HK (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  x19 : s.gpr .x19 = inn s₀
  x20 : s.gpr .x20 = out s₀
  x21 : s.gpr .x21 = kp s₀
  x22 : s.gpr .x22 = s₀.gpr .x3
  x23 : s.gpr .x23 = scr s₀
  cs : ∀ r ∈ untouched, s.gpr r = s₀.gpr r
  saved : SavedRegs H (scr s₀) s₀ s.mem
  key : bytesAt s.mem (kp s₀) (kl s₀) = bytesAt s₀.mem (kp s₀) (kl s₀)

/-- The registers `HK` fixes. -/
abbrev hregs : List Reg := [.x19, .x20, .x21, .x22, .x23, .x25, .x26, .x27, .x28]

theorem hregs_pres : ∀ r ∈ hregs, r ∈ preserved ∧ r ≠ .x30 := by decide

section
variable {Wt : Nat} {s₀ : State}

theorem HK.keep {s s' : State} (h : HK (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ hregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hk : ∀ r ∈ rs, (keyR s₀).Disjoint r) : HK (H := H) s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.x19,
    (hg _ (by simp)).trans h.x20, (hg _ (by simp)).trans h.x21, (hg _ (by simp)).trans h.x22,
    (hg _ (by simp)).trans h.x23, fun r hr => (hg r (by revert r hr; decide)).trans (h.cs r hr),
    h.saved.frame H hf hs, (bytes_keep hf hk (Nat.le_of_lt (s₀.gpr .x3).isLt)).trans h.key⟩

theorem HK.upd {s s' : State} (h : HK (H := H) s₀ s) {d : Reg} {v : BitVec 64} (u : Upd s s' d v)
    (hd : d ∉ hregs) : HK (H := H) s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

variable (hp : PreA (H := H) Wt s₀)
include hp

/-- A region a call writes: the working space of the functions we call, or
a part of `scratch` after the save area. -/
theorem HK.call {s s' : State} (h : HK (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨scr s₀, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = ⟨A s₀ o, k⟩ ∧ 8 * H.W + 56 ≤ o ∧ o + k ≤ 8 * Wt) : HK (H := H) s₀ s' := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have f := ha.frame
  rw [h.sp] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (hregs_pres r hr).1 (hregs_pres r hr).2) f ?_ ?_
  all_goals intro r hr; rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact Offset.disjoint_base _ hk (by omega)
    · exact Offset.disjoint _ (Or.inl h₁) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.stk_s.sub_right ssub).symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact hp.k_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.k_s.sub_right (part_sub h₂)
  · simp only [List.mem_singleton] at hr; subst hr
    exact hp.stk_k.symm

/-- The prologue: our caller's registers saved, ours set, and `init`'s
argument. -/
theorem pro_ok (hH : HashOK H) {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    WP isa (.block (H.save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4,
      .addImm .x .x0 .x23 H.ext])) s fun t => HK (H := H) s₀ t ∧ t.gpr .x0 = A s₀ H.ext := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  refine save_ok H (scr := scr s₀) (by rw [hg _ (by decide)]) (Nat.le_trans hH.hW (by decide))
    (by rw [hw]; exact ws_mem hp) (L := 8 * Wt) (by omega) fun s₁ g₁ rd₁ wr₁ sp₁ f₁ sv₁ => ?_
  refine wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_addImm (by omega) fun s₇ u₇ => WP.block_nil ?_
  have hm₇ : s₇.mem = s₁.mem := by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem]
  have g₀ : ∀ r, r ≠ .x9 → s₁.gpr r = s₀.gpr r := fun r h => by rw [g₁, hg r h]
  have x23 : s₆.gpr .x23 = scr s₀ := by rw [u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
    u₃.other _ (by decide), u₂.other _ (by decide), g₀ _ (by decide)]
  refine ⟨⟨by rw [u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁, hr],
    by rw [u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁, hw],
    by rw [u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁, hsp], ?_, ?_, ?_, ?_,
    by rw [u₇.other _ (by decide), x23], ?_, ?_, ?_⟩, by rw [u₇.gpr, x23]⟩
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr, g₀ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.gpr, u₂.other _ (by decide), g₀ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), u₂.other _ (by decide), g₀ _ (by decide)]
  · rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), g₀ _ (by decide)]
  · intro r hr
    have hr' : r ≠ .x0 ∧ r ≠ .x19 ∧ r ≠ .x20 ∧ r ≠ .x21 ∧ r ≠ .x22 ∧ r ≠ .x23 ∧ r ≠ .x9 := by
      revert r hr; decide
    rw [u₇.other _ hr'.1, u₆.other _ hr'.2.2.2.2.2.1, u₅.other _ hr'.2.2.2.2.1, u₄.other _ hr'.2.2.2.1,
      u₃.other _ hr'.2.2.1, u₂.other _ hr'.2.1, g₀ _ hr'.2.2.2.2.2.2]
  · rw [hm₇]
    exact ⟨by rw [sv₁.x19, hg _ (by decide)], by rw [sv₁.x20, hg _ (by decide)],
      by rw [sv₁.x21, hg _ (by decide)], by rw [sv₁.x22, hg _ (by decide)],
      by rw [sv₁.x24, hg _ (by decide)], by rw [sv₁.x30, hg _ (by decide)],
      by rw [sv₁.x23, hg _ (by decide)]⟩
  · rw [hm₇, ← hm]
    exact bytes_keep f₁ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact hp.k_s.sub_right (part_sub (by omega))) (Nat.le_of_lt (s₀.gpr .x3).isLt)

/-- The streaming state of the key, and the digest. -/
abbrev stA (H : Hash) (s₀ : State) : Addr := A s₀ H.ext
abbrev dgA (H : Hash) (s₀ : State) : Addr := A s₀ (H.ext + H.S)

theorem stk_part {s : State} (h : HK (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ 8 * Wt) :
    (below s.sp 16).Disjoint ⟨A s₀ o, n⟩ := by
  rw [h.sp]; exact hp.stk_s.sub_right (part_sub hon)

theorem cov_part {s : State} (h : HK (H := H) s₀ s) {o n : Nat} (hon : o + n ≤ 8 * Wt) :
    ∃ r' ∈ s.wr, ∃ off, (⟨A s₀ o, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨A s₀ o, n⟩ : Region).len ≤ r'.len :=
  sub_of_off (rs := s.wr) (by rw [h.wr]; exact ws_mem hp) hon

theorem cov_low {s : State} (h : HK (H := H) s₀ s) {n : Nat} (hn : n ≤ 8 * Wt) :
    ∃ r' ∈ s.wr, ∃ off, (⟨scr s₀, n⟩ : Region).base = r'.base + BitVec.ofNat 64 off ∧
      off + (⟨scr s₀, n⟩ : Region).len ≤ r'.len :=
  sub_of_self (rs := s.wr) (r := wsR Wt s₀) (by rw [h.wr]; exact ws_mem hp) hn

/-- The streaming state of the key, started. -/
theorem hk1_ok {s : State} (h : HK (H := H) s₀ s) (hd : s.gpr .x0 = stA H s₀) :
    WP isa (.call H.initN H.initC) s fun t => HK (H := H) s₀ t ∧ VecKept s t ∧
      hH.SH.Repr t.mem (stA H s₀) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  exact init_call hH (st := stA H s₀) hd (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp h (by omega)) fun s₂ a₂ r₂ =>
      ⟨h.call hp a₂ fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact .inr ⟨_, _, rfl, hx, by omega⟩, a₂.vec, r₂⟩

/-- `update`'s arguments: the key. -/
theorem hk2_ok {s : State} (h : HK (H := H) s₀ s) (hr : hH.SH.Repr s.mem (stA H s₀) []) :
    WP isa (.block [.addImm .x .x0 .x23 H.ext, .movz .x .x1 0 0, mov .x2 .x21, mov .x3 .x22, mov .x4 .x23]) s
      fun t => HK (H := H) s₀ t ∧ UpdArgs hH t (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
        t.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr t.mem (stA H s₀) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  refine wp_addImm (by omega) fun s₃ u₃ => wp_movz fun s₄ u₄ => wp_mov fun s₅ u₅ =>
    wp_mov fun s₆ u₆ => wp_mov fun s₇ u₇ => WP.block_nil ?_
  have k₇ := ((((h.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆ (by decide)).upd u₇
    (by decide)
  refine ⟨k₇, ?_, by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr]; rfl,
    by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]; exact hr⟩
  exact
    { x0 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
          u₄.other _ (by decide), u₃.gpr, h.x23]
      x2 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
          u₃.other _ (by decide), h.x21]
      x3 := by rw [u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.x22]
      x4 := by rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
          u₃.other _ (by decide), h.x23]
      cd := covers_one (List.mem_append_left _ (by rw [k₇.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact cov_part hp k₇ (by omega)
        · exact cov_low hp k₇ (by omega)
      st_sc := Offset.disjoint_base _ (by omega) (by omega)
      d_st := hp.k_s.sub_right (part_sub (by omega))
      d_sc := hp.k_s.sub_right (Region.sub_prefix (by omega))
      sp16 := by rw [k₇.sp]; exact hp.sp16
      stk_st := stk_part hp k₇ (by omega)
      stk_d := by rw [k₇.sp]; exact hp.stk_k
      stk_sc := by rw [k₇.sp]; exact hp.stk_s.sub_right (Region.sub_prefix (by omega)) }

/-- The key absorbed. -/
theorem hk3_ok {s : State} (h : HK (H := H) s₀ s) (ua : UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀))
    (hx1 : s.gpr .x1 = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (stA H s₀) []) :
    WP isa (.call H.updN H.updC) s fun t => HK (H := H) s₀ t ∧ VecKept s t ∧
      hH.SH.Repr t.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  refine upd_call hH ua fun s₈ a₈ r₈ => ⟨h.call hp a₈ fun r hr => ?_, a₈.vec, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr hx1
    rwa [List.nil_append, h.key] at this

/-- `finalize`'s arguments: the digest after the state. -/
theorem hk4_ok {s : State} (h : HK (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.block [.addImm .x .x0 .x23 H.ext, mov .x1 .x22, .addImm .x .x2 .x23 (H.ext + H.S), mov .x3 .x23]) s
      fun t => HK (H := H) s₀ t ∧ FinArgs hH t (stA H s₀) (dgA H s₀) (scr s₀) ∧ t.gpr .x1 = s₀.gpr .x3 ∧
        hH.SH.Repr t.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  refine wp_addImm (by omega) fun s₉ u₉ => wp_mov fun s₁₀ u₁₀ => wp_addImm (by omega) fun s₁₁ u₁₁ =>
    wp_mov fun s₁₂ u₁₂ => WP.block_nil ?_
  have k₁₂ := (((h.upd u₉ (by decide)).upd u₁₀ (by decide)).upd u₁₁ (by decide)).upd u₁₂ (by decide)
  refine ⟨k₁₂, ?_, by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, u₉.other _ (by decide),
    h.x22], by rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]; exact hr⟩
  exact
    { x0 := by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.gpr, h.x23]
      x2 := by rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₀.other _ (by decide), u₉.other _ (by decide), h.x23]
      x3 := by rw [u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), h.x23]
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact cov_part hp k₁₂ (by omega)
        · exact cov_part hp k₁₂ (by omega)
        · exact cov_low hp k₁₂ (by omega)
      st_o := Offset.disjoint _ (Or.inl (Nat.le_refl _)) (by omega) (by omega)
      st_sc := Offset.disjoint_base _ (by omega) (by omega)
      o_sc := Offset.disjoint_base _ (by omega) (by omega)
      sp16 := by rw [k₁₂.sp]; exact hp.sp16
      stk_st := stk_part hp k₁₂ (by omega)
      stk_o := stk_part hp k₁₂ (by omega)
      stk_sc := by rw [k₁₂.sp]; exact hp.stk_s.sub_right (Region.sub_prefix (by omega)) }

/-- The digest. -/
theorem hk5_ok {s : State} (h : HK (H := H) s₀ s) (fa : FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀))
    (hx1 : s.gpr .x1 = s₀.gpr .x3) (hr : hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.call H.finN H.finC) s fun t => HK (H := H) s₀ t ∧ VecKept s t ∧
      bytesAt t.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  refine fin_call hH fa fun s₁₃ a₁₃ r₁₃ => ⟨h.call hp a₁₃ fun r hr => ?_, a₁₃.vec, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ hH.hDF]
    exact r₁₃ _ hr (by rw [bytesAt_length]; exact (s₀.gpr .x3).isLt)
      (by rw [hx1, bytesAt_length, BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-- What `hashKey` leaves: `init`'s arguments, with the digest as the key,
and our caller's registers. -/
structure Hashed (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  cs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  x0 : t.gpr .x0 = inn s₀
  x1 : t.gpr .x1 = out s₀
  x4 : t.gpr .x4 = scr s₀
  x2 : t.gpr .x2 = dgA H s₀
  x3 : t.gpr .x3 = BitVec.ofNat 64 H.D
  dg : bytesAt t.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))

/-- The epilogue: `init`'s arguments, and our caller's registers back. -/
theorem hk6_ok {s : State} (h : HK (H := H) s₀ s)
    (hd : bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) :
    WP isa (.block ([mov .x0 .x19, mov .x1 .x20, mov .x4 .x23, .addImm .x .x2 .x23 (H.ext + H.S),
      .movz .x .x3 (BitVec.ofNat 16 H.D) 0] ++ H.restore)) s (Hashed hH s₀) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  simp only [List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_mov fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addImm (by omega) fun s₄ u₄ =>
    wp_movz fun s₅ u₅ => ?_
  have k₅ := ((((h.upd u₁ (by decide)).upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅
    (by decide)
  refine WP.mono (restore_ok H k₅.x23 (Nat.le_trans hH.hW (by decide)) k₅.saved
    (by rw [k₅.wr]; exact ws_mem hp) (L := 8 * Wt) (by omega)) fun t ⟨hm, hrd, hwr, hsp, hcs, ho⟩ => ?_
  refine ⟨by rw [hrd, k₅.rd], by rw [hwr, k₅.wr], by rw [hsp, k₅.sp], fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · by_cases hs : r ∈ VG.Proof.Hmac.Generic.AArch64.savedRegs
    · exact hcs r hs
    · rw [ho r hs]; exact k₅.cs r (by revert r hr hs; decide)
  · rw [ho _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.gpr, h.x19]
  · rw [ho _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.other _ (by decide), h.x20]
  · rw [ho _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), h.x23]
  · rw [ho _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), h.x23]
  · rw [ho _ (by decide), u₅.gpr, movz_ofNat (by have := hH.hDF; have := hH.hF; omega)]
  · rw [hm, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]; exact hd

/-- `hashKey`, from a state with our arguments (`x9` aside). -/
theorem hashKey_ok {s : State} (hg : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r) (hm : s.mem = s₀.mem)
    (hr : s.rd = s₀.rd) (hw : s.wr = s₀.wr) (hsp : s.sp = s₀.sp) :
    WP isa H.hashKey s fun t => Hashed hH s₀ t ∧ VecKept s t := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (WP.preservedV (pro_ok hp hH hg hm hr hw hsp) (by rfl))
    fun s₁ ⟨⟨k₁, d₁⟩, v₁⟩ => ?_)
  refine WP.seq (WP.mono (hk1_ok hH hp k₁ d₁) fun s₂ ⟨k₂, v₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (hk2_ok hH hp k₂ r₂) (by rfl))
    fun s₃ ⟨⟨k₃, a₃, i₃, r₃⟩, v₃⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hH hp k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, v₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (hk4_ok hH hp k₄ r₄) (by rfl))
    fun s₅ ⟨⟨k₅, a₅, i₅, r₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hH hp k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, v₆, b₆⟩ => ?_)
  refine WP.mono (WP.preservedV (hk6_ok hH hp k₆ b₆) (by rfl)) fun t ⟨h, v₇⟩ => ⟨h, ?_⟩
  exact VecKept.trans v₁ (VecKept.trans v₂ (VecKept.trans v₃ (VecKept.trans v₄ (VecKept.trans v₅
    (VecKept.trans v₆ v₇)))))

end

/-! ## Correctness -/

section
variable {Wt : Nat} {s₀ : State}

/-- What `initAny` leaves: the calling convention's obligations, and the
states for the key. -/
abbrev Post (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧
    hH.SH.Repr s'.mem (inn s₀) (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀))) ipad) ∧
    hH.SH.Repr s'.mem (out s₀) (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (kp s₀) (kl s₀))) opad)

/-- What the tests of `key_len` leave: `x9` aside, our arguments. -/
structure Cmp (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .x9 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem Cmp.of_upd {s s' : State} (h : Cmp s₀ s) {v : BitVec 64} (u : Upd s s' .x9 v) : Cmp s₀ s' :=
  ⟨fun r hr => (u.other r hr).trans (h.gpr r hr), u.mem.trans h.mem, u.rd.trans h.rd, u.wr.trans h.wr,
    u.sp.trans h.sp⟩

theorem cmp_refl : Cmp s₀ s₀ := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem shr_ok {s : State} (h : Cmp s₀ s) (hpow : 2 ^ Nat.log2 H.B = H.B) (hlt : Nat.log2 H.B < 64) :
    WP isa (.block [.lsr .x .x9 .x3 (Nat.log2 H.B)]) s fun t =>
      (Cmp s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kl s₀ < H.B))) ∧ VecKept s t := by
  refine WP.preservedV (Q := fun t => Cmp s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kl s₀ < H.B))) ?_
    (by rfl)
  refine wp_lsr hlt fun t u => WP.block_nil ⟨h.of_upd u, ?_⟩
  change eval (.zero .x .x9) t = _
  rw [eval_zero, u.gpr, h.gpr _ (by decide), shr_beq_zero, hpow]

theorem sub_ok {s : State} (h : Cmp s₀ s) (hB : H.B < 4096) :
    WP isa (.block [.subImm .x .x9 .x3 H.B]) s fun t =>
      (Cmp s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kl s₀ = H.B))) ∧ VecKept s t := by
  refine WP.preservedV (Q := fun t => Cmp s₀ t ∧ isa.eval (.zero .x .x9) t = some (decide (kl s₀ = H.B))) ?_
    (by rfl)
  refine wp_subImm hB fun t u => WP.block_nil ⟨h.of_upd u, ?_⟩
  change eval (.zero .x .x9) t = _
  have ex : s₀.gpr .x3 = BitVec.ofNat 64 (kl s₀) := by simp
  rw [eval_zero, u.gpr, h.gpr _ (by decide), ex, sub_beq (s₀.gpr .x3).isLt (by omega)]

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : H.B < k.length) (hl : (hH.SH.H.hash k).length ≤ H.B) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB
  simp only [blockKey, hB, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.B < (hH.SH.H.hash k).length by omega))]

/-- From a `Ready` state with our arguments, `init` leaves `Post`. -/
theorem short_post {s : State} (c : Cmp s₀ s) (hv : VecKept s₀ s) (hr : Ready (H := H) s) :
    WP isa H.init s (Post hH s₀) := by
  refine WP.mono (init_ok hH hr) fun s' ⟨⟨hcs, hsp, hvv⟩, hi, ho⟩ => ⟨⟨fun r hr' => ?_, by rw [hsp, c.sp],
    fun r hr' => (hvv r hr').trans (hv r hr')⟩, ?_, ?_⟩
  · rw [hcs r hr', c.gpr r (by revert r hr'; decide)]
  · simp only [inn, kp, kl, c.gpr _ (show Reg.x0 ≠ .x9 by decide), c.gpr _ (show Reg.x2 ≠ .x9 by decide),
      c.gpr _ (show Reg.x3 ≠ .x9 by decide), c.mem] at hi
    exact hi
  · simp only [out, kp, kl, c.gpr _ (show Reg.x1 ≠ .x9 by decide), c.gpr _ (show Reg.x2 ≠ .x9 by decide),
      c.gpr _ (show Reg.x3 ≠ .x9 by decide), c.mem] at ho
    exact ho

theorem correct_gen (hpow : 2 ^ Nat.log2 H.B = H.B) (hlt : Nat.log2 H.B < 64)
    (hS : ∀ s, Cmp s₀ s → kl s₀ ≤ H.B → Ready (H := H) s) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀) :
    WP isa H.initAny s₀ (Post hH s₀) := by
  have hB := hH.hBB
  unfold Hash.initAny
  refine WP.seq (WP.mono (shr_ok cmp_refl hpow hlt) fun s₁ ⟨⟨c₁, e₁⟩, v₁⟩ => WP.seq ?_)
  refine WP.ite _ e₁ (fun hT => WP.block_nil (short_post hH c₁ v₁ (hS _ c₁ (by
    have := of_decide_eq_true hT; omega)))) fun hF => ?_
  refine WP.seq (WP.mono (sub_ok c₁ (by omega)) fun s₂ ⟨⟨c₂, e₂⟩, v₂⟩ => ?_)
  have v₂' := VecKept.trans v₁ v₂
  refine WP.ite _ e₂ (fun hT => WP.block_nil (short_post hH c₂ v₂' (hS _ c₂ (by
    have := of_decide_eq_true hT; omega)))) fun hF' => ?_
  have hk : H.B < kl s₀ := by have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega
  have hp := hL hk
  refine WP.mono (hashKey_ok hH hp c₂.gpr c₂.mem c₂.rd c₂.wr c₂.sp) fun s₃ ⟨h₃, v₃⟩ => ?_
  have hD := hp.hDB; have := hH.hDF; have := hH.hF
  have r₃ : Ready (H := H) s₃ := ready_at hH hp h₃.x0 h₃.x1 h₃.x4 h₃.sp h₃.rd h₃.wr
    (by show (s₃.gpr .x3).toNat ≤ H.B; rw [h₃.x3, toNat_ofNat_lt (by omega)]; exact hD)
    (.inr ⟨H.ext + H.S, by simp only [keyR, kp, kl, h₃.x2], Nat.le_add_right _ _, by
      show H.ext + H.S + (s₃.gpr .x3).toNat ≤ 8 * Wt
      rw [h₃.x3, toNat_ofNat_lt (by omega)]; have := hp.fits; omega⟩)
  refine WP.mono (init_ok hH r₃) fun s' ⟨⟨hcs, hsp, hvv⟩, hi, ho⟩ => ?_
  have hkey : bytesAt s₃.mem (kp s₃) (kl s₃) = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀)) := by
    simp only [kp, kl, h₃.x2, h₃.x3, toNat_ofNat_lt (show H.D < 2 ^ 64 by omega)]; exact h₃.dg
  have hlen : (hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))).length ≤ H.B := by
    rw [← h₃.dg, bytesAt_length]; exact hD
  have hk0 := blockKey_hash hH (by rw [bytesAt_length]; exact hk) hlen
  refine ⟨⟨fun r hr => (hcs r hr).trans (h₃.cs r hr), by rw [hsp, h₃.sp],
    fun r hr => (hvv r hr).trans (VecKept.trans v₂' v₃ r hr)⟩, ?_, ?_⟩
  · simp only [inn, h₃.x0, hkey, hk0] at hi; exact hi
  · simp only [out, h₃.x1, hkey, hk0] at ho; exact ho

end

/-! ## Constant time -/

abbrev proBlock (H : Hash) : List Instr :=
  H.save ++ [mov .x19 .x0, mov .x20 .x1, mov .x21 .x2, mov .x22 .x3, mov .x23 .x4, .addImm .x .x0 .x23 H.ext]

abbrev argU (H : Hash) : List Instr :=
  [.addImm .x .x0 .x23 H.ext, .movz .x .x1 0 0, mov .x2 .x21, mov .x3 .x22, mov .x4 .x23]

abbrev argF (H : Hash) : List Instr :=
  [.addImm .x .x0 .x23 H.ext, mov .x1 .x22, .addImm .x .x2 .x23 (H.ext + H.S), mov .x3 .x23]

abbrev epi (H : Hash) : List Instr :=
  [mov .x0 .x19, mov .x1 .x20, mov .x4 .x23, .addImm .x .x2 .x23 (H.ext + H.S),
    .movz .x .x3 (BitVec.ofNat 16 H.D) 0] ++ H.restore

/-- The registers `HK` fixes from the public arguments. -/
abbrev pregs : List Reg := [.x19, .x20, .x21, .x22, .x23]

/-- The taint checks of the tests of `key_len` and of `hashKey`'s pieces
between its calls. -/
structure Checks (H : Hash) : Prop where
  shr : ∃ hc, (Taint.check taint (Taint.ofRegs Init.args) (.block [.lsr .x .x9 .x3 (Nat.log2 H.B)]) hc).isSome = true
  sub : ∃ hc, (Taint.check taint (Taint.ofRegs Init.args) (.block [.subImm .x .x9 .x3 H.B]) hc).isSome = true
  pro : ∃ hc, (Taint.check taint (Taint.ofRegs Init.args) (.block (proBlock H)) hc).isSome = true
  argU : ∃ hc, (Taint.check taint (Taint.ofRegs pregs) (.block (argU H)) hc).isSome = true
  argF : ∃ hc, (Taint.check taint (Taint.ofRegs pregs) (.block (argF H)) hc).isSome = true
  epi : ∃ hc, (Taint.check taint (Taint.ofRegs pregs) (.block (epi H)) hc).isSome = true

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
    s.sp = s'.sp ∧ ∀ r ∈ pregs, s.gpr r = s'.gpr r := by
  refine ⟨by rw [h.sp, h'.sp, hq.sp], fun r hr => ?_⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.x19, h'.x19, inn, inn, hq.x0]
  · rw [h.x20, h'.x20, out, out, hq.x1]
  · rw [h.x21, h'.x21, kp, kp, hq.x2]
  · rw [h.x22, h'.x22, hq.x3]
  · rw [h.x23, h'.x23, scr, scr, hq.x4]

include hq in
theorem cmp_agree {s s' : State} (c : Cmp s₀ s) (c' : Cmp s₀' s') :
    s.sp = s'.sp ∧ ∀ r ∈ Init.args, s.gpr r = s'.gpr r := by
  refine ⟨by rw [c.sp, c'.sp, hq.sp], fun r hr => ?_⟩
  have h9 : r ≠ .x9 := by revert r hr; decide
  rw [c.gpr r h9, c'.gpr r h9]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · exact hq.x0
  · exact hq.x1
  · exact hq.x2
  · exact hq.x3
  · exact hq.x4

variable (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
include hp hp' hq

theorem hashKey_rel (hca : Checks H) :
    RelCT isa (fun s s' => Cmp s₀ s ∧ Cmp s₀' s') H.hashKey
      fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' := by
  have eS : stA H s₀' = stA H s₀ := by simp only [stA, A, scr, hq.x4]
  have eD : dgA H s₀' = dgA H s₀ := by simp only [dgA, A, scr, hq.x4]
  have eK : kp s₀' = kp s₀ := hq.x2.symm
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.x3]
  have e8 : scr s₀' = scr s₀ := hq.x4.symm
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  unfold Hash.hashKey
  have pro : RelCT isa (fun s s' => Cmp s₀ s ∧ Cmp s₀' s') (.block (proBlock H))
      fun s s' => (HK (H := H) s₀ s ∧ s.gpr .x0 = stA H s₀) ∧ (HK (H := H) s₀' s' ∧ s'.gpr .x0 = stA H s₀) :=
    rel_taint Init.args (fun _ _ c c' => cmp_agree hq c c') hca.pro
      (fun _ c => pro_ok hp hH c.gpr c.mem c.rd c.wr c.sp)
      (fun _ c => WP.mono (pro_ok hp' hH c.gpr c.mem c.rd c.wr c.sp) fun _ ⟨k, d⟩ => ⟨k, d.trans eS⟩)
  have i1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ s.gpr .x0 = stA H s₀) ∧
      (HK (H := H) s₀' s' ∧ s'.gpr .x0 = stA H s₀)) (.call H.initN H.initC)
      fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀) []) :=
    rel_wp (init_rel hH (st := stA H s₀) fun s s' ⟨⟨k, d⟩, ⟨k', d'⟩⟩ =>
        ⟨d, d', Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; exact cov_part hp k (by omega),
          Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [← eS]; exact cov_part hp' k' (by omega),
          by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun _ ⟨k, d⟩ => WP.mono (hk1_ok hH hp k d) fun _ ⟨k, _, r⟩ => ⟨k, r⟩)
      (fun _ ⟨k, d⟩ => WP.mono (hk1_ok hH hp' k (d.trans eS.symm)) fun _ ⟨k, _, r⟩ => ⟨k, eS ▸ r⟩)
  have u0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
      (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀) [])) (.block (argU H))
      fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s'.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (stA H s₀) []) :=
    rel_taint pregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argU (fun _ ⟨k, r⟩ => hk2_ok hH hp k r)
      (fun _ ⟨k, r⟩ => WP.mono (hk2_ok hH hp' k (eS ▸ r)) fun _ ⟨k, a, i, r⟩ =>
        ⟨k, eS ▸ eK ▸ e8 ▸ eL ▸ a, i, eS ▸ r⟩)
  have u1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (stA H s₀) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          s'.gpr .x1 = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (stA H s₀) [])) (.call H.updN H.updC)
      fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_wp (upd_rel hH fun s s' ⟨⟨k, a, i, _⟩, ⟨k', a', i', _⟩⟩ =>
        ⟨a, a', by rw [i, i'], by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, i, r⟩ => WP.mono (hk3_ok hH hp k a i r) fun _ ⟨k, _, r⟩ => ⟨k, r⟩)
      (fun _ ⟨k, a, i, r⟩ => WP.mono (hk3_ok hH hp' k (eS.symm ▸ eK.symm ▸ e8.symm ▸ eL.symm ▸ a) i
        (eS.symm ▸ r)) fun _ ⟨k, _, r⟩ => ⟨k, r⟩)
  have f0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.block (argF H))
      fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧ s.gpr .x1 = s₀.gpr .x3 ∧
          hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧ s'.gpr .x1 = s₀'.gpr .x3 ∧
          hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_taint pregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argF (fun _ ⟨k, r⟩ => hk4_ok hH hp k r)
      (fun _ ⟨k, r⟩ => hk4_ok hH hp' k r)
  have f1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧
          s.gpr .x1 = s₀.gpr .x3 ∧ hH.SH.Repr s.mem (stA H s₀) (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧ s'.gpr .x1 = s₀'.gpr .x3 ∧
          hH.SH.Repr s'.mem (stA H s₀') (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.call H.finN H.finC)
      fun s s' => (HK (H := H) s₀ s ∧
          bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (dgA H s₀') H.D = hH.SH.H.hash (bytesAt s₀'.mem (kp s₀') (kl s₀'))) :=
    rel_wp (fin_rel hH (st := stA H s₀) (o := dgA H s₀) (sc := scr s₀) fun s s' ⟨⟨k, a, i, _⟩, ⟨k', a', i', _⟩⟩ =>
        ⟨a, eS ▸ eD ▸ e8 ▸ a', by rw [i, i', hq.x3], by rw [k.sp, k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, i, r⟩ => WP.mono (hk5_ok hH hp k a i r) fun _ ⟨k, _, d⟩ => ⟨k, d⟩)
      (fun _ ⟨k, a, i, r⟩ => WP.mono (hk5_ok hH hp' k a i r) fun _ ⟨k, _, d⟩ => ⟨k, d⟩)
  have ep : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧
          bytesAt s.mem (dgA H s₀) H.D = hH.SH.H.hash (bytesAt s₀.mem (kp s₀) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (dgA H s₀') H.D = hH.SH.H.hash (bytesAt s₀'.mem (kp s₀') (kl s₀'))))
      (.block (epi H)) fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' :=
    rel_taint pregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.epi (fun _ ⟨k, d⟩ => hk6_ok hH hp k d)
      (fun _ ⟨k, d⟩ => hk6_ok hH hp' k d)
  exact pro.seq (i1.seq (u0.seq (u1.seq (f0.seq (f1.seq ep)))))

end

section
variable {Wt : Nat} {s₀ s₀' : State} (hc : Init.Checks H) (hq : Init.PubEq s₀ s₀')

/-- Two states from which `init` runs, with the same public arguments. -/
abbrev RR (s s' : State) : Prop := Ready (H := H) s ∧ Ready (H := H) s' ∧ Init.PubEq s s'

include hH hc in
theorem init_rel' : RelCT isa (RR (H := H)) H.init fun _ _ => True :=
  RelCT.of_narrow (Ready (H := H)) (nar H) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ h _ _ he => init_exec h he)
    (fun _ h => let ⟨t, s', he, _⟩ := Init.correct hH h.pre; ⟨t, s', he⟩)
    fun _ _ _ _ _ _ ⟨_, _, ⟨r₁, r₂, pq⟩, e₁, e₂⟩ x₁ x₂ =>
      Init.ct hH hc r₁.pre r₂.pre ⟨pq.x0, pq.x1, pq.x2, pq.x3, pq.x4, pq.sp⟩ _ _ _ _ _ _ ⟨e₁, e₂⟩ x₁ x₂

include hq in
theorem hashed_rr {s s' : State} (h : Hashed hH s₀ s) (h' : Hashed hH s₀' s') (r : Ready (H := H) s)
    (r' : Ready (H := H) s') : RR (H := H) s s' :=
  ⟨r, r', by rw [h.x0, h'.x0, inn, inn, hq.x0], by rw [h.x1, h'.x1, out, out, hq.x1],
    by rw [h.x2, h'.x2, dgA, dgA, A, A, scr, scr, hq.x4], by rw [h.x3, h'.x3], by rw [h.x4, h'.x4, scr, scr, hq.x4],
    by rw [h.sp, h'.sp, hq.sp]⟩

include hq in
theorem cmp_rr {s s' : State} (c : Cmp s₀ s) (c' : Cmp s₀' s') (r : Ready (H := H) s)
    (r' : Ready (H := H) s') : RR (H := H) s s' :=
  ⟨r, r', by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.x0,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.x1,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.x2,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.x3,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.x4, by rw [c.sp, c'.sp]; exact hq.sp⟩

include hH hc hq in
theorem ct_gen (hca : Checks H) (hpow : 2 ^ Nat.log2 H.B = H.B) (hlt : Nat.log2 H.B < 64)
    (hS : ∀ s, Cmp s₀ s → kl s₀ ≤ H.B → Ready (H := H) s) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀)
    (hS' : ∀ s, Cmp s₀' s → kl s₀' ≤ H.B → Ready (H := H) s) (hL' : H.B < kl s₀' → PreA (H := H) Wt s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initAny fun _ _ => True := by
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.x3]
  have hB := hH.hBB
  unfold Hash.initAny
  have shr : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block [.lsr .x .x9 .x3 (Nat.log2 H.B)])
      fun s s' => (Cmp s₀ s ∧ isa.eval (.zero .x .x9) s = some (decide (kl s₀ < H.B))) ∧
        (Cmp s₀' s' ∧ isa.eval (.zero .x .x9) s' = some (decide (kl s₀ < H.B))) :=
    rel_taint Init.args (fun s s' e e' => by subst e e'; exact cmp_agree hq cmp_refl cmp_refl) hca.shr
      (fun _ e => by subst e; exact WP.mono (shr_ok cmp_refl hpow hlt) fun _ ⟨⟨c, ev⟩, _⟩ => ⟨c, ev⟩)
      (fun _ e => by subst e; exact WP.mono (shr_ok cmp_refl hpow hlt) fun _ ⟨⟨c, ev⟩, _⟩ => ⟨c, eL ▸ ev⟩)
  refine shr.seq (RelCT.seq (R := RR (H := H)) ?_ (init_rel' hH hc))
  refine RelCT.ite (fun s s' ⟨⟨_, ev⟩, ⟨_, ev'⟩⟩ => by rw [ev, ev']) ?_ ?_
  · refine rel_nil fun s s' ⟨⟨⟨c, ev⟩, ⟨c', _⟩⟩, hT⟩ => ?_
    rw [ev, Option.some.injEq] at hT
    have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT; omega
    exact cmp_rr hq c c' (hS s c hk) (hS' s' c' (eL ▸ hk))
  · have sub : RelCT isa (fun s s' => (Cmp s₀ s ∧ H.B ≤ kl s₀) ∧ (Cmp s₀' s' ∧ H.B ≤ kl s₀))
        (.block [.subImm .x .x9 .x3 H.B])
        fun s s' => ((Cmp s₀ s ∧ H.B ≤ kl s₀) ∧ isa.eval (.zero .x .x9) s = some (decide (kl s₀ = H.B))) ∧
          ((Cmp s₀' s' ∧ H.B ≤ kl s₀) ∧ isa.eval (.zero .x .x9) s' = some (decide (kl s₀ = H.B))) :=
      rel_taint Init.args (fun _ _ c c' => cmp_agree hq c.1 c'.1) hca.sub
        (fun _ c => WP.mono (sub_ok c.1 (by omega)) fun _ ⟨⟨c₁, ev⟩, _⟩ => ⟨⟨c₁, c.2⟩, ev⟩)
        (fun _ c => WP.mono (sub_ok c.1 (by omega)) fun _ ⟨⟨c₁, ev⟩, _⟩ => ⟨⟨c₁, c.2⟩, eL ▸ ev⟩)
    refine RelCT.mono (P := fun s s' => (Cmp s₀ s ∧ H.B ≤ kl s₀) ∧ (Cmp s₀' s' ∧ H.B ≤ kl s₀)) ?_
      (fun s s' ⟨⟨⟨c, ev⟩, ⟨c', _⟩⟩, hF⟩ => by
        rw [ev, Option.some.injEq] at hF
        have := of_decide_eq_false hF
        exact ⟨⟨c, by omega⟩, ⟨c', by omega⟩⟩) fun _ _ h => h
    refine sub.seq (RelCT.ite (fun s s' ⟨⟨_, ev⟩, ⟨_, ev'⟩⟩ => by rw [ev, ev']) ?_ ?_)
    · refine rel_nil fun s s' ⟨⟨⟨⟨c, _⟩, ev⟩, ⟨⟨c', _⟩, _⟩⟩, hT⟩ => ?_
      rw [ev, Option.some.injEq] at hT
      have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT; omega
      exact cmp_rr hq c c' (hS s c hk) (hS' s' c' (eL ▸ hk))
    · refine RelCT.mono (P := fun s s' => (Cmp s₀ s ∧ Cmp s₀' s') ∧ H.B < kl s₀) ?_
        (fun s s' ⟨⟨⟨⟨c, h₁⟩, ev⟩, ⟨⟨c', _⟩, _⟩⟩, hF⟩ => by
          rw [ev, Option.some.injEq] at hF
          have := of_decide_eq_false hF
          exact ⟨⟨c, c'⟩, by omega⟩) fun _ _ h => h
      refine RelCT.exists_ (P := fun (_ : H.B < kl s₀) s s' => Cmp s₀ s ∧ Cmp s₀' s') ?_
        |>.mono (fun s s' ⟨h, hk⟩ => ⟨hk, h⟩) fun _ _ h => h
      intro hk
      have hp := hL hk
      have hp' := hL' (eL ▸ hk)
      have hD := hp.hDB; have := hH.hDF; have := hH.hF
      have rd : ∀ {s₀ t : State} (hp : PreA (H := H) Wt s₀), Hashed hH s₀ t → Ready (H := H) t :=
        fun {s₀ t} hp h => ready_at hH hp h.x0 h.x1 h.x4 h.sp h.rd h.wr
          (by show (t.gpr .x3).toNat ≤ H.B; rw [h.x3, toNat_ofNat_lt (by omega)]; exact hD)
          (.inr ⟨H.ext + H.S, by simp only [keyR, kp, kl, h.x2], Nat.le_add_right _ _, by
            show H.ext + H.S + (t.gpr .x3).toNat ≤ 8 * Wt
            rw [h.x3, toNat_ofNat_lt (by omega)]; have := hp.fits; omega⟩)
      exact (hashKey_rel hH hq hp hp' hca).mono (fun _ _ h => h)
        fun _ _ ⟨h, h'⟩ => hashed_rr hH hq h h' (rd hp h) (rd hp' h')

end

/-! ## Verified -/

theorem log2_lt : Nat.log2 H.B < 64 ∨ ¬ (2 ^ Nat.log2 H.B = H.B ∧ H.B ≤ 128) := by
  by_cases h : Nat.log2 H.B < 64
  · exact .inl h
  · refine .inr fun ⟨hp, hb⟩ => ?_
    have : 2 ^ 64 ≤ 2 ^ Nat.log2 H.B := Nat.pow_le_pow_right (by decide) (by omega)
    omega

include hH in
theorem hlt (hpow : 2 ^ Nat.log2 H.B = H.B) : Nat.log2 H.B < 64 :=
  (log2_lt (H := H)).resolve_right fun h => h ⟨hpow, hH.hBB⟩

section
variable {Wt : Nat} {s₀ : State}

include hH in
theorem ready_cmp (hp : PreA (H := H) Wt s₀) {s : State} (c : Cmp s₀ s) (hk : kl s₀ ≤ H.B) :
    Ready (H := H) s :=
  ready_at hH hp (c.gpr _ (by decide)) (c.gpr _ (by decide)) (c.gpr _ (by decide)) c.sp c.rd c.wr
    (by show (s.gpr .x3).toNat ≤ H.B; rw [c.gpr _ (by decide)]; exact hk)
    (.inl (by simp only [keyR, kp, kl, c.gpr _ (show Reg.x2 ≠ .x9 by decide), c.gpr _ (show Reg.x3 ≠ .x9 by decide)]))

/-- `init`'s precondition, with any working space at least as large as its
own, makes a `Ready` state, after the tests of `key_len`. -/
theorem ready_of_pre {sc : Nat} (hp : Pre (H := H) sc s₀) {s : State} (c : Cmp s₀ s) : Ready (H := H) s := by
  have hf := hp.fits
  have sub : Region.Sub (scR (nw0 H) s₀) (scR sc s₀) := Region.sub_prefix (by simp only [nw0]; omega)
  have e0 := c.gpr .x0 (by decide); have e1 := c.gpr .x1 (by decide); have e2 := c.gpr .x2 (by decide)
  have e3 := c.gpr .x3 (by decide); have e4 := c.gpr .x4 (by decide)
  have hi : inR (H := H) s = inR (H := H) s₀ := by simp only [inR, inn, e0]
  have ho : outR (H := H) s = outR (H := H) s₀ := by simp only [outR, out, e1]
  have hs : scR (nw0 H) s = scR (nw0 H) s₀ := by simp only [scR, scr, e4]
  have hk : keyR s = keyR s₀ := by simp only [keyR, kp, kl, e2, e3]
  have hK : stkR s = stkR s₀ := by simp only [stkR, c.sp]
  refine ⟨⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fits0, hp.hB, hp.hW, hp.hS⟩, ?_, ?_⟩
  · show (s.gpr .x3).toNat ≤ H.B; rw [e3]; exact hp.kl_le
  · show (inR (H := H) s).Disjoint (outR (H := H) s); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) s).Disjoint (scR (nw0 H) s); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) s).Disjoint (scR (nw0 H) s); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR s).Disjoint (inR (H := H) s); rw [hk, hi]; exact hp.k_i
  · show (keyR s).Disjoint (outR (H := H) s); rw [hk, ho]; exact hp.k_o
  · show (keyR s).Disjoint (scR (nw0 H) s); rw [hk, hs]; exact hp.k_s.sub_right sub
  · show 16 ≤ s.sp.toNat; rw [c.sp]; exact hp.sp16
  · show (stkR s).Disjoint (inR (H := H) s); rw [hK, hi]; exact hp.stk_i
  · show (stkR s).Disjoint (outR (H := H) s); rw [hK, ho]; exact hp.stk_o
  · show (stkR s).Disjoint (keyR s); rw [hK, hk]; exact hp.stk_k
  · show (stkR s).Disjoint (scR (nw0 H) s); rw [hK, hs]; exact hp.stk_s.sub_right sub
  · show (s.gpr .x4).toNat + 8 * nw0 H ≤ 2 ^ 64
    rw [e4]; show (scr s₀).toNat + 8 * nw0 H ≤ 2 ^ 64; have := hp.nw; simp only [nw0]; omega
  · rw [hk, hi, ho, hs, c.rd, c.wr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · exact sub_of_self (r := keyR s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := scR sc s₀) (by simp) (by show 8 * nw0 H ≤ 8 * sc; simp only [nw0]; omega)
  · rw [hi, ho, hs, c.wr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := scR sc s₀) (by simp) (by show 8 * nw0 H ≤ 8 * sc; simp only [nw0]; omega)

end

/-- `initAny`'s working space at its end holds the streaming state and the
digest of a long key; it is the shared contract's. -/
theorem verifiedAny {Wt : Nat} (hc : Init.Checks H) (hca : Checks H) (hfit : H.ext + H.S + H.F ≤ 8 * Wt)
    (hDB : H.D ≤ H.B) (hpow : 2 ^ Nat.log2 H.B = H.B) (hsat : ∃ s, (initAnyG hH.SH Wt).pre s) :
    Verified AArch64.target H.initAny (initAnyG hH.SH Wt) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · have hp := preA_of hH hs hfit hDB hpow
    obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (Wt := Wt) hpow (hlt hH hpow)
      (fun _ c hk => ready_cmp hH hp c hk) (fun _ => hp)
    exact ⟨t, s', he, hg, hpost⟩
  · have hp₁ := preA_of hH h₁ hfit hDB hpow
    have hp₂ := preA_of hH h₂ hfit hDB hpow
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (ct_gen hH hc ⟨p1, p2, p3, p4, p5, p6⟩ hca hpow (hlt hH hpow) (fun _ c hk => ready_cmp hH hp₁ c hk)
      (fun _ => hp₁) (fun _ c hk => ready_cmp hH hp₂ c hk) (fun _ => hp₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

/-- `initAny` is verified against `init`'s contract too, for a key of at most
a block: it runs `init`. -/
theorem verifiedShort {sc : Nat} (hc : Init.Checks H) (hca : Checks H) (hfit : H.buf + 2 * H.B ≤ 8 * sc)
    (hpow : 2 ^ Nat.log2 H.B = H.B) (hsat : ∃ s, (initG hH.SH sc).pre s) :
    Verified AArch64.target H.initAny (initG hH.SH sc) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · have hp := Init.pre_of hH sc hs hfit
    obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (Wt := sc) hpow (hlt hH hpow)
      (fun _ c _ => ready_of_pre hp c) (fun h => absurd hp.kl_le (by omega))
    exact ⟨t, s', he, hg, hpost⟩
  · have hp₁ := Init.pre_of hH sc h₁ hfit
    have hp₂ := Init.pre_of hH sc h₂ hfit
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (ct_gen hH (Wt := sc) hc ⟨p1, p2, p3, p4, p5, p6⟩ hca hpow (hlt hH hpow)
      (fun _ c _ => ready_of_pre hp₁ c) (fun h => absurd hp₁.kl_le (by omega))
      (fun _ c _ => ready_of_pre hp₂ c) (fun h => absurd hp₂.kl_le (by omega))
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.AArch64.InitAny

namespace VG.Proof.Hmac.Generic.AArch64.Instances

open VG.AArch64
open VG.Proof.Hmac.Generic.AArch64

/-- `initAnyG` implies the shared contract for any hash function and
scratch space (`generic_implies`), given that the shared contract is
satisfiable. -/
theorem initAnyImp (S : Spec.Hmac.StreamingHash) (W : Nat)
    (h : ∃ s, (Spec.Hmac.initAnyKeyContract S W AArch64.abi 16).pre s) :
    (initAnyG S W).Implies (Spec.Hmac.initAnyKeyContract S W AArch64.abi 16) := by
  generic_implies [
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, initAnyG, stk, AArch64.abi, AArch64.argRegs] using h

/-- The checks do not look at the functions `initAny` calls. -/
theorem InitAny.Checks.of_eq {H H' : Impl.Hmac.Generic.AArch64.Hash} (hB : H.B = H'.B) (hS : H.S = H'.S)
    (hD : H.D = H'.D) (hW : H.W = H'.W) (h : InitAny.Checks H) : InitAny.Checks H' := by
  obtain ⟨B, S, D, F, W, iN, iC, uN, uC, fN, fC⟩ := H
  obtain ⟨B', S', D', F', W', iN', iC', uN', uC', fN', fC'⟩ := H'
  dsimp only at hB hS hD hW; subst hB hS hD hW
  exact ⟨h.shr, h.sub, h.pro, h.argU, h.argF, h.epi⟩

end VG.Proof.Hmac.Generic.AArch64.Instances
