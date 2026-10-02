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
      x2 := by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, h.x21]
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
      h.x20]
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
  refine WP.seq (WP.mono (WP.preservedV (pro_ok hp hH hg hm hr hw hsp) (by decide +kernel))
    fun s₁ ⟨⟨k₁, d₁⟩, v₁⟩ => ?_)
  refine WP.seq (WP.mono (hk1_ok hH hp k₁ d₁) fun s₂ ⟨k₂, v₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (hk2_ok hH hp k₂ r₂) (by decide +kernel))
    fun s₃ ⟨⟨k₃, a₃, i₃, r₃⟩, v₃⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hH hp k₃ a₃ i₃ r₃) fun s₄ ⟨k₄, v₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (WP.preservedV (hk4_ok hH hp k₄ r₄) (by decide +kernel))
    fun s₅ ⟨⟨k₅, a₅, i₅, r₅⟩, v₅⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hH hp k₅ a₅ i₅ r₅) fun s₆ ⟨k₆, v₆, b₆⟩ => ?_)
  refine WP.mono (WP.preservedV (hk6_ok hH hp k₆ b₆) (by decide +kernel)) fun t ⟨h, v₇⟩ => ⟨h, ?_⟩
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
    WP isa (.block [.lsr .x .x9 .x3 (Nat.log2 H.B)]) s fun t => Cmp s₀ t ∧ VecKept s t ∧
      isa.eval (.zero .x .x9) t = some (decide (kl s₀ < H.B)) :=
  WP.preservedV (wp_lsr hlt fun t u => WP.block_nil ⟨h.of_upd u, by
    change eval (.zero .x .x9) t = _
    rw [eval_zero, u.gpr, h.gpr _ (by decide), shr_beq_zero, hpow]⟩) (by decide +kernel)

theorem sub_ok {s : State} (h : Cmp s₀ s) (hB : H.B < 4096) :
    WP isa (.block [.subImm .x .x9 .x3 H.B]) s fun t => Cmp s₀ t ∧ VecKept s t ∧
      isa.eval (.zero .x .x9) t = some (decide (kl s₀ = H.B)) :=
  WP.preservedV (wp_subImm hB fun t u => WP.block_nil ⟨h.of_upd u, by
    change eval (.zero .x .x9) t = _
    have ex : s₀.gpr .x3 = BitVec.ofNat 64 (kl s₀) := by simp
    rw [eval_zero, u.gpr, h.gpr _ (by decide), ex, sub_beq (s₀.gpr .x3).isLt (by omega)]⟩)
    (by decide +kernel)

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
  refine WP.seq (WP.mono (shr_ok cmp_refl hpow hlt) fun s₁ ⟨c₁, v₁, e₁⟩ => WP.seq ?_)
  refine WP.ite _ e₁ (fun hT => WP.block_nil (short_post hH c₁ v₁ (hS _ c₁ (by
    have := of_decide_eq_true hT; omega)))) fun hF => ?_
  refine WP.seq (WP.mono (sub_ok c₁ (by omega)) fun s₂ ⟨c₂, v₂, e₂⟩ => ?_)
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

end VG.Proof.Hmac.Generic.AArch64.InitAny
