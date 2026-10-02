import VerifiedGarbage.Proof.Hmac.Generic.Arm.Instances
import VerifiedGarbage.Proof.Framework.Narrow

/-!
# HMAC over any streaming hash function on 32-bit ARM: `init` for a key of any length

Untrusted: everything here is checked by Lean. As on x86-64 and AArch64
(`Proof/Hmac/Generic/AArch64/InitAny.lean`): `initAny` tests `key_len`
(`key_len >> log₂ B`, then `key_len - B`); a longer key is replaced by its
digest (`hashKey`, with the hash function's streaming functions, in
`scratch` after `init`'s buffers, `update` and `finalize` in their frames),
and `init` (`Init.lean`) runs on the key or the digest, from a state
permitting more than its narrowed one (`WP.of_narrow`, `RelCT.of_narrow`).
`scratch` is a stack argument, which no frame overwrites.
-/

namespace VG.Proof.Hmac.Generic.Arm

open VG.Arm
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length:
`VG.Spec.Hmac.initAnyKeyContract`. -/
def initAnyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨State.addr (s.gpr .r0), S.stateBytes⟩
    let outer : Region := ⟨State.addr (s.gpr .r1), S.stateBytes⟩
    let key : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 8 * W⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [key, args] ∧ s.wr = [inner, outer, scratch] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    (below s).Disjoint inner ∧ (below s).Disjoint outer ∧ (below s).Disjoint key ∧
    (below s).Disjoint scratch ∧
    (s.gpr .r0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32 ∧ (stackArg s 0).toNat + 8 * W ≤ 2 ^ 32 ∧
    16 ≤ s.sp.toNat ∧ s.sp.toNat + 4 ≤ 2 ^ 32
  post s s' :=
    let k0 := blockKey S.H (bytesAt s.mem (State.addr (s.gpr .r2)) (s.gpr .r3).toNat)
    S.Repr s'.mem (State.addr (s.gpr .r0)) (xorPad k0 ipad) ∧
      S.Repr s'.mem (State.addr (s.gpr .r1)) (xorPad k0 opad)
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

end VG.Proof.Hmac.Generic.Arm

namespace VG.Proof.Hmac.Generic.Arm.InitAny

open VG.Arm
open VG.Impl.Hmac.Generic.Arm (Hash scrAt)
open VG.Proof.Hmac.Generic.Arm
open VG.Proof.Hmac.Generic.Arm.Init (Pre inn out kp kl scr inR outR keyR scR argR stkR)
open VG.Proof.Hmac.Generic.Common (sub_of_off sub_of_self bytes_keep bytesAt_take)
open VG.Proof.Hmac.Common (bytesAt_length)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_cmp wp_subs wp_ldrSp op2_imm op2_reg op2_lsr eval_eq sub_beq)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash}

/-! ## Sizes -/

/-- The words of working space `init` gets: its buffers, rounded up. -/
abbrev nw0 (H : Hash) : Nat := (H.buf + 2 * H.B + 7) / 8

theorem ext_eq : H.ext = 8 * nw0 H := rfl

theorem fits0 : H.buf + 2 * H.B ≤ 8 * nw0 H := by simp only [nw0]; omega

theorem save_le_ext : 8 * H.W + 36 ≤ H.ext := by
  have := fits0 (H := H); simp only [Hash.buf] at this; rw [ext_eq]; omega

theorem ext_lt (hH : HashOK H) : H.ext + H.S + H.F < 4096 := by
  have := hH.hW; have := hH.hBB; have := hH.hSB; have := hH.hF
  simp only [ext_eq, nw0, Hash.buf]; omega

section
variable (Wt : Nat) (s₀ : State)

/-- All of `scratch`. -/
abbrev wsR : Region := ⟨State.addr (scr s₀), 8 * Wt⟩

/-- An address in `scratch`, and as a register holds it. -/
abbrev A (o : Nat) : Addr := State.addr (scr s₀) + BitVec.ofNat 64 o
abbrev A32 (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

end

/-- The precondition of `initAny`, with the sizes of `H`. -/
structure PreA (Wt : Nat) (s₀ : State) : Prop where
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, wsR Wt s₀]
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (wsR Wt s₀)
  o_s : (outR (H := H) s₀).Disjoint (wsR Wt s₀)
  k_s : (keyR s₀).Disjoint (wsR Wt s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (wsR Wt s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (wsR Wt s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * Wt ≤ 2 ^ 32
  sp16 : 16 ≤ s₀.sp.toNat
  spf : s₀.sp.toNat + 4 ≤ 2 ^ 32
  fits : H.ext + H.S + H.F ≤ 8 * Wt
  hDB : H.D ≤ H.B
  pow : 2 ^ Nat.log2 H.B = H.B

theorem preA_of (hH : HashOK H) {Wt : Nat} {s₀ : State} (h : (initAnyG hH.SH Wt).pre s₀)
    (hfit : H.ext + H.S + H.F ≤ 8 * Wt) (hDB : H.D ≤ H.B) (hpow : 2 ^ Nat.log2 H.B = H.B) :
    PreA (H := H) Wt s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, _, _, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21⟩ := h
  have hS := hH.hS
  simp only [hS] at *
  exact ⟨h1, h2, h3, h4, h5, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    hfit, hDB, hpow⟩

/-! ## Running `init` from a state that permits more -/

/-- `s`, permitted only what `init` needs: the key and its stack argument,
the states and its working space. -/
abbrev nar (H : Hash) (s : State) : State :=
  s.withRegions [keyR s, argR s] [inR (H := H) s, outR (H := H) s, scR (nw0 H) s]

/-- A state from which `init` runs: its precondition, narrowed, and the
narrowed regions within those of the state. -/
structure Ready (s : State) : Prop where
  pre : Pre (H := H) (nw0 H) (nar H s)
  cr : Covers ([keyR s, argR s] ++ [inR (H := H) s, outR (H := H) s, scR (nw0 H) s]) (s.rd ++ s.wr)
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
      hH.SH.Repr s'.mem (State.addr (inn s))
        (xorPad (blockKey hH.SH.H (bytesAt s.mem (State.addr (kp s)) (kl s))) ipad) ∧
      hH.SH.Repr s'.mem (State.addr (out s))
        (xorPad (blockKey hH.SH.H (bytesAt s.mem (State.addr (kp s)) (kl s))) opad) := by
  have h := Init.correct hH hr.pre
  refine WP.mono (WP.of_narrow (n := nar H s) (fun s₁ : State => s₁.withRegions s.rd s.wr)
    (fun t s₁ he => init_exec hr he) h) fun s' hs' => ?_
  obtain ⟨s₁, rfl, hg, hq⟩ := hs'
  exact ⟨hg, hq⟩

/-! ## `Ready` states -/

theorem below_arg (s : State) (_h : s.sp.toNat + 4 ≤ 2 ^ 32) : (below s).Disjoint (argR s) := by
  have e : stackArgAddr s 0 = State.addr s.sp := by simp [stackArgAddr]
  simp only [argR, e]
  exact (Offset.base_disjoint_below _ (n := 16) (k := 4) (by omega)).symm

section
variable {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀)
include hp

theorem nw_lt : 8 * Wt ≤ 2 ^ 32 := by have := hp.nw; omega

theorem ext_le : H.ext + H.S + H.F ≤ 8 * Wt := hp.fits

theorem ws_sub0 : Region.Sub (scR (nw0 H) s₀) (wsR Wt s₀) := by
  have := hp.fits; rw [ext_eq] at this; exact Region.sub_prefix (by omega)

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ 8 * Wt) : Region.Sub ⟨A s₀ o, n⟩ (wsR Wt s₀) :=
  Offset.sub_base _ h

theorem ws_mem : wsR Wt s₀ ∈ s₀.wr := by rw [hp.wr]; simp

theorem addrA {o : Nat} (ho : o < 8 * Wt) : State.addr (A32 s₀ o) = A s₀ o :=
  addr_add (by have := hp.nw; omega)

theorem toNatA {o : Nat} (ho : o < 8 * Wt) : (A32 s₀ o).toNat = (scr s₀).toNat + o := by
  have := hp.nw
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega), Nat.mod_eq_of_lt (by omega)]

include hH in
/-- A state with `init`'s arguments, for a key in the key's region or in
`scratch` after `init`'s working space, of at most a block. -/
theorem ready_at {t : State} (hr0 : t.gpr .r0 = inn s₀) (hr1 : t.gpr .r1 = out s₀) (hsp : t.sp = s₀.sp)
    (ha : scr t = scr s₀) (hrd : t.rd = s₀.rd) (hwr : t.wr = s₀.wr) (hkl : kl t ≤ H.B)
    (hk : (keyR t = keyR s₀ ∧ (kp t).toNat + kl t ≤ 2 ^ 32) ∨
      ∃ o, kp t = A32 s₀ o ∧ H.ext ≤ o ∧ o + kl t ≤ 8 * Wt ∧ o < 8 * Wt) :
    Ready (H := H) t := by
  have he := ext_le hp; have hL := nw_lt hp
  have hi : inR (H := H) t = inR (H := H) s₀ := by simp only [inR, inn, hr0]
  have ho : outR (H := H) t = outR (H := H) s₀ := by simp only [outR, out, hr1]
  have hs : scR (nw0 H) t = scR (nw0 H) s₀ := by simp only [scR, ha]
  have hA : argR t = argR s₀ := by simp only [argR, stackArgAddr, hsp]
  have hK : stkR t = stkR s₀ := by simp only [stkR, below, hsp]
  have sub := ws_sub0 hp
  have h8 : 8 * nw0 H ≤ 8 * Wt := by rw [← ext_eq]; omega
  have kfacts : (keyR t).Disjoint (scR (nw0 H) s₀) ∧ (kp t).toNat + kl t ≤ 2 ^ 32 ∧
      ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, (keyR t).base = r'.base + BitVec.ofNat 64 off ∧
        off + (keyR t).len ≤ r'.len := by
    rcases hk with ⟨e, n⟩ | ⟨o, e, h₁, h₂, h₃⟩
    · rw [e]
      exact ⟨hp.k_s.sub_right sub, n,
        sub_of_self (r := keyR s₀) (List.mem_append_left _ (by rw [hp.rd]; simp)) (Nat.le_refl _)⟩
    · have ek : keyR t = ⟨A s₀ o, kl t⟩ := by simp only [keyR, e, addrA hp (o := o) (by omega)]
      rw [ek]
      exact ⟨Offset.disjoint_base _ (by rw [← ext_eq]; omega) (by omega),
        by rw [e, toNatA hp (by omega)]; have := hp.nw; omega,
        sub_of_off (List.mem_append_right _ (ws_mem hp)) h₂⟩
  obtain ⟨k_s, nk, kc⟩ := kfacts
  refine ⟨⟨hkl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, nk, ?_, ?_, ?_, fits0, hH.hBB, hH.hW,
    hH.hSB⟩, ?_, ?_⟩
  · show (inR (H := H) t).Disjoint (outR (H := H) t); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) t).Disjoint (scR (nw0 H) t); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) t).Disjoint (scR (nw0 H) t); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR t).Disjoint (scR (nw0 H) t); rw [hs]; exact k_s
  · show (argR t).Disjoint (inR (H := H) t); rw [hA, hi]; exact hp.a_i
  · show (argR t).Disjoint (outR (H := H) t); rw [hA, ho]; exact hp.a_o
  · show (argR t).Disjoint (scR (nw0 H) t); rw [hA, hs]; exact hp.a_s.sub_right sub
  · show (stkR t).Disjoint (inR (H := H) t); rw [hK, hi]; exact hp.b_i
  · show (stkR t).Disjoint (outR (H := H) t); rw [hK, ho]; exact hp.b_o
  · show (stkR t).Disjoint (scR (nw0 H) t); rw [hK, hs]; exact hp.b_s.sub_right sub
  · show (t.gpr .r0).toNat + H.S ≤ 2 ^ 32; rw [hr0]; exact hp.ni
  · show (t.gpr .r1).toNat + H.S ≤ 2 ^ 32; rw [hr1]; exact hp.no
  · show (scr t).toNat + 8 * nw0 H ≤ 2 ^ 32; rw [ha]; have := hp.nw; omega
  · show 16 ≤ t.sp.toNat; rw [hsp]; exact hp.sp16
  · show t.sp.toNat + 4 ≤ 2 ^ 32; rw [hsp]; exact hp.spf
  · rw [hi, ho, hs, hA, hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact kc
      · exact sub_of_self (r := argR s₀) (List.mem_append_left _ (by rw [hp.rd]; simp)) (Nat.le_refl _)
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
  r4 : s.gpr .r4 = inn s₀
  r5 : s.gpr .r5 = out s₀
  r6 : s.gpr .r6 = kp s₀
  r9 : s.gpr .r9 = s₀.gpr .r3
  r11 : s.gpr .r11 = scr s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  key : bytesAt s.mem (State.addr (kp s₀)) (kl s₀) = bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)
  arg : stackArg s 0 = scr s₀

/-- The registers `HK` fixes. -/
abbrev hregs : List Reg := [.r4, .r5, .r6, .r9, .r11]

theorem hregs_pres : ∀ r ∈ hregs, r ∈ preserved ∧ r ≠ .lr := by decide

/-- What the tests of `key_len` leave: `r12` and the flags aside, our state. -/
structure Cmp (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .r12 → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem Cmp.of_upd {s s' : State} {s₀ : State} (h : Cmp s₀ s) {v : BitVec 32} (u : Upd s s' .r12 v) : Cmp s₀ s' :=
  ⟨fun r hr => (u.other r hr).trans (h.gpr r hr), u.mem.trans h.mem, u.rd.trans h.rd, u.wr.trans h.wr,
    u.sp.trans h.sp⟩

/-- `ext` and the digest's offset, as registers hold them. -/
abbrev stA (H : Hash) (s₀ : State) : BitVec 32 := A32 s₀ H.ext
abbrev dgA (H : Hash) (s₀ : State) : BitVec 32 := A32 s₀ (H.ext + H.S)

section
variable {Wt : Nat} {s₀ : State}

theorem HK.keep {s s' : State} (h : HK (H := H) s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hsp : s'.sp = s.sp) (hg : ∀ r ∈ hregs, s'.gpr r = s.gpr r) {rs : List Region}
    (hf : Frame rs s.mem s'.mem) (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hk : ∀ r ∈ rs, (keyR s₀).Disjoint r) (ha : ∀ r ∈ rs, (argR s₀).Disjoint r) : HK (H := H) s₀ s' := by
  refine ⟨hrd.trans h.rd, hwr.trans h.wr, hsp.trans h.sp, (hg _ (by simp)).trans h.r4,
    (hg _ (by simp)).trans h.r5, (hg _ (by simp)).trans h.r6, (hg _ (by simp)).trans h.r9,
    (hg _ (by simp)).trans h.r11, h.saved.frame H hf hs,
    (bytes_keep hf hk (Nat.le_of_lt (by have := (s₀.gpr .r3).isLt; show (s₀.gpr .r3).toNat < 2 ^ 64; omega))).trans h.key, ?_⟩
  have e : stackArgAddr s' 0 = stackArgAddr s₀ 0 := by simp only [stackArgAddr, hsp, h.sp]
  rw [stackArg, e, hf.readW (r := argR s₀) (Region.contains_self _ _) ha (by decide), ← h.arg, stackArg,
    stackArgAddr, stackArgAddr, h.sp]

theorem HK.upd {s s' : State} (h : HK (H := H) s₀ s) {d : Reg} {v : BitVec 32} (u : Upd s s' d v)
    (hd : d ∉ hregs) : HK (H := H) s₀ s' :=
  h.keep u.rd u.wr u.sp (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp) (by simp)

variable (hp : PreA (H := H) Wt s₀)
include hp

/-- A region a call writes: the working space of the functions we call, or
a part of `scratch` after the save area. -/
theorem HK.call {s s' : State} (h : HK (H := H) s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨State.addr (scr s₀), k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = ⟨A s₀ o, k⟩ ∧ 8 * H.W + 36 ≤ o ∧ o + k ≤ 8 * Wt) : HK (H := H) s₀ s' := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have f := ha.frame
  rw [below_eq h.sp] at f
  refine h.keep ha.rd ha.wr ha.sp (fun r hr => ha.cs r (hregs_pres r hr).1 (hregs_pres r hr).2) f ?_ ?_ ?_
  all_goals intro r hr; rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact Offset.disjoint_base _ hk (by omega)
    · exact Offset.disjoint _ (Or.inl h₁) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.b_s.sub_right ssub).symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact hp.k_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.k_s.sub_right (part_sub h₂)
  · simp only [List.mem_singleton] at hr; subst hr
    exact hp.b_k.symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact hp.a_s.sub_right (Region.sub_prefix (by omega))
    · exact hp.a_s.sub_right (part_sub h₂)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (below_arg s₀ hp.spf).symm

omit hp in
/-- `d ← scratch + o`, through `r12`. -/
theorem scrAt_ok {s : State} {d : Reg} (_hd : d ≠ .r12) (h11 : s.gpr .r11 = scr s₀) {o : Nat} (ho : o < 2 ^ 16)
    {rest : List Instr} {Q : State → Prop}
    (k : ∀ s', s'.gpr d = A32 s₀ o → (∀ r, r ≠ d → r ≠ .r12 → s'.gpr r = s.gpr r) → s'.mem = s.mem →
      s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) :
    WP isa (.block (scrAt d o ++ rest)) s Q := by
  simp only [scrAt, List.cons_append, List.nil_append]
  refine wp_movw fun s₁ u₁ => wp_add (op2_reg _ _) fun s₂ u₂ => k s₂ ?_ (fun r h₁ h₂ => ?_)
    (by rw [u₂.mem, u₁.mem]) (by rw [u₂.rd, u₁.rd]) (by rw [u₂.wr, u₁.wr]) (by rw [u₂.sp, u₁.sp])
  · rw [u₂.gpr, u₁.other _ (by decide), u₁.gpr, h11, movw_ofNat ho]
  · rw [u₂.other r h₁, u₁.other r h₂]

omit hp in
theorem HK.same {s s' : State} (h : HK (H := H) s₀ s) (hg : ∀ r ∈ hregs, s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) (hsp : s'.sp = s.sp) : HK (H := H) s₀ s' :=
  h.keep hrd hwr hsp hg (rs := []) (by rw [hm]; exact Frame.refl _ _) (by simp) (by simp) (by simp)

/-- The prologue: `scratch` loaded, our caller's registers saved, ours set,
and `init`'s argument. -/
theorem pro_ok (hH : HashOK H) {s : State} (c : Cmp s₀ s) :
    WP isa (.block ([.ldrSp .r12 0] ++ H.save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
      .mov .r9 (.reg .r3), .mov .r11 (.reg .r12)] ++ scrAt .r0 H.ext)) s fun t =>
      HK (H := H) s₀ t ∧ t.gpr .r0 = stA H s₀ := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have ea : State.addr (s.sp + BitVec.ofNat 32 0) = stackArgAddr s₀ 0 := by simp [stackArgAddr, c.sp]
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldrSp (by decide) ea (by rw [c.rd, hp.rd]; exact ⟨argR s₀, by simp, Region.contains_self _ _⟩)
    fun s₁ u₁ => ?_
  have h12 : s₁.gpr .r12 = scr s₀ := by rw [u₁.gpr, c.mem]; rfl
  refine save_ok H (scr := scr s₀) h12 hH.hW (by rw [u₁.wr, c.wr]; exact ws_mem hp) (L := 8 * Wt) (by omega)
    hp.nw fun s₂ g₂ rd₂ wr₂ sp₂ f₂ sv₂ => ?_
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ => wp_mov (op2_reg _ _) fun s₅ u₅ =>
    wp_mov (op2_reg _ _) fun s₆ u₆ => wp_mov (op2_reg _ _) fun s₇ u₇ => ?_
  have g₂' : ∀ r, r ≠ .r12 → s₂.gpr r = s₀.gpr r := fun r h => by rw [g₂, u₁.other r h, c.gpr r h]
  have r11 : s₇.gpr .r11 = scr s₀ := by
    rw [u₇.gpr, u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      g₂, h12]
  rw [← List.append_nil (scrAt .r0 H.ext)]
  refine scrAt_ok (by decide) r11 (by omega) fun s₈ x₈ o₈ m₈ rd₈ wr₈ sp₈ => WP.block_nil ⟨?_, x₈⟩
  have hm : s₈.mem = s₂.mem := by rw [m₈, u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem]
  have g : ∀ r ∈ hregs, s₈.gpr r = s₇.gpr r := fun r hr => o₈ r (by revert r hr; decide) (by revert r hr; decide)
  have fr : ∀ {rs : List Region}, rs = [saveR H (scr s₀)] → Frame rs s₀.mem s₈.mem := fun e => by
    rw [hm, e, ← c.mem, ← u₁.mem]; exact f₂
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  refine ⟨by rw [rd₈, u₇.rd, u₆.rd, u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, c.rd],
    by rw [wr₈, u₇.wr, u₆.wr, u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, c.wr],
    by rw [sp₈, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp, c.sp], ?_, ?_, ?_, ?_, by rw [g _ (by simp), r11],
    ?_, ?_, ?_⟩
  · rw [g _ (by simp), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide),
      u₄.other _ (by decide), u₃.gpr, g₂' _ (by decide)]
  · rw [g _ (by simp), u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr,
      u₃.other _ (by decide), g₂' _ (by decide)]
  · rw [g _ (by simp), u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr, u₄.other _ (by decide),
      u₃.other _ (by decide), g₂' _ (by decide)]
  · rw [g _ (by simp), u₇.other _ (by decide), u₆.gpr, u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), g₂' _ (by decide)]
  · rw [hm]
    exact SavedRegs.of_eq H sv₂ fun r hr => by rw [u₁.other r (by revert r hr; decide), c.gpr r (by revert r hr; decide)]
  · exact bytes_keep (fr rfl) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.k_s.sub_right ssub)
      (Nat.le_of_lt (by have := (s₀.gpr .r3).isLt; show (s₀.gpr .r3).toNat < 2 ^ 64; omega))
  · have e : stackArgAddr s₈ 0 = stackArgAddr s₀ 0 := by
      simp only [stackArgAddr, sp₈, u₇.sp, u₆.sp, u₅.sp, u₄.sp, u₃.sp, sp₂, u₁.sp, c.sp]
    rw [stackArg, e, (fr rfl).readW (r := argR s₀) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.a_s.sub_right ssub) (by decide)]
    rfl

include hH in
theorem stA_ok : (stA H s₀).toNat + H.S ≤ 2 ^ 32 ∧ State.addr (stA H s₀) = A s₀ H.ext := by
  have he := ext_le hp; have := hp.nw; have := hH.hD0; have := hH.hDF
  exact ⟨by rw [toNatA hp (by omega)]; omega, addrA hp (by omega)⟩

include hH in
theorem dgA_ok : (dgA H s₀).toNat + H.F ≤ 2 ^ 32 ∧ State.addr (dgA H s₀) = A s₀ (H.ext + H.S) := by
  have he := ext_le hp; have := hp.nw; have := hH.hD0; have := hH.hDF
  exact ⟨by rw [toNatA hp (by omega)]; omega, addrA hp (by omega)⟩

/-- The streaming state of the key, started. -/
theorem hk1_ok {s : State} (h : HK (H := H) s₀ s) (hd : s.gpr .r0 = stA H s₀) :
    WP isa (.call H.initN H.initC) s fun t => HK (H := H) s₀ t ∧
      hH.SH.Repr t.mem (A s₀ H.ext) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  obtain ⟨n, ea⟩ := stA_ok hH hp
  refine init_call hH hd n (Covers.of_sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ea]
      exact sub_of_off (rs := s.wr) (by rw [h.wr]; exact ws_mem hp) (by omega)) fun s₂ a₂ r₂ =>
    ⟨h.call hp a₂ fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩,
      ea ▸ r₂⟩

omit hp in
theorem count_zero {t : State} (h2 : t.gpr .r2 = 0) (h3 : t.gpr .r3 = 0) : count t = BitVec.ofNat 64 0 := by
  rw [count, h2, h3]; rfl

omit hp in
theorem count_reg {t : State} {x : BitVec 32} (h2 : t.gpr .r2 = x) (h3 : t.gpr .r3 = 0) :
    count t = BitVec.ofNat 64 x.toNat := by
  rw [count, h2, h3]
  apply BitVec.eq_of_toNat_eq
  have := x.isLt
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, show (0 : BitVec 32).toNat = 0 from rfl,
    Nat.zero_shiftLeft, Nat.zero_or]
  omega

/-- `update`'s arguments: the key. -/
theorem hk2_ok {s : State} (h : HK (H := H) s₀ s) (hr : hH.SH.Repr s.mem (A s₀ H.ext) []) :
    WP isa (.block (scrAt .r0 H.ext ++ [.mov .r1 (.reg .r6), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11),
      .mov .r2 (.imm 0), .mov .r3 (.imm 0)])) s fun t => HK (H := H) s₀ t ∧
      UpdArgs hH t (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧ count t = BitVec.ofNat 64 0 ∧
      hH.SH.Repr t.mem (A s₀ H.ext) [] := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  obtain ⟨nst, ea⟩ := stA_ok hH hp
  refine scrAt_ok (by decide) h.r11 (by omega) fun s₁ x₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have k₁ := h.same (fun r hr => o₁ r (by revert r hr; decide) (by revert r hr; decide)) m₁ rd₁ wr₁ sp₁
  refine wp_mov (op2_reg _ _) fun s₂ u₂ => wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_reg _ _) fun s₄ u₄ =>
    wp_mov (op2_imm (by decide)) fun s₅ u₅ => wp_mov (op2_imm (by decide)) fun s₆ u₆ => WP.block_nil ?_
  have k₆ := ((((k₁.upd u₂ (by decide)).upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)).upd u₆
    (by decide)
  have hm : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, m₁]
  refine ⟨k₆, ?_, count_zero (by rw [u₆.other _ (by decide), u₅.gpr]) (by rw [u₆.gpr]), by rw [hm]; exact hr⟩
  have ssc : Region.Sub ⟨State.addr (scr s₀), hH.Wb⟩ (wsR Wt s₀) := Region.sub_prefix (by omega)
  exact
    { r0 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.other _ (by decide), x₁]
      r1 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          u₂.gpr, k₁.r6]
      r7 := by
        rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr,
          u₂.other _ (by decide), k₁.r9]; simp
      r10 := by rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.other _ (by decide),
          u₂.other _ (by decide), k₁.r11]
      hlen := (s₀.gpr .r3).isLt
      sp16 := by rw [k₆.sp]; exact hp.sp16
      cd := covers_one (List.mem_append_left _ (by rw [k₆.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ea]; exact sub_of_off (rs := s₆.wr) (by rw [k₆.wr]; exact ws_mem hp) (by omega)
        · exact sub_of_self (rs := s₆.wr) (r := wsR Wt s₀) (by rw [k₆.wr]; exact ws_mem hp) (by show hH.Wb ≤ 8 * Wt; omega)
      st_sc := by rw [ea]; exact Offset.disjoint_base _ (by omega) (by omega)
      d_st := by rw [ea]; exact hp.k_s.sub_right (part_sub (by omega))
      d_sc := hp.k_s.sub_right ssc
      b_st := by rw [below_eq k₆.sp, ea]; exact hp.b_s.sub_right (part_sub (by omega))
      b_d := by rw [below_eq k₆.sp]; exact hp.b_k
      b_sc := by rw [below_eq k₆.sp]; exact hp.b_s.sub_right ssc
      nst := nst
      nd := hp.nk
      nsc := by have := hp.nw; omega }

/-- The key absorbed. -/
theorem hk3_ok {s : State} (h : HK (H := H) s₀ s) (ua : UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀))
    (hc : count s = BitVec.ofNat 64 0) (hr : hH.SH.Repr s.mem (A s₀ H.ext) []) :
    WP isa (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16)) s fun t =>
      HK (H := H) s₀ t ∧ hH.SH.Repr t.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  obtain ⟨_, ea⟩ := stA_ok hH hp
  refine upd_frame hH ua fun s₈ a₈ r₈ => ⟨h.call hp a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] (ea ▸ hr) hc
    rwa [List.nil_append, h.key, ea] at this

/-- `finalize`'s arguments: the digest after the state. -/
theorem hk4_ok {s : State} (h : HK (H := H) s₀ s)
    (hr : hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) :
    WP isa (.block (scrAt .r0 H.ext ++ scrAt .r1 (H.ext + H.S) ++ [.mov .r2 (.reg .r9), .mov .r3 (.imm 0),
      .mov .r12 (.reg .r11)])) s fun t => HK (H := H) s₀ t ∧
      FinArgs hH t (stA H s₀) (dgA H s₀) (scr s₀) ∧ count t = BitVec.ofNat 64 (kl s₀) ∧
      hH.SH.Repr t.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  obtain ⟨nst, ea⟩ := stA_ok hH hp
  obtain ⟨ndg, eo⟩ := dgA_ok hH hp
  simp only [List.append_assoc]
  refine scrAt_ok (by decide) h.r11 (by omega) fun s₁ x₁ o₁ m₁ rd₁ wr₁ sp₁ => ?_
  have k₁ := h.same (fun r hr => o₁ r (by revert r hr; decide) (by revert r hr; decide)) m₁ rd₁ wr₁ sp₁
  refine scrAt_ok (by decide) k₁.r11 (by omega) fun s₂ x₂ o₂ m₂ rd₂ wr₂ sp₂ => ?_
  have k₂ := k₁.same (fun r hr => o₂ r (by revert r hr; decide) (by revert r hr; decide)) m₂ rd₂ wr₂ sp₂
  refine wp_mov (op2_reg _ _) fun s₃ u₃ => wp_mov (op2_imm (by decide)) fun s₄ u₄ =>
    wp_mov (op2_reg _ _) fun s₅ u₅ => WP.block_nil ?_
  have k₅ := ((k₂.upd u₃ (by decide)).upd u₄ (by decide)).upd u₅ (by decide)
  have hm : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, m₂, m₁]
  refine ⟨k₅, ?_, count_reg (by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, k₂.r9])
    (by rw [u₅.other _ (by decide), u₄.gpr]), by rw [hm]; exact hr⟩
  have ssc : Region.Sub ⟨State.addr (scr s₀), hH.Wb⟩ (wsR Wt s₀) := Region.sub_prefix (by omega)
  exact
    { r0 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
          o₂ _ (by decide) (by decide), x₁]
      r1 := by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), x₂]
      r12 := by rw [u₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), k₂.r11]
      sp16 := by rw [k₅.sp]; exact hp.sp16
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ea]; exact sub_of_off (rs := s₅.wr) (by rw [k₅.wr]; exact ws_mem hp) (by omega)
        · rw [eo]; exact sub_of_off (rs := s₅.wr) (by rw [k₅.wr]; exact ws_mem hp) (by omega)
        · exact sub_of_self (rs := s₅.wr) (r := wsR Wt s₀) (by rw [k₅.wr]; exact ws_mem hp) (by show hH.Wb ≤ 8 * Wt; omega)
      st_o := by rw [ea, eo]; exact Offset.disjoint _ (Or.inl (Nat.le_refl _)) (by omega) (by omega)
      st_sc := by rw [ea]; exact Offset.disjoint_base _ (by omega) (by omega)
      o_sc := by rw [eo]; exact Offset.disjoint_base _ (by omega) (by omega)
      b_st := by rw [below_eq k₅.sp, ea]; exact hp.b_s.sub_right (part_sub (by omega))
      b_o := by rw [below_eq k₅.sp, eo]; exact hp.b_s.sub_right (part_sub (by omega))
      b_sc := by rw [below_eq k₅.sp]; exact hp.b_s.sub_right ssc
      nst := nst
      no := ndg
      nsc := by have := hp.nw; omega }

/-- The digest. -/
theorem hk5_ok {s : State} (h : HK (H := H) s₀ s) (fa : FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀))
    (hc : count s = BitVec.ofNat 64 (kl s₀))
    (hr : hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) :
    WP isa (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8)) s fun t => HK (H := H) s₀ t ∧
      bytesAt t.mem (A s₀ (H.ext + H.S)) H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hWb := hH.hWb
  obtain ⟨_, ea⟩ := stA_ok hH hp
  obtain ⟨_, eo⟩ := dgA_ok hH hp
  refine fin_frame hH fa fun s₁₃ a₁₃ r₁₃ => ⟨h.call hp a₁₃ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩
    · rw [eo]; exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ hH.hDF, ← eo]
    exact r₁₃ _ (ea ▸ hr) (by rw [bytesAt_length]; have := (s₀.gpr .r3).isLt; show (s₀.gpr .r3).toNat < 2 ^ 64; omega)
      (by rw [hc, bytesAt_length])

/-- What `hashKey` leaves: `init`'s arguments, with the digest as the key,
and our caller's registers. -/
structure Hashed (s₀ t : State) : Prop where
  rd : t.rd = s₀.rd
  wr : t.wr = s₀.wr
  sp : t.sp = s₀.sp
  cs : ∀ r ∈ preserved, t.gpr r = s₀.gpr r
  r0 : t.gpr .r0 = inn s₀
  r1 : t.gpr .r1 = out s₀
  r2 : t.gpr .r2 = dgA H s₀
  r3 : t.gpr .r3 = BitVec.ofNat 32 H.D
  arg : stackArg t 0 = scr s₀
  dg : bytesAt t.mem (A s₀ (H.ext + H.S)) H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))

/-- The epilogue: `init`'s arguments, and our caller's registers back. -/
theorem hk6_ok {s : State} (h : HK (H := H) s₀ s)
    (hd : bytesAt s.mem (A s₀ (H.ext + H.S)) H.D = hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) :
    WP isa (.block ([.mov .r0 (.reg .r4), .mov .r1 (.reg .r5)] ++ scrAt .r2 (H.ext + H.S) ++
      [.movw .r3 (BitVec.ofNat 16 H.D)] ++ H.restore)) s (Hashed hH s₀) := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H); have hl := ext_lt hH
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => ?_
  have k₂ := (h.upd u₁ (by decide)).upd u₂ (by decide)
  refine scrAt_ok (by decide) k₂.r11 (by omega) fun s₃ x₃ o₃ m₃ rd₃ wr₃ sp₃ => ?_
  have k₃ := k₂.same (fun r hr => o₃ r (by revert r hr; decide) (by revert r hr; decide)) m₃ rd₃ wr₃ sp₃
  refine wp_movw fun s₄ u₄ => ?_
  have k₄ := k₃.upd u₄ (by decide)
  refine WP.mono (restore_ok H k₄.r11 hH.hW k₄.saved (by rw [k₄.wr]; exact ws_mem hp) (L := 8 * Wt) (by omega)
    hp.nw) fun t ⟨hm, hrd, hwr, hsp, hcs, ho⟩ => ?_
  refine ⟨by rw [hrd, k₄.rd], by rw [hwr, k₄.wr], by rw [hsp, k₄.sp],
    fun r hr => hcs r (Arm.preserved_saved r hr), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ho _ (by decide), u₄.other _ (by decide), o₃ _ (by decide) (by decide), u₂.other _ (by decide), u₁.gpr,
      h.r4]
  · rw [ho _ (by decide), u₄.other _ (by decide), o₃ _ (by decide) (by decide), u₂.gpr, u₁.other _ (by decide),
      h.r5]
  · rw [ho _ (by decide), u₄.other _ (by decide), x₃]
  · rw [ho _ (by decide), u₄.gpr, movw_ofNat (by have := hH.hDF; have := hH.hF; omega)]
  · have e : stackArgAddr t 0 = stackArgAddr s₄ 0 := by simp only [stackArgAddr, hsp]
    rw [stackArg, e, hm]; exact k₄.arg
  · rw [hm, u₄.mem, m₃, u₂.mem, u₁.mem]; exact hd

theorem hashKey_ok {s : State} (c : Cmp s₀ s) : WP isa H.hashKey s (Hashed hH s₀) := by
  unfold Hash.hashKey
  refine WP.seq (WP.mono (pro_ok hp hH c) fun s₁ ⟨k₁, d₁⟩ => ?_)
  refine WP.seq (WP.mono (hk1_ok hH hp k₁ d₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hH hp k₂ r₂) fun s₃ ⟨k₃, a₃, c₃, r₃⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hH hp k₃ a₃ c₃ r₃) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hH hp k₄ r₄) fun s₅ ⟨k₅, a₅, c₅, r₅⟩ => ?_)
  refine WP.seq (WP.mono (hk5_ok hH hp k₅ a₅ c₅ r₅) fun s₆ ⟨k₆, b₆⟩ => ?_)
  exact hk6_ok hH hp k₆ b₆

end

/-! ## The tests of `key_len` -/

section
variable {s₀ : State}

theorem shr_ok (hlog : 1 ≤ Nat.log2 H.B ∧ Nat.log2 H.B ≤ 31) (hpow : 2 ^ Nat.log2 H.B = H.B) :
    WP isa (.block [.mov .r12 (.shifted .r3 .lsr (Nat.log2 H.B)), .cmp .r12 (.imm 0)]) s₀ fun t =>
      Cmp s₀ t ∧ isa.eval .eq t = some (decide (kl s₀ < H.B)) := by
  refine wp_mov (op2_lsr hlog) fun s₁ u₁ => wp_cmp (op2_imm (by decide)) fun s₂ f₂ z₂ => WP.block_nil
    ⟨⟨fun r hr => by rw [f₂.gpr, u₁.other r hr], by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd],
      by rw [f₂.wr, u₁.wr], by rw [f₂.sp, u₁.sp]⟩, ?_⟩
  change eval .eq s₂ = _
  have ex : s₀.gpr .r3 = BitVec.ofNat 32 (kl s₀) := by simp
  rw [eval_eq, z₂, u₁.gpr, ex, VG.Proof.MdStream.Arm.ofNat_shr (s₀.gpr .r3).isLt,
    VG.Proof.MdStream.Arm.cmp0 (by have := (s₀.gpr .r3).isLt; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) this),
    hpow]
  have hB : 0 < H.B := by rw [← hpow]; exact Nat.two_pow_pos _
  by_cases h : kl s₀ < H.B
  · simp [h, Nat.div_eq_of_lt h]
  · have : 0 < kl s₀ / H.B := Nat.div_pos (by omega) hB
    simp [h]; omega

theorem sub_ok {s : State} (c : Cmp s₀ s) (hB : H.B ≤ 128) (he : encodable (BitVec.ofNat 32 H.B) = true) :
    WP isa (.block [.subs .r12 .r3 (.imm (BitVec.ofNat 32 H.B))]) s fun t =>
      Cmp s₀ t ∧ isa.eval .eq t = some (decide (kl s₀ = H.B)) := by
  refine wp_subs (op2_imm he) fun t u z => WP.block_nil ⟨c.of_upd u, ?_⟩
  change eval .eq t = _
  have ex : s₀.gpr .r3 = BitVec.ofNat 32 (kl s₀) := by simp
  rw [eval_eq, z, c.gpr _ (by decide), ex, sub_beq (s₀.gpr .r3).isLt (by omega)]

end

/-! ## Correctness -/

section
variable {Wt : Nat} {s₀ : State}

/-- What `initAny` leaves: the calling convention's obligations, and the
states for the key. -/
abbrev Post (s₀ s' : State) : Prop :=
  abiPreserved s₀ s' ∧
    hH.SH.Repr s'.mem (State.addr (inn s₀))
      (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ipad) ∧
    hH.SH.Repr s'.mem (State.addr (out s₀))
      (xorPad (blockKey hH.SH.H (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) opad)

theorem Cmp.scr {s : State} (c : Cmp s₀ s) : scr s = scr s₀ := by
  simp only [stackArg, stackArgAddr, c.mem, c.sp]

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : H.B < k.length) (hl : (hH.SH.H.hash k).length ≤ H.B) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB
  simp only [blockKey, hB, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.B < (hH.SH.H.hash k).length by omega))]

/-- From a `Ready` state with our arguments, `init` leaves `Post`. -/
theorem short_post {s : State} (c : Cmp s₀ s) (hr : Ready (H := H) s) : WP isa H.init s (Post hH s₀) := by
  refine WP.mono (init_ok hH hr) fun s' ⟨⟨hcs, hsp⟩, hi, ho⟩ => ⟨⟨fun r hr' => ?_, by rw [hsp, c.sp]⟩, ?_, ?_⟩
  · rw [hcs r hr', c.gpr r (by revert r hr'; decide)]
  · simp only [inn, kp, kl, c.gpr _ (show Reg.r0 ≠ .r12 by decide), c.gpr _ (show Reg.r2 ≠ .r12 by decide),
      c.gpr _ (show Reg.r3 ≠ .r12 by decide), c.mem] at hi
    exact hi
  · simp only [out, kp, kl, c.gpr _ (show Reg.r1 ≠ .r12 by decide), c.gpr _ (show Reg.r2 ≠ .r12 by decide),
      c.gpr _ (show Reg.r3 ≠ .r12 by decide), c.mem] at ho
    exact ho

/-- After `hashKey`, `init` runs on the digest. -/
theorem ready_long (hp : PreA (H := H) Wt s₀) {t : State} (h : Hashed hH s₀ t) : Ready (H := H) t := by
  have hD := hp.hDB; have := hH.hDF; have := hH.hF; have he := hp.fits; have := hH.hD0
  refine ready_at hH hp h.r0 h.r1 h.sp h.arg h.rd h.wr
    (by show (t.gpr .r3).toNat ≤ H.B; rw [h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hD)
    (.inr ⟨H.ext + H.S, h.r2, Nat.le_add_right _ _, ?_, by omega⟩)
  show H.ext + H.S + (t.gpr .r3).toNat ≤ 8 * Wt
  rw [h.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

theorem correct_gen (hlog : 1 ≤ Nat.log2 H.B ∧ Nat.log2 H.B ≤ 31) (hpow : 2 ^ Nat.log2 H.B = H.B)
    (he : encodable (BitVec.ofNat 32 H.B) = true)
    (hS : ∀ s, Cmp s₀ s → kl s₀ ≤ H.B → Ready (H := H) s) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀) :
    WP isa H.initAny s₀ (Post hH s₀) := by
  have hB := hH.hBB
  unfold Hash.initAny
  refine WP.seq (WP.mono (shr_ok hlog hpow) fun s₁ ⟨c₁, e₁⟩ => WP.seq ?_)
  refine WP.ite _ e₁ (fun hT => WP.block_nil (short_post hH c₁ (hS _ c₁ (by
    have := of_decide_eq_true hT; omega)))) fun hF => ?_
  refine WP.seq (WP.mono (sub_ok c₁ hB he) fun s₂ ⟨c₂, e₂⟩ => ?_)
  refine WP.ite _ e₂ (fun hT => WP.block_nil (short_post hH c₂ (hS _ c₂ (by
    have := of_decide_eq_true hT; omega)))) fun hF' => ?_
  have hk : H.B < kl s₀ := by have := of_decide_eq_false hF; have := of_decide_eq_false hF'; omega
  have hp := hL hk
  refine WP.mono (hashKey_ok hH hp c₂) fun s₃ h₃ => ?_
  have hD := hp.hDB; have := hH.hDF; have := hH.hF
  refine WP.mono (init_ok hH (ready_long hH hp h₃)) fun s' ⟨⟨hcs, hsp⟩, hi, ho⟩ => ?_
  have hkey : bytesAt s₃.mem (State.addr (kp s₃)) (kl s₃) =
      hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀)) := by
    have e2 : State.addr (kp s₃) = A s₀ (H.ext + H.S) := by
      simp only [kp, h₃.r2]; exact (dgA_ok hH hp).2
    have e3 : kl s₃ = H.D := by simp only [kl, h₃.r3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show H.D < 2 ^ 32 by omega)]
    rw [e2, e3]; exact h₃.dg
  have hlen : (hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))).length ≤ H.B := by
    rw [← h₃.dg, bytesAt_length]; exact hD
  have hk0 := blockKey_hash hH (by rw [bytesAt_length]; exact hk) hlen
  refine ⟨⟨fun r hr => (hcs r hr).trans (h₃.cs r hr), by rw [hsp, h₃.sp]⟩, ?_, ?_⟩
  · simp only [inn, h₃.r0, hkey, hk0] at hi; exact hi
  · simp only [out, h₃.r1, hkey, hk0] at ho; exact ho

end

/-! ## Constant time -/

abbrev proBlock (H : Hash) : List Instr :=
  [.ldrSp .r12 0] ++ H.save ++ [.mov .r4 (.reg .r0), .mov .r5 (.reg .r1), .mov .r6 (.reg .r2),
    .mov .r9 (.reg .r3), .mov .r11 (.reg .r12)] ++ scrAt .r0 H.ext

abbrev argU (H : Hash) : List Instr :=
  scrAt .r0 H.ext ++ [.mov .r1 (.reg .r6), .mov .r7 (.reg .r9), .mov .r10 (.reg .r11), .mov .r2 (.imm 0),
    .mov .r3 (.imm 0)]

abbrev argF (H : Hash) : List Instr :=
  scrAt .r0 H.ext ++ scrAt .r1 (H.ext + H.S) ++ [.mov .r2 (.reg .r9), .mov .r3 (.imm 0), .mov .r12 (.reg .r11)]

abbrev epi (H : Hash) : List Instr :=
  [.mov .r0 (.reg .r4), .mov .r1 (.reg .r5)] ++ scrAt .r2 (H.ext + H.S) ++ [.movw .r3 (BitVec.ofNat 16 H.D)] ++
    H.restore

/-- The taint checks of the tests of `key_len` and of `hashKey`'s pieces
between its calls. -/
structure Checks (H : Hash) : Prop where
  shr : ∃ hc, (VG.Taint.check taint (Taint.ofRegs Init.args)
    (.block [.mov .r12 (.shifted .r3 .lsr (Nat.log2 H.B)), .cmp .r12 (.imm 0)]) hc).isSome = true
  sub : ∃ hc, (VG.Taint.check taint (Taint.ofRegs Init.args)
    (.block [.subs .r12 .r3 (.imm (BitVec.ofNat 32 H.B))]) hc).isSome = true
  pro : ∃ hc, (VG.Taint.check taint (argTaint Init.args 4) (.block (proBlock H)) hc).isSome = true
  argU : ∃ hc, (VG.Taint.check taint (Taint.ofRegs hregs) (.block (argU H)) hc).isSome = true
  argF : ∃ hc, (VG.Taint.check taint (Taint.ofRegs hregs) (.block (argF H)) hc).isSome = true
  epi : ∃ hc, (VG.Taint.check taint (Taint.ofRegs hregs) (.block (epi H)) hc).isSome = true

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
  rcases hr with rfl | rfl | rfl | rfl | rfl
  · rw [h.r4, h'.r4, inn, inn, hq.r0]
  · rw [h.r5, h'.r5, out, out, hq.r1]
  · rw [h.r6, h'.r6, kp, kp, hq.r2]
  · rw [h.r9, h'.r9, hq.r3]
  · rw [h.r11, h'.r11, scr, scr, hq.a0]

include hq in
theorem cmp_agree {s s' : State} (c : Cmp s₀ s) (c' : Cmp s₀' s') : ∀ r ∈ Init.args, s.gpr r = s'.gpr r := by
  intro r hr
  have h12 : r ≠ .r12 := by revert r hr; decide
  rw [c.gpr r h12, c'.gpr r h12]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact hq.r0
  · exact hq.r1
  · exact hq.r2
  · exact hq.r3

variable (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
include hp hp' hq

omit hq hp hp' in
theorem args_wf' {s : State} {s₁ : State} (hp₁ : PreA (H := H) Wt s₁) (c : Cmp s₁ s) :
    s.sp.toNat + 4 ≤ 2 ^ 32 ∧ ∀ r ∈ s.wr, Region.Disjoint ⟨State.addr s.sp, 4⟩ r := by
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s₁ := by simp [stackArgAddr, c.sp]
  refine ⟨by rw [c.sp]; exact hp₁.spf, ?_⟩
  simp only [e, c.wr, hp₁.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact hp₁.a_i
  · exact hp₁.a_o
  · exact hp₁.a_s

theorem hashKey_rel (hca : Checks H) :
    RelCT isa (fun s s' => Cmp s₀ s ∧ Cmp s₀' s') H.hashKey
      fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' := by
  have eS : stA H s₀' = stA H s₀ := by simp only [stA, A32, scr, hq.a0]
  have eD : dgA H s₀' = dgA H s₀ := by simp only [dgA, A32, scr, hq.a0]
  have eA : ∀ o, A s₀' o = A s₀ o := fun o => by simp only [A, scr, hq.a0]
  have eK : kp s₀' = kp s₀ := hq.r2.symm
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.r3]
  have e8 : scr s₀' = scr s₀ := hq.a0.symm
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  obtain ⟨nst, ea⟩ := stA_ok hH hp
  unfold Hash.hashKey
  have pro : RelCT isa (fun s s' => Cmp s₀ s ∧ Cmp s₀' s') (.block (proBlock H))
      fun s s' => (HK (H := H) s₀ s ∧ s.gpr .r0 = stA H s₀) ∧ (HK (H := H) s₀' s' ∧ s'.gpr .r0 = stA H s₀) :=
    rel_agree (argTaint Init.args 4) (fun s s' c c' =>
        agree_argTaint (cmp_agree hq c c') (by rw [c.sp, c'.sp, hq.sp]) (args_wf' hp c)
          (args_wf' hp' c')
          (argMem_of (j := 1) (by rw [c.sp, c'.sp, hq.sp]) (by rw [c.sp]; exact hp.spf) fun i hi => by
            rw [show i = 0 by omega]; exact c.scr.trans (hq.a0.trans c'.scr.symm))) hca.pro
      (fun _ c => pro_ok hp hH c)
      (fun _ c => WP.mono (pro_ok hp' hH c) fun _ ⟨k, d⟩ => ⟨k, d.trans eS⟩)
  have i1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ s.gpr .r0 = stA H s₀) ∧
      (HK (H := H) s₀' s' ∧ s'.gpr .r0 = stA H s₀)) (.call H.initN H.initC)
      fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (A s₀ H.ext) []) ∧
        (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (A s₀ H.ext) []) :=
    rel_wp (init_rel hH (st := stA H s₀) fun s s' ⟨⟨k, d⟩, ⟨k', d'⟩⟩ =>
        ⟨d, d', nst, Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [ea]
            exact sub_of_off (rs := s.wr) (by rw [k.wr]; exact ws_mem hp) (by omega),
          Covers.of_sub fun r hr => by
            simp only [List.mem_singleton] at hr; subst hr; rw [ea, ← eA]
            exact sub_of_off (rs := s'.wr) (by rw [k'.wr]; exact ws_mem hp') (by omega)⟩)
      (fun _ ⟨k, d⟩ => hk1_ok hH hp k d)
      (fun _ ⟨k, d⟩ => WP.mono (hk1_ok hH hp' k (d.trans eS.symm)) fun _ ⟨k, r⟩ => ⟨k, eA _ ▸ r⟩)
  have u0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ hH.SH.Repr s.mem (A s₀ H.ext) []) ∧
      (HK (H := H) s₀' s' ∧ hH.SH.Repr s'.mem (A s₀ H.ext) [])) (.block (argU H))
      fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          count s = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (A s₀ H.ext) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          count s' = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (A s₀ H.ext) []) :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argU (fun _ ⟨k, r⟩ => hk2_ok hH hp k r)
      (fun _ ⟨k, r⟩ => WP.mono (hk2_ok hH hp' k ((eA _).symm ▸ r)) fun _ ⟨k, a, c, r⟩ =>
        ⟨k, eS ▸ eK ▸ e8 ▸ eL ▸ a, c, eA _ ▸ r⟩)
  have u1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ UpdArgs hH s (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          count s = BitVec.ofNat 64 0 ∧ hH.SH.Repr s.mem (A s₀ H.ext) []) ∧
        (HK (H := H) s₀' s' ∧ UpdArgs hH s' (stA H s₀) (kp s₀) (scr s₀) (kl s₀) ∧
          count s' = BitVec.ofNat 64 0 ∧ hH.SH.Repr s'.mem (A s₀ H.ext) []))
      (.frame (.push [.r1, .r7, .r10, .r12]) (.call H.updN H.updC) (.pop .r1 16))
      fun s s' => (HK (H := H) s₀ s ∧
          hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧
          hH.SH.Repr s'.mem (A s₀' H.ext) (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))) :=
    rel_wp (upd_rel hH (sp := s₀.sp) fun s s' ⟨⟨k, a, c, _⟩, ⟨k', a', c', _⟩⟩ =>
        ⟨a, a', by rw [c, c'], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, c, r⟩ => hk3_ok hH hp k a c r)
      (fun _ ⟨k, a, c, r⟩ => hk3_ok hH hp' k (eS.symm ▸ eK.symm ▸ e8.symm ▸ eL.symm ▸ a) c ((eA _).symm ▸ r))
  have f0 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧
          hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧
          hH.SH.Repr s'.mem (A s₀' H.ext) (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))))
      (.block (argF H))
      fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧
          count s = BitVec.ofNat 64 (kl s₀) ∧
          hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧
          count s' = BitVec.ofNat 64 (kl s₀') ∧
          hH.SH.Repr s'.mem (A s₀' H.ext) (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))) :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.argF (fun _ ⟨k, r⟩ => hk4_ok hH hp k r)
      (fun _ ⟨k, r⟩ => hk4_ok hH hp' k r)
  have f1 : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ FinArgs hH s (stA H s₀) (dgA H s₀) (scr s₀) ∧
          count s = BitVec.ofNat 64 (kl s₀) ∧
          hH.SH.Repr s.mem (A s₀ H.ext) (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ FinArgs hH s' (stA H s₀') (dgA H s₀') (scr s₀') ∧
          count s' = BitVec.ofNat 64 (kl s₀') ∧
          hH.SH.Repr s'.mem (A s₀' H.ext) (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))))
      (.frame (.push [.r1, .r12]) (.call H.finN H.finC) (.pop .r1 8))
      fun s s' => (HK (H := H) s₀ s ∧ bytesAt s.mem (A s₀ (H.ext + H.S)) H.D =
          hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (A s₀' (H.ext + H.S)) H.D =
          hH.SH.H.hash (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))) :=
    rel_wp (fin_rel hH (sp := s₀.sp) (st := stA H s₀) (o := dgA H s₀) (sc := scr s₀)
        fun s s' ⟨⟨k, a, c, _⟩, ⟨k', a', c', _⟩⟩ =>
        ⟨a, eS ▸ eD ▸ e8 ▸ a', by rw [c, c', eL], k.sp, by rw [k'.sp, hq.sp]⟩)
      (fun _ ⟨k, a, c, r⟩ => hk5_ok hH hp k a c r)
      (fun _ ⟨k, a, c, r⟩ => hk5_ok hH hp' k a c r)
  have ep : RelCT isa (fun s s' => (HK (H := H) s₀ s ∧ bytesAt s.mem (A s₀ (H.ext + H.S)) H.D =
          hH.SH.H.hash (bytesAt s₀.mem (State.addr (kp s₀)) (kl s₀))) ∧
        (HK (H := H) s₀' s' ∧ bytesAt s'.mem (A s₀' (H.ext + H.S)) H.D =
          hH.SH.H.hash (bytesAt s₀'.mem (State.addr (kp s₀')) (kl s₀'))))
      (.block (epi H)) fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' :=
    rel_taint hregs (fun _ _ h h' => hk_agree hq h.1 h'.1) hca.epi (fun _ ⟨k, d⟩ => hk6_ok hH hp k d)
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
      Init.ct hH hc r₁.pre r₂.pre ⟨pq.sp, pq.r0, pq.r1, pq.r2, pq.r3, pq.a0⟩ _ _ _ _ _ _ ⟨e₁, e₂⟩ x₁ x₂

include hq in
theorem hashed_rr {s s' : State} (h : Hashed hH s₀ s) (h' : Hashed hH s₀' s') (r : Ready (H := H) s)
    (r' : Ready (H := H) s') : RR (H := H) s s' :=
  ⟨r, r', by rw [h.sp, h'.sp, hq.sp], by rw [h.r0, h'.r0, inn, inn, hq.r0], by rw [h.r1, h'.r1, out, out, hq.r1],
    by rw [h.r2, h'.r2, dgA, dgA, A32, A32, scr, scr, hq.a0], by rw [h.r3, h'.r3],
    by rw [h.arg, h'.arg, scr, scr, hq.a0]⟩

include hq in
theorem cmp_rr {s s' : State} (c : Cmp s₀ s) (c' : Cmp s₀' s') (r : Ready (H := H) s)
    (r' : Ready (H := H) s') : RR (H := H) s s' :=
  ⟨r, r', by rw [c.sp, c'.sp]; exact hq.sp,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.r0,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.r1,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.r2,
    by rw [c.gpr _ (by decide), c'.gpr _ (by decide)]; exact hq.r3,
    (Cmp.scr c).trans (hq.a0.trans (Cmp.scr c').symm)⟩

include hH hc hq in
theorem ct_gen (hca : Checks H) (hlog : 1 ≤ Nat.log2 H.B ∧ Nat.log2 H.B ≤ 31) (hpow : 2 ^ Nat.log2 H.B = H.B)
    (he : encodable (BitVec.ofNat 32 H.B) = true)
    (hS : ∀ s, Cmp s₀ s → kl s₀ ≤ H.B → Ready (H := H) s) (hL : H.B < kl s₀ → PreA (H := H) Wt s₀)
    (hS' : ∀ s, Cmp s₀' s → kl s₀' ≤ H.B → Ready (H := H) s) (hL' : H.B < kl s₀' → PreA (H := H) Wt s₀') :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initAny fun _ _ => True := by
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.r3]
  have hB := hH.hBB
  unfold Hash.initAny
  have refl : ∀ {t : State}, Cmp t t := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  have shr : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀')
      (.block [.mov .r12 (.shifted .r3 .lsr (Nat.log2 H.B)), .cmp .r12 (.imm 0)])
      fun s s' => (Cmp s₀ s ∧ isa.eval .eq s = some (decide (kl s₀ < H.B))) ∧
        (Cmp s₀' s' ∧ isa.eval .eq s' = some (decide (kl s₀ < H.B))) :=
    rel_taint Init.args (fun s s' e e' => by subst e e'; exact cmp_agree hq refl refl) hca.shr
      (fun _ e => by subst e; exact shr_ok hlog hpow)
      (fun _ e => by subst e; exact WP.mono (shr_ok hlog hpow) fun _ ⟨c, ev⟩ => ⟨c, eL ▸ ev⟩)
  refine shr.seq (RelCT.seq (R := RR (H := H)) ?_ (init_rel' hH hc))
  refine RelCT.ite (fun s s' ⟨⟨_, ev⟩, ⟨_, ev'⟩⟩ => by rw [ev, ev']) ?_ ?_
  · refine rel_nil fun s s' ⟨⟨⟨c, ev⟩, ⟨c', _⟩⟩, hT⟩ => ?_
    rw [ev, Option.some.injEq] at hT
    have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT; omega
    exact cmp_rr hq c c' (hS s c hk) (hS' s' c' (eL ▸ hk))
  · have sub : RelCT isa (fun s s' => (Cmp s₀ s ∧ H.B ≤ kl s₀) ∧ (Cmp s₀' s' ∧ H.B ≤ kl s₀))
        (.block [.subs .r12 .r3 (.imm (BitVec.ofNat 32 H.B))])
        fun s s' => ((Cmp s₀ s ∧ H.B ≤ kl s₀) ∧ isa.eval .eq s = some (decide (kl s₀ = H.B))) ∧
          ((Cmp s₀' s' ∧ H.B ≤ kl s₀) ∧ isa.eval .eq s' = some (decide (kl s₀ = H.B))) :=
      rel_taint Init.args (fun _ _ c c' => cmp_agree hq c.1 c'.1) hca.sub
        (fun _ c => WP.mono (sub_ok c.1 hB he) fun _ ⟨c₁, ev⟩ => ⟨⟨c₁, c.2⟩, ev⟩)
        (fun _ c => WP.mono (sub_ok c.1 hB he) fun _ ⟨c₁, ev⟩ => ⟨⟨c₁, c.2⟩, eL ▸ ev⟩)
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
      exact (hashKey_rel hH hq hp hp' hca).mono (fun _ _ h => h)
        fun _ _ ⟨h, h'⟩ => hashed_rr hH hq h h' (ready_long hH hp h) (ready_long hH hp' h')

end

/-! ## Verified -/

section
variable {Wt : Nat} {s₀ : State}

include hH in
theorem ready_cmp (hp : PreA (H := H) Wt s₀) {s : State} (c : Cmp s₀ s) (hk : kl s₀ ≤ H.B) :
    Ready (H := H) s :=
  ready_at hH hp (c.gpr _ (by decide)) (c.gpr _ (by decide)) c.sp c.scr c.rd c.wr
    (by show (s.gpr .r3).toNat ≤ H.B; rw [c.gpr _ (by decide)]; exact hk)
    (.inl ⟨by simp only [keyR, kp, kl, c.gpr _ (show Reg.r2 ≠ .r12 by decide),
      c.gpr _ (show Reg.r3 ≠ .r12 by decide)],
      by simp only [kp, kl, c.gpr _ (show Reg.r2 ≠ .r12 by decide), c.gpr _ (show Reg.r3 ≠ .r12 by decide)];
         exact hp.nk⟩)

/-- `init`'s precondition, with any working space at least as large as its
own, makes a `Ready` state, after the tests of `key_len`. -/
theorem ready_of_pre {sc : Nat} (hp : Pre (H := H) sc s₀) {s : State} (c : Cmp s₀ s) : Ready (H := H) s := by
  have hf := hp.fits
  have sub : Region.Sub (scR (nw0 H) s₀) (scR sc s₀) := Region.sub_prefix (by simp only [nw0]; omega)
  have e0 := c.gpr .r0 (by decide); have e1 := c.gpr .r1 (by decide); have e2 := c.gpr .r2 (by decide)
  have e3 := c.gpr .r3 (by decide)
  have ha : scr s = scr s₀ := c.scr
  have hi : inR (H := H) s = inR (H := H) s₀ := by simp only [inR, inn, e0]
  have ho : outR (H := H) s = outR (H := H) s₀ := by simp only [outR, out, e1]
  have hs : scR (nw0 H) s = scR (nw0 H) s₀ := by simp only [scR, ha]
  have hk : keyR s = keyR s₀ := by simp only [keyR, kp, kl, e2, e3]
  have hA : argR s = argR s₀ := by simp only [argR, stackArgAddr, c.sp]
  have hK : stkR s = stkR s₀ := by simp only [stkR, below, c.sp]
  refine ⟨⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fits0, hp.hB, hp.hW,
    hp.hS⟩, ?_, ?_⟩
  · show (s.gpr .r3).toNat ≤ H.B; rw [e3]; exact hp.kl_le
  · show (inR (H := H) s).Disjoint (outR (H := H) s); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) s).Disjoint (scR (nw0 H) s); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) s).Disjoint (scR (nw0 H) s); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR s).Disjoint (scR (nw0 H) s); rw [hk, hs]; exact hp.k_s.sub_right sub
  · show (argR s).Disjoint (inR (H := H) s); rw [hA, hi]; exact hp.a_i
  · show (argR s).Disjoint (outR (H := H) s); rw [hA, ho]; exact hp.a_o
  · show (argR s).Disjoint (scR (nw0 H) s); rw [hA, hs]; exact hp.a_s.sub_right sub
  · show (stkR s).Disjoint (inR (H := H) s); rw [hK, hi]; exact hp.b_i
  · show (stkR s).Disjoint (outR (H := H) s); rw [hK, ho]; exact hp.b_o
  · show (stkR s).Disjoint (scR (nw0 H) s); rw [hK, hs]; exact hp.b_s.sub_right sub
  · show (s.gpr .r0).toNat + H.S ≤ 2 ^ 32; rw [e0]; exact hp.ni
  · show (s.gpr .r1).toNat + H.S ≤ 2 ^ 32; rw [e1]; exact hp.no
  · show (s.gpr .r2).toNat + (s.gpr .r3).toNat ≤ 2 ^ 32; rw [e2, e3]; exact hp.nk
  · show (scr s).toNat + 8 * nw0 H ≤ 2 ^ 32; rw [ha]; have := hp.nw; simp only [nw0]; omega
  · show 16 ≤ s.sp.toNat; rw [c.sp]; exact hp.sp16
  · show s.sp.toNat + 4 ≤ 2 ^ 32; rw [c.sp]; exact hp.spf
  · rw [hk, hA, hi, ho, hs, c.rd, c.wr, hp.rd, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact sub_of_self (r := keyR s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := argR s₀) (by simp) (Nat.le_refl _)
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

/-- The facts about the block size the tests of `key_len` need. -/
structure BOK (H : Hash) : Prop where
  log : 1 ≤ Nat.log2 H.B ∧ Nat.log2 H.B ≤ 31
  pow : 2 ^ Nat.log2 H.B = H.B
  enc : encodable (BitVec.ofNat 32 H.B) = true

/-- `initAny`'s working space at its end holds the streaming state and the
digest of a long key; it is the shared contract's. -/
theorem verifiedAny {Wt : Nat} (hc : Init.Checks H) (hca : Checks H) (hb : BOK H)
    (hfit : H.ext + H.S + H.F ≤ 8 * Wt) (hDB : H.D ≤ H.B) (hsat : ∃ s, (initAnyG hH.SH Wt).pre s) :
    Verified Arm.target H.initAny (initAnyG hH.SH Wt) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · have hp := preA_of hH hs hfit hDB hb.pow
    obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (Wt := Wt) hb.log hb.pow hb.enc
      (fun _ c hk => ready_cmp hH hp c hk) (fun _ => hp)
    exact ⟨t, s', he, hg, hpost⟩
  · have hp₁ := preA_of hH h₁ hfit hDB hb.pow
    have hp₂ := preA_of hH h₂ hfit hDB hb.pow
    obtain ⟨p1, p2, p3, p4, p5, p6⟩ := hpub
    exact (ct_gen hH hc ⟨p1, p2, p3, p4, p5, p6⟩ hca hb.log hb.pow hb.enc (fun _ c hk => ready_cmp hH hp₁ c hk)
      (fun _ => hp₁) (fun _ c hk => ready_cmp hH hp₂ c hk) (fun _ => hp₂) _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.Arm.InitAny

namespace VG.Proof.Hmac.Generic.Arm.Instances

open VG.Arm
open VG.Proof.Hmac.Generic.Arm

/-- `initAnyG` implies the shared contract for any hash function and
scratch space (`generic_implies`), given that the shared contract is
satisfiable. -/
theorem initAnyImp (S : Spec.Hmac.StreamingHash) (W : Nat)
    (h : ∃ s, (Spec.Hmac.initAnyKeyContract S W Arm.abi 16).pre s) :
    (initAnyG S W).Implies (Spec.Hmac.initAnyKeyContract S W Arm.abi 16) := by
  generic_implies [
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, initAnyG, below, count, Arm.abi, Arm.argRegs,
    Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using h

/-! ## md5 -/

theorem md5_initAnyChecks : InitAny.Checks md5H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem md5_initAnyImp :
    (initAnyG Spec.Hmac.md5S 128).Implies (Spec.Hmac.md5I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.md5S 128 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.md5I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.md5S, Spec.Hmac.md5, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 80 128)

theorem md5_initAny : Verified Arm.target md5H.initAny (Spec.Hmac.md5I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny md5OK md5_initChecks md5_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) md5_initAnyImp.sat_left).of_implies md5_initAnyImp

/-! ## sha1 -/

theorem sha1_initAnyChecks : InitAny.Checks sha1H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha1_initAnyImp :
    (initAnyG Spec.Hmac.sha1S 140).Implies (Spec.Hmac.sha1I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha1S 140 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha1I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha1S, Spec.Hmac.sha1, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 84 140)

theorem sha1_initAny : Verified Arm.target sha1H.initAny (Spec.Hmac.sha1I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha1OK sha1_initChecks sha1_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha1_initAnyImp.sat_left).of_implies sha1_initAnyImp

/-! ## sha384 -/

theorem sha384_initAnyChecks : InitAny.Checks sha384H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha384_initAnyImp :
    (initAnyG Spec.Hmac.sha384S 426).Implies (Spec.Hmac.sha384I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha384S 426 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha384I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha384S, Spec.Hmac.sha384, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 192 426)

theorem sha384_initAny : Verified Arm.target sha384H.initAny (Spec.Hmac.sha384I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha384OK sha384_initChecks sha384_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha384_initAnyImp.sat_left).of_implies sha384_initAnyImp

/-! ## sha512 -/

theorem sha512_initAnyChecks : InitAny.Checks sha512H' where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha512_initAnyImp :
    (initAnyG Spec.Hmac.sha512S 426).Implies (Spec.Hmac.sha512I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha512S 426 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512S, Spec.Hmac.sha512, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 192 426)

theorem sha512_initAny : Verified Arm.target sha512H'.initAny (Spec.Hmac.sha512I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha512OK sha512_initChecks sha512_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha512_initAnyImp.sat_left).of_implies sha512_initAnyImp

/-! ## sha512_224 -/

theorem sha512_224_initAnyChecks : InitAny.Checks sha512_224H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha512_224_initAnyImp :
    (initAnyG Spec.Hmac.sha512_224S 426).Implies (Spec.Hmac.sha512_224I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha512_224S 426 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_224I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 192 426)

theorem sha512_224_initAny : Verified Arm.target sha512_224H.initAny (Spec.Hmac.sha512_224I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha512_224OK sha512_224_initChecks sha512_224_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha512_224_initAnyImp.sat_left).of_implies sha512_224_initAnyImp

/-! ## sha512_256 -/

theorem sha512_256_initAnyChecks : InitAny.Checks sha512_256H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha512_256_initAnyImp :
    (initAnyG Spec.Hmac.sha512_256S 426).Implies (Spec.Hmac.sha512_256I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha512_256S 426 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha512_256I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 192 426)

theorem sha512_256_initAny : Verified Arm.target sha512_256H.initAny (Spec.Hmac.sha512_256I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha512_256OK sha512_256_initChecks sha512_256_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha512_256_initAnyImp.sat_left).of_implies sha512_256_initAnyImp

/-! ## sha256 -/

theorem sha256_initAnyChecks : InitAny.Checks sha256H where
  shr := ⟨_, by taint_decide⟩
  sub := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  epi := ⟨_, by taint_decide⟩

theorem sha256_initAnyImp :
    (initAnyG Spec.Hmac.sha256S 200).Implies (Spec.Hmac.sha256I.initAnyKeyContract Arm.abi 16) :=
  initAnyImp Spec.Hmac.sha256S 200 (by
    inst_sat [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch, Spec.Hmac.sha256I,
      Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha256S, Spec.Hmac.sha256, initAnyG, below,
      count, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] using initSat 96 200)

theorem sha256_initAny : Verified Arm.target sha256H.initAny (Spec.Hmac.sha256I.initAnyKeyContract Arm.abi 16) :=
  (InitAny.verifiedAny sha256OK sha256_initChecks sha256_initAnyChecks ⟨by decide, by decide, by decide⟩ (by decide)
    (by decide) sha256_initAnyImp.sat_left).of_implies sha256_initAnyImp

end VG.Proof.Hmac.Generic.Arm.Instances
