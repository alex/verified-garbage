import VerifiedGarbage.Proof.Hmac.Generic.X86.Instances
import VerifiedGarbage.Proof.Framework.Narrow

/-!
# HMAC over any streaming hash function on x86 (32-bit): `init` for a key of any length

Untrusted: everything here is checked by Lean. As on the other targets
(`Proof/Hmac/Generic/Arm/InitAny.lean`): `initAny` compares `key_len` with
`B + 1`; a longer key is replaced by its digest (`hashKey`, with the hash
function's streaming functions, in `scratch` after `init`'s buffers), which
is passed to `init` (`Init.lean`) in the argument slots of `key` and
`key_len`, and `init` runs from a state permitting more than its narrowed one
(`WP.of_narrow`, `RelCT.of_narrow`).

The arguments are writable, so the taint analysis cannot assume them public
in the states the function runs in: the pieces that read them (the test of
`key_len` and `hashCore`) are checked in the same states with the arguments
read-only (`nN`), and moved to the real ones by `RelCT.of_narrow`.
-/

namespace VG.Proof.Hmac.Generic.X86

open VG.X86
open Spec.Hmac (StreamingHash xorPad ipad opad blockKey)
open Spec.Sha256 (bytesAt)

/-- `init(inner, outer, key, key_len, scratch)` for a key of any length, with
the arguments writable: `VG.Spec.Hmac.initAnyKeyContract`. -/
def initAnyG (S : StreamingHash) (W : Nat) : Contract isa where
  pre s :=
    let inner : Region := ⟨(arg s 0).setWidth 64, S.stateBytes⟩
    let outer : Region := ⟨(arg s 1).setWidth 64, S.stateBytes⟩
    let key : Region := ⟨(arg s 2).setWidth 64, (arg s 3).toNat⟩
    let scratch : Region := ⟨(arg s 4).setWidth 64, 8 * W⟩
    let args : Region := ⟨argAddr s 0, 20⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    let stack : Region := ⟨(s.gpr .esp).setWidth 64 - 48, 48⟩
    s.rd = [key] ∧ s.wr = [inner, outer, scratch, args] ∧
    inner.Disjoint outer ∧ inner.Disjoint scratch ∧ outer.Disjoint scratch ∧
    key.Disjoint inner ∧ key.Disjoint outer ∧ key.Disjoint scratch ∧
    args.Disjoint inner ∧ args.Disjoint outer ∧ args.Disjoint scratch ∧
    ret.Disjoint inner ∧ ret.Disjoint outer ∧ ret.Disjoint scratch ∧
    stack.Disjoint inner ∧ stack.Disjoint outer ∧ stack.Disjoint key ∧ stack.Disjoint scratch ∧
    (arg s 0).toNat + S.stateBytes ≤ 2 ^ 32 ∧ (arg s 1).toNat + S.stateBytes ≤ 2 ^ 32 ∧
    (arg s 2).toNat + (arg s 3).toNat ≤ 2 ^ 32 ∧ (arg s 4).toNat + 8 * W ≤ 2 ^ 32 ∧
    48 ≤ (s.gpr .esp).toNat ∧ (s.gpr .esp).toNat + 24 ≤ 2 ^ 32
  post := (initG S W).post
  pub := (initG S W).pub

end VG.Proof.Hmac.Generic.X86

namespace VG.Proof.Hmac.Generic.X86.InitAny

open VG.X86
open VG.Impl.Hmac.Generic.X86 (Hash at_)
open VG.Proof.Hmac.Generic.X86
open VG.Proof.Hmac.Generic.X86.Init (Pre E inn out kp kl scr inR outR keyR scR argR retR stkR kl_lt)
open VG.Proof.Sha256.X86.Stream (Upd Mupd Fupd wp_mov wp_movi wp_movm wp_store wp_addi wp_cmpi eval_b
  readW_writeW_addr)
open VG.Proof.Hmac.Generic.Common (sub_of_off sub_of_self bytes_keep bytesAt_take InRegions.right')
open VG.Proof.Hmac.Common (bytesAt_length)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey)

variable {H : Hash}

/-! ## Sizes -/

/-- The words of working space `init` gets: its buffers, rounded up. -/
abbrev nw0 (H : Hash) : Nat := (H.buf + 2 * H.B + 7) / 8

theorem ext_eq : H.ext = 8 * nw0 H := rfl

theorem fits0 : H.buf + 2 * H.B ≤ 8 * nw0 H := by simp only [nw0]; omega

theorem save_le_ext : 8 * H.W + 16 ≤ H.ext := by
  have := fits0 (H := H); simp only [Hash.buf] at this; rw [ext_eq]; omega

theorem ext_lt (hH : HashOK H) : H.ext + H.S + H.F < 4096 := by
  have := hH.hW; have := hH.hBB; have := hH.hSB; have := hH.hF
  simp only [ext_eq, nw0, Hash.buf]; omega

section
variable (Wt : Nat) (s₀ : State)

/-- All of `scratch`. -/
abbrev wsR : Region := ⟨(scr s₀).setWidth 64, 8 * Wt⟩

/-- An address in `scratch`, and as a register holds it. -/
abbrev A (o : Nat) : Addr := (scr s₀).setWidth 64 + BitVec.ofNat 64 o
abbrev A32 (o : Nat) : BitVec 32 := scr s₀ + BitVec.ofNat 32 o

/-- The regions with the arguments read-only. -/
abbrev rdN : List Region := [keyR s₀, argR s₀]
abbrev wrN : List Region := [inR (H := H) s₀, outR (H := H) s₀, wsR Wt s₀]

/-- `s`, with the arguments of `s₀` read-only. -/
abbrev nN (s : State) : State := s.withRegions (rdN s₀) (wrN (H := H) Wt s₀)

end

/-- The facts about the regions of `initAny`'s precondition, with the sizes
of `H`, but where the arguments are. -/
structure Lay (Wt : Nat) (s₀ : State) : Prop where
  i_o : (inR (H := H) s₀).Disjoint (outR (H := H) s₀)
  i_s : (inR (H := H) s₀).Disjoint (wsR Wt s₀)
  o_s : (outR (H := H) s₀).Disjoint (wsR Wt s₀)
  k_i : (keyR s₀).Disjoint (inR (H := H) s₀)
  k_o : (keyR s₀).Disjoint (outR (H := H) s₀)
  k_s : (keyR s₀).Disjoint (wsR Wt s₀)
  a_i : (argR s₀).Disjoint (inR (H := H) s₀)
  a_o : (argR s₀).Disjoint (outR (H := H) s₀)
  a_s : (argR s₀).Disjoint (wsR Wt s₀)
  r_i : (retR s₀).Disjoint (inR (H := H) s₀)
  r_o : (retR s₀).Disjoint (outR (H := H) s₀)
  r_s : (retR s₀).Disjoint (wsR Wt s₀)
  b_i : (stkR s₀).Disjoint (inR (H := H) s₀)
  b_o : (stkR s₀).Disjoint (outR (H := H) s₀)
  b_k : (stkR s₀).Disjoint (keyR s₀)
  b_s : (stkR s₀).Disjoint (wsR Wt s₀)
  ni : (inn s₀).toNat + H.S ≤ 2 ^ 32
  no : (out s₀).toNat + H.S ≤ 2 ^ 32
  nk : (kp s₀).toNat + kl s₀ ≤ 2 ^ 32
  nw : (scr s₀).toNat + 8 * Wt ≤ 2 ^ 32
  sp48 : 48 ≤ (E s₀).toNat
  spf : (E s₀).toNat + 24 ≤ 2 ^ 32
  fits : H.ext + H.S + H.F ≤ 8 * Wt
  hDB : H.D ≤ H.B

/-- The precondition of `initAny`: the arguments writable. -/
structure PreA (Wt : Nat) (s₀ : State) : Prop extends Lay (H := H) Wt s₀ where
  rd : s₀.rd = [keyR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, wsR Wt s₀, argR s₀]

/-- The same, with the arguments read-only. -/
structure PreN (Wt : Nat) (s₀ : State) : Prop extends Lay (H := H) Wt s₀ where
  rd : s₀.rd = [keyR s₀, argR s₀]
  wr : s₀.wr = [inR (H := H) s₀, outR (H := H) s₀, wsR Wt s₀]

theorem preA_of (hH : HashOK H) {Wt : Nat} {s₀ : State} (h : (initAnyG hH.SH Wt).pre s₀)
    (hfit : H.ext + H.S + H.F ≤ 8 * Wt) (hDB : H.D ≤ H.B) : PreA (H := H) Wt s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24⟩ := h
  have hS := hH.hS
  have e : (⟨(s₀.gpr .esp).setWidth 64 - 48, 48⟩ : Region) = stkR s₀ := by
    simp only [stkR, below]; rw [Taint.sub_setWidth h23]; rfl
  simp only [hS, e] at *
  exact ⟨⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23,
    h24, hfit, hDB⟩, h1, h2⟩

section
variable {Wt : Nat} {s₀ : State}

theorem nN_args (s : State) (i : Nat) : arg (nN (H := H) Wt s₀ s) i = arg s i := by simp

/-- The narrowed initial state. -/
theorem PreA.narrow (hp : PreA (H := H) Wt s₀) : PreN (H := H) Wt (nN (H := H) Wt s₀ s₀) := by
  exact ⟨⟨hp.i_o, hp.i_s, hp.o_s, hp.k_i, hp.k_o, hp.k_s, hp.a_i, hp.a_o, hp.a_s, hp.r_i, hp.r_o, hp.r_s,
    hp.b_i, hp.b_o, hp.b_k, hp.b_s, hp.ni, hp.no, hp.nk, hp.nw, hp.sp48, hp.spf, hp.fits, hp.hDB⟩, rfl, rfl⟩

/-- The narrowed regions are among the real ones. -/
theorem PreA.covers (hp : PreA (H := H) Wt s₀) :
    Covers (rdN s₀ ++ wrN (H := H) Wt s₀) (s₀.rd ++ s₀.wr) ∧ Covers (wrN (H := H) Wt s₀) s₀.wr := by
  rw [hp.rd, hp.wr]
  refine ⟨Covers.of_sub fun r hr => ?_, Covers.of_sub fun r hr => ?_⟩
  · simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact sub_of_self (r := keyR s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := argR s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := wsR Wt s₀) (by simp) (Nat.le_refl _)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
    · exact sub_of_self (r := wsR Wt s₀) (by simp) (Nat.le_refl _)

end

/-! ## Running code from the narrowed states -/

/-- Code run from `nN s₀ s` runs from `s`, which permits more. -/
theorem exec_nN {Wt : Nat} {s₀ s : State} (hp : PreA (H := H) Wt s₀) (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr)
    {c : Prog isa} {t : List Leak} {s₁ : State} (he : Exec isa c (nN (H := H) Wt s₀ s) t s₁) :
    Exec isa c s t (s₁.withRegions s.rd s.wr) := by
  obtain ⟨c₁, c₂⟩ := hp.covers
  have := Exec.widen he (rd := s.rd) (wr := s.wr) (by simpa [hrd, hwr] using c₁) (by simpa [hwr] using c₂)
  simpa using this

/-! ## Running `init` from a state that permits more -/

/-- `s`, permitted only what `init` needs: the key and its arguments, the
states and its working space. -/
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
      hH.SH.Repr s'.mem ((inn s).setWidth 64)
        (xorPad (blockKey hH.SH.H (bytesAt s.mem ((kp s).setWidth 64) (kl s))) ipad) ∧
      hH.SH.Repr s'.mem ((out s).setWidth 64)
        (xorPad (blockKey hH.SH.H (bytesAt s.mem ((kp s).setWidth 64) (kl s))) opad) := by
  have h := Init.correct hH hr.pre
  refine WP.mono (WP.of_narrow (n := nar H s) (fun s₁ : State => s₁.withRegions s.rd s.wr)
    (fun t s₁ he => init_exec hr he) h) fun s' hs' => ?_
  obtain ⟨s₁, rfl, hg, hq⟩ := hs'
  simp only [initG, arg_withRegions, State.withRegions_mem] at hq
  exact ⟨by simpa [abiPreserved] using hg, hq⟩

/-! ## `Ready` states -/

section
variable {Wt : Nat} {s₀ : State} (hp : Lay (H := H) Wt s₀)
include hp

theorem nw_lt : 8 * Wt ≤ 2 ^ 32 := by have := hp.nw; omega

theorem ext_le : H.ext + H.S + H.F ≤ 8 * Wt := hp.fits

theorem ws_sub0 : Region.Sub (scR (nw0 H) s₀) (wsR Wt s₀) := by
  have := hp.fits; rw [ext_eq] at this; exact Region.sub_prefix (by omega)

omit hp in
theorem part_sub {o n : Nat} (h : o + n ≤ 8 * Wt) : Region.Sub ⟨A s₀ o, n⟩ (wsR Wt s₀) :=
  Offset.sub_base _ h

theorem addrA {o : Nat} (ho : o < 8 * Wt) : (A32 s₀ o).setWidth 64 = A s₀ o :=
  setWidth_add (by have := hp.nw; omega)

theorem toNatA {o : Nat} (ho : o < 8 * Wt) : (A32 s₀ o).toNat = (scr s₀).toNat + o :=
  toNat_add_ofNat (by have := hp.nw; omega)

end

include hH in
/-- A state with `init`'s arguments, for a key in the key's region or in
`scratch` after `init`'s working space, of at most a block. -/
theorem ready_at {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀) {t : State} (hsp : t.gpr .esp = E s₀)
    (h0 : arg t 0 = inn s₀) (h1 : arg t 1 = out s₀) (h4 : arg t 4 = scr s₀) (hrd : t.rd = s₀.rd)
    (hwr : t.wr = s₀.wr) (hkl : kl t ≤ H.B)
    (hk : (kp t = kp s₀ ∧ kl t = kl s₀) ∨ ∃ o, kp t = A32 s₀ o ∧ H.ext ≤ o ∧ o + kl t ≤ 8 * Wt ∧ o < 8 * Wt) :
    Ready (H := H) t := by
  have he := ext_le hp.toLay; have hL := nw_lt hp.toLay
  have hi : inR (H := H) t = inR (H := H) s₀ := by simp only [inR, inn, h0]
  have ho : outR (H := H) t = outR (H := H) s₀ := by simp only [outR, out, h1]
  have hs : scR (nw0 H) t = scR (nw0 H) s₀ := by simp only [scR, scr, h4]
  have hA : argR t = argR s₀ := by simp only [argR, E, hsp]
  have hR : retR t = retR s₀ := by simp only [retR, E, hsp]
  have hK : stkR t = stkR s₀ := by simp only [stkR, E, hsp]
  have sub := ws_sub0 hp.toLay
  have h8 : 8 * nw0 H ≤ 8 * Wt := by rw [← ext_eq]; omega
  have kfacts : (keyR t).Disjoint (inR (H := H) s₀) ∧ (keyR t).Disjoint (outR (H := H) s₀) ∧
      (keyR t).Disjoint (scR (nw0 H) s₀) ∧ (stkR s₀).Disjoint (keyR t) ∧ (kp t).toNat + kl t ≤ 2 ^ 32 ∧
      ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, (keyR t).base = r'.base + BitVec.ofNat 64 off ∧
        off + (keyR t).len ≤ r'.len := by
    rcases hk with ⟨e, e'⟩ | ⟨o, e, h₁, h₂, h₃⟩
    · have ek : keyR t = keyR s₀ := by simp only [keyR, e, e']
      rw [ek, e, e']
      exact ⟨hp.k_i, hp.k_o, hp.k_s.sub_right sub, hp.b_k, hp.nk,
        sub_of_self (r := keyR s₀) (List.mem_append_left _ (by rw [hp.rd]; simp)) (Nat.le_refl _)⟩
    · have ek : keyR t = ⟨A s₀ o, kl t⟩ := by simp only [keyR, e, addrA hp.toLay (o := o) (by omega)]
      have ks : Region.Sub (keyR t) (wsR Wt s₀) := by rw [ek]; exact part_sub h₂
      refine ⟨hp.i_s.symm.sub_left ks, hp.o_s.symm.sub_left ks, ?_, hp.b_s.sub_right ks,
        by rw [e, toNatA hp.toLay (by omega)]; have := hp.nw; omega, ?_⟩
      · rw [ek]; exact Offset.disjoint_base _ (by rw [← ext_eq]; omega) (by omega)
      · rw [ek]; exact sub_of_off (List.mem_append_right _ (by rw [hp.wr]; simp)) h₂
  obtain ⟨k_i, k_o, k_s, b_k, nk, kc⟩ := kfacts
  refine ⟨⟨hkl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, nk, ?_, ?_,
    ?_, fits0, hH.hBB, hH.hB0, hH.hW, hH.hSB⟩, ?_, ?_⟩
  · show (inR (H := H) t).Disjoint (outR (H := H) t); rw [hi, ho]; exact hp.i_o
  · show (inR (H := H) t).Disjoint (scR (nw0 H) t); rw [hi, hs]; exact hp.i_s.sub_right sub
  · show (outR (H := H) t).Disjoint (scR (nw0 H) t); rw [ho, hs]; exact hp.o_s.sub_right sub
  · show (keyR t).Disjoint (inR (H := H) t); rw [hi]; exact k_i
  · show (keyR t).Disjoint (outR (H := H) t); rw [ho]; exact k_o
  · show (keyR t).Disjoint (scR (nw0 H) t); rw [hs]; exact k_s
  · show (argR t).Disjoint (inR (H := H) t); rw [hA, hi]; exact hp.a_i
  · show (argR t).Disjoint (outR (H := H) t); rw [hA, ho]; exact hp.a_o
  · show (argR t).Disjoint (scR (nw0 H) t); rw [hA, hs]; exact hp.a_s.sub_right sub
  · show (retR t).Disjoint (inR (H := H) t); rw [hR, hi]; exact hp.r_i
  · show (retR t).Disjoint (outR (H := H) t); rw [hR, ho]; exact hp.r_o
  · show (retR t).Disjoint (scR (nw0 H) t); rw [hR, hs]; exact hp.r_s.sub_right sub
  · show (stkR t).Disjoint (inR (H := H) t); rw [hK, hi]; exact hp.b_i
  · show (stkR t).Disjoint (outR (H := H) t); rw [hK, ho]; exact hp.b_o
  · show (stkR t).Disjoint (keyR t); rw [hK]; exact b_k
  · show (stkR t).Disjoint (scR (nw0 H) t); rw [hK, hs]; exact hp.b_s.sub_right sub
  · show (inn t).toNat + H.S ≤ 2 ^ 32; rw [inn, h0]; exact hp.ni
  · show (out t).toNat + H.S ≤ 2 ^ 32; rw [out, h1]; exact hp.no
  · show (scr t).toNat + 8 * nw0 H ≤ 2 ^ 32; rw [scr, h4]; have := hp.nw; omega
  · show 48 ≤ (E t).toNat; rw [E, hsp]; exact hp.sp48
  · show (E t).toNat + 24 ≤ 2 ^ 32; rw [E, hsp]; exact hp.spf
  · rw [hi, ho, hs, hA, hrd, hwr]
    exact Covers.of_sub fun r hr => by
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl
      · exact kc
      · exact sub_of_self (r := argR s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) (Nat.le_refl _)
      · exact sub_of_self (r := inR (H := H) s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (List.mem_append_right _ (by rw [hp.wr]; simp)) h8
  · rw [hi, ho, hs, hwr, hp.wr]
    exact Covers.of_sub fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · exact sub_of_self (r := inR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := outR (H := H) s₀) (by simp) (Nat.le_refl _)
      · exact sub_of_self (r := wsR Wt s₀) (by simp) h8

/-! ## The test of `key_len` -/

/-- What the test of `key_len` leaves: `eax` and the flags aside, our state. -/
structure Cmp (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .eax → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

theorem Cmp.esp {s₀ s : State} (c : Cmp s₀ s) : s.gpr .esp = E s₀ := c.gpr _ (by decide)

theorem Cmp.arg {s₀ s : State} (c : Cmp s₀ s) (i : Nat) : arg s i = arg s₀ i := by
  simp only [VG.X86.arg, argAddr, c.mem, c.gpr .esp (by decide)]

/-- The test of `key_len`. -/
abbrev cmpBlock (H : Hash) : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .alu .cmp .eax (.imm (BitVec.ofNat 32 (H.B + 1)))]

include hH in
theorem cmp_ok {s₀ : State} (hin : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ 3) 4) :
    WP isa (.block (cmpBlock H)) s₀ fun t => Cmp s₀ t ∧ t.cf = some (decide (kl s₀ < H.B + 1)) := by
  have hB := hH.hBB
  refine wp_movm (a := argAddr s₀ 3) rfl hin fun s₁ u₁ => wp_cmpi fun s₂ f₂ c₂ _ => WP.block_nil
    ⟨⟨fun r hr => by rw [f₂.gpr, u₁.other r hr], by rw [f₂.mem, u₁.mem], by rw [f₂.rd, u₁.rd],
      by rw [f₂.wr, u₁.wr]⟩, ?_⟩
  rw [c₂, u₁.gpr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rfl

/-! ## Hashing a longer key

Proven from the states with the arguments read-only (`PreN`). -/

/-- The streaming state and the digest of a long key, as registers hold
their addresses. -/
abbrev stA (H : Hash) (s₀ : State) : BitVec 32 := A32 s₀ H.ext
abbrev dgA (H : Hash) (s₀ : State) : BitVec 32 := A32 s₀ (H.ext + H.S)

/-- What `hashCore` keeps, from its prologue on. -/
structure HK (Wt : Nat) (s₀ s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  esp : s.gpr .esp = E s₀
  ebp : s.gpr .ebp = scr s₀
  ebx : s.gpr .ebx = stA H s₀
  saved : SavedRegs H (scr s₀) s₀ s.mem
  frame : Frame [wsR Wt s₀, stkR s₀] s₀.mem s.mem

/-- The registers `HK` fixes. -/
abbrev hregs : List Reg := [.esp, .ebp, .ebx]

section
variable {Wt : Nat} {s₀ : State}

theorem HK.keep {s s' : State} (h : HK (H := H) Wt s₀ s) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr)
    (hg : ∀ r ∈ hregs, s'.gpr r = s.gpr r) {rs : List Region} (hf : Frame rs s.mem s'.mem)
    (hs : ∀ r ∈ rs, (saveR H (scr s₀)).Disjoint r)
    (hsub : ∀ r ∈ rs, ∃ r' ∈ [wsR Wt s₀, stkR s₀], Region.Sub r r') : HK (H := H) Wt s₀ s' :=
  ⟨hrd.trans h.rd, hwr.trans h.wr, (hg _ (by simp)).trans h.esp, (hg _ (by simp)).trans h.ebp,
    (hg _ (by simp)).trans h.ebx, h.saved.frame H hf hs, h.frame.trans (hf.sub hsub)⟩

theorem HK.upd {s s' : State} (h : HK (H := H) Wt s₀ s) {d : Reg} (hd : d ∉ hregs) {v : BitVec 32}
    (u : Upd s s' d v) : HK (H := H) Wt s₀ s' :=
  h.keep u.rd u.wr (fun r hr => u.other r fun e => hd (e ▸ hr)) (rs := [])
    (by rw [u.mem]; exact Frame.refl _ _) (by simp) (by simp)

theorem HK.stk {s : State} (h : HK (H := H) Wt s₀ s) : stk s = stkR s₀ := by
  show below (s.gpr .esp) 48 = below (E s₀) 48; rw [h.esp]

variable (hp : Lay (H := H) Wt s₀)
include hp

/-- `HK` after a call that writes the working space of the functions we
call, or parts of `scratch` after the save area. -/
theorem HK.call {s s' : State} (h : HK (H := H) Wt s₀ s) {ws : List Region} (ha : After s ws s')
    (hw : ∀ r ∈ ws, (∃ k, r = ⟨(scr s₀).setWidth 64, k⟩ ∧ k ≤ 8 * H.W) ∨
      ∃ o k, r = ⟨A s₀ o, k⟩ ∧ 8 * H.W + 16 ≤ o ∧ o + k ≤ 8 * Wt) : HK (H := H) Wt s₀ s' := by
  have hL := nw_lt hp; have he := ext_le hp; have hx := save_le_ext (H := H)
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have f := ha.frame
  rw [h.stk] at f
  refine h.keep ha.rd ha.wr (fun r hr => ha.cs r (by revert r hr; decide)) f ?_ ?_
  all_goals intro r hr; rcases List.mem_append.mp hr with hr | hr
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact Offset.disjoint_base _ hk (by omega)
    · exact Offset.disjoint _ (Or.inl h₁) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact (hp.b_s.sub_right ssub).symm
  · rcases hw r hr with ⟨k, rfl, hk⟩ | ⟨o, k, rfl, h₁, h₂⟩
    · exact ⟨wsR Wt s₀, by simp, Region.sub_prefix (by omega)⟩
    · exact ⟨wsR Wt s₀, by simp, part_sub h₂⟩
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨stkR s₀, by simp, fun _ h => h⟩

/-- The key, while `HK` holds. -/
theorem HK.key {s : State} (h : HK (H := H) Wt s₀ s) :
    bytesAt s.mem ((kp s₀).setWidth 64) (kl s₀) = bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀) :=
  bytes_keep h.frame (fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hp.k_s
    · exact hp.b_k.symm) (Nat.le_of_lt (Nat.lt_trans (kl_lt s₀) (by decide)))

theorem stk_arg : (stkR s₀).Disjoint (argR s₀) := stk_args hp.sp48 (by have := hp.spf; omega)

theorem stk_ret' : (stkR s₀).Disjoint (retR s₀) := stk_ret hp.sp48 (by have := hp.spf; omega)

/-- The arguments, while `HK` holds. -/
theorem HK.argEq {s : State} (h : HK (H := H) Wt s₀ s) {i : Nat} (hi : i < 5) : arg s i = arg s₀ i :=
  arg_keep rfl h.esp (n := 20) (by have := hp.spf; omega) h.frame (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.a_s
    · exact (stk_arg hp).symm) (by omega)

theorem HK.readArg {s : State} (h : HK (H := H) Wt s₀ s) {i : Nat} (hi : i < 5) :
    s.mem.readW (argAddr s₀ i) 32 = arg s₀ i := by
  have := h.argEq hp hi
  simp only [VG.X86.arg] at this ⊢
  rwa [show argAddr s i = argAddr s₀ i by rw [argAddr_eq, argAddr_eq, h.esp]] at this

/-- The return address, while `HK` holds. -/
theorem HK.ret {s : State} (h : HK (H := H) Wt s₀ s) :
    s.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32 :=
  h.frame.readW (r := retR s₀) (Region.contains_self _ _) (by
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rintro r (rfl | rfl)
    · exact hp.r_s
    · exact (stk_ret' hp).symm) (by decide)

include hH in
theorem stA_ok : (stA H s₀).toNat + H.S ≤ 2 ^ 32 ∧ (stA H s₀).setWidth 64 = A s₀ H.ext := by
  have he := ext_le hp; have := hp.nw; have := hH.hD0; have := hH.hDF
  exact ⟨by rw [toNatA hp (by omega)]; omega, addrA hp (by omega)⟩

include hH in
theorem dgA_ok : (dgA H s₀).toNat + H.F ≤ 2 ^ 32 ∧ (dgA H s₀).setWidth 64 = A s₀ (H.ext + H.S) := by
  have he := ext_le hp; have := hp.nw; have := hH.hD0; have := hH.hDF
  exact ⟨by rw [toNatA hp (by omega)]; omega, addrA hp (by omega)⟩

end

/-- The prologue of `hashCore`: `scratch` loaded, our caller's registers
saved, and the state's address. -/
abbrev proBlock (H : Hash) : List Instr :=
  [.mov .eax (.mem (at_ .esp 20))] ++ H.save ++ [.mov .ebp (.reg .eax)] ++ Impl.Hmac.Generic.X86.scr .ebx H.ext

/-- `update`'s arguments: the key. -/
abbrev argU : List Instr := [.mov .eax (.imm 0), .mov .edx (.mem (at_ .esp 12)), .mov .ecx (.mem (at_ .esp 16))]

/-- `finalize`'s arguments: the digest after the state. -/
abbrev argF (H : Hash) : List Instr :=
  [.mov .eax (.mem (at_ .esp 16)), .mov .ecx (.imm 0)] ++ Impl.Hmac.Generic.X86.scr .edx (H.ext + H.S)

section
variable {Wt : Nat} {s₀ : State} (hp : PreN (H := H) Wt s₀)
include hp

theorem argIn {s : State} (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) {i : Nat} (hi : i < 5) :
    InRegions (s.rd ++ s.wr) (argAddr s₀ i) 4 := by
  rw [hrd, hwr, hp.rd]
  exact ⟨argR s₀, by simp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

include hH in
theorem pro_ok {s : State} (c : Cmp s₀ s) :
    WP isa (.block (proBlock H)) s (HK (H := H) Wt s₀) := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hl := ext_lt hH
  simp only [proBlock, Impl.Hmac.Generic.X86.scr, List.append_assoc, List.cons_append,
    List.nil_append]
  refine wp_movm (a := argAddr s₀ 4) (by rw [ea_at, c.esp]; rfl) (argIn hp c.rd c.wr (by decide))
    fun s₁ u₁ => ?_
  have h1 : s₁.gpr .eax = scr s₀ := by rw [u₁.gpr, c.mem]; rfl
  refine save_ok H (scr := scr s₀) h1 hH.hW (by rw [u₁.wr, c.wr, hp.wr]; simp) (L := 8 * Wt) (by omega)
    hp.nw fun s₂ g₂ rd₂ wr₂ f₂ sv₂ => ?_
  refine wp_mov fun s₃ u₃ => wp_mov fun s₄ u₄ => wp_addi fun s₅ u₅ => WP.block_nil ?_
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have hm : s₅.mem = s₂.mem := by rw [u₅.mem, u₄.mem, u₃.mem]
  refine ⟨by rw [u₅.rd, u₄.rd, u₃.rd, rd₂, u₁.rd, c.rd], by rw [u₅.wr, u₄.wr, u₃.wr, wr₂, u₁.wr, c.wr],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), g₂, u₁.other _ (by decide),
      c.esp],
    by rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, g₂, h1],
    by rw [u₅.gpr, u₄.gpr, u₃.gpr, g₂, h1], ?_, ?_⟩
  · rw [hm]
    exact SavedRegs.of_eq H sv₂ fun r hr => by
      rw [u₁.other r (by revert r hr; decide), c.gpr r (by revert r hr; decide)]
  · rw [hm]
    have f := f₂
    rw [u₁.mem, c.mem] at f
    exact f.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact ⟨wsR Wt s₀, by simp, ssub⟩

include hH in
theorem initArgs_of {s : State} (h : HK (H := H) Wt s₀ s) : InitArgs (H := H) s .ebx (stA H s₀) := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H)
  obtain ⟨n, ea⟩ := stA_ok hH hp.toLay
  exact
    { hst := h.ebx
      hr := by decide
      sp48 := by rw [h.esp]; exact hp.sp48
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [ea]
        exact sub_of_off (rs := s.wr) (L := 8 * Wt) (by rw [h.wr, hp.wr]; simp) (by omega)
      b_st := by rw [h.stk, ea]; exact hp.b_s.sub_right (part_sub (by omega))
      nst := n }

include hH in
/-- The streaming state of the key, started. -/
theorem hk1_ok {s : State} (h : HK (H := H) Wt s₀ s) :
    WP isa (H.callInit .ebx) s fun t => HK (H := H) Wt s₀ t ∧ hH.SH.Repr t.mem ((stA H s₀).setWidth 64) [] := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H)
  obtain ⟨_, ea⟩ := stA_ok hH hp.toLay
  refine init_frame hH (initArgs_of hH hp h) fun s₂ a₂ r₂ => ⟨h.call hp.toLay a₂ fun r hr => ?_, r₂⟩
  simp only [List.mem_singleton] at hr; subst hr; rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩

include hH in
theorem hk2_ok {s : State} (h : HK (H := H) Wt s₀ s) :
    WP isa (.block argU) s fun t => HK (H := H) Wt s₀ t ∧
      UpdArgs hH t .eax .ebx (stA H s₀) (kp s₀) (scr s₀) 0 (kl s₀) ∧ t.mem = s.mem := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  obtain ⟨nst, ea⟩ := stA_ok hH hp.toLay
  refine wp_movi fun s₁ u₁ => wp_movm (a := argAddr s₀ 2) (by rw [ea_at, u₁.other _ (by decide), h.esp]; rfl)
    (by rw [u₁.rd, u₁.wr]; exact argIn hp h.rd h.wr (by decide)) fun s₂ u₂ =>
    wp_movm (a := argAddr s₀ 3) (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), h.esp]; rfl)
    (by rw [u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact argIn hp h.rd h.wr (by decide)) fun s₃ u₃ => WP.block_nil ?_
  have k₃ := ((h.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃
  have hm : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₃, ?_, hm⟩
  have ssc : Region.Sub ⟨(scr s₀).setWidth 64, hH.Wb⟩ (wsR Wt s₀) := Region.sub_prefix (by omega)
  have sst : Region.Sub ⟨(stA H s₀).setWidth 64, H.S⟩ (wsR Wt s₀) := by rw [ea]; exact part_sub (by omega)
  exact
    { hst := k₃.ebx
      hlo := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      eax := by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
      ecx := by
        rw [u₃.gpr, u₂.mem, u₁.mem, h.readArg hp.toLay (by decide), kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      edx := by rw [u₃.other _ (by decide), u₂.gpr, u₁.mem, h.readArg hp.toLay (by decide)]
      ebp := k₃.ebp
      hr := by decide
      hl := by decide
      hlen := kl_lt s₀
      sp48 := by rw [k₃.esp]; exact hp.sp48
      cd := covers_one (List.mem_append_left _ (by rw [k₃.rd, hp.rd]; simp))
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · rw [ea]; exact sub_of_off (rs := s₃.wr) (L := 8 * Wt) (by rw [k₃.wr, hp.wr]; simp) (by omega)
        · exact sub_of_self (rs := s₃.wr) (r := wsR Wt s₀) (by rw [k₃.wr, hp.wr]; simp)
            (by show hH.Wb ≤ 8 * Wt; omega)
      st_sc := by rw [ea]; exact Offset.disjoint_base _ (by omega) (by omega)
      d_st := hp.k_s.sub_right sst
      d_sc := hp.k_s.sub_right ssc
      b_st := by rw [k₃.stk]; exact hp.b_s.sub_right sst
      b_d := by rw [k₃.stk]; exact hp.b_k
      b_sc := by rw [k₃.stk]; exact hp.b_s.sub_right ssc
      nst := nst
      nd := hp.nk
      nsc := by have := hp.nw; omega }

include hH in
/-- The key absorbed. -/
theorem hk3_ok {s : State} (h : HK (H := H) Wt s₀ s)
    (ua : UpdArgs hH s .eax .ebx (stA H s₀) (kp s₀) (scr s₀) 0 (kl s₀))
    (hr : hH.SH.Repr s.mem ((stA H s₀).setWidth 64) []) :
    WP isa (.frame (.push [.ebp, .ecx, .edx, .eax, .eax, .ebx]) (.call H.updN H.updC) (.pop .eax 6)) s fun t =>
      HK (H := H) Wt s₀ t ∧
        hH.SH.Repr t.mem ((stA H s₀).setWidth 64) (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)) := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hWb := hH.hWb
  obtain ⟨_, ea⟩ := stA_ok hH hp.toLay
  refine upd_frame hH ua fun s₈ a₈ r₈ => ⟨h.call hp.toLay a₈ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · have := r₈ [] hr (by decide)
    rwa [List.nil_append, h.key hp.toLay] at this

include hH in
theorem hk4_ok {s : State} (h : HK (H := H) Wt s₀ s) :
    WP isa (.block (argF H)) s fun t => HK (H := H) Wt s₀ t ∧
      FinArgs hH t .ebx (stA H s₀) (dgA H s₀) (scr s₀) (BitVec.ofNat 32 (kl s₀)) 0 ∧ t.mem = s.mem := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have hWb := hH.hWb
  obtain ⟨nst, ea⟩ := stA_ok hH hp.toLay
  obtain ⟨ndg, eo⟩ := dgA_ok hH hp.toLay
  simp only [argF, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_movm (a := argAddr s₀ 3) (by rw [ea_at, h.esp]; rfl) (argIn hp h.rd h.wr (by decide))
    fun s₁ u₁ => wp_movi fun s₂ u₂ => wp_mov fun s₃ u₃ => wp_addi fun s₄ u₄ => WP.block_nil ?_
  have k₄ := (((h.upd (by decide) u₁).upd (by decide) u₂).upd (by decide) u₃).upd (by decide) u₄
  have hm : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine ⟨k₄, ?_, hm⟩
  have ssc : Region.Sub ⟨(scr s₀).setWidth 64, hH.Wb⟩ (wsR Wt s₀) := Region.sub_prefix (by omega)
  exact
    { hst := k₄.ebx
      eax := by
        rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr,
          h.readArg hp.toLay (by decide), kl, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      ecx := by rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]
      edx := by rw [u₄.gpr, u₃.gpr, u₂.other _ (by decide), u₁.other _ (by decide), h.ebp]
      ebp := k₄.ebp
      hr := by decide
      sp48 := by rw [k₄.esp]; exact hp.sp48
      cw := Covers.of_sub fun r hr => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · rw [ea]; exact sub_of_off (rs := s₄.wr) (L := 8 * Wt) (by rw [k₄.wr, hp.wr]; simp) (by omega)
        · rw [eo]; exact sub_of_off (rs := s₄.wr) (L := 8 * Wt) (by rw [k₄.wr, hp.wr]; simp) (by omega)
        · exact sub_of_self (rs := s₄.wr) (r := wsR Wt s₀) (by rw [k₄.wr, hp.wr]; simp)
            (by show hH.Wb ≤ 8 * Wt; omega)
      st_o := by rw [ea, eo]; exact Offset.disjoint _ (Or.inl (Nat.le_refl _)) (by omega) (by omega)
      st_sc := by rw [ea]; exact Offset.disjoint_base _ (by omega) (by omega)
      o_sc := by rw [eo]; exact Offset.disjoint_base _ (by omega) (by omega)
      b_st := by rw [k₄.stk, ea]; exact hp.b_s.sub_right (part_sub (by omega))
      b_o := by rw [k₄.stk, eo]; exact hp.b_s.sub_right (part_sub (by omega))
      b_sc := by rw [k₄.stk]; exact hp.b_s.sub_right ssc
      nst := nst
      no := ndg
      nsc := by have := hp.nw; omega }

/-- What `hashCore` leaves: our state and the digest of the key. -/
abbrev HashedC (hH : HashOK H) (Wt : Nat) (s₀ t : State) : Prop :=
  HK (H := H) Wt s₀ t ∧
    bytesAt t.mem ((dgA H s₀).setWidth 64) H.D = hH.SH.H.hash (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))

include hH in
/-- The digest. -/
theorem hk5_ok {s : State} (h : HK (H := H) Wt s₀ s)
    (fa : FinArgs hH s .ebx (stA H s₀) (dgA H s₀) (scr s₀) (BitVec.ofNat 32 (kl s₀)) 0)
    (hr : hH.SH.Repr s.mem ((stA H s₀).setWidth 64) (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))) :
    WP isa (.frame (.push [.ebp, .edx, .ecx, .eax, .ebx]) (.call H.finN H.finC) (.pop .eax 5)) s
      (HashedC hH Wt s₀) := by
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hWb := hH.hWb
  obtain ⟨_, ea⟩ := stA_ok hH hp.toLay
  obtain ⟨_, eo⟩ := dgA_ok hH hp.toLay
  refine fin_frame hH fa fun s₁ a₁ r₁ => ⟨h.call hp.toLay a₁ fun r hr => ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · rw [ea]; exact .inr ⟨_, _, rfl, hx, by omega⟩
    · rw [eo]; exact .inr ⟨_, _, rfl, by omega, by omega⟩
    · exact .inl ⟨_, rfl, hWb⟩
  · rw [bytesAt_take _ _ hH.hDF]
    exact r₁ _ hr (by rw [bytesAt_length]; exact Nat.lt_trans (kl_lt s₀) (by decide))
      (by rw [bytesAt_length, zero_append_ofNat (kl_lt s₀)])

include hH in
theorem hashCore_ok {s : State} (c : Cmp s₀ s) : WP isa H.hashCore s (HashedC hH Wt s₀) := by
  unfold Hash.hashCore
  refine WP.seq (pro_ok hH hp c |>.mono fun s₁ k₁ => ?_)
  refine WP.seq (WP.mono (hk1_ok hH hp k₁) fun s₂ ⟨k₂, r₂⟩ => ?_)
  refine WP.seq (WP.mono (hk2_ok hH hp k₂) fun s₃ ⟨k₃, a₃, m₃⟩ => ?_)
  refine WP.seq (WP.mono (hk3_ok hH hp k₃ a₃ (m₃ ▸ r₂)) fun s₄ ⟨k₄, r₄⟩ => ?_)
  refine WP.seq (WP.mono (hk4_ok hH hp k₄) fun s₅ ⟨k₅, a₅, m₅⟩ => ?_)
  exact hk5_ok hH hp k₅ a₅ (m₅ ▸ r₄)

end

/-! ## Correctness, from the states with the arguments writable -/

section
variable {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀)
include hp

include hH in
/-- `hashCore`, from the narrowed state. -/
theorem hashCore_wide {s : State} (c : Cmp s₀ s) : WP isa H.hashCore s (HashedC hH Wt s₀) := by
  have hz := hashCore_ok hH hp.narrow (s := nN (H := H) Wt s₀ s) ⟨c.gpr, c.mem, rfl, rfl⟩
  refine WP.mono (WP.of_narrow (fun s₁ : State => s₁.withRegions s.rd s.wr)
    (fun t s₁ he => exec_nN hp c.rd c.wr he) hz) fun t ⟨s₁, e, k, d⟩ => ?_
  subst e
  exact ⟨⟨c.rd, c.wr, k.esp, k.ebp, k.ebx, k.saved, k.frame⟩, d⟩

theorem argW {i : Nat} (hi : i < 5) : InRegions s₀.wr (argAddr s₀ i) 4 := by
  rw [hp.wr]
  exact ⟨argR s₀, by simp, arg_contains rfl (by omega) (by have := hp.spf; omega)⟩

theorem ret_arg : (retR s₀).Disjoint (argR s₀) := by
  have := hp.spf
  simp only [retR, argR]
  rw [addr_eq (by omega)]
  exact Offset.base_disjoint _ (by omega) (by omega)

end

/-- What `hashKey` leaves: `init`'s arguments, with the digest as the key,
and our caller's registers. -/
structure Hashed (hH : HashOK H) (s₀ u : State) : Prop where
  rd : u.rd = s₀.rd
  wr : u.wr = s₀.wr
  esp : u.gpr .esp = E s₀
  cs : ∀ r ∈ savedRegs, u.gpr r = s₀.gpr r
  a0 : arg u 0 = inn s₀
  a1 : arg u 1 = out s₀
  a2 : arg u 2 = dgA H s₀
  a3 : arg u 3 = BitVec.ofNat 32 H.D
  a4 : arg u 4 = scr s₀
  ret : u.mem.readW ((E s₀).setWidth 64) 32 = s₀.mem.readW ((E s₀).setWidth 64) 32
  dg : bytesAt u.mem ((dgA H s₀).setWidth 64) H.D =
    hH.SH.H.hash (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))

section
variable {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀)
include hp

include hH in
/-- The digest and its size in the argument slots, and our caller's
registers back. -/
theorem hashArgs_ok {t : State} (h : HashedC hH Wt s₀ t) :
    WP isa (.block H.hashArgs) t (Hashed hH s₀) := by
  obtain ⟨k, d⟩ := h
  have hL := nw_lt hp.toLay; have he := ext_le hp.toLay; have hx := save_le_ext (H := H); have hl := ext_lt hH
  have spf := hp.spf
  obtain ⟨_, eo⟩ := dgA_ok hH hp.toLay
  simp only [Hash.hashArgs, Impl.Hmac.Generic.X86.scr, List.cons_append, List.nil_append]
  refine wp_mov fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_store (a := argAddr s₀ 2)
    (by rw [ea_at, u₂.other _ (by decide), u₁.other _ (by decide), k.esp]; rfl)
    (by rw [u₂.wr, u₁.wr, k.wr]; exact argW hp (by decide)) fun s₃ m₃ => wp_movi fun s₄ u₄ =>
    wp_store (a := argAddr s₀ 3) (by rw [ea_at, u₄.other _ (by decide), m₃.gpr, u₂.other _ (by decide),
      u₁.other _ (by decide), k.esp]; rfl)
    (by rw [u₄.wr, m₃.wr, u₂.wr, u₁.wr, k.wr]; exact argW hp (by decide)) fun s₅ m₅ => ?_
  have eax₂ : s₂.gpr .eax = dgA H s₀ := by rw [u₂.gpr, u₁.gpr, k.ebp]
  have eax₄ : s₄.gpr .eax = BitVec.ofNat 32 H.D := u₄.gpr
  have g : ∀ r, r ≠ .eax → s₅.gpr r = t.gpr r := fun r hr => by
    rw [m₅.gpr, u₄.other r hr, m₃.gpr, u₂.other r hr, u₁.other r hr]
  have hm₅ : s₅.mem = (t.mem.writeW (argAddr s₀ 2) (dgA H s₀)).writeW (argAddr s₀ 3) (BitVec.ofNat 32 H.D) := by
    rw [m₅.mem, eax₄, u₄.mem, m₃.mem, eax₂, u₂.mem, u₁.mem]
  have fA : Frame [argR s₀] t.mem s₅.mem := by
    rw [hm₅]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (arg_contains rfl (by omega) (by omega))).writeW (List.mem_singleton_self _) _
      (arg_contains rfl (by omega) (by omega))
  have ssub : Region.Sub (saveR H (scr s₀)) (wsR Wt s₀) := part_sub (by omega)
  have sv : SavedRegs H (scr s₀) s₀ s₅.mem := k.saved.frame H fA (by
    simp only [List.mem_singleton]; rintro r rfl; exact (hp.a_s.sub_right ssub).symm)
  have hrd : s₅.rd = s₀.rd := by rw [m₅.rd, u₄.rd, m₃.rd, u₂.rd, u₁.rd, k.rd]
  have hwr : s₅.wr = s₀.wr := by rw [m₅.wr, u₄.wr, m₃.wr, u₂.wr, u₁.wr, k.wr]
  refine WP.mono (restore_ok H (scr := scr s₀) (L := 8 * Wt) (by rw [g _ (by decide), k.ebp]) sv
    (by rw [hwr, hp.wr]; simp) (by omega) hp.nw) fun u ⟨hm, hurd, huwr, hg, ho⟩ => ?_
  have esp : u.gpr .esp = E s₀ := by rw [ho _ (by decide) (by decide), g _ (by decide), k.esp]
  have hA : ∀ i, argAddr u i = argAddr s₀ i := fun i => by rw [argAddr_eq, argAddr_eq, esp]
  have slot : ∀ i, i < 5 → i ≠ 2 → i ≠ 3 → arg u i = arg s₀ i := fun i hi h2 h3 => by
    simp only [VG.X86.arg, hA, hm, hm₅]
    rw [show argAddr s₀ i = addr (E s₀) (4 + 4 * i) from rfl, show argAddr s₀ 3 = addr (E s₀) (4 + 4 * 3) from rfl,
      show argAddr s₀ 2 = addr (E s₀) (4 + 4 * 2) from rfl,
      readW_writeW_addr _ _ (by omega) (by omega) (by omega), readW_writeW_addr _ _ (by omega) (by omega) (by omega)]
    exact k.readArg hp.toLay hi
  refine ⟨by rw [hurd, hrd], by rw [huwr, hwr], esp, hg, slot 0 (by decide) (by decide) (by decide),
    slot 1 (by decide) (by decide) (by decide), ?_, ?_, slot 4 (by decide) (by decide) (by decide), ?_, ?_⟩
  · simp only [VG.X86.arg, hA, hm, hm₅]
    rw [show argAddr s₀ 3 = addr (E s₀) (4 + 4 * 3) from rfl, show argAddr s₀ 2 = addr (E s₀) (4 + 4 * 2) from rfl,
      readW_writeW_addr _ _ (by omega) (by omega) (by omega), Mem.readW_writeW_self32]
  · simp only [VG.X86.arg, hA, hm, hm₅]
    rw [Mem.readW_writeW_self32]
  · rw [hm, fA.readW (r := retR s₀) (Region.contains_self _ _) (by
      simp only [List.mem_singleton]; rintro r rfl; exact ret_arg hp) (by decide)]
    exact k.ret hp.toLay
  · rw [hm, bytes_keep fA (by
      simp only [List.mem_singleton]; rintro r rfl; rw [eo]
      exact hp.a_s.symm.sub_left (part_sub (by have := hH.hDF; omega))) (by have := hH.hF; have := hH.hDF; omega)]
    exact d

include hH in
/-- After `hashKey`, `init` runs on the digest. -/
theorem ready_long {u : State} (h : Hashed hH s₀ u) : Ready (H := H) u := by
  have hD := hp.hDB; have := hH.hDF; have := hH.hF; have he := hp.fits; have := hH.hD0
  have e3 : kl u = H.D := by
    simp only [kl, h.a3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show H.D < 2 ^ 32 by omega)]
  refine ready_at hH hp h.esp h.a0 h.a1 h.a4 h.rd h.wr (by rw [e3]; exact hD)
    (.inr ⟨H.ext + H.S, h.a2, Nat.le_add_right _ _, by rw [e3]; omega, by omega⟩)

include hH in
theorem ready_cmp {s : State} (c : Cmp s₀ s) (hk : kl s₀ ≤ H.B) : Ready (H := H) s :=
  ready_at hH hp c.esp (c.arg 0) (c.arg 1) (c.arg 4) c.rd c.wr
    (by show (arg s 3).toNat ≤ H.B; rw [c.arg 3]; exact hk) (.inl ⟨c.arg 2, by simp only [kl, c.arg 3]⟩)

end

/-- A key longer than a block and its digest give the same `K₀`. -/
theorem blockKey_hash {k : List Byte} (hk : H.B < k.length) (hl : (hH.SH.H.hash k).length ≤ H.B) :
    blockKey hH.SH.H (hH.SH.H.hash k) = blockKey hH.SH.H k := by
  have hB := hH.hB
  simp only [blockKey, hB, ite_eq_left_of_eq_true _ _ (eq_true hk),
    ite_eq_right_of_eq_false _ _ (eq_false (show ¬ H.B < (hH.SH.H.hash k).length by omega))]

/-- What `initAny` leaves. -/
abbrev Post (s₀ s' : State) : Prop := abiPreserved s₀ s' ∧ (initG hH.SH 0).post s₀ s'

theorem short_post {s₀ s : State} (c : Cmp s₀ s) (hr : Ready (H := H) s) : WP isa H.init s (Post hH s₀) := by
  refine WP.mono (init_ok hH hr) fun s' ⟨⟨hcs, hret⟩, hi, ho⟩ => ⟨⟨fun r hr' => ?_, ?_⟩, ?_, ?_⟩
  · rw [hcs r hr', c.gpr r (by revert r hr'; decide)]
  · have e := c.esp; simp only [E] at e; rw [← e, hret, c.mem]
  · simp only [inn, kp, kl, c.arg, c.mem] at hi; exact hi
  · simp only [out, kp, kl, c.arg, c.mem] at ho; exact ho

theorem correct_gen {Wt : Nat} {s₀ : State} (hp : PreA (H := H) Wt s₀) :
    WP isa H.initAny s₀ (Post hH s₀) := by
  have hB := hH.hBB
  unfold Hash.initAny
  refine WP.seq (WP.mono (cmp_ok hH (InRegions.right' (argW hp (by decide)))) fun s₁ ⟨c₁, e₁⟩ => WP.seq ?_)
  refine WP.ite _ ((eval_b s₁).trans e₁) (fun hT => WP.block_nil (short_post hH c₁ (ready_cmp hH hp c₁ (by
    have := of_decide_eq_true hT; omega)))) fun hF => ?_
  have hk : H.B < kl s₀ := by have := of_decide_eq_false hF; omega
  unfold Hash.hashKey
  refine WP.seq (WP.mono (hashCore_wide hH hp c₁) fun t ht => WP.mono (hashArgs_ok hH hp ht) fun u hu => ?_)
  have hD := hp.hDB; have := hH.hDF; have := hH.hF
  refine WP.mono (init_ok hH (ready_long hH hp hu)) fun s' ⟨⟨hcs, hret⟩, hi, ho⟩ => ?_
  obtain ⟨_, eo⟩ := dgA_ok hH hp.toLay
  have hkey : bytesAt u.mem ((kp u).setWidth 64) (kl u) =
      hH.SH.H.hash (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀)) := by
    have e3 : kl u = H.D := by
      simp only [kl, hu.a3, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show H.D < 2 ^ 32 by omega)]
    rw [kp, hu.a2, e3]; exact hu.dg
  have hlen : (hH.SH.H.hash (bytesAt s₀.mem ((kp s₀).setWidth 64) (kl s₀))).length ≤ H.B := by
    rw [← hu.dg, bytesAt_length]; exact hD
  have hk0 := blockKey_hash hH (by rw [bytesAt_length]; exact hk) hlen
  refine ⟨⟨fun r hr => ?_, by have e := hu.esp; simp only [E] at e; rw [← e, hret, e]; exact hu.ret⟩, ?_, ?_⟩
  · rw [hcs r hr]
    by_cases he : r = .esp
    · subst he; exact hu.esp
    · exact hu.cs r (callee_saved r hr he)
  · simp only [inn, hu.a0, hkey, hk0] at hi; exact hi
  · simp only [out, hu.a1, hkey, hk0] at ho; exact ho

/-! ## Constant time -/

/-- The taint checks of the test of `key_len` and of `hashKey`'s pieces
between its calls. -/
structure Checks (H : Hash) : Prop where
  cmp : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block (cmpBlock H)) hc).isSome = true
  pro : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block (proBlock H)) hc).isSome = true
  argU : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block argU) hc).isSome = true
  argF : ∃ hc, (VG.Taint.check taint (argTaint [] (4 + 4 * 5)) (.block (argF H)) hc).isSome = true
  args : ∃ hc, (VG.Taint.check taint (τr [.esp, .ebp]) (.block H.hashArgs) hc).isSome = true

theorem rel_nil {P Q : State → State → Prop} (h : ∀ s s', P s s' → Q s s') : RelCT isa P (.block []) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | block h₁ =>
    cases e₂ with
    | block h₂ =>
      simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
      obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, h _ _ hp⟩

/-- The arguments lie outside the writable regions of a narrowed state. -/
theorem argsOutN {Wt : Nat} {z₀ : State} (hp : PreN (H := H) Wt z₀) {s : State} (hsp : s.gpr .esp = E z₀)
    (hwr : s.wr = z₀.wr) : ArgsOut 5 s := by
  have e : (⟨(s.gpr .esp).setWidth 64, 4 + 4 * 5⟩ : Region) = ⟨(E z₀).setWidth 64, 4 + 20⟩ := by rw [hsp]
  have := hp.spf
  refine ⟨by rw [hsp]; exact hp.spf, ?_⟩
  rw [e, hwr, hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact Taint.frame_disjoint (by omega) hp.r_i hp.a_i
  · exact Taint.frame_disjoint (by omega) hp.r_o hp.a_o
  · exact Taint.frame_disjoint (by omega) hp.r_s hp.a_s

/-- Two narrowed states agree on the arguments. -/
theorem agreeArgs {Wt : Nat} {z₀ z₀' : State} (hp : PreN (H := H) Wt z₀) (hp' : PreN (H := H) Wt z₀')
    (hq : Init.PubEq z₀ z₀') {s s' : State} (hsp : s.gpr .esp = E z₀) (hsp' : s'.gpr .esp = E z₀')
    (hwr : s.wr = z₀.wr) (hwr' : s'.wr = z₀'.wr) (ha : ∀ i < 5, arg s i = arg z₀ i)
    (ha' : ∀ i < 5, arg s' i = arg z₀' i) : VG.X86.Taint.Agree (argTaint [] (4 + 4 * 5)) s s' :=
  agree_argTaint (fun _ h => nomatch h) (by rw [hsp, hsp', E, E, hq.esp]) (argsOutN hp hsp hwr)
    (argsOutN hp' hsp' hwr') fun i hi => by rw [ha i hi, ha' i hi, hq.args i hi]

include hH in
/-- `hashCore` is constant time, from narrowed states. -/
theorem hashCore_rel {Wt : Nat} {z₀ z₀' : State} (hp : PreN (H := H) Wt z₀) (hp' : PreN (H := H) Wt z₀')
    (hq : Init.PubEq z₀ z₀') (hca : Checks H) :
    RelCT isa (fun s s' => Cmp z₀ s ∧ Cmp z₀' s') H.hashCore fun _ _ => True := by
  have e8 : scr z₀' = scr z₀ := (hq.args 4 (by decide)).symm
  have eS : stA H z₀' = stA H z₀ := by simp only [stA, A32, e8]
  have eD : dgA H z₀' = dgA H z₀ := by simp only [dgA, A32, e8]
  have eK : kp z₀' = kp z₀ := (hq.args 2 (by decide)).symm
  have eL : kl z₀' = kl z₀ := by simp only [kl, hq.args 3 (by decide)]
  have eE : E z₀' = E z₀ := hq.esp.symm
  unfold Hash.hashCore
  have pro : RelCT isa (fun s s' => Cmp z₀ s ∧ Cmp z₀' s') (.block (proBlock H))
      fun s s' => HK (H := H) Wt z₀ s ∧ HK (H := H) Wt z₀' s' :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' c c' =>
        agreeArgs hp hp' hq c.esp c'.esp c.wr c'.wr (fun i _ => c.arg i) (fun i _ => c'.arg i)) hca.pro
      (fun _ c => pro_ok hH hp c) (fun _ c => pro_ok hH hp' c)
  have i1 : RelCT isa (fun s s' => HK (H := H) Wt z₀ s ∧ HK (H := H) Wt z₀' s') (H.callInit .ebx)
      fun s s' => (HK (H := H) Wt z₀ s ∧ hH.SH.Repr s.mem ((stA H z₀).setWidth 64) []) ∧
        (HK (H := H) Wt z₀' s' ∧ hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) []) :=
    rel_wp (init_rel hH (sp := E z₀) (st := stA H z₀) fun s s' ⟨k, k'⟩ =>
        ⟨initArgs_of hH hp k, eS ▸ initArgs_of hH hp' k', k.esp, by rw [k'.esp, eE]⟩)
      (fun _ k => hk1_ok hH hp k) (fun _ k => hk1_ok hH hp' k)
  have u0 : RelCT isa (fun s s' => (HK (H := H) Wt z₀ s ∧ hH.SH.Repr s.mem ((stA H z₀).setWidth 64) []) ∧
        (HK (H := H) Wt z₀' s' ∧ hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) [])) (.block argU)
      fun s s' => (HK (H := H) Wt z₀ s ∧ UpdArgs hH s .eax .ebx (stA H z₀) (kp z₀) (scr z₀) 0 (kl z₀) ∧
          hH.SH.Repr s.mem ((stA H z₀).setWidth 64) []) ∧
        (HK (H := H) Wt z₀' s' ∧ UpdArgs hH s' .eax .ebx (stA H z₀') (kp z₀') (scr z₀') 0 (kl z₀') ∧
          hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) []) :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' h h' =>
        agreeArgs hp hp' hq h.1.esp h'.1.esp h.1.wr h'.1.wr (fun i hi => h.1.argEq hp.toLay hi)
          (fun i hi => h'.1.argEq hp'.toLay hi)) hca.argU
      (fun _ ⟨k, r⟩ => WP.mono (hk2_ok hH hp k) fun _ ⟨k, a, m⟩ => ⟨k, a, m ▸ r⟩)
      (fun _ ⟨k, r⟩ => WP.mono (hk2_ok hH hp' k) fun _ ⟨k, a, m⟩ => ⟨k, a, m ▸ r⟩)
  have u1 : RelCT isa (fun s s' =>
        (HK (H := H) Wt z₀ s ∧ UpdArgs hH s .eax .ebx (stA H z₀) (kp z₀) (scr z₀) 0 (kl z₀) ∧
          hH.SH.Repr s.mem ((stA H z₀).setWidth 64) []) ∧
        (HK (H := H) Wt z₀' s' ∧ UpdArgs hH s' .eax .ebx (stA H z₀') (kp z₀') (scr z₀') 0 (kl z₀') ∧
          hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) []))
      (.frame (.push [.ebp, .ecx, .edx, .eax, .eax, .ebx]) (.call H.updN H.updC) (.pop .eax 6))
      fun s s' => (HK (H := H) Wt z₀ s ∧
          hH.SH.Repr s.mem ((stA H z₀).setWidth 64) (bytesAt z₀.mem ((kp z₀).setWidth 64) (kl z₀))) ∧
        (HK (H := H) Wt z₀' s' ∧
          hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) (bytesAt z₀'.mem ((kp z₀').setWidth 64) (kl z₀'))) :=
    rel_wp (upd_rel hH (sp := E z₀) fun s s' ⟨⟨k, a, _⟩, ⟨k', a', _⟩⟩ =>
        ⟨a, eS ▸ eK ▸ e8 ▸ eL ▸ a', k.esp, by rw [k'.esp, eE]⟩)
      (fun _ ⟨k, a, r⟩ => hk3_ok hH hp k a r) (fun _ ⟨k, a, r⟩ => hk3_ok hH hp' k a r)
  have f0 : RelCT isa (fun s s' => (HK (H := H) Wt z₀ s ∧
          hH.SH.Repr s.mem ((stA H z₀).setWidth 64) (bytesAt z₀.mem ((kp z₀).setWidth 64) (kl z₀))) ∧
        (HK (H := H) Wt z₀' s' ∧
          hH.SH.Repr s'.mem ((stA H z₀').setWidth 64) (bytesAt z₀'.mem ((kp z₀').setWidth 64) (kl z₀'))))
      (.block (argF H))
      fun s s' => (HK (H := H) Wt z₀ s ∧
          FinArgs hH s .ebx (stA H z₀) (dgA H z₀) (scr z₀) (BitVec.ofNat 32 (kl z₀)) 0) ∧
        (HK (H := H) Wt z₀' s' ∧
          FinArgs hH s' .ebx (stA H z₀') (dgA H z₀') (scr z₀') (BitVec.ofNat 32 (kl z₀')) 0) :=
    rel_agree (argTaint [] (4 + 4 * 5)) (fun s s' h h' =>
        agreeArgs hp hp' hq h.1.esp h'.1.esp h.1.wr h'.1.wr (fun i hi => h.1.argEq hp.toLay hi)
          (fun i hi => h'.1.argEq hp'.toLay hi)) hca.argF
      (fun _ ⟨k, _⟩ => WP.mono (hk4_ok hH hp k) fun _ ⟨k, a, _⟩ => ⟨k, a⟩)
      (fun _ ⟨k, _⟩ => WP.mono (hk4_ok hH hp' k) fun _ ⟨k, a, _⟩ => ⟨k, a⟩)
  have f1 : RelCT isa (fun s s' => (HK (H := H) Wt z₀ s ∧
          FinArgs hH s .ebx (stA H z₀) (dgA H z₀) (scr z₀) (BitVec.ofNat 32 (kl z₀)) 0) ∧
        (HK (H := H) Wt z₀' s' ∧
          FinArgs hH s' .ebx (stA H z₀') (dgA H z₀') (scr z₀') (BitVec.ofNat 32 (kl z₀')) 0))
      (.frame (.push [.ebp, .edx, .ecx, .eax, .ebx]) (.call H.finN H.finC) (.pop .eax 5)) fun _ _ => True :=
    fin_rel hH (sp := E z₀) fun s s' ⟨⟨k, a⟩, ⟨k', a'⟩⟩ =>
      ⟨a, eS ▸ eD ▸ e8 ▸ eL ▸ a', k.esp, by rw [k'.esp, eE]⟩
  exact pro.seq (i1.seq (u0.seq (u1.seq (f0.seq f1))))

/-- Code proven constant time from the narrowed states is constant time
from the states themselves. -/
theorem rel_nN {Wt : Nat} {s₀ s₀' : State} (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
    (er : rdN s₀' = rdN s₀) (ew : wrN (H := H) Wt s₀' = wrN (H := H) Wt s₀)
    {c : Prog isa} {F F' G G' : State → Prop}
    (hF : ∀ s, F s → s.rd = s₀.rd ∧ s.wr = s₀.wr) (hF' : ∀ s, F' s → s.rd = s₀'.rd ∧ s.wr = s₀'.wr)
    (hex : ∀ s, F s → ∃ t s₁, Exec isa c (nN (H := H) Wt s₀ s) t s₁)
    (hex' : ∀ s, F' s → ∃ t s₁, Exec isa c (nN (H := H) Wt s₀ s) t s₁)
    (h : RelCT isa (fun a b => ∃ s s', (F s ∧ F' s') ∧ a = nN (H := H) Wt s₀ s ∧ b = nN (H := H) Wt s₀ s') c
      fun _ _ => True)
    (hw : ∀ s, F s → WP isa c s G) (hw' : ∀ s, F' s → WP isa c s G') :
    RelCT isa (fun s s' => F s ∧ F' s') c fun s s' => G s ∧ G' s' := by
  have e' : ∀ s, nN (H := H) Wt s₀ s = nN (H := H) Wt s₀' s := fun s => by simp only [nN, er, ew]
  have hct := RelCT.of_narrow (M := isa) (fun s => F s ∨ F' s) (nN (H := H) Wt s₀) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun _ _ h => ⟨.inl h.1, .inr h.2⟩)
    (fun s hs t s₁ he => hs.elim (fun f => exec_nN hp (hF s f).1 (hF s f).2 he)
      (fun f => exec_nN hp' (hF' s f).1 (hF' s f).2 (e' s ▸ he)))
    (fun s hs => hs.elim (hex s) (hex' s)) h
  exact (hct.wp fun s s' h => ⟨hw s h.1, hw' s' h.2⟩).mono (fun _ _ h => h) fun _ _ h => h.2

/-- Two states from which `init` runs, with the same public arguments. -/
abbrev RR (s s' : State) : Prop := Ready (H := H) s ∧ Ready (H := H) s' ∧ Init.PubEq s s'

include hH in
theorem init_rel' (hc : Init.Checks H) : RelCT isa (RR (H := H)) H.init fun _ _ => True :=
  RelCT.of_narrow (Ready (H := H)) (nar H) (fun s s₁ => s₁.withRegions s.rd s.wr)
    (fun _ _ h => ⟨h.1, h.2.1⟩) (fun _ h _ _ he => init_exec h he)
    (fun _ h => let ⟨t, s', he, _⟩ := Init.correct hH h.pre; ⟨t, s', he⟩)
    fun _ _ _ _ _ _ ⟨_, _, ⟨r₁, r₂, pq⟩, e₁, e₂⟩ x₁ x₂ =>
      Init.ct hH hc r₁.pre r₂.pre ⟨pq.esp, pq.args⟩ _ _ _ _ _ _ ⟨e₁, e₂⟩ x₁ x₂

theorem hashed_rr {s₀ s₀' : State} (hq : Init.PubEq s₀ s₀') {s s' : State} (h : Hashed hH s₀ s)
    (h' : Hashed hH s₀' s') (r : Ready (H := H) s) (r' : Ready (H := H) s') : RR (H := H) s s' := by
  have e8 : scr s₀' = scr s₀ := (hq.args 4 (by decide)).symm
  refine ⟨r, r', by rw [h.esp, h'.esp, E, E, hq.esp], fun i hi => ?_⟩
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · rw [h.a0, h'.a0, inn, inn, hq.args 0 (by decide)]
  · rw [h.a1, h'.a1, out, out, hq.args 1 (by decide)]
  · rw [h.a2, h'.a2, dgA, dgA, A32, A32, e8]
  · rw [h.a3, h'.a3]
  · rw [h.a4, h'.a4, e8]

theorem cmp_rr {s₀ s₀' : State} (hq : Init.PubEq s₀ s₀') {s s' : State} (c : Cmp s₀ s) (c' : Cmp s₀' s')
    (r : Ready (H := H) s) (r' : Ready (H := H) s') : RR (H := H) s s' :=
  ⟨r, r', by rw [c.esp, c'.esp, E, E, hq.esp], fun i hi => by rw [c.arg, c'.arg, hq.args i hi]⟩

include hH in
theorem ct_gen {Wt : Nat} {s₀ s₀' : State} (hp : PreA (H := H) Wt s₀) (hp' : PreA (H := H) Wt s₀')
    (hq : Init.PubEq s₀ s₀') (hc : Init.Checks H) (hca : Checks H) :
    RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') H.initAny fun _ _ => True := by
  have hB := hH.hBB
  have eL : kl s₀' = kl s₀ := by simp only [kl, hq.args 3 (by decide)]
  have e8 : scr s₀' = scr s₀ := (hq.args 4 (by decide)).symm
  have er : rdN s₀' = rdN s₀ := by
    simp only [rdN, keyR, argR, kp, kl, E, hq.args 2 (by decide), hq.args 3 (by decide), hq.esp]
  have ew : wrN (H := H) Wt s₀' = wrN (H := H) Wt s₀ := by
    simp only [wrN, inR, outR, wsR, inn, out, e8, hq.args 0 (by decide), hq.args 1 (by decide)]
  have hpn' : PreN (H := H) Wt (nN (H := H) Wt s₀ s₀') := by
    have := hp'.narrow; simp only [nN] at this ⊢; rwa [er, ew] at this
  have hqn : Init.PubEq (nN (H := H) Wt s₀ s₀) (nN (H := H) Wt s₀ s₀') := ⟨hq.esp, hq.args⟩
  obtain ⟨_, hcm⟩ := hca.cmp
  unfold Hash.initAny
  have cmp : RelCT isa (fun s s' => s = s₀ ∧ s' = s₀') (.block (cmpBlock H))
      fun s s' => (Cmp s₀ s ∧ s.cf = some (decide (kl s₀ < H.B + 1))) ∧
        (Cmp s₀' s' ∧ s'.cf = some (decide (kl s₀ < H.B + 1))) := by
    refine rel_nN hp hp' er ew (F := (· = s₀)) (F' := (· = s₀'))
      (fun _ e => by rw [e]; exact ⟨rfl, rfl⟩) (fun _ e => by rw [e]; exact ⟨rfl, rfl⟩)
      (fun _ e => by
        rw [e]; obtain ⟨t, s₁, he, _⟩ := cmp_ok hH (s₀ := nN (H := H) Wt s₀ s₀) (argIn hp.narrow rfl rfl (by decide))
        exact ⟨t, s₁, he⟩)
      (fun _ e => by
        rw [e]; obtain ⟨t, s₁, he, _⟩ := cmp_ok hH (s₀ := nN (H := H) Wt s₀ s₀') (argIn hpn' rfl rfl (by decide))
        exact ⟨t, s₁, he⟩)
      (RelCT.taint (A := taint) (argTaint [] (4 + 4 * 5)) (fun a b ⟨s, s', ⟨e, e'⟩, ea, eb⟩ => by
        rw [ea, eb, e, e']
        exact agreeArgs hp.narrow hpn' hqn rfl rfl rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)) hcm)
      (fun _ e => by rw [e]; exact cmp_ok hH (InRegions.right' (argW hp (by decide))))
      (fun _ e => by
        rw [e]; exact WP.mono (cmp_ok hH (InRegions.right' (argW hp' (by decide)))) fun _ ⟨c, ev⟩ =>
          ⟨c, eL ▸ ev⟩)
  unfold Hash.hashKey
  refine cmp.seq (RelCT.seq (R := RR (H := H)) ?_ (init_rel' hH hc))
  refine RelCT.ite (fun s s' ⟨⟨_, ev⟩, ⟨_, ev'⟩⟩ => (ev.trans ev'.symm : s.cf = s'.cf)) ?_ ?_
  · refine rel_nil fun s s' ⟨⟨⟨c, ev⟩, ⟨c', _⟩⟩, hT⟩ => ?_
    have hT' : s.cf = some true := hT
    rw [ev, Option.some.injEq] at hT'
    have hk : kl s₀ ≤ H.B := by have := of_decide_eq_true hT'; omega
    exact cmp_rr hq c c' (ready_cmp hH hp c hk) (ready_cmp hH hp' c' (eL ▸ hk))
  · refine RelCT.mono (P := fun s s' => (Cmp s₀ s ∧ Cmp s₀' s') ∧ H.B < kl s₀) ?_
      (fun s s' ⟨⟨⟨c, ev⟩, ⟨c', _⟩⟩, hF⟩ => by
        have hF' : s.cf = some false := hF
        rw [ev, Option.some.injEq] at hF'
        have := of_decide_eq_false hF'
        exact ⟨⟨c, c'⟩, by omega⟩) fun _ _ h => h
    refine RelCT.exists_ (P := fun (_ : H.B < kl s₀) s s' => Cmp s₀ s ∧ Cmp s₀' s') ?_
      |>.mono (fun s s' ⟨h, hk⟩ => ⟨hk, h⟩) fun _ _ h => h
    intro hk
    have core : RelCT isa (fun s s' => Cmp s₀ s ∧ Cmp s₀' s') H.hashCore
        fun s s' => HashedC hH Wt s₀ s ∧ HashedC hH Wt s₀' s' :=
      rel_nN hp hp' er ew (F := Cmp s₀) (F' := Cmp s₀') (fun _ c => ⟨c.rd, c.wr⟩) (fun _ c => ⟨c.rd, c.wr⟩)
        (fun s c => by
          obtain ⟨t, s₁, he, _⟩ := hashCore_ok hH hp.narrow (s := nN (H := H) Wt s₀ s) ⟨c.gpr, c.mem, rfl, rfl⟩
          exact ⟨t, s₁, he⟩)
        (fun s c => by
          obtain ⟨t, s₁, he, _⟩ := hashCore_ok hH hpn' (s := nN (H := H) Wt s₀ s) ⟨c.gpr, c.mem, rfl, rfl⟩
          exact ⟨t, s₁, he⟩)
        ((hashCore_rel hH hp.narrow hpn' hqn hca).mono (fun a b ⟨s, s', ⟨c, c'⟩, ea, eb⟩ => by
          rw [ea, eb]; exact ⟨⟨c.gpr, c.mem, rfl, rfl⟩, ⟨c'.gpr, c'.mem, rfl, rfl⟩⟩) fun _ _ h => h)
        (fun _ c => hashCore_wide hH hp c) (fun _ c => hashCore_wide hH hp' c)
    have args : RelCT isa (fun s s' => HashedC hH Wt s₀ s ∧ HashedC hH Wt s₀' s') (.block H.hashArgs)
        fun s s' => Hashed hH s₀ s ∧ Hashed hH s₀' s' :=
      rel_agree (τr [.esp, .ebp]) (fun s s' h h' => agree_regs fun r hr => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl
          · rw [h.1.esp, h'.1.esp, E, E, hq.esp]
          · rw [h.1.ebp, h'.1.ebp, e8]) hca.args
        (fun _ h => hashArgs_ok hH hp h) (fun _ h => hashArgs_ok hH hp' h)
    exact (core.seq args).mono (fun _ _ h => h) fun _ _ ⟨h, h'⟩ =>
      hashed_rr hH hq h h' (ready_long hH hp h) (ready_long hH hp' h')

/-! ## Verified -/

/-- `initAny` is verified against `initAnyG`, given the taint checks, which
the kernel evaluates for each hash function. -/
theorem verifiedAny {Wt : Nat} (hc : Init.Checks H) (hca : Checks H) (hfit : H.ext + H.S + H.F ≤ 8 * Wt)
    (hDB : H.D ≤ H.B) (hsat : ∃ s, (initAnyG hH.SH Wt).pre s) :
    Verified X86.target H.initAny (initAnyG hH.SH Wt) := by
  refine ⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hpub e₁ e₂ => ?_, hsat⟩
  · obtain ⟨t, s', he, hg, hpost⟩ := correct_gen hH (preA_of hH hs hfit hDB)
    exact ⟨t, s', he, hg, hpost⟩
  · obtain ⟨p1, p2⟩ := hpub
    exact (ct_gen hH (preA_of hH h₁ hfit hDB) (preA_of hH h₂ hfit hDB) ⟨p1, p2⟩ hc hca
      _ _ _ _ _ _ ⟨rfl, rfl⟩ e₁ e₂).1

end VG.Proof.Hmac.Generic.X86.InitAny

namespace VG.Proof.Hmac.Generic.X86.Instances

open VG.X86
open VG.Proof.Hmac.Generic.X86

/-! ## sha1 -/

theorem sha1_initAnyChecks : InitAny.Checks sha1H where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem sha1_initAnyImp :
    (initAnyG Spec.Hmac.sha1S 140).Implies (Spec.Hmac.sha1I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 84 140
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha1I, Spec.Hmac.sha1S, Spec.Hmac.sha1, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 84 140

theorem sha1_initAny : Verified X86.target sha1H.initAny (Spec.Hmac.sha1I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny sha1OK sha1_initChecks sha1_initAnyChecks (by decide) (by decide)
    sha1_initAnyImp.sat_left).of_implies sha1_initAnyImp

/-! ## md5 -/

theorem md5_initAnyChecks : InitAny.Checks md5H where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem md5_initAnyImp :
    (initAnyG Spec.Hmac.md5S 128).Implies (Spec.Hmac.md5I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 80 128
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.md5I, Spec.Hmac.md5S, Spec.Hmac.md5, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 80 128

theorem md5_initAny : Verified X86.target md5H.initAny (Spec.Hmac.md5I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny md5OK md5_initChecks md5_initAnyChecks (by decide) (by decide)
    md5_initAnyImp.sat_left).of_implies md5_initAnyImp

/-! ## sha384 -/

theorem sha384_initAnyChecks : InitAny.Checks sha384H where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem sha384_initAnyImp :
    (initAnyG Spec.Hmac.sha384S 426).Implies (Spec.Hmac.sha384I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 426
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha384I, Spec.Hmac.sha384S, Spec.Hmac.sha384, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 426

theorem sha384_initAny : Verified X86.target sha384H.initAny (Spec.Hmac.sha384I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny sha384OK sha384_initChecks sha384_initAnyChecks (by decide) (by decide)
    sha384_initAnyImp.sat_left).of_implies sha384_initAnyImp

/-! ## sha512 -/

theorem sha512_initAnyChecks : InitAny.Checks sha512H' where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem sha512_initAnyImp :
    (initAnyG Spec.Hmac.sha512S 426).Implies (Spec.Hmac.sha512I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 426
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512I, Spec.Hmac.sha512S, Spec.Hmac.sha512, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 426

theorem sha512_initAny : Verified X86.target sha512H'.initAny (Spec.Hmac.sha512I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny sha512OK sha512_initChecks sha512_initAnyChecks (by decide) (by decide)
    sha512_initAnyImp.sat_left).of_implies sha512_initAnyImp

/-! ## sha512_224 -/

theorem sha512_224_initAnyChecks : InitAny.Checks sha512_224H where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem sha512_224_initAnyImp :
    (initAnyG Spec.Hmac.sha512_224S 426).Implies (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 426
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512_224I, Spec.Hmac.sha512_224S, Spec.Hmac.sha512_224, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 426

theorem sha512_224_initAny : Verified X86.target sha512_224H.initAny (Spec.Hmac.sha512_224I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny sha512_224OK sha512_224_initChecks sha512_224_initAnyChecks (by decide) (by decide)
    sha512_224_initAnyImp.sat_left).of_implies sha512_224_initAnyImp

/-! ## sha512_256 -/

theorem sha512_256_initAnyChecks : InitAny.Checks sha512_256H where
  cmp := ⟨_, by taint_decide⟩
  pro := ⟨_, by taint_decide⟩
  argU := ⟨_, by taint_decide⟩
  argF := ⟨_, by taint_decide⟩
  args := ⟨_, by taint_decide⟩

theorem sha512_256_initAnyImp :
    (initAnyG Spec.Hmac.sha512_256S 426).Implies (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi 48) := by
  obtain ⟨a0, a1, a2, a3, a4, e, esp⟩ := initSat_args 192 426
  sig_implies [Spec.Hmac.Instance.initAnyKeyContract, Spec.Hmac.Instance.initAnyKeyScratch,
    Spec.Hmac.initAnyKeyContract, Spec.Hmac.initSig, Spec.Hmac.sha512_256I, Spec.Hmac.sha512_256S, Spec.Hmac.sha512_256, initAnyG,
    initG, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    [a0, a1, a2, a3, a4, e, esp, initSat] using initSat 192 426

theorem sha512_256_initAny : Verified X86.target sha512_256H.initAny (Spec.Hmac.sha512_256I.initAnyKeyContract X86.abi 48) :=
  (InitAny.verifiedAny sha512_256OK sha512_256_initChecks sha512_256_initAnyChecks (by decide) (by decide)
    sha512_256_initAnyImp.sat_left).of_implies sha512_256_initAnyImp

end VG.Proof.Hmac.Generic.X86.Instances
