import VerifiedGarbage.Proof.Pbkdf2.Md.AArch64.PbkCommon
import VerifiedGarbage.Proof.Pbkdf2.AArch64.Iterate

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on AArch64: `pbkdf2`'s calls

Untrusted: everything here is checked by Lean. The calls of HMAC's `init`
and `finalize` and of `iterate`, whose contracts (`initG`, `finG`, `iterK`)
their proofs are given as hypotheses: each is run with `WP.callF` (the
callee may use the 16 bytes below the stack pointer, a frame deep), and
shown constant time in two runs with `RelCT.call`.
-/

namespace VG.Proof.Pbkdf2.Md.AArch64.Pbk

open VG.AArch64
open VG.Impl.Pbkdf2.Md.AArch64 (Hash)
open VG.Proof.Pbkdf2.Md.AArch64 (HashOK)
open VG.Proof.Pbkdf2.AArch64 (iterK)
open VG.Proof.Hmac.Generic.AArch64 (initG finG After frame_depth fdepth_lt ce0 ce1 ce2 ce3 ce4)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = out
  x2 : s.gpr .x2 = k
  x3 : (s.gpr .x3).toNat = kl
  x4 : s.gpr .x4 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨out, H.S⟩
  stk_k : (below s.sp 16).Disjoint ⟨k, kl⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) :
    (initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hB := hH.hB
  simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce0, ce1, ce2, ce3, ce4, a.x0, a.x1, a.x2, a.x3, a.x4, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s, a.sp16, a.stk_i, a.stk_o, a.stk_k,
    a.stk_s, a.scnw⟩

theorem hinit_call (hv : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) (hd : H.hmacInit.fdepth ≤ 1)
    {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s' →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.callF hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd)
  intro s' h₁ h₂ h₃ h₄ h₅ hpost
  simp only [initG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3] at hpost
  exact hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄⟩ hpost.1 hpost.2

theorem hinit_rel (hv : Verified AArch64.target H.hmacInit (initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → InitArgs (H := H) s inn out k sc kl ∧ InitArgs (H := H) s' inn out k sc kl ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have x3 : s.gpr .x3 = s'.gpr .x3 := BitVec.eq_of_toNat_eq (by rw [a.x3, a'.x3])
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [initG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x4, a'.x4, x3, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  x0 : s.gpr .x0 = inn
  x1 : s.gpr .x1 = outer
  x2 : s.gpr .x2 = cnt
  x3 : s.gpr .x3 = o
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  sp16 : 16 ≤ s.sp.toNat
  stk_i : (below s.sp 16).Disjoint ⟨inn, H.S⟩
  stk_u : (below s.sp 16).Disjoint ⟨outer, H.S⟩
  stk_o : (below s.sp 16).Disjoint ⟨o, H.D⟩
  stk_s : (below s.sp 16).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : FinArgs (H := H) s inn outer cnt o sc) :
    (finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, State.withRegions_sp,
    State.callEntry_sp, ce0, ce1, ce3, ce4, a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s, a.sp16, a.stk_i, a.stk_u, a.stk_o,
    a.stk_s, a.scnw⟩

theorem hfin_call (hv : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) (hd : H.hmacFin.fdepth ≤ 1)
    {s : State} {inn outer cnt o sc : Addr}
    (a : FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.callF hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd)
  intro s' h₁ h₂ h₃ h₄ h₅ hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄⟩ fun k0 text hk hl hi hc ho => ?_
  have hD := hH.hD; have hB := hH.hB
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB] at hpost
  exact hpost k0 text hk hl hi hc ho

theorem hfin_rel (hv : Verified AArch64.target H.hmacFin (finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs (H := H) s inn outer cnt o sc ∧ FinArgs (H := H) s' inn outer cnt o sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [finG, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  x0 : s.gpr .x0 = key
  x1 : s.gpr .x1 = u
  x2 : s.gpr .x2 = n
  x3 : s.gpr .x3 = t
  x4 : s.gpr .x4 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : IterArgs (H := H) s key u n t sc) :
    (iterK hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [iterK, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr, ce0, ce1, ce3, ce4,
    a.x0, a.x1, a.x3, a.x4, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s, a.knw, a.scnw⟩

theorem iter_call (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) (hd : H.iterate.fdepth ≤ 1)
    {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', After s [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s' →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.callF hv.1 (a.pre hH) (covers_app a.cr a.cw) a.cw ?_ (fdepth_lt hd)
  intro s' h₁ h₂ h₃ h₄ h₅ hpost
  refine hQ s' ⟨h₁, h₂, h₃, h₅, frame_depth hd h₄⟩ fun k0 hk hi ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [iterK, State.withRegions_gpr, State.withRegions_mem, State.callEntry_mem, ce0, ce1, ce2, ce3,
    a.x0, a.x1, a.x2, a.x3, hD, hB, hS] at hpost
  exact hpost k0 hk hi ho

theorem iter_rel (hv : Verified AArch64.target H.iterate (iterK hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → IterArgs (H := H) s key u n t sc ∧ IterArgs (H := H) s' key u n t sc ∧
      s.sp = s'.sp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw⟩
  simp only [iterK, State.withRegions_gpr, State.withRegions_sp, State.callEntry_sp, ce0, ce1, ce2, ce3, ce4,
    a.x0, a'.x0, a.x1, a'.x1, a.x2, a'.x2, a.x3, a'.x3, a.x4, a'.x4, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.AArch64.Pbk
