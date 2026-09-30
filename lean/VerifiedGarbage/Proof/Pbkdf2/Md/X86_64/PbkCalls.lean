import VerifiedGarbage.Proof.Pbkdf2.Md.X86_64.PbkCommon

/-!
# PBKDF2-HMAC over any Merkle–Damgård hash function on x86-64: `pbkdf2`'s calls

Untrusted: everything here is checked by Lean. The calls of HMAC's `init`
and `finalize` and of `iterate`, whose contracts (`initG`, `finG`, `iterG`)
their proofs are given as hypotheses: each is run with `WP.call`, and shown
constant time in two runs with `RelCT.call`. Each uses at most 24 bytes of
stack below `rsp` (a call two deep).
-/

namespace VG.Proof.Pbkdf2.Md.X86_64.Pbk

open VG.X86_64
open VG.Impl.Pbkdf2.Md.X86_64 (Hash)
open VG.Proof.Pbkdf2.Md.X86_64 (HashOK)
open VG.Proof.Hmac.Generic.X86_64 (initG finG iterG ne_rsp callEntry_bytes)
open Spec.Sha256 (bytesAt)
open Spec.Hmac (xorPad ipad opad blockKey hmacBlockKey)

variable {H : Hash} (hH : HashOK H)

theorem ret24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp, 8⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp]; exact Offset.sub_below _ (a := 8) (by omega) (by omega)

theorem stk24 (s : State) : Region.Sub ⟨s.callEntry.gpr .rsp - 16, 16⟩ (below (s.gpr .rsp) 24) := by
  rw [State.callEntry_rsp, show s.gpr .rsp - 8 - 16 = s.gpr .rsp - BitVec.ofNat 64 24 from
    Offset.sub_sub_ofNat _ 8 16]
  exact Offset.sub_below _ (a := 24) (by omega) (by omega)

theorem b16 (s : State) : Region.Sub (below (s.gpr .rsp) 16) (below (s.gpr .rsp) 24) :=
  below_sub (by omega) (by omega)

/-- The bytes of a region outside the 24 bytes below `rsp` read the same on
entry to a callee. -/
theorem entry_bytes (s : State) {p : Addr} {n : Nat} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, n⟩)
    (hn : n ≤ 2 ^ 64) : bytesAt s.callEntry.mem p n = bytesAt s.mem p n := by
  simp only [bytesAt]
  exact List.map_congr_left fun i hi => callEntry_bytes s (hd.sub_left (b16 s)) hn (List.mem_range.mp hi)

/-- A streaming state outside the 24 bytes below `rsp` represents the same
message on entry to a callee. -/
theorem entry_repr (s : State) {p : Addr} (hd : (below (s.gpr .rsp) 24).Disjoint ⟨p, H.S⟩) {m : List Byte}
    (h : hH.SH.Repr s.mem p m) : hH.SH.Repr s.callEntry.mem p m :=
  hH.stream.repr _ _ _ _ _ (fun i hi => callEntry_bytes s (hd.sub_left (b16 s))
    (by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 2 ^ 64; omega) hi) h

/-! ## HMAC's `init` -/

/-- The regions of a call of HMAC's `init`. -/
structure InitArgs (s : State) (inn out k sc : Addr) (kl : Nat) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = out
  rdx : s.gpr .rdx = k
  rcx : (s.gpr .rcx).toNat = kl
  r8 : s.gpr .r8 = sc
  klB : kl ≤ H.P.B
  cr : Covers [⟨k, kl⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨out, H.S⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨out, H.S⟩ ⟨sc, 8 * H.W⟩
  k_i : Region.Disjoint ⟨k, kl⟩ ⟨inn, H.S⟩
  k_o : Region.Disjoint ⟨k, kl⟩ ⟨out, H.S⟩
  k_s : Region.Disjoint ⟨k, kl⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨out, H.S⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨k, kl⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem covers_app {rd wr : List Region} {s : State} (hr : Covers rd (s.rd ++ s.wr)) (hw : Covers wr s.wr) :
    Covers (rd ++ wr) (s.rd ++ s.wr) := fun a n hi => by
  obtain ⟨r, hr', hc⟩ := hi
  rcases List.mem_append.mp hr' with h | h
  · exact hr a n ⟨r, h, hc⟩
  · obtain ⟨r'', h'', hc''⟩ := hw a n ⟨r, h, hc⟩
    exact ⟨r'', List.mem_append_right _ h'', hc''⟩

theorem InitArgs.pre {s : State} {inn out k sc : Addr} {kl : Nat} (a : InitArgs (H := H) s inn out k sc kl) :
    (initG hH.SH H.W).pre (s.callEntry.withRegions [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hB := hH.hB
  simp only [initG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, a.r8, hS, hB]
  exact ⟨a.klB, trivial, trivial, a.i_o, a.i_s, a.o_s, a.k_i, a.k_o, a.k_s,
    a.stk_i.sub_left (ret24 s), a.stk_o.sub_left (ret24 s), a.stk_s.sub_left (ret24 s),
    a.stk_i.sub_left (stk24 s), a.stk_o.sub_left (stk24 s), a.stk_k.sub_left (stk24 s),
    a.stk_s.sub_left (stk24 s), a.scnw⟩

theorem hinit_call (hv : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) (hsp : NoSp H.hmacInit)
    (hd : H.hmacInit.depth ≤ 2) {s : State} {inn out k sc : Addr} {kl : Nat}
    (a : InitArgs (H := H) s inn out k sc kl) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      hH.SH.Repr s'.mem inn (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) ipad) →
      hH.SH.Repr s'.mem out (xorPad (blockKey hH.SH.H (bytesAt s.mem k kl)) opad) → Q s') :
    WP isa (.call H.hmacInitN H.hmacInit) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  have e : bytesAt s.callEntry.mem k kl = bytesAt s.mem k kl :=
    entry_bytes s a.stk_k (by have := a.klB; have := hH.B_le; omega)
  simp only [initG, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, e] at hpost
  exact hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) hpost.1 hpost.2

theorem hinit_rel (hv : Verified X86_64.target H.hmacInit (initG hH.SH H.W)) {P : State → State → Prop}
    {inn out k sc : Addr} {kl : Nat}
    (h : ∀ s s', P s s' → InitArgs (H := H) s inn out k sc kl ∧ InitArgs (H := H) s' inn out k sc kl ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacInitN H.hmacInit) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨k, kl⟩] [⟨inn, H.S⟩, ⟨out, H.S⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  have cx : s.gpr .rcx = s'.gpr .rcx := BitVec.eq_of_toNat_eq (by rw [a.rcx, a'.rcx])
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [initG, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.r8, a'.r8, cx, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## HMAC's `finalize` -/

/-- The regions of a call of HMAC's `finalize`. -/
structure FinArgs (s : State) (inn outer cnt o sc : Addr) : Prop where
  rdi : s.gpr .rdi = inn
  rsi : s.gpr .rsi = outer
  rdx : s.gpr .rdx = cnt
  rcx : s.gpr .rcx = o
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨outer, H.S⟩] (s.rd ++ s.wr)
  cw : Covers [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  i_u : Region.Disjoint ⟨inn, H.S⟩ ⟨outer, H.S⟩
  i_o : Region.Disjoint ⟨inn, H.S⟩ ⟨o, H.D⟩
  i_s : Region.Disjoint ⟨inn, H.S⟩ ⟨sc, 8 * H.W⟩
  u_o : Region.Disjoint ⟨outer, H.S⟩ ⟨o, H.D⟩
  u_s : Region.Disjoint ⟨outer, H.S⟩ ⟨sc, 8 * H.W⟩
  o_s : Region.Disjoint ⟨o, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_i : (below (s.gpr .rsp) 24).Disjoint ⟨inn, H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨outer, H.S⟩
  stk_o : (below (s.gpr .rsp) 24).Disjoint ⟨o, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem FinArgs.pre {s : State} {inn outer cnt o sc : Addr} (a : FinArgs (H := H) s inn outer cnt o sc) :
    (finG hH.SH H.W).pre (s.callEntry.withRegions [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [finG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.i_u, a.i_o, a.i_s, a.u_o, a.u_s, a.o_s,
    a.stk_i.sub_left (ret24 s), a.stk_u.sub_left (ret24 s), a.stk_o.sub_left (ret24 s),
    a.stk_s.sub_left (ret24 s), a.stk_i.sub_left (stk24 s), a.stk_u.sub_left (stk24 s),
    a.stk_o.sub_left (stk24 s), a.stk_s.sub_left (stk24 s), a.scnw⟩

theorem hfin_call (hv : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) (hsp : NoSp H.hmacFin)
    (hd : H.hmacFin.depth ≤ 2) {s : State} {inn outer cnt o sc : Addr}
    (a : FinArgs (H := H) s inn outer cnt o sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0 text, k0.length = H.P.B → k0.length + text.length < 2 ^ 64 →
        hH.SH.Repr s.mem inn (xorPad k0 ipad ++ text) → cnt = BitVec.ofNat 64 (H.P.B + text.length) →
        hH.SH.Repr s.mem outer (xorPad k0 opad) → bytesAt s'.mem o H.D = hmacBlockKey hH.SH.H k0 text) →
      Q s') :
    WP isa (.call H.hmacFinN H.hmacFin) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) fun k0 text hk hl hi hc ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  simp only [finG, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB] at hpost
  exact hpost k0 text hk hl (entry_repr hH s a.stk_i hi) hc (entry_repr hH s a.stk_u ho)

theorem hfin_rel (hv : Verified X86_64.target H.hmacFin (finG hH.SH H.W)) {P : State → State → Prop}
    {inn outer cnt o sc : Addr}
    (h : ∀ s s', P s s' → FinArgs (H := H) s inn outer cnt o sc ∧ FinArgs (H := H) s' inn outer cnt o sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.hmacFinN H.hmacFin) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨outer, H.S⟩] [⟨inn, H.S⟩, ⟨o, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [finG, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

/-! ## `iterate` -/

/-- The regions of a call of `iterate`. -/
structure IterArgs (s : State) (key u : Addr) (n : BitVec 64) (t sc : Addr) : Prop where
  rdi : s.gpr .rdi = key
  rsi : s.gpr .rsi = u
  rdx : s.gpr .rdx = n
  rcx : s.gpr .rcx = t
  r8 : s.gpr .r8 = sc
  cr : Covers [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] (s.rd ++ s.wr)
  cw : Covers [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] s.wr
  k_t : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨t, H.D⟩
  k_s : Region.Disjoint ⟨key, 2 * H.S⟩ ⟨sc, 8 * H.W⟩
  u_t : Region.Disjoint ⟨u, H.D⟩ ⟨t, H.D⟩
  u_s : Region.Disjoint ⟨u, H.D⟩ ⟨sc, 8 * H.W⟩
  t_s : Region.Disjoint ⟨t, H.D⟩ ⟨sc, 8 * H.W⟩
  stk_k : (below (s.gpr .rsp) 24).Disjoint ⟨key, 2 * H.S⟩
  stk_u : (below (s.gpr .rsp) 24).Disjoint ⟨u, H.D⟩
  stk_t : (below (s.gpr .rsp) 24).Disjoint ⟨t, H.D⟩
  stk_s : (below (s.gpr .rsp) 24).Disjoint ⟨sc, 8 * H.W⟩
  knw : key.toNat + 2 * H.S ≤ 2 ^ 64
  scnw : sc.toNat + 8 * H.W ≤ 2 ^ 64

theorem IterArgs.pre {s : State} {key u t sc : Addr} {n : BitVec 64} (a : IterArgs (H := H) s key u n t sc) :
    (iterG hH.SH H.W).pre (s.callEntry.withRegions [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩]) := by
  have hS := hH.hS; have hD := hH.hD
  simp only [iterG, State.withRegions_gpr, State.withRegions_rd, State.withRegions_wr,
    ne_rsp (by decide : Reg.rdi ≠ .rsp), ne_rsp (by decide : Reg.rsi ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a.rsi, a.rcx, a.r8, hS, hD]
  exact ⟨trivial, trivial, a.k_t, a.k_s, a.u_t, a.u_s, a.t_s,
    a.stk_k.sub_left (ret24 s), a.stk_u.sub_left (ret24 s), a.stk_t.sub_left (ret24 s),
    a.stk_s.sub_left (ret24 s), a.stk_k.sub_left (stk24 s), a.stk_u.sub_left (stk24 s),
    a.stk_t.sub_left (stk24 s), a.stk_s.sub_left (stk24 s), a.knw, a.scnw⟩

theorem iter_call (hv : Verified X86_64.target H.iterate (iterG hH.SH H.W)) (hsp : NoSp H.iterate)
    (hd : H.iterate.depth ≤ 2) {s : State} {key u t sc : Addr} {n : BitVec 64}
    (a : IterArgs (H := H) s key u n t sc) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → (∀ r ∈ calleeSaved, s'.gpr r = s.gpr r) →
      Frame ([⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] ++ [below (s.gpr .rsp) 24]) s.mem s'.mem →
      (∀ k0, k0.length = H.P.B → hH.SH.Repr s.mem key (xorPad k0 ipad) →
        hH.SH.Repr s.mem (key + BitVec.ofNat 64 H.S) (xorPad k0 opad) →
        bytesAt s'.mem t H.D = Spec.Pbkdf2.iterate (hmacBlockKey hH.SH.H k0) (n.setWidth 32).toNat
          (bytesAt s.mem u H.D) (bytesAt s.mem t H.D)) →
      Q s') :
    WP isa (.call H.iterN H.iterate) s Q := by
  refine WP.call hv.1 hsp (by omega) (a.pre hH) (covers_app a.cr a.cw) a.cw ?_
  intro s' h₁ h₂ h₃ h₄ _ ⟨s₂, hm, _, hpost⟩
  refine hQ s' h₁ h₂ h₃ (Frame.below_mono h₄ (by omega) (by omega)) fun k0 hk hi ho => ?_
  have hS := hH.hS; have hD := hH.hD; have hB := hH.hB
  have hS2 : H.S ≤ 256 := by have := hH.N_le; have := hH.B_le; show H.P.N + H.P.B ≤ 256; omega
  have hDn : H.D ≤ 2 ^ 64 := by have := hH.hDN; have := hH.N_le; omega
  simp only [iterG, State.withRegions_gpr, State.withRegions_mem, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), a.rdi, a.rsi, a.rdx, a.rcx, hm, hD, hB, hS,
    entry_bytes s a.stk_u hDn, entry_bytes s a.stk_t hDn] at hpost
  have eS : H.S = H.P.N + H.P.B := rfl
  refine hpost k0 hk (entry_repr hH s (a.stk_k.sub_right (Region.sub_prefix (by omega))) hi)
    (entry_repr hH s (a.stk_k.sub_right (Offset.sub_base _ (by omega))) ho)

theorem iter_rel (hv : Verified X86_64.target H.iterate (iterG hH.SH H.W)) {P : State → State → Prop}
    {key u t sc : Addr} {n : BitVec 64}
    (h : ∀ s s', P s s' → IterArgs (H := H) s key u n t sc ∧ IterArgs (H := H) s' key u n t sc ∧
      s.gpr .rsp = s'.gpr .rsp) :
    RelCT isa P (.call H.iterN H.iterate) fun _ _ => True := by
  refine RelCT.call hv.1 hv.2.1 [⟨key, 2 * H.S⟩, ⟨u, H.D⟩] [⟨t, H.D⟩, ⟨sc, 8 * H.W⟩] fun s s' hp => ?_
  obtain ⟨a, a', sp⟩ := h s s' hp
  refine ⟨a.pre hH, a'.pre hH, ?_, covers_app a.cr a.cw, a.cw, covers_app a'.cr a'.cw, a'.cw, sp⟩
  simp only [iterG, State.withRegions_gpr, State.callEntry_rsp, ne_rsp (by decide : Reg.rdi ≠ .rsp),
    ne_rsp (by decide : Reg.rsi ≠ .rsp), ne_rsp (by decide : Reg.rdx ≠ .rsp),
    ne_rsp (by decide : Reg.rcx ≠ .rsp), ne_rsp (by decide : Reg.r8 ≠ .rsp), a.rdi, a'.rdi, a.rsi, a'.rsi,
    a.rdx, a'.rdx, a.rcx, a'.rcx, a.r8, a'.r8, sp]
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial⟩

end VG.Proof.Pbkdf2.Md.X86_64.Pbk
