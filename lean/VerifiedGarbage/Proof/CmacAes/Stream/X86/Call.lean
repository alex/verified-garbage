import VerifiedGarbage.Proof.CmacAes.Stream.X86.Contract
import VerifiedGarbage.Proof.Framework.X86.RelCT

/-!
# Streaming AES-CMAC on x86: the calls

Untrusted: everything here is checked by Lean. A call, in a frame of its
arguments, of each function the streaming functions call
(`vg_aes_expand_key`, `vg_cmac_aes_subkeys`, `vg_cmac_aes_update` and
`vg_cmac_aes_finalize`), from its contract (`WP.callWith`): what it needs
(`…Args`: the registers pushed as its arguments, and the regions), what it
leaves (`…Post`, in terms of the memory before the call), and that two calls
with the same arguments and stack pointer leak the same (`…_rel`, by
`RelCT.callWith`). A call of a function of six arguments uses the 56 bytes
below `esp` (`push`, the return address and the callee's call of
`vg_aes_ctr32`); `vg_cmac_aes_subkeys`, of four, 48; `vg_aes_expand_key`,
which calls nothing, 20.
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86
open VG.Proof.CmacAes.X86 (updateX86 subkeysX86 finalizeX86 update_wp subkeys_wp finalize_wp update_ct
  subkeys_ct finalize_ct toNat_rounds)

/-! ## The stack -/

/-- The registers `call6` pushes. -/
abbrev rs6 : List Reg := [.edi, .esi, .ebx, .edx, .ecx, .eax]

/-- The registers `call4` pushes. -/
abbrev rs4 : List Reg := [.ebx, .edx, .ecx, .eax]

theorem hrs6 : Reg.esp ∉ rs6 := by decide
theorem hrs4 : Reg.esp ∉ rs4 := by decide

/-- A callee's return address, `k + 4` bytes below `esp`. -/
theorem sub_ret {E : BitVec 32} {k b : Nat} (h : k + 4 ≤ b) (hb : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 (k + 4)).setWidth 64, 4⟩ (below E b) := by
  have := below_inner (sp := E) (a := 4) (b := b) (k := k) (by omega) hb
  simp only [below] at this
  rwa [BitVec.sub_sub, ← BitVec.ofNat_add] at this

/-- A callee's stack, the `a` bytes below its stack pointer `E - k`. -/
theorem sub_stk {E : BitVec 32} {k a b : Nat} (h : k + a ≤ b) (hb : b ≤ E.toNat) :
    Region.Sub ⟨(E - BitVec.ofNat 32 k).setWidth 64 - BitVec.ofNat 64 a, a⟩ (below E b) := by
  rw [← Taint.sub_setWidth (by rw [sub_toNat (by omega)]; omega)]
  exact below_inner (by omega) hb

/-- The bytes of a region the stack does not overlap, from the state a call
is made in. -/
theorem entry_bytes {rs : List Reg} {s : State} (hfit : 4 * rs.length + 4 ≤ (s.gpr .esp).toNat)
    (hrs : Reg.esp ∉ rs) {b : Nat} (hb : 4 * rs.length + 4 ≤ b) (hb' : b ≤ (s.gpr .esp).toNat) {p : Addr}
    {n : Nat} (hd : (below (s.gpr .esp) b).Disjoint ⟨p, n⟩) (hn : n ≤ 2 ^ 64) :
    Spec.Aes.bytesAt (pushed rs s).callEntry.mem p n = Spec.Aes.bytesAt s.mem p n :=
  Proof.Cmac.bytesAt_frame (callEntry_frame hfit hrs) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hd.sub_left (below_sub hb hb')).symm) hn

theorem eq_ofNat {x : BitVec 32} {n : Nat} (h : x = BitVec.ofNat 32 n) (hn : n < 2 ^ 32) : x.toNat = n := by
  rw [h, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-! ## The callees -/

theorem upd_nosp : NoSp Impl.CmacAes.X86.update := NoSp.of_all (by lit_decide)
theorem upd_stack : stackUse Impl.CmacAes.X86.update = 28 := by lit_decide
theorem sub_nosp : NoSp Impl.CmacAes.X86.subkeys := NoSp.of_all (by lit_decide)
theorem sub_stack : stackUse Impl.CmacAes.X86.subkeys = 28 := by lit_decide
theorem fin_nosp : NoSp Impl.CmacAes.X86.finalize := NoSp.of_all (by lit_decide)
theorem fin_stack : stackUse Impl.CmacAes.X86.finalize = 28 := by lit_decide
theorem ek_nosp : NoSp Impl.Aes.X86.expandKey := NoSp.of_all (by lit_decide)
theorem ek_stack : stackUse Impl.Aes.X86.expandKey = 0 := by lit_decide

/-! ## `vg_cmac_aes_update` -/

/-- What a call of `vg_cmac_aes_update` needs: the key schedule `W`, the
chaining value `C`, `n` blocks at `D`, the working space `S` and the rounds
`R`, in `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi`. -/
structure UArgs (s : State) (W C D S : BitVec 32) (R n : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = C
  ebx : s.gpr .ebx = D
  esi : s.gpr .esi = BitVec.ofNat 32 n
  edi : s.gpr .edi = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 56 ≤ (s.gpr .esp).toNat
  hn : 16 * n < 2 ^ 32
  wc : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  dc : (⟨D.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨C.setWidth 64, 16⟩
  ds : (⟨D.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  cs : (⟨C.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bW : (below (s.gpr .esp) 56).Disjoint ⟨W.setWidth 64, 240⟩
  bD : (below (s.gpr .esp) 56).Disjoint ⟨D.setWidth 64, 16 * n⟩
  bC : (below (s.gpr .esp) 56).Disjoint ⟨C.setWidth 64, 16⟩
  bS : (below (s.gpr .esp) 56).Disjoint ⟨S.setWidth 64, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fC : C.toNat + 16 ≤ 2 ^ 32
  fD : D.toNat + 16 * n ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩, ⟨D.setWidth 64, 16 * n⟩] (s.rd ++ s.wr)
  writes : Covers [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_update` leaves. -/
structure UPost (s : State) (W C D S : BitVec 32) (R n : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (C.setWidth 64) 16 =
    Spec.Cmac.chain (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1))))
      (Spec.Aes.bytesAt s.mem (C.setWidth 64) 16) (Spec.Cmac.blocksAt s.mem (D.setWidth 64) 16 n)

/-- The regions `vg_cmac_aes_update` is called with. -/
abbrev uRd (E W D : BitVec 32) (n : Nat) : List Region :=
  [⟨W.setWidth 64, 240⟩, ⟨D.setWidth 64, 16 * n⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev uWr (C S : BitVec 32) : List Region := [⟨C.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩]

namespace UArgs
variable {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n)
include h

theorem fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rs6 s).callEntry 0 = W ∧ arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed rs6 s).callEntry 2 = C ∧ arg (pushed rs6 s).callEntry 3 = D ∧
    arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 n ∧ arg (pushed rs6 s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs6 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi]

theorem callPre : CallPre updateX86 rs6 (uRd (s.gpr .esp) W D n) (uWr C S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega)
  have he := h.esp
  have eA : argAddr (pushed rs6 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed rs6 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (24 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 56) := below_sub (by omega) he
  have bR := sub_ret (E := s.gpr .esp) (k := 24) (b := 56) (by omega) he
  have bK := sub_stk (E := s.gpr .esp) (k := 24 + 4) (a := 28) (b := 56) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [updateX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hN]
    refine ⟨trivial, trivial, h.wc, h.ws, h.dc, h.ds, h.cs, h.bC.sub_left bA, h.bS.sub_left bA,
      h.bC.sub_left bR, h.bS.sub_left bR, h.bW.sub_left bK, h.bD.sub_left bK, h.bC.sub_left bK,
      h.bS.sub_left bK, h.fW, h.fC, h.fD, h.fS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end UArgs

theorem upd_call {s : State} {W C D S : BitVec 32} {R n : Nat} (h : UArgs s W C D S R n) :
    WP isa (call6 "vg_cmac_aes_update" Impl.CmacAes.X86.update) s (UPost s W C D S R n) := by
  have hR := toNat_rounds h.rounds
  have hN : (BitVec.ofNat 32 n).toNat = n := eq_ofNat rfl (by have := h.hn; omega)
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := rs6) (k := updateX86) (fun _ hs => update_wp hs) upd_nosp (by simp) hrs6
    (by rw [upd_stack]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [upd_stack] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : BitVec 32} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p.setWidth 64, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed rs6 s).callEntry.mem (p.setWidth 64) k = Spec.Aes.bytesAt s.mem (p.setWidth 64) k :=
    fun hd hk => entry_bytes h.fit hrs6 (by simp) he hd hk
  simp only [updateX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hN, m₂] at post
  rw [post, Proof.Cmac.Stream.blocksAt_eq, Proof.Cmac.Stream.blocksAt_eq, Proof.CmacAes.X86.ciphAt,
    keep (h.bW.sub_right (Region.sub_prefix hRb)) (by omega), keep h.bC (by decide),
    keep h.bD (by have := h.hn; omega)]

theorem upd_rel {W C D S E : BitVec 32} {R n : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → UArgs s₁ W C D S R n ∧ UArgs s₂ W C D S R n ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call6 "vg_cmac_aes_update" Impl.CmacAes.X86.update) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => update_wp hs) update_ct (uRd E W D n) (uWr C S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

/-! ## `vg_cmac_aes_finalize` -/

/-- What a call of `vg_cmac_aes_finalize` needs: the key schedule and
subkeys `K`, the state `St`, the `L` last bytes at `P`, the working space
`S` and the rounds `R`, in `eax`, `ecx`, `edx`, `ebx`, `esi` and `edi`. -/
structure FArgs (s : State) (K St P S : BitVec 32) (L R : Nat) : Prop where
  eax : s.gpr .eax = K
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = St
  ebx : s.gpr .ebx = P
  esi : s.gpr .esi = BitVec.ofNat 32 L
  edi : s.gpr .edi = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  len : L ≤ 16
  esp : 56 ≤ (s.gpr .esp).toNat
  kst : (⟨K.setWidth 64, 272⟩ : Region).Disjoint ⟨St.setWidth 64, 16⟩
  ks : (⟨K.setWidth 64, 272⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  pst : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨St.setWidth 64, 16⟩
  ps : (⟨P.setWidth 64, L⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  sts : (⟨St.setWidth 64, 16⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bK : (below (s.gpr .esp) 56).Disjoint ⟨K.setWidth 64, 272⟩
  bP : (below (s.gpr .esp) 56).Disjoint ⟨P.setWidth 64, L⟩
  bSt : (below (s.gpr .esp) 56).Disjoint ⟨St.setWidth 64, 16⟩
  bS : (below (s.gpr .esp) 56).Disjoint ⟨S.setWidth 64, 2176⟩
  fK : K.toNat + 272 ≤ 2 ^ 32
  fSt : St.toNat + 16 ≤ 2 ^ 32
  fP : P.toNat + L ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨K.setWidth 64, 272⟩, ⟨P.setWidth 64, L⟩] (s.rd ++ s.wr)
  writes : Covers [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_finalize` leaves. -/
structure FPost (s : State) (K St P S : BitVec 32) (L R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 56] s.mem s'.mem
  out : let ciph := Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (K.setWidth 64) (16 * (R + 1)))
    let ks := Spec.Cmac.subkeys ciph 16
    Spec.Aes.bytesAt s.mem (K.setWidth 64 + 240) 32 = ks.1 ++ ks.2 →
    ∀ msg : List Byte, msg.length % 16 = 0 → (msg = [] ∨ 0 < L) →
      Spec.Aes.bytesAt s.mem (St.setWidth 64) 16 = Spec.Cmac.chain ciph (Spec.Cmac.zeros 16) (Spec.Cmac.blocks 16 msg) →
      Spec.Aes.bytesAt s'.mem (St.setWidth 64) 16 =
        Spec.Cmac.macFull ciph 16 (msg ++ Spec.Aes.bytesAt s.mem (P.setWidth 64) L)

/-- The regions `vg_cmac_aes_finalize` is called with. -/
abbrev fRd (E K P : BitVec 32) (L : Nat) : List Region :=
  [⟨K.setWidth 64, 272⟩, ⟨P.setWidth 64, L⟩, ⟨(E - BitVec.ofNat 32 24).setWidth 64, 24⟩]
abbrev fWr (St S : BitVec 32) : List Region := [⟨St.setWidth 64, 16⟩, ⟨S.setWidth 64, 2176⟩]

namespace FArgs
variable {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R)
include h

theorem fit : 4 * rs6.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rs6 s).callEntry 0 = K ∧ arg (pushed rs6 s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed rs6 s).callEntry 2 = St ∧ arg (pushed rs6 s).callEntry 3 = P ∧
    arg (pushed rs6 s).callEntry 4 = BitVec.ofNat 32 L ∧ arg (pushed rs6 s).callEntry 5 = S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs6 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx, h.esi, h.edi]

theorem callPre : CallPre finalizeX86 rs6 (fRd (s.gpr .esp) K P L) (fWr St S) s := by
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h.args
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  have he := h.esp
  have eA : argAddr (pushed rs6 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 24).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed rs6 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (24 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 24) (below (s.gpr .esp) 56) := below_sub (by omega) he
  have bR := sub_ret (E := s.gpr .esp) (k := 24) (b := 56) (by omega) he
  have bK := sub_stk (E := s.gpr .esp) (k := 24 + 4) (a := 28) (b := 56) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [finalizeX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, a4, a5, eA, eSp, hR, hL]
    refine ⟨trivial, trivial, h.kst, h.ks, h.pst, h.ps, h.sts, h.bSt.sub_left bA, h.bS.sub_left bA,
      h.bSt.sub_left bR, h.bS.sub_left bR, h.bK.sub_left bK, h.bP.sub_left bK, h.bSt.sub_left bK,
      h.bS.sub_left bK, h.fK, h.fSt, h.fP, h.fS, ?_, ?_, h.rounds, h.len⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end FArgs

theorem fin_call {s : State} {K St P S : BitVec 32} {L R : Nat} (h : FArgs s K St P S L R) :
    WP isa (call6 "vg_cmac_aes_finalize" Impl.CmacAes.X86.finalize) s (FPost s K St P S L R) := by
  have hR := toNat_rounds h.rounds
  have hL : (BitVec.ofNat 32 L).toNat = L := eq_ofNat rfl (by have := h.len; omega)
  have hRb : 16 * (R + 1) ≤ 272 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := rs6) (k := finalizeX86) (fun _ hs => finalize_wp hs) fin_nosp (by simp) hrs6
    (by rw [fin_stack]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, a3, a4, -⟩ := h.args
  rw [fin_stack] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  have keep : ∀ {p : Addr} {k : Nat}, (below (s.gpr .esp) 56).Disjoint ⟨p, k⟩ → k ≤ 2 ^ 64 →
      Spec.Aes.bytesAt (pushed rs6 s).callEntry.mem p k = Spec.Aes.bytesAt s.mem p k :=
    fun hd hk => entry_bytes h.fit hrs6 (by simp) he hd hk
  simp only [finalizeX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, a3, a4, hR, hL, m₂] at post
  intro _ _ hk msg hm hne hst
  have eK := keep (h.bK.sub_right (Region.sub_prefix hRb)) (by omega)
  have eK2 := keep (p := K.setWidth 64 + 240) (k := 32)
    (h.bK.sub_right (Offset.sub_base (K.setWidth 64) (d := 240) (n := 32) (by decide))) (by decide)
  have eSt := keep h.bSt (by decide)
  have eP := keep h.bP (by omega)
  simp only [Proof.CmacAes.X86.ciphAt, eK, eK2, eSt, eP] at post
  exact post hk msg hm hne hst

theorem fin_rel {K St P S E : BitVec 32} {L R : Nat} {Q : State → State → Prop}
    (h : ∀ s₁ s₂, Q s₁ s₂ → FArgs s₁ K St P S L R ∧ FArgs s₂ K St P S L R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa Q (call6 "vg_cmac_aes_finalize" Impl.CmacAes.X86.finalize) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => finalize_wp hs) finalize_ct (fRd E K P L) (fWr St S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3, b4, b5⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5) with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]
  · rw [a4, b4]
  · rw [a5, b5]

/-! ## `vg_cmac_aes_subkeys` -/

/-- What a call of `vg_cmac_aes_subkeys` needs: the key schedule `W`, the
subkeys `K`, the working space `S` and the rounds `R`, in `eax`, `ecx`,
`edx` and `ebx`. -/
structure SArgs (s : State) (W K S : BitVec 32) (R : Nat) : Prop where
  eax : s.gpr .eax = W
  ecx : s.gpr .ecx = BitVec.ofNat 32 R
  edx : s.gpr .edx = K
  ebx : s.gpr .ebx = S
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  esp : 48 ≤ (s.gpr .esp).toNat
  wk : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨K.setWidth 64, 32⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  ks : (⟨K.setWidth 64, 32⟩ : Region).Disjoint ⟨S.setWidth 64, 2176⟩
  bW : (below (s.gpr .esp) 48).Disjoint ⟨W.setWidth 64, 240⟩
  bK : (below (s.gpr .esp) 48).Disjoint ⟨K.setWidth 64, 32⟩
  bS : (below (s.gpr .esp) 48).Disjoint ⟨S.setWidth 64, 2176⟩
  fW : W.toNat + 240 ≤ 2 ^ 32
  fK : K.toNat + 32 ≤ 2 ^ 32
  fS : S.toNat + 2176 ≤ 2 ^ 32
  reads : Covers [⟨W.setWidth 64, 240⟩] (s.rd ++ s.wr)
  writes : Covers [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩] s.wr

/-- What a call of `vg_cmac_aes_subkeys` leaves. -/
structure SPost (s : State) (W K S : BitVec 32) (R : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩, below (s.gpr .esp) 48] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (K.setWidth 64) 32 =
    (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))) 16).1 ++
      (Spec.Cmac.subkeys (Spec.Cmac.aesWith R (Spec.Aes.bytesAt s.mem (W.setWidth 64) (16 * (R + 1)))) 16).2

/-- The regions `vg_cmac_aes_subkeys` is called with. -/
abbrev sRd (E W : BitVec 32) : List Region :=
  [⟨W.setWidth 64, 240⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev sWr (K S : BitVec 32) : List Region := [⟨K.setWidth 64, 32⟩, ⟨S.setWidth 64, 2176⟩]

namespace SArgs
variable {s : State} {W K S : BitVec 32} {R : Nat} (h : SArgs s W K S R)
include h

theorem fit : 4 * rs4.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rs4 s).callEntry 0 = W ∧ arg (pushed rs4 s).callEntry 1 = BitVec.ofNat 32 R ∧
    arg (pushed rs4 s).callEntry 2 = K ∧ arg (pushed rs4 s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs4 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx]

theorem callPre : CallPre subkeysX86 rs4 (sRd (s.gpr .esp) W) (sWr K S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hR := toNat_rounds h.rounds
  have he := h.esp
  have eA : argAddr (pushed rs4 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed rs4 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (16 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 48) := below_sub (by omega) he
  have bR := sub_ret (E := s.gpr .esp) (k := 16) (b := 48) (by omega) he
  have bK := sub_stk (E := s.gpr .esp) (k := 16 + 4) (a := 28) (b := 48) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [subkeysX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hR]
    refine ⟨trivial, trivial, h.wk, h.ws, h.ks, h.bK.sub_left bA, h.bS.sub_left bA,
      h.bK.sub_left bR, h.bS.sub_left bR, h.bW.sub_left bK, h.bK.sub_left bK,
      h.bS.sub_left bK, h.fW, h.fK, h.fS, ?_, ?_, h.rounds⟩
    · rw [sub_toNat (by omega)]; omega
    · rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end SArgs

theorem sub_call {s : State} {W K S : BitVec 32} {R : Nat} (h : SArgs s W K S R) :
    WP isa (call4 "vg_cmac_aes_subkeys" Impl.CmacAes.X86.subkeys) s (SPost s W K S R) := by
  have hR := toNat_rounds h.rounds
  have hRb : 16 * (R + 1) ≤ 240 := by rcases h.rounds with h | h | h <;> omega
  have he := h.esp
  refine WP.callWith (rs := rs4) (k := subkeysX86) (fun _ hs => subkeys_wp hs) sub_nosp (by simp) hrs4
    (by rw [sub_stack]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [sub_stack] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [subkeysX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hR, m₂] at post
  rw [post, Proof.CmacAes.X86.ciphAt,
    entry_bytes h.fit hrs4 (by simp) he (h.bW.sub_right (Region.sub_prefix hRb)) (by omega)]

theorem sub_rel {W K S E : BitVec 32} {R : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → SArgs s₁ W K S R ∧ SArgs s₂ W K S R ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call4 "vg_cmac_aes_subkeys" Impl.CmacAes.X86.subkeys) fun _ _ => True := by
  refine RelCT.callWith (fun _ hs => subkeys_wp hs) subkeys_ct (sRd E W) (sWr K S) fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

/-! ## `vg_aes_expand_key` -/

/-- What a call of `vg_aes_expand_key` needs: the key `Kp` of `KL` bytes,
the schedule `W` and the working space `S`, in `eax`, `ecx`, `edx` and
`ebx`. -/
structure EArgs (s : State) (Kp W S : BitVec 32) (KL : Nat) : Prop where
  eax : s.gpr .eax = Kp
  ecx : s.gpr .ecx = BitVec.ofNat 32 KL
  edx : s.gpr .edx = W
  ebx : s.gpr .ebx = S
  klen : KL = 16 ∨ KL = 24 ∨ KL = 32
  esp : 20 ≤ (s.gpr .esp).toNat
  kw : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨W.setWidth 64, 240⟩
  ks : (⟨Kp.setWidth 64, KL⟩ : Region).Disjoint ⟨S.setWidth 64, 512⟩
  ws : (⟨W.setWidth 64, 240⟩ : Region).Disjoint ⟨S.setWidth 64, 512⟩
  bK : (below (s.gpr .esp) 20).Disjoint ⟨Kp.setWidth 64, KL⟩
  bW : (below (s.gpr .esp) 20).Disjoint ⟨W.setWidth 64, 240⟩
  bS : (below (s.gpr .esp) 20).Disjoint ⟨S.setWidth 64, 512⟩
  fK : Kp.toNat + KL ≤ 2 ^ 32
  fW : W.toNat + 240 ≤ 2 ^ 32
  fS : S.toNat + 512 ≤ 2 ^ 32
  reads : Covers [⟨Kp.setWidth 64, KL⟩] (s.rd ++ s.wr)
  writes : Covers [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩] s.wr

/-- What a call of `vg_aes_expand_key` leaves. -/
structure EPost (s : State) (Kp W S : BitVec 32) (KL : Nat) (s' : State) : Prop where
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  saved : ∀ r ∈ calleeSaved, s'.gpr r = s.gpr r
  frame : Frame [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩, below (s.gpr .esp) 20] s.mem s'.mem
  out : Spec.Aes.bytesAt s'.mem (W.setWidth 64) (16 * (Spec.Aes.rounds (KL / 4) + 1)) =
    Spec.Aes.expandKey (Spec.Aes.bytesAt s.mem (Kp.setWidth 64) KL)

/-- The regions `vg_aes_expand_key` is called with. -/
abbrev eRd (E Kp : BitVec 32) (KL : Nat) : List Region :=
  [⟨Kp.setWidth 64, KL⟩, ⟨(E - BitVec.ofNat 32 16).setWidth 64, 16⟩]
abbrev eWr (W S : BitVec 32) : List Region := [⟨W.setWidth 64, 240⟩, ⟨S.setWidth 64, 512⟩]

namespace EArgs
variable {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : EArgs s Kp W S KL)
include h

theorem fit : 4 * rs4.length + 4 ≤ (s.gpr .esp).toNat := by have := h.esp; simp only [List.length_cons, List.length_nil]; omega

theorem args : arg (pushed rs4 s).callEntry 0 = Kp ∧ arg (pushed rs4 s).callEntry 1 = BitVec.ofNat 32 KL ∧
    arg (pushed rs4 s).callEntry 2 = W ∧ arg (pushed rs4 s).callEntry 3 = S := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  rw [callEntry_arg h.fit hrs4 (by decide)] <;> simp [h.eax, h.ecx, h.edx, h.ebx]

theorem callPre : CallPre Proof.Aes.expandKeyX86 rs4 (eRd (s.gpr .esp) Kp KL) (eWr W S) s := by
  obtain ⟨a0, a1, a2, a3⟩ := h.args
  have hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h | h <;> omega)
  have he := h.esp
  have eA : argAddr (pushed rs4 s).callEntry 0 = (s.gpr .esp - BitVec.ofNat 32 16).setWidth 64 := by
    rw [callEntry_argAddr0]; rfl
  have eSp : (pushed rs4 s).callEntry.gpr .esp = s.gpr .esp - BitVec.ofNat 32 (16 + 4) := by
    rw [callEntry_esp']; rfl
  have bA : Region.Sub (below (s.gpr .esp) 16) (below (s.gpr .esp) 20) := below_sub (by omega) he
  have bR := sub_ret (E := s.gpr .esp) (k := 16) (b := 20) (by omega) he
  refine ⟨?_, ?_, ?_⟩
  · simp only [Proof.Aes.expandKeyX86, State.withRegions_rd, State.withRegions_wr, State.withRegions_gpr,
      arg_withRegions, argAddr_withRegions, a0, a1, a2, a3, eA, eSp, hK]
    refine ⟨trivial, trivial, h.kw, h.ks, h.ws, h.bW.sub_left bA, h.bS.sub_left bA,
      h.bW.sub_left bR, h.bS.sub_left bR, h.fK, h.fW, h.fS, ?_, h.klen⟩
    rw [sub_toNat (by omega)]; have := (s.gpr .esp).isLt; omega
  · intro a k ⟨r, hr, hcn⟩
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · obtain ⟨r', hr', hc'⟩ := h.reads a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', hr', hc'⟩)
    · exact InRegions_append_cons.mpr (.inl hcn)
    all_goals
      obtain ⟨r', hr', hc'⟩ := h.writes a k ⟨_, by simp, hcn⟩
      exact InRegions_append_cons.mpr (.inr ⟨r', List.mem_append_right _ hr', hc'⟩)
  · intro a k hi
    obtain ⟨r', hr', hc'⟩ := h.writes a k hi
    exact ⟨r', List.mem_cons_of_mem _ hr', hc'⟩

end EArgs

theorem ek_call {s : State} {Kp W S : BitVec 32} {KL : Nat} (h : EArgs s Kp W S KL) :
    WP isa (call4 "vg_aes_expand_key" Impl.Aes.X86.expandKey) s (EPost s Kp W S KL) := by
  have hK : (BitVec.ofNat 32 KL).toNat = KL := eq_ofNat rfl (by rcases h.klen with h | h | h <;> omega)
  have he := h.esp
  refine WP.callWith (rs := rs4) (k := Proof.Aes.expandKeyX86) Proof.Aes.X86.expandKey_correct ek_nosp
    (by simp) hrs4 (by rw [ek_stack]; simp only [List.length_cons, List.length_nil]; omega) h.callPre
    fun s' rd' wr' cs' f' ⟨s₂, m₂, post⟩ => ?_
  obtain ⟨a0, a1, a2, -⟩ := h.args
  rw [ek_stack] at f'
  refine ⟨rd', wr', cs', f'.mono fun r hr => by simpa using hr, ?_⟩
  simp only [Proof.Aes.expandKeyX86, arg_withRegions, State.withRegions_mem, a0, a1, a2, hK, m₂] at post
  rw [post, entry_bytes h.fit hrs4 (by simp) he h.bK (by rcases h.klen with h | h | h <;> omega)]

theorem ek_rel {Kp W S E : BitVec 32} {KL : Nat} {P : State → State → Prop}
    (h : ∀ s₁ s₂, P s₁ s₂ → EArgs s₁ Kp W S KL ∧ EArgs s₂ Kp W S KL ∧ s₁.gpr .esp = E ∧ s₂.gpr .esp = E) :
    RelCT isa P (call4 "vg_aes_expand_key" Impl.Aes.X86.expandKey) fun _ _ => True := by
  refine RelCT.callWith Proof.Aes.X86.expandKey_correct Proof.Aes.X86.expandKey_ct (eRd E Kp KL) (eWr W S)
    fun s₁ s₂ hp => ?_
  obtain ⟨h₁, h₂, e₁, e₂⟩ := h s₁ s₂ hp
  have p₁ := h₁.callPre
  have p₂ := h₂.callPre
  rw [e₁] at p₁
  rw [e₂] at p₂
  refine ⟨p₁, p₂, e₁.trans e₂.symm, ?_⟩
  obtain ⟨a0, a1, a2, a3⟩ := h₁.args
  obtain ⟨b0, b1, b2, b3⟩ := h₂.args
  refine ⟨by simp only [State.withRegions_gpr, callEntry_esp', e₁, e₂], fun i hi => ?_⟩
  simp only [arg_withRegions]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl
  · rw [a0, b0]
  · rw [a1, b1]
  · rw [a2, b2]
  · rw [a3, b3]

end VG.Proof.CmacAes.Stream.X86
