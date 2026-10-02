import VerifiedGarbage.Proof.MlDsa.AArch64.Message.Rel
import VerifiedGarbage.Proof.MlDsa.AArch64.Call.Base

/-!
# ML-DSA on AArch64, `sign_message` and `verify_message`: two runs of the hashing

Untrusted: everything here is checked by Lean. In two runs with the same
layout (`Two`), zeroing the state and each call of a sponge function leak
the same: their addresses and arguments are functions of the layout alone,
and the sponge functions' public data are those arguments (`zeroSt_tr`,
`kabs_tr`, `kpad_tr`, `ksqz_tr`); so do `muHash` and `trHash`.
-/

namespace VG.Proof.MlDsa.AArch64.Message

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.AArch64 (Only)
open VG.Spec.Sha3 (rates)
open VG.Spec.MlDsa (Params)

section
variable {I : Lay → Mem → Mem → Prop}

/-! ## Zeroing the state -/

theorem zeroSt_taint : (taint.check (AArch64.Taint.ofRegs [.x28]) (.block zeroSt) (.block [])).isSome = true := by
  rfl

theorem zeroSt_tr {Φ : Lay → Mem → State → Prop} : RelCT isa (Two I Φ) (.block zeroSt) fun _ _ => True :=
  AArch64.taintRel [.x28] (fun a b h => ⟨h.x28.2, fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact h.x28.1⟩) zeroSt_taint

/-! ## The sponge functions -/

/-- The arguments of a call of `vg_keccak_absorb`, in its registers. -/
structure AbsA (s : State) (st dt sc : Addr) (pos len : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h3 : s.gpr .x3 = dt
  h4 : (s.gpr .x4).toNat = len
  h5 : s.gpr .x5 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₂ : Region.Disjoint ⟨dt, len⟩ ⟨st, 200⟩
  d₃ : Region.Disjoint ⟨dt, len⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨dt, len⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem AbsA.pre {s : State} {st dt sc : Addr} {pos len : Nat} (h : AbsA s st dt sc pos len) :
    Proof.Sha3.absorbAArch64.pre (s.callEntry.withRegions [⟨dt, len⟩] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.absorbAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x3), gpr_ce s (r := .x4), gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, h.hp⟩

theorem absA_of {L : Lay} (hL : L.Ok) {g : Reg → BitVec 64} {v : VReg → BitVec 128} {m₀ : Mem} {t t1 : State}
    (hc : Ctx L g v m₀ t) {src len pos : Arg} (hm : Moved (absArgs src len pos) t t1) {dp : Addr} {n q : Nat}
    (hdp : src.val t = dp) (hn : len.val t = BitVec.ofNat 64 n) (hq : pos.val t = BitVec.ofNat 64 q)
    (hql : q < 136) (hnl : n < 2 ^ 64) (dS : Region.Disjoint ⟨dp, n⟩ ⟨L.ST, 200⟩)
    (dK : Region.Disjoint ⟨dp, n⟩ ⟨L.KS, 640⟩) (kD : L.STK.Disjoint ⟨dp, n⟩) : AbsA t1 L.ST dp L.KS q n := by
  have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
  have e2 := hm.1 (.x2, pos) (by simp)
  have e0 := hm.1 (.x0, .off oST) (by simp)
  have e1 := hm.1 (.x1, .imm 136) (by simp)
  have e3 := hm.1 (.x3, src) (by simp)
  have e4 := hm.1 (.x4, len) (by simp)
  have e5 := hm.1 (.x5, .off oKS) (by simp)
  simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e5
  rw [hq] at e2
  rw [hdp] at e3
  rw [hn] at e4
  exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega, e3, by rw [e4, BitVec.toNat_ofNat]; omega, e5,
    hql, st_ks, dS, dK, by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
    by simp only [Proof.MlKem.AArch64.stk, hs1]; exact kD, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩

/-- Two runs of a call of `vg_keccak_absorb` whose arguments are the same
functions of the layout in both. -/
theorem kabs_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {src len pos : Arg}
    (hok : argsOk (absArgs src len pos) = true) (dp : Lay → Addr) (n q : Lay → Nat)
    (hv : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t →
      src.val t = dp L ∧ len.val t = BitVec.ofNat 64 (n L) ∧ pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136 ∧ n L < 2 ^ 64 ∧ (∃ R ∈ L.rd ++ L.wr, Within ⟨dp L, n L⟩ R) ∧
      Region.Disjoint ⟨dp L, n L⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨dp L, n L⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨dp L, n L⟩) :
    RelCT isa (Two I Φ) (kabs v.callee src len pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      Moved (absArgs src len pos) t t1 → AbsA t1 L.ST (dp L) L.KS (q L) (n L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      obtain ⟨h1, h2, h3⟩ := hv L g vv m₀ t hL hc hφ
      obtain ⟨s1, s2, _, s4, s5, s6⟩ := hs L hL
      exact absA_of hL hc hm h1 h2 h3 s1 s2 s4 s5 s6
  refine call_tr hok (Proof.Sha3.AArch64.Stream.Absorb.absorb_correct v)
    (Proof.Sha3.AArch64.Stream.Absorb.absorb_ct v) (fun L => [⟨dp L, n L⟩]) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.absorbAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x3),
      gpr_ce a1 (r := .x4), gpr_ce a1 (r := .x5), gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1),
      gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x3), gpr_ce b1 (r := .x4), gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · obtain ⟨_, _, hin, _, _, _⟩ := hs L hL
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · simp only [List.mem_singleton] at hr; subst hr; exact hin
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
      · exact cov_xw hL (e := 200) (by omega)

/-- The arguments of a call of `vg_keccak_pad`, in its registers. -/
structure PadA (s : State) (st sc : Addr) (pos : Nat) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = pos
  h4 : s.gpr .x4 = sc
  hp : pos < 136
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem PadA.pre {s : State} {st sc : Addr} {pos : Nat} (h : PadA s st sc pos) :
    Proof.Sha3.padAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.padAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x4), h.h0, h.h1, h.h2, h.h4]
  exact ⟨trivial, trivial, h.d₁, h.hsp, h.k₁, h.k₃, by decide, h.hp⟩

theorem kpad_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {pos : Arg}
    (hok : argsOk (padArgs pos) = true) (q : Lay → Nat)
    (hv : ∀ (L : Lay) g vv m (t : State), L.Ok → Ctx L g vv m t → Φ L m t → pos.val t = BitVec.ofNat 64 (q L))
    (hs : ∀ L : Lay, L.Ok → q L < 136) :
    RelCT isa (Two I Φ) (kpad v.callee pos) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t → Φ L m₀ t →
      Moved (padArgs pos) t t1 → PadA t1 L.ST L.KS (q L) :=
    fun L g vv m₀ t t1 hL hc hφ hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e2 := hm.1 (.x2, pos) (by simp)
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e4 := hm.1 (.x4, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, x0] at e0 e1 e4
      rw [hv L g vv m₀ t hL hc hφ] at e2
      have := hs L hL
      exact ⟨e0, by rw [e1]; rfl, by rw [e2, BitVec.toNat_ofNat]; omega, e4, this, st_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩
  refine call_tr hok (Proof.Sha3.AArch64.Stream.Pad.pad_correct v) (Proof.Sha3.AArch64.Stream.Pad.pad_ct v)
    (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc hφ hm => (args L g vv m₀ t t1 hL hc hφ hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ φ₁ φ₂ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ φ₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ φ₂ f₂
    simp only [Proof.Sha3.padAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x4),
      gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1), gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x4),
      x.h0, x.h4, y.h0, y.h4, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_xw hL (e := 200) (by omega)

/-- The arguments of a call of `vg_keccak_squeeze`, in its registers. -/
structure SqzA (s : State) (st out sc : Addr) : Prop where
  h0 : s.gpr .x0 = st
  h1 : (s.gpr .x1).toNat = 136
  h2 : (s.gpr .x2).toNat = 0
  h3 : s.gpr .x3 = out
  h4 : (s.gpr .x4).toNat = 64
  h5 : s.gpr .x5 = sc
  d₁ : Region.Disjoint ⟨st, 200⟩ ⟨out, 64⟩
  d₂ : Region.Disjoint ⟨st, 200⟩ ⟨sc, 640⟩
  d₃ : Region.Disjoint ⟨out, 64⟩ ⟨sc, 640⟩
  hsp : 16 ≤ s.sp.toNat
  k₁ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨st, 200⟩
  k₂ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨out, 64⟩
  k₃ : (Proof.MlKem.AArch64.stk s).Disjoint ⟨sc, 640⟩

theorem SqzA.pre {s : State} {st out sc : Addr} (h : SqzA s st out sc) :
    Proof.Sha3.squeezeAArch64.pre (s.callEntry.withRegions [] [⟨st, 200⟩, ⟨out, 64⟩, ⟨sc, 640⟩]) := by
  simp only [Proof.Sha3.squeezeAArch64, State.withRegions_rd, State.withRegions_wr,
    State.withRegions_sp, State.callEntry_sp, gpr_ce s (r := .x0), gpr_ce s (r := .x1), gpr_ce s (r := .x2),
    gpr_ce s (r := .x3), gpr_ce s (r := .x4), gpr_ce s (r := .x5), h.h0, h.h1, h.h2, h.h3, h.h4, h.h5]
  exact ⟨trivial, trivial, h.d₁, h.d₂, h.d₃, h.hsp, h.k₁, h.k₂, h.k₃, by decide, by decide⟩

theorem ksqz_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} :
    RelCT isa (Two I Φ) (ksqz v.callee) fun _ _ => True := by
  have args : ∀ (L : Lay) g vv m₀ (t t1 : State), L.Ok → Ctx L g vv m₀ t →
      Moved sqzArgs t t1 → SqzA t1 L.ST L.MU L.KS :=
    fun L g vv m₀ t t1 hL hc hm => by
      have hs1 : t1.sp = L.SP := hm.2.sp.trans hc.sp
      have e0 := hm.1 (.x0, .off oST) (by simp)
      have e1 := hm.1 (.x1, .imm 136) (by simp)
      have e2 := hm.1 (.x2, .imm 0) (by simp)
      have e3 := hm.1 (.x3, .off oMU) (by simp)
      have e4 := hm.1 (.x4, .imm 64) (by simp)
      have e5 := hm.1 (.x5, .off oKS) (by simp)
      simp only [Arg.val, hc.x28, oST, oKS, oMU, x0] at e0 e1 e2 e3 e4 e5
      exact ⟨e0, by rw [e1]; rfl, by rw [e2]; rfl, e3, by rw [e4]; rfl, e5, st_mu, st_ks, mu_ks,
        by rw [hs1]; exact hL.nSP, by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_st hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_mu hL,
        by simp only [Proof.MlKem.AArch64.stk, hs1]; exact k_ks hL⟩
  refine call_tr (by decide) (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_correct v)
    (Proof.Sha3.AArch64.Stream.Squeeze.squeeze_ct v) (fun _ => []) (fun L => [⟨L.ST, 200⟩, ⟨L.MU, 64⟩, ⟨L.KS, 640⟩])
    (fun L g vv m₀ t t1 hL hc _ hm => (args L g vv m₀ t t1 hL hc hm).pre)
    (fun L g₁ g₂ v₁ v₂ m₁ m₂ a b a1 b1 hL _ c₁ c₂ _ _ f₁ f₂ => ?_) fun L _ _ _ _ hL _ _ => ?_
  · have x := args L g₁ v₁ m₁ a a1 hL c₁ f₁
    have y := args L g₂ v₂ m₂ b b1 hL c₂ f₂
    simp only [Proof.Sha3.squeezeAArch64, State.withRegions_sp, State.callEntry_sp,
      gpr_ce a1 (r := .x0), gpr_ce a1 (r := .x1), gpr_ce a1 (r := .x2), gpr_ce a1 (r := .x3),
      gpr_ce a1 (r := .x4), gpr_ce a1 (r := .x5), gpr_ce b1 (r := .x0), gpr_ce b1 (r := .x1),
      gpr_ce b1 (r := .x2), gpr_ce b1 (r := .x3), gpr_ce b1 (r := .x4), gpr_ce b1 (r := .x5),
      x.h0, x.h3, x.h5, y.h0, y.h3, y.h5, true_and]
    exact ⟨BitVec.eq_of_toNat_eq (x.h1.trans y.h1.symm), BitVec.eq_of_toNat_eq (x.h2.trans y.h2.symm),
      BitVec.eq_of_toNat_eq (x.h4.trans y.h4.symm), by rw [f₁.2.sp, f₂.2.sp, c₁.sp, c₂.sp]⟩
  · refine ⟨fun r hr => by simp at hr, fun r hr => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · have := cov_xw hL (e := 0) (k := 200) (by omega); rwa [x0] at this
    · exact cov_xw hL (e := 840) (by omega)
    · exact cov_xw hL (e := 200) (by omega)

/-! ## `μ` and `tr` -/

/-- The position after the context string. -/
abbrev qCtx (L : Lay) : Nat := (66 + L.ctxLen.toNat) % 136
/-- The position after the message. -/
abbrev qMsg (L : Lay) : Nat := (qCtx L + L.len.toNat) % 136

theorem muHash_tr (v : Proof.Sha3.AArch64.Permutation) {Φ : Lay → Mem → State → Prop} {tr : Arg}
    (hok : tr.ok = true) (hret : tr.isRet = false) (trp : Lay → Addr)
    (htr : ∀ (L : Lay) g vv m (t : State), Ctx L g vv m t → tr.val t = trp L)
    (hs : ∀ L : Lay, L.Ok → (∃ R ∈ L.rd ++ L.wr, Within ⟨trp L, 64⟩ R) ∧
      Region.Disjoint ⟨trp L, 64⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨trp L, 64⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨trp L, 64⟩) :
    RelCT isa (Two I Φ) (muHash v.callee tr) fun _ _ => True := by
  -- The relation keeps only the position in `x0`.
  let Ψ : (Lay → Nat) → Lay → Mem → State → Prop := fun q L _ t => (t.gpr .x0).toNat = q L
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun _ _ _ => True) zeroSt_tr
    fun L g vv m₀ t hL hc _ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have a1 := two_wp (I := I) (Ψ := Ψ fun _ => 64)
    (kabs_tr v (Φ := fun _ _ _ => True) (absOk hok rfl rfl hret rfl) trp (fun _ => 64)
      (fun _ => 0) (fun L g vv m t _ hc _ => ⟨htr L g vv m t hc, rfl, rfl⟩)
      fun L hL => ⟨by decide, by decide, (hs L hL).1, (hs L hL).2.1, (hs L hL).2.2.1, (hs L hL).2.2.2⟩)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d⟩ := hs L hL
      exact WP.mono (kabs_ok v hL hc (src := tr) (len := .imm 64) (pos := .imm 0) (n := 64) (q := 0)
        (absOk hok rfl rfl hret rfl) (htr L g vv m₀ t hc) rfl rfl (by decide)
        (by decide) a b c d) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have hdr : ∀ L : Lay, L.Ok → 64 < 136 ∧ 2 < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.X + BitVec.ofNat 64 984, 2⟩ R) ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.ST, 200⟩ ∧
      Region.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.X + BitVec.ofNat 64 984, 2⟩ := fun L hL =>
    ⟨by decide, by decide, cov_x hL (by omega),
      by have := Offset.disjoint L.X (d := 984) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
         simpa only [x0] using this,
      Offset.disjoint L.X (d := 984) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega),
      hL.stk_x (by omega)⟩
  have a2 := two_wp (I := I) (Φ := Ψ fun _ => 64) (Ψ := Ψ fun _ => 66)
    (kabs_tr v (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.X + BitVec.ofNat 64 984) (fun _ => 2) (fun _ => 64)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.off]; rfl, rfl, rfl⟩) hdr)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := hdr L hL
      exact WP.mono (kabs_ok v hL hc (src := .off oHdr) (len := .imm 2) (pos := .imm 64) (n := 2) (q := 64)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.off]; rfl) rfl rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have ctxS : ∀ L : Lay, L.Ok → 66 < 136 ∧ L.ctxLen.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.ctx, L.ctxLen.toNat⟩ R) ∧
      Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.ctx, L.ctxLen.toNat⟩ := fun L hL =>
    ⟨by decide, L.ctxLen.isLt, ⟨L.CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by decide)).symm, hL.kCtx⟩
  have a3 := two_wp (I := I) (Φ := Ψ fun _ => 66) (Ψ := Ψ qCtx)
    (kabs_tr v (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.ctx) (fun L => L.ctxLen.toNat) (fun _ => 66)
      (fun L g vv m t _ hc _ => ⟨by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl,
        by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega), ofNat_toNat_self]; rfl, rfl⟩) ctxS)
    fun L g vv m₀ t hL hc _ => by
      obtain ⟨a, b, c, d, e, f⟩ := ctxS L hL
      exact WP.mono (kabs_ok v hL hc (src := .slot fCtx) (len := .slot fCtxLen) (pos := .imm 66) (q := 66)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fCtx) (j := 3) rfl (by omega)]; rfl)
        (by rw [hc.slotV (f := fCtxLen) (j := 4) rfl (by omega), ofNat_toNat_self]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have msgS : ∀ L : Lay, L.Ok → qCtx L < 136 ∧ L.len.toNat < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.msg, L.len.toNat⟩ R) ∧
      Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.msg, L.len.toNat⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.msg, L.len.toNat⟩ := fun L hL =>
    ⟨Nat.mod_lt _ (by decide), L.len.isLt, ⟨L.MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by decide)).symm, hL.kMsg⟩
  have a4 := two_wp (I := I) (Φ := Ψ qCtx) (Ψ := Ψ qMsg)
    (kabs_tr v (src := .slot fMsg) (len := .slot fLen) (pos := .ret) (absOk rfl rfl rfl rfl rfl)
      (fun L => L.msg) (fun L => L.len.toNat) qCtx
      (fun L g vv m t _ hc hφ => ⟨by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl,
        by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega), ofNat_toNat_self]; rfl, ofNat_toNat_eq hφ⟩) msgS)
    fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := msgS L hL
      exact WP.mono (kabs_ok v hL hc (src := .slot fMsg) (len := .slot fLen) (pos := .ret)
        (absOk rfl rfl rfl rfl rfl) (by rw [hc.slotV (f := fMsg) (j := 1) rfl (by omega)]; rfl)
        (by rw [hc.slotV (f := fLen) (j := 2) rfl (by omega), ofNat_toNat_self]; rfl) (ofNat_toNat_eq hφ)
        a b c d e f) fun t' ⟨hc', _, _, hx⟩ => ⟨hc', hx⟩
  have pd := kpad_tr v (I := I) (Φ := Ψ qMsg) (pos := .ret) (padOk rfl) qMsg
    (fun L g vv m t _ _ hφ => ofNat_toNat_eq hφ) fun L _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := Ψ qMsg) (Ψ := fun _ _ _ => True) pd
    fun L g vv m₀ t hL hc hφ => WP.mono (kpad_ok v hL hc (pos := .ret) (padOk rfl) (ofNat_toNat_eq hφ)
      (Nat.mod_lt _ (by decide))) fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (a2.seq (a3.seq (a4.seq (pd'.seq (ksqz_tr v))))))

theorem trHash_tr (v : Proof.Sha3.AArch64.Permutation) {p : Params} (hk : p.pkLen < 2 ^ 16)
    {Φ : Lay → Mem → State → Prop} (hΦ : ∀ L m t, Φ L m t → L.keyLen = p.pkLen) :
    RelCT isa (Two I Φ) (trHash v.callee p) fun _ _ => True := by
  have keySide : ∀ L : Lay, L.Ok → 0 < 136 ∧ L.keyLen < 2 ^ 64 ∧
      (∃ R ∈ L.rd ++ L.wr, Within ⟨L.key, L.keyLen⟩ R) ∧
      Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.ST, 200⟩ ∧ Region.Disjoint ⟨L.key, L.keyLen⟩ ⟨L.KS, 640⟩ ∧
      L.STK.Disjoint ⟨L.key, L.keyLen⟩ := fun L hL =>
    ⟨by decide, by have := hL.hKey.2; omega, ⟨L.KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by decide); simpa only [x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by decide)).symm, hL.kKey⟩
  have z := two_wp (I := I) (Φ := Φ) (Ψ := fun L _ _ => L.keyLen = p.pkLen) zeroSt_tr
    fun L g vv m₀ t hL hc hφ => WP.mono (zeroSt_ok hL hc) fun t' ⟨hc', _⟩ => ⟨hc', hΦ L m₀ t hφ⟩
  have a1 := two_wp (I := I) (Φ := fun L _ _ => L.keyLen = p.pkLen) (Ψ := fun _ _ _ => True)
    (kabs_tr v (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
      (absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl) (fun L => L.key) (fun L => L.keyLen)
      (fun _ => 0) (fun L g vv m t _ hc hφ => ⟨by rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl,
        by rw [hφ]; rfl, rfl⟩) keySide)
    fun L g vv m₀ t hL hc hφ => by
      obtain ⟨a, b, c, d, e, f⟩ := keySide L hL
      exact WP.mono (kabs_ok v hL hc (src := .slot fKey) (len := .imm p.pkLen) (pos := .imm 0)
        (n := L.keyLen) (q := 0) (absOk rfl (by simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl)
        (by rw [hc.slotV (f := fKey) (j := 0) rfl (by omega)]; rfl) (by rw [hφ]; rfl) rfl a b c d e f)
        fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  have pd := kpad_tr v (I := I) (Φ := fun _ _ _ => True) (pos := .imm (p.pkLen % 136))
    (padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) (fun _ => p.pkLen % 136)
    (fun _ _ _ _ _ _ _ _ => rfl) fun _ _ => Nat.mod_lt _ (by decide)
  have pd' := two_wp (I := I) (Φ := fun _ _ _ => True) (Ψ := fun _ _ _ => True) pd
    fun L g vv m₀ t hL hc _ => WP.mono (kpad_ok v hL hc (pos := .imm (p.pkLen % 136))
      (padOk (by simp only [Arg.ok, decide_eq_true_eq]; omega)) rfl (Nat.mod_lt _ (by decide)))
      fun t' ⟨hc', _⟩ => ⟨hc', trivial⟩
  exact RelCT.seq z (a1.seq (pd'.seq (ksqz_tr v)))

end

end VG.Proof.MlDsa.AArch64.Message
