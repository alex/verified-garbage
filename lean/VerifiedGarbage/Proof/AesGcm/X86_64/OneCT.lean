import VerifiedGarbage.Proof.AesGcm.X86_64.Seal
import VerifiedGarbage.Proof.AesGcm.X86_64.StreamCryptCT

/-!
# AES-GCM on x86-64: the pieces of `seal` and `open` in two runs

Untrusted: everything here is checked by Lean. What stays in `W` between
the pieces (`OneS`: the rounds, the additional data's address and length,
the data's address and length) is the same in both runs, so each piece
(`oneAad`, `oneCrypt`, `oneTag`) leaks the same, by the fragments'
relations.
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- What stays in `W` and the buffers between the pieces of `seal` and `open`. -/
structure OneS (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s : State) :
    Prop where
  env : Env Ctx (W + BitVec.ofNat 64 16) W SP s
  rounds : RoundsAt s.mem W R
  aad : s.mem.readW (W + BitVec.ofNat 64 232) 64 = A
  alen : s.mem.readW (W + BitVec.ofNat 64 184) 64 = BitVec.ofNat 64 al
  dat : s.mem.readW (W + BitVec.ofNat 64 200) 64 = D
  len : s.mem.readW (W + BitVec.ofNat 64 208) 64 = BitVec.ofNat 64 n
  dA : DataOk (W + BitVec.ofNat 64 16) W SP s A al
  dD : DataW Ctx (W + BitVec.ofNat 64 16) W SP s D n
  /-- The total length, once `oneBlocks` has kept it. -/
  tlen : ∀ N, T = some N → s.mem.readW (W + BitVec.ofNat 64 192) 64 = BitVec.ofNat 64 N

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

theorem OneS.frame {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : OneS Ctx W SP R A al D n T s) (he : Env Ctx (W + BitVec.ofNat 64 16) W SP s') (hrd : s'.rd = s.rd)
    (hwr : s'.wr = s.wr) (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩)
    (hf : Frame (oneFrame W D SP n) s.mem s'.mem) : OneS Ctx W SP R A al D n T s' := by
  have kp : ∀ d, (128 ≤ d ∧ d + 8 ≤ 216) ∨ (224 ≤ d ∧ d + 8 ≤ 240) →
      s'.mem.readW (W + BitVec.ofNat 64 d) 64 = s.mem.readW (W + BitVec.ofNat 64 d) 64 :=
    fun d hd => hf.readW (r := ⟨W + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (kept_oneFrame L hDW hd)
      (by decide)
  exact ⟨he, ⟨by rw [kp 176 (.inl ⟨by decide, by decide⟩)]; exact h.rounds.1, h.rounds.2⟩,
    by rw [kp 232 (.inr ⟨by decide, by decide⟩)]; exact h.aad, by rw [kp 184 (.inl ⟨by decide, by decide⟩)]; exact h.alen,
    by rw [kp 200 (.inl ⟨by decide, by decide⟩)]; exact h.dat, by rw [kp 208 (.inl ⟨by decide, by decide⟩)]; exact h.len,
    h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr, fun N hN => by rw [kp 192 (.inl ⟨by decide, by decide⟩)]; exact h.tlen N hN⟩

omit L in
theorem OneS.keep {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s s' : State}
    (h : OneS Ctx W SP R A al D n T s) (hg : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s'.gpr r = s.gpr r)
    (hm : s'.mem = s.mem) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : OneS Ctx W SP R A al D n T s' :=
  ⟨h.env.keep hg hrd hwr, by rw [hm]; exact h.rounds, by rw [hm]; exact h.aad, by rw [hm]; exact h.alen,
    by rw [hm]; exact h.dat, by rw [hm]; exact h.len, h.dA.of_eq hrd hwr, h.dD.of_eq hrd hwr,
    fun N hN => by rw [hm]; exact h.tlen N hN⟩

omit L in
/-- Two slots of `W` loaded, and a constant. -/
theorem load2_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s : State}
    (h : OneS Ctx W SP R A al D n T s) {o₁ o₂ : Nat} {P : Addr} {k : Nat}
    (h₁ : s.mem.readW (W + BitVec.ofNat 64 o₁) 64 = P) (h₂ : s.mem.readW (W + BitVec.ofNat 64 o₂) 64 = BitVec.ofNat 64 k)
    (q₁ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₁) 8) (q₂ : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o₂) 8) :
    WP isa (.block [.mov .r12 (.mem (at_ .r15 o₁)), .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)]) s
      fun s₁ => OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = P ∧ s₁.gpr .rbp = BitVec.ofNat 64 k ∧
        s₁.gpr .rbx = BitVec.ofNat 64 0 := by
  have h15 := h.env.r15
  obtain ⟨s₁, run₁, h12, hbp, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .r12 (.mem (at_ .r15 o₁)),
      .mov .rbp (.mem (at_ .r15 o₂)), .mov32 .rbx (imm 0)] s = some s₁ ∧ s₁.gpr .r12 = P ∧
      s₁.gpr .rbp = BitVec.ofNat 64 k ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .r12 → r ≠ .rbp → r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧
      s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [gpr_setReg, h₁]
    · simp [gpr_setReg, h₂]
    · simp [gpr_setReg]
    · intro r a b c; simp [gpr_setReg, a, b, c]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, h12, hbp, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide) (by decide)

omit L in
/-- A length's slot, modulo 16, into `rbx`. -/
theorem mod16_ok {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s : State}
    (h : OneS Ctx W SP R A al D n T s) {o : Nat} {k : Nat} (ho : (o = alenO ∧ k = al) ∨ (o = lenO ∧ k = n)) :
    WP isa (.block [.mov .rbx (.mem (at_ .r15 o)), .alu .and .rbx (imm 15)]) s fun s₁ =>
      OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (k % 16) := by
  have he := h.env
  have hk : k < 2 ^ 64 := by rcases ho with ⟨-, rfl⟩ | ⟨-, rfl⟩; exacts [h.dA.lt, h.dD.ok.lt]
  have hand := and15 (BitVec.ofNat 64 k)
  rw [toNat_ofNat_of_lt hk, imm_eq (by decide)] at hand
  have hs : s.mem.readW (W + BitVec.ofNat 64 o) 64 = BitVec.ofNat 64 k := by
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩; exacts [h.alen, h.len]
  have ro : InRegions (s.rd ++ s.wr) (W + BitVec.ofNat 64 o) 8 := by
    rcases ho with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact he.perm.wR (show 184 + 8 ≤ 2560 by decide)
    · exact he.perm.wR (show 208 + 8 ≤ 2560 by decide)
  have h15 := he.r15
  obtain ⟨s₁, run₁, hbx, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 o)),
      .alu .and .rbx (imm 15)] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (k % 16) ∧
      (∀ r, r ≠ .rbx → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    refine ⟨_, by xrun [h15, ro], ?_, ?_, ?_, ?_, ?_⟩
    · simp only [gpr_setReg, gpr_arithFlags, ite_true, hs, hand]
    · intro r a; simp [gpr_setReg, a]
    all_goals rfl
  refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide)

end

section
variable (v : GcmImpl) {Ctx W SP : Addr} (L : Lay Ctx (W + BitVec.ofNat 64 16) W SP)
include L

omit L in
theorem w_one {D : Addr} {n : Nat} {m m' : Mem} (h : Frame (wFrame W SP) m m') : Frame (oneFrame W D SP n) m m' :=
  wFrame_one (o := 0) (.inl rfl) (wFrame_cons h)

/-- Two runs in `OneS` for the same parameters. -/
abbrev OneS₂ (Ctx W SP : Addr) (R : Nat) (A : Addr) (al : Nat) (D : Addr) (n : Nat) (T : Option Nat) (s₁ s₂ : State) :
    Prop :=
  OneS Ctx W SP R A al D n T s₁ ∧ OneS Ctx W SP R A al D n T s₂

omit L in
theorem OneS₂.env {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} {s₁ s₂ : State}
    (h : OneS₂ Ctx W SP R A al D n T s₁ s₂) : ∀ r ∈ [Reg.r13, .r14, .r15, .rsp], s₁.gpr r = s₂.gpr r :=
  env_agree h.1.env h.2.env

/-- The additional data, absorbed and padded. -/
theorem aadRest_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat} (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP R A al D n T)
      (.seq (.block [.mov .r12 (.mem (at_ .r15 aadO)), .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)])
      (.seq (absorb v.callees 16) (.seq (.block [.mov .rbx (.mem (at_ .r15 alenO)), .alu .and .rbx (imm 15)])
        (flush v.callees 16)))) (OneS₂ Ctx W SP R A al D n T) := by
  have hL : ∀ s, OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 aadO)),
      .mov .rbp (.mem (at_ .r15 alenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = A ∧ s₁.gpr .rbp = BitVec.ofNat 64 al ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.aad h.alen (h.env.perm.wR (show 232 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 184 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = A ∧
    s.gpr .rbp = BitVec.ofNat 64 al ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] A al s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dA, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorb v.callees 16) s (OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (absorb_ok v L (.inr rfl) (ai s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (absFrame_one o.frame))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := A) (n := al) rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  have hM : ∀ s, OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .alu .and .rbx (imm 15)]) s fun s₁ => OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (al % 16) :=
    fun s h => mod16_ok h (.inl ⟨rfl, rfl⟩)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ OneS₂ Ctx W SP R A al D n T s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hM hM
  have hF : ∀ s, OneS Ctx W SP R A al D n T s ∧ s.gpr .rbx = BitVec.ofNat 64 (al % 16) →
      WP isa (flush v.callees 16) s (OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (x := List.replicate al 0) ⟨h.1.env, rfl⟩
      (by simpa using h.2))) fun _ ⟨o, hrd, hwr⟩ => h.1.frame L o.env hrd hwr hDW (w_one (tFrame_one o.frame))
  have d := rel_wp ((flush_rel v L (.inr rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (al % 16)) ∧
      (OneS Ctx W SP R A al D n T s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (al % 16)))
      (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  exact (RelCT.seq a (RelCT.seq b (RelCT.seq c d))).mono (fun _ _ h => h) fun _ _ h => h.2

/-- `J₀` of the nonce, and the additional data. -/
theorem oneAad_rel {R : Nat} {Np A : Addr} {nl al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (fun s₁ s₂ => (OneS Ctx W SP R A al D n T s₁ ∧ s₁.gpr .r12 = Np ∧ s₁.gpr .rbp = BitVec.ofNat 64 nl ∧
        DataOk (W + BitVec.ofNat 64 16) W SP s₁ Np nl) ∧ (OneS Ctx W SP R A al D n T s₂ ∧ s₂.gpr .r12 = Np ∧
        s₂.gpr .rbp = BitVec.ofNat 64 nl ∧ DataOk (W + BitVec.ofNat 64 16) W SP s₂ Np nl))
      (oneAad v.callees) (OneS₂ Ctx W SP R A al D n T) := by
  have ji : ∀ s, (OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) →
      J0In Ctx (W + BitVec.ofNat 64 16) W SP (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) Np nl s :=
    fun s h => ⟨h.1.env, rfl, h.2.1, h.2.2.1, h.2.2.2⟩
  have hJ : ∀ s, (OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = Np ∧ s.gpr .rbp = BitVec.ofNat 64 nl ∧
      DataOk (W + BitVec.ofNat 64 16) W SP s Np nl) → WP isa (j0 v.callees) s (OneS Ctx W SP R A al D n T) :=
    fun s h => WP.mono (WP.with_rdwr (j0_ok v L (ji s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (j0Frame_one o.frame))
  have a := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      j0_rel v L (H₁ := H₁) (H₂ := H₂) (Np := Np) (n := nl)).mono
      (fun _ _ h => ⟨_, _, ji _ h.1, ji _ h.2⟩) fun _ _ h => h) (fun _ _ h => h) hJ hJ
  exact RelCT.seq a ((aadRest_rel v L hDW).mono (fun _ _ h => h.2) fun _ _ h => h)

/-- The data encrypted or decrypted. -/
theorem oneCrypt_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {T : Option Nat}
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP R A al D n T) (oneCrypt v.callees) (OneS₂ Ctx W SP R A al D n T) := by
  have hL : ∀ s, OneS Ctx W SP R A al D n T s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP R A al D n T s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let CI : State → Prop := fun s => OneS Ctx W SP R A al D n T s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ci : ∀ s, CI s → CrIn Ctx (W + BitVec.ofNat 64 16) W SP R 0 0 D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD, h.1.rounds⟩
  have hC : ∀ s, CI s → WP isa (crypt v.callees) s (OneS Ctx W SP R A al D n T) := fun s h =>
    WP.mono (WP.with_rdwr (crypt_ok v L (ci s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (crFrame_one o.frame)
  have b := rel_wp ((crypt_rel v L (R := R) (icb₁ := 0) (icb₂ := 0) (P₁ := 0) (P₂ := 0) (D := D) (n := n) rfl).mono
      (P' := fun s₁ s₂ => True ∧ CI s₁ ∧ CI s₂) (fun _ _ h => ⟨ci _ h.2.1, ci _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hC hC
  exact (RelCT.seq a b).mono (fun _ _ h => h) fun _ _ h => h.2

/-- The tag of the data (as ciphertext) into `W + o`. -/
theorem oneTag_rel {R : Nat} {A : Addr} {al : Nat} {D : Addr} {n : Nat} {N : Nat} {o : Nat} (ho : o = 0 ∨ o = 112)
    (hDW : (⟨D, n⟩ : Region).Disjoint ⟨W, 2560⟩) :
    RelCT isa (OneS₂ Ctx W SP R A al D n (some N)) (oneTag v.callees o) fun _ _ => True := by
  have hL : ∀ s, OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .r12 (.mem (at_ .r15 dataO)),
      .mov .rbp (.mem (at_ .r15 lenO)), .mov32 .rbx (imm 0)]) s fun s₁ => OneS Ctx W SP R A al D n (some N) s₁ ∧
      s₁.gpr .r12 = D ∧ s₁.gpr .rbp = BitVec.ofNat 64 n ∧ s₁.gpr .rbx = BitVec.ofNat 64 0 := fun s h =>
    load2_ok h h.dat h.len (h.env.perm.wR (show 200 + 8 ≤ 2560 by decide)) (h.env.perm.wR (show 208 + 8 ≤ 2560 by decide))
  have a := rel_wp (rel_taint [.r13, .r14, .r15, .rsp] (fun _ _ h => OneS₂.env h) ⟨_, by taint_decide⟩)
    (fun _ _ h => h) hL hL
  let AI : State → Prop := fun s => OneS Ctx W SP R A al D n (some N) s ∧ s.gpr .r12 = D ∧
    s.gpr .rbp = BitVec.ofNat 64 n ∧ s.gpr .rbx = BitVec.ofNat 64 0
  have ai : ∀ s, AI s → AbsIn Ctx (W + BitVec.ofNat 64 16) W SP 16 (blockAt s.mem (Ctx + BitVec.ofNat 64 240)) [] D n s :=
    fun s h => ⟨h.1.env, h.2.1, h.2.2.1, h.2.2.2, h.1.dD.ok, rfl⟩
  have hA : ∀ s, AI s → WP isa (absorb v.callees 16) s (OneS Ctx W SP R A al D n (some N)) := fun s h =>
    WP.mono (WP.with_rdwr (absorb_ok v L (.inr rfl) (ai s h))) fun _ ⟨o, hrd, hwr⟩ =>
      h.1.frame L o.env hrd hwr hDW (w_one (absFrame_one o.frame))
  have b := rel_wp ((RelCT.exists_ fun H₁ => RelCT.exists_ fun H₂ =>
      absorb_rel v L (.inr rfl) (H₁ := H₁) (H₂ := H₂) (x₁ := []) (x₂ := []) (D := D) (n := n) rfl).mono
      (P' := fun s₁ s₂ => True ∧ AI s₁ ∧ AI s₂) (fun _ _ h => ⟨_, _, ai _ h.2.1, ai _ h.2.2⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hA hA
  have hM : ∀ s, OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .rbx (.mem (at_ .r15 lenO)),
      .alu .and .rbx (imm 15)]) s fun s₁ => OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16) :=
    fun s h => mod16_ok h (.inr ⟨rfl, rfl⟩)
  have c := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ OneS₂ Ctx W SP R A al D n (some N) s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hM hM
  have hF : ∀ s, OneS Ctx W SP R A al D n (some N) s ∧ s.gpr .rbx = BitVec.ofNat 64 (n % 16) →
      WP isa (flush v.callees 16) s (OneS Ctx W SP R A al D n (some N)) := fun s h =>
    WP.mono (WP.with_rdwr (flush_ok v L (yo := 16) (.inr rfl) (x := List.replicate n 0) ⟨h.1.env, rfl⟩
      (by simpa using h.2))) fun _ ⟨o, hrd, hwr⟩ => h.1.frame L o.env hrd hwr hDW (w_one (tFrame_one o.frame))
  have d := rel_wp ((flush_rel v L (.inr rfl)).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 (n % 16)) ∧
      (OneS Ctx W SP R A al D n (some N) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 (n % 16)))
      (fun _ _ h => ⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; rw [h.2.1.2, h.2.2.2]⟩) fun _ _ h => h)
    (fun _ _ h => h.2) hF hF
  -- The lengths, for `tag`.
  have hT : ∀ s, OneS Ctx W SP R A al D n (some N) s → WP isa (.block [.mov .rbx (.mem (at_ .r15 alenO)),
      .mov .rbp (.mem (at_ .r15 tlenO))]) s fun s₁ => OneS Ctx W SP R A al D n (some N) s₁ ∧
      s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N := fun s h => by
    have q₁ := h.env.perm.wR (show 184 + 8 ≤ 2560 by decide)
    have q₂ := h.env.perm.wR (show 192 + 8 ≤ 2560 by decide)
    have h15 := h.env.r15
    obtain ⟨s₁, run₁, hbx, hbp, hg₁, hm₁, hrd₁, hwr₁⟩ : ∃ s₁, runBlock isa [.mov .rbx (.mem (at_ .r15 alenO)),
        .mov .rbp (.mem (at_ .r15 tlenO))] s = some s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧
        s₁.gpr .rbp = BitVec.ofNat 64 N ∧ (∀ r, r ≠ .rbx → r ≠ .rbp → s₁.gpr r = s.gpr r) ∧ s₁.mem = s.mem ∧
        s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      refine ⟨_, by xrun [h15, q₁, q₂], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [gpr_setReg, h.alen]
      · simp [gpr_setReg, h.tlen N rfl]
      · intro r a b; simp [gpr_setReg, a, b]
      all_goals rfl
    refine WP.of_runBlock ⟨s₁, run₁, h.keep (fun r hr => ?_) hm₁ hrd₁ hwr₁, hbx, hbp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hg₁ _ (by decide) (by decide)
  have e := rel_wp (rel_taint (P := fun s₁ s₂ => True ∧ OneS₂ Ctx W SP R A al D n (some N) s₁ s₂) [.r13, .r14, .r15, .rsp]
      (fun _ _ h => OneS₂.env h.2) ⟨_, by taint_decide⟩) (fun _ _ h => h.2) hT hT
  have t := (tag_rel v L (R := R) ho).mono (P' := fun (s₁ s₂ : State) => True ∧
      (OneS Ctx W SP R A al D n (some N) s₁ ∧ s₁.gpr .rbx = BitVec.ofNat 64 al ∧ s₁.gpr .rbp = BitVec.ofNat 64 N) ∧
      (OneS Ctx W SP R A al D n (some N) s₂ ∧ s₂.gpr .rbx = BitVec.ofNat 64 al ∧ s₂.gpr .rbp = BitVec.ofNat 64 N))
    (fun _ _ h => ⟨⟨h.2.1.1.env, h.2.2.1.env, fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [h.2.1.2.1, h.2.2.2.1]
      · rw [h.2.1.2.2, h.2.2.2.2]⟩, h.2.1.1.rounds, h.2.2.1.rounds⟩) fun _ _ h => h
  exact RelCT.seq a (RelCT.seq b (RelCT.seq c (RelCT.seq d (RelCT.seq e t))))

end

end VG.Proof.AesGcm.X86_64
