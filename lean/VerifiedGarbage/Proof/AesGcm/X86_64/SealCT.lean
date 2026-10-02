import VerifiedGarbage.Proof.AesGcm.X86_64.OneCT

/-!
# AES-GCM on x86-64: `vg_aes_gcm_seal` is constant time

Untrusted: everything here is checked by Lean. After the entry, which loads
`work` from the stack first, both runs go through the same pieces with the
same public data (`oneAad_rel`, `oneCrypt_rel`, `oneTag_rel`).
-/

namespace VG.Proof.AesGcm.X86_64

open VG VG.X86_64 VG.X86_64.RegUpd VG.Impl.AesGcm.X86_64
open VG.Spec.Gcm (Block blockAt)

/-- What the entry of `seal` and `open` leaves, for `oneAad`. -/
def OneIn (s₀ : State) (k : Nat) (s : State) : Prop :=
  OneS (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .r8) (s₀.gpr .r9).toNat
      (stackArg s₀ 0) (stackArg s₀ 1).toNat s ∧ s.gpr .r12 = s₀.gpr .rdx ∧
    s.gpr .rbp = BitVec.ofNat 64 (s₀.gpr .rcx).toNat ∧
    DataOk (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) (s₀.gpr .rsp) s (s₀.gpr .rdx) (s₀.gpr .rcx).toNat ∧
    k = k

theorem OneEntry.oneIn {k : Nat} {s₀ s : State}
    (C : OneCtx s₀ k (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rdx) (s₀.gpr .r8) (stackArg s₀ 0)
      (s₀.gpr .rcx).toNat (s₀.gpr .r9).toNat (stackArg s₀ 1).toNat)
    (E : OneEntry s₀ (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .r8) (stackArg s₀ 0) (stackArg s₀ 1).toNat s) :
    OneIn s₀ k s :=
  ⟨⟨E.env, E.rounds, E.aad, by rw [E.alen, BitVec.ofNat_toNat, BitVec.setWidth_eq], E.dat, E.len,
    C.aad.of_eq E.rd E.wr, C.data.of_eq E.rd E.wr⟩, E.r12, by rw [E.rbp, BitVec.ofNat_toNat, BitVec.setWidth_eq],
    C.nonce.of_eq E.rd E.wr, rfl⟩

theorem one_pub {k : Nat} {s₀ s₀' : State} (hq : Proof.AesGcm.onePub k s₀ s₀') :
    ∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₀.gpr r = s₀'.gpr r := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, -⟩ := hq
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

theorem oneIn_pub {k : Nat} (hk : 3 ≤ k) {s₀ s₀' : State} (hq : Proof.AesGcm.onePub k s₀ s₀') {s : State}
    (h : OneIn s₀' k s) : OneIn s₀ k s := by
  obtain ⟨q₁, q₂, q₃, q₄, q₅, q₆, q₇, qa⟩ := hq
  have a₀ := qa 0 (by omega); have a₁ := qa 1 (by omega); have a₂ := qa 2 (by omega)
  simp only [Proof.AesGcm.arg] at a₀ a₁ a₂
  unfold OneIn
  rw [q₁, q₂, q₃, q₄, q₅, q₆, q₇, a₀, a₁, a₂]
  exact h

theorem seal_rel (v : GcmImpl) {s₀ s₀' : State} (hp : Proof.AesGcm.sealX86_64.pre s₀)
    (hp' : Proof.AesGcm.sealX86_64.pre s₀') (hq : Proof.AesGcm.sealX86_64.pub s₀ s₀') :
    RelCT isa (fun s₁ s₂ => s₁ = s₀ ∧ s₂ = s₀') («seal» v.callees) fun _ _ => True := by
  have C := OneCtx.of hp
  have C' := OneCtx.of hp'
  have L := C.lay
  have hE : ∀ {s : State} (hp : Proof.AesGcm.sealX86_64.pre s), WP isa (.block oneEntry) s (OneIn s 3) := fun hp =>
    WP.mono (oneEntry_ok le_rfl (OneCtx.of hp) rfl rfl rfl rfl rfl rfl) fun _ E => E.oneIn (OneCtx.of hp)
  have hE₁ := hE hp
  have hE₂ := WP.mono (hE hp') fun _ h => oneIn_pub le_rfl hq h
  have hw : stackArg s₀ 2 = stackArg s₀' 2 := hq.2.2.2.2.2.2.2 2 (by decide)
  rw [oneEntry, List.append_assoc, List.append_assoc, List.append_assoc] at hE₁ hE₂
  rw [«seal», oneEntry, List.append_assoc, List.append_assoc, List.append_assoc]
  have ha₂ := C.args 2 (by decide); have ha₂' := C'.args 2 (by decide)
  refine rel_reassoc_inner3 (fn_rel₂ (Ctx := s₀.gpr .rdi) (St := stackArg s₀ 2 + BitVec.ofNat 64 16)
    (W := stackArg s₀ 2) (SP := s₀.gpr .rsp) (k := 24) [.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp] (by simp)
    ⟨_, by taint_decide⟩ (one_pub hq) hw (by simpa [hp.2.2.1] using ha₂) (by simpa using ha₂')
    ⟨_, by taint_decide⟩ hE₁ hE₂ ?_)
  have hDW := C.dE
  have a := (oneAad_rel v L hDW).mono (P' := fun (s₁ s₂ : State) => True ∧ OneIn s₀ 3 s₁ ∧ OneIn s₀ 3 s₂)
    (fun _ _ h => ⟨⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1⟩,
    ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩⟩) fun _ _ h => h
  have hT : ∀ s, OneS (s₀.gpr .rdi) (stackArg s₀ 2) (s₀.gpr .rsp) (s₀.gpr .rsi).toNat (s₀.gpr .r8) (s₀.gpr .r9).toNat
      (stackArg s₀ 0) (stackArg s₀ 1).toNat s → WP isa (oneTag v.callees 0) s
        (Env (s₀.gpr .rdi) (stackArg s₀ 2 + BitVec.ofNat 64 16) (stackArg s₀ 2) (s₀.gpr .rsp)) := fun s h =>
    WP.mono (oneTag_ok v L (.inl rfl) (a := List.replicate (s₀.gpr .r9).toNat 0) h.env rfl h.rounds h.dat h.len h.alen
      (by simp) h.dD.ok hDW h.dD.ctx) fun _ o => o.1
  have t := rel_wp (oneTag_rel v L (.inl rfl) hDW) (fun _ _ h => h) hT hT
  exact RelCT.seq a (RelCT.seq (oneCrypt_rel v L hDW) (t.mono (fun _ _ h => h) fun _ _ h => h.2))

theorem seal_ct (v : GcmImpl) :
    ConstantTime isa Proof.AesGcm.sealX86_64.pre Proof.AesGcm.sealX86_64.pub («seal» v.callees) :=
  ct_of_rel fun _ _ hp hp' hq => seal_rel v hp hp' hq

end VG.Proof.AesGcm.X86_64
