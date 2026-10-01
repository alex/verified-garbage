import VerifiedGarbage.Proof.MlKem1024.X86_64.EncRest

/-!
# ML-KEM-1024 on x86-64: K-PKE.Encrypt

Untrusted: everything here is checked by Lean. `encrypt1024`, from its inputs
and `r15 = 1`: `r15` is 1 exactly when every `SampleNTT` succeeded, and then
the ciphertext is `K-PKE.Encrypt(ek, m, r)` (`encrypt_ok`); for a given `ρ`,
it leaks the same in two runs (`encrypt_tr`). Every check of the pieces is
one Boolean (`encChk`), which the callers evaluate in their layouts.
-/

namespace VG.Proof.MlKem1024.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64 VG.Impl.MlKem1024.X86_64
open VG.Proof.MlKem VG.Proof.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc4

open VG.Impl.MlKem1024.X86_64.Encrypt1024

variable {rbs wbs : List (Reg × Nat)} {E : Ptr}

/-- Every check of `encrypt`. -/
def encChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  matChk bs wbs chk E && quadEChk bs wbs chk E 0 && quadEChk bs wbs chk E 4 && quadEChk bs wbs chk E 8 &&
    quadEChk bs wbs chk E 12 && inKeep bs chk E [] && prfsEChk bs wbs chk E &&
    (List.range 16).all (fun e => keepB bs [] (aS4 (e / 4) (e % 4)) 1024) && keepB bs [] (sc oSB) 32 &&
    (List.range 4).all (yChk bs wbs chk E) && (List.range 4).all (uChk bs wbs chk E) &&
    (List.range 4).all (tChk bs wbs chk E) && vChk bs wbs chk E

structure EncChks (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : matChk bs wbs chk E = true
  samp : SampChks bs wbs chk E
  inK : inKeep bs chk E [] = true
  prfs : prfsEChk bs wbs chk E = true
  aK : ∀ e < 16, keepB bs [] (aS4 (e / 4) (e % 4)) 1024 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  y : ∀ N < 4, yChk bs wbs chk E N = true
  u : ∀ i < 4, uChk bs wbs chk E i = true
  t : ∀ i < 4, tChk bs wbs chk E i = true
  v : vChk bs wbs chk E = true

theorem encChk_spec {bs wbs : List (Reg × Nat)} {chk : List (Ptr × Nat) → Bool} {E : Ptr} (h : encChk bs wbs chk E = true) :
    EncChks bs wbs chk E := by
  simp only [encChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, q0⟩, q4⟩, q8⟩, q12⟩, h3⟩, hp⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, ⟨q0, q4, q8, q12⟩, h3, hp, h4, h5, h6, h7, h8, h9⟩

theorem rest_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hc : EncChks (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte}
    {s : State} (h : ER0 C E ek m r s) : WP isa (rest v.callee E) s (EOut C E ek m r) := by
  unfold rest
  refine WP.seq (WP.mono (prfsE_ok v hc.prfs h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E ek m r k 0 0) 4 0
    (fun k _ hk s hs => WP.mono (y_ok (by omega) (hc.y k (by omega)) hs) fun _ h => h.2) s₀ h₀.2) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E ek m r 4 k 0) 4 0
    (fun k _ hk s hs => WP.mono (u_ok (by omega) (hc.u k (by omega)) hs) fun _ h => h.2) s₁ h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E ek m r 4 4 k) 4 0
    (fun k _ hk s hs => WP.mono (t_ok (by omega) (hc.t k (by omega)) hs) fun _ h => h.2) s₂ h₂) fun s₃ h₃ => ?_)
  exact WP.mono (v_ok hc.v h₃) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, by rw [h15, ifp h₃.ok], fun _ => hct⟩

theorem encrypt_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hc : encChk (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : EIn C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (encrypt1024 v.callee E) s (EOut C E ek m r) := by
  have hc := encChk_spec hc
  unfold encrypt1024
  refine WP.seq (WP.mono (mat_ok v hc.mat hc.samp h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · exact rest_ok v hc (ER0.start (h₁.flag hP hc.inK hc.aK hc.sbK) (KeyGen4.r15_ne h₁.r15 hne))
  · have h₂ := h₁.flag hP hc.inK hc.aK hc.sbK
    exact ⟨h₂.i.out, h₂.r15, fun ho => absurd ho (KeyGen4.r15_eq h₁.r15 he)⟩

theorem rest_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hc : EncChks (rbs ++ wbs) wbs C.chk E) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ C E ρ x ∧ ER0ρ C E ρ y) (rest v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ C E ρ x ∧ EOρ C E ρ y) := by
  unfold rest
  refine RelCT.seq (prfsE_tr v hc.prfs) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ C E ρ k 0 0 x ∧ ERρ C E ρ k 0 0 y) 4 0
    fun k _ hk => y_tr (by omega) (hc.y k (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ C E ρ 4 k 0 x ∧ ERρ C E ρ 4 k 0 y) 4 0
    fun k _ hk => u_tr (by omega) (hc.u k (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ C E ρ 4 4 k x ∧ ERρ C E ρ 4 4 k y) 4 0
    fun k _ hk => t_tr (by omega) (hc.t k (by omega))) ?_
  exact v_tr hc.v

theorem encrypt_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hc : encChk (rbs ++ wbs) wbs C.chk E = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 1536) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ C E ρ x ∧ EIρ C E ρ y) (encrypt1024 v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ C E ρ x ∧ EOρ C E ρ y) := by
  have hc := encChk_spec hc
  unfold encrypt1024
  refine RelCT.seq (mat_tr v hc.mat hc.samp ht) (ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by
    rw [h₁.r15, h₂.r15, e₁, e₂]) (RelCT.mono (rest_tr v hc) ?_ fun _ _ h => h) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen4.r15_ne h₁.r15 hne
    have o₂ : allOk4 (rhoE ek₂) 16 := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, ER0.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, ER0.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen4.r15_eq h₁.r15 he
    have o₂ : ¬ allOk4 (rhoE ek₂) 16 := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc.inK hc.aK hc.sbK
    have k₂ := h₂.flag hy hc.inK hc.aK hc.sbK
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.r15, fun h => absurd h o₂⟩⟩

end Enc4

end VG.Proof.MlKem1024.X86_64
