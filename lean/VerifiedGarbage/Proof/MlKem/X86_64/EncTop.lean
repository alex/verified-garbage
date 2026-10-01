import VerifiedGarbage.Proof.MlKem.X86_64.EncRest

/-!
# ML-KEM-768 on x86-64: K-PKE.Encrypt

Untrusted: everything here is checked by Lean. `encrypt`, from its inputs
and `r15 = 1`: `r15` is 1 exactly when every `SampleNTT` succeeded, and then
the ciphertext is `K-PKE.Encrypt(ek, m, r)` (`encrypt_ok`); for a given `ρ`,
it leaks the same in two runs (`encrypt_tr`). Every check of the pieces is
one Boolean (`encChk`), which the callers evaluate in their layouts.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr}

/-- Every check of `encrypt`. -/
def encChk (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  matChk bs wbs chk E && quadEChk bs wbs chk E 0 && quadEChk bs wbs chk E 4 && sampEChk bs wbs chk E 8 &&
    inKeep bs chk E [] &&
    (List.range 9).all (fun e => keepB bs [] (aS (e / 3) (e % 3)) 1024) && keepB bs [] (sc oSB) 32 &&
    (List.range 3).all (yChk bs wbs chk E) && (List.range 3).all (uChk bs wbs chk E) &&
    (List.range 3).all (tChk bs wbs chk E) && vChk bs wbs chk E

structure EncChks (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : matChk bs wbs chk E = true
  samp : SampChks bs wbs chk E
  inK : inKeep bs chk E [] = true
  aK : ∀ e < 9, keepB bs [] (aS (e / 3) (e % 3)) 1024 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  y : ∀ N < 3, yChk bs wbs chk E N = true
  u : ∀ i < 3, uChk bs wbs chk E i = true
  t : ∀ i < 3, tChk bs wbs chk E i = true
  v : vChk bs wbs chk E = true

theorem encChk_spec {bs wbs : List (Reg × Nat)} {chk : List (Ptr × Nat) → Bool} {E : Ptr} (h : encChk bs wbs chk E = true) :
    EncChks bs wbs chk E := by
  simp only [encChk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, q0⟩, q4⟩, s8⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, ⟨q0, q4, s8⟩, h3, h4, h5, h6, h7, h8, h9⟩

theorem rest_ok {C : Ctx rbs wbs} (hc : EncChks (rbs ++ wbs) wbs C.chk E) {a : Nat → Nat → Poly}
    {ek m r : List Byte} {s : State} (h : ER C E a ek m r 0 0 0 s) :
    WP isa (rest E) s fun s' => C.Out s' ∧ s'.gpr .r15 = 1 ∧
      bytesAt s'.mem (pa s' (sc oCT)) 1088 = ct768 a ek m r := by
  unfold rest
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E a ek m r k 0 0) 3 0
    (fun k _ hk s hs => WP.mono (y_ok (by omega) (hc.y k (by omega)) hs) fun _ h => h.2) s h) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E a ek m r 3 k 0) 3 0
    (fun k _ hk s hs => WP.mono (u_ok (by omega) (hc.u k (by omega)) hs) fun _ h => h.2) s₁ h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER C E a ek m r 3 3 k) 3 0
    (fun k _ hk s hs => WP.mono (t_ok (by omega) (hc.t k (by omega)) hs) fun _ h => h.2) s₂ h₂) fun s₃ h₃ => ?_)
  exact WP.mono (v_ok hc.v h₃) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, h15, hct⟩

theorem encrypt_ok (v : Sample4Impl) {C : Ctx rbs wbs} (hc : encChk (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : EIn C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (encrypt v.callee E) s (EOut C E ek m r) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine WP.seq (WP.mono (mat_ok v hc.mat hc.samp h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · have ho := KeyGen.r15_ne h₁.r15 hne
    exact WP.mono (rest_ok hc (ER.start (h₁.flag hP hc.inK hc.aK hc.sbK) ho)) fun _ ⟨hO, h15, hct⟩ =>
      ⟨hO, by rw [h15, ifp ho], fun _ => hct⟩
  · have h₂ := h₁.flag hP hc.inK hc.aK hc.sbK
    exact ⟨h₂.i.out, h₂.r15, fun ho => absurd ho (KeyGen.r15_eq h₁.r15 he)⟩

theorem rest_tr {C : Ctx rbs wbs} (hc : EncChks (rbs ++ wbs) wbs C.chk E) {P : (Nat → Nat → Poly) → List Byte → Prop} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ERP C E P 0 0 0 x ∧ ERP C E P 0 0 0 y) (rest E)
      (fun x y => LRel rbs wbs x y ∧ EOP C P x ∧ EOP C P y) := by
  unfold rest
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERP C E P k 0 0 x ∧ ERP C E P k 0 0 y) 3 0
    fun k _ hk => y_tr (by omega) (hc.y k (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERP C E P 3 k 0 x ∧ ERP C E P 3 k 0 y) 3 0
    fun k _ hk => u_tr (by omega) (hc.u k (by omega))) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERP C E P 3 3 k x ∧ ERP C E P 3 3 k y) 3 0
    fun k _ hk => t_tr (by omega) (hc.t k (by omega))) ?_
  exact v_tr hc.v

theorem encrypt_tr (v : Sample4Impl) {C : Ctx rbs wbs} (hc : encChk (rbs ++ wbs) wbs C.chk E = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 1152) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ C E ρ x ∧ EIρ C E ρ y) (encrypt v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ C E ρ x ∧ EOρ C E ρ y) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine RelCT.seq (mat_tr v hc.mat hc.samp ht) (ifOk_tr (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by
    rw [h₁.r15, h₂.r15, e₁, e₂]) (RelCT.mono (rest_tr hc (P := fun a ek => rhoE ek = ρ ∧ allOk ρ 9 ∧ a = aHat ρ)) ?_
      fun _ _ ⟨hl, ⟨_, ek₁, m₁, r₁, ⟨e₁, o₁, a₁⟩, h₁⟩, ⟨_, ek₂, m₂, r₂, ⟨e₂, o₂, a₂⟩, h₂⟩⟩ =>
        ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁.1, by rw [h₁.2.1, e₁, ifp o₁], fun _ => by rw [h₁.2.2, a₁, e₁]⟩,
          ⟨ek₂, m₂, r₂, e₂, h₂.1, by rw [h₂.2.1, e₂, ifp o₂], fun _ => by rw [h₂.2.2, a₂, e₂]⟩⟩) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.r15 hne
    have o₂ : allOk (rhoE ek₂) 9 := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b,
      ⟨_, ek₁, m₁, r₁, ⟨e₁, by rw [← e₁]; exact o₁, by rw [e₁]⟩, ER.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
      ⟨_, ek₂, m₂, r₂, ⟨e₂, by rw [← e₂]; exact o₂, by rw [e₂]⟩, ER.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.r15 he
    have o₂ : ¬ allOk (rhoE ek₂) 9 := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc.inK hc.aK hc.sbK
    have k₂ := h₂.flag hy hc.inK hc.aK hc.sbK
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.r15, fun h => absurd h o₂⟩⟩

end Enc

end VG.Proof.MlKem.X86_64
