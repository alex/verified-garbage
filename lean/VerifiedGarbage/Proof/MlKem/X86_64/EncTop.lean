import VerifiedGarbage.Proof.MlKem.X86_64.EncRest

/-!
# ML-KEM on x86-64: K-PKE.Encrypt

`encrypt L`, from its inputs and `r15 = 1`: `r15` is 1 exactly when every
`SampleNTT` succeeded, and then the ciphertext is `K-PKE.Encrypt(ek, m, r)`
(`encrypt_ok`); for a given `ρ`, it leaks the same in two runs (`encrypt_tr`).
Every check of the pieces is one Boolean (`encChk`), which the callers
evaluate in their layouts, for each parameter set.
-/

namespace VG.Proof.MlKem.X86_64

open VG VG.X86_64 VG.Impl.MlKem.X86_64
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

namespace Enc

open VG.Impl.MlKem.X86_64.Encrypt

variable {rbs wbs : List (Reg × Nat)} {E : Ptr} {L : Kem}

/-- Every check of `encrypt`. -/
def encChk (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Bool :=
  matChk L bs wbs chk E && (List.range (L.k * L.k / 4)).all (fun q => quadEChk L bs wbs chk E (4 * q)) &&
    (List.range (L.k * L.k)).all (fun e => !decide (4 * (L.k * L.k / 4) ≤ e) || sampEChk L bs wbs chk E e) &&
    inKeep L bs chk E [] && prfsEChk L bs wbs chk E &&
    (List.range (L.k * L.k)).all (fun e => keepB bs [] (pS (L.pA + e)) 1024) && keepB bs [] (sc oSB) 32 &&
    (List.range L.k).all (yChk L bs wbs chk E) && (List.range L.k).all (uChk L bs wbs chk E) &&
    (List.range L.k).all (tChk L bs wbs chk E) && vChk L bs wbs chk E

structure EncChks (L : Kem) (bs wbs : List (Reg × Nat)) (chk : List (Ptr × Nat) → Bool) (E : Ptr) : Prop where
  mat : matChk L bs wbs chk E = true
  q : ∀ q < L.k * L.k / 4, quadEChk L bs wbs chk E (4 * q) = true
  s : ∀ e < L.k * L.k, 4 * (L.k * L.k / 4) ≤ e → sampEChk L bs wbs chk E e = true
  inK : inKeep L bs chk E [] = true
  prfs : prfsEChk L bs wbs chk E = true
  aK : ∀ e < L.k * L.k, keepB bs [] (pS (L.pA + e)) 1024 = true
  sbK : keepB bs [] (sc oSB) 32 = true
  y : ∀ N < L.k, yChk L bs wbs chk E N = true
  u : ∀ i < L.k, uChk L bs wbs chk E i = true
  t : ∀ i < L.k, tChk L bs wbs chk E i = true
  v : vChk L bs wbs chk E = true

theorem encChk_spec {bs wbs : List (Reg × Nat)} {chk : List (Ptr × Nat) → Bool} {E : Ptr}
    (h : encChk L bs wbs chk E = true) : EncChks L bs wbs chk E := by
  simp only [encChk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, hq⟩, hs⟩, h3⟩, hp⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, hq, fun e he he' => (hs e he).resolve_left (fun h => h he'), h3, hp, h4, h5, h6, h7, h8, h9⟩

theorem rest_ok (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4) {C : Ctx rbs wbs}
    (hc : EncChks L (rbs ++ wbs) wbs C.chk E) {ek m r : List Byte} {s : State} (h : ER0 L C E ek m r s) :
    WP isa (rest L v.callee E) s (EOut L C E ek m r) := by
  unfold rest
  refine WP.seq (WP.mono (prfsE_ok v hk.2 hc.prfs h) fun s₀ h₀ => ?_)
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER L C E ek m r k 0 0) L.k 0
    (fun k _ hk' s hs => WP.mono (y_ok v.arith (by omega) (hc.y k (by omega)) hs) fun _ h => h.2) s₀ h₀.2)
    fun s₁ h₁ => ?_)
  rw [Nat.zero_add] at h₁
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER L C E ek m r L.k k 0) L.k 0
    (fun k _ hk' s hs => WP.mono (u_ok v.arith K hk.1 (by omega) (hc.u k (by omega)) hs) fun _ h => h.2) s₁ h₁)
    fun s₂ h₂ => ?_)
  rw [Nat.zero_add] at h₂
  refine WP.seq (WP.mono (seqR_ok (I := fun k => ER L C E ek m r L.k L.k k) L.k 0
    (fun k _ hk' s hs => WP.mono (t_ok (by omega) (hc.t k (by omega)) hs) fun _ h => h.2) s₂ h₂) fun s₃ h₃ => ?_)
  rw [Nat.zero_add] at h₃
  exact WP.mono (v_ok v.arith K hk.1 hc.v h₃) fun _ ⟨_, ho, h15, hct⟩ => ⟨ho, by rw [h15, ifp h₃.ok], fun _ => hct⟩

theorem encrypt_ok (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4)
    {C : Ctx rbs wbs} (hc : encChk L (rbs ++ wbs) wbs C.chk E = true) {ek m r : List Byte} {s : State}
    (h : EIn L C E ek m r s) (h15 : s.gpr .r15 = 1) : WP isa (encrypt L v.callee E) s (EOut L C E ek m r) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine WP.seq (WP.mono (mat_ok v hk.2 hc.mat hc.q hc.s h h15) fun s₁ h₁ => ?_)
  refine ifOk_ok (fun s₂ hP hne => ?_) fun s₂ hP he => ?_
  · exact rest_ok v K hk hc (ER0.start (h₁.flag hP hc.inK hc.aK hc.sbK) (KeyGen.r15_ne h₁.m.r15 hne))
  · have h₂ := h₁.flag hP hc.inK hc.aK hc.sbK
    exact ⟨h₂.i.out, h₂.m.r15, fun ho => absurd ho (KeyGen.r15_eq h₁.m.r15 he)⟩

theorem rest_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (hk : 0 < L.k ∧ L.k ≤ 4)
    {C : Ctx rbs wbs} (hc : EncChks L (rbs ++ wbs) wbs C.chk E) {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ ER0ρ L C E ρ x ∧ ER0ρ L C E ρ y) (rest L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  unfold rest
  refine RelCT.seq (prfsE_tr v hk.2 hc.prfs) ?_
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ L C E ρ k 0 0 x ∧ ERρ L C E ρ k 0 0 y) L.k 0
    fun k _ hk' => y_tr v.arith (by omega) (hc.y k (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k k 0 x ∧ ERρ L C E ρ L.k k 0 y) L.k 0
    fun k _ hk' => u_tr v.arith K hk.1 (by omega) (hc.u k (by omega))) ?_
  rw [Nat.zero_add]
  refine RelCT.seq (seqR_tr (R := fun k x y => LRel rbs wbs x y ∧ ERρ L C E ρ L.k L.k k x ∧
    ERρ L C E ρ L.k L.k k y) L.k 0 fun k _ hk' => t_tr (by omega) (hc.t k (by omega))) ?_
  rw [Nat.zero_add]
  exact v_tr v.arith K hk.1 hc.v

theorem encrypt_tr (v : Sample4Impl) {wc wd : List Nat} (K : KemCalls L wc wd) (W : KemWf L) {C : Ctx rbs wbs}
    (hc : encChk L (rbs ++ wbs) wbs C.chk E = true) {h : VG.Taint.Hint X86_64.Taint.T}
    (ht : (taint.check (X86_64.Taint.ofRegs [.rbx, E.1]) (copy (sc oSB) (E.1, E.2 + 384 * L.k) 32) h).isSome = true)
    {ρ : List Byte} :
    RelCT isa (fun x y => LRel rbs wbs x y ∧ EIρ L C E ρ x ∧ EIρ L C E ρ y) (encrypt L v.callee E)
      (fun x y => LRel rbs wbs x y ∧ EOρ L C E ρ x ∧ EOρ L C E ρ y) := by
  have hc := encChk_spec hc
  unfold encrypt
  refine RelCT.seq (mat_tr v W.k.2 hc.mat hc.q hc.s W.ijT ht) (ifOk_tr
    (fun x y ⟨_, ⟨_, _, _, e₁, h₁⟩, ⟨_, _, _, e₂, h₂⟩⟩ => by rw [h₁.m.r15, h₂.m.r15, e₁, e₂])
    (RelCT.mono (rest_tr v K W.k hc) ?_ fun _ _ h => h) ?_)
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, hne⟩
    have o₁ := KeyGen.r15_ne h₁.m.r15 hne
    have o₂ : allOk L.k (rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, ER0.start (h₁.flag hx hc.inK hc.aK hc.sbK) o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, ER0.start (h₂.flag hy hc.inK hc.aK hc.sbK) o₂⟩⟩
  · rintro x y ⟨x₀, y₀, ⟨hl, ⟨ek₁, m₁, r₁, e₁, h₁⟩, ⟨ek₂, m₂, r₂, e₂, h₂⟩⟩, hx, hy, he⟩
    have o₁ := KeyGen.r15_eq h₁.m.r15 he
    have o₂ : ¬ allOk L.k (rhoE L ek₂) (L.k * L.k) := by rw [e₂, ← e₁]; exact o₁
    have k₁ := h₁.flag hx hc.inK hc.aK hc.sbK
    have k₂ := h₂.flag hy hc.inK hc.aK hc.sbK
    exact ⟨hl.post C.bs hx.b hy.b, ⟨ek₁, m₁, r₁, e₁, k₁.i.out, k₁.m.r15, fun h => absurd h o₁⟩,
      ⟨ek₂, m₂, r₂, e₂, k₂.i.out, k₂.m.r15, fun h => absurd h o₂⟩⟩

end Enc

end VG.Proof.MlKem.X86_64
