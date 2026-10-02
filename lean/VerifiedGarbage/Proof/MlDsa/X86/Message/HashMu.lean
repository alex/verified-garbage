import VerifiedGarbage.Proof.MlDsa.X86.Message.Hash
import VerifiedGarbage.Proof.MlKem.KPke

/-!
# ML-DSA on x86 (32-bit), `sign_message` and `verify_message`: `μ` and `tr`

Untrusted: everything here is checked by Lean. In the body, `muHash` leaves
`μ = H(tr ‖ 0 ‖ ctx_len ‖ ctx ‖ M, 64)` at `X + 840` (`muHash_piece`), and
`trHash` leaves `H(pk, 64)` there (`trHash_piece`): from the zeroed state,
each absorb continues the message from the position the previous one
returned, which is public, as the lengths are.
-/

namespace VG.Proof.MlDsa.X86.Message

open VG VG.X86 VG.Impl.MlDsa.X86.Message
open VG.Proof.MlDsa.Message
open VG.Proof.MlKem.X86 (Within Piece P0)
open VG.Spec.Sha3 (bytesAt stateAt Repr)
open VG.Spec.MlDsa (Params)

/-- The two bytes `0 ‖ ctx_len` of the formatted message. -/
abbrev hdrBytes (L : Lay) : List Byte := [0, BitVec.ofNat 8 L.ctxLen.toNat]

theorem ofNat_toNat32 (x : BitVec 32) : BitVec.ofNat 32 x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt x.isLt]

theorem ofNat_toNat_eq32 {x : BitVec 32} {n : Nat} (h : x.toNat = n) : x = BitVec.ofNat 32 n := by
  subst h; exact (ofNat_toNat32 x).symm

/-- The arguments of an absorb are fit, if its data and length are not `eax`. -/
theorem absOk {n : Nat} {src len pos : Arg} (h1 : src.ok n = true) (h2 : len.ok n = true) (h3 : pos.ok n = true)
    (r1 : src.isRet = false) (r2 : len.isRet = false) : argsOk n (absArgs src len pos) = true := by
  simp (config := { decide := true }) [argsOk, h1, h2, h3, r1, r2]
  exact ⟨rfl, rfl, rfl⟩

theorem padOk {n : Nat} {pos : Arg} (h : pos.ok n = true) : argsOk n (padArgs pos) = true := by
  simp (config := { decide := true }) [argsOk, h]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem sqzOk {n : Nat} : argsOk n sqzArgs = true := by
  simp (config := { decide := true }) [argsOk]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem argOk {L : Lay} (hL : L.Ok) {i : Nat} (hi : i < 5) : (Arg.arg i).ok L.nA = true := by
  have := hL.nA5; simp only [Arg.ok, decide_eq_true_eq]; omega

theorem Ctx.arg' {L : Lay} {m₁ : Mem} {t : State} (hc : Ctx L m₁ t) (hL : L.Ok) {i : Nat} (hi : i < 5) :
    (Arg.arg i).val t = L.argv.getD i 0 :=
  hc.argV (by have := hL.nA5; omega)

section
variable (lay : State → Lay) (s₀ : State)

/-- The context string and the message, as on entry. -/
abbrev ctxB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).ctx.setWidth 64) (lay s₀).ctxLen.toNat
abbrev msgB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).msg.setWidth 64) (lay s₀).len.toNat
abbrev keyB : List Byte := bytesAt (P0 s₀).mem ((lay s₀).key.setWidth 64) (lay s₀).keyLen

end

section
variable {Pre : State → Prop} {Pub : State → State → Prop} {lay : State → Lay} {A : State → State → Prop}

theorem muHash_piece (tr : Arg) (trp : State → BitVec 32) (trv : State → List Byte)
    {ht : Taint.Hint VG.X86.Taint.T}
    (tt : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs tr (.imm 64) (.imm 0)))) ht).isSome =
      true)
    (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s)
    (hnA : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA) (hok : ∀ s₀, Pre s₀ → tr.ok (lay s₀).nA = true) (hret : tr.isRet = false)
    (htr : ∀ s₀ s, Pre s₀ → CtxO lay s₀ s → tr.val s = trp s₀)
    (htp : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → trp s₀ = trp s₀')
    (hv : ∀ s₀ s, Pre s₀ → A s₀ s → bytesAt s.mem ((trp s₀).setWidth 64) 64 = trv s₀)
    (hv' : ∀ s₀, Pre s₀ → (trv s₀).length = 64)
    (hb : ∀ s₀, Pre s₀ → (lay s₀).Ok → (trp s₀).toNat + 64 ≤ 2 ^ 32 ∧
      (∃ R ∈ (lay s₀).rd ++ (lay s₀).wr, Within ⟨(trp s₀).setWidth 64, 64⟩ R) ∧
      Region.Disjoint ⟨(trp s₀).setWidth 64, 64⟩ ⟨(lay s₀).ST, 200⟩ ∧
      Region.Disjoint ⟨(trp s₀).setWidth 64, 64⟩ ⟨(lay s₀).KS, 640⟩ ∧
      (lay s₀).STK.Disjoint ⟨(trp s₀).setWidth 64, 64⟩) :
    Piece Pre Pub A (fun s₀ s => CtxO lay s₀ s ∧ bytesAt s.mem (lay s₀).MU 64 =
      Spec.MlDsa.H (trv s₀ ++ hdrBytes (lay s₀) ++ ctxB lay s₀ ++ msgB lay s₀) 64) (muHash tr) := by
  -- Zero the state.
  refine Piece.seq (zeroSt_piece hpub hA (B := fun s₀ s => CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST =
      Spec.Sha3.zero ∧ bytesAt s.mem ((trp s₀).setWidth 64) 64 = trv s₀)
    fun s₀ s s' h₀ ha hc' hf hz => ⟨hc', hz, ?_⟩) ?_
  · obtain ⟨-, -, dS, -, -⟩ := hb s₀ h₀ hc'.ok
    rw [← hv s₀ s h₀ ha]
    exact Proof.MlKem.bytesAt_congr fun i hi =>
      hf.bytes (R := ⟨(trp s₀).setWidth 64, 64⟩) (by simpa using dS) (by show 64 ≤ 2 ^ 64; decide) hi
  -- `tr`.
  refine Piece.seq (kabs_piece tr (.imm 64) (.imm 0) trp (fun _ => 64) (fun _ => 0) tt hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => ?_) (fun s₀ s h₀ h => ⟨htr s₀ s h₀ h.1, rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨htp s₀ s₀' h₀ h₀' hq, rfl, rfl⟩) (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · exact absOk (hok s₀ h₀) rfl rfl hret rfl
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hb s₀ h₀ h.1.ok
    exact ⟨by decide, by decide, h1, h2, h3, h4, h5⟩
  · have := hR [] (Proof.MlKem.repr_nil h.2.1) rfl
    rwa [List.nil_append, h.2.2] at this
  have argA : ∀ s₀, Pre s₀ → ∀ i < 5, (Arg.arg i).ok (lay s₀).nA = true := fun s₀ h₀ i hi => by
    have := hnA s₀ h₀; simp only [Arg.ok, decide_eq_true_eq]; omega
  -- `0 ‖ ctx_len`.
  refine Piece.seq (kabs_piece (.off oHdr) (.imm 2) (.imm 64) (fun s₀ => (lay s₀).X32 + BitVec.ofNat 32 944)
    (fun _ => 2) (fun _ => 64) (by taint_decide) hpub (fun _ _ _ h => h.1)
    (fun _ _ => absOk rfl rfl rfl rfl rfl) (fun s₀ s h₀ h => ⟨h.1.ctx.off _, rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨by rw [(hpub s₀ s₀' h₀ h₀' hq).x], rfl, rfl⟩) (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀ ++ hdrBytes (lay s₀)))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · have hL := h.1.ok
    have ehd : ((lay s₀).X32 + BitVec.ofNat 32 944).setWidth 64 = (lay s₀).X + BitVec.ofNat 64 944 :=
      hL.xo (by decide)
    refine ⟨by decide, by decide, by rw [hL.x32_toNat (by decide)]; have := hL.x32_lt; omega,
      by rw [ehd]; exact cov_x hL (e := 944) (k := 2) (by omega), ?_, ?_, by rw [ehd]; exact hL.stk_x (by omega)⟩
    · rw [ehd]
      have := Offset.disjoint (lay s₀).X (d := 944) (n := 2) (e := 0) (k := 200) (by omega) (by omega) (by omega)
      simpa only [x0] using this
    · rw [ehd]
      exact Offset.disjoint (lay s₀).X (d := 944) (n := 2) (e := 200) (k := 640) (by omega) (by omega) (by omega)
  · have ehd : ((lay s₀).X32 + BitVec.ofNat 32 944).setWidth 64 = (lay s₀).X + BitVec.ofNat 64 944 :=
      h.1.ok.xo (by decide)
    have := hR _ h.2 (by rw [hv' s₀ h₀])
    rwa [ehd, h.1.ctx.hdr] at this
  -- The context string.
  refine Piece.seq (kabs_piece (.arg 3) (.arg 4) (.imm 66) (fun s₀ => (lay s₀).ctx)
    (fun s₀ => (lay s₀).ctxLen.toNat) (fun _ => 66) (by taint_decide) hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => absOk (argA s₀ h₀ 3 (by omega)) (argA s₀ h₀ 4 (by omega)) rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a3],
      by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a4, ofNat_toNat32], rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).ctx, by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen], rfl⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (trv s₀ ++ hdrBytes (lay s₀) ++ ctxB lay s₀) ∧
      (s.gpr .eax).toNat = (66 + (lay s₀).ctxLen.toNat) % 136)
    fun s₀ s s' h₀ h hc' _ hR he => ⟨hc', ?_, he⟩) ?_
  · have hL := h.1.ok
    have := hL.ctxLt
    exact ⟨by decide, by omega, hL.nCtx, ⟨(lay s₀).CTX, List.mem_append_left _ hL.inCtx, within_self _⟩,
      by have := hL.x_r hL.xCtx (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm,
      (hL.x_r hL.xCtx (e := 200) (k := 640) (by omega)).symm, hL.kCtx⟩
  · have hL := h.1.ok
    have := hR _ h.2 (by simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil])
    rwa [h.1.ctx.bytesAt_eq hL.xCtx hL.kCtx (by have := hL.nCtx; omega)] at this
  -- The message.
  refine Piece.seq (kabs_piece (.arg 1) (.arg 2) .ret (fun s₀ => (lay s₀).msg)
    (fun s₀ => (lay s₀).len.toNat) (fun s₀ => (66 + (lay s₀).ctxLen.toNat) % 136) (by taint_decide) hpub
    (fun _ _ _ h => h.1)
    (fun s₀ h₀ => absOk (argA s₀ h₀ 1 (by omega)) (argA s₀ h₀ 2 (by omega)) rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a1],
      by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a2, ofNat_toNat32], ofNat_toNat_eq32 h.2.2⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).msg, by rw [(hpub s₀ s₀' h₀ h₀' hq).len],
      by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen]⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => CtxO lay s₀ s ∧
      Repr s.mem (lay s₀).ST 136 (trv s₀ ++ hdrBytes (lay s₀) ++ ctxB lay s₀ ++ msgB lay s₀) ∧
      (s.gpr .eax).toNat = ((66 + (lay s₀).ctxLen.toNat) % 136 + (lay s₀).len.toNat) % 136)
    fun s₀ s s' h₀ h hc' _ hR he => ⟨hc', ?_, he⟩) ?_
  · have hL := h.1.ok
    exact ⟨Nat.mod_lt _ (by decide), (lay s₀).len.isLt, hL.nMsg,
      ⟨(lay s₀).MSG, List.mem_append_left _ hL.inMsg, within_self _⟩,
      by have := hL.x_r hL.xMsg (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm,
      (hL.x_r hL.xMsg (e := 200) (k := 640) (by omega)).symm, hL.kMsg⟩
  · have hL := h.1.ok
    have := hR _ h.2.1 (by
      simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil, Proof.MlKem.bytesAt_length])
    rwa [h.1.ctx.bytesAt_eq hL.xMsg hL.kMsg (by have := hL.nMsg; omega)] at this
  -- Pad and squeeze.
  refine Piece.seq (kpad_piece .ret (fun s₀ => ((66 + (lay s₀).ctxLen.toNat) % 136 + (lay s₀).len.toNat) % 136)
    (by taint_decide) hpub (fun _ _ _ h => h.1) (fun _ _ => padOk rfl) (fun s₀ s h₀ h => ofNat_toNat_eq32 h.2.2)
    (fun s₀ s₀' h₀ h₀' hq => by rw [(hpub s₀ s₀' h₀ h₀' hq).ctxLen, (hpub s₀ s₀' h₀ h₀' hq).len])
    (fun _ _ _ _ => Nat.mod_lt _ (by decide))
    (B := fun s₀ s => CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST = Spec.Sha3.absorb 136
      (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix (trv s₀ ++ hdrBytes (lay s₀) ++ ctxB lay s₀ ++ msgB lay s₀)))
    fun s₀ s s' h₀ h hc' _ hS => ⟨hc', hS _ h.2.1 ?_⟩) ?_
  · simp only [List.length_append, hv' s₀ h₀, List.length_cons, List.length_nil, Proof.MlKem.bytesAt_length]
    omega
  exact ksqz_piece hpub (fun _ _ _ h => h.1) (fun _ _ => sqzOk) fun s₀ s s' h₀ h hc' _ hm =>
    ⟨hc', by rw [hm, h.2, Spec.MlDsa.H, Proof.MlKem.shake256_eq]⟩

/-! ## `tr = H(pk, 64)` -/

theorem trHash_piece {p : Params} (hpub : ∀ s₀ s₀', Pre s₀ → Pre s₀' → Pub s₀ s₀' → PubL (lay s₀) (lay s₀'))
    (hA : ∀ s₀ s, Pre s₀ → A s₀ s → CtxO lay s₀ s) (hnA : ∀ s₀, Pre s₀ → 5 ≤ (lay s₀).nA)
    (hk : ∀ s₀, Pre s₀ → (lay s₀).keyLen = p.pkLen) {ht₁ ht₂ : Taint.Hint VG.X86.Taint.T}
    (tt₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (absArgs (.arg 0) (.imm p.pkLen) (.imm 0)))) ht₁).isSome =
      true)
    (tt₂ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (setArgs (padArgs (.imm (p.pkLen % 136))))) ht₂).isSome =
      true) :
    Piece Pre Pub A (fun s₀ s => CtxO lay s₀ s ∧ bytesAt s.mem (lay s₀).MU 64 = Spec.MlDsa.H (keyB lay s₀) 64)
      (trHash p) := by
  refine Piece.seq (zeroSt_piece hpub hA (B := fun s₀ s => CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST =
      Spec.Sha3.zero) fun s₀ s s' h₀ ha hc' _ hz => ⟨hc', hz⟩) ?_
  refine Piece.seq (kabs_piece (.arg 0) (.imm p.pkLen) (.imm 0) (fun s₀ => (lay s₀).key)
    (fun s₀ => (lay s₀).keyLen) (fun _ => 0) tt₁ hpub (fun _ _ _ h => h.1)
    (fun s₀ h₀ => absOk (by have := hnA s₀ h₀; simp only [Arg.ok, decide_eq_true_eq]; omega) rfl rfl rfl rfl)
    (fun s₀ s h₀ h => ⟨by rw [h.1.ctx.arg' h.1.ok (by omega), h.1.ok.a0], by rw [hk s₀ h₀]; rfl, rfl⟩)
    (fun s₀ s₀' h₀ h₀' hq => ⟨(hpub s₀ s₀' h₀ h₀' hq).key, by rw [hk s₀ h₀, hk s₀' h₀'], rfl⟩)
    (fun s₀ s h₀ h => ?_)
    (B := fun s₀ s => CtxO lay s₀ s ∧ Repr s.mem (lay s₀).ST 136 (keyB lay s₀))
    fun s₀ s s' h₀ h hc' _ hR _ => ⟨hc', ?_⟩) ?_
  · have hL := h.1.ok
    have := hL.hKey
    exact ⟨by decide, by omega, hL.nKey, ⟨(lay s₀).KEY, List.mem_append_left _ hL.inKey, within_self _⟩,
      by have := hL.x_r hL.xKey (e := 0) (k := 200) (by omega); simpa only [x0] using this.symm,
      (hL.x_r hL.xKey (e := 200) (k := 640) (by omega)).symm, hL.kKey⟩
  · have hL := h.1.ok
    have := hR [] (Proof.MlKem.repr_nil h.2) rfl
    rwa [List.nil_append, h.1.ctx.bytesAt_eq hL.xKey hL.kKey (by have := hL.nKey; omega)] at this
  refine Piece.seq (kpad_piece (.imm (p.pkLen % 136)) (fun _ => p.pkLen % 136) tt₂ hpub
    (fun _ _ _ h => h.1) (fun _ _ => padOk rfl) (fun _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun _ _ _ _ => Nat.mod_lt _ (by decide))
    (B := fun s₀ s => CtxO lay s₀ s ∧ stateAt s.mem (lay s₀).ST = Spec.Sha3.absorb 136
      (Spec.Sha3.pad 136 Spec.Sha3.shakeSuffix (keyB lay s₀)))
    fun s₀ s s' h₀ h hc' _ hS => ⟨hc', hS _ h.2 (by rw [Proof.MlKem.bytesAt_length, hk s₀ h₀])⟩) ?_
  exact ksqz_piece hpub (fun _ _ _ h => h.1) (fun _ _ => sqzOk) fun s₀ s s' h₀ h hc' _ hm =>
    ⟨hc', by rw [hm, h.2, Spec.MlDsa.H, Proof.MlKem.shake256_eq]⟩

end

end VG.Proof.MlDsa.X86.Message
