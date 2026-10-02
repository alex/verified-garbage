import VerifiedGarbage.Proof.MlKem.X86.DecapsDec
import VerifiedGarbage.Proof.MlKem.X86.DecapsCmp

/-!
# ML-KEM on x86 (32-bit): the body of decapsulation

`m'` is decrypted (`DecapsDec.lean`), `ek` copied from `dk` and `G(m' ‖ h)`
hashed (`start_piece`), `c'` computed (`Enc.encrypt_piece`), `K̄ = J(z ‖ c)`
hashed, `c` and `c'` compared and `K'` or `K̄` selected into `key`
(`DecapsCmp.lean`) without branching (`fin_piece`). If every `SampleNTT`
succeeded, K-PKE.Encrypt succeeds with the matrix sampled within one bound on
their iterations (`KPke.kpkeEncrypt_some`); if one failed within
`minIterations`, it fails with that bound (`KPke.kpkeEncrypt_none`) (`post`).
Each parameter set's contract implies `TPre (Y L)` and its public data
(`Proof/MlKem/X86/Decaps.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3Suffix shakeSuffix)

/-- The facts of the layout that decapsulation uses beyond K-PKE. -/
class DecapsOK (L : KemLay) : Prop where
  ekc : ((Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ && (Y L).okW ⟨3, L.eEK, L.p.ekLen⟩ &&
    (Y L).sep ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩) = true
  ek4 : 4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ctLen < 2 ^ 32
  aEM : (Y L).apart (bM L) [⟨3, L.eEK, L.p.ekLen⟩] = true
  g : ((Y L).okW ⟨3, L.eST, 200⟩ && (Y L).okW ⟨3, L.eWK, 640⟩ && (Y L).ok (Enc.bM L (Y L).sc) &&
    (Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ && (Y L).okW (Enc.bKR L (Y L).sc) &&
    (Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ && (Y L).sep (Enc.bM L (Y L).sc) ⟨3, L.eST, 200⟩ &&
    (Y L).sep (Enc.bM L (Y L).sc) ⟨3, L.eWK, 640⟩ && (Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eST, 200⟩ &&
    (Y L).sep ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eWK, 640⟩ && (Y L).sep ⟨3, L.eST, 200⟩ (Enc.bKR L (Y L).sc) &&
    (Y L).sep (Enc.bKR L (Y L).sc) ⟨3, L.eWK, 640⟩) = true
  aG : (Y L).apart (Enc.bEK L (Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true ∧
    (Y L).apart (Enc.bM L (Y L).sc) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true ∧
    (Y L).ok ⟨0, 768 * L.p.k + 32, 32⟩ = true ∧ (Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ = true ∧
    (Y L).ok ⟨0, 384 * L.p.k, L.p.ekLen⟩ = true
  j : ((Y L).okW ⟨3, L.eST, 200⟩ && (Y L).okW ⟨3, L.eWK, 640⟩ && (Y L).ok ⟨0, 768 * L.p.k + 64, 32⟩ &&
    (Y L).ok ⟨1, 0, L.p.ctLen⟩ && (Y L).okW (bKB L) && (Y L).sep ⟨3, L.eST, 200⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eST, 200⟩ && (Y L).sep ⟨0, 768 * L.p.k + 64, 32⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eST, 200⟩ && (Y L).sep ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eWK, 640⟩ &&
    (Y L).sep ⟨3, L.eST, 200⟩ (bKB L) && (Y L).sep (bKB L) ⟨3, L.eWK, 640⟩) = true
  dJ : Enc.safe L (Y L) [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, bKB L] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨3, L.eST, 200⟩, ⟨3, L.eWK, 640⟩, bKB L] = true
  dNil : Enc.safe L (Y L) [] = true ∧ (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [] = true
  dKey : Enc.safe L (Y L) [bKey] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [bKey] = true ∧
    (Y L).apart (bC L) [bKey] = true
  acc : (Y L).ok ⟨3, L.eACC, 4⟩ = true

variable {L : KemLay}

/-- After `ek` is copied from `dk`. -/
structure G1 (L : KemLay) (s₀ s : State) : Prop extends DM L s₀ s where
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK L (Y L).sc)) L.p.ekLen = ekD L s₀

/-- `m'` decrypted, and the inputs of the re-encryption, then `c`. -/
theorem start_piece [CeOK L] [DecOK L] [DecapsOK L] (hk : 0 < L.p.k) {Q : State → State → Prop}
    {c : Prog isa} (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Base L (Y L) (I L)) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <| .seq (decrypt L) <|
        .seq (copyW 3 ⟨0, 384 * L.p.k, L.p.ekLen⟩ ⟨3, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash2 3 L.eST L.eWK 72 6 ⟨3, L.eM, 32⟩ ⟨0, 768 * L.p.k + 32, 32⟩ ⟨3, L.eKR, 64⟩) c) := by
  obtain ⟨e₁, e₂, e₃, -⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨g₁, g₂, g₃, -, g₅⟩ := DecapsOK.aG (L := L)
  refine Piece.seq (ldsc_piece (Y := Y L) (by yd_taint)) ?_
  refine Piece.seq (decrypt_piece hk) ?_
  refine Piece.seq (B := G1 L) (copyW_piece' (Y := Y L) 0 (384 * L.p.k) 3 L.eEK (L.p.ekLen / 4) L.p.ekLen e₁ e₂ e₃
    DecapsOK.ekc (by yd_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by rdecide) DecapsOK.aEM (fr1 fr)]; exact h.m⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨3, L.eEK, L.p.ekLen⟩) L.p.ekLen = _
    rw [post, ekD_eq]
    exact dk_slice hp h.ctx (by unfold Params.ekLen Params.dkLen; omega) g₅
  refine Piece.seq (hash2_piece (Y := Y L) L.eST L.eWK 72 6 (Enc.bM L (Y L).sc) ⟨0, 768 * L.p.k + 32, 32⟩
    (Enc.bKR L (Y L).sc) rate72 DecapsOK.g (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by rdecide) g₁ fr]; exact h.ekc,
        by rw [keepBytes hp (by rdecide) g₂ fr]; exact h.m, ?_⟩) hc
  rw [out, dk_slice hp h.ctx (by unfold Params.dkLen; omega) g₃, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from
    sha3Suffix32, ← padded, ← sha3_512_eq]
  show _ = krD L s₀
  rw [krD_eq, ← h.m]
  rfl

theorem done_keep {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (Y L).stk)
    (hs : Enc.safe L (Y L) bs = true)
    (hc : (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Enc.Done L (Y L) (I L) s₀ s) (c : Ctx (Y L) s₀ s') :
    Enc.Done L (Y L) (I L) s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- `K̄ = J(z ‖ c)`. -/
abbrev kbar (L : KemLay) (s₀ : State) : List Byte := J (KPke.dkZ L.p (dk L s₀) ++ ct L s₀)

/-- After `K̄` is hashed. -/
structure J1 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (Y L) (I L) s₀ s where
  kb : bytesAt s.mem (Buf.addr s₀ (bKB L)) 32 = kbar L s₀

/-- After `c` and `c'` are compared. -/
structure J2 (L : KemLay) (s₀ s : State) : Prop extends J1 L s₀ s where
  ebx : s.gpr .ebx = mask (ct L s₀ = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen)

/-- After `K'` or `K̄` is selected into `key`. -/
structure J3 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (Y L) (I L) s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ bKey) 32 =
    if ct L s₀ = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen then (krD L s₀).take 32 else kbar L s₀

/-- After `eACC` is loaded, to be returned. -/
structure Fin (L : KemLay) (s₀ s : State) : Prop extends J3 L s₀ s where
  eax : s.gpr .eax = Enc.accE L (Y L) s₀ s

theorem selB_mask (p : Prop) [Decidable p] (a b : Byte) :
    selB ((mask p).setWidth 8) a b = if p then a else b := by
  unfold mask
  split
  · rw [show (BitVec.setWidth 8 (0xffffffff : BitVec 32)) = BitVec.allOnes 8 by decide, selB, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [show (BitVec.setWidth 8 (0 : BitVec 32)) = 0#8 by decide, selB, BitVec.and_zero, BitVec.xor_zero]

/-- The key, from the re-encryption. -/
theorem fin_piece [DecOK L] [CmpOK L] [DecapsOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Done L (Y L) (I L)) (Fin L)
      (.seq (hash2 3 L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩ ⟨1, 0, L.p.ctLen⟩ ⟨3, L.eH, 32⟩) <|
        .seq (cmpC L) <| .seq (selC L) (.block [.mov .eax (.mem (at_ .esi L.eACC))])) := by
  obtain ⟨-, -, -, g₄, -⟩ := DecapsOK.aG (L := L)
  obtain ⟨-, -, -, hN⟩ := DecapsOK.ek4 (L := L)
  obtain ⟨d₁, d₂⟩ := DecapsOK.dJ (L := L)
  obtain ⟨n₁, n₂⟩ := DecapsOK.dNil (L := L)
  obtain ⟨k₁, k₂, k₃⟩ := DecapsOK.dKey (L := L)
  refine Piece.seq (B := J1 L) (hash2_piece (Y := Y L) L.eST L.eWK 136 0x1f ⟨0, 768 * L.p.k + 64, 32⟩
    ⟨1, 0, L.p.ctLen⟩ (bKB L) rate136 DecapsOK.j (by rdecide) (by rdecide) hN (by rdecide) (by taint_rfl) (by yd_taint)
    (by yd_taint) (by yd_taint) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨done_keep hp (by rdecide) d₁ d₂ fr h h', ?_⟩) ?_
  · rw [out, dk_slice hp h.ctx (by unfold Params.dkLen; omega) g₄, ct_slice hp h.ctx (by omega) DecOK.ct.1,
      List.drop_zero, List.take_of_length_le (l := ct L s₀) (by rw [ct_eq, bytesAt_length]),
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, ← padded, ← J_eq]
    show _ = J (KPke.dkZ L.p (dk L s₀) ++ ct L s₀)
    rfl
  refine Piece.seq (B := J2 L) (cmp_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' e =>
    ⟨⟨done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂ (m' ▸ Frame.refl _ _) h.toDone h',
      by rw [m']; exact h.kb⟩, by rw [e, m']⟩) ?_
  refine Piece.seq (B := J3 L) (sel_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
    ⟨done_keep hp (M := 0) (by rdecide) k₁ k₂ (fr1 fr) h.toDone h', ?_⟩) ?_
  · have kc : bytesAt s'.mem (Buf.addr s₀ (bC L)) L.p.ctLen = bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen :=
      keepBytes hp (N := 0) (by rdecide) k₃ (fr1 fr)
    have lk : (krD L s₀).length = 64 := by rw [show krD L s₀ = (I L).kr s₀ from rfl, ← h.kr, bytesAt_length]
    have lj : (kbar L s₀).length = 32 := J_length _
    rw [kc]
    refine bytesAt_eq (by split <;> simp [lk, lj]) fun j hj => ?_
    rw [out j hj, h.ebx, selB_mask]
    have kk : (krD L s₀).take 32 = bytesAt s.mem (Buf.addr s₀ (bK L)) 32 := by
      rw [show krD L s₀ = (I L).kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]; rfl
    split
    · simp only [kk, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
    · simp only [← h.kb, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
  exact ld32_piece (Y := Y L) L.eACC DecapsOK.acc (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨done_keep hp (bs := []) (M := 0) (by rdecide) n₁ n₂
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece [CeOK L] [DecOK L] [CmpOK L] [DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) (Fin L) (decapsBody L) :=
  start_piece hk <| .seq (Enc.encrypt_piece (hS L) (hρ L) hk) fin_piece

theorem piece [CeOK L] [DecOK L] [CmpOK L] [DecapsOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L]
    [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) (hsp : NoSp (decapsBody L)) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin L s₀) s₀ s')
      (leaf (decapsBody L)) :=
  topLeaf hsp ((body_piece hk).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- The postcondition, from the final state of the body. -/
theorem post [Enc.VOK L] (hη : L.p.η₁ = 2 ∧ L.p.η₂ = 2) {s₀ s : State} (hp : TPre (Y L) s₀) (h : Fin L s₀ s) :
    Outcome (fun iters => decapsInternal L.p iters (dk L s₀) (ct L s₀)) (Enc.accE L (Y L) s₀ s)
      (bytesAt s.mem (Buf.addr s₀ bKey) 32) := by
  have er : Enc.rE (I L) s₀ = (G (KPke.decM L.p (dk L s₀) (ct L s₀) ++ KPke.dkH L.p (dk L s₀))).2 := by
    show (krD L s₀).drop 32 = _; rw [krD_eq, mD_eq]; rfl
  have ek : Enc.ρE L (I L) s₀ = ekRho L.p (KPke.dkEk L.p (dk L s₀)) := by
    show ekRho L.p (ekD L s₀) = _; rw [ekD_eq]
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; omega
    refine .inr ⟨e, ?_⟩
    show decapsInternal L.p minIterations (dk L s₀) (ct L s₀) = none
    rw [Enc.mSE, ek] at hn
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_none (i := k % L.p.k) (j := k / L.p.k) (Nat.mod_lt _ hk0)
      (Nat.div_lt_of_lt_mul hk) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    rw [ek] at hM
    refine .inl ⟨e, M, ?_⟩
    show decapsInternal L.p M (dk L s₀) (ct L s₀) = _
    have ec : bytesAt s.mem (Buf.addr s₀ (bC L)) L.p.ctLen =
        KPke.ct L.p (Enc.aE L (I L) s₀) ((I L).ek s₀) ((I L).m s₀) (Enc.rE (I L) s₀) :=
      Enc.ct_eq (hS L) hp h.toDone e
    rw [KPke.decapsInternal_eq, KPke.kpkeEncrypt_some hη hM, h.key, ec, er,
      show Enc.aE L (I L) s₀ = fun i j => sv (matSeed (ekRho L.p (KPke.dkEk L.p (dk L s₀))) i j) by rw [← ek],
      show (I L).ek s₀ = KPke.dkEk L.p (dk L s₀) from ekD_eq L s₀,
      show (I L).m s₀ = KPke.decM L.p (dk L s₀) (ct L s₀) from mD_eq L s₀, krD_eq, mD_eq]
    rfl

end VG.Proof.MlKem.X86.Decaps
