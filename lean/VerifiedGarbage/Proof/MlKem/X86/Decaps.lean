import VerifiedGarbage.Proof.MlKem.X86.DecapsDec
import VerifiedGarbage.Proof.MlKem.X86.DecapsCmp

/-!
# ML-KEM-768 on x86 (32-bit): `vg_mlkem768_decaps`

`m'` is decrypted (`DecapsDec.lean`), `ek` copied from `dk` and `G(m' ‖ h)`
hashed (`start_piece`), `c'` computed (`Enc.encrypt_piece`), `K̄ = J(z ‖ c)`
hashed, `c` and `c'` compared and `K'` or `K̄` selected into `key`
(`DecapsCmp.lean`) without branching (`fin_piece`). If every `SampleNTT`
succeeded, K-PKE.Encrypt succeeds with the matrix sampled within one bound on
their iterations (`kpkeEncrypt768_some`); if one failed within
`minIterations`, it fails with that bound (`kpkeEncrypt768_none`).
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3Suffix shakeSuffix)

/-- After `ek` is copied from `dk`. -/
structure G1 (s₀ s : State) : Prop extends DM s₀ s where
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK Y.sc)) 1184 = ekD s₀

/-- `m'` decrypted, and the inputs of the re-encryption, then `c`. -/
theorem start_piece {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (Enc.Base Y I) Q c) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <| .seq decrypt <|
        .seq (copyW 3 ⟨0, 1152, 1184⟩ ⟨3, eEK, 1184⟩ 296) <|
        .seq (hash2 3 eST eWK 72 6 ⟨3, eM, 32⟩ ⟨0, 2336, 32⟩ ⟨3, eKR, 64⟩) c) := by
  refine Piece.seq (ldsc_piece (Y := Y) (by taint_decide)) ?_
  refine Piece.seq decrypt_piece ?_
  refine Piece.seq (B := G1) (copyW_piece (Y := Y) 0 1152 3 eEK 296 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by decide) (by decide) (fr1 fr)]; exact h.m⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨3, eEK, 4 * 296⟩) (4 * 296) = _
    rw [post, ekD_eq]
    exact dk_slice hp h.ctx (by decide) (by decide)
  refine Piece.seq (hash2_piece (Y := Y) eST eWK 72 6 (Enc.bM Y.sc) ⟨0, 2336, 32⟩ (Enc.bKR Y.sc) rate72
    (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by decide) (by decide) fr]; exact h.ekc,
        by rw [keepBytes hp (by decide) (by decide) fr]; exact h.m, ?_⟩) hc
  rw [out, dk_slice hp h.ctx (by decide) (by decide), show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from
    sha3Suffix32, ← padded, ← sha3_512_eq]
  show _ = krD s₀
  rw [krD_eq, ← h.m]
  rfl

theorem done_keep {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : Enc.safe Y bs = true) (hc : Y.apart ⟨Y.sc, eC + 960, 128⟩ bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : Enc.Done Y I s₀ s) (c : Ctx Y s₀ s') : Enc.Done Y I s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- `K̄ = J(z ‖ c)`. -/
abbrev kbar (s₀ : State) : List Byte := J (dkZ (dk s₀) ++ ct s₀)

/-- After `K̄` is hashed. -/
structure J1 (s₀ s : State) : Prop extends Enc.Done Y I s₀ s where
  kb : bytesAt s.mem (Buf.addr s₀ bKB) 32 = kbar s₀

/-- After `c` and `c'` are compared. -/
structure J2 (s₀ s : State) : Prop extends J1 s₀ s where
  ebx : s.gpr .ebx = mask (ct s₀ = bytesAt s.mem (Buf.addr s₀ bC) 1088)

/-- After `K'` or `K̄` is selected into `key`. -/
structure J3 (s₀ s : State) : Prop extends Enc.Done Y I s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ bKey) 32 =
    if ct s₀ = bytesAt s.mem (Buf.addr s₀ bC) 1088 then (krD s₀).take 32 else kbar s₀

/-- After `eACC` is loaded, to be returned. -/
structure Fin (s₀ s : State) : Prop extends J3 s₀ s where
  eax : s.gpr .eax = Enc.accE Y s₀ s

theorem selB_mask (p : Prop) [Decidable p] (a b : Byte) :
    selB ((mask p).setWidth 8) a b = if p then a else b := by
  unfold mask
  split
  · rw [show (BitVec.setWidth 8 (0xffffffff : BitVec 32)) = BitVec.allOnes 8 by decide, selB, BitVec.and_allOnes,
      ← BitVec.xor_assoc, BitVec.xor_comm b a, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  · rw [show (BitVec.setWidth 8 (0 : BitVec 32)) = 0#8 by decide, selB, BitVec.and_zero, BitVec.xor_zero]

/-- The key, from the re-encryption. -/
theorem fin_piece :
    Piece (TPre Y) (TPub Y lk) (Enc.Done Y I) Fin
      (.seq (hash2 3 eST eWK 136 0x1f ⟨0, 2368, 32⟩ ⟨1, 0, 1088⟩ ⟨3, deKB, 32⟩) <|
        .seq cmpC <| .seq selC (.block [.mov .eax (.mem (at_ .esi eACC))])) := by
  refine Piece.seq (B := J1) (hash2_piece (Y := Y) eST eWK 136 0x1f ⟨0, 2368, 32⟩ ⟨1, 0, 1088⟩ bKB rate136
    (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨done_keep hp (by decide) (by decide) (by decide) fr h h', ?_⟩) ?_
  · rw [out, dk_slice hp h.ctx (by decide) (by decide), ct_slice hp h.ctx (by decide) (by decide), List.drop_zero,
      List.take_of_length_le (l := ct s₀) (by rw [ct_eq, bytesAt_length]),
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, ← padded, ← J_eq]
    show _ = J (dkZ (dk s₀) ++ ct s₀)
    rw [dkZ]
  refine Piece.seq (B := J2) (cmp_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' e =>
    ⟨⟨done_keep hp (bs := []) (M := 0) (by decide) (by decide) (by decide) (m' ▸ Frame.refl _ _) h.toDone h',
      by rw [m']; exact h.kb⟩, by rw [e, m']⟩) ?_
  refine Piece.seq (B := J3) (sel_piece (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
    ⟨done_keep hp (M := 0) (by decide) (by decide) (by decide) (fr1 fr) h.toDone h', ?_⟩) ?_
  · have kc : bytesAt s'.mem (Buf.addr s₀ bC) 1088 = bytesAt s.mem (Buf.addr s₀ bC) 1088 :=
      keepBytes hp (N := 0) (by decide) (by decide) (fr1 fr)
    have lk : (krD s₀).length = 64 := by rw [show krD s₀ = I.kr s₀ from rfl, ← h.kr, bytesAt_length]
    have lj : (kbar s₀).length = 32 := J_length _
    rw [kc]
    refine bytesAt_eq (by split <;> simp [lk, lj]) fun j hj => ?_
    rw [out j hj, h.ebx, selB_mask]
    have kk : (krD s₀).take 32 = bytesAt s.mem (Buf.addr s₀ bK) 32 := by
      rw [show krD s₀ = I.kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]; rfl
    split
    · simp only [kk, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
    · simp only [← h.kb, Spec.Sha3.bytesAt, List.getElem_map, List.getElem_range]
  exact ld32_piece (Y := Y) eACC (by decide) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨done_keep hp (bs := []) (M := 0) (by decide) (by decide) (by decide)
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Fin decapsBody :=
  start_piece <| .seq (Enc.encrypt_piece hS hρ) fin_piece

theorem piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem.X86.decaps :=
  topLeaf (NoSp.of_all (by decide +kernel)) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- The postcondition, from the final state of the body. -/
theorem post {s₀ s : State} (hp : TPre Y s₀) (h : Fin s₀ s) :
    Outcome (fun iters => decapsInternal mlKem768 iters (dk s₀) (ct s₀)) (Enc.accE Y s₀ s)
      (bytesAt s.mem (Buf.addr s₀ bKey) 32) := by
  have er : Enc.rE I s₀ = (G (decM (dk s₀) (ct s₀) ++ dkH (dk s₀))).2 := by
    show (krD s₀).drop 32 = _; rw [krD_eq, mD_eq]; rfl
  have ek : Enc.ρE I s₀ = ekRho mlKem768 (dkEk (dk s₀)) := by
    show ekRho mlKem768 (ekD s₀) = _; rw [ekD_eq]
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    refine .inr ⟨e, ?_⟩
    show decapsInternal mlKem768 minIterations (dk s₀) (ct s₀) = none
    rw [Enc.mSE, ek] at hn
    rw [decapsInternal768, kpkeEncrypt768_none (i := k % 3) (j := k / 3) (by omega) (by omega) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    rw [ek] at hM
    refine .inl ⟨e, M, ?_⟩
    show decapsInternal mlKem768 M (dk s₀) (ct s₀) = _
    have ec : bytesAt s.mem (Buf.addr s₀ bC) 1088 = ct768 (Enc.aE I s₀) (I.ek s₀) (I.m s₀) (Enc.rE I s₀) :=
      Enc.ct_eq hS hp h.toDone e
    rw [decapsInternal768, kpkeEncrypt768_some hM, h.key, ec, er,
      show Enc.aE I s₀ = fun i j => sv (matSeed (ekRho mlKem768 (dkEk (dk s₀))) i j) by rw [← ek],
      show I.ek s₀ = dkEk (dk s₀) from ekD_eq s₀, show I.m s₀ = decM (dk s₀) (ct s₀) from mD_eq s₀, krD_eq, mD_eq]
    rfl

/-- Memory with the arguments `0`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x10 else if a = 0x500d then 0x20 else if a = 0x5012 then 1 else 0

theorem verified : Verified X86.target Impl.MlKem.X86.decaps (decapsContract X86.abi 88) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' h₀ hq => ?_) ?_
  · have hp := pre_of h₀
    obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post hp hfin
    rw [dk_eq, ct_eq, addr0, addr0, addr0] at r
    exact r
  · let st := satState satMem [⟨0, 2400⟩, ⟨0x1000, 1088⟩]
      [⟨0x2000, 32⟩, ⟨0x10000, 32768⟩, ⟨0x5004, 16⟩]
    refine ⟨st, ?_⟩
    sig_sat_check [decapsContract, decapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]

end VG.Proof.MlKem.X86.Decaps
