import VerifiedGarbage.Proof.MlKem1024.X86.KeyGenG
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.Ntt

/-!
# ML-KEM-1024 on x86 (32-bit): `ŝ` and `ê` in `vg_mlkem1024_keygen`

Untrusted: everything here is checked by Lean. `kg4Prf N` computes
`NTT(SamplePolyCBD₂(PRF₂(σ, N)))` into `scratch[1024N]` (`prf_piece`), and the
eight of them take `P 0` to `P 8` (`prfs_piece`).
-/

namespace VG.Proof.MlKem1024.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad shakeSuffix)

/-- `P N` holds after a block or call whose frame is apart from what it states. -/
theorem P.keep {N : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (h₁ : Y.apart bACC bs = true) (h₂ : Y.apart bRho bs = true) (h₃ : Y.apart bSig bs = true)
    (h₄ : ∀ j < N, Y.apart (bSE j) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : P N s₀ s) (c : Ctx Y s₀ s') : P N s₀ s' :=
  ⟨c, by rw [keepW hp hM h₁ fr]; exact h.acc, by rw [keepBytes hp hM h₂ fr]; exact h.rho,
    by rw [keepBytes hp hM h₃ fr]; exact h.sig, fun j hj => keepPoly hp hM (h₄ j hj) fr (h.se j hj)⟩

/-- `σ ‖ N` is stored. -/
structure Q1 (N : Nat) (s₀ s : State) : Prop extends P N s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ bNB) 1 = [BitVec.ofNat 8 N]

/-- `PRF₂(σ, N)` is computed. -/
structure Q2 (N : Nat) (s₀ s : State) : Prop extends P N s₀ s where
  prf : bytesAt s.mem (Buf.addr s₀ bPRF) 128 = prf 2 (kgSigma1024 (d s₀)) (BitVec.ofNat 8 N)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` is computed. -/
structure Q3 (N : Nat) (s₀ s : State) : Prop extends P N s₀ s where
  cbd : PolyIs s.mem (Buf.addr s₀ (bSE N)) (cbd (kgSigma1024 (d s₀)) N)

theorem sigN_split {s₀ : State} (hp : TPre Y s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ bSigN) 33 = bytesAt m (Buf.addr s₀ bSig) 32 ++ bytesAt m (Buf.addr s₀ bNB) 1 := by
  have e : Buf.addr s₀ bNB = Buf.addr s₀ bSig + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bNB) (by decide), Buf.addr_eq hp (b := bSig) (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e]
  exact bytesAt_add m (Buf.addr s₀ bSig) 32 1

theorem apart_prf : ∀ j < 8, Y.apart (bSE j) [⟨Y.sc, kg4ST, 200⟩, ⟨Y.sc, kg4WK, 640⟩, bPRF] = true := by decide
theorem apart_nb : ∀ j < 8, Y.apart (bSE j) [⟨Y.sc, kg4RS + 64, 1⟩] = true := by decide
theorem apart_se : ∀ N < 8, ∀ j < N, Y.apart (bSE j) [bSE N] = true := by decide
theorem apart_ntt : ∀ N < 8, ∀ j < N, Y.apart (bSE j) [bSE N, bNS] = true := by decide
theorem apart_se' : ∀ N < 8,
    (Y.apart bACC [bSE N] && Y.apart bRho [bSE N] && Y.apart bSig [bSE N]) = true := by decide
theorem apart_ntt' : ∀ N < 8,
    (Y.apart bACC [bSE N, bNS] && Y.apart bRho [bSE N, bNS] && Y.apart bSig [bSE N, bNS]) = true := by decide
theorem ok_cbd : ∀ N < 8, (Y.ok bPRF && Y.okW (bSE N) && Y.sep bPRF (bSE N)) = true := by decide
theorem ok_ntt : ∀ N < 8, (Y.okW (bSE N) && Y.okW bNS && Y.sep (bSE N) bNS) = true := by decide

/-- `ŝ[N]` or `ê[N - 4]`. -/
theorem prf_piece (N : Nat) (hN : N < 8) {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (kg4RS + 64) N)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax bPRF ++ ptrTo Y.sc .ecx (bSE N))) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax (bSE N) ++ ptrTo Y.sc .ecx bNS)) h₃).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (P N) (P (N + 1)) (kg4Prf N) := by
  refine Piece.seq (B := Q1 N) (st8_piece (Y := Y) (kg4RS + 64) N (by decide) t₁
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (M := 0) (by decide) (by decide) (by decide) (by decide)
      (fun j hj => apart_nb j (by omega)) (m' ▸ frW8) h'
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 N]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    refine (ite_eq_left (rfl : Buf.addr s₀ bNB = Buf.addr s₀ ⟨Y.sc, kg4RS + 64, 1⟩)).trans ?_
    rw [BitVec.setWidth_ofNat_of_le (by decide)]
  refine Piece.seq (B := Q2 N) (hash1_piece (Y := Y) kg4ST kg4WK 136 0x1f bSigN bPRF rate136 (by decide)
    (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (by decide) (by decide) (by decide) (by decide) (fun j hj => apart_prf j (by omega)) fr h'
  · rw [out, sigN_split hp, h.sig, h.nb, show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32,
      prf_eq]
  refine Piece.seq (B := Q3 N) (cbd2C_piece (Y := Y) 3 kg4PRF 3 (1024 * N) (ok_cbd N hN) (by decide) t₂
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨?_, ?_⟩) ?_
  · have a := apart_se' N hN
    simp only [Bool.and_eq_true] at a
    exact h.keep hp (by decide) a.1.1 a.1.2 a.2 (apart_se N hN) fr h'
  · rw [h.prf] at post; exact post
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 (1024 * N) 3 kg4NS (ok_ntt N hN) (by decide) t₃
    (fun _ _ _ h => ⟨h.ctx, h.cbd.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have a := apart_ntt' N hN
  simp only [Bool.and_eq_true] at a
  have k := h.keep hp (by decide) a.1.1 a.1.2 a.2 (apart_ntt N hN) fr h'
  refine ⟨h', k.acc, k.rho, k.sig, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.se j hj
  · rw [h.cbd.2] at post; exact post

/-- The eight, then `c`. -/
theorem prfs_piece {B : State → State → Prop} {c : Prog isa} (h : Piece (TPre Y) (TPub Y lk) (P 8) B c) :
    Piece (TPre Y) (TPub Y lk) (P 0) B (.seq (kg4Prf 0) <| .seq (kg4Prf 1) <| .seq (kg4Prf 2) <| .seq (kg4Prf 3) <|
      .seq (kg4Prf 4) <| .seq (kg4Prf 5) <| .seq (kg4Prf 6) <| .seq (kg4Prf 7) c) :=
  .seq (prf_piece 0 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 1 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 2 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 3 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 4 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 5 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 6 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) <|
  .seq (prf_piece 7 (by decide) (by taint_decide) (by taint_decide) (by taint_decide)) h

end VG.Proof.MlKem1024.X86.KeyGen
