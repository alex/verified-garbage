import VerifiedGarbage.Proof.MlKem.X86.KeyGenG
import VerifiedGarbage.Proof.MlKem.X86.Cbd
import VerifiedGarbage.Proof.MlKem.X86.Ntt

/-!
# ML-KEM on x86 (32-bit): `ŝ` and `ê` in key generation

`kgPrf L N` computes `NTT(SamplePolyCBD₂(PRF₂(σ, N)))` into `scratch[1024N]`
(`prf_piece`), and the `2k` of them take `P 0` to `P (2k)` (`prfs_piece`).
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad shakeSuffix)

variable {L : KemLay}

/-- `P N` holds after a block or call whose frame is apart from what it states. -/
theorem P.keep {N : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (h₁ : (Y L).apart (bACC L) bs = true) (h₂ : (Y L).apart (bRho L) bs = true)
    (h₃ : (Y L).apart (bSig L) bs = true) (h₄ : ∀ j < N, (Y L).apart (bSE j) bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : P L N s₀ s) (c : Ctx (Y L) s₀ s') : P L N s₀ s' :=
  ⟨c, by rw [keepW hp hM h₁ fr]; exact h.acc, by rw [keepBytes hp hM h₂ fr]; exact h.rho,
    by rw [keepBytes hp hM h₃ fr]; exact h.sig, fun j hj => keepPoly hp hM (h₄ j hj) fr (h.se j hj)⟩

/-- `σ ‖ N` is stored. -/
structure Q1 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (bNB L)) 1 = [BitVec.ofNat 8 N]

/-- `PRF₂(σ, N)` is computed. -/
structure Q2 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  prf : bytesAt s.mem (Buf.addr s₀ (bPRF L)) 128 = prf 2 (KPke.kgSigma L.p (d s₀)) (BitVec.ofNat 8 N)

/-- `SamplePolyCBD₂(PRF₂(σ, N))` is computed. -/
structure Q3 (L : KemLay) (N : Nat) (s₀ s : State) : Prop extends P L N s₀ s where
  cbd : PolyIs s.mem (Buf.addr s₀ (bSE N)) (cbd (KPke.kgSigma L.p (d s₀)) N)

/-- The facts of the layout that `ŝ` and `ê` use. -/
class PrfOK (L : KemLay) : Prop where
  sig : (Y L).ok (bNB L) = true ∧ (Y L).ok (bSig L) = true
  nb : (Y L).apart (bACC L) [⟨3, L.kgRS + 64, 1⟩] = true ∧ (Y L).apart (bRho L) [⟨3, L.kgRS + 64, 1⟩] = true ∧
    (Y L).apart (bSig L) [⟨3, L.kgRS + 64, 1⟩] = true
  hash : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok (bSigN L) && (Y L).okW (bPRF L) &&
    (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep (bSigN L) ⟨3, L.kgST, 200⟩ &&
    (Y L).sep (bSigN L) ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ (bPRF L) &&
    (Y L).sep (bPRF L) ⟨3, L.kgWK, 640⟩) = true ∧
    (Y L).apart (bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true ∧
    (Y L).apart (bRho L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true ∧
    (Y L).apart (bSig L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true
  prf : ∀ N < 2 * L.p.k,
    (∀ j < N, (Y L).apart (bSE j) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, bPRF L] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [⟨3, L.kgRS + 64, 1⟩] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [bSE N] = true) ∧
    (∀ j < N, (Y L).apart (bSE j) [bSE N, bNS L] = true) ∧
    ((Y L).apart (bACC L) [bSE N] && (Y L).apart (bRho L) [bSE N] && (Y L).apart (bSig L) [bSE N]) = true ∧
    ((Y L).apart (bACC L) [bSE N, bNS L] && (Y L).apart (bRho L) [bSE N, bNS L] &&
      (Y L).apart (bSig L) [bSE N, bNS L]) = true ∧
    ((Y L).ok (bPRF L) && (Y L).okW (bSE N) && (Y L).sep (bPRF L) (bSE N)) = true ∧
    ((Y L).okW (bSE N) && (Y L).okW (bNS L) && (Y L).sep (bSE N) (bNS L)) = true

theorem sigN_split [PrfOK L] {s₀ : State} (hp : TPre (Y L) s₀) (m : Mem) :
    bytesAt m (Buf.addr s₀ (bSigN L)) 33 =
      bytesAt m (Buf.addr s₀ (bSig L)) 32 ++ bytesAt m (Buf.addr s₀ (bNB L)) 1 := by
  have e : Buf.addr s₀ (bNB L) = Buf.addr s₀ (bSig L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bNB L) PrfOK.sig.1, Buf.addr_eq hp (b := bSig L) PrfOK.sig.2, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  rw [e]
  exact bytesAt_add m (Buf.addr s₀ (bSig L)) 32 1

variable [GOK L] [PrfOK L]

/-- `ŝ[N]` or `ê[N - k]`. -/
theorem prf_piece (N : Nat) (hN : N < 2 * L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L N) (P L (N + 1)) (kgPrf L N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := PrfOK.prf N hN
  obtain ⟨b₁, b₂, b₃⟩ := PrfOK.nb (L := L)
  obtain ⟨c₁, c₂, c₃, c₄⟩ := PrfOK.hash (L := L)
  refine Piece.seq (B := Q1 L N) (st8_piece (Y := Y L) (L.kgRS + 64) N (GOK.rs (L := L)).2.2.2.1 (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (M := 0) (by rdecide) b₁ b₂ b₃ (fun j hj => a₂ j hj) (m' ▸ frW8 (Y := Y L)) h'
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 N]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    refine (ite_eq_left (rfl : Buf.addr s₀ (bNB L) = Buf.addr s₀ ⟨(Y L).sc, L.kgRS + 64, 1⟩)).trans ?_
    rw [BitVec.setWidth_ofNat_of_le (by decide)]
  refine Piece.seq (B := Q2 L N) (hash1_piece (Y := Y L) L.kgST L.kgWK 136 0x1f (bSigN L) (bPRF L) rate136 c₁
    (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ⟨?_, ?_⟩) ?_
  · exact h.keep hp (by rdecide) c₂ c₃ c₄ (fun j hj => a₁ j hj) fr h'
  · rw [out, sigN_split hp, h.sig, h.nb, show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32,
      prf_eq]
  refine Piece.seq (B := Q3 L N) (cbd2C_piece (Y := Y L) 3 L.kgPRF 3 (1024 * N) a₇ (by rdecide) (by yk_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨?_, ?_⟩) ?_
  · simp only [Bool.and_eq_true] at a₅
    exact h.keep hp (by rdecide) a₅.1.1 a₅.1.2 a₅.2 a₃ fr h'
  · rw [h.prf] at post; exact post
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 (1024 * N) 3 L.kgNS a₈ (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, h.cbd.1⟩) fun s₀ s s' hp h h' fr post => ?_
  simp only [Bool.and_eq_true] at a₆
  have k := h.keep hp (by rdecide) a₆.1.1 a₆.1.2 a₆.2 a₄ fr h'
  refine ⟨h', k.acc, k.rho, k.sig, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.se j hj
  · rw [h.cbd.2] at post; exact post

/-- The `2k` of them, then `c`. -/
theorem prfs_piece {B : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L (2 * L.p.k)) B c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L 0) B (seqs ((List.range (2 * L.p.k)).map (kgPrf L)) c) :=
  Piece.seqs0 (P := P L) (2 * L.p.k) prf_piece h

end VG.Proof.MlKem.X86.KeyGen
