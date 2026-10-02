import VerifiedGarbage.Proof.MlKem.X86.KeyGenPre
import VerifiedGarbage.Proof.MlKem.X86.TopKeep

/-!
# ML-KEM-768 on x86 (32-bit): the start of `vg_mlkem768_keygen`

`esi = scratch`, the word `kgACC` set to 1, and `ρ ‖ σ = G(d ‖ 3)` at `kgRS`
(`start_piece`), which is `P 0`: the state of the loop over `N` that computes
`ŝ` and `ê`.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt Repr stateAt squeezeFrom absorb pad sha3_512 sha3Suffix shakeSuffix)

/-! ## Buffers -/

abbrev bSE (j : Nat) : Buf := ⟨3, 1024 * j, 1024⟩
abbrev bT : Buf := ⟨3, Impl.MlKem.X86.kgT, 1024⟩
abbrev bA : Buf := ⟨3, kgA, 1024⟩
abbrev bP : Buf := ⟨3, kgP, 1024⟩
abbrev bNS : Buf := ⟨3, kgNS, 1024⟩
abbrev bSS : Buf := ⟨3, kgSS, 2048⟩
abbrev bST : Buf := ⟨3, kgST, 200⟩
abbrev bWK : Buf := ⟨3, kgWK, 640⟩
abbrev bRS : Buf := ⟨3, kgRS, 64⟩
abbrev bRho : Buf := ⟨3, kgRS, 32⟩
abbrev bSig : Buf := ⟨3, kgRS + 32, 32⟩
abbrev bNB : Buf := ⟨3, kgRS + 64, 1⟩
abbrev bPRF : Buf := ⟨3, kgPRF, 128⟩
abbrev bACC : Buf := ⟨3, kgACC, 4⟩

/-- `σ ‖ N`, `PRF`'s input. -/
abbrev bSigN : Buf := ⟨3, kgRS + 32, 33⟩

section
variable (s₀ : State)
/-- `ŝ[j]` (`j < 3`) or `ê[j - 3]`. -/
abbrev seP (j : Nat) : Poly := ntt (cbd (kgSigma (d s₀)) j)
end

/-- While `ŝ` and `ê` are computed: `ŝ[j]` or `ê[j - 3]` for `j < N`. -/
structure P (N : Nat) (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  acc : s.mem.readW (Buf.addr s₀ bACC) 32 = 1
  rho : bytesAt s.mem (Buf.addr s₀ bRho) 32 = kgRho (d s₀)
  sig : bytesAt s.mem (Buf.addr s₀ bSig) 32 = kgSigma (d s₀)
  se : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP s₀ j)

/-- After `kgACC` is set. -/
structure I1 (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  acc : s.mem.readW (Buf.addr s₀ bACC) 32 = 1

/-- After the `3` of `G`'s input is stored. -/
structure I2 (s₀ s : State) : Prop extends I1 s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ bNB) 1 = [BitVec.ofNat 8 3]

theorem rs_split {s₀ : State} (hp : TPre Y s₀) {m : Mem} {o : List Byte}
    (h : bytesAt m (Buf.addr s₀ bRS) 64 = o) :
    bytesAt m (Buf.addr s₀ bRho) 32 = o.take 32 ∧ bytesAt m (Buf.addr s₀ bSig) 32 = o.drop 32 := by
  have e₁ : Buf.addr s₀ bRho = Buf.addr s₀ bRS := rfl
  have e₂ : Buf.addr s₀ bSig = Buf.addr s₀ bRS + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bSig) (by decide), Buf.addr_eq hp (b := bRS) (by decide), BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine ⟨by rw [e₁, ← bytesAt_take _ _ (show 32 ≤ 64 by decide), h], ?_⟩
  rw [e₂, ← h, bytesAt_drop _ _ (show 32 ≤ 64 by decide)]

/-- The start, then `c`. -/
theorem start_piece {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (P 0) Q c) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
        .seq (.block [.mov .eax (.imm 1), .store (at_ .esi kgACC) .eax]) <|
        .seq (.block (st8 (kgRS + 64) 3)) <|
        .seq (hash2 3 kgST kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, kgRS + 64, 1⟩ ⟨3, kgRS, 64⟩) c) := by
  refine Piece.seq (ldsc_piece (Y := Y) (by taint_decide)) ?_
  refine Piece.seq (B := I1) (st32_piece (Y := Y) kgACC 1 (by decide) (by taint_decide) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := I2) (st8_piece (Y := Y) (kgRS + 64) 3 (by decide) (by taint_decide)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨⟨h', ?_⟩, ?_⟩) ?_
  · rw [← h.acc, m']; exact keepW hp (by decide) (by decide) frW8
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 3]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    exact (ite_eq_left (rfl : Buf.addr s₀ bNB = Buf.addr s₀ ⟨Y.sc, kgRS + 64, 1⟩)).trans (by decide)
  refine Piece.seq (hash2_piece (Y := Y) kgST kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, kgRS + 64, 1⟩ ⟨3, kgRS, 64⟩ rate72
    (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr out => ?_) hc
  have hd : bytesAt s.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32 = d s₀ := h.ctx.roBytes hp (b := ⟨0, 0, 32⟩) (by decide) rfl
  rw [hd, h.nb, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq] at out
  obtain ⟨r₁, r₂⟩ := rs_split hp out
  refine ⟨h', ?_, r₁, r₂, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [← h.acc]; exact keepW hp (by decide) (by decide) fr

end VG.Proof.MlKem.X86.KeyGen
