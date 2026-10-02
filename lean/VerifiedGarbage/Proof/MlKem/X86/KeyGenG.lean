import VerifiedGarbage.Proof.MlKem.X86.KeyGenPre
import VerifiedGarbage.Proof.MlKem.X86.TopKeep

/-!
# ML-KEM on x86 (32-bit): the start of key generation

`esi = scratch`, the word `kgACC` set to 1, and `ρ ‖ σ = G(d ‖ k)` at `kgRS`
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

section
variable (L : KemLay)
abbrev bT : Buf := ⟨3, L.kgT, 1024⟩
abbrev bA : Buf := ⟨3, L.kgA, 1024⟩
abbrev bP : Buf := ⟨3, L.kgP, 1024⟩
abbrev bNS : Buf := ⟨3, L.kgNS, 1024⟩
abbrev bSS : Buf := ⟨3, L.kgSS, 2048⟩
abbrev bST : Buf := ⟨3, L.kgST, 200⟩
abbrev bWK : Buf := ⟨3, L.kgWK, 640⟩
abbrev bRS : Buf := ⟨3, L.kgRS, 64⟩
abbrev bRho : Buf := ⟨3, L.kgRS, 32⟩
abbrev bSig : Buf := ⟨3, L.kgRS + 32, 32⟩
abbrev bNB : Buf := ⟨3, L.kgRS + 64, 1⟩
abbrev bPRF : Buf := ⟨3, L.kgPRF, 128⟩
abbrev bACC : Buf := ⟨3, L.kgACC, 4⟩

/-- `σ ‖ N`, `PRF`'s input. -/
abbrev bSigN : Buf := ⟨3, L.kgRS + 32, 33⟩
end

section
variable (L : KemLay) (s₀ : State)
/-- `ŝ[j]` (`j < k`) or `ê[j - k]`. -/
abbrev seP (j : Nat) : Poly := ntt (cbd (KPke.kgSigma L.p (d s₀)) j)
end

/-- The facts of the layout that the start of key generation uses. -/
class GOK (L : KemLay) : Prop where
  rs : (Y L).ok (bSig L) = true ∧ (Y L).ok (bRS L) = true ∧ (Y L).okW (bACC L) = true ∧
    (Y L).okW (bNB L) = true ∧ (Y L).apart (bACC L) [⟨3, L.kgRS + 64, 1⟩] = true
  g : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok ⟨0, 0, 32⟩ &&
    (Y L).ok ⟨3, L.kgRS + 64, 1⟩ && (Y L).okW ⟨3, L.kgRS, 64⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgST, 200⟩ && (Y L).sep ⟨0, 0, 32⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgST, 200⟩ && (Y L).sep ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgWK, 640⟩ &&
    (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgRS, 64⟩ && (Y L).sep ⟨3, L.kgRS, 64⟩ ⟨3, L.kgWK, 640⟩) = true ∧
    (Y L).apart (bACC L) [⟨3, L.kgST, 200⟩, ⟨3, L.kgWK, 640⟩, ⟨3, L.kgRS, 64⟩] = true
variable {L : KemLay}

/-- While `ŝ` and `ê` are computed: `ŝ[j]` or `ê[j - k]` for `j < N`. -/
structure P (L : KemLay) (N : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (bACC L)) 32 = 1
  rho : bytesAt s.mem (Buf.addr s₀ (bRho L)) 32 = KPke.kgRho L.p (d s₀)
  sig : bytesAt s.mem (Buf.addr s₀ (bSig L)) 32 = KPke.kgSigma L.p (d s₀)
  se : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bSE j)) (seP L s₀ j)

/-- After `kgACC` is set. -/
structure I1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  acc : s.mem.readW (Buf.addr s₀ (bACC L)) 32 = 1

/-- After the `k` of `G`'s input is stored. -/
structure I2 (L : KemLay) (s₀ s : State) : Prop extends I1 L s₀ s where
  nb : bytesAt s.mem (Buf.addr s₀ (bNB L)) 1 = [BitVec.ofNat 8 L.p.k]

theorem rs_split [GOK L] {s₀ : State} (hp : TPre (Y L) s₀) {m : Mem} {o : List Byte}
    (h : bytesAt m (Buf.addr s₀ (bRS L)) 64 = o) :
    bytesAt m (Buf.addr s₀ (bRho L)) 32 = o.take 32 ∧ bytesAt m (Buf.addr s₀ (bSig L)) 32 = o.drop 32 := by
  have e₁ : Buf.addr s₀ (bRho L) = Buf.addr s₀ (bRS L) := rfl
  have e₂ : Buf.addr s₀ (bSig L) = Buf.addr s₀ (bRS L) + BitVec.ofNat 64 32 := by
    rw [Buf.addr_eq hp (b := bSig L) GOK.rs.1, Buf.addr_eq hp (b := bRS L) GOK.rs.2.1, BitVec.add_assoc,
      ← BitVec.ofNat_add]
  refine ⟨by rw [e₁, ← bytesAt_take _ _ (show 32 ≤ 64 by decide), h], ?_⟩
  rw [e₂, ← h, bytesAt_drop _ _ (show 32 ≤ 64 by decide)]

/-- The start, then `c`. -/
theorem start_piece [GOK L] {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (P L 0) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 32))]) <|
        .seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.kgACC) .eax]) <|
        .seq (.block (st8 (L.kgRS + 64) L.p.k)) <|
        .seq (hash2 3 L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩) c) := by
  obtain ⟨-, -, o₃, o₄, a₁⟩ := GOK.rs (L := L)
  obtain ⟨g₁, g₂⟩ := GOK.g (L := L)
  refine Piece.seq (ldsc_piece (Y := Y L) (by yk_taint)) ?_
  refine Piece.seq (B := I1 L) (st32_piece (Y := Y L) L.kgACC 1 o₃ (by taint_rfl) (fun _ _ _ h => h)
    fun s₀ s s' hp _ h' m' => ⟨h', by rw [m']; exact Mem.readW_writeW_self32 _ _ _⟩) ?_
  refine Piece.seq (B := I2 L) (st8_piece (Y := Y L) (L.kgRS + 64) L.p.k o₄ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' => ⟨⟨h', ?_⟩, ?_⟩) ?_
  · rw [← h.acc, m']; exact keepW hp (N := 0) (by rdecide) a₁ (frW8 (Y := Y L))
  · rw [m']
    refine bytesAt_eq (L := [BitVec.ofNat 8 L.p.k]) rfl fun i hi => ?_
    obtain rfl : i = 0 := by omega
    simp only [BitVec.add_zero, writeW8_apply, List.getElem_cons_zero]
    exact (ite_eq_left (rfl : Buf.addr s₀ (bNB L) = Buf.addr s₀ ⟨(Y L).sc, L.kgRS + 64, 1⟩)).trans
      (by rw [BitVec.setWidth_ofNat_of_le (by decide)])
  refine Piece.seq (hash2_piece (Y := Y L) L.kgST L.kgWK 72 6 ⟨0, 0, 32⟩ ⟨3, L.kgRS + 64, 1⟩ ⟨3, L.kgRS, 64⟩
    rate72 g₁ (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr out => ?_) hc
  have hd : bytesAt s.mem (Buf.addr s₀ ⟨0, 0, 32⟩) 32 = d s₀ :=
    h.ctx.roBytes hp (b := ⟨0, 0, 32⟩) (by rdecide) rfl
  rw [hd, h.nb, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq] at out
  obtain ⟨r₁, r₂⟩ := rs_split hp out
  refine ⟨h', ?_, r₁, r₂, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  rw [← h.acc]; exact keepW hp (by rdecide) g₂ fr

end VG.Proof.MlKem.X86.KeyGen
