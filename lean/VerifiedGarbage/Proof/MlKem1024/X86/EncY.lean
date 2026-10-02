import VerifiedGarbage.Proof.MlKem1024.X86.EncBase

/-!
# ML-KEM-1024 on x86 (32-bit): `ŷ` in K-PKE.Encrypt

`SamplePolyCBD₂(PRF₂(r, N))` into a polynomial, keeping what a predicate
states (`cbd_piece`); `ŷ[N]` (`y_piece`), and the start of `encrypt4`: `e4ACC`
set to 1 and the four `ŷ[N]` (`ys_piece`), which reach `P 4`.
-/

namespace VG.Proof.MlKem1024.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt shakeSuffix)

variable {Y : Lay} {lk : State → List Byte}

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`, keeping `Q`. -/
theorem cbd_piece (hS : SOK Y) {I : Inp} (N o : Nat) {Q : State → State → Prop}
    (hQ : ∀ s₀ s, Q s₀ s → Base Y I s₀ s)
    (hk : Keeps Y Q [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, ⟨Y.sc, o, 1024⟩] 72)
    (hc : (Y.ok (bPRF Y.sc) && Y.okW ⟨Y.sc, o, 1024⟩ && Y.sep (bPRF Y.sc) ⟨Y.sc, o, 1024⟩) = true)
    {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (e4KR + 64) N)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax (bPRF Y.sc) ++ ptrTo Y.sc .ecx ⟨Y.sc, o, 1024⟩)) h₂).isSome = true) :
    Piece (TPre Y) (TPub Y lk) Q
      (fun s₀ s => Q s₀ s ∧ PolyIs s.mem (Buf.addr s₀ ⟨Y.sc, o, 1024⟩) (cbd (rE I s₀) N)) (enc4Cbd Y.sc N o) := by
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (bN Y.sc)) 1 = [BitVec.ofNat 8 N])
    (st8_piece (Y := Y) (e4KR + 64) N (by sc_decide) t₁ (fun _ _ _ h => (hQ _ _ h).ctx)
      fun s₀ s s' hp h h' m' => ⟨hk.widen k88 (bs' := [⟨Y.sc, e4KR + 64, 1⟩]) (by simp) (Nat.zero_le _)
        s₀ s s' hp h h' (m' ▸ frW8), by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (bPRF Y.sc)) 128 = prf 2 (rE I s₀) (BitVec.ofNat 8 N))
    (hash1_piece (Y := Y) e4ST e4WK 136 0x1f (bRN Y.sc) (bPRF Y.sc) rate136 (by sc_decide) (by sc_decide)
      (by show 33 < 2 ^ 32; decide) (by show 128 < 2 ^ 32; decide) (by sc_taint) (by sc_taint) (by sc_taint)
      (by sc_taint)
      (fun _ _ _ h => (hQ _ _ h.1).ctx) fun s₀ s s' hp h h' fr out =>
        ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr, ?_⟩) ?_
  · rw [out, rn_split hS hp, (hQ _ _ h.1).kr, h.2,
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, prf_eq]
  exact cbd2C_piece (Y := Y) Y.sc e4PRF Y.sc o hc (by sc_decide) t₂ (fun _ _ _ h => (hQ _ _ h.1).ctx)
    fun s₀ s s' hp h h' fr post => ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr,
      by rw [h.2] at post; exact post⟩

/-- `e4ACC`. -/
abbrev accE (Y : Lay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (bACC Y.sc)) 32

/-- While `ŷ` is computed: `ŷ[j]` for `j < N`. -/
structure P (Y : Lay) (I : Inp) (N : Nat) (s₀ s : State) : Prop extends Base Y I s₀ s where
  acc : accE Y s₀ s = 1
  y : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)

theorem P.keep {I : Inp} {N : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (h₁ : inApart Y bs = true) (h₂ : Y.apart (bACC Y.sc) bs = true)
    (h₃ : ∀ j < N, Y.apart (bY Y.sc j) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : P Y I N s₀ s)
    (c : Ctx Y s₀ s') : P Y I N s₀ s' :=
  ⟨h.toBase.keep hp hM h₁ fr c, (keepW hp hM h₂ fr).trans h.acc,
    fun j hj => keepPoly hp hM (h₃ j hj) fr (h.y j hj)⟩

theorem apart_y (hS : SOK Y) : ∀ N < 4,
    inApart Y [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bY Y.sc N] = true ∧
    Y.apart (bACC Y.sc) [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bY Y.sc N] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bN Y.sc, bST Y.sc, bWK Y.sc, bPRF Y.sc, bY Y.sc N] = true) ∧
    (Y.ok (bPRF Y.sc) && Y.okW (bY Y.sc N) && Y.sep (bPRF Y.sc) (bY Y.sc N)) = true ∧
    (Y.okW (bY Y.sc N) && Y.okW (bNS Y.sc) && Y.sep (bY Y.sc N) (bNS Y.sc)) = true ∧
    inApart Y [bY Y.sc N, bNS Y.sc] = true ∧ Y.apart (bACC Y.sc) [bY Y.sc N, bNS Y.sc] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bY Y.sc N, bNS Y.sc] = true) := by sc_decide

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
theorem y_piece (hS : SOK Y) {I : Inp} (N : Nat) (hN : N < 4) {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esi]) (.block (st8 (e4KR + 64) N)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax (bPRF Y.sc) ++ ptrTo Y.sc .ecx (bY Y.sc N))) h₂).isSome = true)
    (t₃ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax (bY Y.sc N) ++ ptrTo Y.sc .ecx (bNS Y.sc))) h₃).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (P Y I N) (P Y I (N + 1)) (enc4YC Y.sc N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := apart_y hS N hN
  refine Piece.seq (cbd_piece hS N (1024 * N) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => h.keep hp hS.le a₁ a₂ a₃ fr c) a₄ t₁ t₂) ?_
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack Y.sc (1024 * N) Y.sc e4NS a₅ hS.le t₃
    (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.1.keep hp hS.le a₆ a₇ a₈ fr h'
  refine ⟨k.toBase, k.acc, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.y j hj
  · rw [h.2.2] at post; exact post

/-- `e4ACC ← 1`, the four `ŷ[N]`, then `c`. -/
theorem ys_piece (hS : SOK Y) {I : Inp} {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre Y) (TPub Y lk) (P Y I 4) Q c) :
    Piece (TPre Y) (TPub Y lk) (Base Y I) Q
      (.seq (.block [.mov .eax (.imm 1), .store (at_ .esi e4ACC) .eax]) <|
        .seq (enc4YC Y.sc 0) <| .seq (enc4YC Y.sc 1) <| .seq (enc4YC Y.sc 2) <| .seq (enc4YC Y.sc 3) c) := by
  refine Piece.seq (B := P Y I 0) (st32_piece (Y := Y) e4ACC 1 (by sc_decide) (by sc_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (M := 0) hS.le (by sc_decide) (m' ▸ frW32) h',
        by show s'.mem.readW _ 32 = _; rw [m']; exact Mem.readW_writeW_self32 _ _ _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩) ?_
  exact .seq (y_piece hS 0 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) <|
    .seq (y_piece hS 1 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) <|
    .seq (y_piece hS 2 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) <|
    .seq (y_piece hS 3 (by decide) (by sc_taint) (by sc_taint) (by sc_taint)) h

end VG.Proof.MlKem1024.X86.Enc
