import VerifiedGarbage.Proof.MlKem.X86.EncBase

/-!
# ML-KEM on x86 (32-bit): `ŷ` in K-PKE.Encrypt

`SamplePolyCBD₂(PRF₂(r, N))` into a polynomial, keeping what a predicate
states (`cbd_piece`); `ŷ[N]` (`y_piece`), and the start of `encrypt`: `eACC`
set to 1 and the `k` polynomials `ŷ[N]` (`ys_piece`), which reach `P k`.
-/

namespace VG.Proof.MlKem.X86.Enc

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt shakeSuffix)

variable {L : KemLay} {Y : Lay} {lk : State → List Byte}

section
variable [BaseOK L]

/-- `SamplePolyCBD₂(PRF₂(r, N))` into `scratch + o`, keeping `Q`. -/
theorem cbd_piece (hS : SOK L Y) {I : Inp} (N o : Nat) {Q : State → State → Prop}
    (hQ : ∀ s₀ s, Q s₀ s → Base L Y I s₀ s)
    (hk : Keeps Y Q [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, ⟨Y.sc, o, 1024⟩] 72)
    (hc : (Y.ok (bPRF L Y.sc) && Y.okW ⟨Y.sc, o, 1024⟩ && Y.sep (bPRF L Y.sc) ⟨Y.sc, o, 1024⟩) = true) :
    Piece (TPre Y) (TPub Y lk) Q
      (fun s₀ s => Q s₀ s ∧ PolyIs s.mem (Buf.addr s₀ ⟨Y.sc, o, 1024⟩) (cbd (rE I s₀) N)) (encCbd L Y.sc N o) := by
  have k88 : 72 + 16 ≤ Y.stk := hS.le
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧ bytesAt s.mem (Buf.addr s₀ (bN L Y.sc)) 1 = [BitVec.ofNat 8 N])
    (st8_piece (Y := Y) (L.eKR + 64) N (BaseOK.n hS) (by taint_rfl) (fun _ _ _ h => (hQ _ _ h).ctx)
      fun s₀ s s' hp h h' m' => ⟨hk.widen k88 (bs' := [⟨Y.sc, L.eKR + 64, 1⟩]) (by simp) (Nat.zero_le _)
        s₀ s s' hp h h' (m' ▸ frW8), by rw [m']; exact st8_byte _ _ _⟩) ?_
  refine Piece.seq (B := fun s₀ s => Q s₀ s ∧
      bytesAt s.mem (Buf.addr s₀ (bPRF L Y.sc)) 128 = prf 2 (rE I s₀) (BitVec.ofNat 8 N))
    (hash1_piece (Y := Y) L.eST L.eWK 136 0x1f (bRN L Y.sc) (bPRF L Y.sc) rate136 (BaseOK.hash hS) hS.le
      (by show 33 < 2 ^ 32; decide) (by show 128 < 2 ^ 32; decide) (by taint_rfl) (by sc_taint) (by sc_taint) (by sc_taint)
      (fun _ _ _ h => (hQ _ _ h.1).ctx) fun s₀ s s' hp h h' fr out =>
        ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr, ?_⟩) ?_
  · rw [out, rn_split hS hp, (hQ _ _ h.1).kr, h.2,
      show (BitVec.ofNat 32 0x1f).setWidth 8 = shakeSuffix from shakeSuffix32, prf_eq]
  exact cbd2C_piece (Y := Y) Y.sc L.ePRF Y.sc o hc hS.le (by sc_taint) (fun _ _ _ h => (hQ _ _ h.1).ctx)
    fun s₀ s s' hp h h' fr post => ⟨hk.widen k88 (by simp) (by decide) s₀ s s' hp h.1 h' fr,
      by rw [h.2] at post; exact post⟩

end

/-- `eACC`. -/
abbrev accE (L : KemLay) (Y : Lay) (s₀ s : State) : BitVec 32 := s.mem.readW (Buf.addr s₀ (bACC L Y.sc)) 32

/-- While `ŷ` is computed: `ŷ[j]` for `j < N`. -/
structure P (L : KemLay) (Y : Lay) (I : Inp) (N : Nat) (s₀ s : State) : Prop extends Base L Y I s₀ s where
  acc : accE L Y s₀ s = 1
  y : ∀ j < N, PolyIs s.mem (Buf.addr s₀ (bY Y.sc j)) (yE I s₀ j)

theorem P.keep {I : Inp} {N : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ Y.stk) (h₁ : inApart L Y bs = true) (h₂ : Y.apart (bACC L Y.sc) bs = true)
    (h₃ : ∀ j < N, Y.apart (bY Y.sc j) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : P L Y I N s₀ s)
    (c : Ctx Y s₀ s') : P L Y I N s₀ s' :=
  ⟨h.toBase.keep hp hM h₁ fr c, (keepW hp hM h₂ fr).trans h.acc,
    fun j hj => keepPoly hp hM (h₃ j hj) fr (h.y j hj)⟩

/-- The facts of the layout that `ys_piece` uses. -/
class YOK (L : KemLay) : Prop where
  y : ∀ {Y : Lay}, SOK L Y → ∀ N < L.p.k,
    inApart L Y [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true ∧
    Y.apart (bACC L Y.sc) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bN L Y.sc, bST L Y.sc, bWK L Y.sc, bPRF L Y.sc, bY Y.sc N] = true) ∧
    (Y.ok (bPRF L Y.sc) && Y.okW (bY Y.sc N) && Y.sep (bPRF L Y.sc) (bY Y.sc N)) = true ∧
    (Y.okW (bY Y.sc N) && Y.okW (bNS L Y.sc) && Y.sep (bY Y.sc N) (bNS L Y.sc)) = true ∧
    inApart L Y [bY Y.sc N, bNS L Y.sc] = true ∧ Y.apart (bACC L Y.sc) [bY Y.sc N, bNS L Y.sc] = true ∧
    (∀ j < N, Y.apart (bY Y.sc j) [bY Y.sc N, bNS L Y.sc] = true)
  acc : ∀ {Y : Lay}, SOK L Y → Y.okW (bACC L Y.sc) = true ∧ inApart L Y [bACC L Y.sc] = true

variable [BaseOK L] [YOK L]

/-- `ŷ[N] = NTT(SamplePolyCBD₂(PRF₂(r, N)))`. -/
theorem y_piece (hS : SOK L Y) {I : Inp} (N : Nat) (hN : N < L.p.k) :
    Piece (TPre Y) (TPub Y lk) (P L Y I N) (P L Y I (N + 1)) (encYC L Y.sc N) := by
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆, a₇, a₈⟩ := YOK.y hS N hN
  refine Piece.seq (cbd_piece hS N (1024 * N) (fun _ _ h => h.toBase)
    (fun s₀ s s' hp h c fr => h.keep hp hS.le a₁ a₂ a₃ fr c) a₄) ?_
  refine inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack Y.sc (1024 * N) Y.sc L.eNS a₅ hS.le (by sc_taint)
    (fun _ _ _ h => ⟨h.1.ctx, h.2.1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.1.keep hp hS.le a₆ a₇ a₈ fr h'
  refine ⟨k.toBase, k.acc, fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · exact k.y j hj
  · rw [h.2.2] at post; exact post

/-- `eACC ← 1`, the `k` polynomials `ŷ[N]`, then `c`. -/
theorem ys_piece (hS : SOK L Y) {I : Inp} {Q : State → State → Prop} {c : Prog isa}
    (h : Piece (TPre Y) (TPub Y lk) (P L Y I L.p.k) Q c) :
    Piece (TPre Y) (TPub Y lk) (Base L Y I) Q
      (.seq (.block [.mov .eax (.imm 1), .store (at_ .esi L.eACC) .eax]) <|
        seqs ((List.range L.p.k).map (encYC L Y.sc)) c) := by
  obtain ⟨o₁, o₂⟩ := YOK.acc hS
  refine Piece.seq (B := P L Y I 0) (st32_piece (Y := Y) L.eACC 1 o₁ (by taint_rfl)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' m' =>
      ⟨h.keep hp (M := 0) hS.le o₂ (m' ▸ frW32) h',
        by show s'.mem.readW _ 32 = _; rw [m']; exact Mem.readW_writeW_self32 _ _ _,
        fun j hj => absurd hj (Nat.not_lt_zero _)⟩) ?_
  exact Piece.seqs0 L.p.k (fun N hN => y_piece hS N hN) h

end VG.Proof.MlKem.X86.Enc
