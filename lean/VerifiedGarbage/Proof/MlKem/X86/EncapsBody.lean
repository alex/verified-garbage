import VerifiedGarbage.Proof.MlKem.X86.EncV
import VerifiedGarbage.Impl.MlKem.X86.Encaps

/-!
# ML-KEM on x86 (32-bit): the body of encapsulation

The layout of the arguments (`Y L`: `ek`, `m`, `key`, `ct`, `scratch`, and
the 88 bytes of stack). `ek` and `m` are copied into `scratch`, `H(ek)` and
`G(m ‖ H(ek))` hashed (`start_piece`), the ciphertext computed
(`Enc.encrypt_piece`), and `K` and the ciphertext copied out (`fin_piece`).
If every `SampleNTT` succeeded, K-PKE.Encrypt succeeds with the matrix sampled
within one bound on their iterations (`KPke.kpkeEncrypt_some`); if one failed
within `minIterations`, it fails with that bound (`KPke.kpkeEncrypt_none`)
(`post`). Each parameter set's contract implies `TPre (Y L)` and its public
data `TPub (Y L) (lk L)` (`Proof/MlKem/X86/Encaps.lean` for ML-KEM-768).
-/

namespace VG.Proof.MlKem.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512 sha3Suffix)

/-- `ek` and `m` (read), `key`, `ct` and `scratch` (written); 88 bytes of stack. -/
def Y (L : KemLay) : Lay :=
  ⟨[(L.p.ekLen, false), (32, false), (32, true), (L.p.ctLen, true), (L.scratch, true)], 4, 88⟩

section
variable (L : KemLay) (s₀ : State)
/-- `ek` (irreducible, so that elaboration never evaluates its bytes). -/
@[irreducible] def ek : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.ekLen⟩) L.p.ekLen
/-- `m`. -/
@[irreducible] def msg : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32
/-- What encaps may leak: `ρ`. -/
abbrev lk : List Byte := ekRho L.p (ek L s₀)
/-- `G(m ‖ H(ek))`, as 64 bytes. -/
@[irreducible] def kr : List Byte := sha3_512 (msg s₀ ++ H (ek L s₀))
end

theorem ek_eq (L : KemLay) (s₀ : State) : ek L s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, L.p.ekLen⟩) L.p.ekLen := by
  unfold ek; rfl
theorem msg_eq (s₀ : State) : msg s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 := by unfold msg; rfl
theorem kr_eq (L : KemLay) (s₀ : State) : kr L s₀ = sha3_512 (msg s₀ ++ H (ek L s₀)) := by unfold kr; rfl

/-- The inputs of K-PKE.Encrypt. -/
abbrev I (L : KemLay) : Enc.Inp := ⟨ek L, msg, kr L⟩

theorem hS (L : KemLay) : Enc.SOK L (Y L) := ⟨of_decide_eq_true rfl, rfl, rfl, rfl⟩

theorem hρ (L : KemLay) : Enc.RhoPub L (Y L) (lk L) (I L) := fun _ _ _ _ hq => hq.2.2

theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

/-! ## The inputs of K-PKE.Encrypt -/

/-- `H(ek)`. -/
abbrev bH (L : KemLay) : Buf := ⟨(Y L).sc, L.eH, 32⟩

/-- The facts of the layout that encapsulation uses. -/
class EncapsOK (L : KemLay) : Prop where
  ekc : ((Y L).ok ⟨0, 0, L.p.ekLen⟩ && (Y L).okW ⟨(Y L).sc, L.eEK, L.p.ekLen⟩ &&
    (Y L).sep ⟨0, 0, L.p.ekLen⟩ ⟨(Y L).sc, L.eEK, L.p.ekLen⟩) = true
  mc : ((Y L).ok ⟨1, 0, 32⟩ && (Y L).okW ⟨(Y L).sc, L.eM, 32⟩ && (Y L).sep ⟨1, 0, 32⟩ ⟨(Y L).sc, L.eM, 32⟩) = true
  ek4 : 4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ekLen < 2 ^ 32
  ct4 : 4 * (L.p.ctLen / 4) = L.p.ctLen ∧ 0 < L.p.ctLen / 4 ∧ L.p.ctLen / 4 < 2 ^ 30
  aEM : (Y L).apart (Enc.bEK L (Y L).sc) [⟨(Y L).sc, L.eM, 32⟩] = true
  hh : ((Y L).okW ⟨(Y L).sc, L.eST, 200⟩ && (Y L).okW ⟨(Y L).sc, L.eWK, 640⟩ && (Y L).ok (Enc.bEK L (Y L).sc) && (Y L).okW (bH L) &&
    (Y L).sep ⟨(Y L).sc, L.eST, 200⟩ ⟨(Y L).sc, L.eWK, 640⟩ && (Y L).sep (Enc.bEK L (Y L).sc) ⟨(Y L).sc, L.eST, 200⟩ &&
    (Y L).sep (Enc.bEK L (Y L).sc) ⟨(Y L).sc, L.eWK, 640⟩ && (Y L).sep ⟨(Y L).sc, L.eST, 200⟩ (bH L) &&
    (Y L).sep (bH L) ⟨(Y L).sc, L.eWK, 640⟩) = true
  aH : (Y L).apart (Enc.bEK L (Y L).sc) [⟨(Y L).sc, L.eST, 200⟩, ⟨(Y L).sc, L.eWK, 640⟩, bH L] = true ∧
    (Y L).apart (Enc.bM L (Y L).sc) [⟨(Y L).sc, L.eST, 200⟩, ⟨(Y L).sc, L.eWK, 640⟩, bH L] = true
  g : ((Y L).okW ⟨(Y L).sc, L.eST, 200⟩ && (Y L).okW ⟨(Y L).sc, L.eWK, 640⟩ && (Y L).ok (Enc.bM L (Y L).sc) && (Y L).ok (bH L) &&
    (Y L).okW (Enc.bKR L (Y L).sc) && (Y L).sep ⟨(Y L).sc, L.eST, 200⟩ ⟨(Y L).sc, L.eWK, 640⟩ &&
    (Y L).sep (Enc.bM L (Y L).sc) ⟨(Y L).sc, L.eST, 200⟩ && (Y L).sep (Enc.bM L (Y L).sc) ⟨(Y L).sc, L.eWK, 640⟩ &&
    (Y L).sep (bH L) ⟨(Y L).sc, L.eST, 200⟩ && (Y L).sep (bH L) ⟨(Y L).sc, L.eWK, 640⟩ &&
    (Y L).sep ⟨(Y L).sc, L.eST, 200⟩ (Enc.bKR L (Y L).sc) && (Y L).sep (Enc.bKR L (Y L).sc) ⟨(Y L).sc, L.eWK, 640⟩) = true
  aG : (Y L).apart (Enc.bEK L (Y L).sc) [⟨(Y L).sc, L.eST, 200⟩, ⟨(Y L).sc, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true ∧
    (Y L).apart (Enc.bM L (Y L).sc) [⟨(Y L).sc, L.eST, 200⟩, ⟨(Y L).sc, L.eWK, 640⟩, Enc.bKR L (Y L).sc] = true
  key : ((Y L).ok ⟨(Y L).sc, L.eKR, 32⟩ && (Y L).okW ⟨2, 0, 32⟩ && (Y L).sep ⟨(Y L).sc, L.eKR, 32⟩ ⟨2, 0, 32⟩) = true
  ct : ((Y L).ok ⟨(Y L).sc, L.eC, L.p.ctLen⟩ && (Y L).okW ⟨3, 0, L.p.ctLen⟩ &&
    (Y L).sep ⟨(Y L).sc, L.eC, L.p.ctLen⟩ ⟨3, 0, L.p.ctLen⟩) = true
  dKey : Enc.safe L (Y L) [⟨2, 0, 32⟩] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨2, 0, 32⟩] = true
  dCt : Enc.safe L (Y L) [⟨3, 0, L.p.ctLen⟩] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [⟨3, 0, L.p.ctLen⟩] = true ∧
    (Y L).apart ⟨2, 0, 32⟩ [⟨3, 0, L.p.ctLen⟩] = true ∧ (Y L).apart (Enc.bACC L (Y L).sc) [⟨3, 0, L.p.ctLen⟩] = true
  acc : (Y L).ok (Enc.bACC L (Y L).sc) = true ∧ Enc.safe L (Y L) [] = true ∧
    (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ [] = true

/-- `sc_taint`, for code with `scratch` at `(Y L).sc`. -/
macro "ye_taint" : tactic => `(tactic| ((try simp only [show ∀ L, (Y L).sc = 4 from fun _ => rfl]); sc_taint))

variable {L : KemLay}

/-- After `ek` is copied. -/
structure Q1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK L (Y L).sc)) L.p.ekLen = ek L s₀

/-- After `m` is copied. -/
structure Q2 (L : KemLay) (s₀ s : State) : Prop extends Q1 L s₀ s where
  mc : bytesAt s.mem (Buf.addr s₀ (Enc.bM L (Y L).sc)) 32 = msg s₀

/-- After `H(ek)` is hashed. -/
structure Q3 (L : KemLay) (s₀ s : State) : Prop extends Q2 L s₀ s where
  hh : bytesAt s.mem (Buf.addr s₀ (bH L)) 32 = H (ek L s₀)

variable [EncapsOK L]

/-- The inputs of K-PKE.Encrypt, then `c`. -/
theorem start_piece {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Base L (Y L) (I L)) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
        .seq (copyW 4 ⟨0, 0, L.p.ekLen⟩ ⟨4, L.eEK, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, L.eM, 32⟩ 8) <|
        .seq (hash1 4 L.eST L.eWK 136 6 ⟨4, L.eEK, L.p.ekLen⟩ ⟨4, L.eH, 32⟩) <|
        .seq (hash2 4 L.eST L.eWK 72 6 ⟨4, L.eM, 32⟩ ⟨4, L.eH, 32⟩ ⟨4, L.eKR, 64⟩) c) := by
  obtain ⟨e₁, e₂, e₃, e₄⟩ := EncapsOK.ek4 (L := L)
  have ekc := EncapsOK.ekc (L := L)
  have hok : (Y L).ok ⟨0, 0, L.p.ekLen⟩ = true := by simp only [Bool.and_eq_true] at ekc; exact ekc.1.1
  have mc := EncapsOK.mc (L := L)
  have hokm : (Y L).ok ⟨1, 0, 32⟩ = true := by simp only [Bool.and_eq_true] at mc; exact mc.1.1
  refine Piece.seq (ldsc_piece (Y := Y L) (by ye_taint)) ?_
  refine Piece.seq (B := Q1 L) (copyW_piece' (Y := Y L) 0 0 4 L.eEK (L.p.ekLen / 4) L.p.ekLen e₁ e₂ e₃ ekc
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h) fun s₀ s s' hp h h' _ post => ⟨h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, L.eEK, L.p.ekLen⟩) L.p.ekLen = _
    rw [post, ek_eq]
    exact h.roBytes hp (b := ⟨0, 0, L.p.ekLen⟩) hok rfl
  refine Piece.seq (B := Q2 L) (copyW_piece (Y := Y L) 1 0 4 L.eM 8 (by rdecide) (by rdecide) mc
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by rdecide) EncapsOK.aEM (fr1 fr)]; exact h.ekc⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, L.eM, 4 * 8⟩) (4 * 8) = _
    rw [post, msg_eq]
    exact h.ctx.roBytes hp (b := ⟨1, 0, 32⟩) hokm rfl
  obtain ⟨a₁, a₂⟩ := EncapsOK.aH (L := L)
  refine Piece.seq (B := Q3 L) (hash1_piece (Y := Y L) L.eST L.eWK 136 6 (Enc.bEK L (Y L).sc) (bH L) rate136
    EncapsOK.hh (by rdecide) e₄ (by rdecide) (by taint_rfl) (by ye_taint) (by ye_taint) (by ye_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨⟨⟨h', by rw [keepBytes hp (by rdecide) a₁ fr]; exact h.ekc⟩,
        by rw [keepBytes hp (by rdecide) a₂ fr]; exact h.mc⟩, ?_⟩) ?_
  · rw [out, h.ekc, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← H_eq]
  obtain ⟨g₁, g₂⟩ := EncapsOK.aG (L := L)
  refine Piece.seq (hash2_piece (Y := Y L) L.eST L.eWK 72 6 (Enc.bM L (Y L).sc) (bH L) (Enc.bKR L (Y L).sc) rate72
    EncapsOK.g (by rdecide) (by rdecide) (by rdecide) (by rdecide) (by taint_rfl) (by ye_taint) (by ye_taint) (by ye_taint)
    (by ye_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by rdecide) g₁ fr]; exact h.ekc,
        by rw [keepBytes hp (by rdecide) g₂ fr]; exact h.mc, ?_⟩) hc
  rw [out, h.mc, h.hh, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq]
  exact (kr_eq L s₀).symm

/-! ## The outputs -/

omit [EncapsOK L] in
theorem done_keep {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ (Y L).stk)
    (hs : Enc.safe L (Y L) bs = true) (hc : (Y L).apart ⟨(Y L).sc, L.eC + 32 * L.p.du * L.p.k, 32 * L.p.dv⟩ bs = true)
    (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : Enc.Done L (Y L) (I L) s₀ s) (c : Ctx (Y L) s₀ s') :
    Enc.Done L (Y L) (I L) s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- After `K` is copied into `key`. -/
structure F1 (L : KemLay) (s₀ s : State) : Prop extends Enc.Done L (Y L) (I L) s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = (Encaps.kr L s₀).take 32

/-- After the ciphertext is copied into `ct`. -/
structure F2 (L : KemLay) (s₀ s : State) : Prop extends F1 L s₀ s where
  ct : Enc.accE L (Y L) s₀ s = 1 → bytesAt s.mem (Buf.addr s₀ ⟨3, 0, L.p.ctLen⟩) L.p.ctLen =
    KPke.ct L.p (Enc.aE L (I L) s₀) (Encaps.ek L s₀) (msg s₀) (Enc.rE (I L) s₀)

/-- After `eACC` is loaded, to be returned. -/
structure Fin (L : KemLay) (s₀ s : State) : Prop extends F2 L s₀ s where
  eax : s.gpr .eax = Enc.accE L (Y L) s₀ s

theorem fin_piece [Enc.VOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Enc.Done L (Y L) (I L)) (Fin L)
      (.seq (copyW 4 ⟨4, L.eKR, 32⟩ ⟨2, 0, 32⟩ 8) <|
        .seq (copyW 4 ⟨4, L.eC, L.p.ctLen⟩ ⟨3, 0, L.p.ctLen⟩ (L.p.ctLen / 4))
          (.block [.mov .eax (.mem (at_ .esi L.eACC))])) := by
  obtain ⟨c₁, c₂, c₃⟩ := EncapsOK.ct4 (L := L)
  obtain ⟨d₁, d₂⟩ := EncapsOK.dKey (L := L)
  obtain ⟨d₃, d₄, d₅, d₆⟩ := EncapsOK.dCt (L := L)
  obtain ⟨u₁, u₂, u₃⟩ := EncapsOK.acc (L := L)
  refine Piece.seq (B := F1 L) (copyW_piece (Y := Y L) 4 L.eKR 2 0 8 (by rdecide) (by rdecide) EncapsOK.key
    (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨done_keep hp (M := 0) (by rdecide) d₁ d₂ (fr1 fr) h h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨2, 0, 4 * 8⟩) (4 * 8) = _
    rw [post, show Encaps.kr L s₀ = (I L).kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]
    rfl
  refine Piece.seq (B := F2 L) (copyW_piece' (Y := Y L) 4 L.eC 3 0 (L.p.ctLen / 4) L.p.ctLen c₁ c₂ c₃
    EncapsOK.ct (by ye_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨done_keep hp (M := 0) (by rdecide) d₃ d₄ (fr1 fr) h.toDone h',
        by rw [keepBytes hp (N := 0) (by rdecide) d₅ (fr1 fr)]; exact h.key⟩, fun e => ?_⟩) ?_
  · have ea : Enc.accE L (Y L) s₀ s' = Enc.accE L (Y L) s₀ s := keepW hp (N := 0) (by rdecide) d₆ (fr1 fr)
    rw [post]
    exact Enc.ct_eq (hS L) hp h.toDone (ea ▸ e)
  exact ld32_piece (Y := Y L) L.eACC u₁ (by taint_rfl) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨⟨done_keep hp (bs := []) (M := 0) (by rdecide) u₂ u₃
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩, fun e₁ => by
        rw [m']; exact h.ct (by show s.mem.readW _ 32 = _; rw [← m']; exact e₁)⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece [CeOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L] [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = P0 s₀) (Fin L) (encapsBody L) :=
  start_piece <| .seq (Enc.encrypt_piece (hS L) (hρ L) hk) fin_piece

theorem piece [CeOK L] [Enc.BaseOK L] [Enc.YOK L] [Enc.EntOK L] [Enc.RowOK L] [Enc.VOK L] (hk : 0 < L.p.k)
    (hsp : NoSp (encapsBody L)) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin L s₀) s₀ s')
      (leaf (encapsBody L)) :=
  topLeaf hsp ((body_piece hk).mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

omit [EncapsOK L] in
/-- The postcondition, from the final state of the body. -/
theorem post (hη : L.p.η₁ = 2 ∧ L.p.η₂ = 2) {s₀ s : State} (h : Fin L s₀ s) :
    Outcome (fun iters => encapsInternal L.p iters (ek L s₀) (msg s₀)) (Enc.accE L (Y L) s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32, bytesAt s.mem (Buf.addr s₀ ⟨3, 0, L.p.ctLen⟩) L.p.ctLen) := by
  have er : Enc.rE (I L) s₀ = (G (msg s₀ ++ H (ek L s₀))).2 := by
    show (kr L s₀).drop 32 = _; rw [kr_eq]; rfl
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    have hk0 : 0 < L.p.k := Nat.pos_of_ne_zero fun h0 => by rw [h0] at hk; exact absurd hk (by rdecide)
    refine .inr ⟨e, ?_⟩
    show encapsInternal L.p minIterations (ek L s₀) (msg s₀) = none
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_none (i := k % L.p.k) (j := k / L.p.k) (Nat.mod_lt _ hk0)
      (Nat.div_lt_of_lt_mul hk) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    refine .inl ⟨e, M, ?_⟩
    show encapsInternal L.p M (ek L s₀) (msg s₀) = _
    rw [KPke.encapsInternal_eq, KPke.kpkeEncrypt_some hη hM, h.key, h.ct e, er, kr_eq]
    rfl

end VG.Proof.MlKem.X86.Encaps
