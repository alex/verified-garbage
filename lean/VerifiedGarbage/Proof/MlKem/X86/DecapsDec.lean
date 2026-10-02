import VerifiedGarbage.Proof.MlKem.X86.DecapsPre

/-!
# ML-KEM on x86 (32-bit): K-PKE.Decrypt in decapsulation

`w = Σ ŝ[i] ×_T NTT(u'[i])`, with `u'[i]` decoded and decompressed from `ct`
and `ŝ[i]` decoded from `dk` (`term0_piece`, `term_piece`), then `m' =
ByteEncode₁(Compress₁(v' - NTT⁻¹(w)))` (`decrypt_piece`), which is `mD`.
-/

namespace VG.Proof.MlKem.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (L : KemLay) (s₀ : State)
/-- `ŝ[i]`. -/
abbrev dS (i : Nat) : Poly := dcS (KPke.dkPke L.p (dk L s₀)) i
/-- `NTT(u'[i])`. -/
abbrev dU (i : Nat) : Poly := ntt (KPke.dcU L.p (ct L s₀) i)
/-- `ŝ[0] ×_T NTT(u'[0]) + … + ŝ[j - 1] ×_T NTT(u'[j - 1])`. -/
abbrev partD (j : Nat) : Poly := KPke.dotK (dS L s₀) (dU L s₀) j
end

section
variable (L : KemLay)
abbrev bA : Buf := ⟨3, L.eA, 1024⟩
abbrev bT : Buf := ⟨3, L.eT, 1024⟩
abbrev bW : Buf := ⟨3, L.eU, 1024⟩
abbrev bP : Buf := ⟨3, L.eP, 1024⟩
abbrev bE : Buf := ⟨3, L.eE, 1024⟩
abbrev bNS : Buf := ⟨3, L.eNS, 1024⟩
abbrev bM : Buf := ⟨3, L.eM, 32⟩
/-- `u'[i]` in `ct`. -/
abbrev bCU (i : Nat) : Buf := ⟨1, 32 * L.p.du * i, 32 * L.p.du⟩
/-- `v'` in `ct`. -/
abbrev bCV : Buf := ⟨1, 32 * L.p.du * L.p.k, 32 * L.p.dv⟩
end

/-- Before term `j`: and `w` so far, if `0 < j`. -/
structure D (L : KemLay) (j : Nat) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  w : 0 < j → Reduced s.mem (Buf.addr s₀ (bW L)) ∧ polyAt s.mem (Buf.addr s₀ (bW L)) = partD L s₀ j

variable {L : KemLay}

theorem D.keep {j : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hW : (Y L).apart (bW L) bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : D L j s₀ s) (c : Ctx (Y L) s₀ s') : D L j s₀ s' :=
  ⟨c, fun hj => ⟨keepRed hp hM hW fr (h.w hj).1, by rw [polyAt_congr (Top.keep hp hM hW fr)]; exact (h.w hj).2⟩⟩

/-- `u'[i]` is decoded, decompressed and in the NTT domain; `ŝ[i]` decoded. -/
structure D1 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (bA L)) (KPke.dcU L.p (ct L s₀) j)

structure D2 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ (bA L)) (dU L s₀ j)

structure D3 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D2 L j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ (bT L)) (dS L s₀ j)

structure D4 (L : KemLay) (j : Nat) (s₀ s : State) : Prop extends D L j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ (bP L)) (multiplyNTTs (dS L s₀ j) (dU L s₀ j))

/-- The facts of the layout that K-PKE.Decrypt uses. -/
class DecOK (L : KemLay) : Prop where
  ct : (Y L).ok ⟨1, 0, L.p.ctLen⟩ = true ∧ (Y L).ok ⟨0, 0, L.p.dkLen⟩ = true ∧
    32 * L.p.du * L.p.k + 32 * L.p.dv ≤ L.p.ctLen
  dec : ∀ i < L.p.k, (Y L).ok (bCU L i) = true ∧ (Y L).ok ⟨0, 384 * i, 384⟩ = true ∧
    ((Y L).ok (bCU L i) && (Y L).okW (bA L) && (Y L).sep (bCU L i) (bA L)) = true ∧
    ((Y L).ok ⟨0, 384 * i, 384⟩ && (Y L).okW (bT L) && (Y L).sep ⟨0, 384 * i, 384⟩ (bT L)) = true
  keep : (Y L).apart (bW L) [bA L] = true ∧ (Y L).apart (bW L) [bA L, bNS L] = true ∧
    ((Y L).okW (bA L) && (Y L).okW (bNS L) && (Y L).sep (bA L) (bNS L)) = true ∧
    (Y L).apart (bW L) [bT L] = true ∧ (Y L).apart (bA L) [bT L] = true ∧
    (Y L).apart (bW L) [bP L, bNS L] = true ∧
    ((Y L).okW (bW L) && (Y L).ok (bP L) && (Y L).sep (bW L) (bP L)) = true
  mul : ((Y L).okW (bW L) && (Y L).ok (bT L) && (Y L).ok (bA L) && (Y L).okW (bNS L) && (Y L).sep (bW L) (bT L) &&
    (Y L).sep (bW L) (bA L) && (Y L).sep (bW L) (bNS L) && (Y L).sep (bT L) (bNS L) &&
    (Y L).sep (bA L) (bNS L)) = true ∧
    ((Y L).okW (bP L) && (Y L).ok (bT L) && (Y L).ok (bA L) && (Y L).okW (bNS L) && (Y L).sep (bP L) (bT L) &&
    (Y L).sep (bP L) (bA L) && (Y L).sep (bP L) (bNS L) && (Y L).sep (bT L) (bNS L) &&
    (Y L).sep (bA L) (bNS L)) = true
  v : ((Y L).okW (bW L) && (Y L).okW (bNS L) && (Y L).sep (bW L) (bNS L)) = true ∧
    ((Y L).ok (bCV L) && (Y L).okW (bE L) && (Y L).sep (bCV L) (bE L)) = true ∧
    (Y L).ok (bCV L) = true ∧ (Y L).apart (bW L) [bE L] = true ∧
    ((Y L).okW (bE L) && (Y L).ok (bW L) && (Y L).sep (bE L) (bW L)) = true ∧
    ((Y L).ok (bE L) && (Y L).okW ⟨3, L.eM, 32 * 1⟩ && (Y L).sep (bE L) ⟨3, L.eM, 32 * 1⟩) = true

variable [DecOK L]

/-- The bytes of `ct[o : o + l]`. -/
theorem ct_slice {s₀ s : State} (hp : TPre (Y L) s₀) (h : Ctx (Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.ctLen)
    (hb : (Y L).ok ⟨1, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, o, l⟩) l = ((ct L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨1, o, l⟩) hb rfl, ct_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨1, o, l⟩) hb, Buf.addr_eq hp (b := ⟨1, 0, L.p.ctLen⟩) DecOK.ct.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- The bytes of `dk[o : o + l]`. -/
theorem dk_slice {s₀ s : State} (hp : TPre (Y L) s₀) (h : Ctx (Y L) s₀ s) {o l : Nat} (hl : o + l ≤ L.p.dkLen)
    (hb : (Y L).ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((dk L s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨0, o, l⟩) hb rfl, dk_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨0, o, l⟩) hb, Buf.addr_eq hp (b := ⟨0, 0, L.p.dkLen⟩) DecOK.ct.2.1, BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- `u'[i]` and `ŝ[i]`, then `c`. -/
theorem uS_piece [CeOK L] (j : Nat) (hj : j < L.p.k) {Q : State → State → Prop} {c : Prog isa}
    (hc : Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D3 L j) Q c) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L j) Q
      (.seq (ddK L 3 L.p.du (bCU L j) (bA L)) <| .seq (nttC 3 (bA L) (bNS L)) <|
        .seq (dec12C 3 ⟨0, 384 * j, 384⟩ (bT L)) c) := by
  obtain ⟨o₁, o₂, o₃, o₄⟩ := DecOK.dec j hj
  obtain ⟨k₁, k₂, k₃, k₄, k₅, -⟩ := DecOK.keep (L := L)
  refine Piece.seq (B := D1 L j) (ddK_piece (Y := Y L) L.p.du (.inl rfl) 1 (32 * L.p.du * j) 3 L.eA o₃ (by rdecide)
    (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨h.keep hp (by rdecide) k₁ fr h', ?_⟩) ?_
  · rw [ct_slice hp h.ctx ?_ o₁] at post
    · exact post
    · have := DecOK.ct (L := L)
      have : 32 * L.p.du * j + 32 * L.p.du ≤ 32 * L.p.du * L.p.k := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hj
      omega
  refine Piece.seq (B := D2 L j) (inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 L.eA 3 L.eNS k₃
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₂ fr h', by rw [h.u.2] at post; exact post⟩) ?_
  refine Piece.seq (dec12C_piece (Y := Y L) 0 (384 * j) 3 L.eT o₄ (by rdecide) (by yd_taint)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨⟨h.keep hp (by rdecide) k₄ fr h',
      polyIs_congr (Top.keep hp (by rdecide) (b := bA L) k₅ fr) h.u⟩, ?_⟩) hc
  rw [dk_slice hp h.ctx (by unfold Params.dkLen; omega) o₂] at post
  rw [dS, dcS, KPke.dkPke, slice_take _ (show 384 * j + 384 ≤ 384 * L.p.k by omega)]
  exact post

/-- Term 0: `w ← ŝ[0] ×_T NTT(u'[0])`. -/
theorem term0_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L 0) (D L 1) (decTerm L 0) :=
  uS_piece 0 hk (mulC_piece (Y := Y L) 3 L.eU 3 L.eT 3 L.eA 3 L.eNS DecOK.mul.1
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h', fun _ => ⟨post.1, by rw [post.2, h.t.2, h.u.2]; rfl⟩⟩)

/-- Term `j + 1`: `w ← w + ŝ[j + 1] ×_T NTT(u'[j + 1])`. -/
theorem term_piece [CeOK L] (j : Nat) (hj : j + 1 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (D L (j + 1)) (D L (j + 2)) (decTerm L (j + 1)) := by
  obtain ⟨-, -, -, -, -, k₆, k₇⟩ := DecOK.keep (L := L)
  refine uS_piece (j + 1) hj (.seq (B := D4 L (j + 1)) (mulC_piece (Y := Y L) 3 L.eP 3 L.eT 3 L.eA 3 L.eNS
    DecOK.mul.2 (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by rdecide) k₆ fr h', by rw [h.t.2, h.u.2] at post; exact post⟩) ?_)
  refine accC_piece add_verified add_nosp add_stack 3 L.eU 3 L.eP k₇ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.w (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.w (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(w)`. -/
structure E1 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  w : PolyIs s.mem (Buf.addr s₀ (bW L)) (nttInv (partD L s₀ L.p.k))

/-- And `v'`. -/
structure E2 (L : KemLay) (s₀ s : State) : Prop extends E1 L s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ (bE L)) (KPke.dcV L.p (ct L s₀))

/-- `v' - NTT⁻¹(w)`. -/
structure E3 (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  v : PolyIs s.mem (Buf.addr s₀ (bE L)) (sub (KPke.dcV L.p (ct L s₀)) (nttInv (partD L s₀ L.p.k)))

/-- After `m'` is computed. -/
structure DM (L : KemLay) (s₀ s : State) : Prop where
  ctx : Ctx (Y L) s₀ s
  m : bytesAt s.mem (Buf.addr s₀ (bM L)) 32 = mD L s₀

/-- K-PKE.Decrypt(dk_PKE, c). -/
theorem decrypt_piece [CeOK L] (hk : 0 < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (Ctx (Y L)) (DM L) (decrypt L) := by
  obtain ⟨v₁, v₂, v₃, v₄, v₅, v₆⟩ := DecOK.v (L := L)
  refine (Piece.seqs0 (P := D L) L.p.k (fun j hj => match j, hj with
    | 0, _ => term0_piece hk
    | j + 1, hj => term_piece j hj) ?_).mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩)
    fun _ _ _ h => h
  refine Piece.seq (B := E1 L) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack 3 L.eU 3 L.eNS v₁
    (by rdecide) (by yd_taint) (fun _ _ _ h => ⟨h.ctx, (h.w hk).1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [(h.w hk).2] at post; exact post⟩) ?_
  refine Piece.seq (B := E2 L) (ddK_piece (Y := Y L) L.p.dv (.inr rfl) 1 (32 * L.p.du * L.p.k) 3 L.eE v₂
    (by rdecide) (by yd_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', polyIs_congr (Top.keep hp (by rdecide) (b := bW L) v₄ fr) h.w⟩, ?_⟩) ?_
  · rw [ct_slice hp h.ctx DecOK.ct.2.2 v₃] at post; exact post
  refine Piece.seq (B := E3 L) (accC_piece sub_verified sub_nosp sub_stack 3 L.eE 3 L.eU v₅ (by rdecide)
    (by yd_taint) (fun _ _ _ h => ⟨h.ctx, h.v.1, h.w.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [h.v.2, h.w.2] at post; exact post⟩) ?_
  refine ceC_piece (Y := Y L) ce768 1 (by decide) 3 L.eE 3 L.eM v₆ (by rdecide) (by yd_taint)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩
  rw [show Buf.addr s₀ (bM L) = Buf.addr s₀ ⟨3, L.eM, 32 * 1⟩ from rfl, post, h.v.2, mD_eq, KPke.decM,
    KPke.kpkeDecrypt_eq]

end VG.Proof.MlKem.X86.Decaps
