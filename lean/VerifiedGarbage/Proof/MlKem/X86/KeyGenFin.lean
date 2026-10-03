import VerifiedGarbage.Proof.MlKem.X86.KeyGenRow

/-!
# ML-KEM on x86 (32-bit): the keys in key generation

After the rows: `ρ` copied into `ek` (which completes `ek_PKE`), `ŝ` encoded
into `dk` (`dk_PKE`, `enc_piece`), `ek` copied into `dk`, `H(ek)` hashed into
`dk`, `z` copied into `dk`, and `kgACC` loaded to be returned (`fin_piece`).
`F n` is what holds after `n` of these steps.
-/

namespace VG.Proof.MlKem.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad sha3Suffix)

section
variable (L : KemLay)
/-- `ρ` in `ek`. -/
abbrev bEKr : Buf := ⟨1, 384 * L.p.k, 32⟩
/-- `ByteEncode₁₂(ŝ[j])` in `dk`. -/
abbrev bDK (j : Nat) : Buf := ⟨2, 384 * j, 384⟩
/-- `ek` in `dk`. -/
abbrev bDKE : Buf := ⟨2, 384 * L.p.k, L.p.ekLen⟩
/-- `H(ek)` in `dk`. -/
abbrev bDKH : Buf := ⟨2, 768 * L.p.k + 32, 32⟩
/-- `z` in `dk`. -/
abbrev bDKZ : Buf := ⟨2, 768 * L.p.k + 64, 32⟩
end

/-- After `n` of the steps that write the keys. -/
structure F (L : KemLay) (n : Nat) (s₀ s : State) : Prop extends B L (L.p.k * L.p.k) L.p.k s₀ s where
  rhoE : 1 ≤ n → bytesAt s.mem (Buf.addr s₀ (bEKr L)) 32 = KPke.kgRho L.p (d s₀)
  dk : ∀ j < L.p.k, j + 2 ≤ n → bytesAt s.mem (Buf.addr s₀ (bDK j)) 384 = encode12 (seP L s₀ j)
  cp : L.p.k + 2 ≤ n → accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (bDKE L)) L.p.ekLen = KPke.ekPKE L.p (aM L s₀) (d s₀)
  hh : L.p.k + 3 ≤ n → accV L s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ (bDKH L)) 32 = H (KPke.ekPKE L.p (aM L s₀) (d s₀))
  zk : L.p.k + 4 ≤ n → bytesAt s.mem (Buf.addr s₀ (bDKZ L)) 32 = z s₀

/-- Whether `bs` is apart from what `B` and the first `n` steps state. -/
def safeF (L : KemLay) (bs : List Buf) (n : Nat) : Bool :=
  safe L bs && (n < 1 || (Y L).apart (bEKr L) bs) &&
    ((List.range L.p.k).all fun j => n < j + 2 || (Y L).apart (bDK j) bs) &&
    (n < L.p.k + 2 || (Y L).apart (bDKE L) bs) && (n < L.p.k + 3 || (Y L).apart (bDKH L) bs) &&
    (n < L.p.k + 4 || (Y L).apart (bDKZ L) bs)

variable {L : KemLay}

theorem F.keep {n : Nat} {s₀ s s' : State} (hp : TPre (Y L) s₀) {bs : List Buf} {M : Nat}
    (hM : M + 16 ≤ (Y L).stk) (hs : safeF L bs n = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : F L n s₀ s)
    (c : Ctx (Y L) s₀ s') : F L n s₀ s' := by
  simp only [safeF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hs
  have k := h.toB.keep hp hM h₀ (Nat.le_refl _) fr c
  have ea : accV L s₀ s' = accV L s₀ s := keepW hp hM (by simp only [safe, Bool.and_eq_true] at h₀; exact h₀.1.1) fr
  refine ⟨k, fun hn => ?_, fun j hj hn => ?_, fun hn e₁ => ?_, fun hn e₁ => ?_, fun hn => ?_⟩
  · rcases h₁ with h₁ | h₁
    · omega
    · rw [keepBytes hp hM h₁ fr]; exact h.rhoE hn
  · rcases h₂ j hj with h₂ | h₂
    · omega
    · rw [keepBytes hp hM h₂ fr]; exact h.dk j hj hn
  · rcases h₃ with h₃ | h₃
    · omega
    · rw [keepBytes hp hM h₃ fr]; exact h.cp hn (ea ▸ e₁)
  · rcases h₄ with h₄ | h₄
    · omega
    · rw [keepBytes hp hM h₄ fr]; exact h.hh hn (ea ▸ e₁)
  · rcases h₅ with h₅ | h₅
    · omega
    · rw [keepBytes hp hM h₅ fr]; exact h.zk hn

/-- The facts of the layout that writing the keys uses. -/
class FinOK (L : KemLay) : Prop where
  fin : safeF L [bEKr L] 0 = true ∧ (∀ j < L.p.k, safeF L [bDK j] (j + 1) = true) ∧
    safeF L [bDKE L] (L.p.k + 1) = true ∧
    safeF L [⟨(Y L).sc, L.kgST, 200⟩, ⟨(Y L).sc, L.kgWK, 640⟩, bDKH L] (L.p.k + 2) = true ∧
    safeF L [bDKZ L] (L.p.k + 3) = true ∧ safeF L [] (L.p.k + 4) = true ∧ (Y L).apart (bACC L) [bDKE L] = true ∧
    (Y L).apart (bACC L) [⟨(Y L).sc, L.kgST, 200⟩, ⟨(Y L).sc, L.kgWK, 640⟩, bDKH L] = true
  enc : ∀ j < L.p.k, ((Y L).ok (bSE j) && (Y L).okW (bDK j) && (Y L).sep (bSE j) (bDK j)) = true
  ek : (Y L).ok ⟨1, 0, 384 * L.p.k⟩ = true ∧ (Y L).ok (bEKr L) = true ∧ (Y L).ok ⟨2, 0, 384 * L.p.k⟩ = true ∧
    (Y L).ok (bDKE L) = true ∧ (Y L).ok (bDKH L) = true ∧ (Y L).ok (bDKZ L) = true ∧
    (Y L).ok ⟨2, 0, 384 * L.p.k + L.p.ekLen⟩ = true ∧ (Y L).ok ⟨2, 0, 768 * L.p.k + 64⟩ = true
  rho : ((Y L).ok ⟨3, L.kgRS, 4 * 8⟩ && (Y L).okW ⟨1, 384 * L.p.k, 4 * 8⟩ &&
    (Y L).sep ⟨3, L.kgRS, 4 * 8⟩ ⟨1, 384 * L.p.k, 4 * 8⟩) = true
  cp : ((Y L).ok ⟨1, 0, L.p.ekLen⟩ && (Y L).okW (bDKE L) && (Y L).sep ⟨1, 0, L.p.ekLen⟩ (bDKE L)) = true ∧
    4 * (L.p.ekLen / 4) = L.p.ekLen ∧ 0 < L.p.ekLen / 4 ∧ L.p.ekLen / 4 < 2 ^ 30 ∧ L.p.ekLen < 2 ^ 32
  hh : ((Y L).okW ⟨3, L.kgST, 200⟩ && (Y L).okW ⟨3, L.kgWK, 640⟩ && (Y L).ok ⟨1, 0, L.p.ekLen⟩ &&
    (Y L).okW (bDKH L) && (Y L).sep ⟨3, L.kgST, 200⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgST, 200⟩ &&
    (Y L).sep ⟨1, 0, L.p.ekLen⟩ ⟨3, L.kgWK, 640⟩ && (Y L).sep ⟨3, L.kgST, 200⟩ (bDKH L) &&
    (Y L).sep (bDKH L) ⟨3, L.kgWK, 640⟩) = true
  zk : ((Y L).ok ⟨0, 32, 4 * 8⟩ && (Y L).okW ⟨2, 768 * L.p.k + 64, 4 * 8⟩ &&
    (Y L).sep ⟨0, 32, 4 * 8⟩ ⟨2, 768 * L.p.k + 64, 4 * 8⟩) = true
  acc : (Y L).ok ⟨3, L.kgACC, 4⟩ = true

/-- `ek`, if every sample succeeded. -/
theorem ek_full [FinOK L] {n : Nat} {s₀ s : State} (hp : TPre (Y L) s₀) (h : F L n s₀ s) (hn : 1 ≤ n)
    (e : accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, L.p.ekLen⟩) L.p.ekLen = KPke.ekPKE L.p (aM L s₀) (d s₀) := by
  obtain ⟨o₁, o₂, -⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := 32) (L := L.p.ekLen) (Nat.zero_add _) rfl o₁ o₂,
    bytes_catK hp _ o₁, h.rhoE hn, KPke.ekPKE]
  exact congrArg (· ++ _) (catK_congr fun i hi => by rw [Nat.zero_add]; exact h.ek e i hi)

/-- `dk`, if every sample succeeded. -/
theorem dk_full [FinOK L] {s₀ s : State} (hp : TPre (Y L) s₀) (h : F L (L.p.k + 4) s₀ s) (e : accV L s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, L.p.dkLen⟩) L.p.dkLen =
      KPke.dkPKE L.p (d s₀) ++ KPke.ekPKE L.p (aM L s₀) (d s₀) ++ H (KPke.ekPKE L.p (aM L s₀) (d s₀)) ++ z s₀ := by
  obtain ⟨-, -, o₃, o₄, o₅, o₆, o₇, o₈⟩ := FinOK.ek (L := L)
  rw [bytes_split hp _ (o' := 768 * L.p.k + 64) (l₁ := 768 * L.p.k + 64) (l₂ := 32) (Nat.zero_add _)
      (by unfold Params.dkLen; omega) o₈ o₆,
    bytes_split hp _ (o' := 768 * L.p.k + 32) (l₁ := 768 * L.p.k + 32) (l₂ := 32) (Nat.zero_add _) rfl
      (by unfold Params.ekLen at o₇; rw [show 768 * L.p.k + 32 = 384 * L.p.k + (384 * L.p.k + 32) by omega]; exact o₇) o₅,
    bytes_split hp _ (o' := 384 * L.p.k) (l₁ := 384 * L.p.k) (l₂ := L.p.ekLen) (Nat.zero_add _)
      (by unfold Params.ekLen; omega) o₃ o₄,
    bytes_catK hp _ o₃, h.cp (by omega) e, h.hh (by omega) e, h.zk (by omega), KPke.dkPKE]
  refine congrArg (fun x => x ++ _ ++ _ ++ _) (catK_congr fun j hj => ?_)
  rw [Nat.zero_add]; exact h.dk j hj (by omega)

variable [FinOK L]

/-- `dk[384j : 384j + 384] ← ByteEncode₁₂(ŝ[j])`. -/
theorem enc_piece (j : Nat) (hj : j < L.p.k) :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (F L (j + 1)) (F L (j + 2)) (kgEnc j) := by
  refine enc12C_piece (Y := Y L) 3 (1024 * j) 2 (384 * j) (FinOK.enc j hj) (by rdecide) (by yk_taint)
    (fun _ _ _ h => ⟨h.ctx, (h.se j (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.keep hp (by rdecide) ((FinOK.fin (L := L)).2.1 j hj) fr h'
  refine ⟨k.toB, fun hn => k.rhoE (by omega), fun j' hj' hn => ?_, fun hn => by omega, fun hn => by omega,
    fun hn => by omega⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | e
  · exact k.dk j' hj' (by omega)
  · obtain rfl : j' = j := by omega
    rw [post, (h.se j' (by omega)).2]

/-- After the keys are written: `kgACC` returned. -/
structure Done (L : KemLay) (s₀ s : State) : Prop extends F L (L.p.k + 4) s₀ s where
  eax : s.gpr .eax = accV L s₀ s

/-- The keys, from the rows. -/
theorem fin_piece [GOK L] :
    Piece (TPre (Y L)) (TPub (Y L) (lk L)) (B L (L.p.k * L.p.k) L.p.k) (Done L)
      (.seq (copyW 3 ⟨3, L.kgRS, 32⟩ ⟨1, 384 * L.p.k, 32⟩ 8) <|
        seqs ((List.range L.p.k).map kgEnc) <|
        .seq (copyW 3 ⟨1, 0, L.p.ekLen⟩ ⟨2, 384 * L.p.k, L.p.ekLen⟩ (L.p.ekLen / 4)) <|
        .seq (hash1 3 L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩ ⟨2, 768 * L.p.k + 32, 32⟩) <|
        .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 768 * L.p.k + 64, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi L.kgACC))])) := by
  obtain ⟨f₁, -, f₄, f₅, f₆, f₇, f₈, f₉⟩ := FinOK.fin (L := L)
  obtain ⟨c₁, c₂, c₃, c₄, c₅⟩ := FinOK.cp (L := L)
  refine Piece.seq (B := F L 1) (copyW_piece (Y := Y L) 3 L.kgRS 1 (384 * L.p.k) 8 (by decide) (by decide)
    FinOK.rho (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (M := 0) (by rdecide)
      (by simp only [safeF, Bool.and_eq_true] at f₁; exact f₁.1.1.1.1.1) (Nat.le_refl _) (fr1 fr) h'
    refine ⟨k, fun _ => ?_, fun _ _ hn => by omega, fun hn => by omega, fun hn => by omega, fun hn => by omega⟩
    rw [show Buf.addr s₀ (bEKr L) = Buf.addr s₀ ⟨1, 384 * L.p.k, 4 * 8⟩ from rfl, post]
    exact h.rho
  refine Piece.seqs0 (P := fun i => F L (i + 1)) L.p.k (fun j hj => enc_piece j hj) ?_
  refine Piece.seq (B := F L (L.p.k + 2)) (copyW_piece' (Y := Y L) 1 0 2 (384 * L.p.k) (L.p.ekLen / 4) L.p.ekLen
    c₂ c₃ c₄ c₁ (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₄ (fr1 fr) h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (N := 0) (by rdecide) f₈ (fr1 fr)
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ e₁ => ?_,
      fun hn => by omega, fun hn => by omega⟩
    rw [post]
    exact ek_full hp h (by omega) (ea ▸ e₁)
  refine Piece.seq (B := F L (L.p.k + 3)) (hash1_piece (Y := Y L) L.kgST L.kgWK 136 6 ⟨1, 0, L.p.ekLen⟩
    ⟨2, 768 * L.p.k + 32, 32⟩ rate136 FinOK.hh (by rdecide) c₅ (by rdecide) (by taint_rfl) (by yk_taint) (by yk_taint)
    (by yk_taint) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ?_) ?_
  · have k := h.keep hp (by rdecide) f₅ fr h'
    have ea : accV L s₀ s' = accV L s₀ s := keepW hp (by rdecide) f₉ fr
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by omega),
      fun _ e₁ => ?_, fun hn => by omega⟩
    rw [out, ek_full hp h (by omega) (ea ▸ e₁), show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32,
      ← padded, ← H_eq]
  refine Piece.seq (B := F L (L.p.k + 4)) (copyW_piece (Y := Y L) 0 32 2 (768 * L.p.k + 64) 8 (by decide)
    (by decide) FinOK.zk (by yk_taint) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by rdecide) f₆ (fr1 fr) h'
    refine ⟨k.toB, fun _ => k.rhoE (by omega), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by omega),
      fun _ => k.hh (by omega), fun _ => ?_⟩
    rw [show Buf.addr s₀ (bDKZ L) = Buf.addr s₀ ⟨2, 768 * L.p.k + 64, 4 * 8⟩ from rfl, post]
    exact h.ctx.roBytes hp (b := ⟨0, 32, 32⟩) (by rdecide) rfl
  exact ld32_piece (Y := Y L) L.kgACC FinOK.acc (by yk_taint) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨h.keep hp (bs := []) (M := 0) (by rdecide) f₇
      (m' ▸ Frame.refl _ _) h',
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']; rfl⟩

end VG.Proof.MlKem.X86.KeyGen
