import VerifiedGarbage.Proof.MlKem1024.X86.KeyGenRow

/-!
# ML-KEM-1024 on x86 (32-bit): the keys in `vg_mlkem1024_keygen`

Untrusted: everything here is checked by Lean. After the rows (`B 16 4`),
`ρ` is copied into `ek`, `ŝ` encoded into `dk`, `ek` copied into `dk`,
`H(ek)` hashed into `dk` and `z` copied into it (`F n` after `n` of these),
and `kg4ACC` returned (`fin_piece`). If `kg4ACC` is 1, `ek` is `ek_PKE` and `dk`
is `dk_PKE ‖ ek ‖ H(ek) ‖ z` (`ek_full`, `dk_full`).
-/

namespace VG.Proof.MlKem1024.X86.KeyGen

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt squeezeFrom absorb pad sha3Suffix)

/-- `ρ` in `ek`. -/
abbrev bEKr : Buf := ⟨1, 1536, 32⟩
/-- `ByteEncode₁₂(ŝ[j])` in `dk`. -/
abbrev bDK (j : Nat) : Buf := ⟨2, 384 * j, 384⟩
/-- `ek` in `dk`. -/
abbrev bDKE : Buf := ⟨2, 1536, 1568⟩
/-- `H(ek)` in `dk`. -/
abbrev bDKH : Buf := ⟨2, 3104, 32⟩
/-- `z` in `dk`. -/
abbrev bDKZ : Buf := ⟨2, 3136, 32⟩

/-- After `n` of the steps that write the keys. -/
structure F (n : Nat) (s₀ s : State) : Prop extends B 16 4 s₀ s where
  rhoE : 1 ≤ n → bytesAt s.mem (Buf.addr s₀ bEKr) 32 = kgRho1024 (d s₀)
  dk : ∀ j < 4, j + 2 ≤ n → bytesAt s.mem (Buf.addr s₀ (bDK j)) 384 = encode12 (seP s₀ j)
  cp : 6 ≤ n → accV s₀ s = 1 → bytesAt s.mem (Buf.addr s₀ bDKE) 1568 = ekPKE1024 (aM s₀) (d s₀)
  hh : 7 ≤ n → accV s₀ s = 1 → bytesAt s.mem (Buf.addr s₀ bDKH) 32 = H (ekPKE1024 (aM s₀) (d s₀))
  zk : 8 ≤ n → bytesAt s.mem (Buf.addr s₀ bDKZ) 32 = z s₀

/-- Whether `bs` is apart from what `B` and the first `n` steps state. -/
def safeF (bs : List Buf) (n : Nat) : Bool :=
  safe bs && (n < 1 || Y.apart bEKr bs) && ((List.range 4).all fun j => n < j + 2 || Y.apart (bDK j) bs) &&
    (n < 6 || Y.apart bDKE bs) && (n < 7 || Y.apart bDKH bs) && (n < 8 || Y.apart bDKZ bs)

theorem F.keep {n : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : safeF bs n = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : F n s₀ s) (c : Ctx Y s₀ s') :
    F n s₀ s' := by
  simp only [safeF, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hs
  obtain ⟨⟨⟨⟨⟨h₀, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩ := hs
  have k := h.toB.keep hp hM h₀ (Nat.le_refl _) fr c
  have ea : accV s₀ s' = accV s₀ s := keepW hp hM (by simp only [safe, Bool.and_eq_true] at h₀; exact h₀.1.1) fr
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

/-- `ek`, if every sample succeeded. -/
theorem ek_full {n : Nat} {s₀ s : State} (hp : TPre Y s₀) (h : F n s₀ s) (hn : 1 ≤ n) (e : accV s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, 0, 1568⟩) 1568 = ekPKE1024 (aM s₀) (d s₀) := by
  rw [bytes_split hp _ (o' := 1536) (l₁ := 1536) (l₂ := 32) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 1152) (l₁ := 1152) (l₂ := 384) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 768) (l₁ := 768) (l₂ := 384) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 384) (l₁ := 384) (l₂ := 384) rfl rfl (by decide) (by decide)]
  rw [h.ek e 0 (by decide), h.ek e 1 (by decide), h.ek e 2 (by decide), h.ek e 3 (by decide), h.rhoE hn]
  rfl

/-- `dk`, if every sample succeeded. -/
theorem dk_full {s₀ s : State} (hp : TPre Y s₀) (h : F 8 s₀ s) (e : accV s₀ s = 1) :
    bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 3168⟩) 3168 =
      dkPKE1024 (d s₀) ++ ekPKE1024 (aM s₀) (d s₀) ++ H (ekPKE1024 (aM s₀) (d s₀)) ++ z s₀ := by
  rw [bytes_split hp _ (o' := 3136) (l₁ := 3136) (l₂ := 32) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 3104) (l₁ := 3104) (l₂ := 32) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 1536) (l₁ := 1536) (l₂ := 1568) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 1152) (l₁ := 1152) (l₂ := 384) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 768) (l₁ := 768) (l₂ := 384) rfl rfl (by decide) (by decide),
    bytes_split hp _ (o' := 384) (l₁ := 384) (l₂ := 384) rfl rfl (by decide) (by decide)]
  rw [h.dk 0 (by decide) (by decide), h.dk 1 (by decide) (by decide), h.dk 2 (by decide) (by decide),
    h.dk 3 (by decide) (by decide), h.cp (by decide) e, h.hh (by decide) e, h.zk (by decide)]
  rfl

theorem safe_fin : safeF [bEKr] 0 = true ∧ (∀ j < 4, safeF [bDK j] (j + 1) = true) ∧ safeF [bDKE] 5 = true ∧
    safeF [⟨Y.sc, kg4ST, 200⟩, ⟨Y.sc, kg4WK, 640⟩, bDKH] 6 = true ∧ safeF [bDKZ] 7 = true := by decide

theorem ok_enc : ∀ j < 4, (Y.ok (bSE j) && Y.okW (bDK j) && Y.sep (bSE j) (bDK j)) = true := by decide

/-- `dk[384j : 384j + 384] ← ByteEncode₁₂(ŝ[j])`. -/
theorem enc_piece (j : Nat) (hj : j < 4) {ht : Taint.Hint VG.X86.Taint.T}
    (t : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax (bSE j) ++ ptrTo Y.sc .ecx (bDK j))) ht).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (F (j + 1)) (F (j + 2)) (enc12C 3 (bSE j) (bDK j)) := by
  refine enc12C_piece (Y := Y) 3 (1024 * j) 2 (384 * j) (ok_enc j hj) (by decide) t
    (fun _ _ _ h => ⟨h.ctx, (h.se j (by omega)).1⟩) fun s₀ s s' hp h h' fr post => ?_
  have k := h.keep hp (by decide) (safe_fin.2.1 j hj) fr h'
  refine ⟨k.toB, fun hn => k.rhoE (by omega), fun j' hj' hn => ?_, fun hn => by omega, fun hn => by omega,
    fun hn => by omega⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | e
  · exact k.dk j' hj' (by omega)
  · obtain rfl : j' = j := by omega
    rw [post, (h.se j' (by omega)).2]

/-- After the keys are written: `kg4ACC` returned. -/
structure Done (s₀ s : State) : Prop extends F 8 s₀ s where
  eax : s.gpr .eax = accV s₀ s

/-- The keys, from the rows. -/
theorem fin_piece :
    Piece (TPre Y) (TPub Y lk) (B 16 4) Done
      (.seq (copyW 3 ⟨3, kg4RS, 32⟩ ⟨1, 1536, 32⟩ 8) <|
        .seq (enc12C 3 ⟨3, 0, 1024⟩ ⟨2, 0, 384⟩) <| .seq (enc12C 3 ⟨3, 1024, 1024⟩ ⟨2, 384, 384⟩) <|
        .seq (enc12C 3 ⟨3, 2048, 1024⟩ ⟨2, 768, 384⟩) <| .seq (enc12C 3 ⟨3, 3072, 1024⟩ ⟨2, 1152, 384⟩) <|
        .seq (copyW 3 ⟨1, 0, 1568⟩ ⟨2, 1536, 1568⟩ 392) <|
        .seq (hash1 3 kg4ST kg4WK 136 6 ⟨1, 0, 1568⟩ ⟨2, 3104, 32⟩) <|
        .seq (copyW 3 ⟨0, 32, 32⟩ ⟨2, 3136, 32⟩ 8) (.block [.mov .eax (.mem (at_ .esi kg4ACC))])) := by
  obtain ⟨-, -, f₄, f₅, f₆⟩ := safe_fin
  refine Piece.seq (B := F 1) (copyW_piece (Y := Y) 3 kg4RS 1 1536 8 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (M := 0) (by decide) (by decide) (by decide) (fr1 fr) h'
    refine ⟨k, fun _ => ?_, fun _ _ hn => by omega, fun hn => by omega, fun hn => by omega, fun hn => by omega⟩
    rw [show Buf.addr s₀ bEKr = Buf.addr s₀ ⟨1, 1536, 4 * 8⟩ from rfl, post]
    exact h.rho
  refine Piece.seq (enc_piece 0 (by decide) (by taint_decide)) ?_
  refine Piece.seq (enc_piece 1 (by decide) (by taint_decide)) ?_
  refine Piece.seq (enc_piece 2 (by decide) (by taint_decide)) ?_
  refine Piece.seq (enc_piece 3 (by decide) (by taint_decide)) ?_
  refine Piece.seq (B := F 6) (copyW_piece (Y := Y) 1 0 2 1536 392 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by decide) f₄ (fr1 fr) h'
    have ea : accV s₀ s' = accV s₀ s := keepW hp (N := 0) (by decide) (by decide) (fr1 fr)
    refine ⟨k.toB, fun _ => k.rhoE (by decide), fun j hj _ => k.dk j hj (by omega), fun _ e₁ => ?_, fun hn => by omega,
      fun hn => by omega⟩
    rw [show Buf.addr s₀ bDKE = Buf.addr s₀ ⟨2, 1536, 4 * 392⟩ from rfl, post]
    exact ek_full hp h (by decide) (ea ▸ e₁)
  refine Piece.seq (B := F 7) (hash1_piece (Y := Y) kg4ST kg4WK 136 6 ⟨1, 0, 1568⟩ ⟨2, 3104, 32⟩ rate136
    (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out => ?_) ?_
  · have k := h.keep hp (by decide) f₅ fr h'
    have ea : accV s₀ s' = accV s₀ s := keepW hp (by decide) (by decide) fr
    refine ⟨k.toB, fun _ => k.rhoE (by decide), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by decide),
      fun _ e₁ => ?_, fun hn => by omega⟩
    rw [out, ek_full hp h (by decide) (ea ▸ e₁), show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32,
      ← padded, ← H_eq]
  refine Piece.seq (B := F 8) (copyW_piece (Y := Y) 0 32 2 3136 8 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ?_) ?_
  · have k := h.keep hp (by decide) f₆ (fr1 fr) h'
    refine ⟨k.toB, fun _ => k.rhoE (by decide), fun j hj _ => k.dk j hj (by omega), fun _ => k.cp (by decide),
      fun _ => k.hh (by decide), fun _ => ?_⟩
    rw [show Buf.addr s₀ bDKZ = Buf.addr s₀ ⟨2, 3136, 4 * 8⟩ from rfl, post]
    exact h.ctx.roBytes hp (b := ⟨0, 32, 32⟩) (by decide) rfl
  exact ld32_piece (Y := Y) kg4ACC (by decide) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨h.keep hp (bs := []) (M := 0) (by decide) (by decide) (m' ▸ Frame.refl _ _) h',
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']; rfl⟩

end VG.Proof.MlKem1024.X86.KeyGen
