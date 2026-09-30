import VerifiedGarbage.Proof.MlKem1024.X86.DecapsPre

/-!
# ML-KEM-1024 on x86 (32-bit): K-PKE.Decrypt in `vg_mlkem1024_decaps`

Untrusted: everything here is checked by Lean. `w = Σ ŝ[i] ×_T NTT(u'[i])`,
with `u'[i]` decoded and decompressed from `ct` and `ŝ[i]` decoded from `dk`
(`term0_piece`, `term_piece`), then `m' = ByteEncode₁(Compress₁(v' -
NTT⁻¹(w)))` (`decrypt_piece`), which is `mD`.
-/

namespace VG.Proof.MlKem1024.X86.Decaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt)

section
variable (s₀ : State)
/-- `ŝ[i]`. -/
abbrev dS (i : Nat) : Poly := dcS (dkPke1024 (dk s₀)) i
/-- `NTT(u'[i])`. -/
abbrev dU (i : Nat) : Poly := ntt (dcU1024 (ct s₀) i)

/-- `ŝ[0] ×_T NTT(u'[0]) + … + ŝ[j - 1] ×_T NTT(u'[j - 1])`, for `0 < j`. -/
noncomputable def partD : Nat → Poly
  | 0 => zero
  | 1 => multiplyNTTs (dS s₀ 0) (dU s₀ 0)
  | j + 1 => add (partD j) (multiplyNTTs (dS s₀ j) (dU s₀ j))
end

abbrev bA : Buf := ⟨3, e4A, 1024⟩
abbrev bT : Buf := ⟨3, e4T, 1024⟩
abbrev bW : Buf := ⟨3, e4U, 1024⟩
abbrev bP : Buf := ⟨3, e4P, 1024⟩
abbrev bE : Buf := ⟨3, e4E, 1024⟩
abbrev bNS : Buf := ⟨3, e4NS, 1024⟩
abbrev bM : Buf := ⟨3, e4M, 32⟩

/-- Before term `j`: and `w` so far, if `0 < j`. -/
structure D (j : Nat) (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  w : 0 < j → Reduced s.mem (Buf.addr s₀ bW) ∧ polyAt s.mem (Buf.addr s₀ bW) = partD s₀ j

theorem D.keep {j : Nat} {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hW : Y.apart bW bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem) (h : D j s₀ s) (c : Ctx Y s₀ s') :
    D j s₀ s' :=
  ⟨c, fun hj => ⟨keepRed hp hM hW fr (h.w hj).1, by rw [polyAt_congr (Top.keep hp hM hW fr)]; exact (h.w hj).2⟩⟩

/-- `u'[i]` is decoded, decompressed and in the NTT domain; `ŝ[i]` decoded. -/
structure D1 (j : Nat) (s₀ s : State) : Prop extends D j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ bA) (dcU1024 (ct s₀) j)

structure D2 (j : Nat) (s₀ s : State) : Prop extends D j s₀ s where
  u : PolyIs s.mem (Buf.addr s₀ bA) (dU s₀ j)

structure D3 (j : Nat) (s₀ s : State) : Prop extends D2 j s₀ s where
  t : PolyIs s.mem (Buf.addr s₀ bT) (dS s₀ j)

structure D4 (j : Nat) (s₀ s : State) : Prop extends D j s₀ s where
  p : PolyIs s.mem (Buf.addr s₀ bP) (multiplyNTTs (dS s₀ j) (dU s₀ j))

/-- The bytes of `ct[o : o + l]`. -/
theorem ct_slice {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {o l : Nat} (hl : o + l ≤ 1568)
    (hb : Y.ok ⟨1, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨1, o, l⟩) l = ((ct s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨1, o, l⟩) hb rfl, ct_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨1, o, l⟩) hb, Buf.addr_eq hp (b := ⟨1, 0, 1568⟩) (by decide), BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

/-- The bytes of `dk[o : o + l]`. -/
theorem dk_slice {s₀ s : State} (hp : TPre Y s₀) (h : Ctx Y s₀ s) {o l : Nat} (hl : o + l ≤ 3168)
    (hb : Y.ok ⟨0, o, l⟩ = true) :
    bytesAt s.mem (Buf.addr s₀ ⟨0, o, l⟩) l = ((dk s₀).drop o).take l := by
  rw [h.roBytes hp (b := ⟨0, o, l⟩) hb rfl, dk_eq, bytesAt_slice _ _ hl,
    Buf.addr_eq hp (b := ⟨0, o, l⟩) hb, Buf.addr_eq hp (b := ⟨0, 0, 3168⟩) (by decide), BitVec.add_assoc,
    ← BitVec.ofNat_add, Nat.zero_add]

theorem ok_dec : ∀ i < 4, Y.ok ⟨1, 352 * i, 352⟩ = true ∧ Y.ok ⟨0, 384 * i, 384⟩ = true ∧
    (Y.ok ⟨1, 352 * i, 352⟩ && Y.okW bA && Y.sep ⟨1, 352 * i, 352⟩ bA) = true ∧
    (Y.ok ⟨0, 384 * i, 384⟩ && Y.okW bT && Y.sep ⟨0, 384 * i, 384⟩ bT) = true := by decide

/-- `u'[i]` and `ŝ[i]`, then `c`. -/
theorem uS_piece (j : Nat) (hj : j < 4) {h₁ h₂ h₃ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨1, 352 * j, 32 * 11⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * 11))), .mov .edx (.imm (BitVec.ofNat 32 11))] : List Instr) ++
      ptrTo Y.sc .edi bA)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨0, 384 * j, 384⟩ ++ ptrTo Y.sc .ecx bT)) h₂).isSome = true)
    {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (D3 j) Q c)
    (h₃' : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax bA ++ ptrTo Y.sc .ecx bNS)) h₃).isSome
      = true) :
    Piece (TPre Y) (TPub Y lk) (D j) Q
      (.seq (ddC1024 3 11 ⟨1, 352 * j, 352⟩ bA) <| .seq (nttC 3 bA bNS) <| .seq (dec12C 3 ⟨0, 384 * j, 384⟩ bT) c) := by
  obtain ⟨o₁, o₂, o₃, o₄⟩ := ok_dec j hj
  refine Piece.seq (B := D1 j) (ddC1024_piece (Y := Y) 11 (by decide) 1 (352 * j) 3 e4A o₃ (by decide) t₁
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post => ⟨h.keep hp (by decide) (by decide) fr h', ?_⟩) ?_
  · rw [ct_slice hp h.ctx (by omega) o₁] at post; exact post
  refine Piece.seq (B := D2 j) (inPlaceC_piece NttFwd.verified ntt_nosp ntt_stack 3 e4A 3 e4NS (by decide) (by decide)
    h₃' (fun _ _ _ h => ⟨h.ctx, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by decide) (by decide) fr h', by rw [h.u.2] at post; exact post⟩) ?_
  refine Piece.seq (dec12C_piece (Y := Y) 0 (384 * j) 3 e4T o₄ (by decide) t₂ (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' fr post => ⟨⟨h.keep hp (by decide) (by decide) fr h',
      polyIs_congr (Top.keep hp (by decide) (b := bA) (by decide) fr) h.u⟩, ?_⟩) hc
  rw [dk_slice hp h.ctx (by omega) o₂] at post
  rw [dS, dcS, dkPke1024, slice_take _ (show 384 * j + 384 ≤ 1536 by omega)]
  exact post

theorem ok_mul : (Y.okW bW && Y.ok bT && Y.ok bA && Y.okW bNS && Y.sep bW bT && Y.sep bW bA && Y.sep bW bNS &&
    Y.sep bT bNS && Y.sep bA bNS) = true ∧
    (Y.okW bP && Y.ok bT && Y.ok bA && Y.okW bNS && Y.sep bP bT && Y.sep bP bA && Y.sep bP bNS &&
    Y.sep bT bNS && Y.sep bA bNS) = true := by decide

/-- Term 0: `w ← ŝ[0] ×_T NTT(u'[0])`. -/
theorem term0_piece : Piece (TPre Y) (TPub Y lk) (D 0) (D 1) (dec4Term 0) :=
  uS_piece 0 (by decide) (by taint_decide) (by taint_decide) (mulC_piece (Y := Y) 3 e4U 3 e4T 3 e4A 3 e4NS ok_mul.1
    (by decide) (by taint_decide) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩)
    fun s₀ s s' hp h h' fr post => ⟨h', fun _ => ⟨post.1, by rw [post.2, h.t.2, h.u.2]; rfl⟩⟩) (by taint_decide)

/-- Term `j + 1`: `w ← w + ŝ[j + 1] ×_T NTT(u'[j + 1])`. -/
theorem term_piece (j : Nat) (hj : j + 1 < 4) {h₁ h₂ : Taint.Hint VG.X86.Taint.T}
    (t₁ : (VG.X86.taint.check (τr [.esp, .esi]) (.block (ptrTo Y.sc .eax ⟨1, 352 * (j + 1), 32 * 11⟩ ++
      ([.mov .ecx (.imm (BitVec.ofNat 32 (32 * 11))), .mov .edx (.imm (BitVec.ofNat 32 11))] : List Instr) ++
      ptrTo Y.sc .edi bA)) h₁).isSome = true)
    (t₂ : (VG.X86.taint.check (τr [.esp, .esi])
      (.block (ptrTo Y.sc .eax ⟨0, 384 * (j + 1), 384⟩ ++ ptrTo Y.sc .ecx bT)) h₂).isSome = true) :
    Piece (TPre Y) (TPub Y lk) (D (j + 1)) (D (j + 2)) (dec4Term (j + 1)) := by
  refine uS_piece (j + 1) hj t₁ t₂ (.seq (B := D4 (j + 1)) (mulC_piece (Y := Y) 3 e4P 3 e4T 3 e4A 3 e4NS ok_mul.2
    (by decide) (by taint_decide) (fun _ _ _ h => ⟨h.ctx, h.t.1, h.u.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h.keep hp (by decide) (by decide) fr h', by rw [h.t.2, h.u.2] at post; exact post⟩) ?_) (by taint_decide)
  refine accC_piece add_verified add_nosp add_stack 3 e4U 3 e4P (by decide) (by decide) (by taint_decide)
    (fun _ _ _ h => ⟨h.ctx, (h.w (Nat.succ_pos _)).1, h.p.1⟩) fun s₀ s s' hp h h' fr post => ?_
  refine ⟨h', fun _ => ⟨post.1, ?_⟩⟩
  rw [post.2, (h.w (Nat.succ_pos _)).2, h.p.2]
  rfl

/-- `NTT⁻¹(w)`. -/
structure E1 (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  w : PolyIs s.mem (Buf.addr s₀ bW) (nttInv (partD s₀ 4))

/-- And `v'`. -/
structure E2 (s₀ s : State) : Prop extends E1 s₀ s where
  v : PolyIs s.mem (Buf.addr s₀ bE) (dcV1024 (ct s₀))

/-- `v' - NTT⁻¹(w)`. -/
structure E3 (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  v : PolyIs s.mem (Buf.addr s₀ bE) (sub (dcV1024 (ct s₀)) (nttInv (partD s₀ 4)))

/-- After `m'` is computed. -/
structure DM (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  m : bytesAt s.mem (Buf.addr s₀ bM) 32 = mD s₀

/-- K-PKE.Decrypt(dk_PKE, c). -/
theorem decrypt_piece : Piece (TPre Y) (TPub Y lk) (Ctx Y) DM decrypt4 := by
  refine Piece.seq (term0_piece.mono (fun _ _ _ h => ⟨h, fun h => absurd h (Nat.lt_irrefl _)⟩) fun _ _ _ h => h) ?_
  refine Piece.seq (term_piece 0 (by decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (term_piece 1 (by decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (term_piece 2 (by decide) (by taint_decide) (by taint_decide)) ?_
  refine Piece.seq (B := E1) (inPlaceC_piece NttInvP.verified nttInv_nosp nttInv_stack 3 e4U 3 e4NS (by decide)
    (by decide) (by taint_decide) (fun _ _ _ h => ⟨h.ctx, (h.w (by decide)).1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [(h.w (by decide)).2] at post; exact post⟩) ?_
  refine Piece.seq (B := E2) (ddC1024_piece (Y := Y) 5 (by decide) 1 1408 3 e4E (by decide) (by decide) (by taint_decide)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', polyIs_congr (Top.keep hp (by decide) (b := bW) (by decide) fr) h.w⟩, ?_⟩) ?_
  · rw [ct_slice hp h.ctx (by decide) (by decide)] at post; exact post
  refine Piece.seq (B := E3) (accC_piece sub_verified sub_nosp sub_stack 3 e4E 3 e4U (by decide) (by decide)
    (by taint_decide) (fun _ _ _ h => ⟨h.ctx, h.v.1, h.w.1⟩) fun s₀ s s' hp h h' fr post =>
      ⟨h', by rw [h.v.2, h.w.2] at post; exact post⟩) ?_
  refine ceC_piece (Y := Y) 1 (by decide) 3 e4E 3 e4M (by decide) (by decide) (by taint_decide)
    (fun _ _ _ h => ⟨h.ctx, h.v.1⟩) fun s₀ s s' hp h h' fr post => ⟨h', ?_⟩
  rw [show Buf.addr s₀ bM = Buf.addr s₀ ⟨3, e4M, 32 * 1⟩ from rfl, post, h.v.2, mD_eq, decM1024, kpkeDecrypt1024]
  rfl

end VG.Proof.MlKem1024.X86.Decaps
