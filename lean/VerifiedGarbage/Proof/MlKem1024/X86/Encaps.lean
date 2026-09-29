import VerifiedGarbage.Proof.MlKem1024.X86.EncV
import VerifiedGarbage.Impl.MlKem1024.X86.Encaps
import VerifiedGarbage.Spec.MlKem.Contract1024

/-!
# ML-KEM-1024 on x86 (32-bit): `vg_mlkem1024_encaps`

Untrusted: everything here is checked by Lean. The proof of
`vg_mlkem768_encaps` (`Proof/MlKem/X86/Encaps.lean`) for `k = 4`. The layout of
the arguments (`Y`: `ek`, `m`, `key`, `ct`, `scratch`, and the 88 bytes of stack), which the
contract's precondition implies (`pre_of`); the public data, `ρ` (`pub_of`).
`ek` and `m` are copied into `scratch`, `H(ek)` and `G(m ‖ H(ek))` hashed
(`start_piece`), the ciphertext computed (`Enc.encrypt_piece`), and `K` and
the ciphertext copied out (`fin_piece`). If every `SampleNTT` succeeded,
K-PKE.Encrypt succeeds with the matrix sampled within one bound on their
iterations (`kpkeEncrypt1024_some`); if one failed within `minIterations`,
it fails with that bound (`kpkeEncrypt1024_none`).
-/

namespace VG.Proof.MlKem1024.X86.Encaps

open VG VG.X86 VG.Impl.MlKem.X86 VG.Impl.MlKem1024.X86
open VG.Proof.MlKem
open VG.Proof.MlKem.X86
open VG.Proof.MlKem.X86.Top
open VG.Proof.MlKem1024.X86
open VG.Spec.MlKem
open VG.Spec.Sha3 (bytesAt sha3_512 sha3Suffix)

/-- `ek` and `m` (read), `key`, `ct` and `scratch` (written); 88 bytes of stack. -/
def Y : Lay := ⟨[(1568, false), (32, false), (32, true), (1568, true), (49152, true)], 4, 88⟩

section
variable (s₀ : State)
/-- `ek` (irreducible, so that elaboration never evaluates its 1568 bytes). -/
@[irreducible] def ek : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 1568⟩) 1568
/-- `m`. -/
@[irreducible] def msg : List Byte := bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32
/-- What encaps may leak: `ρ`. -/
abbrev lk : List Byte := ekRho mlKem1024 (ek s₀)
/-- `G(m ‖ H(ek))`, as 64 bytes. -/
@[irreducible] def kr : List Byte := sha3_512 (msg s₀ ++ H (ek s₀))
end

theorem ek_eq (s₀ : State) : ek s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨0, 0, 1568⟩) 1568 := by unfold ek; rfl
theorem msg_eq (s₀ : State) : msg s₀ = bytesAt s₀.mem (Buf.addr s₀ ⟨1, 0, 32⟩) 32 := by unfold msg; rfl
theorem kr_eq (s₀ : State) : kr s₀ = sha3_512 (msg s₀ ++ H (ek s₀)) := by unfold kr; rfl

/-- The inputs of K-PKE.Encrypt. -/
abbrev I : Enc.Inp := ⟨ek, msg, kr⟩

theorem hS : Enc.SOK Y := ⟨by decide, by decide, by decide, rfl⟩

theorem hρ : Enc.RhoPub Y lk I := fun _ _ _ _ hq => hq.2.2


theorem addr0 (s₀ : State) (i l : Nat) : Buf.addr s₀ ⟨i, 0, l⟩ = (arg s₀ i).setWidth 64 := by
  simp only [Buf.addr, Buf.ptr, BitVec.add_zero]

theorem pre_of {s₀ : State} (h : (Spec.MlKem1024.encapsContract X86.abi 88).pre s₀) : TPre Y s₀ := by
  sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, -, h25, h26, h27, h28, h29, h30, h31, h32, h33, h34, h35⟩ := h
  have hs : (⟨(E0 s₀).setWidth 64 - 88#64, 88⟩ : Region) = below (E0 s₀) 88 := by
    simp only [below]; rw [Taint.sub_setWidth h1]
  rw [hs] at h25 h26 h27 h28 h29 h30
  have c5 : ∀ i, i < Y.n → i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := fun i hi => by
    simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi; omega
  refine ⟨h1, by decide, by simp only [Y, Lay.n, List.length_cons, List.length_nil]; omega, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, h30, ?_, by decide⟩
  · intro i hi hw
    rw [h3]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
    all_goals exact absurd hw (by decide)
  · intro i hi hw
    rw [h4]
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    · exact absurd hw (by decide)
    · exact absurd hw (by decide)
    all_goals simp [argR, Lay.alen, Y]
  · rw [h4]; simp [gR, Lay.n, Y]
  · intro i hi j hj hne hw
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl <;> rcases c5 j hj with rfl | rfl | rfl | rfl | rfl
    exacts [absurd rfl hne, absurd hw (by decide), h5, h6, h7,
      absurd hw (by decide), absurd rfl hne, h9, h10, h11,
      h5.symm, h9.symm, absurd rfl hne, h13, h14,
      h6.symm, h10.symm, h13.symm, absurd rfl hne, h16,
      h7.symm, h11.symm, h14.symm, h16.symm, absurd rfl hne]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h8.symm, h12.symm, h15.symm, h17.symm, h18.symm]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h19, h20, h21, h22, h23]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h25, h26, h27, h28, h29]
  · intro i hi
    rcases c5 i hi with rfl | rfl | rfl | rfl | rfl
    exacts [h31, h32, h33, h34, h35]

theorem pub_of {s₀ s₀' : State} (h : (Spec.MlKem1024.encapsContract X86.abi 88).pub s₀ s₀') : TPub Y lk s₀ s₀' := by
  sig_pub [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes] at h
  obtain ⟨e₁, e₂, e₃, e₄, e₅, e₆, e₇⟩ := h
  refine ⟨e₁, fun i hi => ?_, ?_⟩
  · simp only [Y, Lay.n, List.length_cons, List.length_nil] at hi
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    exacts [e₃, e₄, e₅, e₆, e₇]
  · have e := Sample.map_toNat_inj e₂
    show ekRho mlKem1024 (ek s₀) = ekRho mlKem1024 (ek s₀')
    rw [ek_eq, ek_eq, addr0, addr0]
    exact e

/-! ## The inputs of K-PKE.Encrypt -/

/-- `H(ek)`. -/
abbrev bH : Buf := ⟨4, en4H, 32⟩

/-- After `ek` is copied. -/
structure Q1 (s₀ s : State) : Prop where
  ctx : Ctx Y s₀ s
  ekc : bytesAt s.mem (Buf.addr s₀ (Enc.bEK Y.sc)) 1568 = ek s₀

/-- After `m` is copied. -/
structure Q2 (s₀ s : State) : Prop extends Q1 s₀ s where
  mc : bytesAt s.mem (Buf.addr s₀ (Enc.bM Y.sc)) 32 = msg s₀

/-- After `H(ek)` is hashed. -/
structure Q3 (s₀ s : State) : Prop extends Q2 s₀ s where
  hh : bytesAt s.mem (Buf.addr s₀ bH) 32 = H (ek s₀)

/-- The inputs of K-PKE.Encrypt, then `c`. -/
theorem start_piece {Q : State → State → Prop} {c : Prog isa} (hc : Piece (TPre Y) (TPub Y lk) (Enc.Base Y I) Q c) :
    Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Q
      (.seq (.block [.mov .esi (.mem (at_ .esp 36))]) <|
        .seq (copyW 4 ⟨0, 0, 1568⟩ ⟨4, e4EK, 1568⟩ 392) <| .seq (copyW 4 ⟨1, 0, 32⟩ ⟨4, e4M, 32⟩ 8) <|
        .seq (hash1 4 e4ST e4WK 136 6 ⟨4, e4EK, 1568⟩ ⟨4, en4H, 32⟩) <|
        .seq (hash2 4 e4ST e4WK 72 6 ⟨4, e4M, 32⟩ ⟨4, en4H, 32⟩ ⟨4, e4KR, 64⟩) c) := by
  refine Piece.seq (ldsc_piece (Y := Y) (by taint_decide)) ?_
  refine Piece.seq (B := Q1) (copyW_piece (Y := Y) 0 0 4 e4EK 392 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h) fun s₀ s s' hp h h' _ post => ⟨h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, e4EK, 4 * 392⟩) (4 * 392) = _
    rw [post, ek_eq]
    exact h.roBytes hp (b := ⟨0, 0, 1568⟩) (by decide) (by decide)
  refine Piece.seq (B := Q2) (copyW_piece (Y := Y) 1 0 4 e4M 8 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨h', by rw [keepBytes hp (N := 0) (by decide) (by decide) (fr1 fr)]; exact h.ekc⟩, ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨4, e4M, 4 * 8⟩) (4 * 8) = _
    rw [post, msg_eq]
    exact h.ctx.roBytes hp (b := ⟨1, 0, 32⟩) (by decide) (by decide)
  refine Piece.seq (B := Q3) (hash1_piece (Y := Y) e4ST e4WK 136 6 (Enc.bEK Y.sc) bH rate136 (by decide)
    (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨⟨⟨h', by rw [keepBytes hp (by decide) (by decide) fr]; exact h.ekc⟩,
        by rw [keepBytes hp (by decide) (by decide) fr]; exact h.mc⟩, ?_⟩) ?_
  · rw [out, h.ekc, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← H_eq]
  refine Piece.seq (hash2_piece (Y := Y) e4ST e4WK 72 6 (Enc.bM Y.sc) bH (Enc.bKR Y.sc) rate72 (by decide)
    (by decide) (by decide) (by decide) (by decide) (by taint_decide) (by taint_decide) (by taint_decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr out =>
      ⟨h', by rw [keepBytes hp (by decide) (by decide) fr]; exact h.ekc,
        by rw [keepBytes hp (by decide) (by decide) fr]; exact h.mc, ?_⟩) hc
  rw [out, h.mc, h.hh, show (BitVec.ofNat 32 6).setWidth 8 = sha3Suffix from sha3Suffix32, ← padded, ← sha3_512_eq]
  exact (kr_eq s₀).symm

/-! ## The outputs -/

theorem done_keep {s₀ s s' : State} (hp : TPre Y s₀) {bs : List Buf} {M : Nat} (hM : M + 16 ≤ Y.stk)
    (hs : Enc.safe Y bs = true) (hc : Y.apart ⟨Y.sc, e4C + 1408, 160⟩ bs = true) (fr : Frame (FR s₀ bs M) s.mem s'.mem)
    (h : Enc.Done Y I s₀ s) (c : Ctx Y s₀ s') : Enc.Done Y I s₀ s' :=
  ⟨h.toB.keep hp hM hs (Nat.le_refl _) fr c, by rw [keepBytes hp hM hc fr]; exact h.cv⟩

/-- After `K` is copied into `key`. -/
structure F1 (s₀ s : State) : Prop extends Enc.Done Y I s₀ s where
  key : bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32 = (Encaps.kr s₀).take 32

/-- After the ciphertext is copied into `ct`. -/
structure F2 (s₀ s : State) : Prop extends F1 s₀ s where
  ct : Enc.accE Y s₀ s = 1 →
    bytesAt s.mem (Buf.addr s₀ ⟨3, 0, 1568⟩) 1568 = ct1024 (Enc.aE I s₀) (Encaps.ek s₀) (msg s₀) (Enc.rE I s₀)

/-- After `e4ACC` is loaded, to be returned. -/
structure Fin (s₀ s : State) : Prop extends F2 s₀ s where
  eax : s.gpr .eax = Enc.accE Y s₀ s

theorem fin_piece :
    Piece (TPre Y) (TPub Y lk) (Enc.Done Y I) Fin
      (.seq (copyW 4 ⟨4, e4KR, 32⟩ ⟨2, 0, 32⟩ 8) <|
        .seq (copyW 4 ⟨4, e4C, 1568⟩ ⟨3, 0, 1568⟩ 392) (.block [.mov .eax (.mem (at_ .esi e4ACC))])) := by
  refine Piece.seq (B := F1) (copyW_piece (Y := Y) 4 e4KR 2 0 8 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨done_keep hp (M := 0) (by decide) (by decide) (by decide) (fr1 fr) h h', ?_⟩) ?_
  · show bytesAt s'.mem (Buf.addr s₀ ⟨2, 0, 4 * 8⟩) (4 * 8) = _
    rw [post, show kr s₀ = I.kr s₀ from rfl, ← h.kr, bytesAt_take _ _ (show 32 ≤ 64 by decide)]
    rfl
  refine Piece.seq (B := F2) (copyW_piece (Y := Y) 4 e4C 3 0 392 (by decide) (by decide) (by decide)
    (by taint_decide) (by taint_decide) (fun _ _ _ h => h.ctx) fun s₀ s s' hp h h' fr post =>
      ⟨⟨done_keep hp (M := 0) (by decide) (by decide) (by decide) (fr1 fr) h.toDone h',
        by rw [keepBytes hp (N := 0) (by decide) (by decide) (fr1 fr)]; exact h.key⟩, fun e => ?_⟩) ?_
  · have ea : Enc.accE Y s₀ s' = Enc.accE Y s₀ s := keepW hp (N := 0) (by decide) (by decide) (fr1 fr)
    show bytesAt s'.mem (Buf.addr s₀ ⟨3, 0, 4 * 392⟩) (4 * 392) = _
    rw [post]
    exact Enc.ct_eq hS hp h.toDone (ea ▸ e)
  exact ld32_piece (Y := Y) e4ACC (by decide) (by taint_decide) (fun _ _ _ h => h.ctx)
    fun s₀ s s' hp h h' m' e => ⟨⟨⟨done_keep hp (bs := []) (M := 0) (by decide) (by decide) (by decide)
      (m' ▸ Frame.refl _ _) h.toDone h', by rw [m']; exact h.key⟩, fun e₁ => by
        rw [m']; exact h.ct (by show s.mem.readW _ 32 = _; rw [← m']; exact e₁)⟩,
      by rw [e]; show _ = s'.mem.readW _ 32; rw [m']⟩

theorem body_piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = P0 s₀) Fin encaps4Body :=
  start_piece <| .seq (Enc.encrypt_piece hS hρ) fin_piece

theorem piece : Piece (TPre Y) (TPub Y lk) (fun s₀ s => s = s₀) (fun s₀ s' => LeafPost (Fin s₀) s₀ s')
    Impl.MlKem1024.X86.encaps :=
  topLeaf (NoSp.of_all (by decide +kernel)) (body_piece.mono (fun _ _ _ h => h) fun _ _ _ h => ⟨h.ctx, h⟩)

/-- The postcondition, from the final state of the body. -/
theorem post {s₀ s : State} (h : Fin s₀ s) :
    Outcome (fun iters => encapsInternal mlKem1024 iters (ek s₀) (msg s₀)) (Enc.accE Y s₀ s)
      (bytesAt s.mem (Buf.addr s₀ ⟨2, 0, 32⟩) 32, bytesAt s.mem (Buf.addr s₀ ⟨3, 0, 1568⟩) 1568) := by
  have er : Enc.rE I s₀ = (G (msg s₀ ++ H (ek s₀))).2 := by
    show (kr s₀).drop 32 = _; rw [kr_eq]; rfl
  rcases h.acc with e | e
  · obtain ⟨k, hk, hn⟩ := h.fail e
    refine .inr ⟨e, ?_⟩
    show encapsInternal mlKem1024 minIterations (ek s₀) (msg s₀) = none
    rw [encapsInternal1024, kpkeEncrypt1024_none (i := k % 4) (j := k / 4) (by omega) (by omega) hn]
    rfl
  · obtain ⟨M, hM⟩ := Enc.samples h.toDone e
    refine .inl ⟨e, M, ?_⟩
    show encapsInternal mlKem1024 M (ek s₀) (msg s₀) = _
    rw [encapsInternal1024, kpkeEncrypt1024_some hM, h.key, h.ct e, er, kr_eq]
    rfl

/-- Memory with the arguments `0`, `0x800`, `0x1000`, `0x2000` and `0x10000` at `0x5004`. -/
def satMem : Mem := fun a =>
  if a = 0x5009 then 0x08 else if a = 0x500d then 0x10 else if a = 0x5011 then 0x20 else if a = 0x5016 then 1
  else 0

theorem verified : Verified X86.target Impl.MlKem1024.X86.encaps (Spec.MlKem1024.encapsContract X86.abi 88) := by
  refine Piece.verified ((piece.pre_mono (fun _ h => pre_of h) fun _ _ _ _ h => pub_of h).mono
    (fun _ _ _ h => h) fun s₀ s' _ hq => ?_) ?_
  · obtain ⟨habi, -, -, s, hfin, hm, hax⟩ := hq
    refine ⟨habi, ?_⟩
    sig_post [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    rw [setWidth_append32, hax, hfin.eax, hm]
    have r := post hfin
    rw [ek_eq, msg_eq, addr0, addr0, addr0, addr0] at r
    exact r
  · obtain ⟨st, hst⟩ : ∃ st, st = satState satMem [⟨0, 1568⟩, ⟨0x800, 32⟩]
        [⟨0x1000, 32⟩, ⟨0x2000, 1568⟩, ⟨0x10000, 49152⟩, ⟨0x5004, 20⟩] := ⟨_, rfl⟩
    have a0 : arg st 0 = 0 := by rw [hst]; decide
    have a1 : arg st 1 = 0x800 := by rw [hst]; decide
    have a2 : arg st 2 = 0x1000 := by rw [hst]; decide
    have a3 : arg st 3 = 0x2000 := by rw [hst]; decide
    have a4 : arg st 4 = 0x10000 := by rw [hst]; decide
    have e : argAddr st 0 = 0x5004 := by rw [hst]; decide
    have esp : st.gpr .esp = 0x5000 := by rw [hst]; rfl
    refine ⟨st, ?_⟩
    sig_pre [Spec.MlKem1024.encapsContract, Spec.MlKem1024.encapsSig, X86.abi, X86.argSlots, X86.argVal, X86.argBytes]
    simp only [a0, a1, a2, a3, a4, e, esp]
    refine ⟨by decide, by decide, by rw [hst]; rfl, by rw [hst]; rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide, by decide, by decide, by decide,
      by decide⟩ <;>
    exact Region.disjoint_of_sep (by decide)

end VG.Proof.MlKem1024.X86.Encaps
