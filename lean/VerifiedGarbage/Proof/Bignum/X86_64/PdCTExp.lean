import VerifiedGarbage.Proof.Bignum.X86_64.PdExp
import VerifiedGarbage.Proof.Bignum.X86_64.CTExp

/-!
# `vg_rsa_public_precomputed` on x86-64: the exponentiation is constant time but for `e`

Besides the bits of `e` (as in `CTExp.lean`), the exponentiation branches on
whether it has started, which is whether the prefix of `e` so far is
nonzero: the runs agree on it because they agree on `e` (`pExpBit_ct`,
`pExpLoop_ct`, `finish_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Impl.Rsa.X86_64.Precomputed
open VG.Proof.MlKem.X86_64

variable {M : Mont}

/-! ## A bit -/

/-- The public data of a bit: the working space, `m`, the prefix `E` of `e`
so far and the bit's byte (shifted) `V`. -/
structure PBitPub where
  L : Lay
  N : Nat
  E : Nat
  V : Nat

/-- What every step needs of the working space and `X ≡ x R`. -/
def PFacts (L : Lay) (N X x : Nat) : Prop :=
  slot L.w 8 ≤ L.Z ∧ 2 ≤ L.w ∧ L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * L.w)) N ∧ X < N ∧
    X % N = x * 2 ^ (64 * L.w) % N

/-- Before a step of a bit, after the prefix `E`. -/
def PQ (p : PBitPub) (t : State) : Prop :=
  ∃ X x, ExpCtx t p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt t.mem p.L.B p.L.w p.N x p.E ∧ PFacts p.L p.N X x ∧
    word t.mem p.L.B (8 * sV) = BitVec.ofNat 64 p.V ∧ p.V < 2 ^ 62

theorem pins_PQ : Pins PQ [.rdi] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]

theorem PQ.goodL {p : PBitPub} {t : State} (h : PQ p t) : GoodL p.L t :=
  let ⟨_, _, hc, _, hf, _⟩ := h; ⟨hc.good, hf.1⟩

/-- The started test keeps `PQ`. -/
theorem startedTest_pq {p : PBitPub} {t : State} (h : PQ p t) :
    WP isa (.block startedTest) t fun t' => PQ p t' ∧ t'.zf = some (decide (p.E = 0)) := by
  obtain ⟨X, x, hc, hy, hf, hV, hV'⟩ := h
  exact WP.mono (startedTest_ok hc.good hf.1 hy) fun t' ⟨hz, hm, k⟩ =>
    ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩, hz⟩

/-- `start` leaks the same in runs with the same working space. -/
theorem start_ct : RelCT isa (Two GoodL) start fun _ _ => True := by
  unfold start
  refine RelCT.seq (two_piece (Ψ := fun (L : Lay) t => t.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t.gpr .rsi = off L.B (slot L.w aXm) ∧ t.gpr .rbx = off L.B (slot L.w aY) ∧ t.gpr .rdi = L.B) [.rdi]
    pins_good (by taint_decide) ?_)
    (two_taint [.rsi, .rbx, .r12, .rdi] (fun L s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2.1, h₂.2.2.1]
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.2.2, h₂.2.2.2]) (by taint_decide))
  rintro L t ⟨hg, hZ⟩
  have hn := hg.scr.nowrap
  have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off L.B (8 * i)) 8 := fun i hi =>
    hg.scr.ld (by have := hdr_lt_slot L.w 8 hi; omega)
  refine WP.mono (WP.keep [.r12, .rsi, .rbx] (Q := fun t₁ => t₁.gpr .r12 = BitVec.ofNat 64 L.w ∧
      t₁.gpr .rsi = off L.B (slot L.w aXm) ∧ t₁.gpr .rbx = off L.B (slot L.w aY)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl sW (by decide), hl (sArr aXm) (by decide),
      hl (sArr aY) (by decide), hg.hdr.hw, hg.hdr.harr aXm (by decide), hg.hdr.harr aY (by decide)]) rfl)
    fun t₁ ⟨⟨h12, hsi, hbx⟩, k⟩ => ⟨h12, hsi, hbx, (k.gpr (by decide)).trans hg.rdi⟩

/-- A bit leaks the same in runs that agree on `e`. -/
theorem pExpBit_ct : RelCT isa (Two PQ) (Precomputed.expBit M.mm) fun _ _ => True := by
  unfold Precomputed.expBit
  -- Whether started.
  refine RelCT.seq (two_piece (Ψ := fun p t => PQ p t ∧ t.zf = some (decide (p.E = 0))) _ pins_PQ
    (by taint_decide) fun p t h => startedTest_pq h) ?_
  -- `Y := Y²` if started.
  refine RelCT.seq (R := Two fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2])
      (two_map (·.L) (fun _ _ h => h.1.1.goodL) (M.ct (by unfold MmUse; decide)))
      (RelCT.block_nil fun _ _ _ => trivial)) ?_) ?_
  · rintro p t ⟨⟨X, x, hc, hy, hf, hV, hV'⟩, hz⟩
    exact WP.mono (pSq_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hy hz) fun t' ⟨hc', hy', ha, _⟩ =>
      ⟨X, x, hc', hy', hf, by rw [ha.hslot (by decide)]; exact hV, hV'⟩
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
      t.zf = some (decide (p.V / 128 % 2 = 0))) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_PQ _ s₁ s₂ h₁ h₂)
    (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hf, hV, hV'⟩
    exact WP.mono (bitTest_ok hc.good hf.1 hV (by omega)) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hf, by rw [hm]; exact hV, hV'⟩, hz⟩
  -- If the bit is set: `Y := Y X` once started, `Y := X` and started if not; then the next bit.
  refine RelCT.seq (R := Two fun (p : PBitPub) t => t.gpr .rdi = p.L.B)
    (two_post (two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_
      (RelCT.block_nil fun _ _ _ => trivial)) ?_)
    (two_taint [.rdi] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁, h₂]) (by taint_decide))
  · refine RelCT.seq (two_piece (Ψ := fun (p : PBitPub) t => PQ ⟨p.L, p.N, 2 * p.E, p.V⟩ t ∧
        t.zf = some (decide (2 * p.E = 0))) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_PQ _ s₁ s₂ h₁.1.1 h₂.1.1)
      (by taint_decide) fun p t h => startedTest_pq h.1.1) ?_
    refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
    · exact two_map (fun (p : PBitPub) => p.L) (fun _ _ h => h.1.1.goodL)
        (M.ct (by unfold MmUse; decide))
    · exact two_map (fun (p : PBitPub) => p.L) (fun _ _ h => h.1.1.goodL) start_ct
  · rintro p t ⟨⟨X, x, hc, hy, hf, -, -⟩, hz⟩
    exact WP.mono (pMul_ok hc hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hy hz)
      fun t' ⟨hc', _⟩ => hc'.good.rdi

/-! ## The bits of a byte -/

/-- After `j` bits of a byte. -/
def PBitsInv (p : BitsPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PBitInv t₀ p.L.B p.L.Z p.L.w p.L.minv p.N X x p.E p.v j s ∧
    PFacts p.L p.N X x ∧ p.v < 256

theorem pBitsInv_pq {p : BitsPub} {j : Nat} {s : State} (hj : j < 8) (h : PBitsInv p j s) :
    PQ ⟨p.L, p.N, p.E * 2 ^ j + p.v / 2 ^ (8 - j), p.v * 2 ^ j⟩ s := by
  obtain ⟨t₀, X, x, hI, hf, hv⟩ := h
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨X, x, hI.ctx, hI.y, hf, hI.v, by have := Nat.mul_le_mul_left p.v hp; dsimp only; omega⟩

/-- The eight bits of a byte leak the same in runs that agree on `e`. -/
theorem pBits_ct : RelCT isa (Two fun p s => 0 < 8 ∧ PBitsInv p 0 s) (.loop (Precomputed.expBit M.mm) .ne)
    (Two fun p s => PBitsInv p 8 s) :=
  two_loop (Φ := PBitsInv) (fun _ => 8)
    (two_map (fun q : BitsPub × Nat =>
      (⟨q.1.L, q.1.N, q.1.E * 2 ^ q.2 + q.1.v / 2 ^ (8 - q.2), q.1.v * 2 ^ q.2⟩ : PBitPub))
      (fun _ _ h => pBitsInv_pq h.1 h.2) pExpBit_ct)
    fun _ _ _ hj ⟨t₀, X, x, hI, hf, hv⟩ =>
      WP.mono (pBitStep_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, X, x, hI', hf, hv⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hv⟩⟩

/-! ## The bytes of `e` -/

/-- After `i` bytes of `e`. -/
def PBytesInv (a : EPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), PByteInv t₀ a.L.B a.L.Z a.L.w a.L.minv a.N X x a.ep a.len a.eb i s ∧
    EFacts a X x ∧ ESrc a t₀

/-- After `byteHead`'s loads. -/
def PHeadMid (q : EPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ PBytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ep ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

theorem pins_pBytes : Pins (fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]

theorem pins_pHeadMid : Pins PHeadMid [.rdi, .rax, .rcx] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, ⟨_, _, _, i₁, _⟩, a₁, c₁⟩ := h₁
  obtain ⟨-, ⟨_, _, _, i₂, _⟩, a₂, c₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of `e` leaks the same in runs that agree on `e`. -/
theorem pByteBody_ct : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s)
    (.seq (.block byteHead) (.seq (.loop (Precomputed.expBit M.mm) .ne) (.block byteNext))) fun _ _ => True := by
  rw [byteHead_eq]
  have w₁ : ∀ (q : EPub × Nat) s, q.2 < q.1.len ∧ PBytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) s (PHeadMid q) := by
    rintro q s ⟨hi, t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByteHead1_ok hf.1 hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, X, x, h3, hf, hsrc⟩, h1, h2⟩
  have w₂ : ∀ (q : EPub × Nat) s, PHeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr sV) .rax,
        .mov32 .rax (.imm 8), .store (hdr sBit) .rax]) s fun t => 0 < 8 ∧ PBitsInv (bitsPub q) 0 t := by
    rintro q s ⟨hi, ⟨t₀, X, x, hI, hf, hsrc⟩, hax, hcx⟩
    refine WP.mono (pByteHead2_ok hf.1 hsrc.1 hi hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI hax hcx)
      fun t ⟨_, _, hB⟩ => ⟨by decide, t, X, x, ?_, hf, ?_⟩
    · simp only [bitsPub, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show q.2 < q.1.eb.length by have := hsrc.1; omega), Option.getD_some]
      exact hB
    · simp only [bitsPub]; exact (List.getD q.1.eb q.2 0).isLt
  have h₁ : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ PBytesInv q.1 q.2 s)
      (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) (Two PHeadMid) :=
    two_piece _ pins_pBytes (by taint_decide) w₁
  have h₂ : RelCT isa (Two PHeadMid) (.block [.movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr sV) .rax, .mov32 .rax (.imm 8), .store (hdr sBit) .rax])
      (Two fun q s => 0 < 8 ∧ PBitsInv (bitsPub q) 0 s) :=
    two_piece _ pins_pHeadMid (by taint_decide) w₂
  have h₃ : RelCT isa (Two fun (p : BitsPub) s => PBitsInv p 8 s) (.block byteNext) fun _ _ => True :=
    two_taint [.rdi] (fun (_ : BitsPub) s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq h₁ h₂))
    (RelCT.seq (two_map bitsPub (fun _ _ h => h) pBits_ct) h₃)

/-- Before `expLoop`. -/
def PExpPre (a : EPub) (s : State) : Prop :=
  ∃ X x : Nat, ExpCtx s a.L.B a.L.Z a.L.w a.L.minv a.N X ∧ EFacts a X x ∧
    word s.mem a.L.B (8 * sE) = a.ep ∧ word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    1 ≤ a.len ∧ ESrc a s

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem pExpLoop_ct : RelCT isa (Two PExpPre) (Precomputed.expLoop M.mm) (Two fun a s => PBytesInv a a.len s) := by
  unfold Precomputed.expLoop
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < a.len ∧ PBytesInv a 0 s) [.rdi]
    (fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]) (by taint_decide) ?_) ?_
  · rintro a s ⟨X, x, hc, hf, he, hlen, hL1, hsrc⟩
    exact WP.mono (pExpInit_ok (x := x) (eb := a.eb) hc hf.1 he hlen) fun t h => ⟨hL1, s, X, x, h, hf, hsrc⟩
  · refine two_loop (Φ := PBytesInv) (fun a => a.len) pByteBody_ct ?_
    rintro a i s hi ⟨t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (pByte_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hsrc.1 hsrc.2.1 hi
      hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hi hz, fun _ => ⟨t₀, X, x, hI', hf, hsrc⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hsrc⟩⟩

/-! ## The result -/

/-- The public data of `finish`: the working space, `m` and `e`. -/
structure FPub where
  L : Lay
  N : Nat
  E : Nat

/-- Before `finish`. -/
def FPre (p : FPub) (s : State) : Prop :=
  ∃ X x, ExpCtx s p.L.B p.L.Z p.L.w p.L.minv p.N X ∧ YSt s.mem p.L.B p.L.w p.N x p.E ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31

theorem pins_FPre : Pins FPre [.rdi] := fun _ _ _ ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩ r hr => by
  simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]

/-- `finish` leaks the same in runs that agree on `e`. -/
theorem finish_ct : RelCT isa (Two FPre) (Precomputed.finish M.mm) fun _ _ => True := by
  unfold Precomputed.finish
  refine RelCT.seq (two_piece (Ψ := fun p t => FPre p t ∧ t.zf = some (decide (p.E = 0))) _ pins_FPre
    (by taint_decide) ?_) ?_
  · rintro p t ⟨X, x, hc, hy, hZ, hw, hw'⟩
    exact WP.mono (startedTest_ok hc.good hZ hy) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨X, x, hc.mem hm k (by decide), by rw [hm]; exact hy, hZ, hw, hw'⟩, hz⟩
  refine two_ite (fun p s₁ s₂ h₁ h₂ => by simp only [eval, h₁.2, h₂.2]) ?_ ?_
  · exact two_map (fun (p : FPub) => p.L) (fun _ _ ⟨⟨⟨_, _, hc, _, hZ, _⟩, _⟩, _⟩ => ⟨hc.good, hZ⟩)
      (M.ct (by unfold MmUse; decide))
  -- `Y := 1`.
  unfold setWord
  refine RelCT.seq (two_piece (Ψ := fun (p : FPub) t => GoodL p.L t ∧ t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
      t.gpr .rcx = BitVec.ofNat 64 0) [.rdi] (fun p s₁ s₂ h₁ h₂ => pins_FPre p s₁ s₂ h₁.1.1 h₂.1.1)
    (by taint_decide) ?_) ?_
  · rintro p t ⟨⟨⟨X, x, hc, hy, hZ, hw, hw'⟩, _⟩, _⟩
    have hl : ∀ i < 32, InRegions (t.rd ++ t.wr) (off p.L.B (8 * i)) 8 := fun i hi =>
      hc.good.scr.ld (by have := hdr_lt_slot p.L.w 8 hi; have := hc.good.scr.nowrap; omega)
    refine WP.mono (WP.keep [.r12, .rdx, .rcx] (Q := fun t₂ => t₂.gpr .r12 = BitVec.ofNat 64 p.L.w ∧
        t₂.gpr .rcx = BitVec.ofNat 64 0 ∧ t₂.mem = t.mem) (by
      xrun [State.ea, hdr, hc.good.rdi, hdrOff, hl sW (by decide), hc.good.hdr.hw]) rfl)
      fun t₂ ⟨⟨h12, hcx, hm⟩, k⟩ => ⟨⟨(hc.mem hm k (by decide)).good, hZ⟩, h12, hcx⟩
  refine RelCT.seq (two_piece (Ψ := fun (p : FPub) t => t.gpr .r8 = off p.L.B (slot p.L.w aY) ∧
      t.gpr .r12 = BitVec.ofNat 64 p.L.w ∧ t.gpr .rcx = BitVec.ofNat 64 0) [.rdi]
    (fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1) (by taint_decide) ?_)
    (two_taint [.r8, .r12, .rcx] (fun p s₁ s₂ h₁ h₂ r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · rw [h₁.1, h₂.1]
      · rw [h₁.2.1, h₂.2.1]
      · rw [h₁.2.2, h₂.2.2]) (by taint_decide))
  rintro p t ⟨⟨hg, hZ⟩, h12, hcx⟩
  have hl : InRegions (t.rd ++ t.wr) (off p.L.B (8 * sArr aY)) 8 :=
    hg.scr.ld (by have := hdr_lt_slot p.L.w 8 (show sArr aY < 32 by decide); have := hg.scr.nowrap; omega)
  refine WP.mono (WP.keep [.r8] (Q := fun t' => t'.gpr .r8 = off p.L.B (slot p.L.w aY)) (by
    xrun [State.ea, hdr, hg.rdi, hdrOff, hl, hg.hdr.harr aY (by decide)]) rfl)
    fun t' ⟨h8, k⟩ => ⟨h8, (k.gpr (by decide)).trans h12, (k.gpr (by decide)).trans hcx⟩

end VG.Proof.Bignum.X86_64
