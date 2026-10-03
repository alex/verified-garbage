import VerifiedGarbage.Proof.Bignum.X86_64.CT

/-!
# `vg_rsa_public` on x86-64: the exponentiation is constant time but for `e`

`expBit` branches on a bit of `e`, which the header holds (`sV`): the runs
agree on it because they agree on `e` (`expBit_ct`).
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public
open VG.Proof.MlKem.X86_64

theorem bitTest_ok {t : State} {B : Addr} {Z w : Nat} {minv : BitVec 64} (hg : Good t B Z w minv)
    (hZ : slot w 8 ≤ Z) {V : Nat} (hV : word t.mem B (8 * sV) = BitVec.ofNat 64 V) (hV' : V < 2 ^ 64) :
    WP isa (.block bitTest) t fun t' => t'.zf = some (decide (V / 128 % 2 = 0)) ∧ t'.mem = t.mem ∧
      Keep [.rax] t t' :=
  WP.mono (WP.keep [.rax] (Q := fun t' => t'.zf = some (decide (V / 128 % 2 = 0)) ∧ t'.mem = t.mem) (by
    unfold bitTest
    xrun [State.ea, hdr, hg.rdi, hdrOff, hg.scr.ld (d := 8 * sV)
      (by have := hdr_lt_slot w 8 (show sV < 32 by decide); omega), hV, bit7 V hV']) rfl)
    fun t' ⟨⟨h1, h2⟩, k⟩ => ⟨h1, h2, k⟩

/-- The public data of a bit: the working space, the bit's byte (shifted) `V`. -/
structure BitPub where
  L : Lay
  V : Nat

/-- Before `expBit`: what its branch and its multiplications need. -/
def BitPre (p : BitPub) (t : State) : Prop :=
  GoodL p.L t ∧ word t.mem p.L.B (8 * sV) = BitVec.ofNat 64 p.V ∧ p.V < 2 ^ 62 ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧
    ((word t.mem p.L.B (slot p.L.w aN)).toNat * p.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv t.mem p.L.B (slot p.L.w aY) p.L.w < wv t.mem p.L.B (slot p.L.w aN) p.L.w ∧
    wv t.mem p.L.B (slot p.L.w aXm) p.L.w < wv t.mem p.L.B (slot p.L.w aN) p.L.w

/-- After the bit test. -/
def BitTested (p : BitPub) (t : State) : Prop := BitPre p t ∧ t.zf = some (decide (p.V / 128 % 2 = 0))

theorem pins_bitPre : Pins BitPre [.rdi] := fun p s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁.1 h₂.1

theorem mm_mid {L : Lay} {t : State} {o a b : Nat} (hg : GoodL L t) (hw : 2 ≤ L.w) (hw' : L.w < 2 ^ 31)
    (ho : o < 8) (ha : a < 8) (hb : b < 8) (d1 : o ≠ aAcc) (d2 : o ≠ aTmp) (d3 : a ≠ aAcc) (d4 : b ≠ aAcc)
    (d5 : o ≠ aN)
    (hinv : ((word t.mem L.B (slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0)
    (hB : wv t.mem L.B (slot L.w b) L.w < wv t.mem L.B (slot L.w aN) L.w) :
    WP isa (mm o a b) t fun t' => GoodL L t' ∧
      wv t'.mem L.B (slot L.w aN) L.w = wv t.mem L.B (slot L.w aN) L.w ∧
      ((word t'.mem L.B (slot L.w aN)).toNat * L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
      wv t'.mem L.B (slot L.w o) L.w < wv t.mem L.B (slot L.w aN) L.w ∧
      Arrays L.B L.w [aAcc, aTmp, o] t.mem t'.mem :=
  WP.mono (mmN_ok hg.1 hg.2 hw hw' ho ha hb d1 d2 d3 d4 d5 rfl hinv hB)
    fun _ ⟨g, n, i, lt, _, ar, _⟩ => ⟨⟨g, hg.2⟩, n, i, lt, ar⟩

/-- `expBit` leaks the same in two runs that agree on the bit. -/
theorem expBit_ct : RelCT isa (Two BitPre) expBit fun _ _ => True := by
  have hn : ∀ {L : Lay} {t : State}, GoodL L t → L.B.toNat + slot L.w 8 ≤ 2 ^ 64 := fun hg => by
    have := hg.1.scr.nowrap; have := hg.2; omega
  unfold expBit
  -- The squaring.
  refine RelCT.seq (two_post (Ψ := BitPre) (two_map (·.L) (fun _ _ h => h.1)
    (montMul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)))
    fun p t h => WP.mono (mm_mid h.1 h.2.2.2.1 h.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) h.2.2.2.2.2.1 h.2.2.2.2.2.2.1)
      fun t' ⟨g, n, i, lt, ar⟩ => ⟨g, by rw [ar.hslot (by decide)]; exact h.2.1, h.2.2.1, h.2.2.2.1,
        h.2.2.2.2.1, i, by rw [n]; exact lt,
        by rw [n, ar.wv_of_not_mem (by decide) (by decide) (hn h.1)]; exact h.2.2.2.2.2.2.2⟩) ?_
  -- The bit.
  refine RelCT.seq (two_piece (Ψ := BitTested) _ pins_bitPre (by taint_decide) fun p t h =>
    WP.mono (bitTest_ok h.1.1 h.1.2 h.2.1 (by have := h.2.2.1; omega)) fun t' ⟨hz, hm, k⟩ =>
      ⟨⟨⟨⟨h.1.1.scr.congr k.2.2, (k.gpr (by decide)).trans h.1.1.rdi, hm ▸ h.1.1.hdr⟩, h.1.2⟩,
        hm ▸ h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, hm ▸ h.2.2.2.2.2.1, hm ▸ h.2.2.2.2.2.2.1,
        hm ▸ h.2.2.2.2.2.2.2⟩, hz⟩) ?_
  -- The multiplication, if the bit is set.
  refine RelCT.seq (R := Two fun (p : BitPub) t => GoodL p.L t) (two_ite (fun p s₁ s₂ h₁ h₂ => by
    simp only [eval, h₁.2, h₂.2]) ?_ ?_) ?_
  · refine two_post (Ψ := fun (p : BitPub) t => GoodL p.L t) (two_map (·.L) (fun _ _ h => h.1.1.1)
      (montMul_ct (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by taint_decide)))
      fun p t h => WP.mono (mm_mid h.1.1.1 h.1.1.2.2.2.1 h.1.1.2.2.2.2.1 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) h.1.1.2.2.2.2.2.1
        h.1.1.2.2.2.2.2.2.2) fun _ h' => h'.1
  · exact RelCT.block_nil fun _ _ hp => two_mono (fun _ _ h => h.1.1.1) hp
  -- The next bit.
  exact two_taint _ (fun (p : BitPub) s₁ s₂ h₁ h₂ => pins_good p.L s₁ s₂ h₁ h₂) (by taint_decide)

/-- The `ne` condition after a count that sets ZF when `j + 1 = n`. -/
theorem eval_ne_count {s : State} {j n : Nat} (hj : j < n) (hz : s.zf = some (decide (j + 1 = n))) :
    isa.eval .ne s = some (decide (j + 1 < n)) := by
  simp only [eval, hz, Option.map_some, Option.some.injEq]
  by_cases h : j + 1 = n
  · simp [h]
  · simp only [h, decide_false, Bool.not_false]; exact (decide_eq_true (by omega)).symm

/-! ## The bits of a byte -/

/-- The public data of the bits of a byte: the working space, `m`, the
exponent so far `E` and the byte `v`. -/
structure BitsPub where
  L : Lay
  N : Nat
  E : Nat
  v : Nat

/-- After `j` bits of a byte. -/
def BitsInv (p : BitsPub) (j : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), BitInv t₀ p.L.B p.L.Z p.L.w p.L.minv p.N X x p.E p.v j s ∧
    slot p.L.w 8 ≤ p.L.Z ∧ 2 ≤ p.L.w ∧ p.L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * p.L.w)) p.N ∧ X < p.N ∧
    X % p.N = x * 2 ^ (64 * p.L.w) % p.N ∧ p.v < 256

theorem bitsInv_pre {p : BitsPub} {j : Nat} {s : State} (hj : j < 8) (h : BitsInv p j s) :
    BitPre ⟨p.L, p.v * 2 ^ j⟩ s := by
  obtain ⟨t₀, X, x, hI, hZ, hw, hw', -, hXN, -, hv⟩ := h
  obtain ⟨Y, hY, hYN, -⟩ := hI.y
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  exact ⟨⟨hI.ctx.good, hZ⟩, hI.v, show p.v * 2 ^ j < 2 ^ 62 by have := Nat.mul_le_mul_left p.v hp; omega, hw, hw', hI.ctx.inv,
    by rw [hY, hI.ctx.n]; exact hYN, by rw [hI.ctx.x, hI.ctx.n]; exact hXN⟩

/-- The eight bits of a byte leak the same in runs that agree on it. -/
theorem bits_ct : RelCT isa (Two fun p s => 0 < 8 ∧ BitsInv p 0 s) (.loop expBit .ne)
    (Two fun p s => BitsInv p 8 s) :=
  two_loop (Φ := BitsInv) (fun _ => 8)
    (two_map (fun q : BitsPub × Nat => (⟨q.1.L, q.1.v * 2 ^ q.2⟩ : BitPub))
      (fun _ _ h => bitsInv_pre h.1 h.2) expBit_ct)
    fun _ _ _ hj ⟨t₀, X, x, hI, hZ, hw, hw', hR, hXN, hXc, hv⟩ =>
      WP.mono (bitStep_ok hZ hw hw' hR hXN hXc hv hj hI) fun _ ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hj hz, fun _ => ⟨t₀, X, x, hI', hZ, hw, hw', hR, hXN, hXc, hv⟩,
          fun h => h ▸ ⟨t₀, X, x, hI', hZ, hw, hw', hR, hXN, hXc, hv⟩⟩

/-! ## The bytes of `e` -/

/-- The public data of the exponentiation: the working space, `m`, and the
`len` bytes `eb` of `e` at `ep`. -/
structure EPub where
  L : Lay
  N : Nat
  ep : Addr
  len : Nat
  eb : List Byte

/-- What the exponentiation's steps need of the bytes of `e`, from `t₀`. -/
def ESrc (a : EPub) (t₀ : State) : Prop :=
  a.eb.length = a.len ∧ a.len < 2 ^ 31 ∧
    (∀ i < a.len, InRegions (t₀.rd ++ t₀.wr) (a.ep + BitVec.ofNat 64 i) 1) ∧
    (∀ i (_ : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb.getD i 0) ∧
    (∀ i < a.len, a.L.Z ≤ ofs a.L.B (a.ep + BitVec.ofNat 64 i))

/-- The working space's and `m`'s facts every step needs. -/
def EFacts (a : EPub) (X x : Nat) : Prop :=
  slot a.L.w 8 ≤ a.L.Z ∧ 2 ≤ a.L.w ∧ a.L.w < 2 ^ 31 ∧ Nat.Coprime (2 ^ (64 * a.L.w)) a.N ∧ X < a.N ∧
    X % a.N = x * 2 ^ (64 * a.L.w) % a.N

/-- After `i` bytes of `e`. -/
def BytesInv (a : EPub) (i : Nat) (s : State) : Prop :=
  ∃ (t₀ : State) (X x : Nat), ByteInv t₀ a.L.B a.L.Z a.L.w a.L.minv a.N X x a.ep a.len a.eb i s ∧
    EFacts a X x ∧ ESrc a t₀

theorem ESrc.bytes {a : EPub} {t₀ : State} (h : ESrc a t₀) :
    ∀ i (hi : i < a.len), t₀.mem (a.ep + BitVec.ofNat 64 i) = a.eb[i]'(by have := h.1; omega) :=
  fun i hi => by rw [h.2.2.2.1 i hi]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by have := h.1; omega]

/-- After `byteHead`'s loads. -/
def HeadMid (q : EPub × Nat) (s : State) : Prop :=
  q.2 < q.1.len ∧ BytesInv q.1 q.2 s ∧ s.gpr .rax = q.1.ep ∧ s.gpr .rcx = BitVec.ofNat 64 q.2

/-- The bits of byte `i`. -/
def bitsPub (q : EPub × Nat) : BitsPub := ⟨q.1.L, q.1.N, pre q.1.eb q.2, (q.1.eb.getD q.2 0).toNat⟩

theorem pins_bytes : Pins (fun (q : EPub × Nat) s => q.2 < q.1.len ∧ BytesInv q.1 q.2 s) [.rdi] :=
  fun _ _ _ ⟨_, _, _, _, h₁, _⟩ ⟨_, _, _, _, h₂, _⟩ r hr => by
    simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]

theorem pins_headMid : Pins HeadMid [.rdi, .rax, .rcx] := by
  intro q s₁ s₂ h₁ h₂ r hr
  obtain ⟨-, ⟨_, _, _, i₁, _⟩, a₁, c₁⟩ := h₁
  obtain ⟨-, ⟨_, _, _, i₂, _⟩, a₂, c₂⟩ := h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · rw [i₁.ctx.good.rdi, i₂.ctx.good.rdi]
  · rw [a₁, a₂]
  · rw [c₁, c₂]

/-- One byte of `e` leaks the same in runs that agree on `e`. -/
theorem byteBody_ct : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ BytesInv q.1 q.2 s)
    (.seq (.block byteHead) (.seq (.loop expBit .ne) (.block byteNext))) fun _ _ => True := by
  rw [byteHead_eq]
  have w₁ : ∀ (q : EPub × Nat) s, q.2 < q.1.len ∧ BytesInv q.1 q.2 s →
      WP isa (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) s (HeadMid q) := by
    rintro q s ⟨hi, t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (byteHead1_ok hf.1 hI) fun t ⟨h1, h2, h3⟩ => ⟨hi, ⟨t₀, X, x, h3, hf, hsrc⟩, h1, h2⟩
  have w₂ : ∀ (q : EPub × Nat) s, HeadMid q s →
      WP isa (.block [.movzx8 .rax { base := .rax, index := some .rcx }, .store (hdr sV) .rax,
        .mov32 .rax (.imm 8), .store (hdr sBit) .rax]) s fun t => 0 < 8 ∧ BitsInv (bitsPub q) 0 t := by
    rintro q s ⟨hi, ⟨t₀, X, x, hI, hf, hsrc⟩, hax, hcx⟩
    refine WP.mono (byteHead2_ok hf.1 hsrc.1 hi hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI hax hcx)
      fun t ⟨_, _, hB⟩ => ⟨by decide, t, X, x, ?_, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1,
        hf.2.2.2.2.2, ?_⟩
    · simp only [bitsPub, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show q.2 < q.1.eb.length by have := hsrc.1; omega), Option.getD_some]
      exact hB
    · simp only [bitsPub]; exact (List.getD q.1.eb q.2 0).isLt
  have h₁ : RelCT isa (Two fun (q : EPub × Nat) s => q.2 < q.1.len ∧ BytesInv q.1 q.2 s)
      (.block [.mov .rax (.mem (hdr sE)), .mov .rcx (.mem (hdr sI))]) (Two HeadMid) :=
    two_piece _ pins_bytes (by taint_decide) w₁
  have h₂ : RelCT isa (Two HeadMid) (.block [.movzx8 .rax { base := .rax, index := some .rcx },
      .store (hdr sV) .rax, .mov32 .rax (.imm 8), .store (hdr sBit) .rax])
      (Two fun q s => 0 < 8 ∧ BitsInv (bitsPub q) 0 s) :=
    two_piece _ pins_headMid (by taint_decide) w₂
  have h₃ : RelCT isa (Two fun (p : BitsPub) s => BitsInv p 8 s) (.block byteNext) fun _ _ => True :=
    two_taint [.rdi] (fun (_ : BitsPub) s₁ s₂ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.ctx.good.rdi, h₂.ctx.good.rdi]) (by taint_decide)
  exact RelCT.seq (RelCT.block_append (RelCT.seq h₁ h₂))
    (RelCT.seq (two_map bitsPub (fun _ _ h => h) bits_ct) h₃)

/-- Before `expLoop`. -/
def ExpPre (a : EPub) (s : State) : Prop :=
  ∃ X x Y : Nat, ExpCtx s a.L.B a.L.Z a.L.w a.L.minv a.N X ∧ EFacts a X x ∧
    wv s.mem a.L.B (slot a.L.w aY) a.L.w = Y ∧ Y < a.N ∧ Y % a.N = 2 ^ (64 * a.L.w) % a.N ∧
    word s.mem a.L.B (8 * sE) = a.ep ∧ word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    1 ≤ a.len ∧ ESrc a s

/-- The exponentiation leaks the same in runs that agree on `e`. -/
theorem expLoop_ct : RelCT isa (Two ExpPre) expLoop (Two fun a s => BytesInv a a.len s) := by
  unfold expLoop
  refine RelCT.seq (two_piece (Ψ := fun a s => 0 < a.len ∧ BytesInv a 0 s) [.rdi]
    (fun _ _ _ ⟨_, _, _, h₁, _⟩ ⟨_, _, _, h₂, _⟩ r hr => by
      simp only [List.mem_singleton] at hr; subst hr; rw [h₁.good.rdi, h₂.good.rdi]) (by taint_decide) ?_) ?_
  · rintro a s ⟨X, x, Y, hc, hf, hY, hYN, hYc, he, hlen, hL1, hsrc⟩
    exact WP.mono (expInit_ok (x := x) (eb := a.eb) hc hf.1 hY hYN hYc he hlen) fun t h =>
      ⟨hL1, s, X, x, h, hf, hsrc⟩
  · refine two_loop (Φ := BytesInv) (fun a => a.len) byteBody_ct ?_
    rintro a i s hi ⟨t₀, X, x, hI, hf, hsrc⟩
    exact WP.mono (byte_ok hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2 hsrc.1 hsrc.2.1 hi
      hsrc.2.2.1 hsrc.bytes hsrc.2.2.2.2 hI) fun s' ⟨hz, hI'⟩ =>
        ⟨eval_ne_count hi hz, fun _ => ⟨t₀, X, x, hI', hf, hsrc⟩, fun h => h ▸ ⟨t₀, X, x, hI', hf, hsrc⟩⟩

/-! ## The exponentiation phase -/

/-- Before the exponentiation phase (`expPhase_ok`'s hypotheses). -/
def EPhasePre (a : EPub) (s : State) : Prop :=
  ∃ X : Nat, Good s a.L.B a.L.Z a.L.w a.L.minv ∧ slot a.L.w 8 ≤ a.L.Z ∧ 2 ≤ a.L.w ∧ a.L.w < 2 ^ 31 ∧
    a.N % 2 = 1 ∧ 1 < a.N ∧ wv s.mem a.L.B (slot a.L.w aN) a.L.w = a.N ∧
    ((word s.mem a.L.B (slot a.L.w aN)).toNat * a.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem a.L.B (slot a.L.w aX) a.L.w = X ∧ wv s.mem a.L.B (slot a.L.w aOne) a.L.w = 1 ∧
    wv s.mem a.L.B (slot a.L.w aR2) a.L.w < a.N ∧
    wv s.mem a.L.B (slot a.L.w aR2) a.L.w % a.N = 2 ^ (64 * a.L.w) * 2 ^ (64 * a.L.w) % a.N ∧
    word s.mem a.L.B (8 * sE) = a.ep ∧ word s.mem a.L.B (8 * sElen) = BitVec.ofNat 64 a.len ∧
    a.eb.length = a.len ∧ 1 ≤ a.len ∧ a.len < 2 ^ 31 ∧ Src s a.L.B a.L.Z a.ep a.eb

/-- After `Y := R`. -/
def EPhase1 (a : EPub) (s : State) : Prop :=
  ∃ (X : Nat) (σ : State), EPhasePre a σ ∧ Good s a.L.B a.L.Z a.L.w a.L.minv ∧
    wv σ.mem a.L.B (slot a.L.w aX) a.L.w = X ∧
    wv s.mem a.L.B (slot a.L.w aN) a.L.w = a.N ∧
    ((word s.mem a.L.B (slot a.L.w aN)).toNat * a.L.minv.toNat + 1) % 2 ^ 64 = 0 ∧
    wv s.mem a.L.B (slot a.L.w aY) a.L.w < a.N ∧
    wv s.mem a.L.B (slot a.L.w aY) a.L.w % a.N = 2 ^ (64 * a.L.w) % a.N ∧
    Frm a.L.B (expPhaseRanges a.L.w) σ.mem s.mem ∧ Keep mmRegs σ s

theorem src_esrc {a : EPub} {s : State} (h : Src s a.L.B a.L.Z a.ep a.eb) (hl : a.eb.length = a.len)
    (hl' : a.len < 2 ^ 31) : ESrc a s :=
  ⟨hl, hl', fun i hi => h.rd i (by omega), fun i hi => by
    rw [h.val i (by omega)]; simp [List.getD_eq_getElem?_getD, show i < a.eb.length by omega],
    fun i hi => h.out i (by omega)⟩

/-- The exponentiation phase leaks the same in runs that agree on `e`. -/
theorem expPhase_ct : RelCT isa (Two EPhasePre) (seqs expSteps) fun _ _ => True := by
  unfold expSteps
  have mmct : ∀ {o a b : Nat} {hc : VG.Taint.Hint VG.X86_64.Taint.T}, o < 8 → a < 8 → b < 8 →
      (taint.check (Taint.ofRegs [.rdi]) (.block (bases o a b aN aAcc aTmp)) hc).isSome = true →
      RelCT isa (Two fun (q : EPub) s => GoodL q.L s) (mm o a b) fun _ _ => True :=
    fun ho ha hb h => two_map (·.L) (fun _ _ h => h) (montMul_ct (by decide) (by decide) (by decide) ho ha hb h)
  -- `Y := R`.
  refine RelCT.seq (two_post (Ψ := EPhase1) (two_map id (fun a s ⟨_, hg, hZ, _⟩ => ⟨hg, hZ⟩)
    (mmct (by decide) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · rintro a s ⟨X, hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone, hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩
    have hR : Nat.Coprime (2 ^ (64 * a.L.w)) a.N := VG.Proof.Bignum.coprime_pow2 hodd _
    refine WP.mono (mmN_ok (o := aY) (a := aR2) (b := aOne) hg hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn hinv (by rw [hone]; exact hN1))
      fun t₁ ⟨hg₁, hn₁, hinv₁, hlt₁, hm₁, ha₁, k₁⟩ => ⟨X, s, ⟨X, hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX, hone,
        hlt2, hr2, he, hlen, hL, hL1, hL', heb⟩, hg₁, hX, hn₁, hinv₁, hlt₁, ?_, Frm.ep_of_arrays ha₁ (by simp), k₁⟩
    apply VG.Proof.Bignum.mont_cancel hR
    rw [hm₁, hone, Nat.mul_one, hr2]
  -- `X := x R`.
  refine RelCT.seq (two_post (Ψ := ExpPre) (two_map id (fun a s ⟨_, σ, hσ, hg, _⟩ =>
      ⟨hg, hσ.choose_spec.2.1⟩) (mmct (by decide) (by decide) (by decide) (by taint_decide))) ?_) ?_
  · rintro a s ⟨X, σ, ⟨X', hg, hZ, hw, hw', hodd, hN1, hn, hinv, hX', hone, hlt2, hr2, he, hlen, hL, hL1, hL',
      heb⟩, hg₁, hX, hn₁, hinv₁, hlt₁, hY₁, f₁, k₁⟩
    have hn' : a.L.B.toNat + slot a.L.w 8 ≤ 2 ^ 64 := by have := hg.scr.nowrap; omega
    have hR : Nat.Coprime (2 ^ (64 * a.L.w)) a.N := VG.Proof.Bignum.coprime_pow2 hodd _
    refine WP.mono (mmN_ok (o := aXm) (a := aX) (b := aR2) hg₁ hZ hw hw' (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hn₁ hinv₁
      (by rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hlt2))
      fun t₂ ⟨hg₂, hn₂, hinv₂, hlt₂, hm₂, ha₂, k₂⟩ => ?_
    rw [f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide),
      f₁.ep_wv hn' (by decide) (by decide) (by decide) (by decide) (by decide), hX] at hm₂
    have hX₂ : wv t₂.mem a.L.B (slot a.L.w aXm) a.L.w % a.N = X * 2 ^ (64 * a.L.w) % a.N := by
      apply VG.Proof.Bignum.mont_cancel hR
      rw [hm₂, Nat.mul_mod, hr2, ← Nat.mul_mod, Nat.mul_assoc]
    have hY₂ : wv t₂.mem a.L.B (slot a.L.w aY) a.L.w = wv s.mem a.L.B (slot a.L.w aY) a.L.w :=
      ha₂.wv_of_not_mem (by decide) (by decide) hn'
    have f₁₂ := f₁.trans (Frm.ep_of_arrays ha₂ (by simp))
    have hin : InScr a.L.B a.L.Z σ.mem t₂.mem :=
      InScr.of_frm f₁₂ fun r hr => (expPhaseRanges_le _ r hr).trans hZ
    have heb₂ := heb.congrK hin (k₁.trans k₂)
    exact ⟨_, X, _, ⟨hg₂, hn₂, hinv₂, rfl⟩, ⟨hZ, hw, hw', hR, hlt₂, hX₂⟩, hY₂, hlt₁, hY₁,
      by rw [f₁₂.ep_hdr (by decide) (by decide) (by decide) (by decide)]; exact he,
      by rw [f₁₂.ep_hdr (by decide) (by decide) (by decide) (by decide)]; exact hlen, hL1,
      src_esrc heb₂ hL hL'⟩
  -- The exponentiation, and `Y R⁻¹`.
  exact RelCT.seq expLoop_ct (two_map id (fun a s ⟨_, _, _, hI, hf, _⟩ => ⟨hI.ctx.good, hf.1⟩)
    (mmct (by decide) (by decide) (by decide) (by taint_decide)))

end VG.Proof.Bignum.X86_64
