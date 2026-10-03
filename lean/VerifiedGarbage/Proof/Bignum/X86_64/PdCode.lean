import VerifiedGarbage.Proof.Bignum.X86_64.PdMain
import VerifiedGarbage.Proof.Bignum.X86_64.PubCode

/-!
# `vg_rsa_public_precomputed` on x86-64: correctness

The entry (`pdEntry_ok`); the values of a valid modulus in `pre` pass the
checks (`checks_true`), and values that pass them make `rest` compute
(`checks_facts`); the whole function (`pdCode_correct`), against
`pdContract`, which states the shared contract's precondition on the
registers and the stack.
-/

namespace VG.Proof.Bignum.X86_64

open VG VG.X86_64 VG.Impl.Bignum.X86_64 VG.Impl.Bignum.X86_64.Public VG.Impl.Rsa.X86_64
open VG.Proof.MlKem.X86_64

/-! ## The contract on the registers and the stack -/

/-- `vg_rsa_public_precomputed(out = rdi, out_len = rsi, pre = rdx,
pre_len = rcx, e = r8, e_len = r9, input = [rsp + 8], input_len = [rsp + 16],
scratch = [rsp + 24], scratch_len = [rsp + 32])`. -/
def pdContract : Contract isa where
  pre s :=
    let out : Region := ⟨s.gpr .rdi, (s.gpr .rsi).toNat⟩
    let pre : Region := ⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩
    let e : Region := ⟨s.gpr .r8, (s.gpr .r9).toNat⟩
    let inp : Region := ⟨stackArg s 0, (stackArg s 1).toNat⟩
    let scr : Region := ⟨stackArg s 2, (stackArg s 3).toNat * 8⟩
    let args : Region := ⟨stackArgAddr s 0, 32⟩
    let ret : Region := ⟨s.gpr .rsp, 8⟩
    (s.gpr .rsp).toNat + 40 ≤ 2 ^ 64 ∧
      s.rd = [pre, e, inp, args] ∧ s.wr = [out, scr] ∧
      out.Disjoint pre ∧ out.Disjoint e ∧ out.Disjoint inp ∧ out.Disjoint scr ∧ out.Disjoint args ∧
      pre.Disjoint scr ∧ e.Disjoint scr ∧ inp.Disjoint scr ∧ scr.Disjoint args ∧
      ret.Disjoint out ∧ ret.Disjoint pre ∧ ret.Disjoint e ∧ ret.Disjoint inp ∧ ret.Disjoint scr ∧
      ret.Disjoint args ∧
      (s.gpr .rdi).toNat + (s.gpr .rsi).toNat ≤ 2 ^ 64 ∧ (s.gpr .rdx).toNat + (s.gpr .rcx).toNat * 8 ≤ 2 ^ 64 ∧
      (s.gpr .r8).toNat + (s.gpr .r9).toNat ≤ 2 ^ 64 ∧ (stackArg s 0).toNat + (stackArg s 1).toNat ≤ 2 ^ 64 ∧
      (stackArg s 2).toNat + (stackArg s 3).toNat * 8 ≤ 2 ^ 64 ∧
      Spec.Rsa.lenValid (s.gpr .rsi).toNat ∧ (s.gpr .rcx).toNat = Spec.Rsa.precomputedWords (s.gpr .rsi).toNat ∧
      (stackArg s 1).toNat = (s.gpr .rsi).toNat ∧ 1 ≤ (s.gpr .r9).toNat ∧
      (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat ∧ Spec.Rsa.scratchWords (s.gpr .rsi).toNat ≤ (stackArg s 3).toNat
  post s s' :=
    ∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
      Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt s.mem (s.gpr .rdx) (s.gpr .rcx).toNat) →
      Spec.Rsa.written s'.mem (s.gpr .rdi) (s.gpr .rsi).toNat ((s'.gpr .rax).setWidth 32)
        (Spec.Rsa.publicOp nB (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
          (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat))
  pub s₁ s₂ :=
    (∀ r ∈ [Reg.rdi, .rsi, .rdx, .rcx, .r8, .r9, .rsp], s₁.gpr r = s₂.gpr r) ∧
      stackArg s₁ 0 = stackArg s₂ 0 ∧ stackArg s₁ 1 = stackArg s₂ 1 ∧ stackArg s₁ 2 = stackArg s₂ 2 ∧
      stackArg s₁ 3 = stackArg s₂ 3 ∧
      Spec.Rsa.wordsAt s₁.mem (s₁.gpr .rdx) (s₁.gpr .rcx).toNat =
        Spec.Rsa.wordsAt s₂.mem (s₂.gpr .rdx) (s₂.gpr .rcx).toNat ∧
      Spec.Rsa.bytesAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9).toNat =
        Spec.Rsa.bytesAt s₂.mem (s₂.gpr .r8) (s₂.gpr .r9).toNat

/-! ## The entry -/

theorem pdEntry_eq : Precomputed.entry = ([.mov .r11 (.mem { base := .rsp, disp := 24 }),
    .store (hdr11 0) .rbx, .store (hdr11 1) .rbp, .store (hdr11 2) .r12, .store (hdr11 3) .r13,
    .store (hdr11 4) .r14, .store (hdr11 5) .r15,
    .store (hdr11 sOut) .rdi, .store (hdr11 sN) .rdx, .store (hdr11 sK) .rsi, .store (hdr11 sE) .r8,
    .store (hdr11 sElen) .r9] : List Instr) ++ [.mov .rax (.mem { base := .rsp, disp := 8 }), .store (hdr11 sIn) .rax,
    .mov .rdi (.reg .r11)] := rfl

/-- `entry`: the header, from the arguments (`out_len` for `k`), and the
working space's base (the third stack argument) in `rdi`. -/
theorem pdEntry_ok {s : State} {B : Addr} (hB : stackArg s 2 = B)
    (hw : ∀ i < 22, InRegions s.wr (off B (8 * i)) 8)
    (ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8) (ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8)
    (hsep : ∀ m', Outside B 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0) :
    WP isa (.block Precomputed.entry) s fun t => t.gpr .rdi = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rsi ∧ word t.mem B (8 * sE) = s.gpr .r8 ∧
      word t.mem B (8 * sElen) = s.gpr .r9 ∧ word t.mem B (8 * sIn) = stackArg s 0 ∧
      Outside B 0 (8 * 22) s.mem t.mem ∧ Keep [.r11, .rax, .rdi] s t := by
  have e0 : s.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := rfl
  have e2 : s.gpr .rsp + BitVec.ofInt 64 24 = stackArgAddr s 2 := rfl
  have hB' : s.mem.readW (stackArgAddr s 2) 64 = B := hB
  have hA0 : s.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := rfl
  rw [pdEntry_eq, WP.block_append_iff]
  refine WP.mono (WP.keep [.r11] (Q := fun t => t.gpr .r11 = B ∧
      word t.mem B (8 * 0) = s.gpr .rbx ∧ word t.mem B (8 * 1) = s.gpr .rbp ∧
      word t.mem B (8 * 2) = s.gpr .r12 ∧ word t.mem B (8 * 3) = s.gpr .r13 ∧
      word t.mem B (8 * 4) = s.gpr .r14 ∧ word t.mem B (8 * 5) = s.gpr .r15 ∧
      word t.mem B (8 * sOut) = s.gpr .rdi ∧ word t.mem B (8 * sN) = s.gpr .rdx ∧
      word t.mem B (8 * sK) = s.gpr .rsi ∧ word t.mem B (8 * sE) = s.gpr .r8 ∧
      word t.mem B (8 * sElen) = s.gpr .r9 ∧ Outside B 0 (8 * 22) s.mem t.mem) ?_ rfl)
    fun t₁ ⟨⟨h11, h0, h1, h2, h3, h4, h5, hO, hN, hK, hE, hL, ho₁⟩, k₁⟩ => ?_
  · xrun [State.ea, hdr11, e2, ha2, hB', hdrOff, hw 0 (by decide), hw 1 (by decide),
      hw 2 (by decide), hw 3 (by decide), hw 4 (by decide), hw 5 (by decide), hw sOut (by decide),
      hw sN (by decide), hw sK (by decide), hw sE (by decide), hw sElen (by decide)]
    exact entryMem_facts _ _ _ _ _ _ _ _ _ _ _ _ _
  have hr₁ : t₁.mem.readW (stackArgAddr s 0) 64 = stackArg s 0 := hsep _ ho₁
  have ha0₁ : InRegions (t₁.rd ++ t₁.wr) (stackArgAddr s 0) 8 := by rw [k₁.2.1, k₁.2.2]; exact ha0
  have hw₁ : InRegions t₁.wr (off B (8 * sIn)) 8 := by rw [k₁.2.2]; exact hw sIn (by decide)
  have e0₁ : t₁.gpr .rsp + BitVec.ofInt 64 8 = stackArgAddr s 0 := by rw [k₁.gpr (by decide)]; exact e0
  refine WP.mono (WP.keep [.rax, .rdi] (Q := fun t => t.gpr .rdi = B ∧
      t.mem = t₁.mem.writeW (off B (8 * sIn)) (stackArg s 0)) (by
    xrun [State.ea, hdr11, e0₁, ha0₁, hr₁, h11, hdrOff, hw₁]) rfl) fun t ⟨⟨hdi, hm⟩, k₂⟩ => ?_
  refine ⟨hdi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try rw [hm]
  · exact word_skip h0 (by decide) (by decide) (by decide)
  · exact word_skip h1 (by decide) (by decide) (by decide)
  · exact word_skip h2 (by decide) (by decide) (by decide)
  · exact word_skip h3 (by decide) (by decide) (by decide)
  · exact word_skip h4 (by decide) (by decide) (by decide)
  · exact word_skip h5 (by decide) (by decide) (by decide)
  · exact word_skip hO (by decide) (by decide) (by decide)
  · exact word_skip hN (by decide) (by decide) (by decide)
  · exact word_skip hK (by decide) (by decide) (by decide)
  · exact word_skip hE (by decide) (by decide) (by decide)
  · exact word_skip hL (by decide) (by decide) (by decide)
  · exact word_writeW_self _ _ _ _
  · exact Outside.store_hdr ho₁ (by decide) (by decide) _
  · exact (k₁.trans k₂).mono (by decide)

/-! ## The values in `pre` -/

/-- A number from its words. -/
theorem wv_of_words {m : Mem} {p : Addr} {d x : Nat} : ∀ {n : Nat},
    (∀ i < n, (word m p (d + 8 * i)).toNat = x / 2 ^ (64 * i) % 2 ^ 64) → wv m p d n = x % 2 ^ (64 * n)
  | 0, _ => by simp only [wv, Nat.mul_zero, Nat.pow_zero, Nat.mod_one]
  | n + 1, h => by
    rw [wv, wv_of_words fun i hi => h i (by omega), h n (by omega), pow64_succ, Nat.mod_mul]

/-- The `2 w` words at `pp`, as two numbers of `w` words. -/
theorem pre_words {m : Mem} {pp : Addr} {w N R : Nat}
    (h : Spec.Rsa.wordsAt m pp (2 * w) = Spec.Rsa.toWords N w ++ Spec.Rsa.toWords R w)
    (hN : N < 2 ^ (64 * w)) (hR : R < 2 ^ (64 * w)) :
    wv m pp 0 w = N ∧ wv m pp (8 * w) w = R := by
  rw [Spec.Rsa.wordsAt, Spec.Rsa.toWords, Spec.Rsa.toWords, show 2 * w = w + w by omega, List.range_add,
    List.map_append, List.map_map] at h
  obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
  rw [List.map_inj_left] at h1 h2
  refine ⟨?_, ?_⟩
  · rw [← Nat.mod_eq_of_lt hN]
    refine wv_of_words fun i hi => ?_
    show (m.readW (pp + BitVec.ofNat 64 (0 + 8 * i)) 64).toNat = _
    rw [Nat.zero_add, h1 i (List.mem_range.mpr hi), BitVec.toNat_ofNat]
  · rw [← Nat.mod_eq_of_lt hR]
    refine wv_of_words fun i hi => ?_
    have := h2 i (List.mem_range.mpr hi)
    simp only [Function.comp_apply] at this
    show (m.readW (pp + BitVec.ofNat 64 (8 * w + 8 * i)) 64).toNat = _
    rw [show 8 * w + 8 * i = 8 * (w + i) by omega, this, BitVec.toNat_ofNat]

/-- `pre` holds the values of the valid modulus `nB`. -/
theorem pre_of_some {m : Mem} {pp : Addr} {k : Nat} {nB : List Byte} (hl : nB.length = k) (hk : 64 ≤ k)
    (hpp : Spec.Rsa.publicPrecompute nB = some (Spec.Rsa.wordsAt m pp (2 * ((k + 7) / 8)))) :
    Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true ∧ wv m pp 0 ((k + 7) / 8) = Spec.Rsa.os2ip nB ∧
      wv m pp (8 * ((k + 7) / 8)) ((k + 7) / 8) = 2 ^ (128 * ((k + 7) / 8)) % Spec.Rsa.os2ip nB := by
  have hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k = true := by
    cases hv : Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) k
    · simp [Spec.Rsa.publicPrecompute, hl, hv] at hpp
    · rfl
  rw [publicPrecompute_some hl hv] at hpp
  have hlt : Spec.Rsa.os2ip nB < 2 ^ (64 * ((k + 7) / 8)) := by
    have := os2ip_lt nB
    rw [hl, pow256_eq] at this
    exact Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega))
  have hpos : 0 < Spec.Rsa.os2ip nB := by
    have := (valid_facts hv hk).2.1; omega
  obtain ⟨h1, h2⟩ := pre_words (Option.some.inj hpp).symm hlt (Nat.lt_trans (Nat.mod_lt _ hpos) hlt)
  exact ⟨hv, h1, h2⟩

/-- The checks pass for the values of a valid modulus. -/
theorem checks_true {m : Mem} {B : Addr} {w N : Nat} (hw : 1 ≤ w) (hN : wv m B (slot w aN) w = N)
    (hodd : N % 2 = 1) (hlo : 2 ^ (64 * (w - 1)) ≤ N) (hRN : wv m B (slot w aR2) w < N) :
    (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) = true := by
  have h1 : (word m B (slot w aN)).toNat % 2 = 1 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide), hN, hodd]
  have h3 : word m B (slot w aN + 8 * (w - 1)) ≠ 0 := by
    intro h0
    have h := word_of_wv m B (slot w aN) w (q := w - 1) (by omega)
    rw [h0, hN, show (0 : BitVec 64).toNat = 0 from rfl] at h
    have hlt := wv_lt m B (slot w aN) w
    rw [hN] at hlt
    have hp : 0 < 2 ^ (64 * (w - 1)) := Nat.two_pow_pos _
    have hq : N / 2 ^ (64 * (w - 1)) < 2 ^ 64 := by
      rw [Nat.div_lt_iff_lt_mul hp, ← Nat.pow_add, show 64 + 64 * (w - 1) = 64 * w by omega]; exact hlt
    have hq1 : 1 ≤ N / 2 ^ (64 * (w - 1)) := (Nat.le_div_iff_mul_le hp).mpr (by omega)
    rw [Nat.mod_eq_of_lt hq] at h
    omega
  rw [hN]
  simp only [h1, hRN, decide_true, Bool.and_true, Bool.true_and, decide_eq_true_eq]
  exact h3

/-- What values that pass the checks give: an odd `N > 1`, and `R < N`. -/
theorem checks_facts {m : Mem} {B : Addr} {w : Nat} (hw : 2 ≤ w)
    (h : (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) = true) :
    wv m B (slot w aN) w % 2 = 1 ∧ 1 < wv m B (slot w aN) w ∧ wv m B (slot w aR2) w < wv m B (slot w aN) w := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨by rw [← Nat.mod_mod_of_dvd _ (show 2 ∣ 2 ^ 64 by decide), wv_mod64 _ _ _ (by omega)]; exact h1, ?_, h2⟩
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  rw [Nat.add_sub_cancel] at h3
  have ht : (word m B (slot (v + 1) aN + 8 * v)).toNat ≠ 0 := fun h0 => h3 (BitVec.eq_of_toNat_eq (by rw [h0]; rfl))
  have hp : 1 < 2 ^ (64 * v) := Nat.one_lt_two_pow (by omega)
  rw [wv]
  have : 2 ^ (64 * v) ≤ 2 ^ (64 * v) * (word m B (slot (v + 1) aN + 8 * v)).toNat :=
    Nat.le_mul_of_pos_right _ (by omega)
  omega

/-! ## The whole function -/

/-- What `code` uses of its contract's precondition, for the working space
`B` (the third stack argument) of `Z` bytes, the modulus' length `k` and
`pre`'s `2 w` words. -/
structure PdCtx (s : State) : Prop where
  hk1 : 64 ≤ (s.gpr .rsi).toNat
  hk2 : (s.gpr .rsi).toNat ≤ 1024
  hL1 : 1 ≤ (s.gpr .r9).toNat
  hL2 : (s.gpr .r9).toNat ≤ (s.gpr .rsi).toNat
  hpl : (s.gpr .rcx).toNat = 2 * (((s.gpr .rsi).toNat + 7) / 8)
  hZ : 128 * (s.gpr .rsi).toNat ≤ (stackArg s 3).toNat * 8
  hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8)
  ha0 : InRegions (s.rd ++ s.wr) (stackArgAddr s 0) 8
  ha2 : InRegions (s.rd ++ s.wr) (stackArgAddr s 2) 8
  hsep : ∀ m', Outside (stackArg s 2) 0 (8 * 22) s.mem m' → m'.readW (stackArgAddr s 0) 64 = stackArg s 0
  hpr : ∀ i < 2 * (((s.gpr .rsi).toNat + 7) / 8), InRegions (s.rd ++ s.wr) (off (s.gpr .rdx) (8 * i)) 8
  hps : ∀ j < 16 * (((s.gpr .rsi).toNat + 7) / 8),
    (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdx + BitVec.ofNat 64 j)
  heb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .r8)
    (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
  hxb : Src s (stackArg s 2) ((stackArg s 3).toNat * 8) (stackArg s 0)
    (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
  hout : ∀ j < (s.gpr .rsi).toNat, InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1
  houts : ∀ j < (s.gpr .rsi).toNat, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rdi + BitVec.ofNat 64 j)
  hret : ∀ b < 8, (stackArg s 3).toNat * 8 ≤ ofs (stackArg s 2) (s.gpr .rsp + BitVec.ofNat 64 b) ∧
    ∀ j < (s.gpr .rsi).toNat, s.gpr .rsp + BitVec.ofNat 64 b ≠ s.gpr .rdi + BitVec.ofNat 64 j

theorem pdCtx_of {s : State} (h : pdContract.pre s) : PdCtx s := by
  simp only [pdContract] at h
  obtain ⟨hsp, hrd, hwr, dOp, dOe, dOi, dOs, dOa, dps, des, dis, dsa, dRo, dRp, dRe, dRi, dRs, dRa,
    wO, wP, wE, wI, wS, hk, hpl, hil, hL1, hL2, hsl⟩ := h
  obtain ⟨hk1, hk2⟩ := hk
  unfold Spec.Rsa.scratchWords at hsl
  unfold Spec.Rsa.precomputedWords Spec.Rsa.modulusWords at hpl
  have hs : Scr s (stackArg s 2) ((stackArg s 3).toNat * 8) := ⟨by rw [hwr]; simp, wS⟩
  have hn := hs.nowrap
  have hpre : (⟨s.gpr .rdx, (s.gpr .rcx).toNat * 8⟩ : Region) ∈ s.rd ++ s.wr := by rw [hrd]; simp
  refine ⟨hk1, hk2, hL1, hL2, hpl, by omega, hs,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp, by simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega⟩,
    ⟨⟨stackArgAddr s 0, 32⟩, by rw [hrd]; simp,
      by rw [stackArgAddr_two]; exact Offset.contains_base _ (by omega) (by omega)⟩,
    fun m' ho => Mem.readW_congr fun b hb => ho _ (Or.inr (by
      have := out_scr dsa.symm (contains_byte (stackArgAddr s 0) (i := b) (by omega) (by omega)); omega)),
    fun i hi => ⟨_, hpre, Offset.contains_base _ (by omega) (by omega)⟩,
    fun j hj => out_scr dps (contains_byte _ (by omega) (by omega)),
    src_of_region (by rw [hrd]; simp) (by omega) des,
    src_of_region (by rw [hrd, ← hil]; simp) (by omega) (by rw [← hil]; exact dis),
    fun j hj => ⟨_, by rw [hwr]; exact List.mem_cons_self .., contains_byte _ (by omega) (by omega)⟩,
    fun j hj => out_scr dOs (contains_byte _ (by omega) (by omega)), fun b hb => ?_⟩
  have hc := contains_byte (s.gpr .rsp) (i := b) (len := 8) (by omega) (by omega)
  exact ⟨out_scr dRs hc, fun j hj he => dRo _ hc (by rw [he]; exact contains_byte _ (by omega) (by omega))⟩

/-- The checks' result, from the numbers in the arrays. -/
def chkv (w N R : Nat) : Bool :=
  decide (N % 2 = 1) && decide (R < N) && decide (N / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0)

theorem chk_eq {m : Mem} {B : Addr} {w : Nat} (hw : 1 ≤ w) :
    (decide ((word m B (slot w aN)).toNat % 2 = 1) &&
      decide (wv m B (slot w aR2) w < wv m B (slot w aN) w) &&
      decide (word m B (slot w aN + 8 * (w - 1)) ≠ 0)) =
      chkv w (wv m B (slot w aN) w) (wv m B (slot w aR2) w) := by
  have h1 : (word m B (slot w aN)).toNat % 2 = wv m B (slot w aN) w % 2 := by
    rw [← wv_mod64 _ _ _ hw, Nat.mod_mod_of_dvd _ (by decide)]
  have h3 : word m B (slot w aN + 8 * (w - 1)) ≠ 0 ↔ wv m B (slot w aN) w / 2 ^ (64 * (w - 1)) % 2 ^ 64 ≠ 0 := by
    rw [← word_of_wv m B _ w (q := w - 1) (by omega)]
    exact ⟨fun h h0 => h (BitVec.eq_of_toNat_eq (by rw [h0]; rfl)), fun h h0 => h (by rw [h0]; rfl)⟩
  unfold chkv
  rw [h1, decide_eq_decide.mpr h3]

/-- `pre`'s words after the entry, as before it. -/
theorem pre_wv_entry {s t₁ : State} (c : PdCtx s)
    (i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem) {e : Nat}
    (he : e + 8 * (((s.gpr .rsi).toNat + 7) / 8) ≤ 16 * (((s.gpr .rsi).toNat + 7) / 8)) :
    wv t₁.mem (s.gpr .rdx) e (((s.gpr .rsi).toNat + 7) / 8) = wv s.mem (s.gpr .rdx) e (((s.gpr .rsi).toNat + 7) / 8) :=
  wv_congr fun i hi => Mem.readW_congr fun b hb => i₁ _ (by
    have := c.hps (e + 8 * i + b) (by omega); rwa [off, BitVec.add_assoc, BitVec.ofNat_add_ofNat])

/-- `rest`'s hypotheses, after the entry and the load, for values that pass
the checks. -/
theorem pdPre_of {s t₁ t₂ : State} (c : PdCtx s) (hdi : t₁.gpr .rdi = stackArg s 2)
    (hO : word t₁.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi) (hK : word t₁.mem (stackArg s 2) (8 * sK) = s.gpr .rsi)
    (hE : word t₁.mem (stackArg s 2) (8 * sE) = s.gpr .r8) (hL : word t₁.mem (stackArg s 2) (8 * sElen) = s.gpr .r9)
    (hIn : word t₁.mem (stackArg s 2) (8 * sIn) = stackArg s 0)
    (ho₁ : Outside (stackArg s 2) 0 (8 * 22) s.mem t₁.mem) (k₁ : Keep [.r11, .rax, .rdi] s t₁)
    (hW₂ : word t₂.mem (stackArg s 2) (8 * sW) = BitVec.ofNat 64 (((s.gpr .rsi).toNat + 7) / 8))
    (hb₂ : ∀ j < 8, word t₂.mem (stackArg s 2) (8 * sArr j) = off (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) j))
    (f₂ : Frm (stackArg s 2) (pdLoadRanges (((s.gpr .rsi).toNat + 7) / 8)) t₁.mem t₂.mem) (k₂ : Keep mmRegs t₁ t₂)
    (hodd : wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8) % 2 = 1)
    (hN1 : 1 < wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
    (hRN : wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
      wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) :
    PdPre t₂ (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) (s.gpr .r8)
      (stackArg s 0) (s.gpr .r9).toNat (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat)
      (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat)
      (wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8))
      (wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8)) := by
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    (InScr.of_outside ho₁ (by omega)).trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  exact
    { scr := c.hs.congr kk.2.2, rdi := (k₂.gpr (by decide)).trans hdi, z := hz, k1 := hk1, k2 := hk2,
      hO := by rw [x₂ sOut (by decide)]; exact hO, hK := by rw [x₂ sK (by decide), hK, ofNat_toNat64],
      hE := by rw [x₂ sE (by decide)]; exact hE, hL := by rw [x₂ sElen (by decide), hL, ofNat_toNat64],
      hIn := by rw [x₂ sIn (by decide)]; exact hIn, hW := hW₂, hb := hb₂, n := rfl, r := rfl, odd := hodd,
      n1 := hN1, rlt := hRN, x := c.hxb.congrK i₂ kk, e := c.heb.congrK i₂ kk, xl := bytesAt_length _ _ _,
      el := bytesAt_length _ _ _, L1 := c.hL1, L2 := c.hL2, out := fun j hj => by rw [kk.2.2]; exact c.hout j hj,
      outSep := c.houts }

theorem pdCode_correct (s : State) (h : pdContract.pre s) :
    ∃ t s', Exec isa Precomputed.code s t s' ∧ abiPreserved s s' ∧ pdContract.post s s' := by
  have c := pdCtx_of h
  have hZ' := c.hZ
  have hk1 := c.hk1
  have hk2 := c.hk2
  have hn := c.hs.nowrap
  suffices hwp : WP isa Precomputed.code s fun s' => gprPreserved s s' ∧ pdContract.post s s' by
    obtain ⟨t, s', he, hg, hp⟩ := hwp
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he hg, hp⟩
  unfold Precomputed.code
  have hw : ∀ i < 22, InRegions s.wr (off (stackArg s 2) (8 * i)) 8 := fun i hi => c.hs.st (by omega)
  refine WP.seq (WP.mono (pdEntry_ok rfl hw c.ha0 c.ha2 c.hsep) fun t₁ ⟨hdi, h0, h1, h2, h3, h4, h5, hO, hN, hK,
    hE, hL, hIn, ho₁, k₁⟩ => ?_)
  have i₁ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₁.mem := InScr.of_outside ho₁ (by omega)
  have hz : slot (((s.gpr .rsi).toNat + 7) / 8) 8 ≤ (stackArg s 3).toNat * 8 := by unfold slot hdrBytes; omega
  refine WP.seq (WP.mono (pdLoad_ok (c.hs.congr k₁.2.2) hdi hz (by omega) (by omega) (by rw [hK, ofNat_toNat64])
    hN (fun i hi => by rw [k₁.2.1, k₁.2.2]; exact c.hpr i hi) c.hps)
    fun t₂ ⟨hN₂, hR₂, hW₂, hb₂, hz₂, f₂, k₂⟩ => ?_)
  rw [pre_wv_entry c i₁ (by omega)] at hN₂
  rw [pre_wv_entry c i₁ (by omega)] at hR₂
  have x₂ := Fixed.of_frm f₂ (pdLoadRanges_fixed _)
  have i₂ : InScr (stackArg s 2) ((stackArg s 3).toNat * 8) s.mem t₂.mem :=
    i₁.trans (InScr.of_frm f₂ fun r hr => (pdLoadRanges_le _ r hr).trans hz)
  have kk := k₁.trans k₂
  have hs₂ := c.hs.congr kk.2.2
  have hdi₂ : t₂.gpr .rdi = stackArg s 2 := (k₂.gpr (by decide)).trans hdi
  have hO₂ : word t₂.mem (stackArg s 2) (8 * sOut) = s.gpr .rdi := by rw [x₂ sOut (by decide)]; exact hO
  have hK₂ : word t₂.mem (stackArg s 2) (8 * sK) = BitVec.ofNat 64 (s.gpr .rsi).toNat := by
    rw [x₂ sK (by decide), hK, ofNat_toNat64]
  have hout₂ : ∀ j < (s.gpr .rsi).toNat, InRegions t₂.wr (s.gpr .rdi + BitVec.ofNat 64 j) 1 := fun j hj => by
    rw [kk.2.2]; exact c.hout j hj
  -- What either branch leaves.
  have fin : ∀ t r (cb : Bool),
      MainPost t₂ t (stackArg s 2) ((stackArg s 3).toNat * 8) (s.gpr .rsi).toNat (s.gpr .rdi) r cb →
      (∀ nB : List Byte, nB.length = (s.gpr .rsi).toNat →
        Spec.Rsa.modulusValid (Spec.Rsa.os2ip nB) (s.gpr .rsi).toNat = true →
        wv s.mem (s.gpr .rdx) 0 (((s.gpr .rsi).toNat + 7) / 8) = Spec.Rsa.os2ip nB →
        wv s.mem (s.gpr .rdx) (8 * (((s.gpr .rsi).toNat + 7) / 8)) (((s.gpr .rsi).toNat + 7) / 8) =
          2 ^ (128 * (((s.gpr .rsi).toNat + 7) / 8)) % Spec.Rsa.os2ip nB →
        cb = decide (Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB) ∧
        r = if Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) < Spec.Rsa.os2ip nB then
          Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (stackArg s 0) (s.gpr .rsi).toNat) ^
            Spec.Rsa.os2ip (Spec.Rsa.bytesAt s.mem (s.gpr .r8) (s.gpr .r9).toNat) % Spec.Rsa.os2ip nB else 0) →
      gprPreserved s t ∧ pdContract.post s t := by
    intro t r cb hp H
    refine ⟨⟨fun reg hreg => ?_, Mem.readW_congr fun b hb => ?_⟩, fun nB hl hpp => ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hreg
      rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hp.saved 0 (by decide)).trans ((x₂ 0 (by decide)).trans h0)
      · exact (hp.saved 1 (by decide)).trans ((x₂ 1 (by decide)).trans h1)
      · exact (hp.keep.gpr (by decide)).trans (kk.gpr (by decide))
      · exact (hp.saved 2 (by decide)).trans ((x₂ 2 (by decide)).trans h2)
      · exact (hp.saved 3 (by decide)).trans ((x₂ 3 (by decide)).trans h3)
      · exact (hp.saved 4 (by decide)).trans ((x₂ 4 (by decide)).trans h4)
      · exact (hp.saved 5 (by decide)).trans ((x₂ 5 (by decide)).trans h5)
    · obtain ⟨hZx, hne⟩ := c.hret b hb
      rw [hp.frame _ hZx hne, i₂ _ hZx]
    · rw [c.hpl] at hpp
      obtain ⟨hv, hNv, hRv⟩ := pre_of_some hl hk1 hpp
      exact written_of hl hp.bytes hp.rax (fun _ => H nB hl hv hNv hRv) fun h => absurd h (by rw [hv]; decide)
  generalize hcb : (decide ((word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN)).toNat % 2 = 1) &&
      decide (wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aR2) (((s.gpr .rsi).toNat + 7) / 8) <
        wv t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN) (((s.gpr .rsi).toNat + 7) / 8)) &&
      decide (word t₂.mem (stackArg s 2) (slot (((s.gpr .rsi).toNat + 7) / 8) aN + 8 * ((((s.gpr .rsi).toNat + 7) / 8) - 1)) ≠ 0))
    = cb at hz₂
  refine WP.ite (!cb) (by simp [eval, hz₂]) (fun hb => ?_) (fun hb => ?_)
  · -- Values of no modulus.
    have hcf : cb = false := by simpa using hb
    refine WP.mono (fail_ok hs₂ hdi₂ (by omega) (by omega) (by omega) hO₂ hK₂ hout₂ c.houts)
      fun t hp => fin t 0 false hp fun nB hl hv hNv hRv => ?_
    obtain ⟨hodd, -, hlo⟩ := valid_facts hv hk1
    have := checks_true (by omega) (hN₂.trans hNv) hodd hlo
      (by rw [hR₂, hRv]; exact Nat.mod_lt _ (by omega))
    rw [hcb, hcf] at this
    exact absurd this (by decide)
  · have hct : cb = true := by simpa using hb
    rw [hct] at hcb
    obtain ⟨hodd, hN1, hRN⟩ := checks_facts (by omega) hcb
    have hpre := pdPre_of c hdi hO hK hE hL hIn ho₁ k₁ hW₂ hb₂ f₂ k₂ hodd hN1 hRN
    refine WP.mono (pdRest_ok hpre) fun t ⟨x, hx, hp⟩ => fin t _ _ hp fun nB hl hv hNv hRv => ?_
    rw [hN₂.trans hNv] at hx hp ⊢
    have hxX := hx (by
      rw [hR₂, hRv, Nat.mod_mod, ← Nat.pow_add, show 128 * (((s.gpr .rsi).toNat + 7) / 8) =
        64 * (((s.gpr .rsi).toNat + 7) / 8) + 64 * (((s.gpr .rsi).toNat + 7) / 8) by omega])
    refine ⟨rfl, ?_⟩
    rw [Nat.pow_mod, hxX, ← Nat.pow_mod]

end VG.Proof.Bignum.X86_64
