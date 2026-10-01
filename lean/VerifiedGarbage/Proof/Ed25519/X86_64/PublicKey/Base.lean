import VerifiedGarbage.Proof.Ed25519.X86_64.PublicKey.Hash
import VerifiedGarbage.Proof.Ed25519.Bytes
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedVerified
import VerifiedGarbage.Proof.Ed25519.X86_64.ScalarBasePrecomputedLit

/-!
# Ed25519 public-key derivation on x86-64: pruning and the base point

Untrusted: everything here is checked by Lean. The first half of the digest,
pruned, is stored in the frame (`prune_ok`), `[s]B` is encoded into `out`
(`base_ok`), and the frame's copy of `s` is cleared (`wipe_ok`).
-/

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-! ## Arithmetic -/

theorem and_sub8 (x k : Nat) (hk : 3 ≤ k) : x &&& (2 ^ k - 8) = 8 * (x / 8 % 2 ^ (k - 3)) := by
  have e : 2 ^ k - 8 = 2 ^ 3 * (2 ^ (k - 3) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, Nat.add_sub_cancel' hk]; rfl
  rw [e, show (8 : Nat) = 2 ^ 3 from rfl]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h : 3 ≤ i
  · simp only [h, decide_true, Bool.true_and, Nat.sub_add_cancel h]
    cases x.testBit i <;> simp
  · simp [h]

theorem or_two_pow {y k : Nat} (h : y < 2 ^ k) : y ||| 2 ^ k = 2 ^ k + y := by
  have := Nat.two_pow_add_eq_or_of_lt h 1
  rw [Nat.mul_one] at this
  rw [this, Nat.or_comm]

/-- The pruning of `Spec.Ed25519.prune`, on four 64-bit words. -/
theorem prune_words (d₀ d₁ d₂ d₃ : BitVec 64) :
    ((d₀.toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat + 2 ^ 192 * d₃.toNat) &&& (2 ^ 254 - 8)) |||
        2 ^ 254 =
      (d₀ &&& BitVec.ofNat 64 (2 ^ 64 - 8)).toNat + 2 ^ 64 * d₁.toNat + 2 ^ 128 * d₂.toNat +
        2 ^ 192 * ((d₃ &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)).toNat := by
  have h₀ := d₀.isLt; have h₁ := d₁.isLt; have h₂ := d₂.isLt; have h₃ := d₃.isLt
  have c₁ : (2 ^ 64 - 8) % 2 ^ 64 = 2 ^ 64 - 8 := by decide
  have c₂ : (2 ^ 62 - 1) % 2 ^ 64 = 2 ^ 62 - 1 := by decide
  have c₃ : (2 ^ 62) % 2 ^ 64 = 2 ^ 62 := by decide
  rw [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, c₁, c₂, c₃, and_sub8 _ 64 (by omega), and_sub8 _ 254 (by omega),
    Nat.and_two_pow_sub_one_eq_mod, or_two_pow (Nat.mod_lt _ (by omega)), or_two_pow (by omega)]
  simp only [show (2 : Nat) ^ (254 - 3) = 2 ^ 251 from rfl, show (2 : Nat) ^ (64 - 3) = 2 ^ 61 from rfl]
  omega

/-- Code that writes only caller-saved registers and the frame's scalar. -/
theorem Ctx.store {t t' : State} (hc : Ctx L g mx m₀ t) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hmx : t'.mxcsr = t.mxcsr) (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r)
    (hf : Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem) : Ctx L g mx m₀ t' := by
  have keep : ∀ d, 48 ≤ d → d + 8 ≤ 72 →
      t'.mem.readW (L.B + BitVec.ofNat 64 d) 64 = t.mem.readW (L.B + BitVec.ofNat 64 d) 64 :=
    fun d h₁ h₂ => hf.readW (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)) (by decide)
  exact ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .rsp (by decide)).trans hc.rsp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), by rw [hmx]; exact hc.mx,
    (keep 48 (by omega) (by omega)).trans hc.pScr, (keep 56 (by omega) (by omega)).trans hc.pSeed,
    (keep 64 (by omega) (by omega)).trans hc.pOut,
    hc.frame.trans (Frame.sub hf fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩)⟩

/-- Word `k` of the digest. -/
abbrev dw (t : State) (L : Lay) (k : Nat) : BitVec 64 :=
  t.mem.readW (L.scr + BitVec.ofNat 64 (1568 + 8 * k)) 64

/-- The arguments of `scalar_base_precomputed`. -/
def BaseArgs (L : Lay) (t : State) : Prop :=
  t.gpr .rdi = L.out ∧ t.gpr .rsi = L.B + BitVec.ofNat 64 16 ∧ t.gpr .rdx = L.scr

theorem baseArgs_ok {t : State} (hc : Ctx L g mx m₀ t) :
    WP isa (.block pkBaseArgs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' := by
  have l48 := hc.inFr (d := 48) (by omega) (by omega)
  have l64 := hc.inFr (d := 64) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkBaseArgs, fOut, fScratch, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc,
    State.load64, ea_stk, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.mem_setReg,
    Option.map_some, reduceCtorEq, ite_false, ite_true, hc.rsp, add_add, Nat.reduceAdd, l48, l64,
    Option.some.injEq, exists_eq_left', hc.pScr, hc.pOut, BaseArgs]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, trivial, trivial, trivial⟩

theorem pruneRegs_ok {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    WP isa (.block pkPruneRegs) t fun t' => Ctx L g mx m₀ t' ∧ t'.mem = t.mem ∧ BaseArgs L t' ∧
      t'.gpr .r8 = (dw t L 0 &&& BitVec.ofNat 64 (2 ^ 64 - 8)) ∧ t'.gpr .r9 = dw t L 1 ∧
      t'.gpr .r10 = dw t L 2 ∧
      t'.gpr .r11 = ((dw t L 3 &&& BitVec.ofNat 64 (2 ^ 62 - 1)) ||| BitVec.ofNat 64 (2 ^ 62)) := by
  obtain ⟨hdi, hsi, hdx⟩ := ha
  have s0 := hc.inScr (o := 1568) (by omega)
  have s1 := hc.inScr (o := 1576) (by omega)
  have s2 := hc.inScr (o := 1584) (by omega)
  have s3 := hc.inScr (o := 1592) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneRegs, digestWord, digestAt, Nat.reduceMul, runBlock_cons, runStep_some, runBlock_nil,
    exec, execAlu, readSrc, State.load64, ea_base, RegUpd.gpr_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    RegUpd.mem_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, 
    Option.map_some, Option.bind_some, reduceCtorEq, ite_false, ite_true, hdx,
    Nat.reduceAdd, s0, s1, s2, s3, Option.some.injEq, exists_eq_left', BaseArgs, hdi, hsi]
  exact ⟨hc.regs rfl rfl rfl rfl (by cs_tac), trivial, ⟨trivial, trivial, trivial⟩,
    congrArg (_ &&& ·) (by decide : BitVec.signExtend 64 (BitVec.ofInt 32 (-8)) = BitVec.ofNat 64 (2 ^ 64 - 8)),
    trivial, trivial, trivial⟩

/-- Four words stored in the frame's scalar. -/
theorem four_ok (B : Addr) (m : Mem) (a b c d : BitVec 64) :
    let m' := (((m.writeW (B + BitVec.ofNat 64 16) a).writeW (B + BitVec.ofNat 64 24) b).writeW
      (B + BitVec.ofNat 64 32) c).writeW (B + BitVec.ofNat 64 40) d
    Frame [⟨B + BitVec.ofNat 64 16, 32⟩] m m' ∧ m'.readW (B + BitVec.ofNat 64 16) 64 = a ∧
      m'.readW (B + BitVec.ofNat 64 24) 64 = b ∧ m'.readW (B + BitVec.ofNat 64 32) 64 = c ∧
      m'.readW (B + BitVec.ofNat 64 40) 64 = d := by
  have sep : ∀ x y, x + 8 ≤ y ∨ y + 8 ≤ x → x + 8 ≤ 72 → y + 8 ≤ 72 →
      Mem.Sep (B + BitVec.ofNat 64 x) (64 / 8) (B + BitVec.ofNat 64 y) (64 / 8) :=
    fun x y h h₁ h₂ => Offset.sep B h (by omega) (by omega)
  have ct : ∀ x, 16 ≤ x → x + 8 ≤ 48 →
      (⟨B + BitVec.ofNat 64 16, 32⟩ : Region).Contains (B + BitVec.ofNat 64 x) (64 / 8) :=
    fun x h₁ h₂ => Offset.contains B h₁ (by omega) (by omega)
  refine ⟨(((((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (ct 16 (by omega) (by omega))).writeW
    (List.mem_singleton_self _) _ (ct 24 (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (ct 32 (by omega) (by omega))).writeW (List.mem_singleton_self _) _ (ct 40 (by omega) (by omega))),
    ?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
  · rw [Mem.readW_writeW_sep (sep 16 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 16 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 16 24 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 24 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_sep (sep 24 32 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (sep 32 40 (by omega) (by omega) (by omega)) (by decide),
      Mem.readW_writeW_self64]

theorem stores_ok {u : State} (hc : Ctx L g mx m₀ u) :
    WP isa (.block pkPruneStores) u fun u' => Ctx L g mx m₀ u' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] u.mem u'.mem ∧ u'.gpr = u.gpr ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 16) 64 = u.gpr .r8 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 24) 64 = u.gpr .r9 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 32) 64 = u.gpr .r10 ∧
      u'.mem.readW (L.B + BitVec.ofNat 64 40) 64 = u.gpr .r11 := by
  have w0 := hc.inFrW (d := 16) (by omega) (by omega)
  have w1 := hc.inFrW (d := 24) (by omega) (by omega)
  have w2 := hc.inFrW (d := 32) (by omega) (by omega)
  have w3 := hc.inFrW (d := 40) (by omega) (by omega)
  apply WP.of_runBlock
  simp only [pkPruneStores, runBlock_cons, runStep_some, runBlock_nil, exec, State.store64,
    ea_stk, hc.rsp, add_add, Nat.reduceAdd, w0, w1, w2, w3, ite_true, Option.some.injEq,
    exists_eq_left']
  obtain ⟨hf, h0, h1, h2, h3⟩ := four_ok L.B u.mem (u.gpr .r8) (u.gpr .r9) (u.gpr .r10) (u.gpr .r11)
  exact ⟨hc.store rfl rfl rfl (fun _ _ => rfl) hf, hf, trivial, h0, h1, h2, h3⟩

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

/-- The number of four words in memory. -/
theorem decode_words (m : Mem) (p : Addr) :
    Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt m p 32) = (m.readW p 64).toNat +
      2 ^ 64 * (m.readW (p + BitVec.ofNat 64 8) 64).toNat +
      2 ^ 128 * (m.readW (p + BitVec.ofNat 64 16) 64).toNat +
      2 ^ 192 * (m.readW (p + BitVec.ofNat 64 24) 64).toNat := by
  rw [Proof.Ed25519.decodeLE_eq]
  exact Proof.X25519.leNum_bytesAt_words64 m p

theorem take_bytesAt (m : Mem) (p : Addr) :
    (Spec.Sha512.bytesAt m p 64).take 32 = Spec.Ed25519.bytesAt m p 32 := by
  simp [Spec.Sha512.bytesAt, Spec.Ed25519.bytesAt, ← List.map_take, List.take_range]

theorem prune_ok {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {h : List Byte}
    (hh : Spec.Sha512.bytesAt t.mem (L.scr + BitVec.ofNat 64 1568) 64 = h) :
    WP isa (.block pkPrune) t fun t' => Ctx L g mx m₀ t' ∧
      Frame [⟨L.B + BitVec.ofNat 64 16, 32⟩] t.mem t'.mem ∧ BaseArgs L t' ∧
      Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t'.mem (L.B + BitVec.ofNat 64 16) 32) =
        Spec.Ed25519.prune h := by
  rw [pkPrune, WP.block_append_iff]
  refine WP.mono (pruneRegs_ok hc ha) fun u ⟨hcu, hmu, hau, h8, h9, h10, h11⟩ => ?_
  refine WP.mono (stores_ok hcu) fun u' ⟨hcu', hf, hg, r0, r1, r2, r3⟩ => ?_
  refine ⟨hcu', hmu ▸ hf, by simp only [BaseArgs, hg]; exact hau, ?_⟩
  rw [Spec.Ed25519.prune, ← hh, take_bytesAt]
  simp only [decode_words, add_add, Nat.reduceAdd, r0, r1, r2, r3, h8, h9, h10, h11]
  exact (prune_words _ _ _ _).symm

end VG.Proof.Ed25519.X86_64.PublicKey

namespace VG.Proof.Ed25519.X86_64.PublicKey

open VG VG.X86_64 VG.Impl.Ed25519.X86_64

variable {L : Lay} {g : Reg → BitVec 64} {mx : BitVec 32} {m₀ : Mem}

theorem base_nosp : NoSp scalarBase_precomputed :=
  Proof.Pbkdf2.Md.X86_64.nosp_of (by lit_decide)

theorem base_depth : scalarBase_precomputed.depth ≤ 1 := by lit_decide

abbrev baseRd (L : Lay) : List Region := [⟨L.B + BitVec.ofNat 64 16, 32⟩]
abbrev baseWr (L : Lay) : List Region := [L.OUT, L.SCR]

theorem base_regs {t : State} (ha : BaseArgs L t) (rd wr : List Region) :
    (t.callEntry.withRegions rd wr).gpr .rdi = L.out ∧
      (t.callEntry.withRegions rd wr).gpr .rsi = L.B + BitVec.ofNat 64 16 ∧
      (t.callEntry.withRegions rd wr).gpr .rdx = L.scr :=
  ⟨(gpr_ce _ _ _ (by decide)).trans ha.1, (gpr_ce _ _ _ (by decide)).trans ha.2.1,
    (gpr_ce _ _ _ (by decide)).trans ha.2.2⟩

theorem base_pre (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) :
    Proof.Ed25519.X86_64.scalarBaseLocal.pre (t.callEntry.withRegions (baseRd L) (baseWr L)) := by
  obtain ⟨g1, g2, g3⟩ := base_regs ha (baseRd L) (baseWr L)
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, g3, rsp_ce, hc.rsp, sub8,
    State.withRegions_rd, State.withRegions_wr]
  exact ⟨trivial, trivial, hL.stk_SCR (by omega), hL.stk_OUT (by omega), hL.stk_SCR (by omega), hL.nc⟩

theorem base_sub : ∀ r ∈ baseRd L ++ baseWr L, ∃ R ∈ [L.SEED, L.FR, L.OUT, L.SCR], Within r R := by
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl | rfl)
  · exact ⟨L.FR, by simp, within_stk _ (by omega) (by omega)⟩
  · exact ⟨L.OUT, by simp, within_base _ (by omega)⟩
  · exact ⟨L.SCR, by simp, within_base _ (by omega)⟩

theorem base_wsub : ∀ r ∈ baseWr L, Within r L.OUT ∨ Within r L.SCR := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact .inl (within_base _ (by omega))
  · exact .inr (within_base _ (by omega))

theorem base_ok (hL : L.Ok) {t : State} (hc : Ctx L g mx m₀ t) (ha : BaseArgs L t) {s : Nat}
    (hs : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32) = s) :
    WP isa (.call scalarBaseName scalarBase_precomputed) t fun t' => Ctx L g mx m₀ t' ∧
      Spec.Ed25519.bytesAt t'.mem L.out 32 =
        Spec.Ed25519.encodePoint (Spec.Ed25519.pointMul s Spec.Ed25519.basePoint) := by
  refine call_ok hL Proof.Ed25519.X86_64.scalarBase_precomputed_ok base_nosp base_depth hc
    (base_pre hL hc ha) base_sub base_wsub fun s' hc' _ _ ⟨s₂, hm, _, hpost⟩ => ⟨hc', ?_⟩
  obtain ⟨g1, g2, -⟩ := base_regs ha (baseRd L) (baseWr L)
  have h := hpost
  simp only [Proof.Ed25519.X86_64.scalarBaseLocal, g1, g2, State.withRegions_mem, hm] at h
  have e : Spec.Ed25519.bytesAt t.callEntry.mem (L.B + BitVec.ofNat 64 16) 32 =
      Spec.Ed25519.bytesAt t.mem (L.B + BitVec.ofNat 64 16) 32 := by
    simp only [Spec.Ed25519.bytesAt]
    refine List.map_congr_left fun i hi => ?_
    exact ce_byte t (R := ⟨L.B + BitVec.ofNat 64 16, 32⟩) (by
      rw [hc.ret]; exact Offset.disjoint _ (by omega) (by omega) (by omega))
      (by show (32 : Nat) ≤ 2 ^ 64; decide) (List.mem_range.mp hi)
  rw [h, e, Spec.Ed25519.scalarBase, hs]

end VG.Proof.Ed25519.X86_64.PublicKey
