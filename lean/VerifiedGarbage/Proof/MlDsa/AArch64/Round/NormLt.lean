import VerifiedGarbage.Proof.MlDsa.AArch64.Round.Arith

/-!
# ML-DSA on AArch64: `vg_mldsa_norm_lt`

The top bit of `x10` says whether every coefficient `a` so far has `a < B` or
`q - a < B` (`J`): each is the sign bit of a difference of numbers less than
`2³²` (`sgn_sub`).
-/

namespace VG.Proof.MlDsa.AArch64.Round

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Round VG.Proof.MlDsa.Round
open VG.Proof.MlDsa.AArch64.Arith (Qv toNat_setWidth64 q32 movW_ok)
open VG.Impl.MlDsa.AArch64.Arith (movW)
open VG.Proof.MlKem.AArch64 (Keep)
open VG.Spec.MlDsa

/-- A bit, as a 64-bit value. -/
abbrev bitV (b : Bool) : BitVec 64 := BitVec.ofNat 64 b.toNat

/-- The sign bit of the difference of two numbers less than `2⁶³`. -/
theorem sgn_sub {x y : BitVec 64} (hx : x.toNat < 2 ^ 63) (hy : y.toNat < 2 ^ 63) :
    (x - y) >>> 63 = bitV (decide (x.toNat < y.toNat)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize x.toNat = a at *
  generalize y.toNat = b at *
  by_cases h : a < b
  · rw [decide_eq_true h]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = 2 ^ 64 - b + a := Nat.mod_eq_of_lt (by omega)
    rw [e]; simp only [Bool.toNat_true]; omega
  · rw [decide_eq_false h]
    have e : (2 ^ 64 - b + a) % 2 ^ 64 = a - b := by omega
    rw [e]; simp only [Bool.toNat_false]; omega

theorem bitV_and (b c : Bool) : bitV b &&& bitV c = bitV (b && c) := by cases b <;> cases c <;> decide

theorem bitV_or (b c : Bool) : bitV b ||| bitV c = bitV (b || c) := by cases b <;> cases c <;> decide

theorem bitV_shr (b : Bool) : bitV b >>> 63 = 0 := by cases b <;> decide

theorem nlBody_ok (s : State) (hq : s.gpr .x9 = Qv) (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 4) :
    WP isa (.block (nlBody ++ [Reg.x0].map (fun p => .addImm .x p p 4) ++ ([.subImm .x .x11 .x11 1] : List Instr))) s
      fun s' =>
      (s'.mem = s.mem ∧ s'.gpr .x10 = s.gpr .x10 &&& ((s.mem.readW (s.gpr .x0) 32).setWidth 64 - s.gpr .x1 |||
          Qv - (s.mem.readW (s.gpr .x0) 32).setWidth 64 - s.gpr .x1) ∧
        s'.gpr .x0 = s.gpr .x0 + BitVec.ofNat 64 4 ∧ s'.gpr .x11 = s.gpr .x11 - BitVec.ofNat 64 1) ∧
      Keep [.x0, .x10, .x11, .x12, .x13, .x14] s s' := by
  refine VG.Proof.MlDsa.AArch64.Arith.WP.keep _ ?_ (by rfl)
  unfold nlBody
  arun [h0, hq, List.map_cons, List.map_nil]

/-- Whether coefficient `k` of `f` is within the bound. -/
def okN (m : Mem) (f : Addr) (B k : Nat) : Bool := decide ((coeffAt m f k).toNat < B ∨ q - (coeffAt m f k).toNat < B)

/-- Whether coefficients `0` to `i - 1` are. -/
def allOk (m : Mem) (f : Addr) (B i : Nat) : Bool := decide (∀ k < i, okN m f B k = true)

theorem allOk_zero (m : Mem) (f : Addr) (B : Nat) : allOk m f B 0 = true :=
  decide_eq_true fun _ hk => absurd hk (Nat.not_lt_zero _)

theorem allOk_succ (m : Mem) (f : Addr) (B i : Nat) :
    allOk m f B (i + 1) = (allOk m f B i && okN m f B i) := by
  unfold allOk
  by_cases h : okN m f B i = true
  · rw [h, Bool.and_true]
    exact decide_eq_decide.mpr ⟨fun h' k hk => h' k (by omega), fun h' k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      exacts [h' k hk, h]⟩
  · rw [Bool.not_eq_true] at h
    rw [h, Bool.and_false]
    exact decide_eq_false fun h' => by rw [h' i (Nat.lt_succ_self _)] at h; cases h

theorem ok_bit {a B : BitVec 64} (ha : a.toNat < q) (hB : B.toNat < 2 ^ 32) :
    (a - B ||| Qv - a - B) >>> 63 = bitV (decide (a.toNat < B.toNat ∨ q - a.toNat < B.toNat)) := by
  have hq : q = 8380417 := rfl
  have hQ : Qv.toNat = 8380417 := rfl
  have e : (Qv - a).toNat = q - a.toNat := by
    rw [VG.Proof.MlKem.AArch64.toNat_sub_n (by rw [hQ]; omega), hQ]
  rw [BitVec.ushiftRight_or_distrib, sgn_sub (by omega) (by omega),
    sgn_sub (by rw [e]; omega) (by omega), e, bitV_or]
  rw [Bool.decide_or]

theorem normLt_correct (s₀ : State) (hp : normLtK.pre s₀) :
    ∃ t s', Exec isa normLt s₀ t s' ∧ abiPreserved s₀ s' ∧ normLtK.post s₀ s' := by
  have hr : Reduced s₀.mem (s₀.gpr .x0) := hp.2.2
  let B := arg32 s₀ .x1
  let J : Nat → State → Prop := fun i s => s.gpr .x10 >>> 63 = bitV (allOk s₀.mem (s₀.gpr .x0) B i)
  have hpro : WP isa (.block ([.addImm .w .x1 .x1 0] ++ movW .x9 (BitVec.ofNat 32 Impl.MlDsa.AArch64.Arith.qNat) ++
      ([.movz .x .x10 0 0, .subImm .x .x10 .x10 1] : List Instr))) s₀ fun s =>
      s.gpr .x1 = ((s₀.gpr .x1).setWidth 32).setWidth 64 ∧ s.gpr .x9 = Qv ∧ s.gpr .x10 = BitVec.allOnes 64 ∧
        s.mem = s₀.mem ∧ Keep [.x1, .x9, .x10] s₀ s := by
    rw [WP.block_append_iff, WP.block_append_iff]
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x1] (Q := fun s => s.gpr .x1 =
      ((s₀.gpr .x1).setWidth 32).setWidth 64 ∧ s.mem = s₀.mem) (by arun) (by rfl)) fun s₁ ⟨⟨h1, hm₁⟩, k₁⟩ => ?_
    refine WP.mono (movW_ok .x9 _ s₁) fun s₂ ⟨⟨h9, hm₂⟩, k₂⟩ => ?_
    refine WP.mono (VG.Proof.MlDsa.AArch64.Arith.WP.keep [.x10] (Q := fun s => s.gpr .x10 = BitVec.allOnes 64 ∧
      s.mem = s₂.mem) (by arun) (by rfl)) fun s₃ ⟨⟨h10, hm₃⟩, k₃⟩ => ?_
    refine ⟨by rw [k₃.get .x1, k₂.get .x1, h1], by rw [k₃.get .x9, h9]; exact q32, h10,
      by rw [hm₃, hm₂, hm₁], ((k₁.trans k₂).trans k₃).mono⟩
  have hB : (((s₀.gpr .x1).setWidth 32).setWidth 64 : BitVec 64).toNat = B := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by have := ((s₀.gpr .x1).setWidth 32).isLt; omega)]
  have hB32 : B < 2 ^ 32 := ((s₀.gpr .x1).setWidth 32).isLt
  have hW : WP isa normLt s₀ fun s' =>
      (s'.gpr .x0).setWidth 32 = if normRq [polyAt s₀.mem (s₀.gpr .x0)] < B then 1 else 0 := by
    refine WP.seq (WP.mono hpro fun sL ⟨h1, h9, h10, hmL, kL⟩ => ?_)
    have hL : Layout sL [.x0] [] :=
      { rd := fun p hp' => by
          simp only [List.mem_singleton] at hp'; subst hp'; rw [kL.get .x0, kL.rd, kL.wr, hp.1]; simp
        wr := fun _ h => by cases h
        dis := fun _ _ _ h => by cases h
        pw := List.Pairwise.nil }
    refine WP.seq (WP.mono (loop_ok (fixed := [.x1, .x9]) (clob := [.x0, .x10, .x11, .x12, .x13, .x14])
      (V := fun _ _ => 0) (J := J) hL (by decide) (by decide) (by decide) (by decide)
      (fun s hm hk => ?_) fun i hi s hI => ?_) fun s2 hI => ?_)
    · show s.gpr .x10 >>> 63 = _
      rw [hk.get .x10, h10, allOk_zero]
      decide
    · have hx9 : s.gpr .x9 = Qv := by rw [hI.fixed .x9 (by simp), h9]
      refine WP.mono (nlBody_ok s hx9 (hI.inR hL (by simp) (by simp) hi)) fun s' ⟨⟨hm', h10', h0, hc⟩, hk'⟩ =>
        ⟨⟨by rw [hm']; rfl, fun p hp' => by simp only [List.mem_singleton] at hp'; subst hp'; exact h0, hc, ?_⟩,
          hk'⟩
      show s'.gpr .x10 >>> 63 = _
      have ha : ((s.mem.readW (s.gpr .x0) 32).setWidth 64).toNat = (coeffAt s₀.mem (s₀.gpr .x0) i).toNat := by
        rw [toNat_setWidth64, hI.read hL (by simp) (by simp) hi, hmL, kL.get .x0]
      have hx1 : (s.gpr .x1).toNat = B := by rw [hI.fixed .x1 (by simp), h1, hB]
      rw [h10', BitVec.ushiftRight_and_distrib, hI.j, ok_bit (by rw [ha]; exact hr i hi) (by rw [hx1]; exact hB32),
        ha, hx1, bitV_and, allOk_succ]
      rfl
    · refine (VG.Proof.MlDsa.AArch64.Arith.WP.keep (Q := fun s3 => s3.gpr .x0 = s2.gpr .x10 >>> 63) [.x0]
        (by arun) (by rfl)).mono fun s3 ⟨h0, _⟩ => ?_
      rw [h0, hI.j]
      have e : allOk s₀.mem (s₀.gpr .x0) B 256 = decide (normRq [polyAt s₀.mem (s₀.gpr .x0)] < B) := by
        unfold allOk
        refine decide_eq_decide.mpr ?_
        rw [normRq_lt]
        refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩
        · have := h k hk
          simp only [okN, decide_eq_true_eq] at this
          rw [normZq_lt, polyAt_val hr hk]; exact this
        · have := h k hk
          rw [normZq_lt, polyAt_val hr hk] at this
          simp only [okN, decide_eq_true_eq]; exact this
      rw [e]
      split <;> rename_i h <;> simp [h]
  obtain ⟨t, s', he, hpost⟩ := hW
  exact ⟨t, s', he, VG.Proof.MlKem.AArch64.abi_of rfl (by decide +kernel) he, hpost⟩

theorem normLt_ct : ConstantTime isa normLtK.pre normLtK.pub normLt :=
  VG.Taint.constantTime (A := taint) (VG.AArch64.Taint.ofRegs [.x0])
    (fun _ _ _ _ hp => VG.Proof.MlDsa.AArch64.Arith.agree_regs hp.2.2 fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr; exact hp.1)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def normLtSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 1024⟩]
  wr := []

theorem normLt_verified : Verified AArch64.target normLt (normLtContract AArch64.abi) :=
  Verified.of_correct normLt_correct normLt_ct (by
    mldsa_implies [normLtContract, normLtSig, normLtK, AArch64.abi, AArch64.argRegs] [normLtSat]
      using normLtSat)

end VG.Proof.MlDsa.AArch64.Round
