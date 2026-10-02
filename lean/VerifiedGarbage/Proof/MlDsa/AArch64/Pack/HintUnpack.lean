import VerifiedGarbage.Proof.MlDsa.AArch64.Pack.HintUnpackPoly

/-!
# ML-DSA on AArch64: `vg_mldsa_hint_bit_unpack`

The polynomials (`HintUnpackPoly.lean`), then the bytes from the index up to
`ω`, which must be zero, and the return value: 1 if no check failed (the index
is at most `ω`), 0 otherwise.

Constant time but for its input: once `h` is zeroed, the two runs agree on
all the memory the function may access (the input `y`, which the contract
lets it leak, and `h`), and `memTaint` proves the rest.
-/

namespace VG.Proof.MlDsa.AArch64.Pack

open VG VG.AArch64 VG.Impl.MlDsa.AArch64.Pack
open VG.Spec.MlDsa
open VG.Spec.Sha3 (bytesAt)
open VG.Proof.MlKem.AArch64 (Only Keep wp_add wp_sub wp_lsr wp_addImm wp_movz wp_eor wp_nil eval_nonzero
  ne_zero_iff toNat_ofNat_lt ptr_add ptr_zero count_loop abi_of agree_of)
open VG.Proof.MlKem (bytesAt_getD bytesAt_length)
open VG.Proof.MlDsa.Pack

theorem nz_byte (b : Byte) : (BitVec.ofNat 64 b.toNat != 0) = decide (b ≠ 0) := by
  rw [ne_zero_iff, toNat_ofNat_lt (by have := b.isLt; omega)]
  exact decide_eq_decide.mpr ⟨fun h e => h (by rw [e]; rfl), fun h e => h (BitVec.eq_of_toNat_eq e)⟩

section
variable {s₀ : State} (hp : hintBitUnpackK.pre s₀)

/-! ## The bytes after the last index -/

include hp in
/-- The bytes from the index `idx` up to `ω`. -/
theorem trail_ok {idx : Nat} (hidx : idx ≤ uω s₀) {s : State} (hc : UCom s₀ s)
    (h5 : s.gpr .x5 = BitVec.ofNat 64 idx) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧
      (match optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () with
        | some _ => s'.gpr .x5 = BitVec.ofNat 64 (uω s₀)
        | none => s'.gpr .x5 = BitVec.ofNat 64 256) := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  have hω2 : (s.gpr .x2).toNat = uω s₀ := by rw [hc.x2, toNat_ofNat_small (by omega)]
  unfold hbuTrail
  refine WP.seq (WP.mono (cmp_ok (r := .x2) s (by omega) (by rw [h5, toNat_ofNat_small (by omega)]; omega))
    fun s₁ ⟨c₁, o₁⟩ => ?_)
  rw [h5, hω2, toNat_ofNat_small (by omega)] at c₁
  have hc₁ : UCom s₀ s₁ := hc.of_only o₁
  refine WP.ite _ (eval_nonzero s₁ .x10) (fun hlt => ?_) (fun hge => ?_)
  · rw [c₁] at hlt
    have hlt := of_decide_eq_true hlt
    refine WP.loop (M := isa) (fun m s' => ∃ u, m = uω s₀ - idx - u ∧ idx + u < uω s₀ ∧
        optFold (huTrail (uY s₀)) (List.range' idx u) () = some () ∧ s'.gpr .x5 = BitVec.ofNat 64 (idx + u) ∧
        UCom s₀ s' ∧ s'.mem = s.mem)
      (fun m s' ⟨u, hm, hu, hF, h5', hc', hm'⟩ => ?_) _ s₁
      ⟨0, rfl, by omega, rfl, by rw [o₁.get .x5, h5]; rfl, hc₁, o₁.mem⟩
    unfold hbuTrailByte
    refine WP.seq (WP.mono (yLoad_ok hp (r := .x10) (t := idx + u) (by omega) hc' h5') fun s₂ ⟨h10₂, o₂⟩ => ?_)
    have hc₂ : UCom s₀ s₂ := hc'.of_only o₂
    have hF1 : optFold (huTrail (uY s₀)) (List.range' idx (u + 1)) () = huTrail (uY s₀) () (idx + u) := by
      rw [optFold_range'_succ, hF]; rfl
    refine WP.seq (WP.ite _ (eval_nonzero s₂ .x10) (fun hne => ?_) (fun heq => ?_))
    · -- A nonzero byte: fail.
      rw [h10₂, nz_byte] at hne
      have hne := of_decide_eq_true hne
      have hn : optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () = none :=
        optFold_range'_none _ _ (show u + 1 ≤ uω s₀ - idx by omega) (by rw [hF1, huTrail, ite_pos' hne])
      refine WP.mono (fail_ok s₂) fun s₃ ⟨h5₃, o₃⟩ => ?_
      refine WP.mono (cmp_ok (r := .x2) s₃ (by rw [o₃.get .x2, hc₂.x2, toNat_ofNat_small (by omega)]; omega)
        (by rw [h5₃, toNat_ofNat_small (a := 256) (by decide)]; decide)) fun s₄ ⟨c₄, o₄⟩ => .inl ⟨?_, ?_⟩
      · rw [eval_nonzero, c₄, h5₃, o₃.get .x2, hc₂.x2, toNat_ofNat_small (a := 256) (by decide), toNat_ofNat_small (by omega)]
        exact congrArg some (decide_eq_false (by omega))
      · refine ⟨hc₂.of_only (o₃.trans o₄), by rw [o₄.mem, o₃.mem, o₂.mem, hm'], ?_⟩
        rw [hn]; rw [o₄.get .x5, h5₃]
    · -- A zero byte: next.
      rw [h10₂, nz_byte] at heq
      have heq := of_decide_eq_false heq
      have hF2 : optFold (huTrail (uY s₀)) (List.range' idx (u + 1)) () = some () := by
        rw [hF1, huTrail, ite_neg' heq]
      refine wp_addImm (by decide) fun s₃ o₃ e₃ => wp_nil ?_
      have h5₃ : s₃.gpr .x5 = BitVec.ofNat 64 (idx + (u + 1)) := by
        rw [e₃, o₂.get .x5, h5', ofNat_succ64, Nat.add_assoc]
      refine WP.mono (cmp_ok (r := .x2) s₃ (by rw [o₃.get .x2, hc₂.x2, toNat_ofNat_small (by omega)]; omega)
        (by rw [h5₃, toNat_ofNat_small (by omega)]; omega)) fun s₄ ⟨c₄, o₄⟩ => ?_
      have hc₄ : UCom s₀ s₄ := hc₂.of_only (o₃.trans o₄)
      rw [h5₃, o₃.get .x2, hc₂.x2, toNat_ofNat_small (by omega), toNat_ofNat_small (by omega)] at c₄
      have h5₄ : s₄.gpr .x5 = BitVec.ofNat 64 (idx + (u + 1)) := by rw [o₄.get .x5, h5₃]
      have hm₄ : s₄.mem = s.mem := by rw [o₄.mem, o₃.mem, o₂.mem, hm']
      by_cases e : idx + (u + 1) < uω s₀
      · exact .inr ⟨by rw [eval_nonzero, c₄, decide_eq_true e], _, by omega, u + 1, rfl, e, hF2, h5₄, hc₄, hm₄⟩
      · refine .inl ⟨by rw [eval_nonzero, c₄, decide_eq_false e], hc₄, hm₄, ?_⟩
        rw [show uω s₀ - idx = u + 1 by omega, hF2]
        rw [h5₄, show idx + (u + 1) = uω s₀ by omega]
  · -- `idx = ω`: nothing.
    rw [c₁] at hge
    have hge := of_decide_eq_false hge
    refine WP.block_nil ⟨hc₁, o₁.mem, ?_⟩
    rw [show uω s₀ - idx = 0 by omega]
    simp only [List.range'_zero, optFold]
    rw [o₁.get .x5, h5, show idx = uω s₀ by omega]

include hp in
theorem trail_fail {s : State} (hc : UCom s₀ s) (h5 : s.gpr .x5 = BitVec.ofNat 64 256) :
    WP isa hbuTrail s fun s' => UCom s₀ s' ∧ s'.mem = s.mem ∧ s'.gpr .x5 = BitVec.ofNat 64 256 := by
  obtain ⟨-, -, hω80, -, -⟩ := up_facts hp
  unfold hbuTrail
  refine WP.seq (WP.mono (cmp_ok (r := .x2) s (by rw [hc.x2, toNat_ofNat_small (by omega)]; omega)
    (by rw [h5, toNat_ofNat_small (a := 256) (by decide)]; decide)) fun s₁ ⟨c₁, o₁⟩ => ?_)
  rw [h5, hc.x2, toNat_ofNat_small (a := uω s₀) (by omega), toNat_ofNat_small (a := 256) (by decide)] at c₁
  refine WP.ite _ (eval_nonzero s₁ .x10) (fun h => ?_) fun _ => WP.block_nil ⟨hc.of_only o₁, o₁.mem, by
    rw [o₁.get .x5, h5]⟩
  rw [c₁] at h
  exact absurd (of_decide_eq_true h) (by omega)

/-! ## The return value -/

theorem hbuRet_ok {s : State} (h15 : s.gpr .x15 = BitVec.ofNat 64 1) (h2 : (s.gpr .x2).toNat < 2 ^ 63)
    (h5 : (s.gpr .x5).toNat < 2 ^ 63) :
    WP isa (.block hbuRet) s fun s' =>
      (s'.gpr .x0).setWidth 32 = (if (s.gpr .x2).toNat < (s.gpr .x5).toNat then 0 else 1) ∧ s'.mem = s.mem := by
  unfold hbuRet
  refine wp_sub fun s₁ o₁ e₁ => wp_lsr (by decide) fun s₂ o₂ e₂ => wp_eor fun s₃ o₃ e₃ =>
    wp_nil ⟨?_, by rw [o₃.mem, o₂.mem, o₁.mem]⟩
  have hb : s₂.gpr .x10 = BitVec.ofNat 64 (if (s.gpr .x2).toNat < (s.gpr .x5).toNat then 1 else 0) := by
    apply BitVec.eq_of_toNat_eq
    rw [e₂, e₁, sub_lsr63 h2 h5, toNat_ofNat_lt (by split <;> decide)]
  rw [e₃, hb, o₂.get .x15, o₁.get .x15, h15]
  split <;> rfl

/-! ## The function -/

include hp in
/-- The polynomials. -/
theorem hbuMain_ok {s : State} (hI : hbuInitPost s₀ s) :
    WP isa hbuMain s fun s' => OInv s₀ (uk s₀) s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  obtain ⟨hz, hf, h9, h3, h2, h12, hrd, hwr, hsp⟩ := hI
  have hl := (s₀.gpr .x1).isLt
  have e1 : uLen s₀ = (s₀.gpr .x1).toNat := rfl
  have hx12 : (s₀.gpr .x4 >>> 8).toNat = uk s₀ := by rw [lsr8_toNat, hr4]; omega
  have hx2 : s.gpr .x2 = BitVec.ofNat 64 (uω s₀) := by
    rw [h2]; apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, hx12, toNat_ofNat_lt (by omega)]
    omega
  unfold hbuMain
  refine WP.seq (wp_movz fun s₁ o₁ e₁ => wp_movz fun s₂ o₂ e₂ => wp_add fun s₃ o₃ e₃ => wp_nil ?_)
  have k₃ := (o₁.trans o₂).trans o₃
  refine count_loop (n := uk s₀) (by omega) (OInv s₀) (fun i hi s hP => upoly_ok hp hi hP)
    ⟨⟨by rw [k₃.get .x9, h9], by rw [k₃.get .x2, hx2], by rw [o₃.get .x15, e₂]; rfl, by rw [k₃.rd, hrd],
      by rw [k₃.wr, hwr], by rw [k₃.sp, hsp], by rw [k₃.mem]; exact hf⟩,
      by rw [k₃.get .x3, h3]; exact (ptr_zero _).symm,
      by rw [e₃, o₂.get .x9, o₁.get .x9, o₂.get .x2, o₁.get .x2, h9, hx2, Nat.add_zero],
      by rw [k₃.get .x12, h12, hx12]; rfl,
      ⟨by rw [o₃.get .x5, o₂.get .x5, e₁]; rfl, Nat.zero_le _, by rw [k₃.mem]; exact harr_zero hp hz⟩⟩

/-- The hint of the spec, from the words. -/
theorem harr_hintIs {m : Mem} {hA : Array (Vector Bool n)} (hh : HArr s₀ m hA) :
    HintIs m (s₀.gpr .x3) (uk s₀) hA.toList := by
  refine ⟨by rw [Array.length_toList, hh.1], fun i hi j hj => ?_⟩
  rw [hh.2 i hi j hj]
  congr 3
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]

include hp in
theorem hbu_wp :
    WP isa Impl.MlDsa.AArch64.Pack.hintBitUnpack s₀ fun s' => hintBitUnpackK.post s₀ s' := by
  obtain ⟨hk4, hk8, hω80, hsum, hr4⟩ := up_facts hp
  unfold Impl.MlDsa.AArch64.Pack.hintBitUnpack
  refine WP.seq (WP.mono (hbuInit_ok hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (hbuMain_ok hp h₁) fun s₂ hI => ?_)
  -- The spec, as folds.
  show WP isa _ s₂ fun s' => match hintBitUnpack (uω s₀) (uk s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat) with
    | some hint => (s'.gpr .x0).setWidth 32 = 1 ∧ HintIs s'.mem (s₀.gpr .x3) (uk s₀) hint
    | none => (s'.gpr .x0).setWidth 32 = 0
  rw [hintBitUnpack_eq]
  have hst := hI.st
  have hω2 : ∀ {s : State}, UCom s₀ s → (s.gpr .x2).toNat = uω s₀ := fun hc => by
    rw [hc.x2, toNat_ofNat_small (by omega)]
  cases hS : huS s₀ (uk s₀) with
  | none =>
    rw [hS] at hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = none from hS]
    refine WP.seq (WP.mono (trail_fail hp hI.com hst) fun s₃ ⟨hc₃, m₃, h5₃⟩ => ?_)
    refine WP.mono (hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, toNat_ofNat_small (a := 256) (by decide)]; decide))
      fun s₄ ⟨r₄, m₄⟩ => ?_
    show (s₄.gpr .x0).setWidth 32 = 0
    rw [r₄, hω2 hc₃, h5₃, toNat_ofNat_small (a := 256) (by decide), ite_pos' (by omega)]
  | some st =>
    obtain ⟨hA, idx⟩ := st
    rw [hS] at hst
    obtain ⟨h5, hidx, hh⟩ := hst
    rw [show optFold (huPoly (uω s₀) (bytesAt s₀.mem (s₀.gpr .x0) (s₀.gpr .x1).toNat).toArray)
      (List.range (uk s₀)) (Array.replicate (uk s₀) noHint, 0) = some (hA, idx) from hS]
    refine WP.seq (WP.mono (trail_ok hp hidx hI.com h5) fun s₃ ⟨hc₃, m₃, hr₃⟩ => ?_)
    dsimp only
    revert hr₃
    cases optFold (huTrail (uY s₀)) (List.range' idx (uω s₀ - idx)) () with
    | none =>
      intro h5₃
      refine WP.mono (hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, toNat_ofNat_small (a := 256) (by decide)]; decide))
        fun s₄ ⟨r₄, m₄⟩ => ?_
      show (s₄.gpr .x0).setWidth 32 = 0
      rw [r₄, hω2 hc₃, h5₃, toNat_ofNat_small (a := 256) (by decide), ite_pos' (by omega)]
    | some _ =>
      intro h5₃
      refine WP.mono (hbuRet_ok hc₃.x15 (by rw [hω2 hc₃]; omega) (by rw [h5₃, toNat_ofNat_small (by omega)]; omega))
        fun s₄ ⟨r₄, m₄⟩ => ⟨?_, by rw [m₄, m₃]; exact harr_hintIs hh⟩
      rw [r₄, hω2 hc₃, h5₃, toNat_ofNat_small (by omega), ite_neg' (Nat.lt_irrefl _)]

end

theorem hintBitUnpack_correct (s : State) (hs : hintBitUnpackK.pre s) :
    ∃ t s', Exec isa Impl.MlDsa.AArch64.Pack.hintBitUnpack s t s' ∧ abiPreserved s s' ∧
      hintBitUnpackK.post s s' := by
  obtain ⟨t, s', he, hb⟩ := hbu_wp hs
  exact ⟨t, s', he, abi_of rfl (by decide +kernel) he, hb⟩

/-! ## Constant time -/

/-- The public registers of the loops: `y`, `ω`, `h` and `k`. -/
abbrev hbuTaint : VG.AArch64.Taint.T := VG.AArch64.Taint.ofRegs [.x9, .x2, .x3, .x12]

theorem hintBitUnpack_ct :
    ConstantTime isa hintBitUnpackK.pre hintBitUnpackK.pub Impl.MlDsa.AArch64.Pack.hintBitUnpack := by
  refine RelCT.constantTime (Q := fun _ _ => True) ?_
  refine RelCT.seq (R := memTaint.Agree hbuTaint) ?_
    (RelCT.taint (A := memTaint) hbuTaint (fun _ _ h => h) (by taint_decide))
  refine RelCT.mono (RelCT.wpDep (F := hbuInitPost)
    (RelCT.taint (A := taint) (Taint.ofRegs [.x0, .x1, .x3, .x4])
      (fun _ _ ⟨_, _, h0, h1, h3, h4, hsp, _⟩ => agree_of hsp (by simp [h0, h1, h3, h4])) (by taint_decide))
    (fun x y ⟨hx, hy, _⟩ => ⟨hbuInit_ok hx, hbuInit_ok hy⟩)) (fun _ _ h => h)
    fun x' y' ⟨_, x, y, ⟨hx, hy, hp⟩, fx, fy⟩ => ?_
  obtain ⟨hz₁, hf₁, a9, a3, a2, a12, rd₁, wr₁, sp₁⟩ := fx
  obtain ⟨hz₂, hf₂, b9, b3, b2, b12, rd₂, wr₂, sp₂⟩ := fy
  obtain ⟨p0, p1, p3, p4, psp, hleak⟩ := hp
  have hrd : x'.rd = y'.rd := by rw [rd₁, rd₂, hx.1, hy.1, p0, p1]
  have hwr : x'.wr = y'.wr := by rw [wr₁, wr₂, hx.2.1, hy.2.1, p3, p4]
  refine ⟨agree_of (by rw [sp₁, sp₂, psp]) fun r hr => ?_, hrd, hwr, fun a ha => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · rw [a9, b9, p0]
    · rw [a2, b2, p1, p4]
    · rw [a3, b3, p3]
    · rw [a12, b12, p4]
  · rw [rd₁, wr₁, hx.1, hx.2.1] at ha
    obtain ⟨r, hr, hc⟩ := ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · -- `y`: as on entry, where the runs agree.
      rw [hf₁ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr; exact hx.2.2.1 a hc hc'),
        hf₂ a (fun r hr hc' => by
          simp only [List.mem_singleton] at hr; subst hr
          simp only [uR, ← p3, ← p4] at hc'
          exact hx.2.2.1 a hc hc')]
      have hlt : (a - x.gpr .x0).toNat < (x.gpr .x1).toNat := by simp only [Region.Contains] at hc; omega
      have ea : a = x.gpr .x0 + BitVec.ofNat 64 (a - x.gpr .x0).toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm, BitVec.sub_add_cancel]
      have hb : bytesAt x.mem (x.gpr .x0) (x.gpr .x1).toNat = bytesAt y.mem (x.gpr .x0) (x.gpr .x1).toNat := by
        have hl2 := hleak
        rw [← p0, ← p1] at hl2
        exact map_toNat_inj hl2
      have h₁ := congrArg (·.getD (a - x.gpr .x0).toNat 0) hb
      rw [bytesAt_getD _ _ hlt, bytesAt_getD _ _ hlt, ← ea] at h₁
      exact h₁
    · -- `h`: zeros.
      rw [byte_of_zero_words hz₁ hc, byte_of_zero_words hz₂ (by rw [← p3, ← p4]; exact hc)]

/-- A state satisfying the precondition. -/
def hintBitUnpackSat : State where
  gpr r := match r with
    | .x0 => 0x1000 | .x1 => 84 | .x2 => 80 | .x3 => 0x3000 | .x4 => 1024 | _ => 0
  sp := 0x10000
  mem _ := 0
  rd := [⟨0x1000, 84⟩]
  wr := [⟨0x3000, 4096⟩]

theorem hintBitUnpack_verified :
    Verified AArch64.target Impl.MlDsa.AArch64.Pack.hintBitUnpack (hintBitUnpackContract AArch64.abi) :=
  Verified.of_correct hintBitUnpack_correct hintBitUnpack_ct
    { pre := by sig_implies_pre [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      post := by sig_implies_post [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      pub := by sig_implies_pub [hintBitUnpackContract, hintBitUnpackSig, hintBitUnpackK, AArch64.abi,
        AArch64.argRegs]
      sat := by
        refine ⟨hintBitUnpackSat, ?_⟩
        sig_pre [hintBitUnpackContract, hintBitUnpackSig, AArch64.abi, AArch64.argRegs]
        and_intros
        all_goals first
          | rfl
          | exact Region.disjoint_of_sep (by decide)
          | decide }

end VG.Proof.MlDsa.AArch64.Pack
