import VerifiedGarbage.Proof.MlDsa.X86_64.Round.Bits

/-!
# ML-DSA on x86-64: `vg_mldsa_use_hint`
-/

namespace VG.Proof.MlDsa.X86_64.Round

open VG VG.X86_64 VG.Impl.MlDsa.X86_64.Round VG.Proof.MlDsa.Round
open VG.Spec.MlDsa
open VG.Proof.MlKem.X86_64 (Keep Keep.gpr WP.keep gprPreserved_of)

/-! ## The body -/

/-- `f`, from the coefficient `a` of `r`. -/
abbrev uhF (g : Nat) (a : BitVec 32) : BitVec 64 := hbRawV g (BitVec.setWidth 64 a)

/-- `δ`: `±1` (as `r₀ > 0`) masked by whether the hint `hv` is not 0. -/
def uhDelta (g : Nat) (hv a : BitVec 32) : BitVec 64 :=
  ((0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.ofNat 64 ((uhF g a).toNat *
      (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat)).toNat < (BitVec.setWidth 64 a).toNat))) &&& 2) - 1) &&&
    (0#64 - BitVec.setWidth 64 (BitVec.ofBool (decide ((BitVec.setWidth 64 (0 : BitVec 32)).toNat <
      (BitVec.setWidth 64 hv).toNat))))

/-- `m` as the immediate of the code. -/
abbrev mImm (g : Nat) : BitVec 32 := BitVec.ofNat 32 (dMod g)

/-- The value the body stores. -/
def uhS (g : Nat) (hv a : BitVec 32) : BitVec 32 :=
  BitVec.setWidth 32 (condAddV (condAddV (uhDelta g hv a + uhF g a + BitVec.signExtend 64 (mImm g))
    (BitVec.signExtend 64 (mImm g)) (mImm g)) (BitVec.signExtend 64 (mImm g)) (mImm g))

theorem uhBody_ok {g : Nat} (hg : g = g32 ∨ g = g88) (s : State)
    (h1 : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 4)
    (h1' : InRegions (s.rd ++ s.wr) (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 4)
    (h2 : InRegions s.wr (cfAddr (s.gpr .r10) (s.gpr .rcx)) 4) :
    WP isa (.block (uhBody g ++ ([.alu .sub .rcx (.imm 1)] : List Instr))) s fun s' =>
      (s'.mem = s.mem.writeW (cfAddr (s.gpr .r10) (s.gpr .rcx))
          (uhS g (s.mem.readW (cfAddr (s.gpr .rdi) (s.gpr .rcx)) 32) (s.mem.readW (cfAddr (s.gpr .rsi) (s.gpr .rcx)) 32)) ∧
        s'.gpr .rcx = s.gpr .rcx - 1 ∧ s'.zf = some (s.gpr .rcx - 1 == 0)) ∧
      Keep [.rax, .rdx, .r8, .r9, .r11, .rcx] s s' := by
  refine WP.keep _ ?_ (by rcases hg with rfl | rfl <;> decide)
  unfold uhBody hbRaw condAdd
  xrun [h1, h1', h2, ea_cf, List.cons_append, List.nil_append, uhS, uhDelta, hbRawV, condAddV, dShift_ge, dShift_le]

/-! ## The value -/

/-- `condAdd` of an immediate `k` and mask `k`: `r - k` unless `r < k`. -/
theorem condAddV_imm_toNat' {r : BitVec 64} {k : Nat} (hk : k < 2 ^ 31) (hr : r.toNat < 2 ^ 63) :
    (condAddV r (BitVec.signExtend 64 (BitVec.ofNat 32 k)) (BitVec.ofNat 32 k)).toNat =
      if r.toNat < k then r.toNat else r.toNat - k := by
  have e := sx_ofNat_toNat hk
  have e' : (BitVec.ofNat 32 k).toNat = k := by rw [BitVec.toNat_ofNat]; omega
  rw [condAddV_toNat (by omega) (by omega), e, e']
  split <;> omega

theorem sgn_eq (c : Bool) : ((0#64 - BitVec.setWidth 64 (BitVec.ofBool c)) &&& 2) - 1 =
    if c then 1 else BitVec.allOnes 64 := by cases c <;> decide

theorem and_mask (c : Bool) (y : BitVec 64) : (y &&& (0#64 - BitVec.setWidth 64 (BitVec.ofBool c))) =
    if c then y else 0 := by
  cases c
  · have : (0#64 - BitVec.setWidth 64 (BitVec.ofBool false)) = 0 := by decide
    rw [this]; exact BitVec.and_zero
  · have : (0#64 - BitVec.setWidth 64 (BitVec.ofBool true)) = BitVec.allOnes 64 := by decide
    rw [this, BitVec.and_allOnes]; rfl

theorem dMod_cases (g : Nat) : dMod g = 16 ∨ dMod g = 44 := by unfold dMod; split <;> simp

/-- Two conditional subtractions of `m` reduce `x ≤ 2m + 1` modulo `m`. -/
theorem condAddV_twice {g : Nat} {x : BitVec 64} (hx : x.toNat ≤ 2 * dMod g + 1) :
    (condAddV (condAddV x (BitVec.signExtend 64 (mImm g)) (mImm g)) (BitVec.signExtend 64 (mImm g))
      (mImm g)).toNat = x.toNat % dMod g := by
  have hm : dMod g < 2 ^ 31 := by rcases dMod_cases g with e | e <;> rw [e] <;> decide
  rw [condAddV_imm_toNat' hm (by rw [condAddV_imm_toNat' hm (by omega)]; split <;> omega),
    condAddV_imm_toNat' hm (by omega)]
  rcases dMod_cases g with e | e <;> rw [e] at hx ⊢ <;> (repeat' split) <;> omega

theorem uhS_toNat {g : Nat} (h : g ∈ gamma2s) (hv : BitVec 32) {a : BitVec 32} (ha : a.toNat < q) :
    (uhS g hv a).toNat = (if hv ≠ 0 then (if hbF g a.toNat * (2 * g) < a.toNat then
      hbF g a.toNat + Proof.MlDsa.Round.hbM g + 1 else hbF g a.toNat + Proof.MlDsa.Round.hbM g - 1)
      else hbF g a.toNat + Proof.MlDsa.Round.hbM g) % Proof.MlDsa.Round.hbM g := by
  have ha' : (BitVec.setWidth 64 a).toNat < q := by rw [setWidth64_toNat]; exact ha
  have hf := hbF_le h ha
  have hF : (uhF g a).toNat = hbF g a.toNat := by rw [uhF, hbRawV_toNat h ha', setWidth64_toNat]
  have hg : 2 * g < 2 ^ 31 := by rcases mem_gamma2s h with rfl | rfl <;> decide
  have hfg : hbF g a.toNat * (2 * g) ≤ q - 1 := by
    rw [← hbM_mul h]; exact Nat.mul_le_mul_right _ hf
  have eX : (BitVec.ofNat 64 ((uhF g a).toNat * (BitVec.setWidth 64 (BitVec.ofNat 32 (2 * g))).toNat)).toNat =
      hbF g a.toNat * (2 * g) := by
    rw [BitVec.toNat_ofNat, hF, setWidth64_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 2 * g < 2 ^ 32 by omega)]
    rw [q_eq] at hfg
    omega
  have e0 : (BitVec.setWidth 64 (0 : BitVec 32)).toNat = 0 := rfl
  have eh : decide (0 < (BitVec.setWidth 64 hv).toNat) = decide (hv ≠ 0) := by
    rw [setWidth64_toNat]
    by_cases h0 : hv = 0
    · subst h0; rfl
    · rw [decide_eq_true h0, decide_eq_true_iff]
      exact Nat.pos_of_ne_zero fun e => h0 (BitVec.eq_of_toNat_eq e)
  have hM := dMod_eq h
  have hm : (BitVec.signExtend 64 (mImm g)).toNat = dMod g := sx_ofNat_toNat (by unfold dMod; split <;> decide)
  have hm16 : 16 ≤ dMod g ∧ dMod g ≤ 44 := by rcases dMod_cases g with e | e <;> rw [e] <;> decide
  rw [← hM] at hf ⊢
  have hU : (uhDelta g hv a + uhF g a + BitVec.signExtend 64 (mImm g)).toNat =
      if hv ≠ 0 then (if hbF g a.toNat * (2 * g) < a.toNat then hbF g a.toNat + dMod g + 1
        else hbF g a.toNat + dMod g - 1) else hbF g a.toNat + dMod g := by
    unfold uhDelta
    rw [eX, e0, eh, sgn_eq, and_mask, setWidth64_toNat]
    by_cases hb : hv ≠ 0 <;> by_cases hp : hbF g a.toNat * (2 * g) < a.toNat
    · rw [decide_eq_true hb, decide_eq_true hp]
      simp only [↓reduceIte, ne_eq, hb, hp, not_false_eq_true]
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, hm, show (1 : BitVec 64).toNat = 1 from rfl]; omega
    · rw [decide_eq_true hb, decide_eq_false hp]
      simp only [↓reduceIte, ne_eq, hb, hp, not_false_eq_true, Bool.false_eq_true]
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, hm, BitVec.toNat_allOnes]; omega
    · rw [decide_eq_false hb]
      simp only [↓reduceIte, hb, Bool.false_eq_true]
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, hm, show (0 : BitVec 64).toNat = 0 from rfl]; omega
    · rw [decide_eq_false hb]
      simp only [↓reduceIte, hb, Bool.false_eq_true]
      rw [BitVec.toNat_add, BitVec.toNat_add, hF, hm, show (0 : BitVec 64).toNat = 0 from rfl]; omega
  rw [uhS, BitVec.toNat_setWidth, condAddV_twice (by rw [hU]; split <;> [split; skip] <;> omega), hU]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega))

/-! ## The function -/

theorem useHint_correct (s₀ : State) (hp : useHintK.pre s₀) :
    ∃ t s', Exec isa useHint s₀ t s' ∧ abiPreserved s₀ s' ∧ useHintK.post s₀ s' := by
  have hg : arg32 s₀ .rdx ∈ gamma2s := hp.2.2.2.2.2.2.2.1
  obtain ⟨t, s', he, ⟨hv, hf⟩, hk⟩ := WP.keep [.rax, .rcx, .rdx, .r8, .r9, .r10, .r11]
    (oneOut_ok (ins := [.rdi, .rsi]) (F := fun g xs => uhS g (xs.getD 0 0) (xs.getD 1 0))
      (fun p h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rw [hp.1]; rcases h with rfl | rfl <;> simp)
      hp.2.1 (fun p h => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        exacts [hp.2.2.1, hp.2.2.2.1]) hg (prologue_rdx_rcx s₀)
      (fun p h => by simp only [List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> decide)
      (by decide) (by decide)
      fun g hg' s h1 h2 => uhBody_ok hg' s (h1 _ List.mem_cons_self)
        (h1 _ (List.mem_cons_of_mem _ List.mem_cons_self)) h2) (by decide)
  have hr : Reduced s₀.mem (s₀.gpr .rsi) := hp.2.2.2.2.2.2.2.2
  refine ⟨t, s', he, abiPreserved_of_exec (by decide) he (gprPreserved_of hk (by decide) hf ?_), ?_⟩
  · simpa using hp.2.2.2.2.2.2.1
  · refine natPolyIs_of_toNat fun k hk => ?_
    rw [hv k hk, zipWith_get _ _ _ hk, hintAt_get _ _ hk, useHint_eq hg, polyAt_val hr hk, Int.toNat_natCast]
    simp only [List.map_cons, List.map_nil, List.getD_cons_zero, List.getD_cons_succ]
    rw [uhS_toNat hg _ (hr k hk)]
    simp only [decide_eq_true_eq]

theorem useHint_ct : ConstantTime isa useHintK.pre useHintK.pub useHint :=
  VG.Taint.constantTime (A := X86_64.taint) (regsLo [.rdi, .rsi, .rcx, .rsp] [.rdx])
    (fun _ _ _ _ hp => agree_regsLo (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl
      exacts [hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1]) fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; exact hp.2.2.2.2)
    (by taint_decide)

/-- A state satisfying the precondition. -/
def hintSat : State where
  gpr r := match r with
    | .rdi => 0x1000 | .rsi => 0x2000 | .rdx => 95232 | .rcx => 0x3000 | .rsp => 0x8000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem _ := 0
  rd := [⟨0x1000, 1024⟩, ⟨0x2000, 1024⟩]
  wr := [⟨0x3000, 1024⟩]

theorem useHint_verified : Verified X86_64.target useHint (useHintContract X86_64.abi) :=
  Verified.of_correct useHint_correct useHint_ct (by
    round_implies [useHintContract, useHintSig, useHintK, hintK, X86_64.abi, X86_64.argRegs] [hintSat]
      using hintSat)

end VG.Proof.MlDsa.X86_64.Round
