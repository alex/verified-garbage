import VerifiedGarbage.Proof.CmacTripleDes.Arm.RoundLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.CmacTripleDes.Des
import VerifiedGarbage.Proof.Framework.Arm.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A DES round on 32-bit ARM

Untrusted: everything here is checked by Lean.

As on x86-64 (`Proof/CmacTripleDes/X86_64/Round.lean`): the round's parts are
checked by evaluation (`Straight.check`), the broadcast inputs (`inputs`)
and the output (`output`) over the lane domain, and each half's S-boxes
(`mux`) over the row domain (`Bitslice.rows`), on all 64 values of a box's
input at once. A half's slots hold, at each position, the bits of one box's
input, so each half is checked on its own. `round_ok` composes them: `R` and
`L ⊕ f(R, K)`, with `K` the round key's low word and the low 16 bits of its
high word.
-/

namespace VG.Proof.CmacTripleDes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.Arm

/-- The round's memory: the broadcast inputs and half 0's outputs in slots
0–12 at `r10`, and the round key's two words at `r9`. -/
def rCfg : Cfg := { base := .r10, slots := 13, ext := .r9, exts := 2 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r10) k) 32

/-- The round key's words. -/
abbrev keyLo (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r9) 0) 32
abbrev keyHi (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .r9) 1) 32

/-- The round key: the low 16 bits of its high word, and its low word. -/
abbrev key48 (s : State) : BitVec 48 := (keyHi s).setWidth 16 ++ keyLo s

/-! ## The inputs -/

/-- Bit `b` of the round key, as an atom: of its low word (input word 1) or
its high word (input word 2). -/
def keyAtom (b : Nat) : Nat := if b < 32 then 32 + b else 64 + (b - 32)

/-- Bit `p` of slot `t` (half `t / 6`, input bit `t % 6`): in lane `p / 6`,
below its fifth bit, `R`'s bit (atom `0 … 31`) XOR the key's. -/
def inG (t p : Nat) : List Nat :=
  if p < 24 ∧ p % 6 < 4 then
    [expSrc (24 * (t / 6) + 6 * (p / 6) + t % 6), keyAtom (24 * (t / 6) + 6 * (p / 6) + t % 6)]
  else []

def inPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 12).all fun t => e.slot t == some (outWord (inG t))

theorem inputs_check :
    check (lanes 32 7) rCfg (linExt 1) inputs (linEnv [(.r8, 0)]) inPost = true := by
  lit_decide

theorem inG_lt : ∀ t < 12, ∀ p < 32, ∀ a ∈ inG t p, a < 2 ^ 7 := by lit_decide

/-- The registers the round keeps. -/
def kept : List Reg := [.r9, .r10, .r11, .r12, .lr]

theorem inputs_kept :
    (.r7 :: .r8 :: kept).all (fun r => inputs.all fun i => dstOf i != some r) = true := by
  lit_decide

/-- The inputs of `inputs`: `R` and the round key's words. -/
def inW (s : State) (i : Nat) : BitVec 32 := if i = 0 then s.gpr .r8 else if i = 1 then keyLo s else keyHi s

theorem inputs_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 12, ∀ p < 32, (slotW s' t).getLsbD p = xorBits (inW s) (inG t p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ .r7 :: .r8 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ inputs_check
  have hrel : Rel (LaneRel 7 (assign (inW s) (2 ^ 7))) rCfg (linExt 1) (linEnv [(.r8, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_, fun _ _ h => by cases h⟩
    · simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel (inW s) (i := 0) (by decide)
      · simp at h
    · simp only [rCfg] at hj
      simp only [linExt, Option.some.injEq] at h; subst h
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact inWord_rel (inW s) (i := 1) (by decide)
      · exact inWord_rel (inW s) (i := 2) (by decide)
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun t ht q hq => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost t (List.mem_range.mpr ht)
    simp only [beq_iff_eq] at h
    exact outWord_rel (inG_lt t ht) (p.rel.slot t _ (by simp only [rCfg]; omega) h) q hq
  · rw [List.all_eq_true.mp inputs_kept r hr]; decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t % 6` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 32).testBit (t % 6)) 2048

/-- Half `h`'s slots. -/
def sbEnv (h : Nat) : Env Nat :=
  { reg := fun _ => none, slot := fun t => if 6 * h ≤ t ∧ t < 6 * h + 6 then some (rowIn t) else none }

theorem sboxes_eq : sboxes = sbCode 0 ++ ([.str .r0 .r10 48] : List Instr) ++ sbCode 1 := rfl

/-- At bit `6 j + off i b` (`i` the box in lane `j` of half `h`), output bit
`b` of box `i`, on every row. -/
def sbPost (h : Nat) (e : Env Nat) : Bool :=
  match e.reg .r0 with
  | some F => (List.range 4).all fun j => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) ==
        (Proof.TripleDes.outputTable (boxOf h j) b).testBit c
  | none => false

/-- The slots half `h` reads: the broadcast inputs up to its own. -/
def sCfg (h : Nat) : Cfg := { base := .r10, slots := 6 * h + 6, ext := .r9, exts := 0 }

theorem sbox0_check : check (rows 32 6) (sCfg 0) (fun _ => none) (sbCode 0) (sbEnv 0) (sbPost 0) = true := by
  lit_decide

theorem sbox1_check : check (rows 32 6) (sCfg 1) (fun _ => none) (sbCode 1) (sbEnv 1) (sbPost 1) = true := by
  lit_decide

theorem sbox_kept (h : Nat) (hh : h < 2) :
    (.r7 :: .r8 :: kept).all (fun r => (sbCode h).all fun i => dstOf i != some r) = true := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> lit_decide

/-- The input of the box whose lane of half `h` holds bit `p`, from bit `p`
of the slots. -/
def boxIn (h : Nat) (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (slotW s (6 * h + t)).getLsbD p

theorem off_lt4 : ∀ h < 2, ∀ j < 4, ∀ b < 4, off (boxOf h j) b < 4 := by decide

theorem sbox_ok {h : Nat} (hh : h < 2) {s : State} (hok : Ok (sCfg h) s) :
    ∃ s', runBlock isa (sbCode h) s = some s' ∧
      (∀ j < 4, ∀ b < 4, (s'.gpr .r0).getLsbD (6 * j + off (boxOf h j) b) =
        (Spec.TripleDes.sBox (boxOf h j) (boxIn h s (6 * j + off (boxOf h j) b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ .r7 :: .r8 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion (sCfg h) s] s.mem s'.mem := by
  have hchk : check (rows 32 6) (sCfg h) (fun _ => none) (sbCode h) (sbEnv h) (sbPost h) = true := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact sbox0_check
    · exact sbox1_check
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .r0 = some F ∧ ∀ j < 4, ∀ b < 4, ∀ c < 64,
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) =
        (Spec.TripleDes.sBox (boxOf h j) (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun j hj b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost j
        (List.mem_range.mpr hj)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      rw [← Proof.TripleDes.testBit_outputTable hc]
      simpa using this
    · cases hpost
  have key : ∀ p < 32, ∃ s', runBlock isa (sbCode h) s = some s' ∧
      Post (RowRel p (boxIn h s p).toNat) (sCfg h) (fun _ => none) e' s s'
        (fun r => ((sbCode h).all fun i => dstOf i != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (boxIn h s p).isLt) hok
      ⟨fun r a h => by simp [sbEnv] at h, fun t a ht h' => ?_, (fun _ _ _ h => by cases h),
        fun _ _ h => by cases h⟩ he
    simp only [sbEnv] at h'
    split at h'
    · rename_i ht6
      cases h'
      show (rowIn t).testBit (32 * (boxIn h s p).toNat + p) = (slotW s t).getLsbD p
      have hc := (boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 6 * h + u ∧ u < 6 := ⟨t - 6 * h, by omega, by omega⟩
      rw [rowIn, testBit_tableOf, decide_eq_true (by omega : 32 * (boxIn h s p).toNat + p < 2048),
        Bool.true_and, show (32 * (boxIn h s p).toNat + p) / 32 = (boxIn h s p).toNat by omega,
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, show (6 * h + u) % 6 = u by omega,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr, p₀.sp, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hp : 6 * j + off (boxOf h j) b < 32 := by have := off_lt4 h hh j hj b hb; omega
    obtain ⟨s'', hs'', p₁⟩ := key _ hp
    obtain rfl := run_unique hs'' hs'
    have h' := p₁.rel.reg .r0 F hF
    simp only [RowRel] at h'
    rw [← h', hout j hj b hb _ (boxIn h s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.all_eq_true.mp (sbox_kept h hh) r hr]; decide

/-! ## The output -/

/-- The atom of output bit `u` of the S-boxes: bit `outPos u` of half 1's
outputs (`r0`, input word 0) or of half 0's (slot 12, input word 3). -/
def sAtom (u : Nat) : Nat := if outHalf u = 0 then 96 + outPos u else outPos u

/-- `r7`: `R` (input word 2). -/
def oG7 (p : Nat) : List Nat := [64 + p]

/-- `r8`: bit `j` of `L` (input word 1) XOR the S-boxes' bit `pSrc j`. -/
def oG8 (p : Nat) : List Nat := if p < 32 then [sAtom (pSrc p), 32 + p] else [32 + p]

def oEnv : Env (Nat × Nat) :=
  { reg := fun r => if r = .r0 then some (inWord 0) else if r = .r7 then some (inWord 1)
      else if r = .r8 then some (inWord 2) else none,
    slot := fun k => if k = 12 then some (inWord 3) else none }

def oPost (e : Env (Nat × Nat)) : Bool :=
  e.reg .r7 == some (outWord oG7) && e.reg .r8 == some (outWord oG8)

/-- The slots of the output: half 0's outputs, in slot 12. -/
def oCfg : Cfg := { base := .r10, slots := 13, ext := .r9, exts := 0 }

theorem output_check : check (lanes 32 7) oCfg (fun _ => none) output oEnv oPost = true := by
  lit_decide

theorem oG_lt : ∀ p < 32, (∀ a ∈ oG7 p, a < 2 ^ 7) ∧ ∀ a ∈ oG8 p, a < 2 ^ 7 := by lit_decide

theorem output_kept : kept.all (fun r => output.all fun i => dstOf i != some r) = true := by
  lit_decide

/-- The inputs of `output`. -/
def oW (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then s.gpr .r0 else if i = 1 then s.gpr .r7 else if i = 2 then s.gpr .r8 else slotW s 12

theorem output_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa output s = some s' ∧
      (∀ p < 32, (s'.gpr .r7).getLsbD p = xorBits (oW s) (oG7 p)) ∧
      (∀ p < 32, (s'.gpr .r8).getLsbD p = xorBits (oW s) (oG8 p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ output_check
  have hrel : Rel (LaneRel 7 (assign (oW s) (2 ^ 7))) oCfg (fun _ => none) oEnv s := by
    refine ⟨fun r a h => ?_, fun k a hk h => ?_, (fun _ _ _ h => by cases h), fun _ _ h => by cases h⟩
    · simp only [oEnv] at h
      split at h
      · rename_i hr; subst hr; cases h; exact inWord_rel (oW s) (i := 0) (by decide)
      · split at h
        · rename_i _ hr; subst hr; cases h; exact inWord_rel (oW s) (i := 1) (by decide)
        · split at h
          · rename_i _ _ hr; subst hr; cases h; exact inWord_rel (oW s) (i := 2) (by decide)
          · cases h
    · simp only [oEnv] at h
      split at h
      · rename_i hk; subst hk; cases h; exact inWord_rel (oW s) (i := 3) (by decide)
      · cases h
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  simp only [oPost, Bool.and_eq_true, beq_iff_eq] at hpost
  refine ⟨s', hs', fun q hq => ?_, fun q hq => ?_, p.rd, p.wr, p.sp, fun r hr => p.other r ?_, p.frame⟩
  · exact outWord_rel (fun p hp => (oG_lt p hp).1) (p.rel.reg .r7 _ hpost.1) q hq
  · exact outWord_rel (fun p hp => (oG_lt p hp).2) (p.rel.reg .r8 _ hpost.2) q hq
  · rw [List.all_eq_true.mp output_kept r hr]; decide

/-! ## The round -/

theorem runBlock_append (a b : List Instr) (s : State) :
    runBlock isa (a ++ b) s = (runBlock isa a s).bind (runBlock isa b) := by
  induction a generalizing s with
  | nil => rw [List.nil_append, runBlock_nil]; rfl
  | cons i is ih =>
    rw [List.cons_append, runBlock_cons, runBlock_cons]
    cases exec i s with
    | none => rfl
    | some s' => rw [runStep_some, runStep_some, ih]

theorem wordAddr_eq (b : BitVec 32) {k : Nat} (h : b.toNat + 4 * k < 2 ^ 32) :
    wordAddr b k = State.addr b + BitVec.ofNat 64 (4 * k) := addr_add h

/-- Word `k` of the slots is outside a frame on the first `n` words. -/
theorem slot_frame {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨State.addr b, 4 * n⟩] m m')
    (hk : n ≤ k) (hb : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [wordAddr_eq b (by omega)]
  refine hf.readW (r := ⟨State.addr b + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega) (by omega)

/-- Words `j` and `k` of the slots are apart. -/
theorem slot_word_sep (b : BitVec 32) {j k : Nat} (h : j ≠ k) (hj : b.toNat + 4 * j + 4 ≤ 2 ^ 32)
    (hk : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : Mem.Sep (wordAddr b j) (32 / 8) (wordAddr b k) (32 / 8) := by
  rw [wordAddr_eq b (by omega), wordAddr_eq b (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : State}
    (hx : ∀ t < 12, ∀ p < 32, (slotW s₁ t).getLsbD p = xorBits (inW s) (inG t p))
    {h j o : Nat} (hh : h < 2) (hj : j < 4) (ho : o < 4) :
    boxIn h s₁ (6 * j + o) = chunk (s.gpr .r8) (key48 s) (boxOf h j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega
  have hE := expSrc_lt (24 * h + 6 * j + t) (by omega)
  rw [boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, hx (6 * h + t) (by omega) _ (by omega),
    getLsbD_chunk _ _ (by simp only [boxOf]; omega) ht, inG, ite_eq_left (by omega), hb,
    show (6 * h + t) / 6 = h by omega, show (6 * h + t) % 6 = t by omega, show (6 * j + o) / 6 = j by omega]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, keyAtom]
  rw [Nat.div_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega),
    Nat.mod_eq_of_lt (show expSrc (24 * h + 6 * j + t) < 32 by omega), ite_eq_left rfl]
  congr 1
  rw [BitVec.getLsbD_append]
  by_cases h32 : 24 * h + 6 * j + t < 32
  · rw [ite_eq_left h32, ite_eq_left h32, show (32 + (24 * h + 6 * j + t)) / 32 = 1 by omega,
      show (32 + (24 * h + 6 * j + t)) % 32 = 24 * h + 6 * j + t by omega]
    rfl
  · rw [ite_eq_right h32, ite_eq_right h32, show (64 + (24 * h + 6 * j + t - 32)) / 32 = 2 by omega,
      show (64 + (24 * h + 6 * j + t - 32)) % 32 = 24 * h + 6 * j + t - 32 by omega,
      BitVec.getLsbD_setWidth, decide_eq_true (by omega : 24 * h + 6 * j + t - 32 < 16), Bool.true_and]
    rfl

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

theorem rCfg_s0 {s : State} (hok : Ok rCfg s) : Ok (sCfg 0) s :=
  ⟨fun k hk => hok.slotIn k (by simp only [sCfg, rCfg] at hk ⊢; omega), fun k hk => absurd hk (by simp [sCfg]),
    by have := hok.slots; simp only [sCfg, rCfg] at this ⊢; omega, fun k _ j hj => absurd hj (by simp [sCfg])⟩

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on `r7` and `r8`, with the round
key at `r9`. -/
theorem round_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      s'.gpr .r7 = s.gpr .r8 ∧
      s'.gpr .r8 = s.gpr .r7 ^^^ Spec.TripleDes.roundFunction (s.gpr .r8) (key48 s) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  have hsl := hok.slots
  simp only [rCfg] at hsl
  have hb10 : ∀ k ≤ 12, (s.gpr .r10).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by
    have := hok.slots; simp only [rCfg] at this; omega
  obtain ⟨s₁, h₁, hx, rd₁, wr₁, sp₁, k₁, f₁⟩ := inputs_ok hok
  have r10₁ : s₁.gpr .r10 = s.gpr .r10 := k₁ .r10 (by simp [kept])
  have hok₁ : Ok rCfg s₁ := hok.congr r10₁ (k₁ .r9 (by simp [kept])) rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, sp₂, k₂, f₂⟩ := sbox_ok (h := 0) (by decide) (rCfg_s0 hok₁)
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := (k₂ .r10 (by simp [kept])).trans r10₁
  -- The store of half 0's outputs.
  have w48 : InRegions s₂.wr (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) 4 := by
    rw [wr₂, r10₂, ← r10₁]; exact hok₁.slotIn 12 (by decide)
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) (s₂.gpr .r0) }
  have h₃ : runBlock isa [.str .r0 .r10 48] s₂ = some s₃ := by
    rw [runBlock_cons, exec_str (by decide) w48, runStep_some, runBlock_nil]
  have hok₃ : Ok (sCfg 1) s₃ :=
    ⟨fun k hk => by
      show InRegions s₂.wr _ 4
      rw [wr₂, show s₃.gpr (sCfg 1).base = s₁.gpr .r10 from r10₂.trans r10₁.symm]
      exact hok₁.slotIn k (by simp only [sCfg, rCfg] at hk ⊢; omega),
     fun k hk => absurd hk (by simp [sCfg]),
     by show (s₂.gpr .r10).toNat + 4 * 12 ≤ 2 ^ 32; rw [r10₂]; omega,
     fun k _ j hj => absurd hj (by simp [sCfg])⟩
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, sp₄, k₄, f₄⟩ := sbox_ok (h := 1) (by decide) hok₃
  have r10₄ : s₄.gpr .r10 = s.gpr .r10 := (k₄ .r10 (by simp [kept])).trans r10₂
  have hok₄ : Ok oCfg s₄ :=
    ⟨fun k hk => by
      rw [wr₄]; show InRegions s₂.wr _ 4
      rw [wr₂, show s₄.gpr oCfg.base = s₁.gpr .r10 from r10₄.trans r10₁.symm]
      exact hok₁.slotIn k (by simp only [oCfg, rCfg] at hk ⊢; omega),
     fun k hk => absurd hk (by simp [oCfg]),
     by show (s₄.gpr .r10).toNat + 4 * 13 ≤ 2 ^ 32; rw [r10₄]; omega,
     fun k _ j hj => absurd hj (by simp [oCfg])⟩
  obtain ⟨s₅, h₅, o7, o8, rd₅, wr₅, sp₅, k₅, f₅⟩ := output_ok hok₄
  -- The slots through the S-boxes.
  have slot₃ : ∀ k, 6 ≤ k → k < 12 → slotW s₃ k = slotW s₁ k := fun k hk₁ hk₂ => by
    show (s₂.mem.writeW _ _).readW (wordAddr (s₂.gpr .r10) k) 32 = _
    rw [Mem.readW_writeW_sep (by
        rw [r10₂]
        have := slot_word_sep (s.gpr .r10) (j := k) (k := 12) (by omega) (hb10 k (by omega)) (hb10 12 (by decide))
        rwa [wordAddr] at this) (by decide), r10₂, ← r10₁]
    have := slot_frame (n := 6) (k := k) (b := s₁.gpr .r10) f₂ hk₁ (by rw [r10₁]; exact hb10 k (by omega))
    exact this
  have slot12 : slotW s₄ 12 = s₂.gpr .r0 := by
    show s₄.mem.readW (wordAddr (s₄.gpr .r10) 12) 32 = _
    rw [r10₄, ← r10₂]
    have := slot_frame (n := 12) (k := 12) (b := s₃.gpr .r10) f₄ (by decide) (by rw [r10₂]; exact hb10 12 (by decide))
    rw [show s₃.gpr .r10 = s₂.gpr .r10 from rfl] at this
    rw [this]
    exact Mem.readW_writeW_self32 _ _ _
  have box₄ : ∀ p, boxIn 1 s₃ p = boxIn 1 s₁ p := fun p => by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [boxIn, boxIn, getLsbD_ofBits, getLsbD_ofBits, slot₃ (6 * 1 + t) (by omega) (by omega)]
  have r0₄ : s₄.gpr .r7 = s.gpr .r7 ∧ s₄.gpr .r8 = s.gpr .r8 := by
    refine ⟨?_, ?_⟩
    · rw [k₄ .r7 (by simp), show s₃.gpr .r7 = s₂.gpr .r7 from rfl, k₂ .r7 (by simp), k₁ .r7 (by simp)]
    · rw [k₄ .r8 (by simp), show s₃.gpr .r8 = s₂.gpr .r8 from rfl, k₂ .r8 (by simp), k₁ .r8 (by simp)]
  refine ⟨s₅, ?_, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [round, sboxes_eq, runBlock_append, runBlock_append, h₁, Option.bind_some, runBlock_append,
      runBlock_append, h₂, Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [o7 p hp, oG7]
    simp (config := {decide := true}) only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW,
      show (64 + p) / 32 = 2 by omega, show (64 + p) % 32 = p by omega, ite_true, ite_false]
    rw [r0₄.2]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := pSrc_lt j hj
    rw [o8 j hj, oG8, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    have hL : bitOf (oW s₄) (32 + j) = (s.gpr .r7).getLsbD j := by
      simp (config := {decide := true}) only [bitOf, oW, show (32 + j) / 32 = 1 by omega,
        show (32 + j) % 32 = j by omega, ite_true, ite_false]
      rw [r0₄.1]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb, hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 12.
      have hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      have ho := off_lt4 0 (by decide) _ hh b hb
      have hpos : sAtom (pSrc j) = 96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      have hbit : bitOf (oW s₄) (sAtom (pSrc j)) =
          (slotW s₄ 12).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, oW,
          show (96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b)) / 32 = 3 by omega,
          show (96 + (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b)) % 32 =
            6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b by omega, ite_false]
      rw [hbit, slot12, y₂ _ hh b hb, boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in `r0`.
      have hh8 : pSrc j / 4 < 8 := by omega
      have hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      have hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega
      have ho := off_lt4 1 (by decide) _ hm b hb
      have hpos : sAtom (pSrc j) = 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b := by
        rw [sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      have hbit : bitOf (oW s₄) (sAtom (pSrc j)) =
          (s₄.gpr .r0).getLsbD (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b < 32 by omega),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b < 32 by omega),
          ite_true]
      rw [hbit, y₄ _ hm b hb, box₄, boxIn_eq hx (by decide) hm ho, hi]
      simp only [hbe]
  · rw [rd₅, rd₄]; exact rd₂.trans rd₁
  · rw [wr₅, wr₄]; exact wr₂.trans wr₁
  · rw [sp₅, sp₄]; exact sp₂.trans sp₁
  · rw [k₅ r hr, k₄ r (by simp [hr]), show s₃.gpr r = s₂.gpr r from rfl, k₂ r (by simp [hr]),
      k₁ r (by simp [hr])]
  · have R : ∀ (c : Cfg) (t : State), c.base = .r10 → c.slots ≤ 13 → t.gpr .r10 = s.gpr .r10 →
        ∀ r ∈ [slotRegion c t], ∃ r' ∈ [slotRegion rCfg s], Region.Sub r r' := fun c t hc hn ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [slotRegion, hc, ht]
      exact Region.sub_prefix (by simp only [rCfg]; omega)
    have c12 : (slotRegion rCfg s).Contains (State.addr (s₂.gpr .r10 + BitVec.ofNat 32 48)) (32 / 8) := by
      rw [r10₂, show (48 : Nat) = 4 * 12 from rfl, ← wordAddr, wordAddr_eq _ (by omega)]
      exact Offset.contains_base _ (by simp only [rCfg]; omega) (by omega)
    have f₃ : Frame [slotRegion rCfg s] s₂.mem s₃.mem :=
      (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c12
    exact (((f₁.trans (f₂.sub (R _ _ rfl (by decide) r10₁))).trans f₃).trans
      (f₄.sub (R _ _ rfl (by decide) r10₂))).trans (f₅.sub (R _ _ rfl (by decide) r10₄))

end VG.Proof.CmacTripleDes.Arm
