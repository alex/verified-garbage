import VerifiedGarbage.Impl.CmacTripleDes.X86_64.Round
import VerifiedGarbage.Proof.CmacTripleDes.Des
import VerifiedGarbage.Proof.Framework.X86_64.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows

/-!
# A DES round on x86-64

The round's three parts are checked by evaluation (`Straight.check`): the
broadcast inputs (`inputs`) and the output (`output`), which only move,
mask and XOR bits, over the lane domain; the S-boxes (`sboxes`), which
combine words bitwise with constants that differ by position, over the row
domain (`Bitslice.rows`), on all 64 values of a box's input at once.
`round_ok` composes them: `R` and `L ⊕ f(R, K)`.
-/

namespace VG.Proof.CmacTripleDes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86_64

/-- The round's memory: the broadcast inputs in slots 0–5 at `r15`, and the
round key at `r14`. -/
def rCfg : Cfg := { base := .r15, slots := 6, ext := .r14, exts := 1 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r15) k) 64

/-- The round key's word. -/
abbrev keyW (s : State) : BitVec 64 := s.mem.readW (wordAddr (s.gpr .r14) 0) 64

/-! ## The inputs -/

/-- Bit `p` of slot `t`: in lane `p / 6`, below its fifth bit, bit `t` of
the box's input, `R`'s bit (atom `0 … 63`) XOR the key's (atom `64 …`). -/
def inG (t p : Nat) : List Nat :=
  if p < 48 ∧ p % 6 < 4 then [expSrc (6 * (p / 6) + t), 64 + 6 * (p / 6) + t] else []

def inPost (e : Env (Nat × Nat)) : Bool :=
  (List.range 6).all fun t => e.slot t == some (outWord (inG t))

theorem inputs_check :
    check (lanes 64 7) rCfg (linExt 1) inputs (linEnv [(.r13, 0)]) inPost = true := by
  decide +kernel

theorem inG_lt : ∀ t < 6, ∀ p < 64, ∀ a ∈ inG t p, a < 2 ^ 7 := by decide

/-- The registers the round keeps. -/
def kept : List Reg := [.rbx, .rbp, .rsp, .r10, .r11, .r14, .r15]

theorem inputs_kept :
    (.r12 :: .r13 :: kept).all (fun r => inputs.all fun i => i.dst != some r) = true := by
  decide +kernel

/-- The inputs of `inputs`: `R` and the round key. -/
def inW (s : State) (i : Nat) : BitVec 64 := if i = 0 then s.gpr .r13 else keyW s

theorem inputs_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 6, ∀ p < 64, (slotW s' t).getLsbD p = xorBits (inW s) (inG t p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ inputs_check
  have hrel : Rel (LaneRel 7 (assign (inW s) (2 ^ 7))) rCfg (linExt 1) (linEnv [(.r13, 0)]) s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), fun j a hj h => ?_⟩
    · simp only [linEnv, List.find?, Option.map_eq_some_iff] at h
      split at h
      · rename_i hr
        simp only [beq_iff_eq] at hr; subst hr
        simp only [Option.some.injEq, exists_eq_left'] at h; subst h
        exact inWord_rel (inW s) (i := 0) (by decide)
      · simp at h
    · simp only [rCfg] at hj
      obtain rfl : j = 0 := by omega
      simp only [linExt, Option.some.injEq] at h; subst h
      exact inWord_rel (inW s) (i := 1) (by decide)
  obtain ⟨s', hs', p⟩ := run lanes_sound hok hrel he
  refine ⟨s', hs', fun t ht q hq => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have h := List.all_eq_true.mp hpost t (List.mem_range.mpr ht)
    simp only [beq_iff_eq] at h
    exact outWord_rel (inG_lt t ht) (p.rel.slot t _ (by simp only [rCfg]; omega) h) q hq
  · rw [List.all_eq_true.mp inputs_kept r hr]; decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 64).testBit t) 4096

def sbEnv : Env Nat := { reg := fun _ => none, slot := fun t => if t < 6 then some (rowIn t) else none }

/-- At bit `6 (7 - i) + off i b`, output bit `b` of box `i`, on every row. -/
def sbPost (e : Env Nat) : Bool :=
  match e.reg .rax with
  | some F => (List.range 8).all fun i => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (64 * c + (6 * (7 - i) + off i b)) == (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD b
  | none => false

theorem sboxes_check : check (rows 64 6) rCfg (fun _ => none) sboxes sbEnv sbPost = true := by
  decide +kernel

theorem sboxes_kept :
    (.r12 :: .r13 :: kept).all (fun r => sboxes.all fun i => i.dst != some r) = true := by
  decide +kernel

/-- The input of the box whose lane holds bit `p`, from bit `p` of the slots. -/
def boxIn (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (slotW s t).getLsbD p

theorem sboxes_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa sboxes s = some s' ∧
      (∀ i < 8, ∀ b < 4, (s'.gpr .rax).getLsbD (6 * (7 - i) + off i b) =
        (Spec.TripleDes.sBox i (boxIn s (6 * (7 - i) + off i b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ .r12 :: .r13 :: kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ sboxes_check
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .rax = some F ∧ ∀ i < 8, ∀ b < 4, ∀ c < 64,
      F.testBit (64 * c + (6 * (7 - i) + off i b)) = (Spec.TripleDes.sBox i (BitVec.ofNat 6 c)).getLsbD b := by
    simp only [sbPost] at hpost
    split at hpost
    · rename_i F hF
      refine ⟨F, hF, fun i hi b hb c hc => ?_⟩
      have := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hpost i
        (List.mem_range.mpr hi)) b (List.mem_range.mpr hb)) c (List.mem_range.mpr hc)
      simpa using this
    · cases hpost
  have key : ∀ p < 64, ∃ s', runBlock isa sboxes s = some s' ∧
      Post (RowRel p (boxIn s p).toNat) rCfg (fun _ => none) e' s s'
        (fun r => (sboxes.all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (boxIn s p).isLt) hok
      ⟨fun r a h => by simp [sbEnv] at h, fun t a ht h => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [sbEnv] at h
    split at h
    · rename_i ht6
      cases h
      show (rowIn t).testBit (64 * (boxIn s p).toNat + p) = (slotW s t).getLsbD p
      have hc := (boxIn s p).isLt
      rw [rowIn, testBit_tableOf, decide_eq_true (by omega : 64 * (boxIn s p).toNat + p < 4096),
        Bool.true_and, show (64 * (boxIn s p).toNat + p) / 64 = (boxIn s p).toNat by omega,
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, decide_eq_true ht6, Bool.true_and]
    · cases h
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun i hi b hb => ?_, p₀.rd, p₀.wr, fun r hr => p₀.other r ?_, p₀.frame⟩
  · have hp : 6 * (7 - i) + off i b < 64 := by revert i b; decide
    obtain ⟨s'', hs'', p₁⟩ := key _ hp
    obtain rfl := run_unique hs'' hs'
    have h := p₁.rel.reg .rax F hF
    simp only [RowRel] at h
    rw [← h, hout i hi b hb _ (boxIn s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [List.all_eq_true.mp sboxes_kept r hr]; decide

/-! ## The output -/

/-- No memory. -/
def oCfg : Cfg := { base := .r15, slots := 0, ext := .r14, exts := 0 }

/-- `r12`: `R` (input word 2). -/
def oG12 (p : Nat) : List Nat := [128 + p]

/-- `r13`: bit `j` of `L` (input word 1) XOR, for `j < 32`, the S-boxes' bit
`pSrc j` (in `rax`, input word 0). -/
def oG13 (p : Nat) : List Nat := if p < 32 then [outPos (pSrc p), 64 + p] else [64 + p]

def oIns : List (Reg × Nat) := [(.rax, 0), (.r12, 1), (.r13, 2)]

theorem output_check :
    check (lanes 64 8) oCfg (linExt 3) output (linEnv oIns) (linPost 8 [(.r12, oG12), (.r13, oG13)]) = true := by
  decide +kernel

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by
  decide +kernel

/-- The inputs of `output`. -/
def oW (s : State) (i : Nat) : BitVec 64 :=
  if i = 0 then s.gpr .rax else if i = 1 then s.gpr .r12 else s.gpr .r13

theorem oCfg_ok (s : State) : Ok oCfg s :=
  ⟨fun k hk => absurd hk (by simp [oCfg]), fun k hk => absurd hk (by simp [oCfg]), by decide,
    fun k hk => absurd hk (by simp [oCfg])⟩

theorem output_ok (s : State) :
    ∃ s', runBlock isa output s = some s' ∧
      (∀ p < 64, (s'.gpr .r12).getLsbD p = xorBits (oW s) (oG12 p)) ∧
      (∀ p < 64, (s'.gpr .r13).getLsbD p = xorBits (oW s) (oG13 p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧ s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok output_check (oCfg_ok s) (oW s)
    (fun r i hri => by
      simp only [oIns, List.mem_cons, List.mem_nil_iff, Prod.mk.injEq, or_false] at hri
      rcases hri with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  refine ⟨s', hs', hout .r12 oG12 (by simp), hout .r13 oG13 (by simp), hrd, hwr,
    fun r hr => hoth r (List.all_eq_true.mp output_kept r hr), ?_⟩
  funext a
  exact hfr a fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; simp [slotRegion, oCfg, Region.Contains]

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

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : State}
    (h : ∀ t < 6, ∀ p < 64, (slotW s₁ t).getLsbD p = xorBits (inW s) (inG t p))
    {i o : Nat} (hi : i < 8) (ho : o < 4) :
    boxIn s₁ (6 * (7 - i) + o) = chunk ((s.gpr .r13).setWidth 32) ((keyW s).setWidth 48) i := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hE := expSrc_lt (6 * (7 - i) + t) (by omega)
  rw [boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, h t ht _ (by omega),
    getLsbD_chunk _ _ hi ht, inG, ite_eq_left (by omega), show (6 * (7 - i) + o) / 6 = 7 - i by omega]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, BitVec.getLsbD_setWidth,
    Nat.div_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega),
    Nat.mod_eq_of_lt (show expSrc (6 * (7 - i) + t) < 64 by omega),
    show (64 + 6 * (7 - i) + t) / 64 = 1 by omega, show (64 + 6 * (7 - i) + t) % 64 = 6 * (7 - i) + t by omega,
    hE, show 6 * (7 - i) + t < 48 by omega, decide_true, Bool.true_and, ite_true]
  rfl

theorem off_lt : ∀ i < 8, ∀ b < 4, off i b < 4 := by decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by decide

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on the low 32 bits of `r12` and
`r13`, with the round key the low 48 bits of `[r14]`. -/
theorem round_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      s'.gpr .r12 = s.gpr .r13 ∧
      (s'.gpr .r13).setWidth 32 = (s.gpr .r12).setWidth 32 ^^^
        Spec.TripleDes.roundFunction ((s.gpr .r13).setWidth 32) ((keyW s).setWidth 48) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨s₁, h₁, hx, rd₁, wr₁, k₁, f₁⟩ := inputs_ok hok
  have hok₁ : Ok rCfg s₁ := hok.congr (k₁ .r15 (by simp [kept])) (k₁ .r14 (by simp [kept])) rd₁ wr₁
  obtain ⟨s₂, h₂, hy, rd₂, wr₂, k₂, f₂⟩ := sboxes_ok hok₁
  obtain ⟨s₃, h₃, o12, o13, rd₃, wr₃, k₃, m₃⟩ := output_ok s₂
  have r12₂ : s₂.gpr .r12 = s.gpr .r12 := (k₂ .r12 (by simp)).trans (k₁ .r12 (by simp))
  have r13₂ : s₂.gpr .r13 = s.gpr .r13 := (k₂ .r13 (by simp)).trans (k₁ .r13 (by simp))
  refine ⟨s₃, ?_, ?_, ?_, rd₃.trans (rd₂.trans rd₁), wr₃.trans (wr₂.trans wr₁),
    fun r hr => (k₃ r hr).trans ((k₂ r (by simp [hr])).trans (k₁ r (by simp [hr]))), ?_⟩
  · rw [round, runBlock_append, runBlock_append, h₁, Option.bind_some, h₂, Option.bind_some, h₃]
  · apply BitVec.eq_of_getLsbD_eq
    intro p hp
    rw [o12 p hp, oG12]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW,
      show (128 + p) / 64 = 2 by omega, show (128 + p) % 64 = p by omega]
    rw [ite_eq_right (by decide), ite_eq_right (by decide), r13₂]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := pSrc_lt j hj
    have hi : 7 - pSrc j / 4 < 8 := by omega
    have hb : pSrc j % 4 < 4 := by omega
    have ho := off_lt _ hi _ hb
    have hpos : outPos (pSrc j) = 6 * (7 - (7 - pSrc j / 4)) + off (7 - pSrc j / 4) (pSrc j % 4) := by
      rw [outPos, show 7 - (7 - pSrc j / 4) = pSrc j / 4 by omega]
    rw [BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and, o13 j (by omega), oG13, ite_eq_left hj,
      BitVec.getLsbD_xor, BitVec.getLsbD_setWidth, decide_eq_true hj, Bool.true_and,
      getLsbD_roundFunction _ _ hj]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW]
    rw [Nat.div_eq_of_lt (show outPos (pSrc j) < 64 by omega), Nat.mod_eq_of_lt (show outPos (pSrc j) < 64 by omega),
      show (64 + j) / 64 = 1 by omega, show (64 + j) % 64 = j by omega, ite_eq_left rfl, ite_eq_right (by decide),
      ite_eq_left rfl, r12₂, hpos, hy _ hi _ hb, boxIn_eq hx hi ho, Bool.xor_comm]
  · have hr : slotRegion rCfg s₁ = slotRegion rCfg s := by
      simp only [slotRegion]; rw [show rCfg.base = .r15 from rfl, k₁ .r15 (by simp [kept])]
    rw [hr] at f₂
    rw [m₃]; exact f₁.trans f₂

end VG.Proof.CmacTripleDes.X86_64
