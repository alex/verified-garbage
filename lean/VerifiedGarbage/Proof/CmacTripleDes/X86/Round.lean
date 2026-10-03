import VerifiedGarbage.Proof.CmacTripleDes.X86.RoundLit
import VerifiedGarbage.Proof.TripleDes.SboxTables
import VerifiedGarbage.Proof.CmacTripleDes.Des
import VerifiedGarbage.Proof.Framework.X86.Linear
import VerifiedGarbage.Proof.Framework.Bitslice.Rows
import VerifiedGarbage.Proof.Framework.Offset

/-!
# A DES round on x86 (32-bit)

Untrusted: everything here is checked by Lean.

As on 32-bit ARM (`Proof/CmacTripleDes/Arm/Round.lean`): the round's parts
are checked by evaluation (`Straight.check`), the broadcast inputs
(`inputs`) and the output (`output`) over the lane domain (`linear_ok`, all
their words in slots), and each half's S-boxes (`tree`) over the row domain
(`Bitslice.rows`), on all 64 values of a box's input at once. `round_ok`
composes them: slot `L` becomes `R`, and slot `R` becomes `L ⊕ f(R, K)`,
with `K` the round key's low word and the low 16 bits of its high word.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86

/-- The round's memory: slots 0–17 at `ebp`, and the round key's two words
at `esi`. -/
def rCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 2 }

/-- Slot `k` of the scratch buffer. -/
abbrev slotW (s : State) (k : Nat) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .ebp) k) 32

/-- The round key's words. -/
abbrev keyLo (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 0) 32
abbrev keyHi (s : State) : BitVec 32 := s.mem.readW (wordAddr (s.gpr .esi) 1) 32

/-- The round key: the low 16 bits of its high word, and its low word. -/
abbrev key48 (s : State) : BitVec 48 := (keyHi s).setWidth 16 ++ keyLo s

/-! ## The inputs -/

/-- Bit `b` of the round key, as an atom: of its low word (input word 1) or
its high word (input word 2). -/
def keyAtom (b : Nat) : Nat := if b < 32 then 32 + b else 64 + (b - 32)

/-- Bit `p` of input slot `t` (half `t / 6`, input bit `t % 6`): in lane `p / 6`,
below its fifth bit, `R`'s bit (atom `0 … 31`) XOR the key's. -/
def inG (t p : Nat) : List Nat :=
  if p < 24 ∧ p % 6 < 4 then
    [expSrc (24 * (t / 6) + 6 * (p / 6) + t % 6), keyAtom (24 * (t / 6) + 6 * (p / 6) + t % 6)]
  else []

/-- The slot of input `t`. -/
def inSlot (t : Nat) : Nat := 7 * (t / 6) + t % 6

/-- The inputs' slots, and `L` and `R` (input words 3 and 0) kept. -/
def inOuts : List (Nat × (Nat → List Nat)) :=
  (List.range 12).map (fun t => (inSlot t, inG t)) ++ [(slotL, fun p => [96 + p]), (slotR, fun p => [p])]

theorem inputs_check :
    check (lanes 32 7) rCfg (linExt 1) inputs (linEnv [(slotR, 0), (slotL, 3)]) (linPost rCfg.slots 7 inOuts) =
      true := by
  lit_decide

/-! ## The S-boxes -/

/-- Slot `t` on row `c`, at every position: bit `t % 7` of `c`. -/
def rowIn (t : Nat) : Nat := tableOf (fun a => (a / 32).testBit (t % 7)) 2048

/-- Half `h`'s input slots. -/
def sbEnv (h : Nat) : Env Nat :=
  { reg := fun _ => none, slot := fun t => if 7 * h ≤ t ∧ t < 7 * h + 6 then some (rowIn t) else none }

/-- At bit `6 j + off i b` (`i` the box in lane `j` of half `h`), output bit
`b` of box `i`, on every row. -/
def sbPost (h : Nat) (e : Env Nat) : Bool :=
  match e.reg .ebx with
  | some F => (List.range 4).all fun j => (List.range 4).all fun b => (List.range 64).all fun c =>
      F.testBit (32 * c + (6 * j + off (boxOf h j) b)) ==
        (Proof.TripleDes.outputTable (boxOf h j) b).testBit c
  | none => false

/-- The slots half `h` uses: the broadcast inputs up to its own, and its
spare slot. -/
def sCfg (h : Nat) : Cfg := { base := .ebp, slots := 7 * h + 7, ext := .esi, exts := 0 }

theorem sbox0_check : check (rows 32 6) (sCfg 0) (fun _ => none) (tree 0) (sbEnv 0) (sbPost 0) = true := by
  lit_decide

theorem sbox1_check : check (rows 32 6) (sCfg 1) (fun _ => none) (tree 1) (sbEnv 1) (sbPost 1) = true := by
  lit_decide

/-! ## The output -/

/-- The atom of output bit `u` of the S-boxes: bit `outPos u` of half 0's
outputs (slot 14, input word 0) or of half 1's (slot 15, input word 1). -/
def sAtom (u : Nat) : Nat := if outHalf u = 0 then outPos u else 32 + outPos u

/-- Slot `R`: bit `j` of `L` (input word 2) XOR the S-boxes' bit `pSrc j`. -/
def oGR (p : Nat) : List Nat := if p < 32 then [sAtom (pSrc p), 64 + p] else [64 + p]

/-- Slot `L` gets `R` (input word 3), slot `R` `L ⊕ P(S)`. -/
def oOuts : List (Nat × (Nat → List Nat)) := [(slotL, fun p => [96 + p]), (slotR, oGR)]

/-- The output's slots. -/
def oCfg : Cfg := { base := .ebp, slots := 18, ext := .esi, exts := 0 }

theorem output_check :
    check (lanes 32 7) oCfg (linExt 0) output (linEnv [(14, 0), (15, 1), (slotL, 2), (slotR, 3)])
      (linPost oCfg.slots 7 oOuts) = true := by
  lit_decide

/-! ## Machine facts -/

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
    wordAddr b k = b.setWidth 64 + BitVec.ofNat 64 (4 * k) := addr_eq h

/-- Word `k` of the slots is outside a frame on the first `n` words. -/
theorem slot_frame {m m' : Mem} {b : BitVec 32} {n k : Nat} (hf : Frame [⟨b.setWidth 64, 4 * n⟩] m m')
    (hk : n ≤ k) (hb : b.toNat + 4 * k + 4 ≤ 2 ^ 32) :
    m'.readW (wordAddr b k) 32 = m.readW (wordAddr b k) 32 := by
  rw [wordAddr_eq b (by omega)]
  refine hf.readW (r := ⟨b.setWidth 64 + BitVec.ofNat 64 (4 * k), 4⟩) (Region.contains_self _ _)
    (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint_base _ (by omega) (by omega)

/-- Words `j` and `k` of the slots are apart. -/
theorem slot_word_sep (b : BitVec 32) {j k : Nat} (h : j ≠ k) (hj : b.toNat + 4 * j + 4 ≤ 2 ^ 32)
    (hk : b.toNat + 4 * k + 4 ≤ 2 ^ 32) : Mem.Sep (wordAddr b j) (32 / 8) (wordAddr b k) (32 / 8) := by
  rw [wordAddr_eq b (by omega), wordAddr_eq b (by omega)]
  exact Offset.sep _ (by omega) (by omega) (by omega)

/-- `mov [b + o], r`, run. -/
theorem runBlock_store {s : State} {b r : Reg} {o : Nat} (hout : InRegions s.wr (addr (s.gpr b) o) 4) :
    runBlock isa [.store ⟨b, o⟩ r] s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) } := by
  rw [runBlock_cons, show exec (.store ⟨b, o⟩ r) s = some { s with mem := s.mem.writeW (addr (s.gpr b) o) (s.gpr r) }
    by simp [exec, State.store32, ea_mk, hout], runStep_some, runBlock_nil]

/-! ## The inputs, on the machine -/

/-- The inputs of `inputs`: `R`, the round key's words and `L`. -/
def inW (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then slotW s slotR else if i = 1 then keyLo s else if i = 2 then keyHi s else slotW s slotL

/-- The registers the round keeps. -/
def kept : List Reg := [.esp, .esi, .ebp]

theorem inputs_kept : kept.all (fun r => inputs.all fun i => i.dst != some r) = true := by lit_decide

theorem slot_bits {x y : BitVec 32} (h : ∀ p < 32, x.getLsbD p = y.getLsbD p) : x = y :=
  BitVec.eq_of_getLsbD_eq fun p hp => h p hp

theorem inputs_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa inputs s = some s' ∧
      (∀ t < 12, ∀ p < 32, (slotW s' (inSlot t)).getLsbD p = xorBits (inW s) (inG t p)) ∧
      slotW s' slotL = slotW s slotL ∧ slotW s' slotR = slotW s slotR ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok inputs_check hok (inW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
    (fun j hj => by
      simp only [rCfg] at hj
      rcases (by omega : j = 0 ∨ j = 1) with rfl | rfl
      · exact ⟨by decide, rfl⟩
      · exact ⟨by decide, rfl⟩)
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp inputs_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ inOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (inW s) (g p) := fun j g h p hp => by
    rw [slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', fun t ht p hp => bit _ _ (List.mem_append_left _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩))
    p hp, slot_bits fun p hp => ?_, slot_bits fun p hp => ?_, rd, wr, kp, fr⟩
  · rw [bit slotL _ (List.mem_append_right _ (List.mem_cons_self ..)) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, show (96 + p) / 32 = 3 by omega,
      show (96 + p) % 32 = p by omega]
    rfl
  · rw [bit slotR _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) p hp]
    simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, inW, Nat.div_eq_of_lt hp, Nat.mod_eq_of_lt hp]
    rfl

/-! ## The S-boxes, on the machine -/

theorem tree_kept (h : Nat) (hh : h < 2) : kept.all (fun r => (tree h).all fun i => i.dst != some r) = true := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> lit_decide

/-- The input of the box whose lane of half `h` holds bit `p`, from bit `p`
of the slots. -/
def boxIn (h : Nat) (s : State) (p : Nat) : BitVec 6 := ofBits 6 fun t => (slotW s (7 * h + t)).getLsbD p

theorem off_lt4 : ∀ h < 2, ∀ j < 4, ∀ b < 4, off (boxOf h j) b < 4 := by decide

theorem sbox_ok {h : Nat} (hh : h < 2) {s : State} (hok : Ok (sCfg h) s) :
    ∃ s', runBlock isa (tree h) s = some s' ∧
      (∀ j < 4, ∀ b < 4, (s'.gpr .ebx).getLsbD (6 * j + off (boxOf h j) b) =
        (Spec.TripleDes.sBox (boxOf h j) (boxIn h s (6 * j + off (boxOf h j) b))).getLsbD b) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion (sCfg h) s] s.mem s'.mem := by
  have hchk : check (rows 32 6) (sCfg h) (fun _ => none) (tree h) (sbEnv h) (sbPost h) = true := by
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · exact sbox0_check
    · exact sbox1_check
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ hchk
  obtain ⟨F, hF, hout⟩ : ∃ F, e'.reg .ebx = some F ∧ ∀ j < 4, ∀ b < 4, ∀ c < 64,
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
  have key : ∀ p < 32, ∃ s', runBlock isa (tree h) s = some s' ∧
      Post (RowRel p (boxIn h s p).toNat) (sCfg h) (fun _ => none) e' s s'
        (fun r => ((tree h).all fun i => i.dst != some r) = false) := by
    intro p hp
    refine run (rows_sound hp (boxIn h s p).isLt) hok
      ⟨fun r a h => by simp [sbEnv] at h, fun t a ht h' => ?_, fun _ _ _ h => by cases h⟩ he
    simp only [sbEnv] at h'
    split at h'
    · rename_i ht6
      cases h'
      show (rowIn t).testBit (32 * (boxIn h s p).toNat + p) = (slotW s t).getLsbD p
      have hc := (boxIn h s p).isLt
      obtain ⟨u, rfl, hu⟩ : ∃ u, t = 7 * h + u ∧ u < 6 := ⟨t - 7 * h, by omega, by omega⟩
      rw [rowIn, testBit_tableOf, decide_eq_true (by omega : 32 * (boxIn h s p).toNat + p < 2048),
        Bool.true_and, show (32 * (boxIn h s p).toNat + p) / 32 = (boxIn h s p).toNat by omega,
        BitVec.testBit_toNat, boxIn, getLsbD_ofBits, show (7 * h + u) % 7 = u by omega,
        decide_eq_true hu, Bool.true_and]
    · cases h'
  obtain ⟨s', hs', p₀⟩ := key 0 (by omega)
  refine ⟨s', hs', fun j hj b hb => ?_, p₀.rd, p₀.wr,
    fun r hr => p₀.other r (by simp [List.all_eq_true.mp (tree_kept h hh) r hr]), p₀.frame⟩
  have hp : 6 * j + off (boxOf h j) b < 32 := by have := off_lt4 h hh j hj b hb; omega
  obtain ⟨s'', hs'', p₁⟩ := key _ hp
  obtain rfl := run_unique hs'' hs'
  have h' := p₁.rel.reg .ebx F hF
  simp only [RowRel] at h'
  rw [← h', hout j hj b hb _ (boxIn h s _).isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## The output, on the machine -/

/-- The inputs of `output`: the halves' outputs, `L` and `R`. -/
def oW (s : State) (i : Nat) : BitVec 32 :=
  if i = 0 then slotW s 14 else if i = 1 then slotW s 15 else if i = 2 then slotW s slotL else slotW s slotR

theorem output_kept : kept.all (fun r => output.all fun i => i.dst != some r) = true := by lit_decide

theorem output_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa output s = some s' ∧
      slotW s' slotL = slotW s slotR ∧
      (∀ p < 32, (slotW s' slotR).getLsbD p = xorBits (oW s) (oGR p)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  obtain ⟨s', hs', hout, rd, wr, keep, fr⟩ := linear_ok output_check hok (oW s)
    (fun j i h hj => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => keep _ (List.all_eq_true.mp output_kept r hr)
  have e10 : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ oOuts → ∀ p < 32, (slotW s' j).getLsbD p = xorBits (oW s) (g p) := fun j g h p hp => by
    rw [slotW, e10]; exact hout j g h p hp
  refine ⟨s', hs', slot_bits fun p hp => ?_, fun p hp => bit _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)) p hp,
    rd, wr, kp, fr⟩
  rw [bit slotL _ (List.mem_cons_self ..) p hp]
  simp only [xorBits_cons, xorBits_nil, Bool.xor_false, bitOf, oW, show (96 + p) / 32 = 3 by omega,
    show (96 + p) % 32 = p by omega]
  rfl

/-! ## The round -/

theorem expSrc_lt : ∀ q < 48, expSrc q < 32 := by lit_decide

theorem pSrc_lt : ∀ j < 32, pSrc j < 32 := by lit_decide

/-- The box inputs that `inputs` broadcasts. -/
theorem boxIn_eq {s s₁ : State}
    (hx : ∀ t < 12, ∀ p < 32, (slotW s₁ (inSlot t)).getLsbD p = xorBits (inW s) (inG t p))
    {h j o : Nat} (hh : h < 2) (hj : j < 4) (ho : o < 4) :
    boxIn h s₁ (6 * j + o) = chunk (slotW s slotR) (key48 s) (boxOf h j) := by
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  have hb : 6 * (7 - boxOf h j) = 24 * h + 6 * j := by simp only [boxOf]; omega
  have hE := expSrc_lt (24 * h + 6 * j + t) (by omega)
  have hs : 7 * h + t = inSlot (6 * h + t) := by simp only [inSlot]; omega
  rw [boxIn, getLsbD_ofBits, decide_eq_true ht, Bool.true_and, hs, hx (6 * h + t) (by omega) _ (by omega),
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

/-- The slots of a configuration on fewer slots, with no external words. -/
theorem ok_fewer {c c' : Cfg} {s : State} (h : Ok c s) (hb : c'.base = c.base) (hn : c'.slots ≤ c.slots)
    (he : c'.exts = 0) : Ok c' s :=
  ⟨fun k hk => by rw [hb]; exact h.slotIn k (by omega), fun k hk => absurd hk (by omega),
    by rw [hb]; have := h.fit; omega, fun k _ j hj => absurd hj (by omega)⟩

/-- One round: `(L, R) := (R, L ⊕ f(R, K))` on slots `L` and `R`, with the
round key at `esi`. -/
theorem round_ok {s : State} (hok : Ok rCfg s) :
    ∃ s', runBlock isa round s = some s' ∧
      slotW s' slotL = slotW s slotR ∧
      slotW s' slotR = slotW s slotL ^^^ Spec.TripleDes.roundFunction (slotW s slotR) (key48 s) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion rCfg s] s.mem s'.mem := by
  have hfit := hok.fit
  simp only [rCfg] at hfit
  have hb : ∀ k ≤ 17, (s.gpr .ebp).toNat + 4 * k + 4 ≤ 2 ^ 32 := fun k hk => by omega
  obtain ⟨s₁, h₁, hx, L₁, R₁, rd₁, wr₁, k₁, f₁⟩ := inputs_ok hok
  have e₁ : s₁.gpr .ebp = s.gpr .ebp := k₁ _ (by simp [kept])
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  have hok₁ : Ok rCfg s₁ := hok.congr e₁ i₁ rd₁ wr₁
  obtain ⟨s₂, h₂, y₂, rd₂, wr₂, k₂, f₂⟩ := sbox_ok (h := 0) (by decide) (ok_fewer hok₁ rfl (by decide) rfl)
  have e₂ : s₂.gpr .ebp = s.gpr .ebp := (k₂ _ (by simp [kept])).trans e₁
  -- Half 0's outputs to slot 14.
  have w14 : InRegions s₂.wr (addr (s₂.gpr .ebp) (4 * 14)) 4 := by
    rw [wr₂, e₂, ← e₁]; exact hok₁.slotIn 14 (by decide)
  let s₃ : State := { s₂ with mem := s₂.mem.writeW (addr (s₂.gpr .ebp) (4 * 14)) (s₂.gpr .ebx) }
  have h₃ : runBlock isa [.store (at_ .ebp (4 * 14)) .ebx] s₂ = some s₃ := runBlock_store w14
  have e₃ : s₃.gpr .ebp = s.gpr .ebp := e₂
  obtain ⟨s₄, h₄, y₄, rd₄, wr₄, k₄, f₄⟩ := sbox_ok (h := 1) (by decide)
    (ok_fewer (hok₁.congr (e₃.trans e₁.symm) (show s₃.gpr .esi = s₁.gpr .esi from k₂ .esi (by simp [kept]))
      (rd₂ : s₃.rd = s₁.rd) (wr₂ : s₃.wr = s₁.wr)) rfl (by decide) rfl)
  have e₄ : s₄.gpr .ebp = s.gpr .ebp := (k₄ _ (by simp [kept])).trans e₃
  have w15 : InRegions s₄.wr (addr (s₄.gpr .ebp) (4 * 15)) 4 := by
    rw [wr₄, show s₃.wr = s₁.wr from wr₂, e₄, ← e₁]; exact hok₁.slotIn 15 (by decide)
  let s₅ : State := { s₄ with mem := s₄.mem.writeW (addr (s₄.gpr .ebp) (4 * 15)) (s₄.gpr .ebx) }
  have h₅ : runBlock isa [.store (at_ .ebp (4 * 15)) .ebx] s₄ = some s₅ := runBlock_store w15
  have e₅ : s₅.gpr .ebp = s.gpr .ebp := e₄
  have rd₅ : s₅.rd = s₁.rd := rd₄.trans rd₂
  have wr₅ : s₅.wr = s₁.wr := wr₄.trans wr₂
  obtain ⟨s₆, h₆, L₆, R₆, rd₆, wr₆, k₆, f₆⟩ := output_ok
    (ok_fewer (hok₁.congr (e₅.trans e₁.symm) (show s₅.gpr .esi = s₁.gpr .esi from
      (k₄ .esi (by simp [kept])).trans (k₂ .esi (by simp [kept]))) rd₅ wr₅) rfl (by decide) rfl)
  -- The slots along the way.
  have sep : ∀ j k, j ≠ k → j ≤ 17 → k ≤ 17 →
      Mem.Sep (wordAddr (s.gpr .ebp) j) (32 / 8) (wordAddr (s.gpr .ebp) k) (32 / 8) :=
    fun j k h hj hk => slot_word_sep _ h (hb j hj) (hb k hk)
  have st₃ : ∀ k, k ≠ 14 → k ≤ 17 → slotW s₃ k = slotW s₂ k := fun k hk hk' => by
    show (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) (s₂.gpr .ebx)).readW (wordAddr (s₂.gpr .ebp) k) 32 =
      s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32
    rw [e₂, Mem.readW_writeW_sep (sep k 14 hk hk' (by decide)) (by decide)]
  have st₅ : ∀ k, k ≠ 15 → k ≤ 17 → slotW s₅ k = slotW s₄ k := fun k hk hk' => by
    show (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) (s₄.gpr .ebx)).readW (wordAddr (s₄.gpr .ebp) k) 32 =
      s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32
    rw [e₄, Mem.readW_writeW_sep (sep k 15 hk hk' (by decide)) (by decide)]
  have fr₂ : ∀ k, 7 ≤ k → k ≤ 17 → slotW s₂ k = slotW s₁ k := fun k h₁' h₂' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [e₂, ← e₁]
    exact slot_frame (n := 7) f₂ h₁' (by rw [e₁]; exact hb k h₂')
  have fr₄ : ∀ k, 14 ≤ k → k ≤ 17 → slotW s₄ k = slotW s₃ k := fun k h₁' h₂' => by
    show s₄.mem.readW (wordAddr (s₄.gpr .ebp) k) 32 = s₃.mem.readW (wordAddr (s₃.gpr .ebp) k) 32
    rw [e₄, ← e₃]
    exact slot_frame (n := 14) f₄ h₁' (by rw [e₃]; exact hb k h₂')
  have slotLR : ∀ k, 16 ≤ k → k ≤ 17 → slotW s₅ k = slotW s k := fun k h₁' h₂' => by
    rw [st₅ k (by omega) h₂', fr₄ k (by omega) h₂', st₃ k (by omega) h₂', fr₂ k (by omega) h₂']
    rcases (by omega : k = 16 ∨ k = 17) with rfl | rfl
    · exact L₁
    · exact R₁
  have slot14 : slotW s₅ 14 = s₂.gpr .ebx := by
    rw [st₅ 14 (by decide) (by decide), fr₄ 14 (by decide) (by decide)]
    exact Mem.readW_writeW_self32 _ _ _
  have slot15 : slotW s₅ 15 = s₄.gpr .ebx := Mem.readW_writeW_self32 _ _ _
  have box₄ : ∀ p, boxIn 1 s₃ p = boxIn 1 s₁ p := fun p => by
    apply BitVec.eq_of_getLsbD_eq
    intro t ht
    rw [boxIn, boxIn, getLsbD_ofBits, getLsbD_ofBits]
    by_cases ht6 : t < 6
    · rw [st₃ (7 * 1 + t) (by omega) (by omega), fr₂ (7 * 1 + t) (by omega) (by omega)]
    · simp [ht6]
  refine ⟨s₆, ?_, ?_, ?_, ?_, ?_, fun r hr => ?_, ?_⟩
  · rw [round, runBlock_append, runBlock_append, h₁, Option.bind_some, sboxes, runBlock_append, runBlock_append,
      runBlock_append, h₂, Option.bind_some, h₃, Option.bind_some, h₄, Option.bind_some, h₅, Option.bind_some, h₆]
  · rw [L₆, slotLR slotR (by decide) (by decide)]
  · apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have hu := pSrc_lt j hj
    rw [R₆ j hj, oGR, ite_eq_left hj, BitVec.getLsbD_xor, getLsbD_roundFunction _ _ hj, xorBits_cons,
      xorBits_cons, xorBits_nil, Bool.xor_false]
    have hL : bitOf (oW s₅) (64 + j) = (slotW s slotL).getLsbD j := by
      simp (config := {decide := true}) only [bitOf, oW, show (64 + j) / 32 = 2 by omega,
        show (64 + j) % 32 = j by omega, ite_true, ite_false]
      rw [slotLR slotL (by decide) (by decide)]
    rw [hL, Bool.xor_comm]
    congr 1
    obtain ⟨b, hb', hbe⟩ : ∃ b, b < 4 ∧ pSrc j % 4 = b := ⟨_, Nat.mod_lt _ (by decide), rfl⟩
    by_cases hh : pSrc j / 4 < 4
    · -- Half 0, in slot 14.
      have hi : boxOf 0 (pSrc j / 4) = 7 - pSrc j / 4 := by simp [boxOf]
      have ho := off_lt4 0 (by decide) _ hh b hb'
      have hpos : sAtom (pSrc j) = 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b := by
        rw [sAtom, outHalf, ite_eq_left hh, ite_eq_left rfl, outPos, hi, Nat.mod_eq_of_lt hh, hbe]
      have hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
          (slotW s₅ 14).getLsbD (6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, oW,
          Nat.div_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega),
          Nat.mod_eq_of_lt (show 6 * (pSrc j / 4) + off (boxOf 0 (pSrc j / 4)) b < 32 by omega), ite_true]
      rw [hbit, slot14, y₂ _ hh b hb', boxIn_eq hx (by decide) hh ho, hi]
      simp only [hbe]
    · -- Half 1, in slot 15.
      have hm : pSrc j / 4 % 4 < 4 := Nat.mod_lt _ (by decide)
      have hi : boxOf 1 (pSrc j / 4 % 4) = 7 - pSrc j / 4 := by simp only [boxOf]; omega
      have ho := off_lt4 1 (by decide) _ hm b hb'
      have hpos : sAtom (pSrc j) = 32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [sAtom, outHalf, ite_eq_right hh, ite_eq_right (by decide), outPos, hi, hbe]
      have hbit : bitOf (oW s₅) (sAtom (pSrc j)) =
          (slotW s₅ 15).getLsbD (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b) := by
        rw [hpos]
        simp (config := {decide := true}) only [bitOf, oW,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) / 32 = 1 by omega,
          show (32 + (6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b)) % 32 =
            6 * (pSrc j / 4 % 4) + off (boxOf 1 (pSrc j / 4 % 4)) b by omega, ite_true, ite_false]
      rw [hbit, slot15, y₄ _ hm b hb', box₄, boxIn_eq hx (by decide) hm ho, hi]
      simp only [hbe]
  · rw [rd₆, rd₅]; exact rd₁
  · rw [wr₆, wr₅]; exact wr₁
  · rw [k₆ r hr, show s₅.gpr r = s₄.gpr r from rfl, k₄ r hr, show s₃.gpr r = s₂.gpr r from rfl, k₂ r hr, k₁ r hr]
  · have R : ∀ (c : Cfg) (t : State), c.base = .ebp → c.slots ≤ 18 → t.gpr .ebp = s.gpr .ebp →
        ∀ r ∈ [slotRegion c t], ∃ r' ∈ [slotRegion rCfg s], Region.Sub r r' := fun c t hc hn ht r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      simp only [slotRegion, hc, ht]
      exact Region.sub_prefix (by simp only [rCfg]; omega)
    have cw : ∀ k ≤ 17, (slotRegion rCfg s).Contains (wordAddr (s.gpr .ebp) k) (32 / 8) := fun k hk => by
      rw [wordAddr_eq _ (by omega)]
      exact Offset.contains_base _ (by simp only [rCfg]; omega) (by omega)
    have f₃ : Frame [slotRegion rCfg s] s₂.mem s₃.mem := by
      show Frame _ s₂.mem (s₂.mem.writeW (wordAddr (s₂.gpr .ebp) 14) _)
      rw [e₂]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 14 (by decide))
    have f₅ : Frame [slotRegion rCfg s] s₄.mem s₅.mem := by
      show Frame _ s₄.mem (s₄.mem.writeW (wordAddr (s₄.gpr .ebp) 15) _)
      rw [e₄]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (cw 15 (by decide))
    exact ((((f₁.trans (f₂.sub (R _ _ rfl (by decide) e₁))).trans f₃).trans
      (f₄.sub (R _ _ rfl (by decide) e₃))).trans f₅).trans (f₆.sub (R _ _ rfl (by decide) e₅))

end VG.Proof.CmacTripleDes.X86
