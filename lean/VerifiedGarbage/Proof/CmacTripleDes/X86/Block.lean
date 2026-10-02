import VerifiedGarbage.Proof.CmacTripleDes.X86.Round
import VerifiedGarbage.Proof.CmacTripleDes.Block
import VerifiedGarbage.Proof.CmacTripleDes.Words
import VerifiedGarbage.Proof.Framework.X86.Wp

/-!
# TDEA on x86 (32-bit): the passes and the block

Untrusted: everything here is checked by Lean.

As on 32-bit ARM (`Proof/CmacTripleDes/Arm/Block.lean`): `block` encrypts the
64-bit block in `eax:edx` with the key schedule at `esi` (`block_ok`): `IP`
into slots `L` and `R`, three passes of sixteen rounds (`pass_ok`, the round
keys a step apart, the halves exchanged after each pass), and `IP⁻¹`. During
the block, `esi` points to slot `kpos p j` of the key schedule before round
`j` of pass `p`, and slots 18–20 of the scratch buffer at `ebp` hold the
counters and the step. The block changes only its words of the scratch
buffer (bytes `[0, 84)`) and the registers but `esp` and `ebp`.
-/

namespace VG.Proof.CmacTripleDes.X86

open VG VG.X86 VG.X86.Straight VG.X86.Wp VG.Bitslice VG.Impl.CmacTripleDes VG.Impl.CmacTripleDes.X86
  VG.Proof.CmacTripleDes

/-- What the block needs: the key schedule at `esi` readable, and the words
0–20 of the scratch buffer at `ebp` writable, apart from it. -/
structure BlockPre (s : State) : Prop where
  sched : ∃ len, (⟨(s.gpr .esi).setWidth 64, len⟩ : Region) ∈ s.rd ++ s.wr ∧ 384 ≤ len ∧
    (s.gpr .esi).toNat + len ≤ 2 ^ 32
  scr : ∃ len, (⟨(s.gpr .ebp).setWidth 64, len⟩ : Region) ∈ s.wr ∧ 84 ≤ len ∧
    (s.gpr .ebp).toNat + len ≤ 2 ^ 32
  disj : Region.Disjoint ⟨(s.gpr .ebp).setWidth 64, 84⟩ ⟨(s.gpr .esi).setWidth 64, 384⟩

/-- The block's words of the scratch buffer. -/
abbrev xR (s₀ : State) : Region := ⟨(s₀.gpr .ebp).setWidth 64, 84⟩

/-- What the block keeps. -/
structure Same (s₀ s : State) : Prop where
  ebp : s.gpr .ebp = s₀.gpr .ebp
  esp : s.gpr .esp = s₀.gpr .esp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [xR s₀] s₀.mem s.mem

/-- The key schedule. -/
abbrev sch (s₀ : State) : Spec.TripleDes.Schedule := Spec.TripleDes.scheduleAt s₀.mem ((s₀.gpr .esi).setWidth 64)

/-- Word `k` at offset `off` of a region that does not wrap around. -/
theorem in_word {rs : List Region} {b : BitVec 32} {len off k : Nat}
    (hr : (⟨b.setWidth 64, len⟩ : Region) ∈ rs) (hfit : b.toNat + len ≤ 2 ^ 32) (h : off + 4 * k + 4 ≤ len) :
    InRegions rs (wordAddr (b + BitVec.ofNat 32 off) k) 4 :=
  ⟨_, hr, contains_word rfl hfit h (Nat.le_refl _)⟩

theorem add_zero32 (b : BitVec 32) : b + BitVec.ofNat 32 0 = b := BitVec.add_zero b

/-- Word `k` of a region at `b` that does not wrap around. -/
theorem contains_w {b : BitVec 32} {len k : Nat} (hfit : b.toNat + len ≤ 2 ^ 32) (h : 4 * k + 4 ≤ len) :
    (⟨b.setWidth 64, len⟩ : Region).Contains (wordAddr b k) 4 := by
  have := contains_word (r := ⟨b.setWidth 64, len⟩) (b := b) (off := 0) (k := k) (n := len) rfl hfit (by omega)
    (Nat.le_refl _)
  rwa [add_zero32] at this

theorem contains_w_off {b : BitVec 32} {len off k : Nat} (hfit : b.toNat + len ≤ 2 ^ 32)
    (h : off + 4 * k + 4 ≤ len) :
    (⟨b.setWidth 64, len⟩ : Region).Contains (wordAddr (b + BitVec.ofNat 32 off) k) 4 :=
  contains_word rfl hfit h (Nat.le_refl _)

theorem wordAddr_off (b : BitVec 32) {off k : Nat} (h : b.toNat + off + 4 * k < 2 ^ 32) :
    wordAddr (b + BitVec.ofNat 32 off) k = b.setWidth 64 + BitVec.ofNat 64 (off + 4 * k) := by
  rw [wordAddr, addr_add_ofNat, addr_eq (by omega)]

theorem ok_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : Ok rCfg s := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  refine ⟨fun k hk' => ?_, fun k hk' => ?_, ?_, fun k hk' j hj => ?_⟩
  · simp only [rCfg] at hk'
    rw [h.wr, show rCfg.base = .ebp from rfl, h.ebp, ← add_zero32 (s₀.gpr .ebp)]
    exact in_word hX hXw (by omega)
  · simp only [rCfg] at hk'
    rw [h.rd, h.wr, show rCfg.ext = .esi from rfl, hk]
    exact in_word hR hRw (by omega)
  · show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32
    rw [h.ebp]; omega
  · simp only [rCfg] at hk' hj
    rw [show rCfg.base = .ebp from rfl, show rCfg.ext = .esi from rfl, h.ebp, hk]
    exact hp.disj.sep (contains_w (by omega) (by omega)) (contains_w_off (len := 384) (by omega) (by omega))

theorem key_at {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {n : Nat} (hn : n < 48)
    (hk : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * n)) : key48 s = ((sch s₀).getD n 0).setWidth 48 := by
  obtain ⟨lR, hR, hRl, hRw⟩ := hp.sched
  rw [scheduleAt_getD _ _ hn, setWidth48_readW]
  have rd : ∀ d, d + 4 ≤ 384 → s.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 =
      s₀.mem.readW ((s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d) 32 := fun d hd =>
    h.frame.readW (r := ⟨(s₀.gpr .esi).setWidth 64 + BitVec.ofNat 64 d, 4⟩) (Region.contains_self _ _)
      (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        exact hp.disj.symm.sub_left (Offset.sub_base _ hd)) (by decide)
  rw [key48, keyLo, keyHi, hk, wordAddr_off _ (by omega), wordAddr_off _ (by omega), rd _ (by omega),
    rd _ (by omega), Offset.add_add, show 8 * n + 4 * 0 = 8 * n by omega]

/-! ## The rounds of a pass -/

/-- The key schedule's slot before round `j` of pass `p`. -/
def kpos (p j : Nat) : Nat := if p % 2 = 1 then 16 * p + 15 - j else 16 * p + j

/-- The distance from one round key to the next in pass `p`. -/
def stride (p : Nat) : BitVec 32 := if p % 2 = 1 then BitVec.ofNat 32 (2 ^ 32 - 8) else BitVec.ofNat 32 8

theorem kpos_succ_addr (a : BitVec 32) {p j : Nat} (hp : p < 3) (hj : j < 16) :
    a + BitVec.ofNat 32 (8 * kpos p j) + stride p = a + BitVec.ofNat 32 (8 * kpos p (j + 1)) := by
  rw [BitVec.add_assoc, stride, kpos, kpos]
  congr 1
  split
  · rw [← BitVec.ofNat_add]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · rw [← BitVec.ofNat_add]
    congr 1

theorem ofNat_sub_one {k : Nat} (hk : 1 ≤ k) (hk' : k < 2 ^ 32) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, show (1 : BitVec 32) = BitVec.ofNat 32 1 from rfl, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- After `j` rounds of pass `p`, from the halves `lr`. -/
structure PInv (s₀ : State) (p : Nat) (lr : BitVec 32 × BitVec 32) (j : Nat) (s : State) : Prop where
  same : Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p j)
  step : slotW s slotStep = stride p
  pcnt : slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  rcnt : slotW s slotRounds = BitVec.ofNat 32 (16 - j)
  halves : (slotW s slotL, slotW s slotR) = rounds (passKeys (sch s₀) p) j lr

theorem kpos_lt {p j : Nat} (hp : p < 3) (hj : j < 16) : kpos p j < 48 := by
  simp only [kpos]; split <;> omega

theorem passKeys_at (s₀ : State) {p j : Nat} (hj : j < 16) :
    passKeys (sch s₀) p j = ((sch s₀).getD (kpos p j) 0).setWidth 48 := by
  rw [passKeys_eq _ hj, kpos]
  by_cases h : p % 2 = 1
  · rw [ite_eq_left h, ite_eq_left h, show 16 * p + (15 - j) = 16 * p + 15 - j by omega]
  · rw [ite_eq_right h, ite_eq_right h]

/-- The scratch buffer's word `k` (of 21) is inside it. -/
theorem BlockPre.slotIn {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions s.wr (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr
  rw [h.wr, h.ebp, ← add_zero32 (s₀.gpr .ebp)]
  exact in_word hX hXw (by omega)

theorem BlockPre.slotIn' {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) :
    InRegions (s.rd ++ s.wr) (addr (s.gpr .ebp) (4 * k)) 4 := by
  obtain ⟨r, hr, hc⟩ := hp.slotIn h hk
  exact ⟨r, List.mem_append_right _ hr, hc⟩

theorem BlockPre.fit {s₀ : State} (hp : BlockPre s₀) : (s₀.gpr .ebp).toNat + 84 ≤ 2 ^ 32 := by
  obtain ⟨lX, hX, hXl, hXw⟩ := hp.scr; omega

/-- Slots `j` and `k` are apart. -/
theorem slot_ne {s₀ : State} (hp : BlockPre s₀) {j k : Nat} (h : j ≠ k) (hj : j < 21) (hk : k < 21) :
    Mem.Sep (wordAddr (s₀.gpr .ebp) j) (32 / 8) (wordAddr (s₀.gpr .ebp) k) (32 / 8) :=
  slot_word_sep _ h (by have := hp.fit; omega) (by have := hp.fit; omega)

/-- The frame of the block's words, after a write of one of them. -/
theorem Same.write {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) {k : Nat} (hk : k < 21) (v : BitVec 32) :
    Frame [xR s₀] s₀.mem (s.mem.writeW (wordAddr (s₀.gpr .ebp) k) v) :=
  h.frame.writeW (List.mem_singleton_self _) _ (contains_word rfl (by have := hp.fit; omega)
    (show 0 + 4 * k + 4 ≤ 84 by omega) (Nat.le_refl _) |> fun c => by rwa [add_zero32] at c)

/-- One round of pass `p`. -/
theorem roundStep_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {j : Nat} (hj : j < 16) {s : State} (h : PInv s₀ p lr j s) :
    WP isa (.block (round ++ roundTail)) s fun s' => s'.zf = some (decide (j + 1 = 16)) ∧ PInv s₀ p lr (j + 1) s' := by
  rw [WP.block_append_iff]
  obtain ⟨s₁, h₁, eL, eR, rd₁, wr₁, k₁, f₁⟩ := round_ok (ok_at hp h.same (kpos_lt hp3 hj) h.esi)
  refine WP.of_runBlock ⟨s₁, h₁, ?_⟩
  have e₁ : s₁.gpr .ebp = s₀.gpr .ebp := (k₁ .ebp (by simp [kept])).trans h.same.ebp
  have hsub : ∀ r ∈ [slotRegion rCfg s], ∃ r' ∈ [xR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, xR]; rw [show rCfg.base = .ebp from rfl, h.same.ebp]
    exact Region.sub_prefix (by decide)
  have same₁ : Same s₀ s₁ :=
    ⟨e₁, (k₁ .esp (by simp [kept])).trans h.same.esp, rd₁.trans h.same.rd, wr₁.trans h.same.wr,
      h.same.frame.trans (f₁.sub hsub)⟩
  -- The counters past the round's slots.
  have keep : ∀ k, 18 ≤ k → k < 21 → slotW s₁ k = slotW s k := fun k h₁' h₂' => by
    show s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [e₁, ← h.same.ebp]
    exact slot_frame (n := 18) f₁ h₁' (by rw [h.same.ebp]; have := hp.fit; omega)
  have i₁ : s₁.gpr .esi = s.gpr .esi := k₁ .esi (by simp [kept])
  -- `roundTail`.
  have in20 := hp.slotIn' same₁ (k := slotStep) (by decide)
  have in18 := hp.slotIn' same₁ (k := slotRounds) (by decide)
  have w18 := hp.slotIn same₁ (k := slotRounds) (by decide)
  rw [e₁] at in20 in18 w18
  refine wp_ldm e₁ in20 fun s₂' u₂' => wp_add fun s₂ u₂ _ => wp_ldm (B := s₀.gpr .ebp)
    (by rw [u₂.other _ (by decide), u₂'.other _ (by decide), e₁])
    (by rw [u₂.rd, u₂.wr, u₂'.rd, u₂'.wr]; exact in18) fun s₃ u₃ => wp_subi fun s₄ u₄ _ z₄ => ?_
  have e₄ : s₄.gpr .ebp = s₀.gpr .ebp := by rw [u₄.other _ (by decide), u₃.other _ (by decide),
    u₂.other _ (by decide), u₂'.other _ (by decide), e₁]
  refine wp_stm e₄ (by rw [u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact w18) fun s₅ w₅ => WP.block_nil ?_
  have m₅ : s₅.mem = s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (s₄.gpr .eax) := by
    rw [w₅.mem, u₄.mem, u₃.mem, u₂.mem, u₂'.mem]
  have g₅ : ∀ r, r ≠ .esi → r ≠ .eax → s₅.gpr r = s₁.gpr r := fun r h₁' h₂' => by
    rw [w₅.gpr, u₄.other _ h₂', u₃.other _ h₂', u₂.other _ h₁', u₂'.other _ h₂']
  have e₅ : s₅.gpr .ebp = s₀.gpr .ebp := by rw [g₅ _ (by decide) (by decide), e₁]
  have r18 : slotW s₁ slotRounds = BitVec.ofNat 32 (16 - j) := by rw [keep _ (by decide) (by decide), h.rcnt]
  have ax₄ : s₄.gpr .eax = BitVec.ofNat 32 (16 - (j + 1)) := by
    rw [u₄.gpr, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← slotW, r18, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  have other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₅ k = slotW s₁ k := fun k hk hk' => by
    show s₅.mem.readW (wordAddr (s₅.gpr .ebp) k) 32 = s₁.mem.readW (wordAddr (s₁.gpr .ebp) k) 32
    rw [m₅, e₅, e₁, Mem.readW_writeW_sep (slot_ne hp hk hk' (by decide)) (by decide)]
  refine ⟨?_, ⟨e₅.trans same₁.ebp.symm |>.trans same₁.ebp, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [w₅.zf, z₄, u₃.gpr, u₂.mem, u₂'.mem, ← e₁, ← slotW, r18, ofNat_sub_one (by omega) (by omega),
      Wp.ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [g₅ _ (by decide) (by decide)]; exact same₁.esp
  · rw [w₅.rd, u₄.rd, u₃.rd, u₂.rd, u₂'.rd]; exact same₁.rd
  · rw [w₅.wr, u₄.wr, u₃.wr, u₂.wr, u₂'.wr]; exact same₁.wr
  · rw [m₅]; exact Same.write hp same₁ (by decide) _
  · rw [w₅.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr, u₂'.gpr, u₂'.other _ (by decide), i₁, h.esi, ← e₁, ← slotW,
      keep _ (by decide) (by decide), h.step, kpos_succ_addr _ hp3 hj]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.step]
  · rw [other _ (by decide) (by decide), keep _ (by decide) (by decide), h.pcnt]
  · show s₅.mem.readW (wordAddr (s₅.gpr .ebp) slotRounds) 32 = _
    rw [m₅, e₅, Mem.readW_writeW_self32, ax₄]
  · rw [other _ (by decide) (by decide), other _ (by decide) (by decide), rounds_succ, ← h.halves, eL, eR,
      key_at hp h.same (kpos_lt hp3 hj) h.esi, passKeys_at s₀ hj]

theorem eval_ne (s : State) : isa.eval .ne s = s.zf.map (!·) := rfl

/-- Reading slot `k` after writing slot `j`. -/
theorem rd_wr_ne {s₀ : State} (hp : BlockPre s₀) (m : Mem) {j k : Nat} (v : BitVec 32) (h : k ≠ j) (hk : k < 21)
    (hj : j < 21) :
    (m.writeW (wordAddr (s₀.gpr .ebp) j) v).readW (wordAddr (s₀.gpr .ebp) k) 32 =
      m.readW (wordAddr (s₀.gpr .ebp) k) 32 :=
  Mem.readW_writeW_sep (slot_ne hp h hk hj) (by decide)

/-- Pass `p`: sixteen rounds from the halves `lr`. -/
theorem pass_ok {s₀ : State} (hp : BlockPre s₀) {p : Nat} (hp3 : p < 3) {lr : BitVec 32 × BitVec 32}
    {s : State} (h : Same s₀ s) (hesi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p 0))
    (hstep : slotW s slotStep = stride p) (hpc : slotW s slotPasses = BitVec.ofNat 32 (3 - p))
    (hh : (slotW s slotL, slotW s slotR) = lr) :
    WP isa pass s (PInv s₀ p lr 16) := by
  have w18 := hp.slotIn h (k := slotRounds) (by decide)
  rw [h.ebp] at w18
  refine WP.seq (wp_movi fun s₁ u₁ => wp_stm (B := s₀.gpr .ebp) (by rw [u₁.other _ (by decide), h.ebp])
    (by rw [u₁.wr]; exact w18) fun s₂ w₂ => WP.block_nil ?_)
  have g₂ : ∀ r, r ≠ .eax → s₂.gpr r = s.gpr r := fun r hr => by rw [w₂.gpr, u₁.other _ hr]
  have e₂ : s₂.gpr .ebp = s₀.gpr .ebp := by rw [g₂ _ (by decide), h.ebp]
  have m₂ : s₂.mem = s.mem.writeW (wordAddr (s₀.gpr .ebp) slotRounds) (16 : BitVec 32) := by rw [w₂.mem, u₁.mem, u₁.gpr]
  have other : ∀ k, k ≠ slotRounds → k < 21 → slotW s₂ k = slotW s k := fun k hk hk' => by
    show s₂.mem.readW (wordAddr (s₂.gpr .ebp) k) 32 = s.mem.readW (wordAddr (s.gpr .ebp) k) 32
    rw [m₂, e₂, h.ebp, rd_wr_ne hp _ _ hk hk' (by decide)]
  have hI : PInv s₀ p lr 0 s₂ :=
    ⟨⟨e₂, by rw [g₂ _ (by decide)]; exact h.esp, by rw [w₂.rd, u₁.rd]; exact h.rd,
      by rw [w₂.wr, u₁.wr]; exact h.wr, by rw [m₂]; exact Same.write hp h (by decide) _⟩,
      by rw [g₂ _ (by decide), hesi], by rw [other _ (by decide) (by decide), hstep],
      by rw [other _ (by decide) (by decide), hpc],
      by show s₂.mem.readW (wordAddr (s₂.gpr .ebp) slotRounds) 32 = _; rw [m₂, e₂, Mem.readW_writeW_self32]; rfl,
      by rw [other _ (by decide) (by decide), other _ (by decide) (by decide), hh]; rfl⟩
  refine WP.loop (M := isa) (body := .block (round ++ roundTail)) (c := .ne) (Q := PInv s₀ p lr 16)
    (fun (n : Nat) (t : State) => ∃ j, n = 16 - j ∧ j < 16 ∧ PInv s₀ p lr j t) ?_ 16 _ ⟨0, rfl, by decide, hI⟩
  rintro n t ⟨j, rfl, hj, ht⟩
  refine WP.mono (roundStep_ok hp hp3 hj ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : j + 1 = 16
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 16 - (j + 1), by omega, j + 1, rfl, by omega, h'⟩

/-! ## The passes -/

/-- After `p` passes, from the block `x`. -/
structure OInv (s₀ : State) (x : BitVec 64) (p : Nat) (s : State) : Prop where
  same : Same s₀ s
  esi : s.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos p 0)
  step : slotW s slotStep = stride p
  pcnt : slotW s slotPasses = BitVec.ofNat 32 (3 - p)
  halves : (slotW s slotL, slotW s slotR) = passes (sch s₀) p (split (Spec.TripleDes.permute Spec.TripleDes.ip x))

theorem kpos_tail_addr (a : BitVec 32) {p : Nat} (hp : p < 3) :
    a + BitVec.ofNat 32 (8 * kpos p 16) + (128 - stride p) = a + BitVec.ofNat 32 (8 * kpos (p + 1) 0) := by
  rw [BitVec.add_assoc]
  congr 1
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

theorem stride_succ {p : Nat} (hp : p < 3) : 0 - stride p = stride (p + 1) := by
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl <;> decide

/-- One pass and the exchange after it. -/
theorem passBody_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {p : Nat} (hp3 : p < 3) {s : State}
    (h : OInv s₀ x p s) :
    WP isa (.seq pass (.block passTail)) s fun s' => s'.zf = some (decide (p + 1 = 3)) ∧ OInv s₀ x (p + 1) s' := by
  refine WP.seq (WP.mono (pass_ok hp hp3 h.same h.esi h.step h.pcnt h.halves) fun s₁ h₁ => ?_)
  have e₁ := h₁.same.ebp
  have rin : ∀ k, k < 21 → InRegions (s₁.rd ++ s₁.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' h₁.same hk; rwa [e₁] at this
  have win : ∀ k, k < 21 → InRegions s₁.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn h₁.same hk; rwa [e₁] at this
  refine wp_ldm (o := 4 * slotStep) e₁ (rin _ (by decide)) fun t₁ u₁ => wp_movi fun t₂ u₂ =>
    wp_sub fun t₃ u₃ _ => wp_add fun t₄ u₄ _ => wp_movi fun t₅ u₅ => wp_sub fun t₆ u₆ _ => ?_
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₆.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [u₆.other _ ha, u₅.other _ ha, u₄.other _ hs, u₃.other _ ha, u₂.other _ ha, u₁.other _ hc]
  have e₆ : t₆.gpr .ebp = s₀.gpr .ebp := by rw [g₆ _ (by decide) (by decide) (by decide), e₁]
  have wr₆ : t₆.wr = s₁.wr := by rw [u₆.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have rd₆ : t₆.rd = s₁.rd := by rw [u₆.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have m₆ : t₆.mem = s₁.mem := by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have stp : t₁.gpr .ecx = stride p := by rw [u₁.gpr, ← e₁, ← slotW, h₁.step]
  refine wp_stm e₆ (by rw [wr₆]; exact win _ (by decide)) fun t₇ w₇ => ?_
  refine wp_ldm (o := 4 * slotL) (by rw [w₇.gpr, e₆]) (by rw [w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide))
    fun t₈ u₈ => ?_
  refine wp_ldm (o := 4 * slotR) (by rw [u₈.other _ (by decide), w₇.gpr, e₆])
    (by rw [u₈.rd, u₈.wr, w₇.rd, w₇.wr, rd₆, wr₆]; exact rin _ (by decide)) fun t₉ u₉ => ?_
  have e₉ : t₉.gpr .ebp = s₀.gpr .ebp := by rw [u₉.other _ (by decide), u₈.other _ (by decide), w₇.gpr, e₆]
  have wr₉ : t₉.wr = s₁.wr := by rw [u₉.wr, u₈.wr, w₇.wr, wr₆]
  refine wp_stm (o := 4 * slotL) e₉ (by rw [wr₉]; exact win _ (by decide)) fun t₁₀ w₁₀ => ?_
  refine wp_stm (o := 4 * slotR) (by rw [w₁₀.gpr, e₉]) (by rw [w₁₀.wr, wr₉]; exact win _ (by decide))
    fun t₁₁ w₁₁ => ?_
  refine wp_ldm (o := 4 * slotPasses) (by rw [w₁₁.gpr, w₁₀.gpr, e₉])
    (by rw [w₁₁.rd, w₁₁.wr, w₁₀.rd, w₁₀.wr, u₉.rd, u₈.rd, w₇.rd, rd₆, wr₉]; exact rin _ (by decide))
    fun t₁₂ u₁₂ => wp_subi fun t₁₃ u₁₃ _ z₁₃ => ?_
  have e₁₃ : t₁₃.gpr .ebp = s₀.gpr .ebp := by
    rw [u₁₃.other _ (by decide), u₁₂.other _ (by decide), w₁₁.gpr, w₁₀.gpr, e₉]
  refine wp_stm (o := 4 * slotPasses) e₁₃
    (by rw [u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact win _ (by decide)) fun t₁₄ w₁₄ => WP.block_nil ?_
  -- The memory.
  have m₁₁ : t₁₁.mem = ((s₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotStep) (t₆.gpr .eax)).writeW
      (wordAddr (s₀.gpr .ebp) slotL) (t₉.gpr .ecx)).writeW (wordAddr (s₀.gpr .ebp) slotR) (t₉.gpr .eax) := by
    rw [w₁₁.mem, w₁₀.mem, w₁₀.gpr, u₉.mem, u₈.mem, w₇.mem, m₆]
  have m₁₄ : t₁₄.mem = t₁₁.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (t₁₃.gpr .eax) := by
    rw [w₁₄.mem, u₁₃.mem, u₁₂.mem]
  have rd₁ : ∀ k, slotW s₁ k = s₁.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁]
  have ax₉L : t₉.gpr .eax = slotW s₁ slotL := by
    rw [u₉.other _ (by decide), u₈.gpr, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have ax₉R : t₉.gpr .ecx = slotW s₁ slotR := by
    rw [u₉.gpr, u₈.mem, w₇.mem, m₆, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have pc₁₂ : t₁₂.gpr .eax = slotW s₁ slotPasses := by
    rw [u₁₂.gpr, m₁₁, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd₁]
  have e₁₄ : t₁₄.gpr .ebp = s₀.gpr .ebp := by rw [w₁₄.gpr, e₁₃]
  have sl : ∀ k, slotW t₁₄ k = t₁₄.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁₄]
  have g₁₄ : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .esi → t₁₄.gpr r = s₁.gpr r := fun r ha hc hs => by
    rw [w₁₄.gpr, u₁₃.other _ ha, u₁₂.other _ ha, w₁₁.gpr, w₁₀.gpr, u₉.other _ hc, u₈.other _ ha, w₇.gpr,
      g₆ _ ha hc hs]
  refine ⟨?_, ⟨⟨e₁₄, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [w₁₄.zf, z₁₃, pc₁₂, h₁.pcnt, ofNat_sub_one (by omega) (by omega), Wp.ofNat_beq_zero (by omega)]
    exact congrArg some (decide_eq_decide.mpr (by omega))
  · rw [g₁₄ _ (by decide) (by decide) (by decide)]; exact h₁.same.esp
  · rw [w₁₄.rd, u₁₃.rd, u₁₂.rd, w₁₁.rd, w₁₀.rd, u₉.rd, u₈.rd, w₇.rd, rd₆]; exact h₁.same.rd
  · rw [w₁₄.wr, u₁₃.wr, u₁₂.wr, w₁₁.wr, w₁₀.wr, wr₉]; exact h₁.same.wr
  · have xC : ∀ k, k < 21 → (xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
      contains_w (by have := hp.fit; omega) (by omega)
    rw [m₁₄, m₁₁]
    exact (((h₁.same.frame.writeW (List.mem_singleton_self _) _ (xC slotStep (by decide))).writeW
      (List.mem_singleton_self _) _ (xC slotL (by decide))).writeW (List.mem_singleton_self _) _
      (xC slotR (by decide))).writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))
  · rw [w₁₄.gpr, u₁₃.other .esi (by decide), u₁₂.other .esi (by decide), w₁₁.gpr, w₁₀.gpr,
      u₉.other .esi (by decide), u₈.other .esi (by decide), w₇.gpr, u₆.other .esi (by decide),
      u₅.other .esi (by decide), u₄.gpr, u₃.gpr, u₂.gpr, u₃.other .esi (by decide), u₂.other .esi (by decide),
      u₂.other .ecx (by decide), u₁.other .esi (by decide), h₁.esi, stp, kpos_tail_addr _ hp3]
  · rw [sl, m₁₄, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁,
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, u₆.gpr, u₅.gpr, u₅.other .ecx (by decide), u₄.other .ecx (by decide),
      u₃.other .ecx (by decide), u₂.other .ecx (by decide), stp, stride_succ hp3]
  · rw [sl, m₁₄, Mem.readW_writeW_self32, u₁₃.gpr, pc₁₂, h₁.pcnt, ofNat_sub_one (by omega) (by omega), Nat.sub_sub]
  · rw [sl, sl, m₁₄, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      rd_wr_ne hp _ _ (by decide) (by decide) (by decide), m₁₁, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
      Mem.readW_writeW_self32, Mem.readW_writeW_self32, ax₉L, ax₉R, passes, ← h₁.halves]
    rfl

/-- The three passes. -/
theorem passes_ok {s₀ : State} (hp : BlockPre s₀) {x : BitVec 64} {s : State} (h : OInv s₀ x 0 s) :
    WP isa (.loop (.seq pass (.block passTail)) .ne) s (OInv s₀ x 3) := by
  refine WP.loop (M := isa) (body := .seq pass (.block passTail)) (c := .ne) (Q := OInv s₀ x 3)
    (fun (n : Nat) (t : State) => ∃ p, n = 3 - p ∧ p < 3 ∧ OInv s₀ x p t) ?_ 3 _ ⟨0, rfl, by decide, h⟩
  rintro n t ⟨p, rfl, hp3, ht⟩
  refine WP.mono (passBody_ok hp hp3 ht) fun t' ⟨z', h'⟩ => ?_
  by_cases hz : p + 1 = 3
  · left
    refine ⟨by rw [eval_ne, z']; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [eval_ne, z']; simp [hz], 3 - (p + 1), by omega, p + 1, rfl, by omega, h'⟩

/-! ## `IP` and `IP⁻¹` -/

/-- Bit `b` of a block `hi ‖ lo`, as an atom: of `hi` (input word 0) or `lo`
(input word 1). -/
def xAtom (b : Nat) : Nat := if 32 ≤ b then b - 32 else 32 + b

/-- `IP`'s high half into slot `L`, its low half into slot `R`. -/
def ipGL (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc (32 + t))] else []
def ipGR (t : Nat) : List Nat := if t < 32 then [xAtom (ipSrc t)] else []

theorem ip_check :
    check (lanes 32 6) oCfg (linExt 0) ipCode (linEnv [(0, 0), (1, 1)])
      (linPost oCfg.slots 6 [(slotL, ipGL), (slotR, ipGR)]) = true := by
  decide +kernel

/-- `IP⁻¹(R ‖ L)` into slots 0 (high word) and 1 (low word), from `R` in slot
`L` (input word 0) and `L` in slot `R` (input word 1). -/
def fpG0 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc (32 + t))] else []
def fpG1 (t : Nat) : List Nat := if t < 32 then [xAtom (fpSrc t)] else []

theorem fp_check :
    check (lanes 32 6) oCfg (linExt 0) fpCode (linEnv [(slotL, 0), (slotR, 1)])
      (linPost oCfg.slots 6 [(0, fpG0), (1, fpG1)]) = true := by
  decide +kernel

theorem ip_kept : kept.all (fun r => ipCode.all fun i => i.dst != some r) = true := by decide +kernel

theorem fp_kept : kept.all (fun r => fpCode.all fun i => i.dst != some r) = true := by decide +kernel

theorem ipSrc_lt : ∀ j < 64, ipSrc j < 64 := by decide

theorem fpSrc_lt : ∀ j < 64, fpSrc j < 64 := by decide

/-- A bit of `hi ‖ lo`. -/
theorem bit_xAtom (W : Nat → BitVec 32) {b : Nat} (hb : b < 64) :
    bitOf W (xAtom b) = (W 0 ++ W 1).getLsbD b := by
  rw [BitVec.getLsbD_append, xAtom]
  by_cases h : 32 ≤ b
  · rw [ite_eq_left h, ite_eq_right (by omega), bitOf, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_right h, ite_eq_left (by omega), bitOf, show (32 + b) / 32 = 1 by omega,
      show (32 + b) % 32 = b by omega]

theorem ip_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa ipCode s = some s' ∧
      (slotW s' slotL, slotW s' slotR) = split (Spec.TripleDes.permute Spec.TripleDes.ip (slotW s 0 ++ slotW s 1)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then slotW s 0 else slotW s 1
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok ip_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp ip_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ [(slotL, ipGL), (slotR, ipGR)] → ∀ p < 32,
      (slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = slotW s 0 ++ slotW s 1 := rfl
  simp only [split, Prod.mk.injEq]
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro t ht
  · rw [bit slotL ipGL (List.mem_cons_self ..) t ht, ipGL, ite_eq_left ht, xorBits_cons, xorBits_nil,
      Bool.xor_false, bit_xAtom W (ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth, decide_eq_true ht,
      Bool.true_and, BitVec.getLsbD_ushiftRight, getLsbD_permute _ _ (by decide) (show 32 + t < 64 by omega)]
    rfl
  · rw [bit slotR ipGR (List.mem_cons_of_mem _ (List.mem_cons_self ..)) t ht, ipGR, ite_eq_left ht, xorBits_cons,
      xorBits_nil, Bool.xor_false, bit_xAtom W (ipSrc_lt _ (by omega)), hx, BitVec.getLsbD_setWidth,
      decide_eq_true ht, Bool.true_and, getLsbD_permute _ _ (by decide) (show t < 64 by omega)]
    rfl

theorem fp_ok {s : State} (hok : Ok oCfg s) :
    ∃ s', runBlock isa fpCode s = some s' ∧
      slotW s' 0 ++ slotW s' 1 = Spec.TripleDes.permute Spec.TripleDes.fp (slotW s slotL ++ slotW s slotR) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r ∈ kept, s'.gpr r = s.gpr r) ∧
      Frame [slotRegion oCfg s] s.mem s'.mem := by
  let W : Nat → BitVec 32 := fun i => if i = 0 then slotW s slotL else slotW s slotR
  obtain ⟨s', hs', hout, hrd, hwr, hoth, hfr⟩ := linear_ok fp_check hok W
    (fun j i hji _ => by
      simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at hji
      rcases hji with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by decide, rfl⟩)
    (fun j hj => absurd hj (by simp [oCfg]))
  have kp : ∀ r ∈ kept, s'.gpr r = s.gpr r := fun r hr => hoth _ (List.all_eq_true.mp fp_kept r hr)
  have e : s'.gpr .ebp = s.gpr .ebp := kp _ (by simp [kept])
  have bit : ∀ j g, (j, g) ∈ [(0, fpG0), (1, fpG1)] → ∀ p < 32,
      (slotW s' j).getLsbD p = xorBits W (g p) := fun j g h p hp => by
    rw [slotW, e]; exact hout j g h p hp
  refine ⟨s', hs', ?_, hrd, hwr, kp, hfr⟩
  have hx : W 0 ++ W 1 = slotW s slotL ++ slotW s slotR := rfl
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_append, getLsbD_permute _ _ (by decide) hj,
    show 64 - Spec.TripleDes.fp.getD (64 - 1 - j) 1 = fpSrc j from rfl]
  by_cases h32 : j < 32
  · rw [ite_eq_left h32, bit 1 fpG1 (List.mem_cons_of_mem _ (List.mem_cons_self ..)) j h32, fpG1, ite_eq_left h32,
      xorBits_cons, xorBits_nil, Bool.xor_false, bit_xAtom W (fpSrc_lt _ hj), hx]
  · rw [ite_eq_right h32, bit 0 fpG0 (List.mem_cons_self ..) (j - 32) (by omega), fpG0, ite_eq_left (by omega),
      xorBits_cons, xorBits_nil, Bool.xor_false, show 32 + (j - 32) = j by omega, bit_xAtom W (fpSrc_lt _ hj), hx]

/-! ## The block -/

theorem oCfg_ok {s₀ s : State} (hp : BlockPre s₀) (h : Same s₀ s) : Ok oCfg s :=
  ⟨fun k hk => hp.slotIn h (by simp only [oCfg] at hk; omega), fun k hk => absurd hk (by simp [oCfg]),
    by show (s.gpr .ebp).toNat + 4 * 18 ≤ 2 ^ 32; rw [h.ebp]; have := hp.fit; omega,
    fun k _ j hj => absurd hj (by simp [oCfg])⟩

theorem oCfg_sub {s₀ s : State} (h : Same s₀ s) : ∀ r ∈ [slotRegion oCfg s], ∃ r' ∈ [xR s₀], Region.Sub r r' :=
  fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [slotRegion, xR]; rw [show oCfg.base = .ebp from rfl, h.ebp]
    exact Region.sub_prefix (by decide)

/-- TDEA encryption of the block in `eax:edx` (its high and low words) with
the key schedule at `esi`, into `eax:edx`. -/
theorem block_ok {s₀ : State} (hp : BlockPre s₀) :
    WP isa block s₀ fun s =>
      Same s₀ s ∧ s.gpr .esi = s₀.gpr .esi ∧
        s.gpr .eax ++ s.gpr .edx = tdes (sch s₀) (s₀.gpr .eax ++ s₀.gpr .edx) := by
  have xC : ∀ k, k < 21 → (xR s₀).Contains (wordAddr (s₀.gpr .ebp) k) (32 / 8) := fun k hk =>
    contains_w (by have := hp.fit; omega) (by omega)
  have same₀ : Same s₀ s₀ := ⟨rfl, rfl, rfl, rfl, Frame.refl _ _⟩
  have win : ∀ k, k < 21 → InRegions s₀.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => hp.slotIn same₀ hk
  refine WP.seq ?_
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_stm (o := 4 * 0) rfl (win 0 (by decide)) fun s₁ w₁ =>
    wp_stm (o := 4 * 1) (by rw [w₁.gpr]) (by rw [w₁.wr]; exact win 1 (by decide)) fun s₂ w₂ => WP.block_nil ?_
  have m₂ : s₂.mem = (s₀.mem.writeW (wordAddr (s₀.gpr .ebp) 0) (s₀.gpr .eax)).writeW (wordAddr (s₀.gpr .ebp) 1)
      (s₀.gpr .edx) := by rw [w₂.mem, w₁.mem, w₁.gpr]
  have same₂ : Same s₀ s₂ := ⟨by rw [w₂.gpr, w₁.gpr], by rw [w₂.gpr, w₁.gpr], by rw [w₂.rd, w₁.rd],
    by rw [w₂.wr, w₁.wr], by
      rw [m₂]; exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (xC 0 (by decide))).writeW
        (List.mem_singleton_self _) _ (xC 1 (by decide))⟩
  have sl₂ : ∀ k, slotW s₂ k = s₂.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, same₂.ebp]
  have x₂ : slotW s₂ 0 ++ slotW s₂ 1 = s₀.gpr .eax ++ s₀.gpr .edx := by
    rw [sl₂, sl₂, m₂, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32,
      Mem.readW_writeW_self32]
  obtain ⟨s₃, h₃, ip₃, rd₃, wr₃, k₃, f₃⟩ := ip_ok (oCfg_ok hp same₂)
  refine WP.of_runBlock ⟨s₃, h₃, ?_⟩
  have e₃ : s₃.gpr .ebp = s₀.gpr .ebp := (k₃ .ebp (by simp [kept])).trans same₂.ebp
  have same₃ : Same s₀ s₃ := ⟨e₃, (k₃ .esp (by simp [kept])).trans same₂.esp, rd₃.trans same₂.rd,
    wr₃.trans same₂.wr, same₂.frame.trans (f₃.sub (oCfg_sub same₂))⟩
  have win₃ : ∀ k, k < 21 → InRegions s₃.wr (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn same₃ hk; rwa [e₃] at this
  refine wp_movi fun s₄ u₄ => wp_stm (o := 4 * slotPasses) (B := s₀.gpr .ebp) (by rw [u₄.other _ (by decide), e₃])
    (by rw [u₄.wr]; exact win₃ _ (by decide)) fun s₅ w₅ => wp_movi fun s₆ u₆ =>
    wp_stm (o := 4 * slotStep) (B := s₀.gpr .ebp) (by rw [u₆.other _ (by decide), w₅.gpr, u₄.other _ (by decide), e₃])
    (by rw [u₆.wr, w₅.wr, u₄.wr]; exact win₃ _ (by decide)) fun s₇ w₇ => WP.block_nil ?_
  have m₇ : s₇.mem = (s₃.mem.writeW (wordAddr (s₀.gpr .ebp) slotPasses) (3 : BitVec 32)).writeW
      (wordAddr (s₀.gpr .ebp) slotStep) (8 : BitVec 32) := by
    rw [w₇.mem, u₆.mem, u₆.gpr, w₅.mem, u₄.mem, u₄.gpr]
  have g₇ : ∀ r, r ≠ .eax → s₇.gpr r = s₃.gpr r := fun r hr => by
    rw [w₇.gpr, u₆.other _ hr, w₅.gpr, u₄.other _ hr]
  have e₇ : s₇.gpr .ebp = s₀.gpr .ebp := by rw [g₇ _ (by decide), e₃]
  have sl₇ : ∀ k, slotW s₇ k = s₇.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₇]
  have sl₃ : ∀ k, slotW s₃ k = s₃.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₃]
  have esi₇ : s₇.gpr .esi = s₀.gpr .esi + BitVec.ofNat 32 (8 * kpos 0 0) := by
    rw [g₇ _ (by decide), k₃ .esi (by simp [kept]), show s₂.gpr .esi = s₀.gpr .esi by rw [w₂.gpr, w₁.gpr]]
    simp [kpos]
  have hO : OInv s₀ (s₀.gpr .eax ++ s₀.gpr .edx) 0 s₇ :=
    ⟨⟨e₇, by rw [g₇ _ (by decide)]; exact same₃.esp, by rw [w₇.rd, u₆.rd, w₅.rd, u₄.rd]; exact same₃.rd,
      by rw [w₇.wr, u₆.wr, w₅.wr, u₄.wr]; exact same₃.wr, by
        rw [m₇]; exact (same₃.frame.writeW (List.mem_singleton_self _) _ (xC slotPasses (by decide))).writeW
          (List.mem_singleton_self _) _ (xC slotStep (by decide))⟩,
      esi₇,
      by rw [sl₇, m₇, Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, m₇, rd_wr_ne hp _ _ (by decide) (by decide) (by decide), Mem.readW_writeW_self32]; rfl,
      by rw [sl₇, sl₇, m₇, rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        rd_wr_ne hp _ _ (by decide) (by decide) (by decide), rd_wr_ne hp _ _ (by decide) (by decide) (by decide),
        rd_wr_ne hp _ _ (by decide) (by decide) (by decide), ← sl₃, ← sl₃, ip₃, x₂]; rfl⟩
  refine WP.seq (WP.mono (passes_ok hp hO) fun s₈ h₈ => ?_)
  rw [WP.block_append_iff, WP.block_append_iff]
  refine wp_subi fun s₉ u₉ _ _ => WP.block_nil ?_
  have same₉ : Same s₀ s₉ := ⟨by rw [u₉.other _ (by decide)]; exact h₈.same.ebp,
    by rw [u₉.other _ (by decide)]; exact h₈.same.esp, by rw [u₉.rd]; exact h₈.same.rd,
    by rw [u₉.wr]; exact h₈.same.wr, by rw [u₉.mem]; exact h₈.same.frame⟩
  obtain ⟨s₁₀, h₁₀, fp₁₀, rd₁₀, wr₁₀, k₁₀, f₁₀⟩ := fp_ok (oCfg_ok hp same₉)
  refine WP.of_runBlock ⟨s₁₀, h₁₀, ?_⟩
  have e₁₀ : s₁₀.gpr .ebp = s₀.gpr .ebp := (k₁₀ .ebp (by simp [kept])).trans same₉.ebp
  have same₁₀ : Same s₀ s₁₀ := ⟨e₁₀, (k₁₀ .esp (by simp [kept])).trans same₉.esp, rd₁₀.trans same₉.rd,
    wr₁₀.trans same₉.wr, same₉.frame.trans (f₁₀.sub (oCfg_sub same₉))⟩
  have rin : ∀ k, k < 21 → InRegions (s₁₀.rd ++ s₁₀.wr) (addr (s₀.gpr .ebp) (4 * k)) 4 := fun k hk => by
    have := hp.slotIn' same₁₀ hk; rwa [e₁₀] at this
  refine wp_ldm (o := 4 * 0) e₁₀ (rin 0 (by decide)) fun s₁₁ u₁₁ =>
    wp_ldm (o := 4 * 1) (B := s₀.gpr .ebp) (by rw [u₁₁.other _ (by decide), e₁₀])
    (by rw [u₁₁.rd, u₁₁.wr]; exact rin 1 (by decide)) fun s₁₂ u₁₂ => WP.block_nil ?_
  refine ⟨⟨by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.ebp,
    by rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide)]; exact same₁₀.esp,
    by rw [u₁₂.rd, u₁₁.rd]; exact same₁₀.rd, by rw [u₁₂.wr, u₁₁.wr]; exact same₁₀.wr,
    by rw [u₁₂.mem, u₁₁.mem]; exact same₁₀.frame⟩, ?_, ?_⟩
  · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), k₁₀ .esi (by simp [kept]), u₉.gpr, h₈.esi,
      show 8 * kpos 3 0 = 504 from rfl, show (504 : BitVec 32) = BitVec.ofNat 32 504 from rfl, BitVec.add_sub_cancel]
  · have sl₁₀ : ∀ k, slotW s₁₀ k = s₁₀.mem.readW (wordAddr (s₀.gpr .ebp) k) 32 := fun k => by rw [slotW, e₁₀]
    have sl₉ : ∀ k, slotW s₉ k = slotW s₈ k := fun k => by rw [slotW, slotW, u₉.mem, u₉.other _ (by decide)]
    rw [u₁₂.other _ (by decide), u₁₁.gpr, u₁₂.gpr, u₁₁.mem, ← sl₁₀, ← sl₁₀, fp₁₀, sl₉, sl₉, tdes_eq, ← h₈.halves]

end VG.Proof.CmacTripleDes.X86
