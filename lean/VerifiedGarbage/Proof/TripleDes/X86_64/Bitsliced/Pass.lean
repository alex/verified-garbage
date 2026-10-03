import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Round

/-!
# A bitsliced DES pass on the machine

A pass chooses its first key's address and the step between keys by the
pass count (`passStart`), runs eight pairs of rounds (the loop counts them in
`roundSlot`), exchanges the halves and counts the pass (`passEnd`).
`pass_ok`: it does to the state words what `swapW (pairs …)` does, with the
keys read at the addresses `a₀ + r δ`, which are apart from the scratch
buffer.
-/

namespace VG.Proof.TripleDes.X86_64.Bitsliced

open VG VG.X86_64 VG.X86_64.Straight VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.Bitslice
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner)

/-- Eight readable bytes, apart from the scratch buffer. -/
structure Apart (s : State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (scratchR s)

theorem Apart.congr {s s' : State} {a : Addr} (h : Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [scratchR, hc]; exact h.scratch

theorem Apart.readW {s : State} {a : Addr} (h : Apart s a) {m : Mem}
    (hf : Frame [scratchR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using h.scratch) (by decide)

/-! ## Counting down a slot -/

def decCode (k : Nat) : List Instr := [ld .rax k, .alu .sub .rax (.imm 1), st k .rax]

theorem decCode_ok {s : State} (h : Room s) {k : Nat} (hk : k < 128) :
    ∃ s', runBlock isa (decCode k) s = some s' ∧ sl s' k = sl s k - 1 ∧
      s'.zf = some (sl s k - 1 == 0) ∧ (∀ x < 128, x ≠ k → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let v := sl s k
  let s₁ := s.setReg .rax v
  have e₁ : exec (ld .rax k) s = some s₁ := exec_ld h hk .rax
  let r := v - (1 : BitVec 32).signExtend 64
  let s₂ := (arithFlags s₁ r (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) r)).setReg .rax r
  have e₂ : exec (.alu .sub .rax (.imm 1)) s₁ = some s₂ := by
    simp only [exec, execAlu, readSrc, Option.bind_some]
    simp only [s₁, gpr_setReg_self]; rfl
  have h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg])
    (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  have e₃ := exec_st (r := Reg.rax) h₂ hk
  have hr : r = v - 1 := rfl
  have rcx₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  have mem₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have sl₃ : ∀ x < 128, (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 =
      if x = k then v - 1 else sl s x := by
    intro x hx
    rw [readW_stMem s₂ hk _ hx]
    simp only [s₂, gpr_setReg_self, ← hr]
    rfl
  refine ⟨{ s₂ with mem := stMem s₂ k (s₂.gpr .rax) }, ?_, ?_, ?_, fun x hx hne => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [decCode, runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_nil]
  · change (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) k) 64 = _
    rw [sl₃ k hk]; simp; rfl
  · simp only [s₂, zf_setReg, zf_arithFlags]; rfl
  · change (stMem s₂ k (s₂.gpr .rax)).readW (wordAddr (s₂.gpr .rcx) x) 64 = _
    rw [sl₃ x hx]; simp [hne]
  · simp [s₂, s₁, rd_setReg, rd_arithFlags]
  · simp [s₂, s₁, wr_setReg, wr_arithFlags]
  · exact rcx₂
  · simp [s₂, s₁, gpr_setReg]
  · have f := stMem_frame (s := s₂) hk (s₂.gpr .rax)
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, rcx₂], mem₂] at f
    exact f

/-! ## A pair of rounds -/

theorem roundW_congr {w : Nat} (ρ : Role) (k : BitVec 48) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, roundW ρ k W x = roundW ρ k W' x :=
  VG.Proof.TripleDes.Bitslice.steps_congr ρ k (Nat.le_refl 8) hW

theorem roundPair_eq : roundPair = round .ba ++ round .ab ++ decCode roundSlot := rfl

theorem roundPair_ok {s : State} (h : Room s) (h₁ : Apart s (sl s keySlot))
    (h₂ : Apart s (sl s keySlot + sl s stepSlot)) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (sl s keySlot + sl s stepSlot) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (sl s keySlot) 64).setWidth 48) (words s)) x) ∧
      sl s' keySlot = sl s keySlot + sl s stepSlot + sl s stepSlot ∧
      sl s' roundSlot = sl s roundSlot - 1 ∧ s'.zf = some (sl s roundSlot - 1 == 0) ∧
      (∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s' x = sl s x) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, key₁, misc₁, rd₁, wr₁, c₁, sp₁, f₁⟩ := round_ok .ba h h₁.read
  have g₁ := h.congr c₁ wr₁
  have step₁ : sl s₁ stepSlot = sl s stepSlot := misc₁ _ (by decide) (by decide) (by decide)
  have hk₁ : sl s₁ keySlot = sl s keySlot + sl s stepSlot := key₁
  have a₂ : Apart s₁ (sl s₁ keySlot) := by rw [hk₁]; exact h₂.congr c₁ rd₁ wr₁
  obtain ⟨s₂, run₂, w₂, key₂, misc₂, rd₂, wr₂, c₂, sp₂, f₂⟩ := round_ok .ab g₁ a₂.read
  have g₂ := g₁.congr c₂ wr₂
  obtain ⟨s₃, run₃, cnt₃, zf₃, sl₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := decCode_ok g₂ (by decide : roundSlot < 128)
  have kread : s₁.mem.readW (sl s keySlot + sl s stepSlot) 64 =
      s.mem.readW (sl s keySlot + sl s stepSlot) 64 := h₂.readW f₁
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, ?_, fun x hx hlo hk hr => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), c₃.trans (c₂.trans c₁), sp₃.trans (sp₂.trans sp₁), ?_⟩
  · rw [roundPair_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · simp only [words]
    rw [sl₃ _ (by unfold stSlot; omega) (by unfold stSlot roundSlot; omega)]
    rw [show sl s₂ (stSlot x) = words s₂ x from rfl, w₂ x hx, hk₁, kread]
    exact roundW_congr .ab _ w₁ x hx
  · rw [sl₃ keySlot (by decide) (by decide), key₂, hk₁, step₁]
  · rw [cnt₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [zf₃, misc₂ _ (by decide) (by decide) (by decide), misc₁ _ (by decide) (by decide) (by decide)]
  · rw [sl₃ x hx hr, misc₂ x hx hlo hk, misc₁ x hx hlo hk]
  · rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂, c₁]] at f₃
    exact f₁.trans (f₂.trans f₃)

/-! ## The loop of pairs of rounds -/

theorem cnt_sub (m : Nat) (h : 1 ≤ m) : BitVec.ofNat 64 m - 1 = BitVec.ofNat 64 (m - 1) := by
  have e : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl
  rw [e, BitVec.ofNat_sub_ofNat_of_le _ _ (by decide) h]

/-- The keys of a pass: the low 48 bits of the words at `a₀ + r δ`. -/
def keyAt (m : Mem) (a₀ δ : Addr) (r : Nat) : BitVec 48 :=
  (m.readW (a₀ + BitVec.ofNat 64 r * δ) 64).setWidth 48

theorem kptr_succ (a₀ δ : Addr) (r : Nat) :
    a₀ + BitVec.ofNat 64 r * δ + δ = a₀ + BitVec.ofNat 64 (r + 1) * δ := by
  rw [BitVec.add_assoc, BitVec.ofNat_add, BitVec.add_mul]
  simp

theorem pairs_congr {w : Nat} (key : Nat → BitVec 48) (n : Nat) {W W' : Nat → BitVec w}
    (hW : ∀ x < 64, W x = W' x) : ∀ x < 64, pairs key n W x = pairs key n W' x := by
  induction n with
  | zero => exact hW
  | succ n ih =>
    intro x hx
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ ih) x hx

structure LoopInv (s₀ : State) (m : Nat) (s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (sl s₀ keySlot) (sl s₀ stepSlot)) (8 - m) (words s₀) x
  key : sl s keySlot = sl s₀ keySlot + BitVec.ofNat 64 (2 * (8 - m)) * sl s₀ stepSlot
  cnt : sl s roundSlot = BitVec.ofNat 64 m
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : State) : Prop where
  room : Room s
  rcx : s.gpr .rcx = s₀.gpr .rcx
  rsp : s.gpr .rsp = s₀.gpr .rsp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (sl s₀ keySlot) (sl s₀ stepSlot)) 8 (words s₀) x
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s x = sl s₀ x
  frame : Frame [scratchR s₀] s₀.mem s.mem

theorem pairLoop_ok {s₀ : State} (hk : ∀ r < 16,
      Apart s₀ (sl s₀ keySlot + BitVec.ofNat 64 r * sl s₀ stepSlot))
    (m₀ : Nat) (s₁ : State) (hs₁ : LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block roundPair) .ne) s₁ (LoopPost s₀) := by
  refine WP.loop (M := isa) (LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := sl s₀ keySlot
  let δ := sl s₀ stepSlot
  have hδ : sl s stepSlot = δ := hs.misc _ (by decide) (by decide) (by decide) (by decide)
  have n16 : 2 * (8 - m) + 1 < 16 := by have := hs.pos; omega
  have a₁ : Apart s (sl s keySlot) := by
    rw [hs.key]; exact (hk _ (by omega)).congr hs.rcx hs.rd hs.wr
  have a₂ : Apart s (sl s keySlot + sl s stepSlot) := by
    rw [hs.key, hδ, kptr_succ]; exact (hk _ n16).congr hs.rcx hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', misc', rd', wr', c', sp', f'⟩ := roundPair_ok hs.room a₁ a₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : Frame [scratchR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show scratchR s = scratchR s₀ by simp only [scratchR, hs.rcx]] at f'
    exact this.trans f'
  have k1 : (s.mem.readW (sl s keySlot) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m)) := by
    rw [hs.key]; simp only [keyAt]
    rw [((hk _ (by omega)).readW hs.frame)]
  have k2 : (s.mem.readW (sl s keySlot + sl s stepSlot) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m) + 1) := by
    rw [hs.key, hδ, kptr_succ]; simp only [keyAt]
    rw [((hk _ n16).readW hs.frame)]
  have words' : ∀ x < 64, words s' x = pairs (keyAt s₀.mem a₀ δ) (8 - m + 1) (words s₀) x := by
    intro x hx
    rw [w' x hx, k1, k2]
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ hs.words) x hx
  have misc'' : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → sl s' x = sl s₀ x :=
    fun x hx hlo hk hr => (misc' x hx hlo hk hr).trans (hs.misc x hx hlo hk hr)
  have room' := hs.room.congr c' wr'
  have cntv : sl s roundSlot - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact cnt_sub m hs.pos
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd, wr'.trans hs.wr,
      words', misc'', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega, ⟨room', c'.trans hs.rcx, sp'.trans hs.rsp, rd'.trans hs.rd,
      wr'.trans hs.wr, by omega, by have := hs.le; omega, ?_, ?_, ?_, misc'', frame'⟩⟩
    · show s'.zf.map (!·) = some true
      rw [zf', cntv]
      have : (BitVec.ofNat 64 (m - 1) == 0) = false := by
        have hm : m ≤ 8 := hs.le
        simp only [beq_eq_false_iff_ne, ne_eq]
        intro h0
        have := congrArg BitVec.toNat h0
        have z : (0 : BitVec 64).toNat = 0 := rfl
        simp only [BitVec.toNat_ofNat] at this
        rw [z, Nat.mod_eq_of_lt (by omega)] at this
        have := hs.pos
        omega
      rw [this]; rfl
    · have e : 8 - (m - 1) = 8 - m + 1 := by have := hs.le; omega
      rw [e]; exact words'
    · rw [key', hs.key, hδ, kptr_succ, kptr_succ]
      congr 3
      have := hs.le; omega
    · rw [cnt', cntv]

/-! ## The start of a pass -/

/-- Point at a pass's first key (`a` past the schedule), with step `b`. -/
theorem passKeyCode_ok {s : State} (h : Room s) (a b : BitVec 32) :
    ∃ s', runBlock isa [ld .rdx schedSlot, .alu .add .rdx (.imm a), st keySlot .rdx,
        .mov .rdx (.imm b), st stepSlot .rdx] s = some s' ∧
      sl s' keySlot = sl s schedSlot + a.signExtend 64 ∧ sl s' stepSlot = b.signExtend 64 ∧
      (∀ x < 128, x ≠ keySlot → x ≠ stepSlot → sl s' x = sl s x) ∧ s'.gpr .rax = s.gpr .rax ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr .rcx = s.gpr .rcx ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Frame [scratchR s] s.mem s'.mem := by
  let v := sl s schedSlot
  let s₁ := s.setReg .rdx v
  have e₁ : exec (ld .rdx schedSlot) s = some s₁ := exec_ld h (by decide) .rdx
  have e₂ := exec_addImm s₁ .rdx a
  let w := s₁.gpr .rdx + a.signExtend 64
  let s₂ := (arithFlags s₁ w (decide (2 ^ 64 ≤ (s₁.gpr .rdx).toNat + (a.signExtend 64).toNat))
      (addOverflow (s₁.gpr .rdx) (a.signExtend 64) w)).setReg .rdx w
  have h₂ : Room s₂ := h.congr (by simp [s₂, s₁, gpr_setReg]) (by simp [s₂, s₁, wr_setReg, wr_arithFlags])
  have e₃ := exec_st (r := Reg.rdx) h₂ (by decide : keySlot < 128)
  let s₃ : State := { s₂ with mem := stMem s₂ keySlot (s₂.gpr .rdx) }
  have e₄ := exec_movImm s₃ .rdx b
  let s₄ := s₃.setReg .rdx (b.signExtend 64)
  have h₄ : Room s₄ := h₂.congr (by simp [s₄, s₃, gpr_setReg]) (by simp [s₄, s₃, wr_setReg])
  have e₅ := exec_st (r := Reg.rdx) h₄ (by decide : stepSlot < 128)
  let s₅ : State := { s₄ with mem := stMem s₄ stepSlot (s₄.gpr .rdx) }
  have c₂ : s₂.gpr .rcx = s.gpr .rcx := by simp [s₂, s₁, gpr_setReg]
  have m₂ : s₂.mem = s.mem := by simp [s₂, s₁, mem_setReg, mem_arithFlags]
  have sl₅ : ∀ x < 128, sl s₅ x = if x = stepSlot then b.signExtend 64 else
      if x = keySlot then v + a.signExtend 64 else sl s x := by
    intro x hx
    have a₅ := sl_st s₄ (by decide : stepSlot < 128) (s₄.gpr .rdx) hx
    have a₃ := sl_st s₂ (by decide : keySlot < 128) (s₂.gpr .rdx) hx
    change sl { s₄ with mem := stMem s₄ stepSlot (s₄.gpr .rdx) } x = _
    rw [a₅]
    simp only [s₄, sl_setReg _ (by decide : Reg.rdx ≠ .rcx), gpr_setReg_self]
    split
    · rfl
    · change sl { s₂ with mem := stMem s₂ keySlot (s₂.gpr .rdx) } x = _
      rw [a₃]
      split
      · simp [s₂, s₁, gpr_setReg, w, v]
      · simp only [sl, m₂, c₂]
  refine ⟨s₅, ?_, ?_, ?_, fun x hx a b => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [runBlock_cons, e₁, runStep_some, runBlock_cons, e₂, runStep_some, runBlock_cons, e₃,
      runStep_some, runBlock_cons, e₄, runStep_some, runBlock_cons, e₅, runStep_some, runBlock_nil]
  · rw [sl₅ _ (by decide)]; rfl
  · rw [sl₅ _ (by decide)]; rfl
  · rw [sl₅ x hx]; simp [a, b]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · simp [s₅, s₄, s₃, s₂, s₁, rd_setReg, rd_arithFlags]
  · simp [s₅, s₄, s₃, s₂, s₁, wr_setReg, wr_arithFlags]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · simp [s₅, s₄, s₃, s₂, s₁, gpr_setReg]
  · have f₃ := stMem_frame (s := s₂) (by decide : keySlot < 128) (s₂.gpr .rdx)
    have f₅ := stMem_frame (s := s₄) (by decide : stepSlot < 128) (s₄.gpr .rdx)
    rw [show scratchR s₂ = scratchR s by simp only [scratchR, c₂], m₂] at f₃
    rw [show scratchR s₄ = scratchR s by simp [scratchR, s₄, s₃, gpr_setReg, c₂]] at f₅
    exact f₃.trans f₅

/-- The comparison of `rax` with an immediate. -/
theorem cmp_run (s : State) (v : BitVec 32) :
    runBlock isa [.alu .cmp .rax (.imm v)] s = some (arithFlags s (s.gpr .rax - v.signExtend 64)
      (decide ((s.gpr .rax).toNat < (v.signExtend 64).toNat))
      (subOverflow (s.gpr .rax) (v.signExtend 64) (s.gpr .rax - v.signExtend 64))) := by
  rw [runBlock_cons]
  rfl

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  key : sl s' keySlot = sl s schedSlot + BitVec.ofNat 64 (passKey d p).1
  step : sl s' stepSlot = BitVec.ofInt 64 (passKey d p).2
  round : sl s' roundSlot = 8
  misc : ∀ x < 128, x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → sl s' x = sl s x
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  frame : Frame [scratchR s] s.mem s'.mem

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : sl s passSlot = BitVec.ofNat 64 p) :
    WP isa (passStart d) s (StartPost d p s) := by
  -- the code of a branch, and what follows it
  have branch : ∀ (s₁ : State), Room s₁ → (∀ x < 128, sl s₁ x = sl s x) → s₁.gpr .rcx = s.gpr .rcx →
      s₁.gpr .rsp = s.gpr .rsp → s₁.rd = s.rd → s₁.wr = s.wr → Frame [scratchR s] s.mem s₁.mem →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .rax (.imm 8), st roundSlot .rax]) s₂ (StartPost d p s)) := by
    intro s₁ h₁ sl₁ c₁ sp₁ rd₁ wr₁ f₁
    obtain ⟨s₂, run₂, key₂, step₂, misc₂, -, rd₂, wr₂, c₂, sp₂, f₂⟩ :=
      passKeyCode_ok h₁ (BitVec.ofNat 32 (passKey d p).1) (BitVec.ofInt 32 (passKey d p).2)
    refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
    have h₂ := h₁.congr c₂ wr₂
    have e₃ := exec_movImm s₂ .rax 8
    let s₃ := s₂.setReg .rax ((8 : BitVec 32).signExtend 64)
    have h₃ : Room s₃ := h₂.congr (by simp [s₃, gpr_setReg]) (by simp [s₃, wr_setReg])
    have e₄ := exec_st (r := Reg.rax) h₃ (by decide : roundSlot < 128)
    refine WP.of_runBlock ⟨{ s₃ with mem := stMem s₃ roundSlot (s₃.gpr .rax) }, ?_, ?_⟩
    · rw [runBlock_cons, e₃, runStep_some, runBlock_cons, e₄, runStep_some, runBlock_nil]
    have sl₄ : ∀ x < 128, sl { s₃ with mem := stMem s₃ roundSlot (s₃.gpr .rax) } x =
        if x = roundSlot then 8 else sl s₂ x := by
      intro x hx
      rw [sl_st s₃ (by decide) _ hx]
      simp only [s₃, sl_setReg _ (by decide : Reg.rax ≠ .rcx), gpr_setReg_self]
      split <;> rfl
    obtain ⟨i1, i2⟩ := passKey_imm d p hp.1 hp.2
    refine ⟨h₃.congr rfl rfl, ?_, ?_, ?_, fun x hx a b c => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sl₄ _ (by decide)]; simp only [show keySlot ≠ roundSlot by decide, ite_false]
      rw [key₂, sl₁ _ (by decide), i1]
    · rw [sl₄ _ (by decide)]; simp only [show stepSlot ≠ roundSlot by decide, ite_false]
      rw [step₂, i2]
    · rw [sl₄ _ (by decide)]; rfl
    · rw [sl₄ x hx]; simp only [c, ite_false]; rw [misc₂ x hx a b, sl₁ x hx]
    · simp [s₃, rd_setReg, rd₂, rd₁]
    · simp [s₃, wr_setReg, wr₂, wr₁]
    · simp [s₃, gpr_setReg, c₂, c₁]
    · simp [s₃, gpr_setReg, sp₂, sp₁]
    · have f := stMem_frame (s := s₃) (by decide : roundSlot < 128) (s₃.gpr .rax)
      rw [show scratchR s₃ = scratchR s by simp [scratchR, s₃, gpr_setReg, c₂, c₁]] at f
      rw [show scratchR s₁ = scratchR s by simp only [scratchR, c₁]] at f₂
      exact f₁.trans (f₂.trans f)
  -- load the count and compare it with 3
  let s₁ := s.setReg .rax (BitVec.ofNat 64 p)
  have e₁ : exec (ld .rax passSlot) s = some s₁ := by rw [exec_ld h (by decide) .rax, hc]
  let t₁ := arithFlags s₁ (s₁.gpr .rax - (3 : BitVec 32).signExtend 64)
    (decide ((s₁.gpr .rax).toNat < ((3 : BitVec 32).signExtend 64).toNat))
    (subOverflow (s₁.gpr .rax) ((3 : BitVec 32).signExtend 64) (s₁.gpr .rax - (3 : BitVec 32).signExtend 64))
  have hrun₁ : runBlock isa [ld .rax passSlot, .alu .cmp .rax (.imm 3)] s = some t₁ := by
    rw [runBlock_cons, e₁, runStep_some, cmp_run]
  have ht₁ : Room t₁ := h.congr (by simp [t₁, s₁, gpr_setReg])
    (by simp [t₁, s₁, wr_setReg, wr_arithFlags])
  have sl₁ : ∀ x < 128, sl t₁ x = sl s x := by
    intro x _; simp only [t₁, sl_arithFlags, s₁, sl_setReg _ (by decide : Reg.rax ≠ .rcx)]
  have c₁ : t₁.gpr .rcx = s.gpr .rcx := by simp [t₁, s₁, gpr_setReg]
  have sp₁ : t₁.gpr .rsp = s.gpr .rsp := by simp [t₁, s₁, gpr_setReg]
  have rd₁ : t₁.rd = s.rd := by simp [t₁, s₁, rd_setReg, rd_arithFlags]
  have wr₁ : t₁.wr = s.wr := by simp [t₁, s₁, wr_setReg, wr_arithFlags]
  have f₁ : Frame [scratchR s] s.mem t₁.mem := by
    simp only [t₁, s₁, mem_setReg, mem_arithFlags]; exact Frame.refl _ _
  have rax₁ : t₁.gpr .rax = BitVec.ofNat 64 p := by simp [t₁, s₁, gpr_setReg]
  apply WP.seq
  refine WP.of_runBlock ⟨t₁, hrun₁, ?_⟩
  apply WP.seq
  have zf₁ : isa.eval .e t₁ = some (p == 3) := by
    show t₁.zf = _
    simp only [t₁, zf_arithFlags, s₁, gpr_setReg_self]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    have : p = 3 := by simpa using h3
    subst this
    exact branch t₁ ht₁ sl₁ c₁ sp₁ rd₁ wr₁ f₁
  · intro h3
    have hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := arithFlags t₁ (t₁.gpr .rax - (2 : BitVec 32).signExtend 64)
      (decide ((t₁.gpr .rax).toNat < ((2 : BitVec 32).signExtend 64).toNat))
      (subOverflow (t₁.gpr .rax) ((2 : BitVec 32).signExtend 64) (t₁.gpr .rax - (2 : BitVec 32).signExtend 64))
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ 2, ?_⟩
    have ht₂ : Room t₂ := ht₁.congr (by simp [t₂]) (by simp [t₂, wr_arithFlags])
    have zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, zf_arithFlags, rax₁]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have sl₂ : ∀ x < 128, sl t₂ x = sl s x := fun x hx => by simp only [t₂, sl_arithFlags]; exact sl₁ x hx
    have c₂ : t₂.gpr .rcx = s.gpr .rcx := by simp only [t₂, gpr_arithFlags, c₁]
    have sp₂ : t₂.gpr .rsp = s.gpr .rsp := by simp only [t₂, gpr_arithFlags, sp₁]
    have rd₂ : t₂.rd = s.rd := by simp only [t₂, rd_arithFlags, rd₁]
    have wr₂ : t₂.wr = s.wr := by simp only [t₂, wr_arithFlags, wr₁]
    have f₂ : Frame [scratchR s] s.mem t₂.mem := by simp only [t₂, mem_arithFlags]; exact f₁
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega
      subst this
      exact branch t₂ ht₂ sl₂ c₂ sp₂ rd₂ wr₂ f₂

/-! ## A pass -/

theorem passEnd_eq : passEnd = decCode passSlot := rfl

theorem pairs_keys_congr {w : Nat} {key key' : Nat → BitVec 48} (n : Nat)
    (hk : ∀ r < 2 * n, key r = key' r) (W : Nat → BitVec w) : pairs key n W = pairs key' n W := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pairs]
    rw [ih (fun r hr => hk r (by omega)), hk (2 * n) (by omega), hk (2 * n + 1) (by omega)]

theorem partner_lt : ∀ k < 128, ∀ y, partner k = some y → y < 64 := by
  intro k hk y h
  have key : ∀ k < 128, (partner k).all (· < 64) = true := by decide +kernel
  have := key k hk
  rw [h] at this
  simpa using this

theorem swapW_congr {w : Nat} {W W' : Nat → BitVec w} (hW : ∀ y < 64, W y = W' y) :
    ∀ x < 64, swapW W x = swapW W' x := by
  intro x hx
  simp only [swapW]
  rcases hp : partner x with _ | y
  · exact hW x hx
  · exact hW y (partner_lt x (by omega) y hp)

/-- The first key of pass `p` (counted down from 3) and its step. -/
def passA (d : Spec.TripleDes.Direction) (p : Nat) (sched : Addr) : Addr :=
  sched + BitVec.ofNat 64 (passKey d p).1
def passD (d : Spec.TripleDes.Direction) (p : Nat) : Addr := BitVec.ofInt 64 (passKey d p).2

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  rcx : s'.gpr .rcx = s.gpr .rcx
  rsp : s'.gpr .rsp = s.gpr .rsp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, words s' x =
    swapW (pairs (keyAt s.mem (passA d p (sl s schedSlot)) (passD d p)) 8 (words s)) x
  count : sl s' passSlot = sl s passSlot - 1
  zf : s'.zf = some (sl s passSlot - 1 == 0)
  misc : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ stepSlot → x ≠ roundSlot → x ≠ passSlot →
    sl s' x = sl s x
  frame : Frame [scratchR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : sl s passSlot = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, Apart s (passA d p (sl s schedSlot) + BitVec.ofNat 64 r * passD d p)) :
    WP isa (pass d) s (PassPost d p s) := by
  apply WP.seq
  apply WP.mono (passStart_ok d hp h hc)
  intro s₁ p₁
  have h₁ := p₁.room
  apply WP.seq
  have hk₁ : ∀ r < 16, Apart s₁ (sl s₁ keySlot + BitVec.ofNat 64 r * sl s₁ stepSlot) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr p₁.rcx p₁.rd p₁.wr
  have inv : LoopInv s₁ 8 s₁ := by
    refine ⟨h₁, rfl, rfl, rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_,
      fun _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (pairLoop_ok hk₁ 8 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, hi₃, rd₃, wr₃, c₃, sp₃, f₃⟩ := swapHalves_ok h₂
  have h₃ := h₂.congr c₃ wr₃
  obtain ⟨s₄, run₄, cnt₄, zf₄, misc₄, rd₄, wr₄, c₄, sp₄, f₄⟩ := decCode_ok h₃ (by decide : passSlot < 128)
  refine WP.of_runBlock ⟨s₄, by rw [passEnd_eq]; exact runBlock_cat_some run₃ run₄, ?_⟩
  have keys : ∀ r < 16, keyAt s₁.mem (sl s₁ keySlot) (sl s₁ stepSlot) r =
      keyAt s.mem (passA d p (sl s schedSlot)) (passD d p) r := by
    intro r hr
    simp only [keyAt, p₁.key, p₁.step]
    have e := (hk r hr).readW p₁.frame
    simp only [passA, passD] at e
    rw [e]; rfl
  have state₁ : ∀ x < 64, words s₁ x = words s x := fun x hx =>
    p₁.misc _ (by unfold stSlot; omega) (by unfold stSlot keySlot; omega)
      (by unfold stSlot stepSlot; omega) (by unfold stSlot roundSlot; omega)
  have high : ∀ x < 128, 72 ≤ x → x ≠ keySlot → x ≠ roundSlot → x ≠ passSlot →
      sl s₄ x = sl s₁ x := by
    intro x hx hlo hkx hrx hpx
    rw [misc₄ x hx hpx, hi₃ x hx hlo, p₂.misc x hx hlo hkx hrx]
  have pass₁ : sl s₁ passSlot = sl s passSlot := p₁.misc _ (by decide) (by decide) (by decide) (by decide)
  have pass₃ : sl s₃ passSlot = sl s passSlot := by
    rw [hi₃ _ (by decide) (by decide), p₂.misc _ (by decide) (by decide) (by decide) (by decide), pass₁]
  refine ⟨h₃.congr c₄ wr₄, c₄.trans (c₃.trans (p₂.rcx.trans p₁.rcx)),
    sp₄.trans (sp₃.trans (p₂.rsp.trans p₁.rsp)), rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun x hx hlo a b c e => ?_, ?_⟩
  · simp only [words]
    rw [misc₄ _ (by unfold stSlot; omega) (by unfold stSlot passSlot; omega)]
    rw [show sl s₃ (stSlot x) = words s₃ x from rfl, sw₃ x hx]
    apply swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    exact pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, pass₃]
  · rw [zf₄, pass₃]
  · rw [high x hx hlo a c e]
    exact p₁.misc x hx a b c
  · have g₃ : Frame [scratchR s] s₂.mem s₃.mem := by
      rwa [show scratchR s₂ = scratchR s by simp only [scratchR, p₂.rcx, p₁.rcx]] at f₃
    have g₄ : Frame [scratchR s] s₃.mem s₄.mem := by
      rwa [show scratchR s₃ = scratchR s by simp only [scratchR, c₃, p₂.rcx, p₁.rcx]] at f₄
    have g₂ := p₂.frame
    rw [show scratchR s₁ = scratchR s by simp only [scratchR, p₁.rcx]] at g₂
    exact p₁.frame.trans (g₂.trans (g₃.trans g₄))

end VG.Proof.TripleDes.X86_64.Bitsliced
