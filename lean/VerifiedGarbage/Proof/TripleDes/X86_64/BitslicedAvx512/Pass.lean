import VerifiedGarbage.Proof.TripleDes.X86_64.BitslicedAvx512.Round
import VerifiedGarbage.Proof.TripleDes.X86_64.Bitsliced.Keys

/-!
# An AVX-512 DES pass on the machine

A pass chooses its first key's address (`r8`) and the step between keys
(`r9`) by the pass count (`r11`, `passStart`), runs eight pairs of rounds
(counted in `r10`), exchanges the halves and counts the pass. `pass_ok`: it
does to the state words what `swapW (pairs …)` does, with the keys read at
the addresses `a₀ + r δ`, which are apart from the scratch buffer and the
state words.
-/

namespace VG.Proof.TripleDes.X86_64.BitslicedAvx512

open VG VG.X86_64 VG.X86_64.StraightZ VG.X86_64.RegUpd VG.Impl.TripleDes.X86_64.BitsliceAvx512
open VG.Impl.TripleDes.Bitslice
open VG.Proof.TripleDes.Bitslice (roundW pairs swapW partner)
open VG.Proof.TripleDes.X86_64.Bitsliced (keyAt kptr_succ cnt_sub passA passD roundW_congr pairs_congr
  pairs_keys_congr swapW_congr)
open VG.Impl.TripleDes.X86_64.Bitslice (passKey)

/-- Eight readable bytes, apart from the scratch buffer and the state words. -/
structure Apart (s : State) (a : Addr) : Prop where
  read : InRegions (s.rd ++ s.wr) a 8
  scratch : (⟨a, 8⟩ : Region).Disjoint (scratchR s)
  state : (⟨a, 8⟩ : Region).Disjoint (stateR s)

theorem Apart.congr {s s' : State} {a : Addr} (h : Apart s a) (hc : s'.gpr .rcx = s.gpr .rcx)
    (hsi : s'.gpr .rsi = s.gpr .rsi) (hrd : s'.rd = s.rd) (hwr : s'.wr = s.wr) : Apart s' a where
  read := by rw [hrd, hwr]; exact h.read
  scratch := by simp only [scratchR, hc]; exact h.scratch
  state := by simp only [stateR, hsi]; exact h.state

theorem Apart.readW {s : State} {a : Addr} (h : Apart s a) {m : Mem}
    (hf : Frame [spillR s, stateR s] s.mem m) : m.readW a 64 = s.mem.readW a 64 :=
  hf.readW (Region.contains_self a 8) (by simpa using ⟨h.scratch.sub_right (spill_sub s), h.state⟩)
    (by decide)

/-! ## Counting down a register -/

theorem sub1_run (s : State) (r : Reg) :
    ∃ s', runBlock isa [.alu .sub r (.imm 1)] s = some s' ∧ s'.gpr r = s.gpr r - 1 ∧
      s'.zf = some (s.gpr r - 1 == 0) ∧ (∀ r', r' ≠ r → s'.gpr r' = s.gpr r') ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let v := s.gpr r
  let t := v - (1 : BitVec 32).signExtend 64
  refine ⟨(arithFlags s t (decide (v.toNat < ((1 : BitVec 32).signExtend 64).toNat))
    (subOverflow v ((1 : BitVec 32).signExtend 64) t)).setReg r t, ?_, ?_, ?_, fun r' h => ?_,
    ?_, ?_, ?_⟩
  · rw [runBlock_cons]; rfl
  · simp only [gpr_setReg_self]; rfl
  · simp only [zf_setReg, zf_arithFlags]; rfl
  · simp [gpr_setReg, h]
  · simp [mem_setReg, mem_arithFlags]
  · simp [rd_setReg, rd_arithFlags]
  · simp [wr_setReg, wr_arithFlags]

/-! ## A pair of rounds -/

theorem roundPair_eq : roundPair = round .ba ++ round .ab ++ ([.alu .sub .r10 (.imm 1)] : List Instr) :=
  rfl

theorem roundPair_ok {s : State} (h : Room s)
    (h₁ : Apart s (s.gpr .r8)) (h₂ : Apart s (s.gpr .r8 + s.gpr .r9)) :
    ∃ s', runBlock isa roundPair s = some s' ∧
      (∀ x < 64, words s' x = roundW .ab ((s.mem.readW (s.gpr .r8 + s.gpr .r9) 64).setWidth 48)
        (roundW .ba ((s.mem.readW (s.gpr .r8) 64).setWidth 48) (words s)) x) ∧
      s'.gpr .r8 = s.gpr .r8 + s.gpr .r9 + s.gpr .r9 ∧
      s'.gpr .r10 = s.gpr .r10 - 1 ∧ s'.zf = some (s.gpr .r10 - 1 == 0) ∧
      (∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [spillR s, stateR s] s.mem s'.mem := by
  obtain ⟨s₁, run₁, w₁, key₁, g₁, rd₁, wr₁, f₁⟩ := round_ok .ba h h₁.read
  have c₁ := g₁ .rcx (by decide) (by decide) (by decide)
  have si₁ := g₁ .rsi (by decide) (by decide) (by decide)
  have r9₁ := g₁ .r9 (by decide) (by decide) (by decide)
  have h₁' := h.congr c₁ si₁ wr₁
  have a₂ : Apart s₁ (s₁.gpr .r8) := by rw [key₁]; exact h₂.congr c₁ si₁ rd₁ wr₁
  obtain ⟨s₂, run₂, w₂, key₂, g₂, rd₂, wr₂, f₂⟩ := round_ok .ab h₁' a₂.read
  obtain ⟨s₃, run₃, cnt₃, zf₃, g₃, m₃, rd₃, wr₃⟩ := sub1_run s₂ .r10
  have kread : s₁.mem.readW (s.gpr .r8 + s.gpr .r9) 64 = s.mem.readW (s.gpr .r8 + s.gpr .r9) 64 :=
    h₂.readW f₁
  have r10₂ : s₂.gpr .r10 = s.gpr .r10 := by
    rw [g₂ _ (by decide) (by decide) (by decide), g₁ _ (by decide) (by decide) (by decide)]
  refine ⟨s₃, ?_, fun x hx => ?_, ?_, ?_, ?_, fun r a b c d => ?_, rd₃.trans (rd₂.trans rd₁),
    wr₃.trans (wr₂.trans wr₁), ?_⟩
  · rw [roundPair_eq]; exact runBlock_cat_some (runBlock_cat_some run₁ run₂) run₃
  · have e : words s₃ x = words s₂ x := by
      simp only [words, m₃, g₃ .rsi (by decide)]
    rw [e, w₂ x hx, key₁, kread]
    exact roundW_congr .ab _ w₁ x hx
  · rw [g₃ _ (by decide), key₂, key₁, r9₁]
  · rw [cnt₃, r10₂]
  · rw [zf₃, r10₂]
  · rw [g₃ r d, g₂ r a b c, g₁ r a b c]
  · have e₂ : Frame [spillR s, stateR s] s₁.mem s₂.mem := by
      rwa [show spillR s₁ = spillR s by simp only [spillR, c₁],
        show stateR s₁ = stateR s by simp only [stateR, si₁]] at f₂
    rw [m₃]
    exact f₁.trans e₂

/-! ## The loop of pairs of rounds -/

/-- The registers a pass changes. -/
def PassRegs (r : Reg) : Prop := r ≠ .rax ∧ r ≠ .rbx ∧ r ≠ .r8 ∧ r ≠ .r9 ∧ r ≠ .r10 ∧ r ≠ .r11

structure LoopInv (s₀ : State) (m : Nat) (s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  pos : 1 ≤ m
  le : m ≤ 8
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) (8 - m) (words s₀) x
  key : s.gpr .r8 = s₀.gpr .r8 + BitVec.ofNat 64 (2 * (8 - m)) * s₀.gpr .r9
  cnt : s.gpr .r10 = BitVec.ofNat 64 m
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

structure LoopPost (s₀ s : State) : Prop where
  room : Room s
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  words : ∀ x < 64, words s x = pairs (keyAt s₀.mem (s₀.gpr .r8) (s₀.gpr .r9)) 8 (words s₀) x
  gpr : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s.gpr r = s₀.gpr r
  frame : Frame [spillR s₀, stateR s₀] s₀.mem s.mem

theorem pairLoop_ok {s₀ : State} (hk : ∀ r < 16,
      Apart s₀ (s₀.gpr .r8 + BitVec.ofNat 64 r * s₀.gpr .r9))
    (m₀ : Nat) (s₁ : State) (hs₁ : LoopInv s₀ m₀ s₁) :
    WP isa (.loop (.block roundPair) .ne) s₁ (LoopPost s₀) := by
  refine WP.loop (M := isa) (LoopInv s₀) ?_ m₀ s₁ hs₁
  intro m s hs
  let a₀ := s₀.gpr .r8
  let δ := s₀.gpr .r9
  have hδ : s.gpr .r9 = δ := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hc : s.gpr .rcx = s₀.gpr .rcx := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have hsi : s.gpr .rsi = s₀.gpr .rsi := hs.gpr _ (by decide) (by decide) (by decide) (by decide)
  have n16 : 2 * (8 - m) + 1 < 16 := by have := hs.pos; omega
  have a₁ : Apart s (s.gpr .r8) := by
    rw [hs.key]; exact (hk _ (by omega)).congr hc hsi hs.rd hs.wr
  have a₂ : Apart s (s.gpr .r8 + s.gpr .r9) := by
    rw [hs.key, hδ, kptr_succ]; exact (hk _ n16).congr hc hsi hs.rd hs.wr
  obtain ⟨s', run', w', key', cnt', zf', g', rd', wr', f'⟩ := roundPair_ok hs.room a₁ a₂
  refine WP.of_runBlock ⟨s', run', ?_⟩
  have frame' : Frame [spillR s₀, stateR s₀] s₀.mem s'.mem := by
    have := hs.frame
    rw [show spillR s = spillR s₀ by simp only [spillR, hc],
      show stateR s = stateR s₀ by simp only [stateR, hsi]] at f'
    exact this.trans f'
  have k1 : (s.mem.readW (s.gpr .r8) 64).setWidth 48 = keyAt s₀.mem a₀ δ (2 * (8 - m)) := by
    rw [hs.key]; simp only [keyAt]
    rw [((hk _ (by omega)).readW hs.frame)]
  have k2 : (s.mem.readW (s.gpr .r8 + s.gpr .r9) 64).setWidth 48 =
      keyAt s₀.mem a₀ δ (2 * (8 - m) + 1) := by
    rw [hs.key, hδ, kptr_succ]; simp only [keyAt]
    rw [((hk _ n16).readW hs.frame)]
  have words' : ∀ x < 64, words s' x = pairs (keyAt s₀.mem a₀ δ) (8 - m + 1) (words s₀) x := by
    intro x hx
    rw [w' x hx, k1, k2]
    simp only [pairs]
    exact roundW_congr .ab _ (roundW_congr .ba _ hs.words) x hx
  have gpr' : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r10 → s'.gpr r = s₀.gpr r :=
    fun r a b c d => (g' r a b c d).trans (hs.gpr r a b c d)
  have room' := hs.room.congr (g' _ (by decide) (by decide) (by decide) (by decide))
    (g' _ (by decide) (by decide) (by decide) (by decide)) wr'
  have cntv : s.gpr .r10 - 1 = BitVec.ofNat 64 (m - 1) := by
    rw [hs.cnt]
    exact cnt_sub m hs.pos
  by_cases h1 : m = 1
  · subst h1
    left
    refine ⟨?_, ⟨room', rd'.trans hs.rd, wr'.trans hs.wr, words', gpr', frame'⟩⟩
    show s'.zf.map (!·) = some false
    rw [zf', cntv]; rfl
  · right
    refine ⟨?_, m - 1, by omega, ⟨room', rd'.trans hs.rd, wr'.trans hs.wr, by omega,
      by have := hs.le; omega, ?_, ?_, ?_, gpr', frame'⟩⟩
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

/-- What the start of a pass leaves. -/
structure StartPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  key : s'.gpr .r8 = s.gpr .rdi + BitVec.ofNat 64 (passKey d p).1
  step : s'.gpr .r9 = BitVec.ofInt 64 (passKey d p).2
  round : s'.gpr .r10 = 8
  gpr : ∀ r, r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s'.gpr r = s.gpr r
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem passKey_imm : ∀ d : Spec.TripleDes.Direction, ∀ p, 1 ≤ p → p ≤ 3 →
    (BitVec.ofNat 32 (passKey d p).1).signExtend 64 = BitVec.ofNat 64 (passKey d p).1 ∧
    (BitVec.ofInt 32 (passKey d p).2).signExtend 64 = BitVec.ofInt 64 (passKey d p).2 := by
  intro d p h1 h3
  cases d <;> (rcases p with _ | _ | _ | _ | p) <;> first | omega | decide

/-- A comparison of a register with an immediate. -/
def cmpState (s : State) (r : Reg) (v : BitVec 32) : State :=
  arithFlags s (s.gpr r - v.signExtend 64) (decide ((s.gpr r).toNat < (v.signExtend 64).toNat))
    (subOverflow (s.gpr r) (v.signExtend 64) (s.gpr r - v.signExtend 64))

theorem cmp_run (s : State) (r : Reg) (v : BitVec 32) :
    runBlock isa [.alu .cmp r (.imm v)] s = some (cmpState s r v) := by
  rw [runBlock_cons]
  rfl

theorem passStart_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (hc : s.gpr .r11 = BitVec.ofNat 64 p) :
    WP isa (passStart d) s (StartPost d p s) := by
  -- the code of a branch, and what follows it
  have branch : ∀ (s₁ : State), s₁.gpr = s.gpr → s₁.mem = s.mem → s₁.rd = s.rd → s₁.wr = s.wr →
      WP isa (.block (passKeyCode d p)) s₁ (fun s₂ =>
        WP isa (.block [.mov .r10 (.imm 8)]) s₂ (StartPost d p s)) := by
    intro s₁ g₁ m₁ rd₁ wr₁
    let t₁ := s₁.setReg .r8 (s₁.gpr .rdi)
    let a := BitVec.ofNat 32 (passKey d p).1
    let t₂ := (arithFlags t₁ (t₁.gpr .r8 + a.signExtend 64)
      (decide (2 ^ 64 ≤ (t₁.gpr .r8).toNat + (a.signExtend 64).toNat))
      (addOverflow (t₁.gpr .r8) (a.signExtend 64) (t₁.gpr .r8 + a.signExtend 64))).setReg .r8
      (t₁.gpr .r8 + a.signExtend 64)
    let t₃ := t₂.setReg .r9 ((BitVec.ofInt 32 (passKey d p).2).signExtend 64)
    refine WP.of_runBlock ⟨t₃, ?_, ?_⟩
    · rw [passKeyCode, runBlock_cons, show exec (.mov .r8 (.reg .rdi)) s₁ = some t₁ from rfl,
        runStep_some, runBlock_cons, show exec (.alu .add .r8 (.imm a)) t₁ = some t₂ from rfl,
        runStep_some, runBlock_cons, show exec (.mov .r9 (.imm (BitVec.ofInt 32 (passKey d p).2))) t₂ =
          some t₃ from rfl, runStep_some, runBlock_nil]
    let t₄ := t₃.setReg .r10 ((8 : BitVec 32).signExtend 64)
    refine WP.of_runBlock ⟨t₄, by rw [runBlock_cons]; rfl, ?_⟩
    obtain ⟨i1, i2⟩ := passKey_imm d p hp.1 hp.2
    refine ⟨?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_⟩
    · simp [t₄, t₃, t₂, t₁, gpr_setReg, g₁, a, i1]
    · simp [t₄, t₃, gpr_setReg, i2]
    · simp [t₄, gpr_setReg]
    · simp [t₄, t₃, t₂, t₁, gpr_setReg, a, b, c, g₁]
    · simp [t₄, t₃, t₂, t₁, mem_setReg, mem_arithFlags, m₁]
    · simp [t₄, t₃, t₂, t₁, rd_setReg, rd_arithFlags, rd₁]
    · simp [t₄, t₃, t₂, t₁, wr_setReg, wr_arithFlags, wr₁]
  apply WP.seq
  let t₁ := cmpState s .r11 3
  refine WP.of_runBlock ⟨t₁, cmp_run s .r11 3, ?_⟩
  apply WP.seq
  have zf₁ : isa.eval .e t₁ = some (p == 3) := by
    show t₁.zf = _
    simp only [t₁, cmpState, zf_arithFlags, hc]
    rcases hp with ⟨h1, h3⟩
    rcases p with _ | _ | _ | _ | p <;> first | omega | decide
  apply WP.ite (p == 3) zf₁
  · intro h3
    have : p = 3 := by simpa using h3
    subst this
    exact branch t₁ (by simp [t₁, cmpState]) (by simp [t₁, cmpState, mem_arithFlags])
      (by simp [t₁, cmpState, rd_arithFlags]) (by simp [t₁, cmpState, wr_arithFlags])
  · intro h3
    have hp3 : p ≠ 3 := by simpa using h3
    apply WP.seq
    let t₂ := cmpState t₁ .r11 2
    refine WP.of_runBlock ⟨t₂, cmp_run t₁ .r11 2, ?_⟩
    have zf₂ : isa.eval .e t₂ = some (p == 2) := by
      show t₂.zf = _
      simp only [t₂, t₁, cmpState, zf_arithFlags, gpr_arithFlags, hc]
      rcases hp with ⟨h1, h3⟩
      rcases p with _ | _ | _ | _ | p <;> first | omega | decide
    have g₂ : t₂.gpr = s.gpr := by simp [t₂, t₁, cmpState]
    have m₂ : t₂.mem = s.mem := by simp [t₂, t₁, cmpState, mem_arithFlags]
    have rd₂ : t₂.rd = s.rd := by simp [t₂, t₁, cmpState, rd_arithFlags]
    have wr₂ : t₂.wr = s.wr := by simp [t₂, t₁, cmpState, wr_arithFlags]
    apply WP.ite (p == 2) zf₂
    · intro h2
      have : p = 2 := by simpa using h2
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂
    · intro h2
      have : p = 1 := by have : p ≠ 2 := by simpa using h2
                         omega
      subst this
      exact branch t₂ g₂ m₂ rd₂ wr₂

/-! ## A pass -/

structure PassPost (d : Spec.TripleDes.Direction) (p : Nat) (s s' : State) : Prop where
  room : Room s'
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  words : ∀ x < 64, words s' x =
    swapW (pairs (keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p)) 8 (words s)) x
  count : s'.gpr .r11 = s.gpr .r11 - 1
  zf : s'.zf = some (s.gpr .r11 - 1 == 0)
  gpr : ∀ r, PassRegs r → s'.gpr r = s.gpr r
  frame : Frame [spillR s, stateR s] s.mem s'.mem

theorem pass_ok (d : Spec.TripleDes.Direction) {p : Nat} (hp : 1 ≤ p ∧ p ≤ 3) {s : State}
    (h : Room s) (hc : s.gpr .r11 = BitVec.ofNat 64 p)
    (hk : ∀ r < 16, Apart s (passA d p (s.gpr .rdi) + BitVec.ofNat 64 r * passD d p)) :
    WP isa (pass d) s (PassPost d p s) := by
  apply WP.seq
  apply WP.mono (passStart_ok d hp hc)
  intro s₁ p₁
  have c₁ := p₁.gpr .rcx (by decide) (by decide) (by decide)
  have si₁ := p₁.gpr .rsi (by decide) (by decide) (by decide)
  have h₁ := h.congr c₁ si₁ p₁.wr
  apply WP.seq
  have hk₁ : ∀ r < 16, Apart s₁ (s₁.gpr .r8 + BitVec.ofNat 64 r * s₁.gpr .r9) := by
    intro r hr
    rw [p₁.key, p₁.step]; exact (hk r hr).congr c₁ si₁ p₁.rd p₁.wr
  have inv : LoopInv s₁ 8 s₁ := by
    refine ⟨h₁, rfl, rfl, by decide, by decide, fun _ _ => rfl, ?_, ?_,
      fun _ _ _ _ _ => rfl, Frame.refl _ _⟩
    · simp
    · rw [p₁.round]; rfl
  apply WP.mono (pairLoop_ok hk₁ 8 s₁ inv)
  intro s₂ p₂
  have h₂ := p₂.room
  obtain ⟨s₃, run₃, sw₃, g₃, rd₃, wr₃, f₃⟩ := swapHalves_ok h₂
  obtain ⟨s₄, run₄, cnt₄, zf₄, g₄, m₄, rd₄, wr₄⟩ := sub1_run s₃ .r11
  refine WP.of_runBlock ⟨s₄, runBlock_cat_some run₃ run₄, ?_⟩
  have keys : ∀ r < 16, keyAt s₁.mem (s₁.gpr .r8) (s₁.gpr .r9) r =
      keyAt s.mem (passA d p (s.gpr .rdi)) (passD d p) r := by
    intro r hr
    simp only [keyAt, p₁.key, p₁.step, p₁.mem]
    rfl
  have state₁ : ∀ x < 64, words s₁ x = words s x := fun x _ => by simp only [words, p₁.mem, si₁]
  have gs₂ : ∀ r, r ≠ .rax → r ≠ .rbx → r ≠ .r8 → r ≠ .r9 → r ≠ .r10 → s₂.gpr r = s.gpr r :=
    fun r a b c e f => (p₂.gpr r a b c f).trans (p₁.gpr r c e f)
  have r11₃ : s₃.gpr .r11 = s.gpr .r11 := by
    rw [g₃, gs₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  have c₂ := gs₂ .rcx (by decide) (by decide) (by decide) (by decide) (by decide)
  have si₂ := gs₂ .rsi (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨h.congr (by rw [g₄ _ (by decide), g₃, c₂]) (by rw [g₄ _ (by decide), g₃, si₂])
      (wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr))),
    rd₄.trans (rd₃.trans (p₂.rd.trans p₁.rd)),
    wr₄.trans (wr₃.trans (p₂.wr.trans p₁.wr)), fun x hx => ?_, ?_, ?_,
    fun r hr => ?_, ?_⟩
  · have e : words s₄ x = words s₃ x := by simp only [words, m₄, g₄ .rsi (by decide)]
    rw [e, sw₃ x hx]
    apply swapW_congr _ x hx
    intro y hy
    rw [p₂.words y hy, pairs_keys_congr 8 (fun r hr => keys r (by omega))]
    exact pairs_congr _ 8 state₁ y hy
  · rw [cnt₄, r11₃]
  · rw [zf₄, r11₃]
  · obtain ⟨a, b, c, e, f, g⟩ := hr
    rw [g₄ r g, g₃, gs₂ r a b c e f]
  · have g₃' : Frame [spillR s, stateR s] s₂.mem s₃.mem := by
      refine f₃.sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨stateR s, List.mem_cons_of_mem _ List.mem_cons_self, by
        simp only [stateR, si₂]; exact fun _ h => h⟩
    have g₂ := p₂.frame
    rw [show spillR s₁ = spillR s by simp only [spillR, c₁],
      show stateR s₁ = stateR s by simp only [stateR, si₁], p₁.mem] at g₂
    rw [m₄]
    exact g₂.trans g₃'

end VG.Proof.TripleDes.X86_64.BitslicedAvx512
