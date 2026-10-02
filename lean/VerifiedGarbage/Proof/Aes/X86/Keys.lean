import VerifiedGarbage.Proof.Aes.X86.Encrypt
import VerifiedGarbage.Proof.Framework.Bitslice.Sym

/-!
# Bitslicing the round keys, on x86 (32-bit)

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as two
identical blocks) with `ortho` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `ortho` by its proof (`Linear.lean`), and the address
computations by symbolic execution.
-/

namespace VG.Proof.Aes.X86

open VG VG.X86 VG.X86.Straight VG.Bitslice VG.Impl.Aes.X86 VG.Proof.Aes VG.Proof.Aes.Ct32
open VG.Spec.Aes (roundKey)
open VG.X86.Wp (Upd Mupd Fupd wp_mov wp_movi wp_addi wp_add wp_addm wp_sub wp_subi wp_cmp wp_cmpi wp_test
  wp_bswap wp_ldm wp_xorm wp_stm sub_beq sub_ofNat toNat_ofNat_lt ofNat_pred ofNat_beq_zero)

/-! ## Loading a round key -/

/-- The loads and stores of `keyLoad`, after the address. -/
def loadMoves : List Instr :=
  (List.range 4).flatMap fun w => [.mov .ebx (.mem (at_ .eax (4 * w))), st (2 * w) .ebx, st (2 * w + 1) .ebx]

theorem keyLoad_eq : keyLoad = ([movR .eax .esi, addR .eax .eax, addR .eax .eax, addR .eax .eax,
    addR .eax .eax, .mov .ebx (.mem (argOp 0)), addR .eax .ebx] : List Instr) ++ loadMoves := rfl

def loadCfg : Cfg := { base := sb, slots := 8, ext := .eax, exts := 4 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun w => e.slot (2 * w) == some w && e.slot (2 * w + 1) == some w

theorem loadMoves_check :
    check (names 32) loadCfg (fun k => some k) loadMoves { reg := fun _ => none, slot := fun _ => none }
      loadPost = true := by
  decide +kernel

theorem loadMoves_ok {s : State} (hok : Ok loadCfg s) :
    ∃ s', runBlock isa loadMoves s = some s' ∧
      (∀ w < 4, Q s' (2 * w) = s.mem.readW (wordAddr (s.gpr .eax) w) 32 ∧
        Q s' (2 * w + 1) = s.mem.readW (wordAddr (s.gpr .eax) w) 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .ebx → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion loadCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ loadMoves_check
  let V : Nat → BitVec 32 := fun k => s.mem.readW (wordAddr (s.gpr .eax) k) 32
  have hrel : Rel (NameRel V) loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  have hb : s'.gpr sb = s.gpr sb := p.base
  refine ⟨s', hs', fun w hw => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost w (List.mem_range.mpr hw)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    have h1 := p.rel.slot _ _ (by simp [loadCfg]; omega) this.1
    have h2 := p.rel.slot _ _ (by simp [loadCfg]; omega) this.2
    simp only [NameRel, loadCfg, hb] at h1 h2
    exact ⟨by simp only [Q, hb]; exact h1, by simp only [Q, hb]; exact h2⟩
  · have : (loadMoves.all fun i => i.dst != some r) = true := by
      revert hr; cases r <;> decide
    simp [this]

/-! ## Storing it -/

/-- The loads and stores of `keyStore`, after the address. -/
def storeMoves : List Instr := (List.range 8).flatMap fun k => [movS .eax k, .store (at_ .ebx (4 * k)) .eax]

theorem keyStore_eq : keyStore = ([.mov .eax (.mem (argOp 1)), subR .eax .esi, addR .eax .eax,
    addR .eax .eax, addR .eax .eax, addR .eax .eax, addR .eax .eax, movR .ebx .edi,
    addI .ebx (BitVec.ofNat 32 lastKey), subR .ebx .eax] : List Instr) ++ storeMoves := rfl

def storeCfg : Cfg := { base := .ebx, slots := 8, ext := sb, exts := 8 }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem storeMoves_check :
    check (names 32) storeCfg (fun k => some k) storeMoves { reg := fun _ => none, slot := fun _ => none }
      storePost = true := by
  decide +kernel

theorem storeMoves_ok {s : State} (hok : Ok storeCfg s) :
    ∃ s', runBlock isa storeMoves s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .ebx) k) 32 = Q s k) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      Frame [slotRegion storeCfg s] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ storeMoves_check
  let V : Nat → BitVec 32 := fun k => Q s k
  have hrel : Rel (NameRel V) storeCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  have hb : s'.gpr .ebx = s.gpr .ebx := p.base
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, fun r hr => p.other r ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k (by simp [storeCfg]; omega) this
    simp only [NameRel, storeCfg, hb] at h
    exact h
  · have : (storeMoves.all fun i => i.dst != some r) = true := by
      revert hr; cases r <;> decide
    simp [this]

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `B`, the key schedule `w`
at `S` (as the bytes there), `rounds` and the schedule pointer the
arguments. -/
structure KSetup (s₀ : State) (B S : BitVec 32) (R : Nat) (w : List Byte) : Prop where
  scr : reg32 B 2048 ∈ s₀.wr
  fitB : B.toNat + 2048 ≤ 2 ^ 32
  sch : reg32 S 240 ∈ s₀.rd ++ s₀.wr
  fitS : S.toNat + 240 ≤ 2 ^ 32
  sep : (reg32 S 240).Disjoint (reg32 B 2048)
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  base : s₀.gpr sb = B
  argIn : ∀ i < 2, InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4
  arg0 : s₀.mem.readW (addr (s₀.gpr .esp) 4) 32 = S
  arg1 : s₀.mem.readW (addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R
  argSep : ∀ i < 2, Region.Disjoint ⟨addr (s₀.gpr .esp) (4 + 4 * i), 4⟩ (reg32 B 2048)
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (addr S i)

/-- The regions the key loop writes. -/
abbrev keyFrame (B : BitVec 32) : List Region := [reg32 B 256, ⟨addr B 1024, 480⟩]

/-- The bitsliced round key `i` is in the scratch buffer. -/
def KeyAt (m : Mem) (B : BitVec 32) (R : Nat) (w : List Byte) (i : Nat) : Prop :=
  KeyRel (fun k => m.readW (addr B (keyOff R i + 4 * k)) 32) (roundKey w i)

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (B : BitVec 32) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  esi : s.gpr .esi = BitVec.ofNat 32 j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s.gpr r = s₀.gpr r
  frame : Frame (keyFrame B) s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R → KeyAt s.mem B R w i

/-- After the loop. -/
structure KDone (s₀ : State) (B : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s.gpr r = s₀.gpr r
  frame : Frame (keyFrame B) s₀.mem s.mem
  keys : KeysAt s.mem B R w

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 32} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, rkv, Vector.getElem_ofFn]

section
variable {s₀ : State} {B S : BitVec 32} {R : Nat} {w : List Byte} (hk : KSetup s₀ B S R w)
include hk

theorem KSetup.hR : R ≤ 14 := by rcases hk.rounds with h | h | h <;> omega

/-- The key frame is within the scratch buffer, and so apart from the schedule and the arguments. -/
theorem KSetup.frame_sub : ∀ r ∈ keyFrame B, Region.Sub r (reg32 B 2048) := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Region.sub_prefix (by omega)
  · exact part_sub_reg hk.fitB (by omega)

theorem KSetup.arg {s : State} (hf : Frame (keyFrame B) s₀.mem s.mem) {i : Nat} (hi : i < 2) :
    s.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 = s₀.mem.readW (addr (s₀.gpr .esp) (4 + 4 * i)) 32 :=
  hf.readW (Region.contains_self _ _) (fun r hr => (hk.argSep i hi).sub_right (hk.frame_sub r hr))
    (by decide)

theorem KSetup.sched {s : State} (hf : Frame (keyFrame B) s₀.mem s.mem) {i : Nat} (hi : i < 240) :
    s.mem (addr S i) = s₀.mem (addr S i) :=
  hf _ fun r hr hc => hk.sep _ (reg_contains hk.fitS (by omega) (by decide))
    (hk.frame_sub r hr _ hc)

theorem KSetup.linOk {s : State} (hb : s.gpr sb = B) (hwr : s.wr = s₀.wr) (hrd : s.rd = s₀.rd) :
    Ok linCfg s :=
  Ok.of_off (r := reg32 B 2048) (r' := reg32 B 2048) (b := B) (b' := B) (off := 0) (off' := 0)
    (n := 2048) (n' := 2048) (by rw [hwr]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hb]; simp) (by simp [linCfg])
    (by rw [hrd, hwr]; exact List.mem_append_right _ hk.scr) rfl hk.fitB (Nat.le_refl _)
    (by show s.gpr sb = _; rw [hb]; simp) (by simp [linCfg]) (.inr (.inl rfl))

theorem keyBody_ok {j : Nat} {s : State} (hi : KInv s₀ B R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ s'.cf = some true ∧ KDone s₀ B R w s') ∨
      (0 < j ∧ s'.cf = some false ∧ KInv s₀ B R w (j - 1) s') := by
  have hR := hk.hR
  have hjR := hi.hj
  have hsb : s.gpr sb = B := by rw [hi.keep sb (by decide) (by decide), hk.base]
  have hesp : s.gpr .esp = s₀.gpr .esp := hi.keep _ (by decide) (by decide)
  have harg : ∀ i < 2, InRegions (s.rd ++ s.wr) (addr (s.gpr .esp) (4 + 4 * i)) 4 := fun i hi' => by
    rw [hi.rd, hi.wr, hesp]; exact hk.argIn i hi'
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- The address of the round key.
  rw [keyLoad_eq, WP.block_append_iff (M := isa)]
  refine wp_mov fun s₁ u₁ => wp_add fun s₂ u₂ _ => wp_add fun s₃ u₃ _ => wp_add fun s₄ u₄ _ =>
    wp_add fun s₅ u₅ _ => wp_ldm (B := s.gpr .esp) (o := 4) (by
      rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
        u₁.other _ (by decide)]) (by
      rw [u₅.rd, u₅.wr, u₄.rd, u₄.wr, u₃.rd, u₃.wr, u₂.rd, u₂.wr, u₁.rd, u₁.wr]; exact harg 0 (by omega))
    fun s₅' u₅' => wp_add fun s₆ u₆ _ => WP.block_nil ?_
  have hm₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅'.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have g₆ : ∀ r, r ≠ .eax → r ≠ .ebx → s₆.gpr r = s.gpr r := fun r hr hr' => by
    rw [u₆.other r hr, u₅'.other r hr', u₅.other r hr, u₄.other r hr, u₃.other r hr, u₂.other r hr,
      u₁.other r hr]
  have rd₆ : s₆.rd = s.rd := by rw [u₆.rd, u₅'.rd, u₅.rd, u₄.rd, u₃.rd, u₂.rd, u₁.rd]
  have wr₆ : s₆.wr = s.wr := by rw [u₆.wr, u₅'.wr, u₅.wr, u₄.wr, u₃.wr, u₂.wr, u₁.wr]
  have a0 : s.mem.readW (addr (s.gpr .esp) 4) 32 = S := by
    have := hk.arg hi.frame (i := 0) (by omega)
    simp only [Nat.mul_zero, Nat.add_zero] at this
    rw [hesp, this, hk.arg0]
  have heax : s₆.gpr .eax = S + BitVec.ofNat 32 (16 * j) := by
    rw [u₆.gpr, u₅'.gpr, u₅'.other .eax (by decide), u₅.gpr, u₄.gpr, u₃.gpr, u₂.gpr, u₁.gpr, hi.esi,
      u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem, a0, BitVec.add_comm _ S]
    congr 1
    bv_omega
  -- The loads.
  have hok₁ : Ok loadCfg s₆ :=
    Ok.of_off (r := reg32 B 2048) (r' := reg32 S 240) (b := B) (b' := S) (off := 0) (off' := 16 * j)
      (n := 2048) (n' := 240) (by rw [wr₆, hi.wr]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
      (by show s₆.gpr sb = _; rw [g₆ _ (by decide) (by decide), hsb]; simp) (by simp [loadCfg])
      (by rw [rd₆, wr₆, hi.rd, hi.wr]; exact hk.sch) rfl hk.fitS (Nat.le_refl _) heax
      (by simp only [loadCfg]; omega) (.inr (.inr (.inl hk.sep.symm)))
  obtain ⟨s₇, hs₇, hq₇, hrd₇, hwr₇, hoth₇, hfr₇⟩ := loadMoves_ok hok₁
  refine WP.of_runBlock ⟨s₇, hs₇, ?_⟩
  have hin : InRel (Q s₇) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    rw [getD_eq _ hi16, rkv, Vector.getElem_ofFn, roundKey_getD hi16, hk.w _ (by omega)]
    have hq := hq₇ (i / 4) (by omega)
    have e : bb + 2 * (i / 4) = if bb = 0 then 2 * (i / 4) else 2 * (i / 4) + 1 := by split <;> omega
    rw [e]
    have hw : Q s₇ (if bb = 0 then 2 * (i / 4) else 2 * (i / 4) + 1) =
        s₆.mem.readW (wordAddr (s₆.gpr .eax) (i / 4)) 32 := by split <;> simp [hq]
    rw [hw, readW_bit _ _ (by omega) ht, hm₆, heax, wordAddr, addr_add,
      addr_add64 (by have := hk.fitS; omega),
      show 16 * j + 4 * (i / 4) + i % 4 = 16 * j + i by omega,
      hk.sched hi.frame (by omega)]
  -- Bitslice it.
  have hsb₇ : s₇.gpr sb = B := by rw [hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hsb]
  obtain ⟨s₈, hs₈, hq₈, hrd₈, hwr₈, hoth₈, hfr₈⟩ :=
    toBs_ok (hk.linOk hsb₇ (by rw [hwr₇, wr₆, hi.wr]) (by rw [hrd₇, rd₆, hi.rd]))
  refine WP.of_runBlock ⟨s₈, hs₈, ?_⟩
  have hbs₈ := bs_of_in hq₈ hin
  have hsb₈ : s₈.gpr sb = B := by rw [hoth₈ _ (by decide), hsb₇]
  have hesi₈ : s₈.gpr .esi = BitVec.ofNat 32 j := by
    rw [hoth₈ _ (by decide), hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hi.esi]
  have hesp₈ : s₈.gpr .esp = s₀.gpr .esp := by
    rw [hoth₈ _ (by decide), hoth₇ _ (by decide), g₆ _ (by decide) (by decide), hesp]
  -- The memory so far.
  have fr₈' : Frame [reg32 B 256] s.mem s₈.mem := by
    rw [← hm₆]
    refine (hfr₇.sub fun r hr => ⟨reg32 B 256, List.mem_cons_self .., ?_⟩).trans
      (hfr₈.sub fun r hr => ⟨reg32 B 256, List.mem_cons_self .., ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, loadCfg, g₆ _ (show sb ≠ .eax by decide) (by decide), hsb]
      exact Region.sub_prefix (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₇]
      exact Region.sub_prefix (by omega)
  have fr₈ : Frame (keyFrame B) s₀.mem s₈.mem :=
    hi.frame.trans (fr₈'.sub fun r hr => ⟨reg32 B 256, List.mem_cons_self .., by
      simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  -- The address to store it at.
  rw [keyStore_eq, WP.block_append_iff (M := isa)]
  have hin₈ : InRegions (s₈.rd ++ s₈.wr) (addr (s₀.gpr .esp) 8) 4 := by
    rw [hrd₈, hwr₈, hrd₇, hwr₇, rd₆, wr₆, hi.rd, hi.wr]; exact hk.argIn 1 (by omega)
  refine wp_ldm (B := s₀.gpr .esp) (o := 8) hesp₈ hin₈ fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ _ =>
    wp_add fun s₁₁ u₁₁ _ => wp_add fun s₁₂ u₁₂ _ => wp_add fun s₁₃ u₁₃ _ => wp_add fun s₁₄ u₁₄ _ =>
    wp_add fun s₁₅ u₁₅ _ => wp_mov fun s₁₆ u₁₆ => wp_addi fun s₁₇ u₁₇ => wp_sub fun s₁₈ u₁₈ _ =>
    WP.block_nil ?_
  have a1 : s₈.mem.readW (addr (s₀.gpr .esp) 8) 32 = BitVec.ofNat 32 R := by
    have := hk.arg fr₈ (i := 1) (by omega)
    simp only [Nat.mul_one] at this
    rw [this, hk.arg1]
  have heax : s₁₅.gpr .eax = BitVec.ofNat 32 (32 * (R - j)) := by
    rw [u₁₅.gpr, u₁₄.gpr, u₁₃.gpr, u₁₂.gpr, u₁₁.gpr, u₁₀.gpr, u₉.gpr, u₉.other .esi (by decide),
      hesi₈, a1]
    bv_omega
  have hebx : s₁₈.gpr .ebx = B + BitVec.ofNat 32 (keyOff R j) := by
    rw [u₁₈.gpr, u₁₇.gpr, u₁₆.gpr, u₁₇.other .eax (by decide), u₁₆.other .eax (by decide), heax]
    have : s₁₅.gpr .edi = B := by
      rw [u₁₅.other _ (by decide), u₁₄.other _ (by decide), u₁₃.other _ (by decide),
        u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide),
        u₉.other _ (by decide)]; exact hsb₈
    rw [this]
    simp only [keyOff, lastKey]
    bv_omega
  have hm₁₈ : s₁₈.mem = s₈.mem := by
    rw [u₁₈.mem, u₁₇.mem, u₁₆.mem, u₁₅.mem, u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem]
  have hrd₁₈ : s₁₈.rd = s₀.rd := by
    rw [u₁₈.rd, u₁₇.rd, u₁₆.rd, u₁₅.rd, u₁₄.rd, u₁₃.rd, u₁₂.rd, u₁₁.rd, u₁₀.rd, u₉.rd, hrd₈, hrd₇,
      rd₆, hi.rd]
  have hwr₁₈ : s₁₈.wr = s₀.wr := by
    rw [u₁₈.wr, u₁₇.wr, u₁₆.wr, u₁₅.wr, u₁₄.wr, u₁₃.wr, u₁₂.wr, u₁₁.wr, u₁₀.wr, u₉.wr, hwr₈, hwr₇,
      wr₆, hi.wr]
  have g₁₈ : ∀ r, r ≠ .eax → r ≠ .ebx → s₁₈.gpr r = s₈.gpr r := fun r h1 h2 => by
    rw [u₁₈.other r h2, u₁₇.other r h2, u₁₆.other r h2, u₁₅.other r h1, u₁₄.other r h1,
      u₁₃.other r h1, u₁₂.other r h1, u₁₁.other r h1, u₁₀.other r h1, u₉.other r h1]
  have hko := keyOff_le (j := j) hR
  have hok₂ : Ok storeCfg s₁₈ :=
    Ok.of_off (r := reg32 B 2048) (r' := reg32 B 2048) (b := B) (b' := B) (off := keyOff R j)
      (off' := 0) (n := 2048) (n' := 2048) (by rw [hwr₁₈]; exact hk.scr) rfl hk.fitB (Nat.le_refl _)
      hebx (by simp only [storeCfg, lastKey] at hko ⊢; omega)
      (by rw [hrd₁₈, hwr₁₈]; exact List.mem_append_right _ hk.scr) rfl hk.fitB (Nat.le_refl _)
      (by show s₁₈.gpr sb = _; rw [g₁₈ _ (by decide) (by decide), hsb₈]; simp)
      (by simp only [storeCfg]; omega)
      (.inr (.inr (.inr ⟨rfl, .inr (by simp only [storeCfg]; omega)⟩)))
  obtain ⟨s₁₉, hs₁₉, hst₁₉, hrd₁₉, hwr₁₉, hoth₁₉, hfr₁₉⟩ := storeMoves_ok hok₂
  refine WP.of_runBlock ⟨s₁₉, hs₁₉, ?_⟩
  refine wp_subi fun s₂₀ u₂₀ hcf _ => WP.block_nil ?_
  -- What is kept.
  have hkeep : ∀ r, r ∉ tmpRegs → r ≠ .esi → s₂₀.gpr r = s₀.gpr r := by
    intro r hr hne
    have h1 : r ≠ .eax := by rintro rfl; exact hr (by decide)
    have h2 : r ≠ .ebx := by rintro rfl; exact hr (by decide)
    rw [u₂₀.other r hne, hoth₁₉ r h1, g₁₈ r h1 h2, hoth₈ r hr, hoth₇ r h2, g₆ r h1 h2, hi.keep r hr hne]
  have hebx' : s₁₈.gpr .ebx = B + BitVec.ofNat 32 (keyOff R j) := hebx
  have hstore : slotRegion storeCfg s₁₈ = ⟨addr B (keyOff R j), 32⟩ := by
    simp only [slotRegion, storeCfg]; rw [show s₁₈.gpr .ebx = _ from hebx']; rfl
  have hm₂₀ : s₂₀.mem = s₁₉.mem := u₂₀.mem
  have fr : Frame (keyFrame B) s₀.mem s₂₀.mem := by
    rw [hm₂₀]
    refine fr₈.trans ?_
    rw [← hm₁₈]
    refine hfr₁₉.sub fun r hr => ⟨⟨addr B 1024, 480⟩, by simp, ?_⟩
    simp only [List.mem_singleton] at hr; subst hr
    rw [hstore]
    exact part_sub hk.fitB (by omega) (by simp only [lastKey] at hko; omega)
      (by simp only [lastKey] at hko; omega)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R → KeyAt s₂₀.mem B R w i := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk8 => ?_
    have hki := keyOff_le (j := i) hR
    rw [hm₂₀, hfr₁₉.readW (Region.contains_self _ _) (fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr
        rw [hstore]
        exact part_disj hk.fitB (by simp only [lastKey] at hki; omega)
          (by simp only [lastKey] at hko; omega)
          (by simp only [keyOff, lastKey] at hki hko ⊢; omega)) (by decide), hm₁₈]
    refine fr₈'.readW (Region.contains_self _ _) (fun r hr => ?_) (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    show Region.Disjoint _ ⟨B.setWidth 64, 256⟩
    rw [← addr_zero]
    exact part_disj hk.fitB (by simp only [lastKey] at hki; omega) (by omega)
      (.inr (by simp only [lastKey] at hki; omega))
  -- The key stored now.
  have hnew : KeyAt s₂₀.mem B R w j := by
    refine keyRel_congr (keyRel_of_bs hbs₈) fun k hk8 => ?_
    have := hst₁₉ k hk8
    rw [hebx', wordAddr, addr_add, Q_congr (g₁₈ _ (by decide) (by decide)) hm₁₈] at this
    rw [hm₂₀, this]
  have hesi : s₁₉.gpr .esi = BitVec.ofNat 32 j := by
    rw [hoth₁₉ _ (by decide), g₁₈ _ (by decide) (by decide), hesi₈]
  rw [hesi, toNat_ofNat_lt (by omega)] at hcf
  have hrd : s₂₀.rd = s₀.rd := by rw [u₂₀.rd, hrd₁₉, hrd₁₈]
  have hwr : s₂₀.wr = s₀.wr := by rw [u₂₀.wr, hwr₁₉, hwr₁₈]
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hcf, ⟨hrd, hwr, hkeep, fr, fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega) hiR
  · refine .inr ⟨by omega, by simpa [h0] using hcf, ⟨by omega, ?_, hrd, hwr, hkeep, fr, ?_⟩⟩
    · rw [u₂₀.gpr, hesi]; exact ofNat_pred (by omega)
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega) hiR

theorem keyLoop_ok {s : State} (hi : KInv s₀ B R w R s) :
    WP isa (.loop (.block keyBody) .ae) s (KDone s₀ B R w) := by
  refine WP.loop (M := isa) (KInv s₀ B R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨by simp [X86.eval, hcf], hd⟩
  · exact .inr ⟨by simp [X86.eval, hcf], n - 1, by omega, hi'⟩

end

end VG.Proof.Aes.X86
