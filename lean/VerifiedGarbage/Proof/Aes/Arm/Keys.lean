import VerifiedGarbage.Proof.Aes.Arm.Encrypt
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Framework.Arm.Bytes

/-!
# Bitslicing the round keys, on ARMv7

Untrusted: everything here is checked by Lean.

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as two
identical blocks) with `ortho` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `ortho` by its proof (`Linear.lean`). During the loop
the scratch buffer's base is not in a register: the round keys are stored
through `kp`.
-/

namespace VG.Proof.Aes.Arm

open VG VG.Arm VG.Arm.Straight VG.Bitslice VG.Impl.Aes.Arm
open VG.Spec.Aes (roundKey)

/-- `ortho` does not use memory: its check with no slots. -/
def noMem : Cfg := { base := sb, slots := 0, ext := sb, exts := 0 }

theorem ortho_check0 :
    check (lanes 32 8) noMem (linExt 0) ortho (linEnv qIns) (linPost 8 (qOuts orthoG)) = true := by
  decide +kernel

theorem noMem_ok (s : State) : Ok noMem s where
  slotIn k hk := by simp [noMem] at hk
  extIn k hk := by simp [noMem] at hk
  slots := by simp only [noMem]; have := (s.gpr sb).isLt; omega
  sep k hk := by simp [noMem] at hk

theorem frame_nil {m m' : Mem} {a : Addr} (h : Frame [⟨a, 4 * 0⟩] m m') : m' = m := by
  funext x
  exact h x fun r hr hc => by
    simp only [List.mem_singleton] at hr; subst hr
    simp [Region.Contains] at hc

/-- The registers `ortho` (and the loads of a round key) may write. -/
def orthoWrites : List Reg := [.r0, .r1, .r2, .r3, .r4, .r5, .r6, .r7, .r10, .r11]

theorem ortho_writes : ∀ r, r ∉ orthoWrites → (ortho.all fun i => dstOf i != some r) = true := by
  intro r; cases r <;> decide +kernel

theorem keyLoad_writes : ∀ r, r ∉ orthoWrites → (keyLoad.all fun i => dstOf i != some r) = true := by
  intro r; cases r <;> decide +kernel

/-- `ortho`, wherever `sb` points. -/
theorem ortho_ok' (s : State) :
    ∃ s', runBlock isa ortho s = some s' ∧
      (∀ j < 8, ∀ p < 32, (Q s' j).getLsbD p = (Q s (p % 8)).getLsbD (8 * (p / 8) + j)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ (∀ r, r ∉ orthoWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem := by
  obtain ⟨s', hs', hout, hrd, hwr, hsp, hoth, hfr⟩ := linear_ok ortho_check0 (noMem_ok s) (Q s)
    (fun r i hri => by
      simp only [qIns, List.mem_map, List.mem_range, Prod.mk.injEq] at hri
      obtain ⟨i, hi, rfl, rfl⟩ := hri
      exact ⟨by omega, rfl⟩) (fun j hj => by simp [noMem] at hj)
  have hmem : ∀ j < 8, (q j, orthoG j) ∈ qOuts orthoG := fun j hj => by
    simp only [qOuts, List.mem_map, List.mem_range]; exact ⟨j, hj, rfl⟩
  refine ⟨s', hs', fun j hj p hp => ?_, hrd, hwr, hsp, fun r hr => hoth r ?_, frame_nil hfr⟩
  · rw [hout _ _ (hmem j hj) p hp, orthoG, Straight.xorBits_cons, Straight.xorBits_nil, Bool.xor_false,
      Straight.bitOf_word _ _ _ (by omega)]
  · simp [ortho_writes r hr]

/-! ## Loading a round key -/

def loadCfg : Cfg := { base := sb, slots := 0, ext := .r12, exts := 4 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun k => e.reg (q (2 * k)) == some k && e.reg (q (2 * k + 1)) == some k

theorem keyLoad_check :
    check (names 32) loadCfg (fun k => some k) keyLoad { reg := fun _ => none, slot := fun _ => none }
      loadPost = true := by
  decide +kernel

/-- The registers the key loop writes. -/
def keyWrites : List Reg := kp :: layerWrites

theorem keyLoad_ok {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.rd ++ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr .r12 = b + BitVec.ofNat 32 off) (hoff : off + 16 ≤ len) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      (∀ k < 4, s'.gpr (q (2 * k)) = s.mem.readW (wordAddr (s.gpr .r12) k) 32 ∧
        s'.gpr (q (2 * k + 1)) = s.mem.readW (wordAddr (s.gpr .r12) k) 32) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ orthoWrites → s'.gpr r = s.gpr r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyLoad_check
  have hok : Ok loadCfg s := Ok.of_ext hr hfit hb (by simp [loadCfg]; omega) rfl
  let V : Nat → BitVec 32 := fun k => s.mem.readW (wordAddr (s.gpr .r12) k) 32
  have hrel : Rel (NameRel V) loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_,
      (fun _ _ h => by cases h)⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, fun r hr => p.other r ?_⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨p.rel.reg _ _ this.1, p.rel.reg _ _ this.2⟩
  · funext x
    exact p.frame x fun r' hr' hc => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp [slotRegion, loadCfg, Region.Contains] at hc
  · exact Bool.ne_false_of_eq_true (keyLoad_writes r hr)

/-! ## Storing it -/

def storeCfg : Cfg := { base := kp, slots := 8, ext := kp, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)), slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : check (names 32) storeCfg (fun _ => none) keyStore storeEnv storePost = true := by
  decide +kernel

theorem keyStore_ok {s : State} {b : BitVec 32} {len off : Nat}
    (hr : (⟨State.addr b, len⟩ : Region) ∈ s.wr) (hfit : b.toNat + len ≤ 2 ^ 32)
    (hb : s.gpr kp = b + BitVec.ofNat 32 off) (hoff : off + 32 ≤ len) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr kp) k) 32 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp ∧ s'.gpr = s.gpr ∧
      Frame [⟨State.addr (s.gpr kp), 32⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyStore_check
  have hok : Ok storeCfg s := Ok.of_off hr hfit hb (by simp [storeCfg]; omega) rfl
  let V : Nat → BitVec 32 := fun k => s.gpr (q k)
  have hrel : Rel (NameRel V) storeCfg (fun _ => none) storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [storeCfg] at hk),
      (fun _ _ h => by cases h)⟩
    simp only [storeEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, p.sp, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => dstOf i != some r) = true := by
        simp [keyStore, dstOf]
      simp [this])

/-! ## Stepping back -/

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .r12 = s.gpr .r12 - 16 ∧ s'.gpr kp = s.gpr kp - 32 ∧ s'.gpr .lr = s.gpr .lr - 1 ∧
      s'.z = (s.gpr .lr - 1 == 0) ∧
      (∀ r, r ≠ .r12 → r ≠ kp → r ≠ .lr → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
  refine ⟨_, by simp only [keyStep, runBlock_cons, exec, Op2.eval]; rfl, ?_⟩
  refine ⟨by simp [State.setReg, subFlags, kp], by simp [State.setReg, subFlags, kp],
    by simp [State.setReg, subFlags, kp], by simp [State.setReg, subFlags, kp],
    fun r h1 h2 h3 => by simp [State.setReg, subFlags, h1, h2, h3], rfl, rfl, rfl, rfl⟩

/-! ## Readings and regions -/

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `b`, the key schedule `w`
at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (b sc : BitVec 32) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨State.addr b, 2048⟩ : Region) ∈ s₀.wr
  fit : b.toNat + 2048 ≤ 2 ^ 32
  sch : (⟨State.addr sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  fitS : sc.toNat + 240 ≤ 2 ^ 32
  sep : Region.Disjoint ⟨State.addr sc, 240⟩ ⟨State.addr b, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (State.addr sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : BitVec 32) (R i : Nat) : BitVec 32 := b + BitVec.ofNat 32 (lastKey - 32 * (R - i))

/-- The key area of the scratch buffer at `b`. -/
abbrev keyArea (b : BitVec 32) : Region := ⟨State.addr b + BitVec.ofNat 64 1024, 1024⟩

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : BitVec 32) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  lr : s.gpr .lr = BitVec.ofNat 32 (j + 1)
  r12 : s.gpr .r12 = sc + BitVec.ofNat 32 (16 * j)
  kp : s.gpr kp = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [keyArea b] s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 32) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : BitVec 32) (R : Nat) (w : List Byte) (s : State) : Prop where
  kp : s.gpr kp = keyAddr b R 0 - 32
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [keyArea b] s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 32) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

/-- The 64-bit address of a word of a round key. -/
theorem keyWord_addr {b : BitVec 32} (hfit : b.toNat + 2048 ≤ 2 ^ 32) {R i k : Nat} (hk : k < 8) :
    wordAddr (keyAddr b R i) k = State.addr b + BitVec.ofNat 64 (lastKey - 32 * (R - i) + 4 * k) := by
  simp only [wordAddr, keyAddr, lastKey]
  rw [add_ofNat_ofNat, addr_add (by omega)]

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) {i : Nat} (hi16 : i < 16) :
    s.mem (State.addr sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [roundKey_getD hi16, hk.w _ (by omega)]
  refine hi.frame _ fun r hr hc => ?_
  simp only [List.mem_singleton] at hr; subst hr
  have hsub : Region.Sub (keyArea b) ⟨State.addr b, 2048⟩ := by
    intro a h
    simp only [Region.Contains] at h ⊢
    bv_omega
  refine hk.sep _ ?_ (hsub _ hc)
  simp only [Region.Contains]
  rw [show State.addr sc + BitVec.ofNat 64 (16 * j + i) - State.addr sc = BitVec.ofNat 64 (16 * j + i) by
    bv_omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 32} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, VG.Proof.Aes.getD_eq _ hi, rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ keyWrites) :
    r ∉ orthoWrites ∧ r ≠ .r12 ∧ r ≠ kp ∧ r ≠ .lr := by
  revert hr; cases r <;> decide

theorem keyAddr_pred (b : BitVec 32) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    keyAddr b R j - 32 = keyAddr b R (j - 1) := by
  simp only [keyAddr, lastKey]
  rw [show 2016 - 32 * (R - j) = (2016 - 32 * (R - (j - 1))) + 32 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem keyBody_ok {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ Arm.eval .ne s' = some false ∧ KDone s₀ b R w s') ∨
      (0 < j ∧ Arm.eval .ne s' = some true ∧ KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hsp₁, hm₁, hoth₁⟩ := keyLoad_ok (b := sc) (off := 16 * j)
    (by rw [hi.rd, hi.wr]; exact hk.sch) hk.fitS hi.r12 (by omega)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hin : InRel (Q s₁) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [VG.Proof.Aes.getD_eq _ hi16, rkv, Vector.getElem_ofFn]
    simp only [Q]
    have hq : s₁.gpr (q (2 * (i / 4) + bb)) = s.mem.readW (wordAddr (s.gpr .r12) (i / 4)) 32 := by
      rcases (show bb = 0 ∨ bb = 1 by omega) with rfl | rfl
      · exact (hq₁ _ (by omega)).1
      · exact (hq₁ _ (by omega)).2
    rw [hq, readW_bit _ _ (show i % 4 < 4 by omega) ht, wordAddr, hi.r12, add_ofNat_ofNat,
      addr_add (by have := hk.fitS; omega), BitVec.add_assoc, ← BitVec.ofNat_add, ← hbyte]
    rw [show 16 * j + 4 * (i / 4) + i % 4 = 16 * j + i by omega]
  -- Bitslice it.
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hsp₂, hoth₂, hm₂⟩ := ortho_ok' s₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := bs_of_in hq₂ hin
  -- Store it.
  have hkp₂ : s₂.gpr kp = keyAddr b R j := by
    rw [hoth₂ kp (by decide), hoth₁ kp (by decide), hi.kp]
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hsp₃, hg₃, hfr₃⟩ := keyStore_ok (b := b)
    (off := lastKey - 32 * (R - j)) (by rw [hwr₂, hwr₁, hi.wr]; exact hk.scr) hk.fit hkp₂
    (by simp only [lastKey]; omega)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hr12₄, hkp₄, hlr₄, hz₄, hoth₄, hm₄, hrd₄, hwr₄, hsp₄⟩ := keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  -- The region written now.
  have hsubk : Region.Sub ⟨State.addr (keyAddr b R j), 32⟩ (keyArea b) := by
    have e : State.addr (keyAddr b R j) = State.addr b + BitVec.ofNat 64 (lastKey - 32 * (R - j)) := by
      simp only [keyAddr, lastKey]; rw [addr_add (by have := hk.fit; omega)]
    rw [e]
    exact off_sub _ (by simp only [lastKey]; omega) (by simp only [lastKey]; omega) (by decide)
  -- What is kept.
  have hkeep : ∀ r, r ∉ keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1, hoth₁ r h1, hi.keep r hr]
  have hfr : Frame [keyArea b] s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁, ← hm₂]
    rw [hkp₂] at hfr₃
    exact hfr₃.sub fun r hr => ⟨_, List.mem_singleton_self _, by
      simp only [List.mem_singleton] at hr; subst hr; exact hsubk⟩
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 32) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk8 => ?_
    rw [hm₄, keyWord_addr hk.fit hk8, hfr₃.readW (r := ⟨_, 4⟩) (Region.contains_self _ _) ?_
      (by decide), hm₂, hm₁]
    intro r hr
    simp only [List.mem_singleton] at hr; subst hr
    rw [hkp₂]
    have e : State.addr (keyAddr b R j) = State.addr b + BitVec.ofNat 64 (lastKey - 32 * (R - j)) := by
      simp only [keyAddr, lastKey]; rw [addr_add (by have := hk.fit; omega)]
    rw [e]
    exact off_disjoint _ (by simp only [lastKey]; omega) (by simp only [lastKey]; omega)
      (by simp only [lastKey]; omega)
  -- The key stored now.
  have hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R j) k) 32) (roundKey w j) :=
    keyRel_congr (keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hkp₂, hst₃ k hk]
  have hlr : s₃.gpr .lr = BitVec.ofNat 32 (j + 1) := by
    rw [hg₃, hoth₂ .lr (by decide), hoth₁ .lr (by decide), hi.lr]
  have hr12 : s₃.gpr .r12 = sc + BitVec.ofNat 32 (16 * j) := by
    rw [hg₃, hoth₂ .r12 (by decide), hoth₁ .r12 (by decide), hi.r12]
  have hkp : s₃.gpr kp = keyAddr b R j := by rw [hg₃, hkp₂]
  have hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  have hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  have hsp : s₄.sp = s₀.sp := by rw [hsp₄, hsp₃, hsp₂, hsp₁, hi.sp]
  have hlr' : s₄.gpr .lr = BitVec.ofNat 32 j := by
    rw [hlr₄, hlr]; bv_omega
  have hev : Arm.eval .ne s₄ = some (!(BitVec.ofNat 32 j == 0)) := by
    simp only [Arm.eval, hz₄, hlr]
    congr 3; bv_omega
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, hev.trans (by decide), ⟨by rw [hkp₄, hkp], hrd, hwr, hsp, hkeep, hfr,
      fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega) hiR
  · have hne : BitVec.ofNat 32 j ≠ 0 := by
      intro h; have := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this; omega
    refine .inr ⟨by omega, hev.trans (by simpa using hne),
      ⟨by omega, ?_, ?_, ?_, hrd, hwr, hsp, hkeep, hfr, ?_⟩⟩
    · rw [hlr', show j - 1 + 1 = j by omega]
    · rw [hr12₄, hr12]; bv_omega
    · rw [hkp₄, hkp]; exact keyAddr_pred b hk.rounds (by omega) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega) hiR

theorem keyLoop_ok {s₀ : State} {b sc : BitVec 32} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {s : State} (hi : KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) .ne) s (KDone s₀ b R w) := by
  refine WP.loop (M := isa) (KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hev, hd⟩ | ⟨hn, hev, hi'⟩
  · exact .inl ⟨hev, hd⟩
  · exact .inr ⟨hev, n - 1, by omega, hi'⟩

end VG.Proof.Aes.Arm
