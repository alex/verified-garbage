import VerifiedGarbage.Proof.Aes.X86_64.Encrypt
import VerifiedGarbage.Proof.Framework.Bitslice.Sym

/-!
# Bitslicing the round keys, on x86-64

Untrusted: everything here is checked by Lean.

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as four
identical blocks) with `toBs` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `toBs` by its proof (`Linear.lean`).
-/

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes
open VG.Spec.Aes (roundKey)

/-! ## Loading a round key -/

def loadCfg : Cfg := { base := sb, slots := 0, ext := .rdi, exts := 2 }

def loadPost (e : Env Nat) : Bool :=
  (List.range 4).all fun b => e.reg (q b) == some 0 && e.reg (q (b + 4)) == some 1

theorem keyLoad_check :
    check (names 64) loadCfg (fun k => some k) keyLoad { reg := fun _ => none, slot := fun _ => none }
      loadPost = true := by
  decide +kernel

theorem keyLoad_writes :
    [Reg.rdx, .rsp, .rsi, .rdi, .r8, .r9, .r14, .r15].all
      (fun r => keyLoad.all fun i => i.dst != some r) = true := by
  decide +kernel

/-- The registers the key loop writes. -/
def keyWrites : List Reg := [q 0, q 1, q 2, q 3, q 4, q 5, q 6, q 7, t0, .rdi, .rsi, .r15]

theorem keyLoad_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.rd ++ s.wr)
    (hb : s.gpr .rdi = r.base + BitVec.ofNat 64 off) (hoff : off + 16 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyLoad s = some s' ∧
      (∀ b < 4, s'.gpr (q b) = s.mem.readW (wordAddr (s.gpr .rdi) 0) 64 ∧
        s'.gpr (q (b + 4)) = s.mem.readW (wordAddr (s.gpr .rdi) 1) 64) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.mem = s.mem ∧
      (∀ r, r ∉ sboxWrites ∨ r = .r15 → s'.gpr r = s.gpr r) := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyLoad_check
  have hok : Ok loadCfg s := Ok.of_ext (r := r) hr hb (by simp [loadCfg]; omega) hn rfl
  let V : Nat → BitVec 64 := fun k => s.mem.readW (wordAddr (s.gpr .rdi) k) 64
  have hrel : Rel (NameRel V) loadCfg (fun k => some k) { reg := fun _ => none, slot := fun _ => none } s := by
    refine ⟨(fun _ _ h => by cases h), (fun _ _ _ h => by cases h), fun k a hk h => ?_⟩
    simp only [Option.some.injEq] at h; subst h; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun b hb => ?_, p.rd, p.wr, ?_, fun r hr => p.other r ?_⟩
  · have := List.all_eq_true.mp hpost b (List.mem_range.mpr hb)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨p.rel.reg _ _ this.1, p.rel.reg _ _ this.2⟩
  · funext x
    exact p.frame x fun r' hr' hc => by
      simp only [List.mem_singleton] at hr'; subst hr'
      simp [slotRegion, loadCfg, Region.Contains] at hc
  · refine Bool.ne_false_of_eq_true (List.all_eq_true.mp keyLoad_writes r ?_)
    revert hr; cases r <;> decide

/-! ## Storing it -/

def storeCfg : Cfg := { base := .rsi, slots := 8, ext := .rsi, exts := 0 }

def storeEnv : Env Nat :=
  { reg := fun r => ((List.range 8).find? (fun k => q k == r)), slot := fun _ => none }

def storePost (e : Env Nat) : Bool := (List.range 8).all fun k => e.slot k == some k

theorem keyStore_check : check (names 64) storeCfg (fun _ => none) keyStore storeEnv storePost = true := by
  decide +kernel

theorem keyStore_ok {s : State} {r : Region} {off : Nat} (hr : r ∈ s.wr)
    (hb : s.gpr .rsi = r.base + BitVec.ofNat 64 off) (hoff : off + 64 ≤ r.len) (hn : r.len < 2 ^ 64) :
    ∃ s', runBlock isa keyStore s = some s' ∧
      (∀ k < 8, s'.mem.readW (wordAddr (s.gpr .rsi) k) 64 = s.gpr (q k)) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.gpr = s.gpr ∧
      Frame [⟨s.gpr .rsi, 64⟩] s.mem s'.mem := by
  obtain ⟨e', he, hpost⟩ := of_check _ _ _ keyStore_check
  have hok : Ok storeCfg s := Ok.of_off (r := r) hr hb (by simp [storeCfg]; omega) hn rfl
  let V : Nat → BitVec 64 := fun k => s.gpr (q k)
  have hrel : Rel (NameRel V) storeCfg (fun _ => none) storeEnv s := by
    refine ⟨fun r a h => ?_, (fun _ _ _ h => by cases h), (fun _ _ hk _ => by simp [storeCfg] at hk)⟩
    simp only [storeEnv] at h
    have h1 := List.find?_some h
    simp only [beq_iff_eq] at h1; subst h1; rfl
  obtain ⟨s', hs', p⟩ := run (names_sound V) hok hrel he
  refine ⟨s', hs', fun k hk => ?_, p.rd, p.wr, ?_, p.frame⟩
  · have := List.all_eq_true.mp hpost k (List.mem_range.mpr hk)
    simp only [beq_iff_eq] at this
    have h := p.rel.slot k k hk this
    rw [p.base] at h
    exact h
  · funext r
    exact p.other r (by
      have : (keyStore.all fun i => i.dst != some r) = true := by
        simp [keyStore, Instr.dst]
      simp [this])

/-! ## Stepping back -/

theorem keyStep_ok (s : State) :
    ∃ s', runBlock isa keyStep s = some s' ∧
      s'.gpr .rdi = s.gpr .rdi - 16 ∧ s'.gpr .rsi = s.gpr .rsi - 64 ∧ s'.gpr .r15 = s.gpr .r15 - 1 ∧
      s'.cf = some (decide ((s.gpr .r15).toNat < 1)) ∧
      (∀ r, r ≠ .rdi → r ≠ .rsi → r ≠ .r15 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [keyStep, runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, Option.bind_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags]
  refine ⟨by simp, by simp, by simp, by simp, fun r h1 h2 h3 => by simp [h1, h2, h3], trivial, trivial,
    trivial⟩

/-! ## Readings and regions -/

theorem readW_bit (m : Mem) (a : Addr) {i t : Nat} (hi : i < 8) (ht : t < 8) :
    (m.readW a 64).getLsbD (8 * i + t) = (m (a + BitVec.ofNat 64 i)).getLsbD t := by
  rw [← Mem.extractLsb'_read m a (n := 8) hi, BitVec.getLsbD_extractLsb']
  simp only [Mem.readW, ht, decide_true, Bool.true_and]
  rw [BitVec.getLsbD_setWidth]
  simp [show 8 * i + t < 64 by omega]

theorem off_disjoint (b : Addr) {x lx y ly : Nat} (h : x + lx ≤ y ∨ y + ly ≤ x)
    (hx : x + lx < 2 ^ 64) (hy : y + ly < 2 ^ 64) :
    Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b + BitVec.ofNat 64 y, ly⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  rcases h with h | h <;> bv_omega

theorem base_sub (b : Addr) {lx ly : Nat} (h : lx ≤ ly) (hy : ly < 2 ^ 64) :
    Region.Sub ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 0, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

theorem off_sub_base (b : Addr) {x lx ly : Nat} (h : x + lx ≤ ly) (hy : ly < 2 ^ 64) :
    Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

theorem off_disjoint_base (b : Addr) {x lx ly : Nat} (h : ly ≤ x) (hx : x + lx < 2 ^ 64) :
    Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, ly⟩ := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  bv_omega

theorem off_sub (b : Addr) {x lx y ly : Nat} (h1 : y ≤ x) (h2 : x + lx ≤ y + ly) (hy : y + ly < 2 ^ 64) :
    Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b + BitVec.ofNat 64 y, ly⟩ := by
  intro a h
  simp only [Region.Contains] at h ⊢
  bv_omega

/-! ## The loop -/

/-- Where the loop runs: the scratch buffer at `b`, the key schedule `w`
at `sc` (as the bytes there). -/
structure KSetup (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) : Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₀.wr
  base : s₀.gpr sb = b
  sch : (⟨sc, 240⟩ : Region) ∈ s₀.rd ++ s₀.wr
  sep : Region.Disjoint ⟨sc, 240⟩ ⟨b, 2048⟩
  rounds : R ≤ 14
  w : ∀ i < 16 * (R + 1), w.getD i 0 = s₀.mem (sc + BitVec.ofNat 64 i)

/-- The address of bitsliced round key `i`. -/
abbrev keyAddr (b : Addr) (R i : Nat) : Addr := b + BitVec.ofNat 64 (1920 - 64 * (R - i))

/-- Before bitslicing round key `j`. -/
structure KInv (s₀ : State) (b sc : Addr) (R : Nat) (w : List Byte) (j : Nat) (s : State) : Prop where
  hj : j ≤ R
  r15 : s.gpr .r15 = BitVec.ofNat 64 j
  rdi : s.gpr .rdi = sc + BitVec.ofNat 64 (16 * j)
  rsi : s.gpr .rsi = keyAddr b R j
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s.mem
  done : ∀ i, j < i → i ≤ R →
    KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

/-- After the loop. -/
structure KDone (s₀ : State) (b : Addr) (R : Nat) (w : List Byte) (s : State) : Prop where
  rsi : s.gpr .rsi = keyAddr b R 0 - 64
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keep : ∀ r, r ∉ keyWrites → s.gpr r = s₀.gpr r
  frame : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s.mem
  keys : ∀ i ≤ R, KeyRel (fun k => s.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i)

theorem roundKey_getD {w : List Byte} {j i : Nat} (hi : i < 16) :
    (roundKey w j).getD i 0 = w.getD (16 * j + i) 0 := by
  simp only [roundKey, List.getD_eq_getElem?_getD, List.getElem?_take, hi, ite_true,
    List.getElem?_drop]

theorem frame_regions (b : Addr) : ∀ r ∈ [(⟨b + BitVec.ofNat 64 0, 384⟩ : Region),
    ⟨b + BitVec.ofNat 64 1024, 1024⟩], Region.Sub r ⟨b + BitVec.ofNat 64 0, 2048⟩ := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact off_sub b (by omega) (by omega) (by omega)
  · exact off_sub b (by omega) (by omega) (by omega)

theorem wordAddr_off (b : Addr) (x k : Nat) : wordAddr (b + BitVec.ofNat 64 x) k = b + BitVec.ofNat 64 (x + 8 * k) := by
  rw [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add]

theorem readW_off_frame {m m' : Mem} {b : Addr} {rs : List Region} (hf : Frame rs m m') {x : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + BitVec.ofNat 64 x, 8⟩ r) :
    m'.readW (b + BitVec.ofNat 64 x) 64 = m.readW (b + BitVec.ofNat 64 x) 64 :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- The schedule's bytes are those of `w`. -/
theorem KInv.sched {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) {i : Nat} (hi16 : i < 16) :
    s.mem (sc + BitVec.ofNat 64 (16 * j + i)) = (roundKey w j).getD i 0 := by
  have hjR := hi.hj
  have hR := hk.rounds
  rw [roundKey_getD hi16, hk.w _ (by omega)]
  refine hi.frame _ fun r hr hc => ?_
  have hsub := frame_regions b r hr
  refine hk.sep _ ?_ (by simpa using hsub _ hc)
  simp only [Region.Contains]
  rw [show sc + BitVec.ofNat 64 (16 * j + i) - sc = BitVec.ofNat 64 (16 * j + i) by bv_omega,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-- The round key as a state. -/
def rkv (w : List Byte) (j : Nat) : Spec.Aes.State := Vector.ofFn fun i => (roundKey w j).getD i 0

theorem keyRel_of_bs {K : Nat → BitVec 64} {w : List Byte} {j : Nat}
    (h : BsRel K fun _ => rkv w j) : KeyRel K (roundKey w j) := by
  intro b hb i hi
  rw [h b hb i hi, getD_eq _ hi, rkv, Vector.getElem_ofFn]

theorem keyWrites_not (r : Reg) (hr : r ∉ keyWrites) :
    (r ∉ sboxWrites ∧ r ≠ t1) ∧ r ≠ .rdi ∧ r ≠ .rsi ∧ r ≠ .r15 := by
  revert hr; cases r <;> decide

theorem add_ofNat_sub (b : Addr) {x y : Nat} (h : y ≤ x) :
    b + BitVec.ofNat 64 x - BitVec.ofNat 64 y = b + BitVec.ofNat 64 (x - y) := by
  rw [show x = (x - y) + y by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_sub_one {j : Nat} (h : 0 < j) : BitVec.ofNat 64 j - 1 = BitVec.ofNat 64 (j - 1) := by
  rw [show j = (j - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem keyAddr_pred (b : Addr) {R j : Nat} (hR : R ≤ 14) (hj : 0 < j) (hjR : j ≤ R) :
    keyAddr b R j - 64 = keyAddr b R (j - 1) := by
  simp only [keyAddr]
  rw [show 1920 - 64 * (R - j) = (1920 - 64 * (R - (j - 1))) + 64 by omega, BitVec.ofNat_add,
    ← BitVec.add_assoc]
  exact BitVec.add_sub_cancel _ _

theorem keyBody_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {j : Nat} {s : State} (hi : KInv s₀ b sc R w j s) :
    WP isa (.block keyBody) s fun s' =>
      (j = 0 ∧ s'.cf = some true ∧ KDone s₀ b R w s') ∨
      (0 < j ∧ s'.cf = some false ∧ KInv s₀ b sc R w (j - 1) s') := by
  have hR := hk.rounds
  have hjR := hi.hj
  have hsb : s.gpr sb = b := by rw [hi.keep sb (by decide), hk.base]
  simp only [keyBody]
  repeat rw [WP.block_append_iff (M := isa)]
  -- Load the round key.
  obtain ⟨s₁, hs₁, hq₁, hrd₁, hwr₁, hm₁, hoth₁⟩ := keyLoad_ok (r := ⟨sc, 240⟩) (off := 16 * j)
    (by rw [hi.rd, hi.wr]; exact hk.sch) hi.rdi (by simp only; omega) (by simp only; omega)
  refine WP.of_runBlock ⟨s₁, hs₁, ?_⟩
  have hin : InRel (Q s₁) fun _ => rkv w j := by
    intro bb hb i hi16 t ht
    have hbyte := hi.sched hk hi16
    rw [getD_eq _ hi16, rkv, Vector.getElem_ofFn]
    simp only [Q]
    by_cases h8 : i < 8
    · rw [show bb + 4 * (i / 8) = bb by omega, (hq₁ bb hb).1, show i % 8 = i by omega,
        readW_bit _ _ h8 ht, wordAddr, hi.rdi, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
    · rw [show bb + 4 * (i / 8) = bb + 4 by omega, (hq₁ bb hb).2, readW_bit _ _ (by omega) ht,
        wordAddr, hi.rdi, ← hbyte]
      congr 2; rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add]
      congr 2; omega
  -- Bitslice it.
  have hok₁ : Ok linCfg s₁ := Ok.of_region (r := ⟨b, 2048⟩) (by rw [hwr₁, hi.wr]; exact hk.scr)
    (by simp only [linCfg]; rw [hoth₁ sb (.inl (by decide)), hsb]) (by simp [linCfg]) (by simp [linCfg]) rfl
  obtain ⟨s₂, hs₂, hq₂, hrd₂, hwr₂, hoth₂, hfr₂⟩ := toBs_ok hok₁
  refine WP.of_runBlock ⟨s₂, hs₂, ?_⟩
  have hbs₂ := bs_of_in hq₂ hin
  -- Store it.
  have hrsi₂ : s₂.gpr .rsi = keyAddr b R j := by
    rw [hoth₂ .rsi (by decide), hoth₁ .rsi (.inl (by decide)), hi.rsi]
  obtain ⟨s₃, hs₃, hst₃, hrd₃, hwr₃, hg₃, hfr₃⟩ := keyStore_ok (r := ⟨b, 2048⟩)
    (off := 1920 - 64 * (R - j)) (by rw [hwr₂, hwr₁, hi.wr]; exact hk.scr) hrsi₂
    (by simp only; omega) (by simp only; omega)
  refine WP.of_runBlock ⟨s₃, hs₃, ?_⟩
  -- Step back.
  obtain ⟨s₄, hs₄, hrdi₄, hrsi₄, hr15₄, hcf₄, hoth₄, hm₄, hrd₄, hwr₄⟩ := keyStep_ok s₃
  refine WP.of_runBlock ⟨s₄, hs₄, ?_⟩
  have hsb₁ : s₁.gpr sb = b := by rw [hoth₁ sb (.inl (by decide)), hsb]
  -- What is kept.
  have hkeep : ∀ r, r ∉ keyWrites → s₄.gpr r = s₀.gpr r := by
    intro r hr
    obtain ⟨h1, h2, h3, h4⟩ := keyWrites_not r hr
    rw [hoth₄ r h2 h3 h4, hg₃, hoth₂ r h1.1, hoth₁ r (.inl h1.1), hi.keep r hr]
  have hfr : Frame [⟨b + BitVec.ofNat 64 0, 384⟩, ⟨b + BitVec.ofNat 64 1024, 1024⟩] s₀.mem s₄.mem := by
    rw [hm₄]
    refine hi.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hfr₂.sub fun r hr => ⟨_, List.mem_cons_self .., ?_⟩)
      (hfr₃.sub fun r hr => ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩)
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₁]
      exact base_sub b (by decide) (by decide)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hrsi₂]
      exact off_sub b (by omega) (by omega) (by decide)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [hm₄, readW_off_frame hfr₃ fun r hr => ?_, readW_off_frame hfr₂ fun r hr => ?_, hm₁]
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₁]
      exact off_disjoint_base b (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hrsi₂]
      exact off_disjoint b (by omega) (by omega) (by omega)
  -- The key stored now.
  have hnew : KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R j) k) 64) (roundKey w j) :=
    keyRel_congr (keyRel_of_bs hbs₂) fun k hk => by rw [hm₄, ← hrsi₂, hst₃ k hk]
  have hr15 : s₃.gpr .r15 = BitVec.ofNat 64 j := by
    rw [hg₃, show Reg.r15 = t1 from rfl, toBs_keeps_t1 hok₁ hs₂, show t1 = Reg.r15 from rfl,
      hoth₁ .r15 (.inr rfl), hi.r15]
  have hrdi : s₃.gpr .rdi = sc + BitVec.ofNat 64 (16 * j) := by
    rw [hg₃, hoth₂ .rdi (by decide), hoth₁ .rdi (.inl (by decide)), hi.rdi]
  have hrsi : s₃.gpr .rsi = keyAddr b R j := by rw [hg₃, hrsi₂]
  have hrd : s₄.rd = s₀.rd := by rw [hrd₄, hrd₃, hrd₂, hrd₁, hi.rd]
  have hwr : s₄.wr = s₀.wr := by rw [hwr₄, hwr₃, hwr₂, hwr₁, hi.wr]
  rw [hr15, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at hcf₄
  by_cases h0 : j = 0
  · subst h0
    refine .inl ⟨rfl, by simpa using hcf₄, ⟨by rw [hrsi₄, hrsi], hrd, hwr, hkeep, hfr, fun i hiR => ?_⟩⟩
    by_cases hi0 : i = 0
    · subst hi0; exact hnew
    · exact hold i (by omega) hiR
  · refine .inr ⟨by omega, by simpa [h0] using hcf₄, ⟨by omega, ?_, ?_, ?_, hrd, hwr, hkeep, hfr, ?_⟩⟩
    · rw [hr15₄, hr15]; exact ofNat_sub_one (by omega)
    · rw [hrdi₄, hrdi, show 16 * (j - 1) = 16 * j - 16 by omega]
      exact add_ofNat_sub sc (y := 16) (by omega)
    · rw [hrsi₄, hrsi]; exact keyAddr_pred b hk.rounds (by omega) hi.hj
    · intro i hi' hiR
      by_cases hij : i = j
      · subst hij; exact hnew
      · exact hold i (by omega) hiR

theorem keyLoop_ok {s₀ : State} {b sc : Addr} {R : Nat} {w : List Byte} (hk : KSetup s₀ b sc R w)
    {s : State} (hi : KInv s₀ b sc R w R s) :
    WP isa (.loop (.block keyBody) .ae) s (KDone s₀ b R w) := by
  refine WP.loop (M := isa) (KInv s₀ b sc R w) (fun n s hs => ?_) R s hi
  refine WP.mono (keyBody_ok hk hs) fun s' h => ?_
  rcases h with ⟨_, hcf, hd⟩ | ⟨hn, hcf, hi'⟩
  · exact .inl ⟨by simp [X86_64.eval, hcf], hd⟩
  · exact .inr ⟨by simp [X86_64.eval, hcf], n - 1, by omega, hi'⟩

end VG.Proof.Aes.X86_64