import VerifiedGarbage.Proof.Aes.X86_64.Encrypt
import VerifiedGarbage.Proof.Framework.Bitslice.Sym
import VerifiedGarbage.Proof.Aes.Blocks
import Mathlib.Tactic.SplitIfs
import VerifiedGarbage.Proof.Framework.Offset

section

/-!
# Bitslicing the round keys, on x86-64

The key loop of `vg_aes_ctr32` bitslices each round key (loaded as four
identical blocks) with `toBs` and stores it in the scratch buffer. The
loads and stores are checked by evaluation over the naming domain
(`Bitslice.names`), `toBs` by its proof (`Encrypt.lean`).
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

theorem base_sub (b : Addr) {lx ly : Nat} (h : lx ≤ ly) (hy : ly < 2 ^ 64) :
    Region.Sub ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 0, ly⟩ := by
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
  · exact Offset.sub b (by omega) (by omega)
  · exact Offset.sub b (by omega) (by omega)

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
      exact Offset.sub b (by omega) (by omega)
  -- The keys stored before.
  have hold : ∀ i, j < i → i ≤ R →
      KeyRel (fun k => s₄.mem.readW (wordAddr (keyAddr b R i) k) 64) (roundKey w i) := by
    intro i hji hiR
    refine keyRel_congr (hi.done i hji hiR) fun k hk => ?_
    simp only [keyAddr, wordAddr_off]
    rw [hm₄, readW_off_frame hfr₃ fun r hr => ?_, readW_off_frame hfr₂ fun r hr => ?_, hm₁]
    · simp only [List.mem_singleton] at hr; subst hr
      simp only [slotRegion, linCfg, hsb₁]
      exact Offset.disjoint_base b (by omega) (by omega)
    · simp only [List.mem_singleton] at hr; subst hr
      rw [hrsi₂]
      exact Offset.disjoint b (by omega) (by omega) (by omega)
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

end

/-!
# One group of counter-mode blocks on x86-64

`ctrBlocks` builds the counter blocks `c + b` (`b < 4`) from the slots of
the counter block (`ctrBlocks_wp`, then `ctr_inRel` for `InRel`),
`encrypt4` encrypts them (`Encrypt.lean`), and `xorFull` or `xorTail` XOR
the keystream into the data, byte by byte.
-/

namespace VG.Proof.Aes.X86_64

open VG VG.X86_64 VG.X86_64.Straight VG.Bitslice VG.Impl.Aes.X86_64 VG.Proof.Aes

theorem ofInt_nat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq; simp

/-- An access at an offset of a region. -/
theorem in_off {rs : List Region} {b : Addr} {len : Nat} (hr : (⟨b, len⟩ : Region) ∈ rs)
    {off n : Nat} (h : off + n ≤ len) (hl : len < 2 ^ 64) :
    InRegions rs (b + BitVec.ofNat 64 off) n :=
  ⟨_, hr, Offset.contains_base b h (by omega)⟩

theorem q_ctr : ∀ c < 4, q c ≠ sb ∧ q (c + 4) ≠ sb ∧ q c ≠ t0 ∧ q (c + 4) ≠ t0 ∧ q c ≠ q (c + 4) := by
  decide

/-! ## The counter blocks -/

/-- The words of the counter block: bytes 0–7, bytes 8–11, and the counter. -/
abbrev cloW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 54)) 64
abbrev chiW (m : Mem) (b : Addr) : BitVec 64 := m.readW (b + BitVec.ofNat 64 (8 * 55)) 64
abbrev numW (m : Mem) (b : Addr) : BitVec 32 := m.readW (b + BitVec.ofNat 64 (8 * 56)) 32

/-- The high word of counter block `c + i`. -/
def hiWord (hi : BitVec 64) (c : BitVec 32) (i : Nat) : BitVec 64 :=
  hi ^^^ ((bswap32 (c + BitVec.ofNat 32 i)).setWidth 64).rotateRight 32

theorem ctrBlock_ok {s : State} {b : Addr} {c : Nat} (hc : c < 4) (hb : s.gpr sb = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa (ctrBlock c) s = some s' ∧
      s'.gpr (q c) = cloW s.mem b ∧ s'.gpr (q (c + 4)) = hiWord (chiW s.mem b) (numW s.mem b) c ∧
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := q_ctr c hc
  have hw' : (⟨b, 2048⟩ : Region) ∈ s.rd ++ s.wr := List.mem_append_right _ hw
  have i432 := in_off hw' (off := 8 * 54) (n := 8) (by omega) (by omega)
  have i440 := in_off hw' (off := 8 * 55) (n := 8) (by omega) (by omega)
  have i448 := in_off hw' (off := 8 * 56) (n := 4) (by omega) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [ctrBlock, movS, xorR, rorI, slotAt, cLo, cHi, cNum,
      runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, execAlu32, execShift, readSrc,
      readSrc32, State.load64, State.load32, State.ea, ofInt_nat, State.setReg32, State.setReg,
      State.setFlags, arithFlags, hb, h4, h1.symm, h3.symm, h4.symm, h5.symm,
      ite_false, ite_true, i432, i440, i448, Option.map_some, Option.bind_some,
      BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨by simp [h3, h5, cloW], ?_, fun r r1 r2 r3 => by simp [r1, r2, r3], rfl, rfl, rfl⟩
  simp [hiWord, chiW, numW]

theorem ctrBlock_wp {s : State} {b : Addr} {c : Nat} (hc : c < 4) (hb : s.gpr sb = b)
    (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) {P : State → Prop}
    (h : ∀ s', s'.gpr (q c) = cloW s.mem b → s'.gpr (q (c + 4)) = hiWord (chiW s.mem b) (numW s.mem b) c →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      s'.mem = s.mem → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (ctrBlock c)) s P :=
  let ⟨s', hs, h1, h2, h3, h4, h5, h6⟩ := ctrBlock_ok hc hb hw
  WP.of_runBlock ⟨s', hs, h s' h1 h2 h3 h4 h5 h6⟩

/-- `c := c + 4`. -/
theorem ctrNext_ok {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    ∃ s', runBlock isa [.mov32 t0 (.mem (slotAt sb cNum)), .alu32 .add t0 (.imm 4),
        .store32 (slotAt sb cNum) t0] s = some s' ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 56)) (numW s.mem b + 4) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i448 := in_off (List.mem_append_right s.rd hw) (off := 8 * 56) (n := 4) (by omega) (by omega)
  have o448 := in_off hw (off := 8 * 56) (n := 4) (by omega) (by omega)
  refine ⟨_, by
    simp (config := {decide := true}) only [slotAt, cNum, runBlock_cons, runStep_some, runBlock_nil,
      exec, execAlu32, readSrc32, State.load32, State.store32, State.ea, ofInt_nat, State.setReg32,
      State.setReg, State.setFlags, arithFlags, hb, ite_false, ite_true, i448, o448,
      Option.map_some, Option.bind_some, BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq]
    rfl, ?_⟩
  refine ⟨rfl, fun r hr => by simp [hr], rfl, rfl⟩

theorem q_distinct : ∀ c < 4, ∀ d < 4, c ≠ d →
    q c ≠ q d ∧ q c ≠ q (d + 4) ∧ q (c + 4) ≠ q d ∧ q (c + 4) ≠ q (d + 4) := by
  decide

theorem q_not_sb : ∀ c < 8, q c ≠ sb := by decide

/-- The four counter blocks. -/
theorem ctrBlocks_wp {s : State} {b : Addr} (hb : s.gpr sb = b) (hw : (⟨b, 2048⟩ : Region) ∈ s.wr) :
    WP isa (.block ctrBlocks) s fun s' =>
      (∀ c < 4, s'.gpr (q c) = cloW s.mem b ∧
        s'.gpr (q (c + 4)) = hiWord (chiW s.mem b) (numW s.mem b) c) ∧
      (∀ r, r ∉ sboxWrites → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem.writeW (b + BitVec.ofNat 64 (8 * 56)) (numW s.mem b + 4) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  unfold ctrBlocks
  repeat rw [WP.block_append_iff (M := isa)]
  have keep : ∀ {s s' : State} {c : Nat}, c < 4 →
      (∀ r, r ≠ q c → r ≠ q (c + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
      ∀ r, (r ∉ sboxWrites ∨ r = sb) → s'.gpr r = s.gpr r := by
    intro s s' c hc h r hr
    have : r ∉ sboxWrites ∨ r = sb → r ≠ q c ∧ r ≠ q (c + 4) ∧ r ≠ t0 := by
      have := q_ctr c hc
      rintro (hr | rfl)
      · refine ⟨fun h => hr ?_, fun h => hr ?_, fun h => hr (h ▸ by decide)⟩ <;>
          (subst h; unfold q; split <;> decide)
      · exact ⟨this.1.symm, this.2.1.symm, by decide⟩
    exact h r (this hr).1 (this hr).2.1 (this hr).2.2
  refine ctrBlock_wp (c := 0) (by omega) hb hw fun s₁ a₁ b₁ o₁ m₁ rd₁ wr₁ => ?_
  have hb₁ : s₁.gpr sb = b := (keep (by omega) o₁ sb (.inr rfl)).trans hb
  refine ctrBlock_wp (c := 1) (by omega) hb₁ (wr₁ ▸ hw) fun s₂ a₂ b₂ o₂ m₂ rd₂ wr₂ => ?_
  have hb₂ : s₂.gpr sb = b := (keep (by omega) o₂ sb (.inr rfl)).trans hb₁
  refine ctrBlock_wp (c := 2) (by omega) hb₂ (wr₂ ▸ wr₁ ▸ hw) fun s₃ a₃ b₃ o₃ m₃ rd₃ wr₃ => ?_
  have hb₃ : s₃.gpr sb = b := (keep (by omega) o₃ sb (.inr rfl)).trans hb₂
  refine ctrBlock_wp (c := 3) (by omega) hb₃ (wr₃ ▸ wr₂ ▸ wr₁ ▸ hw) fun s₄ a₄ b₄ o₄ m₄ rd₄ wr₄ => ?_
  have hb₄ : s₄.gpr sb = b := (keep (by omega) o₄ sb (.inr rfl)).trans hb₃
  obtain ⟨s₅, hs₅, m₅, o₅, rd₅, wr₅⟩ := ctrNext_ok hb₄ (wr₄ ▸ wr₃ ▸ wr₂ ▸ wr₁ ▸ hw)
  refine WP.of_runBlock ⟨s₅, hs₅, ?_, fun r hr => ?_, ?_, by rw [rd₅, rd₄, rd₃, rd₂, rd₁],
    by rw [wr₅, wr₄, wr₃, wr₂, wr₁]⟩
  · have ht : ∀ c < 8, q c ≠ t0 := by decide
    intro c hc
    rw [o₅ _ (ht c (by omega)), o₅ _ (ht (c + 4) (by omega))]
    have pres : ∀ {s s' : State} (c d : Nat), c < 4 → d < 4 → c ≠ d →
        (∀ r, r ≠ q d → r ≠ q (d + 4) → r ≠ t0 → s'.gpr r = s.gpr r) →
        s'.gpr (q c) = s.gpr (q c) ∧ s'.gpr (q (c + 4)) = s.gpr (q (c + 4)) := by
      intro s s' c d hc hd hcd o
      have := q_distinct c hc d hd hcd
      exact ⟨o _ this.1 this.2.1 (ht c (by omega)), o _ this.2.2.1 this.2.2.2 (ht (c + 4) (by omega))⟩
    rcases (show c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [(pres 0 3 (by omega) (by omega) (by omega) o₄).1, (pres 0 2 (by omega) (by omega) (by omega) o₃).1,
        (pres 0 1 (by omega) (by omega) (by omega) o₂).1, (pres 0 3 (by omega) (by omega) (by omega) o₄).2,
        (pres 0 2 (by omega) (by omega) (by omega) o₃).2, (pres 0 1 (by omega) (by omega) (by omega) o₂).2,
        a₁, b₁]
      exact ⟨rfl, rfl⟩
    · rw [(pres 1 3 (by omega) (by omega) (by omega) o₄).1, (pres 1 2 (by omega) (by omega) (by omega) o₃).1,
        (pres 1 3 (by omega) (by omega) (by omega) o₄).2, (pres 1 2 (by omega) (by omega) (by omega) o₃).2,
        a₂, b₂, m₁]
      exact ⟨rfl, rfl⟩
    · rw [(pres 2 3 (by omega) (by omega) (by omega) o₄).1, (pres 2 3 (by omega) (by omega) (by omega) o₄).2,
        a₃, b₃, m₂, m₁]
      exact ⟨rfl, rfl⟩
    · rw [a₄, b₄, m₃, m₂, m₁]
      exact ⟨rfl, rfl⟩
  · rw [o₅ r (fun h => hr (h ▸ by decide)), keep (by omega) o₄ r (.inl hr), keep (by omega) o₃ r (.inl hr),
      keep (by omega) o₂ r (.inl hr), keep (by omega) o₁ r (.inl hr)]
  · rw [m₅, m₄, m₃, m₂, m₁]

/-! ## The counter blocks as states -/

theorem bswap32_bit (v : BitVec 32) {k j : Nat} (hk : k < 4) (hj : j < 8) :
    (bswap32 v).getLsbD (8 * k + j) = v.getLsbD (8 * (3 - k) + j) := by
  unfold bswap32
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  split_ifs <;> (first | omega | (rw [decide_eq_true (by omega), Bool.true_and]; congr 1; omega))

theorem rot_bit (v : BitVec 32) {p : Nat} (hp : p < 64) :
    ((v.setWidth 64).rotateRight 32).getLsbD p = (decide (32 ≤ p) && v.getLsbD (p - 32)) := by
  rw [BitVec.getLsbD_rotateRight]
  by_cases h : p < 32
  · simp [h, BitVec.getLsbD_setWidth, show ¬ 32 ≤ p by omega]
  · simp [h, show 32 ≤ p by omega, hp, show p - 32 < 64 by omega]

/-- The counter blocks `4g … 4g + 3` in the words, as `InRel` has them. -/
theorem ctr_inRel {Q : Nat → BitVec 64} {icb : Spec.Gcm.Block} {lo hi : BitVec 64} {C : BitVec 32}
    {g : Nat}
    (hlo : ∀ i < 8, ∀ j < 8, lo.getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j))
    (hhi : ∀ i < 4, ∀ j < 8, hi.getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j))
    (hhi' : ∀ p, 32 ≤ p → hi.getLsbD p = false)
    (hC : C = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g))
    (hQ : ∀ c < 4, Q c = lo ∧ Q (c + 4) = hiWord hi C c) :
    InRel Q (fun c => ctrState icb (4 * g + c)) := by
  intro c hc i hi16 j hj
  obtain ⟨h0, h1⟩ := hQ c hc
  simp only [ctrState, getD_eq _ hi16, Vector.getElem_ofFn]
  rw [ctrBlock_byte _ _ hi16]
  by_cases h8 : i < 8
  · rw [show i / 8 = 0 by omega, show i % 8 = i by omega, Nat.mul_zero, Nat.add_zero, h0,
      ite_eq_left (by omega), toBytes_getD _ hi16, BitVec.getLsbD_extractLsb', hlo i h8 j hj]
    simp [hj]
  · rw [show i / 8 = 1 by omega, Nat.mul_one, h1]
    unfold hiWord
    rw [BitVec.getLsbD_xor, rot_bit _ (by omega)]
    by_cases h12 : i < 12
    · rw [ite_eq_left h12, toBytes_getD _ hi16, BitVec.getLsbD_extractLsb', hhi (i % 8) (by omega) j hj]
      simp only [show ¬ 32 ≤ 8 * (i % 8) + j by omega, decide_false, Bool.false_and, Bool.xor_false, hj,
        decide_true, Bool.true_and]
      congr 1; omega
    · rw [ite_eq_right h12, hhi' _ (by omega), BitVec.getLsbD_extractLsb',
        show 8 * (i % 8) + j - 32 = 8 * (i % 8 - 4) + j by omega, bswap32_bit _ (by omega) hj, hC,
        BitVec.add_assoc, ← BitVec.ofNat_add]
      simp only [show 32 ≤ 8 * (i % 8) + j by omega, decide_true, Bool.true_and, Bool.false_xor, hj]
      congr 1; omega

/-! ## XOR into the data -/

/-- XOR `v` into the 8 bytes at `a`. -/
def xorW (m : Mem) (a : Addr) (v : BitVec 64) : Mem := m.writeW a (m.readW a 64 ^^^ v)

theorem xorW_apply (m : Mem) (a x : Addr) (v : BitVec 64) :
    xorW m a v x = if (x - a).toNat < 8 then m x ^^^ v.extractLsb' (8 * (x - a).toNat) 8 else m x := by
  unfold xorW Mem.writeW Mem.write
  split
  · rename_i h
    have hx : a + BitVec.ofNat 64 (x - a).toNat = x := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    have := Mem.extractLsb'_read m a (n := 8) h
    rw [hx] at this
    rw [← this]
    ext t ht
    simp only [BitVec.getElem_extractLsb', BitVec.getElem_xor, Mem.readW]
    simp
  · rfl

/-- XOR two words into the 16 bytes at `a`. -/
theorem xorW2_apply (m : Mem) (a x : Addr) (v₁ v₂ : BitVec 64) :
    xorW (xorW m a v₁) (a + 8) v₂ x =
      if (x - a).toNat < 16 then
        m x ^^^ (if (x - a).toNat < 8 then v₁.extractLsb' (8 * (x - a).toNat) 8
          else v₂.extractLsb' (8 * ((x - a).toNat - 8)) 8)
      else m x := by
  rw [xorW_apply, xorW_apply]
  by_cases h : (x - a).toNat < 8
  · have : ¬ (x - (a + 8)).toNat < 8 := by bv_omega
    rw [ite_eq_right this, ite_eq_left h, ite_eq_left (show (x - a).toNat < 16 by omega), ite_eq_left h]
  · by_cases h' : (x - a).toNat < 16
    · have : (x - (a + 8)).toNat = (x - a).toNat - 8 := by bv_omega
      rw [this, ite_eq_left (show (x - a).toNat - 8 < 8 by omega), ite_eq_right h, ite_eq_left h',
        ite_eq_right h]
    · have : ¬ (x - (a + 8)).toNat < 8 := by bv_omega
      rw [ite_eq_right this, ite_eq_right h, ite_eq_right h']

theorem xorBlock_ok {s : State} {d : Addr} {c : Nat} (hd : s.gpr .rdx = d)
    (h1 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c)) 8)
    (h2 : InRegions s.wr (d + BitVec.ofNat 64 (16 * c) + 8) 8) (hq : q c ≠ t0 ∧ q (c + 4) ≠ t0) :
    ∃ s', runBlock isa (xorBlock c) s = some s' ∧
      s'.mem = xorW (xorW s.mem (d + BitVec.ofNat 64 (16 * c)) (s.gpr (q c)))
        (d + BitVec.ofNat 64 (16 * c) + 8) (s.gpr (q (c + 4))) ∧
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have e2 : d + BitVec.ofNat 64 (16 * c + 8) = d + BitVec.ofNat 64 (16 * c) + 8 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  have i1 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c)) 8 :=
    let ⟨r, hr, h⟩ := h1; ⟨r, List.mem_append_right _ hr, h⟩
  have i2 : InRegions (s.rd ++ s.wr) (d + BitVec.ofNat 64 (16 * c) + 8) 8 :=
    let ⟨r, hr, h⟩ := h2; ⟨r, List.mem_append_right _ hr, h⟩
  refine ⟨_, by
    simp (config := {decide := true}) only [xorBlock, xorR, at_, runBlock_cons, runStep_some,
      runBlock_nil, exec, execAlu, readSrc, State.load64, State.store64, State.ea, ofInt_nat, e2,
      State.setReg, State.setFlags, arithFlags, hd, hq.1, hq.2, ite_false, ite_true, i1, i2, h1, h2,
      Option.map_some, Option.bind_some]
    rfl, ?_⟩
  exact ⟨rfl, fun r hr => by simp [hr], rfl, rfl⟩

/-- The data after `k` blocks: the keystream `ks` XORed into the first
`16 k` of the `16 n` bytes at `D`. -/
def DataInv (m₀ m : Mem) (D : Addr) (n k : Nat) (ks : Nat → Byte) : Prop :=
  ∀ i < 16 * n, m (D + BitVec.ofNat 64 i) =
    m₀ (D + BitVec.ofNat 64 i) ^^^ (if i < 16 * k then ks i else 0)

theorem off_toNat (D : Addr) {i j : Nat} (hi : i < 2 ^ 64) (hj : j < 2 ^ 64) :
    (D + BitVec.ofNat 64 i - (D + BitVec.ofNat 64 j)).toNat =
      if j ≤ i then i - j else 2 ^ 64 + i - j := Offset.sub_toNat' D hj hi

/-- One block of keystream XORed in. -/
theorem dataInv_step {m₀ m : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {v₁ v₂ : BitVec 64}
    (hn : 16 * n ≤ 2 ^ 64) (hk : k < n) (h : DataInv m₀ m D n k ks)
    (hks : ∀ t < 16, (if t < 8 then v₁.extractLsb' (8 * t) 8 else v₂.extractLsb' (8 * (t - 8)) 8) =
      ks (16 * k + t)) :
    DataInv m₀ (xorW (xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂)
        D n (k + 1) ks ∧
      Frame [⟨D, 16 * n⟩] m
        (xorW (xorW m (D + BitVec.ofNat 64 (16 * k)) v₁) (D + BitVec.ofNat 64 (16 * k) + 8) v₂) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · rw [xorW2_apply, off_toNat D (by omega) (by omega), h i hi]
    by_cases h1 : 16 * k ≤ i
    · rw [ite_eq_left h1]
      by_cases h2 : i - 16 * k < 16
      · rw [ite_eq_left h2, hks _ h2, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_left (show i < 16 * (k + 1) by omega), show 16 * k + (i - 16 * k) = i by omega]
        simp
      · rw [ite_eq_right h2, ite_eq_right (show ¬ i < 16 * k by omega),
          ite_eq_right (show ¬ i < 16 * (k + 1) by omega)]
    · rw [ite_eq_right h1, ite_eq_right (show ¬ 2 ^ 64 + i - 16 * k < 16 by omega),
        ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * (k + 1) by omega)]
  · have hx' : ¬ (x - D).toNat + 1 ≤ 16 * n := hx ⟨D, 16 * n⟩ (List.mem_singleton_self _)
    rw [xorW2_apply, ite_eq_right]
    have : 16 * k < 2 ^ 64 := by omega
    have : (BitVec.ofNat 64 (16 * k)).toNat = 16 * k := by simp; omega
    bv_omega

theorem dataInv_mono {m₀ m : Mem} {D : Addr} {n k k' : Nat} {ks : Nat → Byte} (h : DataInv m₀ m D n k ks)
    (hk : n ≤ k) (hk' : n ≤ k') : DataInv m₀ m D n k' ks := by
  intro i hi
  rw [h i hi, ite_eq_left (show i < 16 * k by omega), ite_eq_left (show i < 16 * k' by omega)]

/-- The keystream, byte by byte: byte `i` is byte `i mod 16` of the
encrypted counter block `i / 16`. -/
def keyStream (R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) (i : Nat) : Byte :=
  (Spec.Aes.cipher R w (ctrState icb (i / 16))).getD (i % 16) 0

theorem ks_of_inRel {Q : Nat → BitVec 64} {R g : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (h : InRel Q (fun c => Spec.Aes.cipher R w (ctrState icb (4 * g + c)))) {c t : Nat} (hc : c < 4)
    (ht : t < 16) :
    (Q (c + 4 * (t / 8))).extractLsb' (8 * (t % 8)) 8 = keyStream R w icb (16 * (4 * g + c) + t) := by
  apply byte_ext
  intro j hj
  rw [BitVec.getLsbD_extractLsb', h c hc t ht j hj, keyStream,
    show (16 * (4 * g + c) + t) / 16 = 4 * g + c by omega, show (16 * (4 * g + c) + t) % 16 = t by omega]
  simp [hj]

theorem xorBlock_wp {s : State} {m₀ : Mem} {D : Addr} {n g c : Nat} {ks : Nat → Byte} (hc : c < 4)
    (hk : 4 * g + c < n) (hn : 16 * n < 2 ^ 64) (hD : (⟨D, 16 * n⟩ : Region) ∈ s.wr)
    (hd : s.gpr .rdx = D + BitVec.ofNat 64 (64 * g)) (hinv : DataInv m₀ s.mem D n (4 * g + c) ks)
    (hks : ∀ t < 16, (s.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
      ks (16 * (4 * g + c) + t))
    {P : State → Prop}
    (h : ∀ s', DataInv m₀ s'.mem D n (4 * g + c + 1) ks → Frame [⟨D, 16 * n⟩] s.mem s'.mem →
      (∀ r, r ≠ t0 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → P s') :
    WP isa (.block (xorBlock c)) s P := by
  have ha : D + BitVec.ofNat 64 (64 * g) + BitVec.ofNat 64 (16 * c) =
      D + BitVec.ofNat 64 (16 * (4 * g + c)) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]; congr 2; omega
  have hq : ∀ c < 8, q c ≠ t0 := by decide
  have i1 := in_off hD (off := 16 * (4 * g + c)) (n := 8) (by omega) hn
  have i2 := in_off hD (off := 16 * (4 * g + c) + 8) (n := 8) (by omega) hn
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at i2
  rw [← ha] at i1 i2
  obtain ⟨s', hs', hm, ho, hrd, hwr⟩ :=
    xorBlock_ok hd i1 i2 ⟨hq c (by omega), hq (c + 4) (by omega)⟩
  rw [ha] at hm
  have hst := dataInv_step (v₁ := s.gpr (q c)) (v₂ := s.gpr (q (c + 4))) (by omega) hk hinv
    (fun t ht => by
      rw [← hks t ht]
      by_cases h8 : t < 8
      · rw [ite_eq_left h8, show t / 8 = 0 by omega, show t % 8 = t by omega, Nat.mul_zero, Nat.add_zero]
      · rw [ite_eq_right h8, show t / 8 = 1 by omega, show t % 8 = t - 8 by omega, Nat.mul_one])
  rw [← hm] at hst
  exact WP.of_runBlock ⟨s', hs', h s' hst.1 hst.2 ho hrd hwr⟩

theorem cmp_wp {s : State} {r : Reg} {k : BitVec 32} {K v : Nat} (hr : s.gpr r = BitVec.ofNat 64 v)
    (hv : v < 2 ^ 64) (hk : (k.signExtend 64).toNat = K) {P : State → Prop}
    (h : ∀ s', s'.cf = some (decide (v < K)) → s'.gpr = s.gpr → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → P s') :
    WP isa (.block [.alu .cmp r (.imm k)]) s P := by
  refine WP.of_runBlock ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu,
    readSrc, Option.bind_some]; rfl, ?_⟩
  exact h _ (by simp [arithFlags, State.setFlags, hr, hk]; rw [Nat.mod_eq_of_lt (by simpa using hv)]) rfl rfl rfl rfl

/-! ## The XOR phase of a group -/

/-- After `k` blocks of the group have been XORed in, from `s₃`. -/
structure XS (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) (k : Nat) (s : State) :
    Prop where
  data : DataInv m₀ s.mem D n (4 * g + k) ks
  frame : Frame [⟨D, 16 * n⟩] s₃.mem s.mem
  keep : ∀ r, r ≠ t0 → s.gpr r = s₃.gpr r
  rd : s.rd = s₃.rd
  wr : s.wr = s₃.wr

/-- Before the XOR phase of group `g`: the keystream is in the words. -/
structure XPre (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ : State) : Prop where
  hg : 4 * g < n
  hn : 16 * n < 2 ^ 64
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₃.wr
  rdx : s₃.gpr .rdx = D + BitVec.ofNat 64 (64 * g)
  r8 : s₃.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  data : DataInv m₀ s₃.mem D n (4 * g) ks
  ks : ∀ c < 4, ∀ t < 16, (s₃.gpr (q (c + 4 * (t / 8)))).extractLsb' (8 * (t % 8)) 8 =
    ks (16 * (4 * g + c) + t)

/-- After the XOR phase: ZF is set if no data is left. -/
def XDone (m₀ : Mem) (D : Addr) (n g : Nat) (ks : Nat → Byte) (s₃ s : State) : Prop :=
  Frame [⟨D, 16 * n⟩] s₃.mem s.mem ∧ (∀ r, r ≠ t0 → r ≠ .rdx → r ≠ .r8 → s.gpr r = s₃.gpr r) ∧
    s.rd = s₃.rd ∧ s.wr = s₃.wr ∧
    ((s.zf = some true ∧ DataInv m₀ s.mem D n n ks) ∨
     (s.zf = some false ∧ 4 * g + 4 < n ∧ DataInv m₀ s.mem D n (4 * (g + 1)) ks ∧
      s.gpr .rdx = D + BitVec.ofNat 64 (64 * (g + 1)) ∧ s.gpr .r8 = BitVec.ofNat 64 (n - 4 * (g + 1))))

section Xor

variable {m₀ : Mem} {D : Addr} {n g : Nat} {ks : Nat → Byte} {s₃ : State}

theorem xs_step (hp : XPre m₀ D n g ks s₃) {k : Nat} (hk : k < 4) (hkn : 4 * g + k < n) {s : State}
    (hs : XS m₀ D n g ks s₃ k s) {P : State → Prop} (h : ∀ s', XS m₀ D n g ks s₃ (k + 1) s' → P s') :
    WP isa (.block (xorBlock k)) s P := by
  have hq : ∀ c < 8, q c ≠ t0 := by decide
  refine xorBlock_wp hk hkn hp.hn (hs.wr ▸ hp.dat) (by rw [hs.keep _ (by decide)]; exact hp.rdx)
    hs.data (fun t ht => by rw [hs.keep _ (hq _ (by omega))]; exact hp.ks k hk t ht)
    fun s' d f o rd wr => h s' ⟨d, hs.frame.trans f, fun r hr => (o r hr).trans (hs.keep r hr),
      rd.trans hs.rd, wr.trans hs.wr⟩

theorem xs_zero (hp : XPre m₀ D n g ks s₃) {s : State} (hg : s.gpr = s₃.gpr) (hm : s.mem = s₃.mem)
    (hrd : s.rd = s₃.rd) (hwr : s.wr = s₃.wr) : XS m₀ D n g ks s₃ 0 s :=
  ⟨by rw [hm, Nat.add_zero]; exact hp.data, by rw [hm]; exact Frame.refl _ _,
    fun r _ => by rw [hg], hrd, hwr⟩

theorem advance_ok (s : State) :
    ∃ s', runBlock isa [.alu .add .rdx (.imm 64), .alu .sub .r8 (.imm 4)] s = some s' ∧
      s'.gpr .rdx = s.gpr .rdx + 64 ∧ s'.gpr .r8 = s.gpr .r8 - 4 ∧ s'.zf = some (s.gpr .r8 - 4 == 0) ∧
      (∀ r, r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧
      s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags, show (4 : BitVec 32).signExtend 64 = 4 by decide,
    show (64 : BitVec 32).signExtend 64 = 64 by decide]
  exact ⟨by simp, by simp, rfl, fun r h1 h2 => by simp [h1, h2], trivial, trivial, trivial⟩

theorem clear_ok (s : State) :
    ∃ s', runBlock isa [.alu .sub .r8 (.reg .r8)] s = some s' ∧ s'.zf = some true ∧
      (∀ r, r ≠ .r8 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc,
    Option.bind_some]; rfl, ?_⟩
  simp only [State.setReg, arithFlags, State.setFlags]
  exact ⟨by simp, fun r h => by simp [h], trivial, trivial, trivial⟩

theorem xorFull_eq : xorFull = xorBlock 0 ++ xorBlock 1 ++ xorBlock 2 ++ xorBlock 3 ++
    ([.alu .add .rdx (.imm 64), .alu .sub .r8 (.imm 4)] : List Instr) := rfl

theorem ofNat_sub_four {x : Nat} (h : 4 ≤ x) : BitVec.ofNat 64 x - 4 = BitVec.ofNat 64 (x - 4) := Offset.ofNat_sub_ofNat h

theorem ofNat_sub_four_ne {x : Nat} (hx : x < 2 ^ 64) (h : 4 ≤ x) (hne : x ≠ 4) :
    BitVec.ofNat 64 x - 4 ≠ 0 := by
  bv_omega

theorem off_add64 (D : Addr) (g : Nat) :
    D + BitVec.ofNat 64 (64 * g) + 64 = D + BitVec.ofNat 64 (64 * (g + 1)) := (Offset.add_add D _ 64).trans (by rw [show 64 * g + 64 = 64 * (g + 1) by omega])

theorem xorPhase_wp (hp : XPre m₀ D n g ks s₃) :
    WP isa (.seq (.block [.alu .cmp .r8 (.imm 4)]) (.ite .ae (.block xorFull) xorTail)) s₃
      (XDone m₀ D n g ks s₃) := by
  have hg := hp.hg
  have hn := hp.hn
  refine WP.seq (cmp_wp hp.r8 (by omega) (K := 4) (by decide) fun s₄ cf₄ g₄ m₄ rd₄ wr₄ => ?_)
  have x₀ := xs_zero hp g₄ m₄ rd₄ wr₄
  refine WP.ite (!decide (n - 4 * g < 4)) (by simp [X86_64.eval, cf₄]) (fun hb => ?_) (fun hb => ?_)
  · -- Four blocks.
    have h4 : 4 ≤ n - 4 * g := by simpa using hb
    rw [xorFull_eq]
    repeat rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₅ x₅ => ?_
    refine xs_step hp (k := 1) (by omega) (by omega) x₅ fun s₆ x₆ => ?_
    refine xs_step hp (k := 2) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
    refine xs_step hp (k := 3) (by omega) (by omega) x₇ fun s₈ x₈ => ?_
    obtain ⟨s₉, hs₉, d₉, r₉, z₉, o₉, m₉, rd₉, wr₉⟩ := advance_ok s₈
    refine WP.of_runBlock ⟨s₉, hs₉, ?_⟩
    have e₁ : s₈.gpr .rdx = D + BitVec.ofNat 64 (64 * g) := (x₈.keep _ (by decide)).trans hp.rdx
    have e₂ : s₈.gpr .r8 = BitVec.ofNat 64 (n - 4 * g) := (x₈.keep _ (by decide)).trans hp.r8
    refine ⟨m₉ ▸ x₈.frame, fun r h1 h2 h3 => (o₉ r h2 h3).trans (x₈.keep r h1), rd₉.trans x₈.rd,
      wr₉.trans x₈.wr, ?_⟩
    rw [z₉, e₂, m₉]
    by_cases hl : n - 4 * g = 4
    · refine .inl ⟨?_, dataInv_mono x₈.data (by omega) (by omega)⟩
      rw [hl]; rfl
    · refine .inr ⟨?_, by omega, by simpa [Nat.mul_add] using x₈.data, ?_, ?_⟩
      · simp only [Option.some.injEq, beq_eq_false_iff_ne]
        exact ofNat_sub_four_ne (by omega) h4 hl
      · rw [d₉, e₁]; exact off_add64 D g
      · rw [r₉, e₂, ofNat_sub_four h4, show n - 4 * (g + 1) = n - 4 * g - 4 by omega]
  · -- The last one to three blocks.
    have h4 : n - 4 * g < 4 := by simpa using hb
    unfold xorTail
    refine WP.seq ?_
    rw [WP.block_append_iff (M := isa)]
    refine xs_step hp (k := 0) (by omega) (by omega) x₀ fun s₅ x₅ => ?_
    refine cmp_wp ((x₅.keep _ (by decide)).trans hp.r8) (by omega) (K := 2) (by decide)
      fun s₆ cf₆ g₆ m₆ rd₆ wr₆ => ?_
    have x₆ : XS m₀ D n g ks s₃ 1 s₆ := ⟨m₆ ▸ x₅.data, m₆ ▸ x₅.frame,
      fun r h => by rw [g₆]; exact x₅.keep r h, rd₆.trans x₅.rd, wr₆.trans x₅.wr⟩
    refine WP.seq (WP.mono (Q := XS m₀ D n g ks s₃ (n - 4 * g)) ?_ fun s hs => ?_)
    · refine WP.ite (!decide (n - 4 * g < 2)) (by simp [X86_64.eval, cf₆]) (fun hb => ?_) (fun hb => ?_)
      · have h2 : 2 ≤ n - 4 * g := by simpa using hb
        refine WP.seq ?_
        rw [WP.block_append_iff (M := isa)]
        refine xs_step hp (k := 1) (by omega) (by omega) x₆ fun s₇ x₇ => ?_
        refine cmp_wp ((x₇.keep _ (by decide)).trans hp.r8) (by omega) (K := 3) (by decide)
          fun s₈ cf₈ g₈ m₈ rd₈ wr₈ => ?_
        have x₈ : XS m₀ D n g ks s₃ 2 s₈ := ⟨m₈ ▸ x₇.data, m₈ ▸ x₇.frame,
          fun r h => by rw [g₈]; exact x₇.keep r h, rd₈.trans x₇.rd, wr₈.trans x₇.wr⟩
        refine WP.ite (!decide (n - 4 * g < 3)) (by simp [X86_64.eval, cf₈]) (fun hb => ?_) (fun hb => ?_)
        · have h3 : n - 4 * g = 2 + 1 := by simp at hb; omega
          refine xs_step hp (k := 2) (by omega) (by omega) x₈ fun s₉ x₉ => ?_
          rw [h3]; exact x₉
        · have h3 : n - 4 * g = 2 := by simp at hb; omega
          exact WP.block_nil (by rw [h3]; exact x₈)
      · have h1 : n - 4 * g = 1 := by simp at hb; omega
        exact WP.block_nil (by rw [h1]; exact x₆)
    · obtain ⟨s', hs', z', o', m', rd', wr'⟩ := clear_ok s
      refine WP.of_runBlock ⟨s', hs', m' ▸ hs.frame, fun r h1 _ h3 => (o' r h3).trans (hs.keep r h1),
        rd'.trans hs.rd, wr'.trans hs.wr, .inl ⟨z', ?_⟩⟩
      have := hs.data
      rw [show 4 * g + (n - 4 * g) = n by omega, ← m'] at this
      exact this

end Xor

/-! ## A group -/

/-- What the group loop runs with: `s₂` is the state after the round keys
are bitsliced, `b` the scratch buffer, `D` the data (`n` blocks, whose
bytes were `m₀`'s), `icb` the first counter block. -/
structure GSetup (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte) (icb : Spec.Gcm.Block) :
    Prop where
  scr : (⟨b, 2048⟩ : Region) ∈ s₂.wr
  dat : (⟨D, 16 * n⟩ : Region) ∈ s₂.wr
  hn : 16 * n < 2 ^ 64
  sep : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 2048⟩
  rounds : R = 10 ∨ R = 12 ∨ R = 14
  keys : KeysAt s₂.mem (b + BitVec.ofNat 64 (1920 - 64 * R)) R w
  lo : ∀ i < 8, ∀ j < 8, (cloW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (15 - i) + j)
  hi : ∀ i < 4, ∀ j < 8, (chiW s₂.mem b).getLsbD (8 * i + j) = icb.getLsbD (8 * (7 - i) + j)
  hi' : ∀ p, 32 ≤ p → (chiW s₂.mem b).getLsbD p = false

/-- The memory a group writes: slots 0–47, the counter and the data. -/
abbrev gRegions (b D : Addr) (n : Nat) : List Region :=
  [⟨b, 384⟩, ⟨b + BitVec.ofNat 64 (8 * 56), 4⟩, ⟨D, 16 * n⟩]

/-- Before group `g`. -/
structure GInv (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (g : Nat) (s : State) : Prop where
  hg : 4 * g < n
  rdx : s.gpr .rdx = D + BitVec.ofNat 64 (64 * g)
  r8 : s.gpr .r8 = BitVec.ofNat 64 (n - 4 * g)
  base : s.gpr sb = b
  rdi : s.gpr .rdi = b + BitVec.ofNat 64 (1920 - 64 * R)
  rsp : s.gpr .rsp = s₂.gpr .rsp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions b D n) s₂.mem s.mem
  num : numW s.mem b = icb.extractLsb' 0 32 + BitVec.ofNat 32 (4 * g)
  data : DataInv m₀ s.mem D n (4 * g) (keyStream R w icb)

/-- After the last group. -/
structure GDone (m₀ : Mem) (s₂ : State) (b D : Addr) (n R : Nat) (w : List Byte)
    (icb : Spec.Gcm.Block) (s : State) : Prop where
  base : s.gpr sb = b
  rsp : s.gpr .rsp = s₂.gpr .rsp
  rd : s.rd = s₂.rd
  wr : s.wr = s₂.wr
  frame : Frame (gRegions b D n) s₂.mem s.mem
  data : DataInv m₀ s.mem D n n (keyStream R w icb)

theorem scr_disj (b : Addr) {lx y ly : Nat} (h : lx ≤ y) (hy : y + ly ≤ 2048) :
    Region.Disjoint ⟨b, lx⟩ ⟨b + BitVec.ofNat 64 y, ly⟩ := Offset.base_disjoint b h (by omega)

theorem scr_sub (b : Addr) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Sub ⟨b + BitVec.ofNat 64 x, lx⟩ ⟨b, 2048⟩ := Offset.sub_base b h

theorem keysAt_frame {m m' : Mem} {b : Addr} {R : Nat} {w : List Byte} {rs : List Region}
    (hR : R ≤ 14) (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨b + 1024, 1024⟩ r)
    (h : KeysAt m (b + BitVec.ofNat 64 (1920 - 64 * R)) R w) :
    KeysAt m' (b + BitVec.ofNat 64 (1920 - 64 * R)) R w :=
  fun j hj => keyRel_congr (h j hj) fun k hk => hf.readW (key_contains _ hR hj hk) hd (by decide)

theorem dataInv_frame {m₀ m m' : Mem} {D : Addr} {n k : Nat} {ks : Nat → Byte} {rs : List Region}
    (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨D, 16 * n⟩ r) (hn : 16 * n < 2 ^ 64)
    (h : DataInv m₀ m D n k ks) : DataInv m₀ m' D n k ks := fun i hi => by
  rw [← h i hi]
  exact hf.bytes (R := ⟨D, 16 * n⟩) hd (by simp only; omega) hi

theorem GSetup.dat_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) {x lx : Nat} (h : x + lx ≤ 2048) :
    Region.Disjoint ⟨D, 16 * n⟩ ⟨b + BitVec.ofNat 64 x, lx⟩ :=
  hs.sep.sub_right (scr_sub b h)

theorem GSetup.keys_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + 1024, 1024⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact keys_disjoint b
  · intro a h₁ h₂
    simp only [Region.Contains] at h₁ h₂
    have : (BitVec.ofNat 64 (8 * 56)).toNat = 448 := by simp
    bv_omega
  · refine (hs.sep.sub_right fun a h => ?_).symm
    simp only [Region.Contains] at h ⊢
    bv_omega

theorem GSetup.slot_disj {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte} {icb : Spec.Gcm.Block}
    (hs : GSetup s₂ b D n R w icb) {x lx : Nat} (h1 : 384 ≤ x) (h2 : x + lx ≤ 448 ∨ 452 ≤ x)
    (h3 : x + lx ≤ 2048) : ∀ r ∈ gRegions b D n, Region.Disjoint ⟨b + BitVec.ofNat 64 x, lx⟩ r := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact (scr_disj b h1 h3).symm
  · exact Offset.disjoint b (by omega) (by omega) (by omega)
  · exact (hs.dat_disj h3).symm

/-- One group: from before group `g`, to after the last group (ZF set) or
before group `g + 1`. -/
theorem group_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b D n R w icb) {g : Nat} {s : State}
    (hi : GInv m₀ s₂ b D n R w icb g s) :
    WP isa group s fun s' => (s'.zf = some true ∧ GDone m₀ s₂ b D n R w icb s') ∨
      (s'.zf = some false ∧ GInv m₀ s₂ b D n R w icb (g + 1) s') := by
  have hR : R ≤ 14 := by rcases hs.rounds with h | h | h <;> omega
  have hn := hs.hn
  have hscr : (⟨b, 2048⟩ : Region) ∈ s.wr := hi.wr ▸ hs.scr
  unfold group
  refine WP.seq (WP.mono (ctrBlocks_wp hi.base hscr) fun s₁ ⟨hq₁, o₁, m₁, rd₁, wr₁⟩ => ?_)
  have hb₁ : s₁.gpr sb = b := (o₁ sb (by decide)).trans hi.base
  have c448 : (⟨b + BitVec.ofNat 64 (8 * 56), 4⟩ : Region).Contains
      (b + BitVec.ofNat 64 (8 * 56)) (32 / 8) := Region.contains_self _ _
  have f₁ : Frame [⟨b + BitVec.ofNat 64 (8 * 56), 4⟩] s.mem s₁.mem := by
    rw [m₁]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ c448
  have hf₁ : Frame (gRegions b D n) s₂.mem s₁.mem :=
    hi.frame.trans (f₁.mono fun r hr => by simp at hr; simp [hr])
  have clo : cloW s.mem b = cloW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega) (by omega) (by omega)) (by decide)
  have chi : chiW s.mem b = chiW s₂.mem b :=
    hi.frame.readW (Region.contains_self _ _) (hs.slot_disj (by omega) (by omega) (by omega)) (by decide)
  have hp : EncPre s₁ R w :=
    ⟨by rw [hb₁, wr₁, hi.wr]; exact hs.scr, hs.rounds, by rw [o₁ .rdi (by decide), hi.rdi, hb₁],
      by rw [o₁ .rdi (by decide), hi.rdi]; exact keysAt_frame hR hf₁ hs.keys_disj hs.keys⟩
  have hin : InRel (Q s₁) (fun c => ctrState icb (4 * g + c)) :=
    ctr_inRel (by rw [clo]; exact hs.lo) (by rw [chi]; exact hs.hi) (by rw [chi]; exact hs.hi') hi.num
      hq₁
  refine WP.seq (WP.mono (encrypt4_ok hp hin) fun s₃ ⟨hc₃, hin₃⟩ => ?_)
  have fr₃ := hc₃.frame
  rw [hb₁] at fr₃
  have d384 : Region.Disjoint ⟨D, 16 * n⟩ ⟨b, 384⟩ := hs.sep.sub_right (Region.sub_prefix (by omega))
  have hx : XPre m₀ D n g (keyStream R w icb) s₃ :=
    { hg := hi.hg, hn := hn, dat := by rw [hc₃.wr, wr₁, hi.wr]; exact hs.dat
      rdx := by rw [hc₃.keep .rdx (by decide) (by decide), o₁ .rdx (by decide), hi.rdx]
      r8 := by rw [hc₃.keep .r8 (by decide) (by decide), o₁ .r8 (by decide), hi.r8]
      data := dataInv_frame fr₃ (by simpa using d384) hn
        (dataInv_frame f₁ (by simpa using hs.dat_disj (by omega)) hn hi.data)
      ks := fun c hc t ht => ks_of_inRel hin₃ hc ht }
  refine WP.mono (xorPhase_wp hx) fun s' ⟨f', o', rd', wr', hz⟩ => ?_
  have keep : ∀ r, r ∉ sboxWrites → r ≠ kp → r ≠ .rdx → r ≠ .r8 → s'.gpr r = s.gpr r :=
    fun r h1 h2 h3 h4 => (o' r (fun h => h1 (h ▸ by decide)) h3 h4).trans ((hc₃.keep r h1 h2).trans (o₁ r h1))
  have base' : s'.gpr sb = b := (keep sb (by decide) (by decide) (by decide) (by decide)).trans hi.base
  have rsp' : s'.gpr .rsp = s₂.gpr .rsp :=
    (keep .rsp (by decide) (by decide) (by decide) (by decide)).trans hi.rsp
  have rd'' : s'.rd = s₂.rd := by rw [rd', hc₃.rd, rd₁, hi.rd]
  have wr'' : s'.wr = s₂.wr := by rw [wr', hc₃.wr, wr₁, hi.wr]
  have frame' : Frame (gRegions b D n) s₂.mem s'.mem :=
    hf₁.trans ((fr₃.mono fun r hr => by simp at hr; simp [hr]).trans (f'.mono fun r hr => by simp at hr; simp [hr]))
  rcases hz with ⟨z, d⟩ | ⟨z, h4, d, rdx', r8'⟩
  · exact .inl ⟨z, base', rsp', rd'', wr'', frame', d⟩
  · refine .inr ⟨z, ⟨by omega, rdx', r8', base', ?_, rsp', rd'', wr'', frame', ?_, d⟩⟩
    · rw [keep .rdi (by decide) (by decide) (by decide) (by decide), hi.rdi]
    · have e₁ : numW s'.mem b = numW s₃.mem b :=
        f'.readW (Region.contains_self _ _) (by simpa using (hs.dat_disj (by omega)).symm) (by decide)
      have e₂ : numW s₃.mem b = numW s₁.mem b :=
        fr₃.readW (Region.contains_self _ _) (by simpa using (scr_disj b (by omega) (by omega)).symm)
          (by decide)
      rw [e₁, e₂, m₁, numW, Mem.readW_writeW_self32, hi.num, BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      simp
      omega

/-- The loop over the groups. -/
theorem groups_ok {m₀ : Mem} {s₂ : State} {b D : Addr} {n R : Nat} {w : List Byte}
    {icb : Spec.Gcm.Block} (hs : GSetup s₂ b D n R w icb) {s : State}
    (hi : GInv m₀ s₂ b D n R w icb 0 s) :
    WP isa (.loop group .ne) s (GDone m₀ s₂ b D n R w icb) := by
  refine WP.loop (M := isa) (fun k s => ∃ g, k = n - 4 * g ∧ GInv m₀ s₂ b D n R w icb g s)
    (fun k s ⟨g, hk, hg⟩ => WP.mono (group_ok hs hg) fun s' h => ?_) n s ⟨0, by omega, hi⟩
  rcases h with ⟨z, d⟩ | ⟨z, d⟩
  · exact .inl ⟨by simp [X86_64.eval, z], d⟩
  · exact .inr ⟨by simp [X86_64.eval, z], n - 4 * (g + 1), by have := hg.hg; omega, g + 1, rfl, d⟩

end VG.Proof.Aes.X86_64
