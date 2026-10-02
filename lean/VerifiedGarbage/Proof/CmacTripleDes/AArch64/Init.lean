import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Update
import VerifiedGarbage.Proof.CmacTripleDes.AArch64.Keys

/-!
# TDEA-CMAC on AArch64: `vg_cmac_triple_des_init`

`initPre` stores the three DES keys, as big-endian integers, in slots 6–8;
each iteration of the loop then writes one DES key's sixteen round keys
(`KInv`); the zero block is encrypted with them and doubled twice into the
subkeys.
-/

namespace VG.Proof.CmacTripleDes.AArch64

open VG VG.AArch64 VG.AArch64.RegUpd VG.AArch64.Straight VG.Impl.CmacTripleDes.AArch64 VG.Proof.CmacTripleDes
  VG.Proof.Cmac

section
variable (s₀ : State)

abbrev K : Addr := s₀.gpr .x0
abbrev Kl : Nat := (s₀.gpr .x1).toNat
abbrev O : Addr := s₀.gpr .x2
abbrev Sc : Addr := s₀.gpr .x3

/-- The key's bytes. -/
abbrev keyB : List Byte := Spec.Aes.bytesAt s₀.mem (K s₀) (Kl s₀)

/-- DES key `j`, as a big-endian integer. -/
abbrev kw (j : Nat) : BitVec 64 := byteRev64 (s₀.mem.readW (K s₀ + BitVec.ofNat 64 (keyOff (Kl s₀) j)) 64)

end

/-- The precondition, by name. -/
structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨K s₀, Kl s₀⟩]
  wr : s₀.wr = [⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩]
  key_out : (⟨K s₀, Kl s₀⟩ : Region).Disjoint ⟨O s₀, 400⟩
  key_scr : (⟨K s₀, Kl s₀⟩ : Region).Disjoint ⟨Sc s₀, 640⟩
  out_scr : (⟨O s₀, 400⟩ : Region).Disjoint ⟨Sc s₀, 640⟩
  key_wrap : (K s₀).toNat + Kl s₀ ≤ 2 ^ 64
  out_wrap : (O s₀).toNat + 400 ≤ 2 ^ 64
  scr_wrap : (Sc s₀).toNat + 640 ≤ 2 ^ 64
  valid : Kl s₀ = 16 ∨ Kl s₀ = 24

theorem IPre.of {s₀ : State} (h : initAArch64.pre s₀) : IPre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i⟩ := h
  ⟨a, b, c, d, e, f, g, h, i⟩

/-- After the round keys of `i` DES keys. -/
structure KInv (s₀ : State) (i : Nat) (s : State) : Prop where
  x15 : s.gpr .x15 = Sc s₀
  x4 : s.gpr .x4 = Sc s₀ + BitVec.ofNat 64 (48 + 8 * i)
  x2 : s.gpr .x2 = O s₀ + BitVec.ofNat 64 (128 * i)
  x3 : s.gpr .x3 = BitVec.ofNat 64 (3 - i)
  sp : s.sp = s₀.sp
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  keys : ∀ j < 3, s.mem.readW (Sc s₀ + BitVec.ofNat 64 (48 + 8 * j)) 64 = kw s₀ j
  sched : ∀ n < 16 * i, s.mem.readW (O s₀ + BitVec.ofNat 64 (8 * n)) 64 =
    (Spec.TripleDes.expandKey (keyB s₀)).getD n 0
  frame : Frame [⟨Sc s₀ + BitVec.ofNat 64 48, 24⟩, ⟨O s₀, 384⟩] s₀.mem s.mem

/-! ## The prologue -/

theorem keyOff_le {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 3) : keyOff (Kl s₀) j + 8 ≤ Kl s₀ := by
  simp only [keyOff]; rcases hp.valid with h | h <;> rw [h] <;> split <;> omega

section
variable {s₀ : State} (hp : IPre s₀)
include hp

theorem IPre.inScr {d n : Nat} (h : d + n ≤ 640) : InRegions s₀.wr (Sc s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨Sc s₀, 640⟩) (by simp) (Offset.contains_base _ h (by have := hp.scr_wrap; omega))

theorem IPre.inOut {d n : Nat} (h : d + n ≤ 400) : InRegions s₀.wr (O s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.wr]; exact in_rw (r := ⟨O s₀, 400⟩) (by simp) (Offset.contains_base _ h (by have := hp.out_wrap; omega))

theorem IPre.inKey {d n : Nat} (h : d + n ≤ Kl s₀) (hn : 0 < n) :
    InRegions (s₀.rd ++ s₀.wr) (K s₀ + BitVec.ofNat 64 d) n := by
  rw [hp.rd]; exact in_rw (r := ⟨K s₀, Kl s₀⟩) (by simp) (Offset.contains_base _ h (by have := hp.key_wrap; omega))

/-- The key is unchanged while only the scratch buffer changes. -/
theorem IPre.keyRead {m : Mem} (hf : Frame [⟨Sc s₀, 640⟩] s₀.mem m) {d : Nat} (hd : d + 8 ≤ Kl s₀) :
    m.readW (K s₀ + BitVec.ofNat 64 d) 64 = s₀.mem.readW (K s₀ + BitVec.ofNat 64 d) 64 :=
  hf.readW (r := ⟨K s₀ + BitVec.ofNat 64 d, 8⟩) (Region.contains_self _ _) (fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact hp.key_scr.sub_left (Offset.sub_base _ hd)) (by decide)

end

theorem readW_writeW_other (m : Mem) (b : Addr) {d e : Nat} (v : BitVec 64) (h : d + 8 ≤ e ∨ e + 8 ≤ d)
    (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    (m.writeW (b + BitVec.ofNat 64 e) v).readW (b + BitVec.ofNat 64 d) 64 = m.readW (b + BitVec.ofNat 64 d) 64 :=
  Mem.readW_writeW_sep (Offset.sep b h hd he) (by decide)

theorem scrSub {S : Addr} {d n : Nat} (h : d + n ≤ 640) : Region.Sub ⟨S + BitVec.ofNat 64 d, n⟩ ⟨S, 640⟩ :=
  Offset.sub_base _ h

/-- A DES key loaded, reversed and stored. -/
theorem keyWord_ok (s : State) (d o : Nat) (hd : d % 8 = 0 ∧ d < 32768) (ho : o % 8 = 0 ∧ o < 32768)
    (r : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 8)
    (w : InRegions s.wr (s.gpr .x15 + BitVec.ofNat 64 o) 8) :
    ∃ s', runBlock isa (keyWord d o) s = some s' ∧
      s'.mem = s.mem.writeW (s.gpr .x15 + BitVec.ofNat 64 o)
        (byteRev64 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64)) ∧
      (∀ r, r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  let s₁ := (s.write .x .x5 (s.mem.readW (s.gpr .x0 + BitVec.ofNat 64 d) 64))
  let s₂ := s₁.write .x .x5 (rev64 (s₁.read .x .x5))
  have w' : InRegions s₂.wr (s₂.gpr .x15 + BitVec.ofNat 64 o) 8 := by
    rw [gpr_write_of_ne _ _ _ (by decide), gpr_write_of_ne _ _ _ (by decide)]; exact w
  refine ⟨_, by
    rw [keyWord, runBlock_cons, exec_ldr_x hd r, runStep_some, runBlock_cons, exec_rev, runStep_some,
      runBlock_cons, exec_str_x ho w', runStep_some, runBlock_nil], ?_⟩
  refine ⟨?_, fun r hr => by simp [s₁, s₂, gpr_write, hr], rfl, rfl, rfl⟩
  simp (config := {decide := true}) only [s₁, s₂, mem_write, State.read, gpr_write, ite_true, ite_false,
    BitVec.setWidth_eq, rev64_eq]

theorem initPre_wp {s₀ : State} (hp : IPre s₀) : WP isa initPre s₀ (KInv s₀ 0) := by
  have sw := hp.scr_wrap
  have kl : 16 ≤ Kl s₀ := by rcases hp.valid with h | h <;> omega
  -- `mov x15, x3`.
  let s₁ := s₀.write .x .x15 (s₀.gpr .x3)
  have g₁ : ∀ r, r ≠ .x15 → s₁.gpr r = s₀.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have x15₁ : s₁.gpr .x15 = Sc s₀ := by simp [s₁, gpr_write]
  obtain ⟨s₂, run₂, m₂, g₂, sp₂, rd₂, wr₂⟩ := keyWord_ok s₁ 0 48 (by decide) (by decide)
    (by rw [g₁ _ (by decide)]; exact hp.inKey (d := 0) (n := 8) (by omega) (by decide))
    (by rw [x15₁]; exact hp.inScr (by decide))
  obtain ⟨s₃, run₃, m₃, g₃, sp₃, rd₃, wr₃⟩ := keyWord_ok s₂ 8 56 (by decide) (by decide)
    (by rw [rd₂, wr₂, g₂ _ (by decide), g₁ _ (by decide)]; exact hp.inKey (d := 8) (n := 8) (by omega) (by decide))
    (by rw [wr₂, g₂ _ (by decide), x15₁]; exact hp.inScr (by decide))
  refine WP.seq (WP.of_runBlock ⟨_, by
    rw [runBlock_append, runBlock_append, runBlock_append, runBlock_cons, exec_mov, runStep_some, runBlock_nil,
      Option.bind_some, run₂, Option.bind_some, run₃, Option.bind_some, runBlock_cons,
      exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩)
  let s₄ := s₃.write .x .x9 (s₃.read .x .x1 - BitVec.ofNat _ 16)
  have g₄ : ∀ r, r ≠ .x9 → r ≠ .x5 → r ≠ .x15 → s₄.gpr r = s₀.gpr r := fun r h₁ h₂ h₃ => by
    rw [gpr_write_of_ne _ _ _ h₁, g₃ r h₂, g₂ r h₂, g₁ r h₃]
  have x15₄ : s₄.gpr .x15 = Sc s₀ := by rw [gpr_write_of_ne _ _ _ (by decide), g₃ _ (by decide), g₂ _ (by decide), x15₁]
  -- The memory so far.
  have c48 : (⟨Sc s₀ + BitVec.ofNat 64 48, 24⟩ : Region).Contains (Sc s₀ + BitVec.ofNat 64 48) (64 / 8) := by
    simpa using Offset.contains_base (Sc s₀ + BitVec.ofNat 64 48) (d := 0) (n := 8) (k := 24) (by decide) (by decide)
  have cAt (d : Nat) (h₁ : 48 ≤ d) (h₂ : d + 8 ≤ 72) :
      (⟨Sc s₀ + BitVec.ofNat 64 48, 24⟩ : Region).Contains (Sc s₀ + BitVec.ofNat 64 d) (64 / 8) := by
    rw [show Sc s₀ + BitVec.ofNat 64 d = Sc s₀ + BitVec.ofNat 64 48 + BitVec.ofNat 64 (d - 48) from
      (Offset.add_add_eq _ (by omega)).symm]
    exact Offset.contains_base _ (by omega) (by omega)
  have f₃ : Frame [⟨Sc s₀ + BitVec.ofNat 64 48, 24⟩] s₀.mem s₃.mem := by
    rw [m₃, m₂, g₂ _ (by decide), x15₁]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c48).writeW (List.mem_singleton_self _) _
      (cAt 56 (by decide) (by decide))
  have fA : Frame [⟨Sc s₀, 640⟩] s₀.mem s₃.mem := f₃.sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr; exact ⟨_, List.mem_singleton_self _, scrSub (by decide)⟩
  have fA₂ : Frame [⟨Sc s₀, 640⟩] s₀.mem s₂.mem := by
    rw [m₂, x15₁]
    exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Offset.contains_base _ (by omega) (by omega))
  have k0 : s₃.mem.readW (Sc s₀ + BitVec.ofNat 64 48) 64 = kw s₀ 0 := by
    rw [m₃, g₂ _ (by decide), x15₁, readW_writeW_other _ _ _ (by decide) (by decide) (by decide), m₂, x15₁,
      Mem.readW_writeW_self64, g₁ _ (by decide)]
    simp [kw, keyOff]
    rfl
  have k1 : s₃.mem.readW (Sc s₀ + BitVec.ofNat 64 56) 64 = kw s₀ 1 := by
    rw [m₃, g₂ _ (by decide), x15₁, Mem.readW_writeW_self64, g₂ _ (by decide), g₁ _ (by decide),
      hp.keyRead fA₂ (d := 8) (by omega)]
    simp [kw, keyOff]
  -- The third DES key.
  have ev : isa.eval (.zero .x .x9) s₄ = some (decide (Kl s₀ = 16)) := by
    show some (_ == 0) = _
    simp only [s₄, State.read, gpr_write_self, BitVec.setWidth_eq]
    rw [g₃ _ (by decide), g₂ _ (by decide), g₁ _ (by decide),
      show s₀.gpr .x1 = BitVec.ofNat 64 (Kl s₀) by apply BitVec.eq_of_toNat_eq; simp,
      Offset.ofNat_sub_ofNat_beq (by have := (s₀.gpr .x1).isLt; omega) (by decide)]
  have third : ∀ d, d + 8 ≤ Kl s₀ → d % 8 = 0 → d < 32768 →
      WP isa (.block [.ldr .x .x5 .x0 d]) s₄ fun s₅ =>
        s₅.gpr .x5 = s₀.mem.readW (K s₀ + BitVec.ofNat 64 d) 64 ∧ (∀ r, r ≠ .x5 → s₅.gpr r = s₄.gpr r) ∧
        s₅.sp = s₀.sp ∧ s₅.mem = s₃.mem ∧ s₅.rd = s₀.rd ∧ s₅.wr = s₀.wr := by
    intro d hd h8 hl
    have r : InRegions (s₄.rd ++ s₄.wr) (s₄.gpr .x0 + BitVec.ofNat 64 d) 8 := by
      rw [g₄ _ (by decide) (by decide) (by decide)]
      show InRegions (s₃.rd ++ s₃.wr) _ 8
      rw [rd₃, wr₃, rd₂, wr₂]; exact hp.inKey (by omega) (by decide)
    refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr_x ⟨h8, hl⟩ r, runStep_some, runBlock_nil], ?_⟩
    refine ⟨?_, fun r hr => gpr_write_of_ne _ _ _ hr, by show s₃.sp = s₀.sp; rw [sp₃, sp₂]; rfl, rfl,
      by show s₃.rd = s₀.rd; rw [rd₃, rd₂]; rfl, by show s₃.wr = s₀.wr; rw [wr₃, wr₂]; rfl⟩
    rw [gpr_write_self, BitVec.setWidth_eq, g₄ _ (by decide) (by decide) (by decide)]
    exact hp.keyRead fA hd
  refine WP.seq (WP.mono (Q := fun (s₅ : State) =>
      s₅.gpr .x5 = s₀.mem.readW (K s₀ + BitVec.ofNat 64 (keyOff (Kl s₀) 2)) 64 ∧
        (∀ r, r ≠ .x5 → s₅.gpr r = s₄.gpr r) ∧ s₅.sp = s₀.sp ∧ s₅.mem = s₃.mem ∧ s₅.rd = s₀.rd ∧
        s₅.wr = s₀.wr) ?_ fun s₅ h₅ => ?_)
  · by_cases h16 : Kl s₀ = 16
    · refine WP.ite true (by rw [ev]; simp [h16]) (fun _ => ?_) (fun h => by cases h)
      have := third 0 (by omega) (by decide) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 0 by simp [keyOff, h16]]
    · refine WP.ite false (by rw [ev]; simp [h16]) (fun h => by cases h) (fun _ => ?_)
      have h24 : Kl s₀ = 24 := by rcases hp.valid with h | h <;> omega
      have := third 16 (by omega) (by decide) (by decide)
      rwa [show keyOff (Kl s₀) 2 = 16 by simp [keyOff, h24]]
  · obtain ⟨ax₅, g₅, sp₅, m₅, rd₅, wr₅⟩ := h₅
    have x15₅ : s₅.gpr .x15 = Sc s₀ := by rw [g₅ _ (by decide), x15₄]
    let s₆ := s₅.write .x .x5 (rev64 (s₅.read .x .x5))
    have w : InRegions s₆.wr (s₆.gpr .x15 + BitVec.ofNat 64 64) 8 := by
      rw [gpr_write_of_ne _ _ _ (by decide), x15₅]; show InRegions s₅.wr _ 8
      rw [wr₅]; exact hp.inScr (by decide)
    refine WP.of_runBlock ⟨_, by
      rw [runBlock_cons, exec_rev, runStep_some, runBlock_cons, exec_str_x (by decide) w, runStep_some,
        runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_movz_x (by decide),
        runStep_some, runBlock_nil], ?_⟩
    have mem₇ : s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5) =
        s₃.mem.writeW (Sc s₀ + BitVec.ofNat 64 64) (kw s₀ 2) := by
      rw [gpr_write_of_ne _ _ _ (by decide), x15₅, m₅]
      simp only [s₆, gpr_write_self, State.read, BitVec.setWidth_eq, rev64_eq, ax₅]
    have x15₆ : s₆.gpr .x15 = Sc s₀ := by rw [gpr_write_of_ne _ _ _ (by decide), x15₅]
    have g₆ : ∀ r, r ≠ .x5 → s₆.gpr r = s₅.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => absurd hn (by omega), ?_⟩
    · simp only [gpr_write, reduceCtorEq, ite_false]; exact x15₆
    · simp only [gpr_write, reduceCtorEq, ite_false, ite_true, BitVec.setWidth_eq, State.read]
      rw [x15₆]
    · simp only [gpr_write, reduceCtorEq, ite_false]
      rw [g₆ _ (by decide), g₅ _ (by decide), g₄ _ (by decide) (by decide) (by decide)]; simp
    · simp only [gpr_write, ite_true]; decide
    · exact sp₅
    · exact rd₅
    · exact wr₅
    · show (s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5)).readW _ 64 = _
      rw [mem₇]
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
      · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k0
      · rw [readW_writeW_other _ _ _ (by decide) (by decide) (by decide)]; exact k1
      · rw [Mem.readW_writeW_self64]
    · show Frame _ s₀.mem (s₅.mem.writeW (s₆.gpr .x15 + BitVec.ofNat 64 64) (s₆.gpr .x5))
      rw [mem₇]
      exact (f₃.mono fun r hr => by simp at hr; simp [hr]).writeW (r := ⟨Sc s₀ + BitVec.ofNat 64 48, 24⟩)
        (by simp) _ (cAt 64 (by decide) (by decide))

/-! ## The round keys -/

theorem keysTail_ok (s : State) :
    ∃ s', runBlock isa [.addImm .x .x2 .x2 128, .addImm .x .x4 .x4 8, .subImm .x .x3 .x3 1] s = some s' ∧
      s'.gpr .x2 = s.gpr .x2 + BitVec.ofNat 64 128 ∧ s'.gpr .x4 = s.gpr .x4 + BitVec.ofNat 64 8 ∧
      s'.gpr .x3 = s.gpr .x3 - BitVec.ofNat 64 1 ∧
      (∀ r, r ∉ [Reg.x2, .x3, .x4] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    rw [runBlock_cons, exec_addImm_x (by decide), runStep_some, runBlock_cons, exec_addImm_x (by decide),
      runStep_some, runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_nil], ?_⟩
  refine ⟨by simp [gpr_write, State.read], by simp [gpr_write, State.read], by simp [gpr_write, State.read],
    fun r hr => ?_, rfl, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp [gpr_write, hr.1, hr.2.1, hr.2.2]

theorem keyStep_ok {s₀ : State} (hp : IPre s₀) {i : Nat} (hi : i < 3) {s : State} (h : KInv s₀ i s) :
    WP isa (.block keysBody) s (KInv s₀ (i + 1)) := by
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  have rdwr : s.rd ++ s.wr = [⟨K s₀, Kl s₀⟩, ⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩] := by rw [h.rd, h.wr, hp.rd, hp.wr]; rfl
  rw [keysBody, List.append_assoc, WP.block_append_iff]
  have r4 : InRegions (s.rd ++ s.wr) (s.gpr .x4 + BitVec.ofNat 64 0) 8 := by
    rw [rdwr, add_ofNat_zero, h.x4]
    exact in_rw (r := ⟨Sc s₀, 640⟩) (by simp) (Offset.contains_base _ (by omega) (by omega))
  refine WP.of_runBlock ⟨_, by rw [runBlock_cons, exec_ldr_x (by decide) r4, runStep_some, runBlock_nil], ?_⟩
  let s₁ := s.write .x .x5 (s.mem.readW (s.gpr .x4 + BitVec.ofNat 64 0) 64)
  have g₁ : ∀ r, r ≠ .x5 → s₁.gpr r = s.gpr r := fun r hr => gpr_write_of_ne _ _ _ hr
  have ax₁ : s₁.gpr .x5 = s.mem.readW (s.gpr .x4) 64 := by
    simp only [s₁, gpr_write_self, BitVec.setWidth_eq, add_ofNat_zero]
  rw [WP.block_append_iff]
  have x2₁ : s₁.gpr .x2 = O s₀ + BitVec.ofNat 64 (128 * i) := by rw [g₁ _ (by decide), h.x2]
  have hok : Ok kCfg s₁ := by
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (by simp [kCfg]), by decide, fun k _ j hj => absurd hj (by simp [kCfg])⟩
    show InRegions s.wr _ 8
    rw [h.wr, hp.wr, show kCfg.base = .x2 from rfl, x2₁]
    exact ⟨⟨O s₀, 400⟩, by simp, contains_word (off := 128 * i) (n := 400) rfl
      (by simp only [kCfg] at hk; omega) (by show 400 ≤ 400; decide) (by show 400 < 2 ^ 64; decide)⟩
  obtain ⟨s₂, run₂, rk₂, rd₂, wr₂, sp₂, g₂, f₂⟩ := roundKeys_ok hok
  refine WP.of_runBlock ⟨s₂, run₂, ?_⟩
  obtain ⟨s₃, run₃, x2₃, x4₃, x3₃, g₃, sp₃, m₃, rd₃, wr₃⟩ := keysTail_ok s₂
  refine WP.of_runBlock ⟨s₃, run₃, ?_⟩
  have gk (r : Reg) (h₁ : r ∉ kWrites) (h₂ : r ≠ .x5) : s₂.gpr r = s.gpr r := by rw [g₂ r h₁, g₁ r h₂]
  have slotR : slotRegion kCfg s₁ = ⟨O s₀ + BitVec.ofNat 64 (128 * i), 128⟩ := by
    simp only [slotRegion]; rw [show kCfg.base = .x2 from rfl, x2₁]; rfl
  rw [slotR] at f₂
  have dec : BitVec.ofNat 64 (3 - i) - BitVec.ofNat 64 1 = BitVec.ofNat 64 (3 - (i + 1)) :=
    ofNat_sub_one (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => ?_, fun n hn => ?_, ?_⟩
  · rw [g₃ _ (by decide), gk _ (by decide) (by decide), h.x15]
  · rw [x4₃, gk _ (by decide) (by decide), h.x4, Offset.add_add, show 48 + 8 * i + 8 = 48 + 8 * (i + 1) by omega]
  · rw [x2₃, gk _ (by decide) (by decide), h.x2, Offset.add_add, show 128 * i + 128 = 128 * (i + 1) by omega]
  · rw [x3₃, gk _ (by decide) (by decide), h.x3, dec]
  · rw [sp₃, sp₂, ← h.sp]; rfl
  · rw [rd₃, rd₂, ← h.rd]; rfl
  · rw [wr₃, wr₂, ← h.wr]; rfl
  · rw [m₃, ← h.keys j hj]
    refine f₂.readW (r := ⟨Sc s₀ + BitVec.ofNat 64 (48 + 8 * j), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
      (by decide)
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Offset.sub_base _ (by omega))).symm.sub_left (scrSub (by omega))
  · rw [m₃]
    by_cases hn' : n < 16 * i
    · rw [← h.sched n hn']
      refine f₂.readW (r := ⟨O s₀ + BitVec.ofNat 64 (8 * n), 8⟩) (Region.contains_self _ _) (fun r hr => ?_)
        (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · obtain ⟨j, rfl⟩ : ∃ j, n = 16 * i + j := ⟨n - 16 * i, by omega⟩
      have hj : j < 16 := by omega
      have hk := keyOff_le hp hi
      rw [show O s₀ + BitVec.ofNat 64 (8 * (16 * i + j)) = wordAddr (s₁.gpr .x2) j by
          rw [x2₁, wordAddr, Offset.add_add, show 128 * i + 8 * j = 8 * (16 * i + j) by omega],
        rk₂ j hj, ax₁, h.x4, h.keys i hi, expandKey_getD _ hi hj, Proof.Cmac.bytesAt_length,
        decode_bytesAt _ _ hk]
  · rw [m₃]
    exact h.frame.trans (f₂.sub fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact ⟨⟨O s₀, 384⟩, by simp, Offset.sub_base _ (by omega)⟩)

theorem keys_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    WP isa (.loop (.block keysBody) (.nonzero .x .x3)) s (KInv s₀ 3) := by
  refine WP.loop (M := isa) (body := .block keysBody) (c := .nonzero .x .x3) (Q := KInv s₀ 3)
    (fun (n : Nat) (t : State) => ∃ i, n = 3 - i ∧ i < 3 ∧ KInv s₀ i t) ?_ 3 s ⟨0, rfl, by decide, h⟩
  rintro n t ⟨i, rfl, hi, ht⟩
  refine WP.mono (keyStep_ok hp hi ht) fun t' h' => ?_
  have ev := eval_nonzero (r := .x3) (x := 3 - (i + 1)) (by omega) h'.x3
  by_cases hz : i + 1 = 3
  · left
    refine ⟨by rw [ev]; simp [hz], ?_⟩
    rwa [hz] at h'
  · right
    exact ⟨by rw [ev]; simp; omega, 3 - (i + 1), by omega, i + 1, rfl, by omega, h'⟩

/-! ## The subkeys -/

theorem dbl64_eq' (y : BitVec 64) :
    (y + y) ^^^ (((BitVec.setWidth 64 (0 : BitVec 16) <<< (16 * 0)) - (y >>> 63)) &&&
      (BitVec.setWidth 64 (0x1b : BitVec 16) <<< (16 * 0))) = dbl64 y := by
  rw [← dbl64_eq]; rfl

theorem dbl_ok (s : State) (d : Nat) (hd : d % 8 = 0 ∧ d < 32768)
    (w : InRegions s.wr (s.gpr .x2 + BitVec.ofNat 64 d) 8) :
    ∃ s', runBlock isa (dbl d) s = some s' ∧
      s'.gpr .x5 = dbl64 (s.gpr .x5) ∧
      s'.mem = s.mem.writeW (s.gpr .x2 + BitVec.ofNat 64 d) (byteRev64 (dbl64 (s.gpr .x5))) ∧
      (∀ r, r ∉ [Reg.x5, .x6, .x7, .x11] → s'.gpr r = s.gpr r) ∧
      s'.sp = s.sp ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine ⟨_, by
    simp (config := {decide := true}) only [dbl, runBlock_cons, runStep_some, runBlock_nil, exec, addr,
      State.store, Size.bits, Size.bytes, State.read, gpr_write, mem_write, wr_write, ite_true, ite_false,
      Option.bind_some, BitVec.setWidth_eq, hd, w]
    rfl, ?_⟩
  refine ⟨?_, ?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [gpr_write, ite_true, ite_false, reduceCtorEq, BitVec.setWidth_eq]
    exact dbl64_eq' _
  · simp only [BitVec.setWidth_eq, Mem.writeW, rev64_eq, dbl64_eq']
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [gpr_write, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2]

theorem init_wp {s₀ : State} (h0 : initAArch64.pre s₀) :
    WP isa init s₀ fun s' => initAArch64.post s₀ s' := by
  have hp := IPre.of h0
  have sw := hp.scr_wrap
  have ow := hp.out_wrap
  refine WP.seq (WP.mono (initPre_wp hp) fun s₁ h₁ => ?_)
  refine WP.seq (WP.mono (keys_ok hp h₁) fun s₂ h₂ => ?_)
  refine WP.seq (WP.of_runBlock ⟨_, by
    rw [runBlock_cons, exec_subImm_x (by decide), runStep_some, runBlock_cons, exec_movz_x (by decide),
      runStep_some, runBlock_nil], ?_⟩)
  let s₃ := (s₂.write .x .x14 (s₂.read .x .x2 - BitVec.ofNat _ 384)).write .x .x5
    ((0 : BitVec 16).setWidth 64 <<< (16 * 0))
  have g₃ : ∀ r, r ≠ .x5 → r ≠ .x14 → s₃.gpr r = s₂.gpr r := fun r h₁ h₂ => by
    simp only [s₃, gpr_write, h₁, h₂, ite_false]
  have x14₃ : s₃.gpr .x14 = O s₀ := by
    simp only [s₃, gpr_write, reduceCtorEq, ite_false, ite_true, State.read, BitVec.setWidth_eq]
    rw [h₂.x2, show 128 * 3 = 384 from rfl, BitVec.add_sub_cancel]
  have x15₃ : s₃.gpr .x15 = Sc s₀ := by rw [g₃ _ (by decide) (by decide), h₂.x15]
  have ax₃ : s₃.gpr .x5 = 0 := by simp only [s₃, gpr_write_self]; decide
  have bp : BlockPre s₃ :=
    { sched := ⟨⟨O s₀, 400⟩, by
          show _ ∈ s₂.rd ++ s₂.wr
          rw [h₂.rd, h₂.wr, hp.rd, hp.wr]; simp, by rw [x14₃],
        by show 384 ≤ 400; decide, by show 400 < 2 ^ 64; decide⟩
      scr := ⟨⟨Sc s₀, 640⟩, by show _ ∈ s₂.wr; rw [h₂.wr, hp.wr]; simp, by rw [x15₃], by show 48 ≤ 640; decide,
        by show 640 < 2 ^ 64; decide⟩
      disj := by
        rw [x14₃, x15₃]
        exact (hp.out_scr.symm.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide)) }
  refine WP.seq (WP.mono (block_ok bp) fun s₄ ⟨same₄, x14₄, ax₄⟩ => ?_)
  -- The key schedule.
  have hsch₂ : Spec.TripleDes.scheduleAt s₂.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀) := by
    apply Vector.ext
    intro n hn
    rw [← vgetD _ hn 0, ← vgetD _ hn 0, scheduleAt_getD _ _ hn, h₂.sched n (by omega)]
  have xR₃ : xR s₃ = ⟨Sc s₀, 48⟩ := by rw [xR, x15₃]
  have f₄ : Frame [⟨Sc s₀, 48⟩] s₂.mem s₄.mem := by rw [← xR₃]; exact same₄.frame
  have outX : ∀ r ∈ [(⟨Sc s₀, 48⟩ : Region)], (⟨O s₀, 384⟩ : Region).Disjoint r := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact (hp.out_scr.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
  have hsch₄ : Spec.TripleDes.scheduleAt s₄.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀) := by
    rw [scheduleAt_frame f₄ outX, hsch₂]
  rw [WP.block_append_iff]
  have x2₄ : s₄.gpr .x2 = O s₀ + BitVec.ofNat 64 384 := by
    rw [same₄.keep .x2 (by simp [outer]), g₃ _ (by decide) (by decide), h₂.x2]
  have wr₄ : s₄.wr = [⟨O s₀, 400⟩, ⟨Sc s₀, 640⟩] := by rw [same₄.wr, ← hp.wr, ← h₂.wr]; rfl
  obtain ⟨s₅, run₅, ax₅, m₅, g₅, sp₅, rd₅, wr₅⟩ := dbl_ok s₄ 0 (by decide) (by
    rw [wr₄, x2₄, Offset.add_add]; rw [← hp.wr]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₅, run₅, ?_⟩
  have x2₅ : s₅.gpr .x2 = O s₀ + BitVec.ofNat 64 384 := by rw [g₅ _ (by decide), x2₄]
  obtain ⟨s₆, run₆, ax₆, m₆, g₆, sp₆, rd₆, wr₆⟩ := dbl_ok s₅ 8 (by decide) (by
    rw [wr₅, wr₄, x2₅, Offset.add_add]; rw [← hp.wr]; exact hp.inOut (by decide))
  refine WP.of_runBlock ⟨s₆, run₆, ?_⟩
  -- Memory.
  have c8 : (⟨O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 8)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have c0 : (⟨O s₀ + BitVec.ofNat 64 384, 16⟩ : Region).Contains (O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0)
      (64 / 8) := Offset.contains_base _ (by decide) (by decide)
  have f₆ : Frame [⟨O s₀ + BitVec.ofNat 64 384, 16⟩] s₄.mem s₆.mem := by
    rw [m₆, m₅, x2₅, x2₄]
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ c0).writeW (List.mem_singleton_self _) _ c8
  refine ⟨?_, ?_⟩
  · show Spec.TripleDes.scheduleAt s₆.mem (O s₀) = Spec.TripleDes.expandKey (keyB s₀)
    rw [scheduleAt_frame f₆ (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact Offset.base_disjoint _ (by decide) (by omega)), hsch₄]
  · show Spec.Aes.bytesAt s₆.mem (O s₀ + BitVec.ofNat 64 384) 16 =
      (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).1 ++
        (Spec.Cmac.subkeys (Spec.Cmac.tdesWith (Spec.TripleDes.expandKey (keyB s₀))) 8).2
    have hk : sch s₃ = Spec.TripleDes.expandKey (keyB s₀) := by rw [sch, x14₃]; exact hsch₂
    rw [subkeys_tdes, m₆, x2₅, ax₅, m₅, x2₄, ax₄, ax₃, hk,
      show O s₀ + BitVec.ofNat 64 384 + BitVec.ofNat 64 0 = O s₀ + BitVec.ofNat 64 384 from BitVec.add_zero _]
    exact bytesAt_store2 _ _ _ _

end VG.Proof.CmacTripleDes.AArch64
