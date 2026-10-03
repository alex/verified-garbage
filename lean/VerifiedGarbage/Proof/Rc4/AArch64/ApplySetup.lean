import VerifiedGarbage.Proof.Rc4.AArch64.Consts
import VerifiedGarbage.Proof.Rc4.AArch64.Group

/-!
# The PRGA's setup

`applySetup_ok`: the setup saves the callee-saved vector registers it uses
in general-purpose registers, reads `i` and `j`, and computes the first
group's base `B = (i + 1) mod 256` rounded down to 16 and the lanes to skip
`sk = (i + 1) mod 16`; loads the table from `B`; and leaves the constants,
`j - B`, `-B` and `S[i + 1]` broadcast: the first group's `LaneInv`.
-/

namespace VG.Proof.Rc4.AArch64
open VG VG.AArch64 VG.AArch64.RegUpd VG.Impl.Rc4.AArch64 VG.Spec.Rc4 VG.Proof.Rc4

/-- The first group, from `i`. -/
def i1 (i : BitVec 8) : Nat := (i.toNat + 1) % 256
def sk0 (i : BitVec 8) : Nat := i1 i % 16
def base0 (i : BitVec 8) : Nat := i1 i - sk0 i

theorem incr_byte (I : BitVec 8) :
    (I.setWidth 64 + 1#64) &&& BitVec.setWidth 64 255#16 = BitVec.ofNat 64 (i1 I) := by
  rw [show BitVec.setWidth 64 255#16 = 255#64 from rfl, and255]
  congr 1
  simp only [i1, BitVec.toNat_add, BitVec.toNat_setWidth, show (1#64).toNat = 1 from rfl]
  have := I.isLt
  omega

theorem low4 (n : Nat) (hn : n < 256) :
    BitVec.ofNat 64 n &&& BitVec.setWidth 64 15#16 = BitVec.ofNat 64 (n % 16) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.setWidth 64 15#16).toNat = 2 ^ 4 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem read_byte' (m : Mem) (p : Addr) : m.read p 1 = m p := by
  change (0#0 ++ m p : BitVec 8) = m p
  exact BitVec.zero_width_append _ _

/-- The general-purpose registers the setup writes. -/
def setupRegs : List Reg :=
  [.x3, .x4, .x5, .x6, .x7, .x8, .x9, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x17]

/-- The save and the scalar part of the setup. -/
theorem setupA_ok {s : State} (hp : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258) :
    WP isa (.block (save true ++ ([.ldrb .x12 .x0 256, .ldrb .x13 .x0 257, .movz .x .x9 255 0,
      .add .x .x4 .x12 .x2, .addImm .x .x6 .x12 1, .logic .and .x .x6 .x6 .x9, .movz .x .x7 15 0,
      .logic .and .x .x5 .x6 .x7, .sub .x .x8 .x6 .x5] : List Instr))) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      t.gpr .x13 = c.j.setWidth 64 ∧ t.gpr .x9 = 255#64 ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧
      t.gpr .x5 = BitVec.ofNat 64 (sk0 c.i) ∧ t.gpr .x8 = BitVec.ofNat 64 (base0 c.i) ∧
      t.v = s.v ∧ t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ setupRegs → t.gpr g = s.gpr g) := by
  have h256 := region_offset _ _ _ 256 1 (by decide) (by decide) hp
  have h257 := region_offset _ _ _ 257 1 (by decide) (by decide) hp
  have hc (x : BitVec 8) : (x.setWidth 32).setWidth 64 = x.setWidth 64 :=
    BitVec.setWidth_setWidth (by decide)
  unfold save saved
  have hi1 : i1 (s.mem (s.gpr .x0 + 256#64)) < 256 := by simp only [i1]; omega
  rrun [List.cons_append, List.nil_append, List.map_cons, List.map_nil, h256, h257, read_byte', hc,
    incr_byte, low4 _ hi1]
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]; rfl
  · simp [State.write]
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [negBase]
  · intro g hg
    simp only [setupRegs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hg
    obtain ⟨h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hg
    simp [h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17]

theorem low_sub (j : BitVec 8) (B : Nat) :
    (j.setWidth 64 - BitVec.ofNat 64 B).setWidth 8 = j - bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := j.isLt
  omega

theorem low_neg (B : Nat) : (255#64 - BitVec.ofNat 64 B + 1#64).setWidth 8 = 0 - bB B := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat,
    show (255#64).toNat = 255 from rfl, show (1#64).toNat = 1 from rfl,
    show (0 : BitVec 8).toNat = 0 from rfl]
  omega

theorem low_nat (n : Nat) : (BitVec.ofNat 64 n).setWidth 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega

theorem tbl_bc (x : BitVec 128) {k : Nat} (hk : k < 16) :
    (ofVBytes fun i => if (vbyte (bc (BitVec.ofNat 8 k)) i).toNat < 16 then
      vbyte x (vbyte (bc (BitVec.ofNat 8 k)) i).toNat else 0#8) = bc (vbyte x k) :=
  vbyte_ext fun e he => by
    rw [vbyte_ofVBytes _ he, vbyte_bc _ he, vbyte_bc _ he, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), ite_eq_left hk]

theorem setupD_ok {s : State} {j : BitVec 8} {B sk : Nat} (hsk : sk < 16)
    (h13 : s.gpr .x13 = j.setWidth 64) (h8 : s.gpr .x8 = BitVec.ofNat 64 B)
    (h9 : s.gpr .x9 = 255#64) (h5 : s.gpr .x5 = BitVec.ofNat 64 sk) :
    WP isa (.block [.sub .x .x6 .x13 .x8, .vop (.dup .b16 (dq 0) .x6), .sub .x .x6 .x9 .x8,
      .addImm .x .x6 .x6 1, .vop (.dup .b16 negBase .x6), .vop (.dup .b16 .v7 .x5),
      .vop (.tbl si (treg 0) .v7)]) s fun t =>
      t.v (dq 0) = bc (j - bB B) ∧ t.v negBase = bc (0 - bB B) ∧
      t.v si = bc (vbyte (s.v (treg 0)) sk) ∧
      (∀ v, v ≠ dq 0 → v ≠ negBase → v ≠ .v7 → v ≠ si → t.v v = s.v v) ∧
      (∀ g, g ≠ .x6 → t.gpr g = s.gpr g) ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have d0 : dq 0 = .v0 := rfl
  have nb : negBase = .v14 := rfl
  have t0 : treg 0 = .v16 := rfl
  have s4 : si = .v4 := rfl
  rrun [d0, nb, t0, s4, h13, h8, h9, h5, bc_lit, low_sub, low_neg, low_nat, tbl_bc _ hsk]
  refine ⟨fun v a b c d => ?_, fun g hg => ?_, ?_⟩
  · simp [a, b, c, d]
  · simp [hg]
  · simp [State.setV, State.write]

theorem i1_eq (i : BitVec 8) : BitVec.ofNat 8 (base0 i + sk0 i) = i + 1 := by
  apply BitVec.eq_of_toNat_eq
  simp only [base0, sk0, i1, BitVec.toNat_ofNat, BitVec.toNat_add, show (1 : BitVec 8).toNat = 1 from rfl]
  omega

theorem base0_mod (i : BitVec 8) : base0 i % 16 = 0 := by simp only [base0, sk0]; omega

theorem sk0_lt (i : BitVec 8) : sk0 i < 16 := by simp only [sk0]; omega

/-- The loop's globals for the call from `s`, entering the loop in `t`. -/
def glob (s t : State) : Glob :=
  ⟨contextAt s.mem (s.gpr .x0), s.gpr .x1, (s.gpr .x2).toNat, s.mem, t⟩

theorem saved_ne : ∀ p ∈ saved true, p.2 ≠ .x6 ∧ p.2 ≠ .x7 := by decide

theorem applySetup_ok {s : State} (hp : InRegions s.wr (s.gpr .x0) 258) :
    WP isa (.block (applyLoad ++ applySetup)) s fun t =>
      let c := contextAt s.mem (s.gpr .x0)
      LaneInv (glob s t) (base0 c.i) 0 (sk0 c.i) 0 t ∧
      t.gpr .x4 = c.i.setWidth 64 + s.gpr .x2 ∧ t.gpr .x9 = 255#64 ∧
      (∀ p ∈ saved true, t.gpr p.2 = (s.v p.1).extractLsb' 0 64) ∧
      (∀ g, g ∉ setupRegs → t.gpr g = s.gpr g) ∧ t.v .v15 = s.v .v15 ∧
      t.mem = s.mem ∧ t.rd = s.rd ∧ t.wr = s.wr ∧ t.sp = s.sp := by
  have hpr : InRegions (s.rd ++ s.wr) (s.gpr .x0) 258 :=
    let ⟨r, h1, h2⟩ := hp; ⟨r, List.mem_append_right _ h1, h2⟩
  have h256 : InRegions (s.rd ++ s.wr) (s.gpr .x0) 256 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      region_offset _ _ _ 0 256 (by decide) (by decide) hpr
  unfold applyLoad applySetup
  rw [WP.block_append_iff]
  refine WP.mono (setupA_ok hpr) fun a ⟨a13, a9, a4, a5, a8, av, am, ard, awr, asp, asv, ag⟩ => ?_
  rw [List.append_assoc, WP.block_append_iff, loadTable_eq]
  have hpa : InRegions (a.rd ++ a.wr) (a.gpr .x0) 256 := by
    rw [ard, awr, ag .x0 (by decide)]; exact h256
  refine WP.mono (loadN_ok (base0_mod _) a8 a9 hpa (Nat.le_refl 16))
    fun b ⟨brow, bv, bg, bm, brd, bwr, bsp⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (constants_ok b) fun e ⟨ec, ev, eg, em, erd, ewr, esp⟩ => ?_
  have e13 : e.gpr .x13 = (contextAt s.mem (s.gpr .x0)).j.setWidth 64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a13]
  have e8 : e.gpr .x8 = BitVec.ofNat 64 (base0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a8]
  have e9 : e.gpr .x9 = 255#64 := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a9]
  have e5 : e.gpr .x5 = BitVec.ofNat 64 (sk0 (contextAt s.mem (s.gpr .x0)).i) := by
    rw [eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5]
  refine WP.mono (setupD_ok (sk0_lt _) e13 e8 e9 e5)
    fun t ⟨tj, tnb, tsi, tv, tg, tm, trd, twr, tsp⟩ => ?_
  have gk : ∀ g, g ∉ setupRegs → t.gpr g = s.gpr g := fun g hg => by
    have h6 : g ≠ .x6 := fun h => hg (h ▸ by decide)
    have h7 : g ≠ .x7 := fun h => hg (h ▸ by decide)
    rw [tg g h6, eg g h6 h7, bg g h6 h7, ag g hg]
  have hsk := sk0_lt (contextAt s.mem (s.gpr .x0)).i
  have hd : doneAt (glob s t) 0 (sk0 (contextAt s.mem (s.gpr .x0)).i) 0 = 0 := by
    simp only [doneAt]; omega
  refine ⟨LaneInv.mk ?_ ?_ ?_ ?_ ?_ ⟨fun _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩ fun _ _ _ => rfl, ?_, ?_,
    fun p hp => ?_, gk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd]
    refine ⟨rows_table (m := s.mem) (p := s.gpr .x0) (base0_mod _) fun r hr => ?_, tj, tnb,
      ec.congr fun r hr => tv r ?_ ?_ ?_ ?_⟩
    · have ht := treg_ne r hr
      rw [tv _ ht.1 (by revert r; decide) (by revert r; decide) (by revert r; decide),
        ev _ (by revert r; decide) (by revert r; decide) (by revert r; decide) (by revert r; decide)
          (by revert r; decide) (by revert r; decide) (by revert r; decide),
        brow r hr, am, ag .x0 (by decide)]
    all_goals rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [hd]
    refine ⟨Nat.zero_le _, ?_, ?_, fun k _ => ?_, ?_⟩
    · rw [gk .x1 (by decide)]; simp [glob]
    · rw [gk .x2 (by decide)]; simp [glob]
    · simp only [Nat.not_lt_zero, ite_false, glob]; rw [tm, em, bm, am]
    · rw [tm, em, bm, am]; exact Frame.refl _ _
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a5,
      Nat.sub_zero]
  · rw [tg _ (by decide), e8]
  · intro _
    refine ⟨?_, ?_⟩
    · rw [hd, Nat.zero_max]; exact (i1_eq _).symm
    · rw [Nat.zero_max, tsi, tbyte, Nat.div_eq_of_lt hsk,
        Nat.mod_eq_of_lt hsk, tv (treg 0) (by decide) (by decide) (by decide) (by decide)]
  · rw [tg _ (by decide), eg _ (by decide) (by decide), bg _ (by decide) (by decide), a4]
  · rw [tg _ (by decide), e9]
  · obtain ⟨h6, h7⟩ := saved_ne p hp
    rw [tg _ h6, eg _ h6 h7, bg _ h6 h7, asv p hp]
  · rw [tv _ (by decide) (by decide) (by decide) (by decide),
      ev _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      bv _ (by decide), av]
  · rw [tm, em, bm, am]
  · rw [trd, erd, brd, ard]
  · rw [twr, ewr, bwr, awr]
  · rw [tsp, esp, bsp, asp]

end VG.Proof.Rc4.AArch64
