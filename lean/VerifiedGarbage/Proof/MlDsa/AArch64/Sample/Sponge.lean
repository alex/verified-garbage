import VerifiedGarbage.Impl.MlDsa.AArch64.Sample.Common
import VerifiedGarbage.Proof.MlKem.AArch64.KeccakCall
import VerifiedGarbage.Proof.MlKem.AArch64.Common
import VerifiedGarbage.Proof.MlKem.KPke
import VerifiedGarbage.Proof.MlDsa.Sample.Hash
import VerifiedGarbage.Proof.MlDsa.Sample.Mem

/-!
# ML-DSA on AArch64: the sampling functions' SHAKE

Untrusted: everything here is checked by Lean. What the sampling functions
share (`Impl/MlDsa/AArch64/Sample/Common.lean`), for any of them: a call is
described by `Sp` (the message, its length, the working space, the output
polynomial and the parameter kept in `x27`), whose regions are laid out as
`SpOk` says. From the prologue on, `Env` holds: the registers of the layout,
the caller's callee-saved registers (in their registers or saved in the
working space), and the memory changed only in the output, the working space
and the stack below `sp`. `sponge` then leaves `outlen` bytes of SHAKE of
the message at `scratch + 840` (`sponge_ok`); `epi_ok` restores the
registers.
-/

namespace VG.Proof.MlDsa.AArch64.Sample

open VG VG.AArch64
open VG.Proof.MlKem.AArch64 (Only Keep MemTo Kept wp_nil wp_mov wp_movz wp_addImm wp_subImm wp_strx
  wp_ldrx wp_strw wp_x only_write write_x_gpr ptr_add ptr_zero sep_off contains_off in_regions
  in_rd_wr in_rd toNat_imm toNat_sub_n absorb_call pad_call squeeze_call stk count_loop)
open VG.Impl.MlDsa.AArch64.Sample
open VG.Impl.MlKem.AArch64 (mov)
open VG.Proof.MlDsa.Sample (padded coeffAddr polyR coeff_contains)
open VG.Spec.Sha3 (bytesAt stateAt Repr rates shakeSuffix)

/-- A call of a sampling function. -/
structure Sp where
  /-- The message hashed. -/
  sd : Addr
  len : Nat
  /-- `scratch`. -/
  scr : Addr
  /-- The output polynomial. -/
  a : Addr
  /-- The parameter, in `x27`. -/
  prm : BitVec 64

namespace Sp
variable (P : Sp)
/-- `scratch + off`. -/
abbrev at' (off : Nat) : Addr := P.scr + BitVec.ofNat 64 off
abbrev scrR : Region := ⟨P.scr, 2048⟩
abbrev sdR : Region := ⟨P.sd, P.len⟩
/-- The message. -/
abbrev msg (σ : State) : List Byte := bytesAt σ.mem P.sd P.len
end Sp

/-- The regions of a call from the entry state `σ`. -/
structure SpOk (P : Sp) (σ : State) : Prop where
  rd : σ.rd = [P.sdR]
  wr : σ.wr = [polyR P.a, P.scrR]
  sd_a : P.sdR.Disjoint (polyR P.a)
  sd_scr : P.sdR.Disjoint P.scrR
  a_scr : (polyR P.a).Disjoint P.scrR
  sp16 : 16 ≤ σ.sp.toNat
  stk_sd : (below σ.sp 16).Disjoint P.sdR
  stk_a : (below σ.sp 16).Disjoint (polyR P.a)
  stk_scr : (below σ.sp 16).Disjoint P.scrR
  len_lt : P.len < 2 ^ 64

/-- What holds from the prologue on, relative to the entry state `σ`. -/
structure Env (P : Sp) (σ s : State) : Prop where
  rd : s.rd = σ.rd
  wr : s.wr = σ.wr
  sp : s.sp = σ.sp
  x25 : s.gpr .x25 = P.scr
  x26 : s.gpr .x26 = P.a
  x27 : s.gpr .x27 = P.prm
  cs : ∀ r ∈ preserved, r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x30 → s.gpr r = σ.gpr r
  saved : s.mem.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ s.mem.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
    s.mem.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ s.mem.readW (P.at' 2040) 64 = σ.gpr .x30
  frame : Frame [polyR P.a, P.scrR, below σ.sp 16] σ.mem s.mem

theorem mem2 {α : Type} {a b x : α} (h : x ∈ [a, b]) : x = a ∨ x = b := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (List.mem_singleton.mp h)

theorem mem3 {α : Type} {a b c x : α} (h : x ∈ [a, b, c]) : x = a ∨ x = b ∨ x = c := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem2 h)

theorem mem4 {α : Type} {a b c d x : α} (h : x ∈ [a, b, c, d]) : x = a ∨ x = b ∨ x = c ∨ x = d := by
  rcases List.mem_cons.mp h with h | h
  · exact .inl h
  · exact .inr (mem3 h)

/-! ## Regions -/

section
variable {P : Sp}

theorem sub_scr {a n : Nat} (h : a + n ≤ 2048) : Region.Sub ⟨P.at' a, n⟩ P.scrR := Offset.sub_base _ h

theorem sub_scr0 {n : Nat} (h : n ≤ 2048) : Region.Sub ⟨P.scr, n⟩ P.scrR := Region.sub_prefix h

theorem disj_scr {a n b m : Nat} (h : a + n ≤ b ∨ b + m ≤ a) (ha : a + n ≤ 2048) (hb : b + m ≤ 2048) :
    Region.Disjoint ⟨P.at' a, n⟩ ⟨P.at' b, m⟩ := Offset.disjoint _ h (by omega) (by omega)

theorem contains_scr {a n : Nat} (h : a + n ≤ 2048) : P.scrR.Contains (P.at' a) n :=
  Offset.contains_base _ h (by omega)

theorem at_zero : P.at' 0 = P.scr := ptr_zero _

theorem at_add (a b : Nat) : P.at' a + BitVec.ofNat 64 b = P.at' (a + b) := ptr_add _ _ _

variable {σ : State} (hp : SpOk P σ)
include hp

theorem sd_scr' {a n : Nat} (h : a + n ≤ 2048) : P.sdR.Disjoint ⟨P.at' a, n⟩ :=
  hp.sd_scr.sub_right (sub_scr h)

theorem stk_scr' {a n : Nat} (h : a + n ≤ 2048) : (below σ.sp 16).Disjoint ⟨P.at' a, n⟩ :=
  hp.stk_scr.sub_right (sub_scr h)

theorem a_scr' {a n : Nat} (h : a + n ≤ 2048) : (polyR P.a).Disjoint ⟨P.at' a, n⟩ :=
  hp.a_scr.sub_right (sub_scr h)

/-- The regions, from the prologue on. -/
theorem regions {s : State} (he : Env P σ s) : s.rd ++ s.wr = [P.sdR, polyR P.a, P.scrR] := by
  rw [he.rd, he.wr, hp.rd, hp.wr]; rfl

theorem inScr {s : State} (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions s.wr (P.at' a) n := by
  rw [hw, hp.wr]
  exact in_regions (List.mem_cons_of_mem _ (List.mem_singleton_self _)) (contains_scr h)

theorem inScrRd {s : State} (hr : s.rd = σ.rd) (hw : s.wr = σ.wr) {a n : Nat} (h : a + n ≤ 2048) :
    InRegions (s.rd ++ s.wr) (P.at' a) n := by
  rw [hr]; exact in_rd_wr (inScr hp hw h)

theorem inA {s : State} (hw : s.wr = σ.wr) {i : Nat} (hi : i < 256) :
    InRegions s.wr (coeffAddr P.a i) 4 := by
  rw [hw, hp.wr]
  exact in_regions (List.mem_cons_self ..) (coeff_contains _ hi)

theorem cov_scr {s : State} (hw : s.wr = σ.wr) {rs : List Region}
    (h : ∀ r ∈ rs, ∃ off, r.base = P.at' off ∧ off + r.len ≤ 2048) : Covers rs s.wr :=
  Covers.of_sub fun r hr => by
    obtain ⟨off, hb, hl⟩ := h r hr
    exact ⟨P.scrR, by rw [hw, hp.wr]; simp, off, hb, hl⟩

omit hp in
theorem cov_rd {s : State} {rs : List Region} (h : Covers rs s.wr) : Covers rs (s.rd ++ s.wr) :=
  fun a n hi => in_rd_wr (h a n hi)

/-- The message is not written. -/
theorem sd_frame {m : Mem} (hf : Frame [polyR P.a, P.scrR, below σ.sp 16] σ.mem m) :
    bytesAt m P.sd P.len = P.msg σ :=
  MlKem.bytesAt_frame hf (fun r hr => by
    rcases mem3 hr with rfl | rfl | rfl
    exacts [hp.sd_a, hp.sd_scr, hp.stk_sd.symm]) (Nat.le_of_lt hp.len_lt)

omit hp in
/-- The saved registers are apart from the parts of `scratch` below them. -/
theorem sv_disj {off n : Nat} (h : off + n ≤ 2016) :
    Region.Disjoint ⟨P.at' 2016, 32⟩ ⟨P.at' off, n⟩ := disj_scr (.inr h) (by omega) (by omega)

omit hp in
theorem sv_frame {m m' : Mem} (h : m.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ m.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
      m.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ m.readW (P.at' 2040) 64 = σ.gpr .x30)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, Region.Disjoint ⟨P.at' 2016, 32⟩ r) :
    m'.readW (P.at' 2016) 64 = σ.gpr .x25 ∧ m'.readW (P.at' 2024) 64 = σ.gpr .x26 ∧
      m'.readW (P.at' 2032) 64 = σ.gpr .x27 ∧ m'.readW (P.at' 2040) 64 = σ.gpr .x30 := by
  have e : ∀ k, k < 4 → m'.readW (P.at' (2016 + 8 * k)) 64 = m.readW (P.at' (2016 + 8 * k)) 64 :=
    fun k hk => by
      refine hf.readW (r := ⟨P.at' 2016, 32⟩) ?_ hd (by decide)
      rw [← at_add]
      exact contains_off (by omega) (by decide)
  exact ⟨(e 0 (by decide)).trans h.1, (e 1 (by decide)).trans h.2.1, (e 2 (by decide)).trans h.2.2.1,
    (e 3 (by decide)).trans h.2.2.2⟩

/-- A call that writes parts of `scratch` below the saved registers, and the
stack below `sp`, keeps `Env`. -/
theorem Env.call {s s' : State} (he : Env P σ s) {rs : List Region} (hk : Kept rs s s')
    (hrs : ∀ r ∈ rs, (∃ off n, r = ⟨P.at' off, n⟩ ∧ off + n ≤ 2016) ∨ r = below s.sp 16) :
    Env P σ s' := by
  have hd : ∀ r ∈ rs, Region.Disjoint ⟨P.at' 2016, 32⟩ r := fun r hr => by
    rcases hrs r hr with ⟨off, n, rfl, h⟩ | rfl
    · exact sv_disj h
    · rw [he.sp]; exact (stk_scr' hp (a := 2016) (n := 32) (by omega)).symm
  refine ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.cs _ (by decide) (by decide), he.x25], by rw [hk.cs _ (by decide) (by decide), he.x26],
    by rw [hk.cs _ (by decide) (by decide), he.x27],
    fun r hr h25 h26 h27 h30 => by rw [hk.cs r hr h30, he.cs r hr h25 h26 h27 h30],
    sv_frame he.saved hk.frame hd, he.frame.trans (hk.frame.sub fun r hr => ?_)⟩
  rcases hrs r hr with ⟨off, n, rfl, h⟩ | rfl
  · exact ⟨P.scrR, by simp, sub_scr (by omega)⟩
  · exact ⟨below σ.sp 16, by simp, by rw [he.sp]; exact fun _ h => h⟩

/-- Code that writes only registers that are not callee-saved, and the
output polynomial, keeps `Env`. -/
theorem Env.keepA {s s' : State} (he : Env P σ s) {regs : List Reg} (hk : Keep regs s s')
    (hf : Frame [polyR P.a] s.mem s'.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) :
    Env P σ s' :=
  ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), he.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), he.x26],
    by rw [hk.get .x27 (fun h' => hr _ h' (by decide)), he.x27],
    fun r hp' h25 h26 h27 h30 => by rw [hk.get r (fun h' => hr _ h' hp'), he.cs r hp' h25 h26 h27 h30],
    sv_frame he.saved hf (fun r hr => by
      rw [List.mem_singleton.mp hr]; exact (a_scr' hp (a := 2016) (n := 32) (by omega)).symm),
    he.frame.trans (hf.mono (by simp))⟩

end

/-- Code that writes only registers that are not callee-saved keeps `Env`. -/
theorem Env.keep {P : Sp} {σ s s' : State} (he : Env P σ s) {regs : List Reg} (hk : Keep regs s s')
    (hm : s'.mem = s.mem) (hr : ∀ r ∈ regs, r ∉ preserved := by decide) : Env P σ s' :=
  ⟨by rw [hk.rd, he.rd], by rw [hk.wr, he.wr], by rw [hk.sp, he.sp],
    by rw [hk.get .x25 (fun h' => hr _ h' (by decide)), he.x25],
    by rw [hk.get .x26 (fun h' => hr _ h' (by decide)), he.x26],
    by rw [hk.get .x27 (fun h' => hr _ h' (by decide)), he.x27],
    fun r hp' h25 h26 h27 h30 => by rw [hk.get r (fun h' => hr _ h' hp'), he.cs r hp' h25 h26 h27 h30],
    by rw [hm]; exact he.saved, by rw [hm]; exact he.frame⟩

/-! ## The prologue -/

/-- The entry of `sponge`: the message in `x3` and its length in `x4`. -/
structure J0 (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  x3 : s.gpr .x3 = P.sd
  x4 : (s.gpr .x4).toNat = P.len

/-- The prologue, for any instructions that set the parameter and the
length. -/
theorem pro_ok {P : Sp} {σ : State} (hp : SpOk P σ) {scr a : Reg} {prm len : Instr}
    (hscr : σ.gpr scr = P.scr) (ha : σ.gpr a = P.a) (ha25 : a ≠ .x25) (hsd : σ.gpr .x0 = P.sd)
    (hprm : ∀ s : State, (∀ r, r ≠ .x25 → r ≠ .x26 → s.gpr r = σ.gpr r) →
      ∃ s', exec prm s = some s' ∧ Only [.x27] s s' ∧ s'.gpr .x27 = P.prm)
    (hlen : ∀ s : State, (∀ r, r ≠ .x25 → r ≠ .x26 → r ≠ .x27 → r ≠ .x3 → s.gpr r = σ.gpr r) →
      ∃ s', exec len s = some s' ∧ Only [.x4] s s' ∧ (s'.gpr .x4).toNat = P.len) :
    WP isa (.block (pro scr a prm len)) σ (J0 P σ) := by
  unfold pro
  refine wp_strx (a := P.at' 2016) (by decide) (by rw [hscr]) (inScr hp rfl (by omega)) fun s₁ h₁ => ?_
  refine wp_strx (a := P.at' 2024) (by decide) (by rw [h₁.gpr, hscr])
    (by rw [h₁.wr]; exact inScr hp rfl (by omega)) fun s₂ h₂ => ?_
  refine wp_strx (a := P.at' 2032) (by decide) (by rw [h₂.gpr, h₁.gpr, hscr])
    (by rw [h₂.wr, h₁.wr]; exact inScr hp rfl (by omega)) fun s₃ h₃ => ?_
  refine wp_strx (a := P.at' 2040) (by decide) (by rw [h₃.gpr, h₂.gpr, h₁.gpr, hscr])
    (by rw [h₃.wr, h₂.wr, h₁.wr]; exact inScr hp rfl (by omega)) fun s₄ h₄ => ?_
  have g₄ : ∀ r, s₄.gpr r = σ.gpr r := fun r => by rw [h₄.gpr, h₃.gpr, h₂.gpr, h₁.gpr]
  refine wp_mov fun s₅ h₅ e₅ => wp_mov fun s₆ h₆ e₆ => ?_
  obtain ⟨s₇, x₇, h₇, e₇⟩ := hprm s₆ fun r h25 h26 => by
    rw [h₆.get r (by simpa using h26), h₅.get r (by simpa using h25), g₄]
  refine Proof.MlKem.AArch64.WP.cons x₇ (wp_mov fun s₈ h₈ e₈ => ?_)
  obtain ⟨s₉, x₉, h₉, e₉⟩ := hlen s₈ fun r h25 h26 h27 h3 => by
    rw [h₈.get r (by simpa using h3), h₇.get r (by simpa using h27), h₆.get r (by simpa using h26),
      h₅.get r (by simpa using h25), g₄]
  refine Proof.MlKem.AArch64.WP.cons x₉ (wp_nil ?_)
  have k₉ := (((h₅.keep.trans h₆.keep).trans h₇.keep).trans h₈.keep).trans h₉.keep
  have m₉ : s₉.mem = (((σ.mem.writeW (P.at' 2016) (σ.gpr .x25)).writeW (P.at' 2024)
      (σ.gpr .x26)).writeW (P.at' 2032) (σ.gpr .x27)).writeW (P.at' 2040) (σ.gpr .x30) := by
    rw [h₉.mem, h₈.mem, h₇.mem, h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem, h₃.gpr, h₂.gpr, h₁.gpr]
  have sep : ∀ a b, 2016 ≤ a → a + 8 ≤ b → b + 8 ≤ 2048 →
      Mem.Sep (P.at' a) (64 / 8) (P.at' b) (64 / 8) := fun a b h1 h2 h3 =>
    Offset.sep _ (.inl h2) (by omega) (by omega)
  refine ⟨⟨by rw [k₉.rd, h₄.rd, h₃.rd, h₂.rd, h₁.rd], by rw [k₉.wr, h₄.wr, h₃.wr, h₂.wr, h₁.wr],
    by rw [k₉.sp, h₄.sp, h₃.sp, h₂.sp, h₁.sp], ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [h₉.get .x25, h₈.get .x25, h₇.get .x25, h₆.get .x25, e₅, g₄, hscr]
  · rw [h₉.get .x26, h₈.get .x26, h₇.get .x26, e₆, h₅.get a (by simpa using ha25), g₄, ha]
  · rw [h₉.get .x27, h₈.get .x27, e₇]
  · intro r hr h25 h26 h27 _
    have h3 : r ≠ .x3 := fun e => by subst e; revert hr; decide
    have h4 : r ≠ .x4 := fun e => by subst e; revert hr; decide
    rw [h₉.get r (by simpa using h4), h₈.get r (by simpa using h3), h₇.get r (by simpa using h27),
      h₆.get r (by simpa using h26), h₅.get r (by simpa using h25), g₄]
  · rw [m₉]
    refine ⟨?_, ?_, ?_, Mem.readW_writeW_self64 _ _ _⟩
    · rw [Mem.readW_writeW_sep (sep 2016 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2016 2032 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2016 2024 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep 2024 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_sep (sep 2024 2032 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (sep 2032 2040 (by omega) (by omega) (by omega)) (by decide),
        Mem.readW_writeW_self64]
  · rw [m₉]
    have hm : P.scrR ∈ [polyR P.a, P.scrR, below σ.sp 16] := by simp
    exact ((((Frame.refl _ _).writeW hm _ (contains_scr (by omega))).writeW hm _
      (contains_scr (by omega))).writeW hm _ (contains_scr (by omega))).writeW hm _ (contains_scr (by omega))
  · rw [h₉.get .x3, e₈, h₇.get .x0, h₆.get .x0, h₅.get .x0, g₄, hsd]
  · exact e₉

/-! ## The sponge -/

/-- The zeros of the Keccak state at `x25`. -/
def zst (n : Nat) : List Instr := (List.range n).map fun k => .str .x .x9 .x25 (8 * k)

theorem zst_ok {P : Sp} {σ : State} (hp : SpOk P σ) :
    ∀ n ≤ 25, ∀ {s : State}, s.gpr .x9 = 0 → s.gpr .x25 = P.scr → s.wr = σ.wr →
      WP isa (.block (zst n)) s fun s' => s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
        s'.sp = s.sp ∧ (∀ k < n, s'.mem.readW (P.at' (8 * k)) 64 = 0) ∧
        Frame [⟨P.scr, 200⟩] s.mem s'.mem
  | 0, _, s, _, _, _ => wp_nil ⟨rfl, rfl, rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _),
      Frame.refl _ _⟩
  | n + 1, hn, s, h9, h25, hw => by
    rw [zst, List.range_succ, List.map_append, WP.block_append_iff]
    refine WP.mono (zst_ok hp n (by omega) h9 h25 hw) fun s₁ ⟨g₁, r₁, w₁, p₁, z₁, f₁⟩ => ?_
    refine wp_strx (a := P.at' (8 * n)) (by constructor <;> omega) (by rw [g₁, h25])
      (by rw [w₁]; exact inScr hp hw (by omega)) fun s₂ h₂ => wp_nil ?_
    refine ⟨by rw [h₂.gpr, g₁], by rw [h₂.rd, r₁], by rw [h₂.wr, w₁], by rw [h₂.sp, p₁],
      fun k hk => ?_, ?_⟩
    · rw [h₂.mem, g₁, h9]
      by_cases e : k = n
      · subst e; exact Mem.readW_writeW_self64 _ _ _
      · rw [Mem.readW_writeW_sep (sep_off _ (by omega) (by omega) (by omega)) (by decide)]
        exact z₁ k (by omega)
    · rw [h₂.mem]
      refine f₁.writeW (List.mem_singleton_self _) _ ?_
      rw [← at_zero (P := P)]
      exact Offset.contains _ (by omega) (by omega) (by omega)

theorem stateAt_zero {m : Mem} {p : Addr}
    (h : ∀ k < 25, m.readW (p + BitVec.ofNat 64 (8 * k)) 64 = 0) : stateAt m p = Spec.Sha3.zero := by
  refine Vector.ext fun i hi => ?_
  simp only [stateAt, Spec.Sha3.zero, Vector.getElem_ofFn, Vector.getElem_replicate]
  exact h i hi

theorem toNat_movz {n : Nat} (h : n < 2 ^ 16) : ((BitVec.ofNat 16 n).setWidth 64).toNat = n := by
  rw [toNat_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem rate_pos {rate : Nat} (h : rate ∈ rates) : 0 < rate := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

theorem rate_lt {rate : Nat} (h : rate ∈ rates) : rate < 2 ^ 16 := by
  simp only [rates, List.mem_cons, List.not_mem_nil, or_false] at h; omega

/-- After zeroing the state: the arguments of `absorb`. -/
structure J1 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  zero : stateAt s.mem P.scr = Spec.Sha3.zero
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = P.sd
  x4 : (s.gpr .x4).toNat = P.len
  x5 : s.gpr .x5 = P.at' 200

section
variable {P : Sp} {σ : State} (hp : SpOk P σ)
include hp

theorem blk1_ok {rate : Nat} (hr : rate < 2 ^ 16) {s : State} (h : J0 P σ s) :
    WP isa (.block (zeroSt ++ absArgs rate)) s (J1 rate P σ) := by
  unfold zeroSt
  refine wp_movz fun s₁ h₁ e₁ => ?_
  rw [List.append_eq, WP.block_append_iff]
  have e1 := h.env.keep h₁.keep h₁.mem
  refine WP.mono (zst_ok hp 25 (by decide) (by rw [e₁]; rfl) e1.x25 e1.wr)
    fun s₂ ⟨g₂, r₂, w₂, p₂, z₂, f₂⟩ => ?_
  have e2 : Env P σ s₂ := ⟨by rw [r₂, e1.rd], by rw [w₂, e1.wr], by rw [p₂, e1.sp], by rw [g₂, e1.x25],
    by rw [g₂, e1.x26], by rw [g₂, e1.x27], fun r hr a b c d => by rw [g₂, e1.cs r hr a b c d],
    sv_frame e1.saved f₂ (fun r hr => by
      rw [List.mem_singleton.mp hr, ← at_zero (P := P)]; exact sv_disj (by omega)),
    e1.frame.trans (f₂.sub fun r hr => by
      rw [List.mem_singleton.mp hr]; exact ⟨P.scrR, by simp, sub_scr0 (by omega)⟩)⟩
  refine wp_mov fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ =>
    wp_addImm (by decide) fun s₆ h₆ e₆ => wp_nil ?_
  have k₆ := ((h₃.keep.trans h₄.keep).trans h₅.keep).trans h₆.keep
  have e6 := e2.keep k₆ (by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem])
  refine ⟨e6, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem]
    exact stateAt_zero fun k hk => z₂ k hk
  · rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, e₃, e2.x25]
  · rw [h₆.get .x1, h₅.get .x1, e₄]; exact toNat_movz hr
  · rw [h₆.get .x2, e₅]; rfl
  · rw [h₆.get .x3, h₅.get .x3, h₄.get .x3, h₃.get .x3, g₂, h₁.get .x3, h.x3]
  · rw [h₆.get .x4, h₅.get .x4, h₄.get .x4, h₃.get .x4, g₂, h₁.get .x4, h.x4]
  · rw [e₆, h₅.get .x25, h₄.get .x25, h₃.get .x25, e2.x25]

/-- After absorbing the message. -/
structure J2 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  repr : Repr s.mem P.scr rate (P.msg σ)
  x0 : (s.gpr .x0).toNat = P.len % rate

theorem call1_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : J1 rate P σ s) :
    WP isa (.call "vg_keccak_absorb" Impl.Sha3.AArch64.Stream.absorb) s (J2 rate P σ) := by
  have hsp := h.env.sp
  refine absorb_call (st := P.scr) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (rate_pos hr)
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (hp.sd_scr.sub_right (sub_scr0 (by omega))) (sd_scr' hp (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact hp.stk_sd) (by rw [stk, hsp]; exact stk_scr' hp (by omega)) ?_
    (cov_scr hp h.env.wr ?_) fun s' hk hrep hx => ⟨Env.call hp h.env hk ?_, ?_, ?_⟩
  · rw [regions hp h.env]
    refine Covers.of_sub fun r hr => ?_
    rcases mem3 hr with rfl | rfl | rfl
    · exact ⟨P.sdR, by simp, 0, (ptr_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, 0, (ptr_zero _).symm, by simp⟩
    · exact ⟨P.scrR, by simp, 200, rfl, by simp⟩
  · intro r hr
    rcases mem2 hr with rfl | rfl
    · exact ⟨0, (at_zero).symm, by simp⟩
    · exact ⟨200, rfl, by simp⟩
  · intro r hr
    rcases mem3 hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [at_zero], by omega⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · have := hrep [] (MlKem.repr_nil h.zero) (by simp)
    rwa [List.nil_append, sd_frame hp h.env.frame] at this
  · rw [hx, Nat.zero_add]

/-- The arguments of `pad`. -/
structure J3 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  repr : Repr s.mem P.scr rate (P.msg σ)
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = P.len % rate
  x3 : (s.gpr .x3).setWidth 8 = shakeSuffix
  x4 : s.gpr .x4 = P.at' 200

omit hp in
theorem blk2_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : J2 rate P σ s) :
    WP isa (.block (padArgs rate)) s (J3 rate P σ) := by
  refine wp_mov fun s₁ h₁ e₁ => wp_mov fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ => wp_movz fun s₄ h₄ e₄ =>
    wp_addImm (by decide) fun s₅ h₅ e₅ => wp_nil ?_
  have k₅ := (((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep
  have m₅ : s₅.mem = s.mem := by rw [h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  refine ⟨h.env.keep k₅ m₅, by rw [m₅]; exact h.repr, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₅.get .x0, h₄.get .x0, h₃.get .x0, e₂, h₁.get .x25, h.env.x25]
  · rw [h₅.get .x1, h₄.get .x1, e₃]; exact toNat_movz (rate_lt hr)
  · rw [h₅.get .x2, h₄.get .x2, h₃.get .x2, h₂.get .x2, e₁, h.x0]
  · rw [h₅.get .x3, e₄]; decide
  · rw [e₅, h₄.get .x25, h₃.get .x25, h₂.get .x25, h₁.get .x25, h.env.x25]

/-- After padding. -/
structure J4 (rate : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  st : stateAt s.mem P.scr = padded rate shakeSuffix (P.msg σ)

theorem call2_ok {rate : Nat} (hr : rate ∈ rates) {s : State} (h : J3 rate P σ s) :
    WP isa (.call "vg_keccak_pad" Impl.Sha3.AArch64.Stream.pad) s (J4 rate P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 200, 640⟩] s.wr := cov_scr hp h.env.wr fun r hr => by
    rcases mem2 hr with rfl | rfl
    · exact ⟨0, (at_zero).symm, by simp⟩
    · exact ⟨200, rfl, by simp⟩
  refine pad_call (st := P.scr) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x4 hr
    (Nat.mod_lt _ (rate_pos hr))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact stk_scr' hp (by omega)) (cov_rd cw) cw fun s' hk hst =>
      ⟨Env.call hp h.env hk ?_, ?_⟩
  · intro r hr
    rcases mem3 hr with rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [at_zero], by omega⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · have := hst (P.msg σ) h.repr (by rw [MlKem.bytesAt_length])
    rw [h.x3] at this
    exact this

/-- The arguments of `squeeze`. -/
structure J5 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  st : stateAt s.mem P.scr = padded rate shakeSuffix (P.msg σ)
  x0 : s.gpr .x0 = P.scr
  x1 : (s.gpr .x1).toNat = rate
  x2 : (s.gpr .x2).toNat = 0
  x3 : s.gpr .x3 = P.at' 840
  x4 : (s.gpr .x4).toNat = outlen
  x5 : s.gpr .x5 = P.at' 200

omit hp in
theorem blk3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : outlen < 2 ^ 16) {s : State}
    (h : J4 rate P σ s) : WP isa (.block (sqzArgs rate outlen)) s (J5 rate outlen P σ) := by
  refine wp_mov fun s₁ h₁ e₁ => wp_movz fun s₂ h₂ e₂ => wp_movz fun s₃ h₃ e₃ =>
    wp_addImm (by decide) fun s₄ h₄ e₄ => wp_movz fun s₅ h₅ e₅ => wp_addImm (by decide) fun s₆ h₆ e₆ =>
    wp_nil ?_
  have k₆ := ((((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep).trans h₅.keep).trans h₆.keep
  have m₆ : s₆.mem = s.mem := by rw [h₆.mem, h₅.mem, h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have g25 : ∀ {u : State}, Keep [.x0, .x1, .x2, .x3, .x4, .x5] s u → u.gpr .x25 = P.scr :=
    fun hk => by rw [hk.get .x25, h.env.x25]
  refine ⟨h.env.keep k₆ m₆, by rw [m₆]; exact h.st, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h₆.get .x0, h₅.get .x0, h₄.get .x0, h₃.get .x0, h₂.get .x0, e₁, h.env.x25]
  · rw [h₆.get .x1, h₅.get .x1, h₄.get .x1, h₃.get .x1, e₂]; exact toNat_movz (rate_lt hr)
  · rw [h₆.get .x2, h₅.get .x2, h₄.get .x2, e₃]; rfl
  · rw [h₆.get .x3, h₅.get .x3, e₄, g25 ((h₁.keep.trans h₂.keep).trans h₃.keep).mono]
  · rw [h₆.get .x4, e₅]; exact toNat_movz ho
  · rw [e₆, h₅.get .x25, h₄.get .x25, h₃.get .x25, h₂.get .x25, h₁.get .x25, h.env.x25]

/-- After squeezing: the output. -/
structure J6 (rate outlen : Nat) (P : Sp) (σ s : State) : Prop where
  env : Env P σ s
  out : bytesAt s.mem (P.at' 840) outlen =
    Spec.Sha3.squeezeFrom rate (padded rate shakeSuffix (P.msg σ)) 0 outlen

theorem call3_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J5 rate outlen P σ s) :
    WP isa (.call "vg_keccak_squeeze" Impl.Sha3.AArch64.Stream.squeeze) s (J6 rate outlen P σ) := by
  have hsp := h.env.sp
  have cw : Covers [⟨P.scr, 200⟩, ⟨P.at' 840, outlen⟩, ⟨P.at' 200, 640⟩] s.wr :=
    cov_scr hp h.env.wr fun r hr => by
      rcases mem3 hr with rfl | rfl | rfl
      · exact ⟨0, (at_zero).symm, by simp⟩
      · exact ⟨840, rfl, by simp; omega⟩
      · exact ⟨200, rfl, by simp⟩
  refine squeeze_call (st := P.scr) (out := P.at' 840) (sc := P.at' 200) h.x0 h.x1 h.x2 h.x3 h.x4 h.x5 hr
    (Nat.zero_le _)
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (by rw [← at_zero (P := P)]; exact disj_scr (.inl (by omega)) (by omega) (by omega))
    (disj_scr (.inr (by omega)) (by omega) (by omega))
    (by rw [hsp]; exact hp.sp16) (by rw [stk, hsp]; exact hp.stk_scr.sub_right (sub_scr0 (by omega)))
    (by rw [stk, hsp]; exact stk_scr' hp (by omega)) (by rw [stk, hsp]; exact stk_scr' hp (by omega))
    (cov_rd cw) cw fun s' hk hout _ _ => ⟨Env.call hp h.env hk ?_, ?_⟩
  · intro r hr
    rcases mem4 hr with rfl | rfl | rfl | rfl
    · exact .inl ⟨0, 200, by rw [at_zero], by omega⟩
    · exact .inl ⟨840, outlen, rfl, ho⟩
    · exact .inl ⟨200, 640, rfl, by omega⟩
    · exact .inr rfl
  · rw [hout, h.st]

/-- The sponge, from `J0`: `outlen` bytes of SHAKE at `scratch + 840`. -/
theorem sponge_ok {rate outlen : Nat} (hr : rate ∈ rates) (ho : 840 + outlen ≤ 2016) {s : State}
    (h : J0 P σ s) : WP isa (sponge rate outlen) s (J6 rate outlen P σ) :=
  WP.seq (WP.mono (blk1_ok hp (rate_lt hr) h) fun _ h1 =>
    WP.seq (WP.mono (call1_ok hp hr h1) fun _ h2 => WP.seq (WP.mono (blk2_ok hr h2) fun _ h3 =>
      WP.seq (WP.mono (call2_ok hp hr h3) fun _ h4 =>
        WP.seq (WP.mono (blk3_ok hr (by omega) h4) fun _ h5 => call3_ok hp hr ho h5)))))

/-! ## The epilogue -/

/-- The epilogue: `x30`, `x26`, `x27` and `x25` restored; with `Env`, the
calling convention's obligations. -/
theorem epi_ok {s : State} (he : Env P σ s) :
    WP isa (.block epi) s fun s' => GprAbi σ s' ∧ s'.mem = s.mem ∧
      Keep [.x30, .x26, .x27, .x25] s s' := by
  have in8 : ∀ {u : State}, u.rd = σ.rd → u.wr = σ.wr → ∀ {off : Nat}, off + 8 ≤ 2048 →
      InRegions (u.rd ++ u.wr) (P.at' off) 8 := fun hr hw _ h' => inScrRd hp hr hw h'
  refine wp_ldrx (a := P.at' 2040) (by decide) (by rw [he.x25]) (in8 he.rd he.wr (by omega))
    fun s₁ h₁ e₁ => ?_
  refine wp_ldrx (a := P.at' 2024) (by decide) (by rw [h₁.get .x25, he.x25])
    (in8 (by rw [h₁.rd, he.rd]) (by rw [h₁.wr, he.wr]) (by omega)) fun s₂ h₂ e₂ => ?_
  refine wp_ldrx (a := P.at' 2032) (by decide) (by rw [h₂.get .x25, h₁.get .x25, he.x25])
    (in8 (by rw [h₂.rd, h₁.rd, he.rd]) (by rw [h₂.wr, h₁.wr, he.wr]) (by omega)) fun s₃ h₃ e₃ => ?_
  refine wp_ldrx (a := P.at' 2016) (by decide) (by rw [h₃.get .x25, h₂.get .x25, h₁.get .x25, he.x25])
    (in8 (by rw [h₃.rd, h₂.rd, h₁.rd, he.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr, he.wr]) (by omega))
    fun s₄ h₄ e₄ => wp_nil ?_
  have k₄ := ((h₁.keep.trans h₂.keep).trans h₃.keep).trans h₄.keep
  have m₄ : s₄.mem = s.mem := by rw [h₄.mem, h₃.mem, h₂.mem, h₁.mem]
  have sv := he.saved
  refine ⟨⟨fun r hr => ?_, by rw [k₄.sp, he.sp]⟩, m₄, k₄⟩
  by_cases h30 : r = .x30
  · subst h30; rw [h₄.get .x30, h₃.get .x30, h₂.get .x30, e₁]; exact sv.2.2.2
  by_cases h26 : r = .x26
  · subst h26; rw [h₄.get .x26, h₃.get .x26, e₂, h₁.mem]; exact sv.2.1
  by_cases h27 : r = .x27
  · subst h27; rw [h₄.get .x27, e₃, h₂.mem, h₁.mem]; exact sv.2.2.1
  by_cases h25 : r = .x25
  · subst h25; rw [e₄, h₃.mem, h₂.mem, h₁.mem]; exact sv.1
  rw [k₄.gpr r (by simp [h30, h25, h26, h27]), he.cs r hr h25 h26 h27 h30]

end

end VG.Proof.MlDsa.AArch64.Sample
