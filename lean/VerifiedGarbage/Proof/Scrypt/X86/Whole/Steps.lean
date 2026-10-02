import VerifiedGarbage.Proof.Scrypt.X86.Whole.Layout
import VerifiedGarbage.Proof.Framework.X86.RegUpd

/-!
# scrypt on x86 (32-bit): the blocks between the calls

Untrusted: everything here is checked by Lean. The parameters as numbers
(`Lay.Ok`), the frame's push (`push_ctx`), and what each block between the
calls does: it keeps `Ctx`, and sets up the next call's arguments in the
frame (`PbkArgs`, `RomixArgs`) or the next block.
-/

namespace VG.Proof.Scrypt.X86.Whole

open VG VG.X86 VG.Impl.Scrypt.X86
open VG.Proof.Pbkdf2.Whole.X86 (toNat_setWidth64)

/-! ## Arithmetic -/

theorem ror25 (x : BitVec 32) (h : x.toNat < 2 ^ 25) :
    x.rotateRight 25 = BitVec.ofNat 32 (x.toNat * 128) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    show 25 % 32 = 25 from rfl, Nat.div_eq_of_lt h, Nat.zero_or]

namespace Lay.Ok

variable {L : Lay} (h : L.Ok)
include h

theorem blen_eq : L.blen.toNat = L.r.toNat * L.pp :=
  (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h.bmod)).symm
theorem pp_pos : 0 < L.pp := h.valid.2.2.2.1

theorem blen_lt : L.blen.toNat * 128 < 2 ^ 32 := by
  have hnb := h.nb; have hB := h.nB
  refine Nat.lt_of_not_le fun hge => ?_
  have hb0 : L.b.toNat = 0 := by omega
  have e : L.blen.toNat * 128 = 2 ^ 32 := by omega
  have eb : L.b.setWidth 64 = 0 := by
    apply BitVec.eq_of_toNat_eq; rw [toNat_setWidth64, hb0]; rfl
  apply h.kb L.A
  · simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  · have z : ∀ x : Addr, x - L.b.setWidth 64 = x := fun x => by rw [eb]; exact BitVec.sub_zero x
    simp only [Region.Contains, z, e, Lay.A, toNat_setWidth64]; omega

theorem blen25 : L.blen.toNat < 2 ^ 25 := by have := h.blen_lt; omega

theorem r_le : L.r.toNat ≤ L.blen.toNat := by
  rw [h.blen_eq]; exact Nat.le_mul_of_pos_right _ h.pp_pos

theorem r25 : L.r.toNat < 2 ^ 25 := by have := h.blen25; have := h.r_le; omega

/-- `128 r p`, the length of `b`. -/
theorem len_b : 128 * L.r.toNat * L.pp = L.blen.toNat * 128 := by
  rw [h.blen_eq, Nat.mul_comm 128, Nat.mul_assoc, Nat.mul_comm 128, Nat.mul_assoc]

/-- The derived key of step 1 is not too long for PBKDF2. -/
theorem ol1 : L.blen.toNat * 128 ≤ (2 ^ 32 - 1) * 32 := by
  have h₁ := h.valid.2.2.2.2.1
  have h₂ := Nat.div_mul_le_self ((2 ^ 32 - 1) * 32) (128 * L.r.toNat)
  have h₃ : L.pp * (128 * L.r.toNat) ≤ (2 ^ 32 - 1) * 32 / (128 * L.r.toNat) * (128 * L.r.toNat) :=
    Nat.mul_le_mul_right _ h₁
  rw [← h.len_b, Nat.mul_comm (128 * L.r.toNat)]
  omega

end Lay.Ok

/-! ## Words at offsets -/

/-- A word read back past a store of another at a different offset. -/
theorem rd_off {P : Addr} {m : Mem} {x y : Nat} {v : BitVec 32} (h : x + 4 ≤ y ∨ y + 4 ≤ x)
    (hx : x + 4 ≤ 2 ^ 32) (hy : y + 4 ≤ 2 ^ 32) :
    (m.writeW (P + BitVec.ofNat 64 y) v).readW (P + BitVec.ofNat 64 x) 32 =
      m.readW (P + BitVec.ofNat 64 x) 32 :=
  Mem.readW_writeW_sep (Offset.sep P h (by omega) (by omega)) (by decide)

/-! ## In the frame -/

theorem ea_esp (t : State) (d : Nat) : t.ea (sp d) = (t.gpr .esp + BitVec.ofNat 32 d).setWidth 64 := rfl

section
variable {L : Lay} {g : Reg → BitVec 32} {m₀ : Mem}

namespace Ctx

variable {t t' : State} (hc : Ctx L g m₀ t)
include hc

theorem inArgs (hL : L.Ok) (d : Nat) (h₁ : 120 ≤ d) (h₂ : d + 4 ≤ 172) :
    InRegions (t.rd ++ t.wr) (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.ARGS, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inFr (hL : L.Ok) (d : Nat) (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 116) :
    InRegions (t.rd ++ t.wr) (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.rd, hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

theorem inFrW (hL : L.Ok) (d : Nat) (h₁ : 80 ≤ d) (h₂ : d + 4 ≤ 116) :
    InRegions t.wr (L.A + BitVec.ofNat 64 d) 4 :=
  ⟨L.FR, by rw [hc.wr]; simp, Offset.contains _ h₁ (by omega) (by have := hL.nB; omega)⟩

/-- Code that writes only the frame and registers other than the
callee-saved ones. -/
theorem store (hL : L.Ok) (hrd : t'.rd = t.rd) (hwr : t'.wr = t.wr)
    (hg : ∀ r ∈ calleeSaved, t'.gpr r = t.gpr r) (hf : Frame [L.FR] t.mem t'.mem) : Ctx L g m₀ t' := by
  have hnB := hL.nB
  refine ⟨hrd.trans hc.rd, hwr.trans hc.wr, (hg .esp (by simp [calleeSaved])).trans hc.esp,
    fun r hr hr' => (hg r hr).trans (hc.cs r hr hr'), hc.kept.frame hf fun R hR => ?_,
    hc.frame.trans (Frame.sub hf fun r hr => ?_)⟩
  · simp only [List.mem_singleton] at hR; subst hR
    exact Offset.disjoint _ (by omega) (by omega) (by omega)
  · simp only [List.mem_singleton] at hr; subst hr
    exact ⟨L.STK, by simp, Offset.sub_base _ (by omega)⟩

end Ctx

/-- A store into the frame is in `FR`. -/
theorem Frame.fr (hL : L.Ok) {m m' : Mem} (hf : Frame [L.FR] m m') {k : Nat} (h₁ : 80 ≤ k)
    (h₂ : k + 4 ≤ 116) (v : BitVec 32) : Frame [L.FR] m (m'.writeW (L.A + BitVec.ofNat 64 k) v) :=
  hf.writeW (List.mem_singleton_self _) _ (Offset.contains _ h₁ (by omega) (by have := hL.nB; omega))

/-- The callee-saved registers, which the blocks leave alone. -/
macro "scrypt_cs_tac" : tactic => `(tactic| (
  intro r hr
  simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_setFlags, RegUpd.gpr_arithFlags, reduceCtorEq, ite_false]))

/-- The arguments of a call of PBKDF2 with the salt `salt` (`sl` bytes) and
the output `out` (`ol` bytes), in the frame. -/
structure PbkArgs (L : Lay) (salt sl out ol : BitVec 32) (m : Mem) : Prop where
  a0 : m.readW (L.A + BitVec.ofNat 64 80) 32 = L.pw
  a1 : m.readW (L.A + BitVec.ofNat 64 84) 32 = L.pwl
  a2 : m.readW (L.A + BitVec.ofNat 64 88) 32 = salt
  a3 : m.readW (L.A + BitVec.ofNat 64 92) 32 = sl
  a4 : m.readW (L.A + BitVec.ofNat 64 96) 32 = 1
  a5 : m.readW (L.A + BitVec.ofNat 64 100) 32 = out
  a6 : m.readW (L.A + BitVec.ofNat 64 104) 32 = ol
  a7 : m.readW (L.A + BitVec.ofNat 64 108) 32 = L.scr

/-! ## One instruction at a time

`Same t u`: `u` is `t` with other values in `eax`, `ecx`, `edx` and the
flags. The blocks load a word into `eax`, maybe change it, and store it in
the frame; each of these steps is proved once, for any offsets. -/

/-- `u` differs from `t` only in registers other than the callee-saved ones. -/
structure Same (t u : State) : Prop where
  rd : u.rd = t.rd
  wr : u.wr = t.wr
  cs : ∀ r ∈ calleeSaved, u.gpr r = t.gpr r
  mem : u.mem = t.mem

theorem Same.refl (t : State) : Same t t := ⟨rfl, rfl, fun _ _ => rfl, rfl⟩

theorem Same.esp {t u : State} (h : Same t u) : u.gpr .esp = t.gpr .esp := h.cs .esp (by simp [calleeSaved])

theorem Same.setReg {t u : State} (h : Same t u) {r : Reg} (hr : r ∉ calleeSaved) (v : BitVec 32) :
    Same t (u.setReg r v) :=
  ⟨h.rd, h.wr, fun r' hr' => by
    rw [RegUpd.gpr_setReg]; split
    · subst r'; exact absurd hr' hr
    · exact h.cs r' hr', h.mem⟩

theorem Same.setFlags {t u : State} (h : Same t u) (a b c d : Option Bool) : Same t (u.setFlags a b c d) :=
  ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem Same.arithFlags {t u : State} (h : Same t u) (x : BitVec 32) (c o : Bool) :
    Same t (VG.X86.arithFlags u x c o) := ⟨h.rd, h.wr, h.cs, h.mem⟩

theorem eax_cs : Reg.eax ∉ calleeSaved := by decide
theorem ecx_cs : Reg.ecx ∉ calleeSaved := by decide
theorem edx_cs : Reg.edx ∉ calleeSaved := by decide

/-- A step of a block, from a state `Same` as `t`. -/
def Step (t : State) (P : State → Prop) (is : List Instr) (Q : State → Prop) : Prop :=
  ∀ u, Same t u → P u → WP isa (.block is) u Q

/-- A load of `[esp + a]`, a word of the frame or of our arguments. -/
theorem ld_eq (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (a : Nat) (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92)
    {u : State} (hu : Same t u) :
    readSrc u (.mem (sp a)) = some (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) := by
  have hin : InRegions (u.rd ++ u.wr) (L.A + BitVec.ofNat 64 (80 + a)) 4 := by
    rw [hu.rd, hu.wr]
    rcases ha with ha | ha
    · exact hc.inFr hL _ (by omega) (by omega)
    · exact hc.inArgs hL _ (by omega) (by omega)
  simp only [readSrc, State.load32, ea_esp, hu.esp, hc.esp, hL.ea_sp (d := a) (by omega), hin, ↓reduceIte,
    hu.mem]

/-- `mov e, [esp + a]`. -/
theorem ld_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {e : Reg} (he : e ∉ calleeSaved) (a : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) {is : List Instr} {Q : State → Prop} {u : State}
    (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32 →
      (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.mem (sp a)) :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ (hu.setReg he (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32))
    (RegUpd.gpr_setReg_self _ _ _) fun r hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩
  simp only [exec, ld_eq hL hc a ha hu, Option.map_some]

/-- `mov e, imm`. -/
theorem imm_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) (x : BitVec 32) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) → WP isa (.block is) u' Q) :
    WP isa (.block (.mov e (.imm x) :: is)) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, h _ (hu.setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => RegUpd.gpr_setReg_of_ne _ _ hr⟩

/-- `ror e, 25`: times 128. -/
theorem ror_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {is : List Instr}
    {Q : State → Prop} {u : State} (hu : Same t u)
    (h : ∀ u', Same t u' → u'.gpr e = (u.gpr e).rotateRight 25 → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (times128 e :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.setFlags (some ((u.gpr e).rotateRight 25).msb) none u.zf u.sf).setReg
    he _) (RegUpd.gpr_setReg_self _ _ _) fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_setFlags]⟩
  simp only [exec, execShift]
  rfl

/-- `add e, src`. -/
theorem add_ok {t : State} {e : Reg} (he : e ∉ calleeSaved) {src : Src} {x : BitVec 32}
    {is : List Instr} {Q : State → Prop} {u : State} (hu : Same t u) (hx : readSrc u src = some x)
    (h : ∀ u', Same t u' → u'.gpr e = u.gpr e + x → (∀ r, r ≠ e → u'.gpr r = u.gpr r) →
      WP isa (.block is) u' Q) :
    WP isa (.block (.alu .add e src :: is)) u Q := by
  refine WP.block_cons_iff.mpr ⟨_, ?_, h _ ((hu.arithFlags (u.gpr e + x) (2 ^ 32 ≤ (u.gpr e).toNat + x.toNat)
    (addOverflow (u.gpr e) x (u.gpr e + x))).setReg he _) (RegUpd.gpr_setReg_self _ _ _)
    fun _ hr => by rw [RegUpd.gpr_setReg_of_ne _ _ hr, RegUpd.gpr_arithFlags]⟩
  simp only [exec, execAlu, hx, Option.bind_some]

/-- `mov [esp + d], eax`, a word of the frame, ending a step. -/
theorem st_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (d : Nat) (hd : d + 4 ≤ 36) {u : State}
    (hu : Same t u) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem = t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax) →
      (∀ r, t'.gpr r = u.gpr r) → WP isa (.block is) t' Q) :
    WP isa (.block (.store (sp d) .eax :: is)) u Q := by
  have hin : InRegions u.wr (L.A + BitVec.ofNat 64 (80 + d)) 4 := by
    rw [hu.wr]; exact hc.inFrW hL _ (by omega) (by omega)
  have hf : Frame [L.FR] t.mem (t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax)) :=
    Frame.fr hL (Frame.refl _ _) (by omega) (by omega) _
  have hf' : Frame [L.FR] t.mem (u.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax)) := by
    rw [hu.mem]; exact hf
  refine WP.block_cons_iff.mpr ⟨{ u with mem := u.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (u.gpr .eax) },
    ?_, h _ (hc.store hL hu.rd hu.wr hu.cs hf') hf' (by rw [hu.mem]) fun _ => rfl⟩
  simp only [exec, State.store32, ea_esp, hu.esp, hc.esp, hL.ea_sp (d := d) (by omega), hin, ↓reduceIte]

/-- A word copied from `[esp + a]` to `[esp + d]`. -/
theorem cp_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) (a d : Nat)
    (ha : a + 4 ≤ 36 ∨ 40 ≤ a ∧ a + 4 ≤ 92) (hd : d + 4 ≤ 36) {is : List Instr} {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem = t.mem.writeW (L.A + BitVec.ofNat 64 (80 + d)) (t.mem.readW (L.A + BitVec.ofNat 64 (80 + a)) 32) →
      WP isa (.block is) t' Q) :
    WP isa (.block (.mov .eax (.mem (sp a)) :: .store (sp d) .eax :: is)) t Q :=
  ld_ok hL hc eax_cs a ha (Same.refl t) fun _ hu he _ =>
    st_ok hL hc d hd hu fun t' hc' hf hm _ => h t' hc' hf (he ▸ hm)

theorem frame_trans {t₁ t₂ t₃ : State} (h₁ : Frame [L.FR] t₁.mem t₂.mem) (h₂ : Frame [L.FR] t₂.mem t₃.mem) :
    Frame [L.FR] t₁.mem t₃.mem := h₁.trans h₂

theorem pbk1Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      PbkArgs L L.salt L.sl L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) t'.mem → Q t') :
    WP isa (.block pbk1Args) t Q := by
  unfold pbk1Args
  refine cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 48 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine cp_ok hL hc₃ 52 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine imm_ok eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine cp_ok hL hc₅ 60 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine ld_ok hL hc₆ eax_cs 64 (by omega) (Same.refl t₆) fun u hu he _ => ?_
  refine ror_ok eax_cs hu fun u' hu' he' _ => ?_
  refine st_ok hL hc₆ 24 (by omega) hu' fun t₇ hc₇ hf₇ hm₇ _ => ?_
  rw [he', he, hc₆.kept.blen, ror25 _ hL.blen25] at hm₇
  refine cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.salt] at hm₃; rw [hc₃.kept.sl] at hm₄
  rw [hc₅.kept.b] at hm₆; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
    Mem.readW_writeW_self32]
/-- `cmp e, e'`, ending a block. -/
theorem cmp_ok {e e' : Reg} {u : State} {Q : State → Prop}
    (h : Q (VG.X86.arithFlags u (u.gpr e - u.gpr e') ((u.gpr e).toNat < (u.gpr e').toNat)
      (subOverflow (u.gpr e) (u.gpr e') (u.gpr e - u.gpr e')))) :
    WP isa (.block [.alu .cmp e (.reg e')]) u Q :=
  WP.block_cons_iff.mpr ⟨_, rfl, WP.block_nil h⟩

theorem cur0_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = L.b →
      Q t') :
    WP isa (.block cur0) t Q :=
  cp_ok hL hc 60 32 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => WP.block_nil (h t₁ hc₁ hf₁ (by
    simp only [Nat.reduceAdd] at hm₁; rw [hm₁, Mem.readW_writeW_self32, hc.kept.b]))

/-- The arguments of a call of ROMix on the block at `cur`, in the frame. -/
structure RomixArgs (L : Lay) (cur : BitVec 32) (m : Mem) : Prop where
  a0 : m.readW (L.A + BitVec.ofNat 64 80) 32 = cur
  a1 : m.readW (L.A + BitVec.ofNat 64 84) 32 = L.r
  a2 : m.readW (L.A + BitVec.ofNat 64 88) 32 = L.v
  a3 : m.readW (L.A + BitVec.ofNat 64 92) 32 = L.vlen
  a4 : m.readW (L.A + BitVec.ofNat 64 96) 32 = L.scr
  a5 : m.readW (L.A + BitVec.ofNat 64 100) 32 = L.r + 2

theorem romixArgs_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem → RomixArgs L cur t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur → Q t') :
    WP isa (.block romixArgs) t Q := by
  unfold romixArgs
  refine cp_ok hL hc 32 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 56 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 68 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine cp_ok hL hc₃ 72 12 (by omega) (by omega) fun t₄ hc₄ hf₄ hm₄ => ?_
  refine cp_ok hL hc₄ 76 16 (by omega) (by omega) fun t₅ hc₅ hf₅ hm₅ => ?_
  refine ld_ok hL hc₅ eax_cs 56 (by omega) (Same.refl t₅) fun u hu he _ => ?_
  refine add_ok eax_cs hu rfl fun u' hu' he' _ => ?_
  refine st_ok hL hc₅ 20 (by omega) hu' fun t₆ hc₆ hf₆ hm₆ _ => WP.block_nil ?_
  rw [he', he] at hm₆
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆
  rw [hcur] at hm₁; rw [hc₁.kept.r] at hm₂; rw [hc₂.kept.v] at hm₃; rw [hc₃.kept.vlen] at hm₄
  rw [hc₄.kept.scr] at hm₅; rw [hc₅.kept.r] at hm₆
  refine h t₆ hc₆ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ hf₆) ?_ ?_
  · constructor <;> simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
      Mem.readW_writeW_self32]
  · simp (disch := decide) only [hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off, hcur]

theorem pbk2Args_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      PbkArgs L L.b (BitVec.ofNat 32 (L.blen.toNat * 128)) L.out L.ol t'.mem → Q t') :
    WP isa (.block pbk2Args) t Q := by
  unfold pbk2Args
  refine cp_ok hL hc 40 0 (by omega) (by omega) fun t₁ hc₁ hf₁ hm₁ => ?_
  refine cp_ok hL hc₁ 44 4 (by omega) (by omega) fun t₂ hc₂ hf₂ hm₂ => ?_
  refine cp_ok hL hc₂ 60 8 (by omega) (by omega) fun t₃ hc₃ hf₃ hm₃ => ?_
  refine ld_ok hL hc₃ eax_cs 64 (by omega) (Same.refl t₃) fun u hu he _ => ?_
  refine ror_ok eax_cs hu fun u' hu' he' _ => ?_
  refine st_ok hL hc₃ 12 (by omega) hu' fun t₄ hc₄ hf₄ hm₄ _ => ?_
  rw [he', he, hc₃.kept.blen, ror25 _ hL.blen25] at hm₄
  refine imm_ok eax_cs 1 (Same.refl t₄) fun u hu he _ => ?_
  refine st_ok hL hc₄ 16 (by omega) hu fun t₅ hc₅ hf₅ hm₅ _ => ?_
  rw [he] at hm₅
  refine cp_ok hL hc₅ 84 20 (by omega) (by omega) fun t₆ hc₆ hf₆ hm₆ => ?_
  refine cp_ok hL hc₆ 88 24 (by omega) (by omega) fun t₇ hc₇ hf₇ hm₇ => ?_
  refine cp_ok hL hc₇ 76 28 (by omega) (by omega) fun t₈ hc₈ hf₈ hm₈ => ?_
  refine WP.block_nil (h t₈ hc₈ (frame_trans hf₁ <| frame_trans hf₂ <| frame_trans hf₃ <| frame_trans hf₄ <|
    frame_trans hf₅ <| frame_trans hf₆ <| frame_trans hf₇ hf₈) ?_)
  simp only [Nat.reduceAdd] at hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇ hm₈
  rw [hc.kept.pw] at hm₁; rw [hc₁.kept.pwl] at hm₂; rw [hc₂.kept.b] at hm₃; rw [hc₅.kept.out] at hm₆
  rw [hc₆.kept.ol] at hm₇; rw [hc₇.kept.scr] at hm₈
  constructor <;> simp (disch := decide) only [hm₈, hm₇, hm₆, hm₅, hm₄, hm₃, hm₂, hm₁, rd_off,
    Mem.readW_writeW_self32]

theorem Ctx.flags {t : State} (hL : L.Ok) (hc : Ctx L g m₀ t) (x : BitVec 32) (c o : Bool) :
    Ctx L g m₀ (VG.X86.arithFlags t x c o) :=
  hc.store hL rfl rfl (fun _ _ => rfl) (Frame.refl _ _)

theorem nextBlock_ok (hL : L.Ok) {t : State} (hc : Ctx L g m₀ t) {cur : BitVec 32}
    (hcur : t.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur) {Q : State → Prop}
    (h : ∀ t', Ctx L g m₀ t' → Frame [L.FR] t.mem t'.mem →
      t'.mem.readW (L.A + BitVec.ofNat 64 112) 32 = cur + BitVec.ofNat 32 (L.r.toNat * 128) →
      t'.zf = some (cur + BitVec.ofNat 32 (L.r.toNat * 128) -
        (BitVec.ofNat 32 (L.blen.toNat * 128) + L.b) == 0) → Q t') :
    WP isa (.block nextBlock) t Q := by
  unfold nextBlock
  refine ld_ok hL hc ecx_cs 56 (by omega) (Same.refl t) fun u₁ hu₁ e₁ _ => ?_
  refine ror_ok ecx_cs hu₁ fun u₂ hu₂ e₂ k₂ => ?_
  refine ld_ok hL hc eax_cs 32 (by omega) hu₂ fun u₃ hu₃ e₃ k₃ => ?_
  refine add_ok eax_cs hu₃ rfl fun u₄ hu₄ e₄ k₄ => ?_
  refine ld_ok hL hc edx_cs 64 (by omega) hu₄ fun u₅ hu₅ e₅ k₅ => ?_
  refine ror_ok edx_cs hu₅ fun u₆ hu₆ e₆ k₆ => ?_
  refine add_ok edx_cs hu₆ (ld_eq hL hc 60 (by omega) hu₆) fun u₇ hu₇ e₇ k₇ => ?_
  refine st_ok hL hc 32 (by omega) hu₇ fun t₁ hc₁ hf₁ hm₁ k₈ => cmp_ok ?_
  have ecx : u₃.gpr .ecx = BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₃ _ (by decide), e₂, e₁, hc.kept.r, ror25 _ hL.r25]
  have eax : u₇.gpr .eax = cur + BitVec.ofNat 32 (L.r.toNat * 128) := by
    rw [k₇ _ (by decide), k₆ _ (by decide), k₅ _ (by decide), e₄, e₃, ecx]
    simp only [Nat.reduceAdd]; rw [hcur]
  have edx : u₇.gpr .edx = BitVec.ofNat 32 (L.blen.toNat * 128) + L.b := by
    rw [e₇, e₆, e₅, hc.kept.blen, ror25 _ hL.blen25]
    simp only [Nat.reduceAdd]; rw [hc.kept.b]
  refine h _ (hc₁.flags hL _ _ _) hf₁ ?_ ?_
  · simp only [RegUpd.mem_arithFlags, hm₁, Nat.reduceAdd, Mem.readW_writeW_self32, eax]
  · simp only [RegUpd.zf_arithFlags, k₈, eax, edx]

end

end VG.Proof.Scrypt.X86.Whole
