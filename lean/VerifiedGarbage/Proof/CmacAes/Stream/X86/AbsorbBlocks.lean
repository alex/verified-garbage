import VerifiedGarbage.Proof.CmacAes.Stream.X86.Common

/-!
# Streaming AES-CMAC on x86: `vg_cmac_aes_absorb`'s straight-line code

The precondition by name (`APre`), what holds at every point of the code
outside the calls (`ACtx`: `esp`, the regions and the stack arguments are
those on entry), and what each piece of code between the copies and calls
computes, in terms of `count` (`c`) and `len` (`L`): the bytes held back `h =
held c`, the bytes copied after them `f = min L (16 - h)`, the data left `L -
f`, whether to chain the block held back (`b1`), the blocks chained after it
(`nb`), and the rest (`rest`).
-/

namespace VG.Proof.CmacAes.Stream.X86

open VG VG.X86 VG.Impl.CmacAes.Stream.X86

variable (v : Proof.Aes.X86.Ctr32Impl)
open VG.Impl.CmacAes.X86 (at_ argOp)
open VG.Proof.MdStream.X86 (Upd Fupd wp_mov wp_movi wp_addi wp_add wp_subi wp_sub wp_andi wp_cmp wp_shr eval_e
  eval_b ofNat_beq_zero sub_ofNat)
open VG.Proof.CmacAes.X86 (wp_arg toNat_rounds)
open VG.Proof.Cmac.Stream (held held_le)

/-! ## The numbers -/

/-- The bytes copied after the `held c` held back. -/
def fOf (c L : Nat) : Nat := min L (16 - held c)

/-- The data left after them. -/
def leftOf (c L : Nat) : Nat := L - fOf c L

/-- The number of blocks the first call chains: the block held back, if data is left. -/
def b1Of (c L : Nat) : Nat := if leftOf c L = 0 then 0 else 1

/-- The number of blocks the second call chains: those of the data left but its
last 1 to 16 bytes. -/
def nbOf (c L : Nat) : Nat := if leftOf c L = 0 then 0 else (leftOf c L - 1) / 16

/-- The bytes copied to the start of the bytes held back at the end. -/
def restOf (c L : Nat) : Nat := leftOf c L - 16 * nbOf c L

theorem f_le (c L : Nat) : fOf c L ≤ L ∧ fOf c L + held c ≤ 16 := by
  have := held_le c; unfold fOf; omega

theorem nb_le (c L : Nat) : fOf c L + 16 * nbOf c L + restOf c L = L := by
  have := f_le c L; unfold restOf nbOf leftOf; split <;> omega

theorem rest_le (c L : Nat) : restOf c L ≤ 16 := by unfold restOf nbOf leftOf; split <;> omega

theorem rest_zero {c L : Nat} (h : leftOf c L = 0) : restOf c L = 0 := by simp [restOf, nbOf, h]

/-! ## Arithmetic on registers -/

/-- `16 nb` for the data left `x > 0`, as `sub 1; mov; and 15; sub` computes it. -/
theorem nb16_bv {x : Nat} (hx : 0 < x) (hx' : x < 2 ^ 32) :
    BitVec.ofNat 32 x - 1 - ((BitVec.ofNat 32 x - 1) &&& 15) = BitVec.ofNat 32 (16 * ((x - 1) / 16)) := by
  apply BitVec.eq_of_toNat_eq
  have e : (BitVec.ofNat 32 x - 1).toNat = x - 1 := by
    rw [BitVec.toNat_sub, BitVec.toNat_ofNat, show (1 : BitVec 32).toNat = 1 from rfl]; omega
  rw [BitVec.toNat_sub, and15, e, BitVec.toNat_ofNat]
  omega

theorem shr4 {n : Nat} (hn : 16 * n < 2 ^ 32) :
    BitVec.ofNat 32 (16 * n) >>> 4 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev aSt : BitVec 32 := arg s₀ 0
abbrev aR : Nat := (arg s₀ 1).toNat
abbrev aD : BitVec 32 := arg s₀ 4
abbrev aL : Nat := (arg s₀ 5).toNat
abbrev aSc : BitVec 32 := arg s₀ 6
abbrev aE : BitVec 32 := s₀.gpr .esp
/-- `count`. -/
abbrev aC : Nat := (countX86 s₀).toNat
abbrev astR : Region := ⟨(aSt s₀).setWidth 64, 304⟩
abbrev adR : Region := ⟨(aD s₀).setWidth 64, aL s₀⟩
abbrev ascR : Region := ⟨(aSc s₀).setWidth 64, 2304⟩
abbrev aaR : Region := ⟨argAddr s₀ 0, 28⟩

/-- Where the function writes: the state, the scratch buffer and the stack. -/
abbrev ABig : List Region := [astR s₀, ascR s₀, below (aE s₀) 56]

end

/-- The precondition, by name. -/
structure APre (s₀ : State) : Prop where
  rd : s₀.rd = [adR s₀, aaR s₀]
  wr : s₀.wr = [astR s₀, ascR s₀]
  st_d : (astR s₀).Disjoint (adR s₀)
  st_s : (astR s₀).Disjoint (ascR s₀)
  d_s : (adR s₀).Disjoint (ascR s₀)
  a_st : (aaR s₀).Disjoint (astR s₀)
  a_s : (aaR s₀).Disjoint (ascR s₀)
  ret_st : (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint (astR s₀)
  ret_s : (⟨(aE s₀).setWidth 64, 4⟩ : Region).Disjoint (ascR s₀)
  b_st' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (astR s₀)
  b_d' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (adR s₀)
  b_s' : (⟨(aE s₀).setWidth 64 - BitVec.ofNat 64 56, 56⟩ : Region).Disjoint (ascR s₀)
  fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32
  fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32
  fS : (aSc s₀).toNat + 2304 ≤ 2 ^ 32
  esp56 : 56 ≤ (aE s₀).toNat
  espfit : (aE s₀).toNat + 32 ≤ 2 ^ 32
  rounds : aR s₀ = 10 ∨ aR s₀ = 12 ∨ aR s₀ = 14

theorem APre.of {s₀ : State} (h : absorbX86.pre s₀) : APre s₀ :=
  let ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩ := h
  ⟨a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p, q, r⟩

namespace APre
variable {s₀ : State} (hp : APre s₀)
include hp

theorem b_st : (below (aE s₀) 56).Disjoint (astR s₀) := by rw [below_eq hp.esp56]; exact hp.b_st'
theorem b_d : (below (aE s₀) 56).Disjoint (adR s₀) := by rw [below_eq hp.esp56]; exact hp.b_d'
theorem b_s : (below (aE s₀) 56).Disjoint (ascR s₀) := by rw [below_eq hp.esp56]; exact hp.b_s'

theorem fit : (s₀.gpr .esp).toNat + 4 + 4 * 7 ≤ 2 ^ 32 := by have := hp.espfit; omega

theorem arg_in {i : Nat} (hi : i < 7) : InRegions (s₀.rd ++ s₀.wr) (argAddr s₀ i) 4 :=
  ⟨aaR s₀, by simp [hp.rd], arg_contains hp.fit hi⟩

/-- The stack arguments are unchanged where only `ABig` changes. -/
theorem keep {m : Mem} (hf : Frame (ABig s₀) s₀.mem m) {i : Nat} (hi : i < 7) :
    m.readW (argAddr s₀ i) 32 = arg s₀ i :=
  arg_keep hf fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact hp.a_st.sub_left (arg_sub hp.fit hi)
    · exact hp.a_s.sub_left (arg_sub hp.fit hi)
    · exact (args_below hp.fit (by decide) hp.esp56).symm.sub_left (arg_sub hp.fit hi)

theorem argsOut : ArgsOut 7 s₀ := by
  refine ⟨by have := hp.espfit; omega, ?_⟩
  rw [hp.wr]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by have := hp.espfit; omega) hp.ret_st hp.a_st
  · exact VG.X86.Taint.frame_disjoint (n := 28) (by have := hp.espfit; omega) hp.ret_s hp.a_s

end APre

theorem APre.lt {s₀ : State} (_hp : APre s₀) : aL s₀ < 2 ^ 32 := (arg s₀ 5).isLt

theorem APre.savedMem_big {s₀ : State} (_hp : APre s₀) : Frame (ABig s₀) s₀.mem (savedMem s₀ (aSc s₀)) :=
  (savedMem_frame _ _).sub fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨ascR s₀, by simp, Offset.sub_base _ (by decide)⟩

/-! ## Between the calls -/

/-- What holds at every point of the code outside the calls: `esp`, the
regions and the stack arguments are those on entry. -/
structure ACtx (s₀ s : State) : Prop where
  esp : s.gpr .esp = aE s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  args : ∀ i < 7, s.mem.readW (argAddr s₀ i) 32 = arg s₀ i

theorem ACtx.of_frame {s₀ s : State} (hp : APre s₀) (hesp : s.gpr .esp = aE s₀) (hrd : s.rd = s₀.rd)
    (hwr : s.wr = s₀.wr) (hf : Frame (ABig s₀) s₀.mem s.mem) : ACtx s₀ s :=
  ⟨hesp, hrd, hwr, fun _ hi => hp.keep hf hi⟩

theorem ACtx.upd {s₀ s s' : State} {d : Reg} {v : BitVec 32} (h : ACtx s₀ s) (u : Upd s s' d v)
    (hd : d ≠ .esp) : ACtx s₀ s' :=
  ⟨by rw [u.other _ (Ne.symm hd), h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.fupd {s₀ s s' : State} (h : ACtx s₀ s) (u : Fupd s s') : ACtx s₀ s' :=
  ⟨by rw [u.gpr, h.esp], by rw [u.rd, h.rd], by rw [u.wr, h.wr], by rw [u.mem]; exact h.args⟩

theorem ACtx.pt {s₀ s : State} (h : ACtx s₀ s) : Pt 7 s₀ s := ⟨h.esp, h.wr, h.args⟩

/-- `mov d, [esp + 4 + 4 i]`. -/
theorem ACtx.wp_arg {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s) {d : Reg} (hd : d ≠ .esp) {i : Nat} (hi : i < 7)
    {is : List Instr} {Q : State → Prop}
    (k : ∀ s', Upd s s' d (arg s₀ i) → ACtx s₀ s' → WP isa (.block is) s' Q) :
    WP isa (.block (.mov d (argOp i) :: is)) s Q :=
  VG.Proof.CmacAes.X86.wp_arg (s₀ := s₀) h.esp (by rw [h.rd, h.wr]; exact hp.arg_in hi) (h.args i hi)
    fun s' u => k s' u (h.upd u hd)

/-! ## `fill`: how many bytes to copy, and where -/

/-- What `fill` leaves. -/
structure Filled (s₀ s s' : State) : Prop where
  ctx : ACtx s₀ s'
  mem : s'.mem = s.mem
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))
  esi : s'.gpr .esi = aD s₀
  edi : s'.gpr .edi = aSt s₀ + BitVec.ofNat 32 (288 + held (aC s₀))

theorem fill_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hax : s.gpr .eax = BitVec.ofNat 32 (held (aC s₀))) : WP isa fill s (Filled s₀ s) := by
  have hh := held_le (aC s₀)
  have hL := hp.lt
  have ⟨hfL, hfh⟩ := f_le (aC s₀) (aL s₀)
  unfold fill
  refine WP.seq (wp_movi fun s₁ u₁ => wp_sub fun s₂ u₂ _ => (h.upd u₁ (by decide)).upd u₂ (by decide) |>.wp_arg hp
    (by decide) (by decide) fun s₃ u₃ c₃ => wp_cmp fun s₄ f₄ cf₄ _ => WP.block_nil ?_)
  have ecx₂ : s₂.gpr .ecx = BitVec.ofNat 32 (16 - held (aC s₀)) := by
    rw [u₂.gpr, u₁.gpr, u₁.other _ (by decide), hax]; exact sub_ofNat hh
  have ecx₄ : s₄.gpr .ecx = BitVec.ofNat 32 (16 - held (aC s₀)) := by rw [f₄.gpr, u₃.other _ (by decide), ecx₂]
  have edx₄ : s₄.gpr .edx = BitVec.ofNat 32 (aL s₀) := by rw [f₄.gpr, u₃.gpr]; exact arg_ofNat s₀ 5
  have c₄ := c₃.fupd f₄
  have cf : s₄.cf = some (decide (aL s₀ < 16 - held (aC s₀))) := by
    rw [cf₄, u₃.gpr, u₃.other _ (by decide), ecx₂, toNat_ofNat32 (by omega)]
  have eax₄ : s₄.gpr .eax = s.gpr .eax := by
    rw [f₄.gpr, u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₄ : s₄.mem = s.mem := by rw [f₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₅ : State) => ACtx s₀ s₅ ∧ s₅.mem = s.mem ∧
      s₅.gpr .ecx = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀)) ∧ s₅.gpr .eax = s.gpr .eax) ?_ fun s₅ h₅ => ?_)
  · have ev : isa.eval .b s₄ = some (decide (aL s₀ < 16 - held (aC s₀))) := by
      show VG.X86.eval .b s₄ = _; rw [eval_b, cf]
    by_cases hl : aL s₀ < 16 - held (aC s₀)
    · refine WP.ite true (by rw [ev]; simp [hl]) (fun _ => wp_mov fun s₅ u₅ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₄.upd u₅ (by decide), by rw [u₅.mem, m₄], by rw [u₅.gpr, edx₄, fOf, Nat.min_eq_left (by omega)],
        by rw [u₅.other _ (by decide), eax₄]⟩
    · refine WP.ite false (by rw [ev]; simp [hl]) (fun h => by cases h) fun _ => WP.block_nil ?_
      exact ⟨c₄, m₄, by rw [ecx₄, fOf, Nat.min_eq_right (by omega)], eax₄⟩
  · obtain ⟨c₅, m₅, ecx₅, eax₅⟩ := h₅
    refine wp_mov fun s₆ u₆ => (c₅.upd u₆ (by decide)).wp_arg hp (by decide) (by decide) fun s₇ u₇ c₇ =>
      c₇.wp_arg hp (by decide) (by decide) fun s₈ u₈ c₈ => wp_addi fun s₉ u₉ => wp_add fun s₁₀ u₁₀ => WP.block_nil ?_
    have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
    refine ⟨(c₈.upd u₉ (by decide)).upd u₁₀ (by decide), by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅],
      ?_, ?_, ?_, ?_⟩
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.gpr, ecx₅]
    · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr]
    · rw [u₁₀.gpr, u₉.gpr, u₉.other _ (by decide), u₈.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), eax₅, hax]
      exact Offset.add_add _ 288 _

/-! ## `chain1`: the arguments of the first call -/

/-- The arguments of a call of `vg_cmac_aes_update` on `n` blocks at `Dd`,
from a state with the regions and stack of `s₀`. -/
theorem APre.uargs {s₀ s : State} (hp : APre s₀) {Dd : BitVec 32} {n : Nat}
    (heax : s.gpr .eax = aSt s₀) (hecx : s.gpr .ecx = BitVec.ofNat 32 (aR s₀))
    (hedx : s.gpr .edx = aSt s₀ + BitVec.ofNat 32 272) (hebx : s.gpr .ebx = Dd)
    (hesi : s.gpr .esi = BitVec.ofNat 32 n) (hedi : s.gpr .edi = aSc s₀) (hesp : s.gpr .esp = aE s₀)
    (hrd : s.rd = s₀.rd) (hwr : s.wr = s₀.wr) (hn : 16 * n < 2 ^ 32)
    (hdc : (⟨Dd.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨(aSt s₀).setWidth 64 + BitVec.ofNat 64 272, 16⟩)
    (hds : (⟨Dd.setWidth 64, 16 * n⟩ : Region).Disjoint ⟨(aSc s₀).setWidth 64, 2176⟩)
    (hstk : (below (aE s₀) 56).Disjoint ⟨Dd.setWidth 64, 16 * n⟩) (hfD : Dd.toNat + 16 * n ≤ 2 ^ 32)
    (hcov : ∃ r' ∈ s₀.rd ++ s₀.wr, ∃ off, Dd.setWidth 64 = r'.base + BitVec.ofNat 64 off ∧ off + 16 * n ≤ r'.len) :
    UArgs s (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) Dd (aSc s₀) (aR s₀) n := by
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fS : (aSc s₀).toNat + 2304 ≤ 2 ^ 32 := hp.fS
  have p272 : (aSt s₀ + BitVec.ofNat 32 272).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 272 :=
    add_setWidth (by omega)
  have c272 : Region.Sub ⟨(aSt s₀ + BitVec.ofNat 32 272).setWidth 64, 16⟩ (astR s₀) := by
    rw [p272]; exact Offset.sub_base _ (by decide)
  exact
  { eax := heax, ecx := hecx, edx := hedx, ebx := hebx, esi := hesi, edi := hedi, rounds := hp.rounds, hn := hn
    esp := by rw [hesp]; exact hp.esp56
    wc := by rw [p272]; exact Offset.base_disjoint _ (by decide) (by omega)
    ws := (hp.st_s.sub_left (Region.sub_prefix (by decide))).sub_right (Region.sub_prefix (by decide))
    dc := by rw [p272]; exact hdc
    ds := hds
    cs := (hp.st_s.sub_left c272).sub_right (Region.sub_prefix (by decide))
    bW := by rw [hesp]; exact hp.b_st.sub_right (Region.sub_prefix (by decide))
    bD := by rw [hesp]; exact hstk
    bC := by rw [hesp]; exact hp.b_st.sub_right c272
    bS := by rw [hesp]; exact hp.b_s.sub_right (Region.sub_prefix (by decide))
    fW := by omega
    fC := by rw [add_toNat (by omega)]; omega
    fD := hfD
    fS := by omega
    reads := by
      rw [hrd, hwr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨astR s₀, by simp [hp.wr], 0, by simp, by simp⟩
      · exact hcov
    writes := by
      rw [hwr, hp.wr]
      refine Covers.of_sub fun r hr => ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨astR s₀, by simp, 272, p272, by simp⟩
      · exact ⟨ascR s₀, by simp, 0, by simp, by simp⟩ }

/-- What `chain1` leaves. -/
structure Chained₁ (s₀ s s' : State) : Prop where
  args : UArgs s' (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) (aSt s₀ + BitVec.ofNat 32 288) (aSc s₀) (aR s₀)
    (b1Of (aC s₀) (aL s₀))
  ctx : ACtx s₀ s'
  ebp : s'.gpr .ebp = s.gpr .ebp
  mem : s'.mem = s.mem

theorem chain1_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))) : WP isa chain1 s (Chained₁ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  unfold chain1
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_sub fun s₃ u₃ z₃ => WP.block_nil ?_)
  have c₃ := c₂.upd u₃ (by decide)
  have z : s₃.zf = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
    rw [z₃, u₂.gpr, u₂.other _ (by decide), u₁.other _ (by decide), hbp, arg_ofNat s₀ 5, sub_ofNat hfL,
      ofNat_beq_zero (by omega)]; rfl
  have ebp₃ : s₃.gpr .ebp = s.gpr .ebp := by
    rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₄ : State) => ACtx s₀ s₄ ∧ s₄.mem = s.mem ∧ s₄.gpr .ebp = s.gpr .ebp ∧
      s₄.gpr .esi = BitVec.ofNat 32 (b1Of (aC s₀) (aL s₀))) ?_ fun s₄ h₄ => ?_)
  · have ev : isa.eval .e s₃ = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
      show VG.X86.eval .e s₃ = _; rw [eval_e, z]
    by_cases h0 : leftOf (aC s₀) (aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₃, m₃, ebp₃, by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; simp only [b1Of, h0, ↓reduceIte]; rfl⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => wp_movi fun s₄ u₄ => WP.block_nil ?_
      exact ⟨c₃.upd u₄ (by decide), by rw [u₄.mem, m₃], by rw [u₄.other _ (by decide), ebp₃],
        by rw [u₄.gpr]; simp only [b1Of, h0, ↓reduceIte]; rfl⟩
  · obtain ⟨c₄, m₄, ebp₄, esi₄⟩ := h₄
    refine c₄.wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ => c₅.wp_arg hp (by decide) (by decide) fun s₆ u₆ c₆ =>
      wp_mov fun s₇ u₇ => wp_addi fun s₈ u₈ => wp_mov fun s₉ u₉ => wp_addi fun s₁₀ u₁₀ =>
      ((((c₆.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀ (by decide)).wp_arg hp
        (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => WP.block_nil ?_
    have eax₁₁ : s₁₁.gpr .eax = aSt s₀ := by
      rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]
    have hb1 : 16 * b1Of (aC s₀) (aL s₀) ≤ 16 := by unfold b1Of; split <;> omega
    have p288 : (aSt s₀ + BitVec.ofNat 32 288).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 288 :=
      add_setWidth (by omega)
    have c288 : Region.Sub ⟨(aSt s₀ + BitVec.ofNat 32 288).setWidth 64, 16 * b1Of (aC s₀) (aL s₀)⟩ (astR s₀) := by
      rw [p288]; exact Offset.sub_base _ (by omega)
    refine ⟨hp.uargs eax₁₁ ?_ ?_ ?_ ?_ u₁₁.gpr c₁₁.esp c₁₁.rd c₁₁.wr (by omega) ?_
      ((hp.st_s.sub_left c288).sub_right (Region.sub_prefix (by decide))) (hp.b_st.sub_right c288)
      (by rw [add_toNat (by omega)]; omega) ⟨astR s₀, by simp [hp.wr], 288, p288, by simp; omega⟩,
      c₁₁, ?_, ?_⟩
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.gpr]; exact arg_ofNat s₀ 1
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr,
        u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.gpr, u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
        u₆.other _ (by decide), u₅.gpr]; rfl
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), esi₄]
    · rw [p288]; exact Offset.disjoint _ (by omega) (by omega) (by omega)
    · rw [u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
        u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), ebp₄]
    · rw [u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, u₅.mem, m₄]

/-! ## `chain2`: the arguments of the second call -/

/-- The data the second call reads: the data left, or, with none left, the
bytes held back (none of which it reads). -/
def d2Of (s₀ : State) : BitVec 32 :=
  if leftOf (aC s₀) (aL s₀) = 0 then aSt s₀ + BitVec.ofNat 32 288 else aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))

/-- What `chain2` leaves. -/
structure Chained₂ (s₀ s s' : State) : Prop where
  args : UArgs s' (aSt s₀) (aSt s₀ + BitVec.ofNat 32 272) (d2Of s₀) (aSc s₀) (aR s₀) (nbOf (aC s₀) (aL s₀))
  ctx : ACtx s₀ s'
  ebp : s'.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))
  mem : s'.mem = s.mem

theorem chain2_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀))) : WP isa chain2 s (Chained₂ s₀ s) := by
  have hL := hp.lt
  have ⟨hfL, _⟩ := f_le (aC s₀) (aL s₀)
  have hsum := nb_le (aC s₀) (aL s₀)
  have fSt : (aSt s₀).toNat + 304 ≤ 2 ^ 32 := hp.fSt
  have fD : (aD s₀).toNat + aL s₀ ≤ 2 ^ 32 := hp.fD
  unfold chain2
  refine WP.seq (wp_movi fun s₁ u₁ => (h.upd u₁ (by decide)).wp_arg hp (by decide) (by decide) fun s₂ u₂ c₂ =>
    wp_addi fun s₃ u₃ => (c₂.upd u₃ (by decide)).wp_arg hp (by decide) (by decide) fun s₄ u₄ c₄ =>
    wp_sub fun s₅ u₅ z₅ => WP.block_nil ?_)
  have c₅ := c₄.upd u₅ (by decide)
  have ebp₄ : s₄.gpr .ebp = s.gpr .ebp := by
    rw [u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.other _ (by decide)]
  have ebp₅ : s₅.gpr .ebp = s.gpr .ebp := by rw [u₅.other _ (by decide), ebp₄]
  have edx₅ : s₅.gpr .edx = BitVec.ofNat 32 (leftOf (aC s₀) (aL s₀)) := by
    rw [u₅.gpr, u₄.gpr, ebp₄, hbp, arg_ofNat s₀ 5, sub_ofNat hfL]; rfl
  have z : s₅.zf = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
    rw [z₅, u₄.gpr, u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide),
      u₁.other _ (by decide), hbp, arg_ofNat s₀ 5, sub_ofNat hfL, ofNat_beq_zero (by omega)]; rfl
  have ecx₅ : s₅.gpr .ecx = BitVec.ofNat 32 0 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]; rfl
  have ebx₅ : s₅.gpr .ebx = aSt s₀ + BitVec.ofNat 32 288 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr, u₂.gpr]; rfl
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  refine WP.seq (WP.mono (Q := fun (s₆ : State) => ACtx s₀ s₆ ∧ s₆.mem = s.mem ∧ s₆.gpr .ebp = s.gpr .ebp ∧
      s₆.gpr .ecx = BitVec.ofNat 32 (16 * nbOf (aC s₀) (aL s₀)) ∧ s₆.gpr .ebx = d2Of s₀) ?_ fun s₆ h₆ => ?_)
  · have ev : isa.eval .e s₅ = some (decide (leftOf (aC s₀) (aL s₀) = 0)) := by
      show VG.X86.eval .e s₅ = _; rw [eval_e, z]
    by_cases h0 : leftOf (aC s₀) (aL s₀) = 0
    · refine WP.ite true (by rw [ev]; simp [h0]) (fun _ => WP.block_nil ?_) (fun h => by cases h)
      exact ⟨c₅, m₅, ebp₅, by rw [ecx₅]; simp only [nbOf, h0, ↓reduceIte],
        by rw [ebx₅]; simp only [d2Of, h0, ↓reduceIte]⟩
    · refine WP.ite false (by rw [ev]; simp [h0]) (fun h => by cases h) fun _ => ?_
      refine wp_mov fun s₆ u₆ => wp_subi fun s₇ u₇ _ => wp_mov fun s₈ u₈ => wp_andi fun s₉ u₉ => wp_sub fun s₁₀ u₁₀ _ =>
        (((((c₅.upd u₆ (by decide)).upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).upd u₁₀
          (by decide)).wp_arg hp (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => wp_add fun s₁₂ u₁₂ => WP.block_nil ?_
      refine ⟨c₁₁.upd u₁₂ (by decide), ?_, ?_, ?_, ?_⟩
      · rw [u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem, m₅]
      · rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅]
      · have ecx₇ : s₇.gpr .ecx = BitVec.ofNat 32 (leftOf (aC s₀) (aL s₀)) - 1 := by rw [u₇.gpr, u₆.gpr, edx₅]
        have ecx₉ : s₉.gpr .ecx = s₇.gpr .ecx := by rw [u₉.other _ (by decide), u₈.other _ (by decide)]
        have eax₉ : s₉.gpr .eax = s₇.gpr .ecx &&& 15 := by rw [u₉.gpr, u₈.gpr]
        rw [u₁₂.other _ (by decide), u₁₁.other _ (by decide), u₁₀.gpr, ecx₉, eax₉, ecx₇]
        simp only [nbOf, h0, ↓reduceIte]
        exact nb16_bv (by omega) (by unfold leftOf; omega)
      · rw [u₁₂.gpr, u₁₁.gpr, u₁₁.other _ (by decide), u₁₀.other _ (by decide), u₉.other _ (by decide),
          u₈.other _ (by decide), u₇.other _ (by decide), u₆.other _ (by decide), ebp₅, hbp]
        simp only [d2Of, h0, ↓reduceIte]
  · obtain ⟨c₆, m₆, ebp₆, ecx₆, ebx₆⟩ := h₆
    have hn16 : 16 * nbOf (aC s₀) (aL s₀) < 2 ^ 32 := by omega
    refine wp_mov fun s₇ u₇ => wp_shr (by decide) fun s₈ u₈ => wp_add fun s₉ u₉ =>
      (((c₆.upd u₇ (by decide)).upd u₈ (by decide)).upd u₉ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₀ u₁₀ c₁₀ => c₁₀.wp_arg hp (by decide) (by decide) fun s₁₁ u₁₁ c₁₁ => wp_mov fun s₁₂ u₁₂ =>
        wp_addi fun s₁₃ u₁₃ => ((c₁₁.upd u₁₂ (by decide)).upd u₁₃ (by decide)).wp_arg hp (by decide) (by decide)
        fun s₁₄ u₁₄ c₁₄ => WP.block_nil ?_
    have ebx₁₄ : s₁₄.gpr .ebx = d2Of s₀ := by
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide), ebx₆]
    have hnb : nbOf (aC s₀) (aL s₀) = 0 ∨ 0 < leftOf (aC s₀) (aL s₀) := by
      unfold nbOf; split <;> omega
    -- The data the call reads.
    have hn0 : leftOf (aC s₀) (aL s₀) = 0 → nbOf (aC s₀) (aL s₀) = 0 := fun h => by simp [nbOf, h]
    have hd2 : ((d2Of s₀).setWidth 64 = (aSt s₀).setWidth 64 + BitVec.ofNat 64 288 ∧ nbOf (aC s₀) (aL s₀) = 0) ∨
        ((d2Of s₀).setWidth 64 = (aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)) ∧
          0 < leftOf (aC s₀) (aL s₀)) := by
      unfold d2Of
      split
      · exact .inl ⟨add_setWidth (by omega), hn0 (by assumption)⟩
      · exact .inr ⟨add_setWidth (by unfold leftOf at *; omega), by omega⟩
    have dD : 0 < leftOf (aC s₀) (aL s₀) →
        Region.Sub ⟨(aD s₀).setWidth 64 + BitVec.ofNat 64 (fOf (aC s₀) (aL s₀)), 16 * nbOf (aC s₀) (aL s₀)⟩
          (adR s₀) := fun _ => Offset.sub_base _ (by omega)
    refine ⟨hp.uargs ?_ ?_ ?_ ebx₁₄ ?_ u₁₄.gpr c₁₄.esp c₁₄.rd c₁₄.wr hn16 ?_ ?_ ?_ ?_ ?_, c₁₄, ?_, ?_⟩
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.gpr]
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.gpr]
      exact arg_ofNat s₀ 1
    · rw [u₁₄.other _ (by decide), u₁₃.gpr, u₁₂.gpr, u₁₁.other _ (by decide), u₁₀.gpr]; rfl
    · rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.gpr, ecx₆]
      exact shr4 hn16
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact Offset.disjoint _ (by omega) (by omega) (by omega)
      · exact (hp.st_d.sub_left (Offset.sub_base _ (by decide))).symm.sub_left (dD hl)
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact (hp.st_s.sub_left (Offset.sub_base _ (by omega))).sub_right (Region.sub_prefix (by decide))
      · exact (hp.d_s.sub_left (dD hl)).sub_right (Region.sub_prefix (by decide))
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact hp.b_st.sub_right (Offset.sub_base _ (by omega))
      · exact hp.b_d.sub_right (dD hl)
    · unfold d2Of
      split
      · rw [add_toNat (by omega)]; omega
      · rw [add_toNat (by unfold leftOf at *; omega)]; omega
    · rcases hd2 with ⟨e, hn⟩ | ⟨e, hl⟩ <;> rw [e]
      · exact ⟨astR s₀, by simp [hp.wr], 288, rfl, by simp; omega⟩
      · exact ⟨adR s₀, by simp [hp.rd], fOf (aC s₀) (aL s₀), rfl, by simp; omega⟩
    · have ebp₈ : s₈.gpr .ebp = s.gpr .ebp := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ebp₆]
      have ecx₈ : s₈.gpr .ecx = BitVec.ofNat 32 (16 * nbOf (aC s₀) (aL s₀)) := by
        rw [u₈.other _ (by decide), u₇.other _ (by decide), ecx₆]
      rw [u₁₄.other _ (by decide), u₁₃.other _ (by decide), u₁₂.other _ (by decide), u₁₁.other _ (by decide),
        u₁₀.other _ (by decide), u₉.gpr, ebp₈, ecx₈, hbp]
      exact (BitVec.ofNat_add _ _).symm
    · rw [u₁₄.mem, u₁₃.mem, u₁₂.mem, u₁₁.mem, u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, m₆]

/-! ## `rest`: the arguments of the last copy -/

/-- What `rest` leaves. -/
structure Rested (s₀ s s' : State) : Prop where
  ctx : ACtx s₀ s'
  mem : s'.mem = s.mem
  esi : s'.gpr .esi = aD s₀ + BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))
  edi : s'.gpr .edi = aSt s₀ + BitVec.ofNat 32 288
  ecx : s'.gpr .ecx = BitVec.ofNat 32 (restOf (aC s₀) (aL s₀))

theorem rest_wp {s₀ s : State} (hp : APre s₀) (h : ACtx s₀ s)
    (hbp : s.gpr .ebp = BitVec.ofNat 32 (fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀))) :
    WP isa (.block rest) s (Rested s₀ s) := by
  have hsum := nb_le (aC s₀) (aL s₀)
  have hsum' : fOf (aC s₀) (aL s₀) + 16 * nbOf (aC s₀) (aL s₀) + restOf (aC s₀) (aL s₀) = (arg s₀ 5).toNat := hsum
  unfold rest
  refine h.wp_arg hp (by decide) (by decide) fun s₁ u₁ c₁ => wp_add fun s₂ u₂ =>
    (c₁.upd u₂ (by decide)).wp_arg hp (by decide) (by decide) fun s₃ u₃ c₃ => wp_addi fun s₄ u₄ =>
    (c₃.upd u₄ (by decide)).wp_arg hp (by decide) (by decide) fun s₅ u₅ c₅ => wp_sub fun s₆ u₆ _ => WP.block_nil ?_
  refine ⟨c₅.upd u₆ (by decide), by rw [u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem], ?_, ?_, ?_⟩
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr,
      u₁.gpr, u₁.other _ (by decide), hbp]
  · rw [u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr]; rfl
  · rw [u₆.gpr, u₅.gpr, u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide),
      u₂.other _ (by decide), u₁.other _ (by decide), hbp, arg_ofNat s₀ 5, sub_ofNat (by omega)]
    congr 1; unfold restOf leftOf; omega

end VG.Proof.CmacAes.Stream.X86
