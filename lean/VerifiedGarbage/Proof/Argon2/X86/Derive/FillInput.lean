import VerifiedGarbage.Proof.Argon2.X86.Derive.FillDep
import VerifiedGarbage.Proof.Argon2.AddressInput

/-!
# Argon2 on x86 (32-bit): the input of the address block

`clearAt_ok`: `clearAt d` zeroes `scratch[d, d + 1024)`. `aheader_ok`: the
seven words of the address-generation input block (§3.4.1.2), at
`scratch + 5120`. `input_ok`: after both, the block there is
`addressInput`, and the one at `scratch + 7168` is zero.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff)

/-- Words of `scratch`. -/
abbrev sw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (scrP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem scr_addr' {o : Nat} (ho : o < 16384) : addr (scrP s₀) o = scrB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.scr_fits; omega)

/-- A word of `scratch` after a store to another, or the same. -/
theorem sw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ 16384) (hb : b + 4 ≤ 16384)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    sw s₀ (m.writeW (addr (scrP s₀) a) v) b = if a = b then v else sw s₀ m b := by
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, sw, sw, scr_addr' hp (by omega), scr_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- `n` stores of `eax = 0` to `[edx + 4k]`, with `edx = scratch + d`. -/
theorem zeros_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384)
    (hx : s.gpr .edx = scrP s₀ + BitVec.ofNat 32 d) (ha : s.gpr .eax = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.store (at_ .edx (4 * k)) .eax)) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem ∧
      ∀ i < n, sw s₀ t.mem (d + 4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((zeros_ok h hd hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : addr (t.gpr .edx) (4 * n) = scrB s₀ + BitVec.ofNat 64 (d + 4 * n) := by
      rw [gt, hx, addr_shift, scr_addr' hp (by omega)]
    have hc : (scrR s₀).Contains (addr (t.gpr .edx) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region).Contains (addr (t.gpr .edx) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains _ (by omega) (by omega) (by omega)
    refine Wp.wp_stm rfl ⟨_, by rw [it.wr]; exact scr_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := scrR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, hx, addr_shift, sw_store hp _ (by omega) (by omega) (by omega), ha]
      by_cases e : d + 4 * n = d + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e]; exact wt i (by omega)

/-- `clearAt d`: zero `scratch[d, d + 1024)`. -/
theorem clearAt_ok {s : State} (h : Inv s₀ s) {d : Nat} (hd : d + 1024 ≤ 16384) {is : List Instr}
    {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) →
      Frame [⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩] s.mem t.mem → (∀ i < 256, sw s₀ t.mem (d + 4 * i) = 0) →
      WP isa (.block is) t Q) :
    WP isa (.block (Impl.Argon2.X86.Derive.clearAt d ++ is)) s Q := by
  unfold Impl.Argon2.X86.Derive.clearAt Impl.Argon2.X86.Derive.scratchAt
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => wp_addi fun s₂ u₂ => wp_movi fun s₃ u₃ => ?_
  have i₃ := ((h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  refine WP.block_append ((zeros_ok hp i₃ hd (by rw [u₃.other _ (by decide), u₂.gpr, u₁.gpr]) u₃.gpr 256
    (Nat.le_refl _)).mono fun t ⟨it, gt, ft, wt⟩ => k t it (fun r a b => ?_) ?_ wt)
  · rw [gt, u₃.other _ a, u₂.other _ b, u₁.other _ b]
  · rw [show s.mem = s₃.mem by rw [u₃.mem, u₂.mem, u₁.mem]]; exact ft

end


/-- The seven words of the address-generation input block. -/
def hdr (s₀ : State) (pass lane slice c : Nat) : Nat → BitVec 32
  | 0 => BitVec.ofNat 32 pass
  | 1 => BitVec.ofNat 32 lane
  | 2 => BitVec.ofNat 32 slice
  | 3 => arg s₀ 14
  | 4 => arg s₀ 5
  | 5 => arg s₀ 0
  | _ => BitVec.ofNat 32 c

/-- The words of the input block after its first `n` words are written over `m`'s. -/
def HW (s₀ : State) (m : Mem) (pass lane slice c n : Nat) (m' : Mem) : Prop :=
  ∀ i < 256, sw s₀ m' (5120 + 4 * i) =
    if i % 2 = 0 ∧ i < 2 * n then hdr s₀ pass lane slice c (i / 2) else sw s₀ m (5120 + 4 * i)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One word of the header. -/
theorem hdr_step {m : Mem} {pass lane slice c n : Nat} (hn : n < 7) {u : State} (h : Inv s₀ u)
    (hx : u.gpr .edx = scrP s₀) (ha : u.gpr .eax = hdr s₀ pass lane slice c n)
    (hw : HW s₀ m pass lane slice c n u.mem) {is : List Instr} {Q : State → Prop}
    (k : ∀ t, Inv s₀ t → t.gpr = u.gpr → Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] u.mem t.mem →
      HW s₀ m pass lane slice c (n + 1) t.mem → WP isa (.block is) t Q) :
    WP isa (.block (.store (at_ .edx (5120 + 8 * n)) .eax :: is)) u Q := by
  have hs := hp.scr_fits
  have ea : addr (u.gpr .edx) (5120 + 8 * n) = scrB s₀ + BitVec.ofNat 64 (5120 + 8 * n) := by
    rw [hx, scr_addr' hp (by omega)]
  have hc : (scrR s₀).Contains (addr (u.gpr .edx) (5120 + 8 * n)) 4 := by
    rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
  have hc' : (⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region).Contains (addr (u.gpr .edx) (5120 + 8 * n)) 4 := by
    rw [ea]; exact Offset.contains _ (by omega) (by omega) (by omega)
  refine Wp.wp_stm rfl ⟨_, by rw [h.wr]; exact scr_mem hp, hc⟩ fun t u₁ =>
    k t (h.store (R := scrR s₀) (by simp) hc u₁) u₁.gpr ?_ fun i hi => ?_
  · rw [u₁.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ hc'
  · rw [u₁.mem, hx, sw_store hp _ (by omega) (by omega) (by omega), ha, hw i hi]
    by_cases e : 5120 + 8 * n = 5120 + 4 * i
    · rw [ite_eq_left e, ite_eq_left (by omega), show i / 2 = n by omega]
    · rw [ite_eq_right e]
      by_cases c₁ : i % 2 = 0 ∧ i < 2 * n
      · rw [ite_eq_left c₁, ite_eq_left (by omega)]
      · rw [ite_eq_right c₁, ite_eq_right (by omega)]

theorem aheader_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c) :
    WP isa (.block Impl.Argon2.X86.Derive.addressHeader) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t.mem ∧ HW s₀ s.mem pass lane slice c 7 t.mem := by
  have fsub : ∀ r ∈ [(⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ (by decide)⟩
  unfold Impl.Argon2.X86.Derive.addressHeader
  refine wp_ldarg hp h (i := 15) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.upd u₁ (by decide) (by decide)
  have w₀ : HW s₀ s.mem pass lane slice c 0 s₁.mem := fun i _ => by
    rw [ite_eq_right (by omega), u₁.mem]
  -- Word 0: the pass.
  refine wp_ldloc hp i₁ (d := passOff) (by decide) fun s₂ u₂ => ?_
  refine hdr_step hp (n := 0) (by decide) (i₁.upd u₂ (by decide) (by decide)) (by rw [u₂.other _ (by decide), u₁.gpr])
    (by rw [u₂.gpr, lw_mem u₁.mem, ps.pass]; rfl) (by rw [u₂.mem]; exact w₀) fun t₂ it₂ g₂ f₂ w₂ => ?_
  -- Word 1: the lane.
  refine wp_ldloc hp it₂ (d := laneOff) (by decide) fun s₃ u₃ => ?_
  refine hdr_step hp (n := 1) (by decide) (it₂.upd u₃ (by decide) (by decide))
    (by rw [u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₃.gpr, lw_keep hp f₂ fsub (by decide), lw_mem u₂.mem, lw_mem u₁.mem, ps.lane]; rfl)
    (by rw [u₃.mem]; exact w₂) fun t₃ it₃ g₃ f₃ w₃ => ?_
  have F₃ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₃.mem := by
    rw [← u₁.mem, ← u₂.mem]; exact f₂.trans (by rw [← u₃.mem]; exact f₃)
  -- Word 2: the slice.
  refine wp_ldloc hp it₃ (d := sliceOff) (by decide) fun s₄ u₄ => ?_
  refine hdr_step hp (n := 2) (by decide) (it₃.upd u₄ (by decide) (by decide))
    (by rw [u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₄.gpr, lw_keep hp F₃ fsub (by decide), ps.slice]; rfl)
    (by rw [u₄.mem]; exact w₃) fun t₄ it₄ g₄ f₄ w₄ => ?_
  have F₄ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₄.mem :=
    F₃.trans (by rw [← u₄.mem]; exact f₄)
  -- Words 3 to 5: the arguments.
  refine wp_ldarg hp it₄ (i := 14) (by decide) fun s₅ u₅ => ?_
  refine hdr_step hp (n := 3) (by decide) (it₄.upd u₅ (by decide) (by decide))
    (by rw [u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), u₁.gpr])
    (by rw [u₅.gpr]; rfl) (by rw [u₅.mem]; exact w₄) fun t₅ it₅ g₅ f₅ w₅ => ?_
  have F₅ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₅.mem :=
    F₄.trans (by rw [← u₅.mem]; exact f₅)
  refine wp_ldarg hp it₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  refine hdr_step hp (n := 4) (by decide) (it₅.upd u₆ (by decide) (by decide))
    (by rw [u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃,
      u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₆.gpr]; rfl) (by rw [u₆.mem]; exact w₅) fun t₆ it₆ g₆ f₆ w₆ => ?_
  have F₆ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₆.mem :=
    F₅.trans (by rw [← u₆.mem]; exact f₆)
  refine wp_ldarg hp it₆ (i := 0) (by decide) fun s₇ u₇ => ?_
  refine hdr_step hp (n := 5) (by decide) (it₆.upd u₇ (by decide) (by decide))
    (by rw [u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅, u₅.other _ (by decide), g₄,
      u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂, u₂.other _ (by decide), u₁.gpr])
    (by rw [u₇.gpr]; rfl) (by rw [u₇.mem]; exact w₆) fun t₇ it₇ g₇ f₇ w₇ => ?_
  have F₇ : Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩] s.mem t₇.mem :=
    F₆.trans (by rw [← u₇.mem]; exact f₇)
  -- Word 6: the counter.
  refine wp_ldloc hp it₇ (d := counterOff) (by decide) fun s₈ u₈ => ?_
  refine hdr_step hp (n := 6) (by decide) (it₇.upd u₈ (by decide) (by decide))
    (by rw [u₈.other _ (by decide), g₇, u₇.other _ (by decide), g₆, u₆.other _ (by decide), g₅,
      u₅.other _ (by decide), g₄, u₄.other _ (by decide), g₃, u₃.other _ (by decide), g₂,
      u₂.other _ (by decide), u₁.gpr])
    (by rw [u₈.gpr, lw_keep hp F₇ fsub (by decide), hc]; rfl)
    (by rw [u₈.mem]; exact w₇) fun t it g f w => WP.block_nil ⟨it, fun r a b => ?_,
      F₇.trans (by rw [← u₈.mem]; exact f), w⟩
  rw [g, u₈.other _ a, g₇, u₇.other _ a, g₆, u₆.other _ a, g₅, u₅.other _ a, g₄, u₄.other _ a, g₃,
    u₃.other _ a, g₂, u₂.other _ a, u₁.other _ b]

end

theorem zero_append32 (x : BitVec 32) : 0#32 ++ x = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append, BitVec.toNat_ofNat]
  simp
  have := x.isLt
  omega

/-- The input block's words. -/
def inWord (s₀ : State) (pass lane slice c : Nat) (i : Nat) : BitVec 32 :=
  if i % 2 = 0 ∧ i < 14 then hdr s₀ pass lane slice c (i / 2) else 0

theorem input_words {s₀ : State} (hp : DPre s₀) {pass lane slice c : Nat} (h₁ : pass < 2 ^ 32)
    (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    ofWords (inWord s₀ pass lane slice c) = Proof.Argon2.addressInput (prm s₀) pass lane slice c := by
  have eb : (arg s₀ 14).toNat = (prm s₀).blocks := hp.blocks
  have ep : (arg s₀ 5).toNat = (prm s₀).passes := rfl
  have ek : (arg s₀ 0).toNat = (prm s₀).variant.code := (variant_code hp.kind_le).symm
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, Proof.Argon2.addressInput, Vector.getElem_set, zeroBlock,
    Vector.getElem_replicate, inWord]
  rw [ite_eq_right (by omega)]
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ 7 ≤ j) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | hj7
  · simp [hdr]; rw [zero_append32, Wp.toNat_ofNat_lt h₁]
  · simp [hdr]; rw [zero_append32, Wp.toNat_ofNat_lt h₂]
  · simp [hdr]; rw [zero_append32, Wp.toNat_ofNat_lt h₃]
  · simp [hdr]; rw [zero_append32, eb]
  · simp [hdr]; rw [zero_append32, ep]
  · simp [hdr]; rw [zero_append32, ek]
  · simp [hdr]; rw [zero_append32, Wp.toNat_ofNat_lt h₄]
  · rw [ite_eq_right (by omega)]
    simp (disch := omega) only [ite_eq_right]
    rfl

theorem ofWords_zero : ofWords (fun _ => 0) = zeroBlock := by
  apply Vector.ext
  intro j hj
  simp only [ofWords, Vector.getElem_ofFn, zeroBlock, Vector.getElem_replicate]
  rfl

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- A word of `scratch` outside a frame's region of `scratch`. -/
theorem sw_frame {m m' : Mem} {a n : Nat} (f : Frame [⟨scrB s₀ + BitVec.ofNat 64 a, n⟩] m m') {o : Nat}
    (h : o + 4 ≤ a ∨ a + n ≤ o) (ho : o + 4 ≤ 16384) (hn : a + n ≤ 16384) : sw s₀ m' o = sw s₀ m o := by
  rw [sw, sw, scr_addr' hp (by omega)]
  refine f.readW (r := ⟨scrB s₀ + BitVec.ofNat 64 o, 4⟩) (Region.contains_self _ _) (fun r hr => ?_) (by decide)
  simp only [List.mem_singleton] at hr; subst hr
  exact Offset.disjoint _ h (by omega) (by omega)

/-- The address-generation input block at `scratch + 5120`, and a zero block at `scratch + 7168`. -/
theorem input_ok {s : State} (h : Inv s₀ s) {pass slice lane index c : Nat}
    (ps : Pos s₀ s pass slice lane index) (hc : lw s₀ s counterOff = BitVec.ofNat 32 c)
    (h₁ : pass < 2 ^ 32) (h₂ : lane < 2 ^ 32) (h₃ : slice < 2 ^ 32) (h₄ : c < 2 ^ 32) :
    WP isa (.block (Impl.Argon2.X86.Derive.clearAt 5120 ++ (Impl.Argon2.X86.Derive.clearAt 7168 ++
      Impl.Argon2.X86.Derive.addressHeader))) s fun t => Inv s₀ t ∧
      (∀ r, r ≠ .eax → r ≠ .edx → t.gpr r = s.gpr r) ∧
      Frame [⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, ⟨scrB s₀ + BitVec.ofNat 64 7168, 1024⟩] s.mem t.mem ∧
      blk t.mem (scrP s₀) 5120 = Proof.Argon2.addressInput (prm s₀) pass lane slice c ∧
      blk t.mem (scrP s₀) 7168 = zeroBlock := by
  have fsub : ∀ d, d + 1024 ≤ 16384 → ∀ r ∈ [(⟨scrB s₀ + BitVec.ofNat 64 d, 1024⟩ : Region)],
      ∃ r' ∈ [memR s₀, scrR s₀, outR s₀, callR s₀], Region.Sub r r' := fun d hd r hr => by
    simp only [List.mem_singleton] at hr; subst hr
    exact ⟨scrR s₀, by simp, Offset.sub_base _ hd⟩
  refine clearAt_ok hp h (d := 5120) (by decide) fun t₁ i₁ g₁ f₁ z₁ => ?_
  refine clearAt_ok hp i₁ (d := 7168) (by decide) fun t₂ i₂ g₂ f₂ z₂ => ?_
  have L : ∀ d, d + 4 ≤ 144 → lw s₀ t₂ d = lw s₀ s d := fun d hd => by
    rw [lw_keep hp f₂ (fsub _ (by decide)) hd, lw_keep hp f₁ (fsub _ (by decide)) hd]
  refine (aheader_ok hp i₂ (pass := pass) (slice := slice) (lane := lane) (index := index) (c := c)
    (ps.of_lw fun d hd => L d (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl | rfl <;> decide)) (by rw [L _ (by decide)]; exact hc)).mono
    fun t ⟨it, gt, ft, wt⟩ => ⟨it, fun r a b => by rw [gt r a b, g₂ r a b, g₁ r a b], ?_, ?_, ?_⟩
  · refine (Frame.trans (f₁.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inl hr, fun _ h => h⟩)
      (f₂.sub fun r hr => ⟨r, by simp at hr ⊢; exact .inr hr, fun _ h => h⟩)).trans
      (ft.sub fun r hr => ⟨⟨scrB s₀ + BitVec.ofNat 64 5120, 1024⟩, by simp, by
        simp only [List.mem_singleton] at hr; subst hr; exact fun _ h => h⟩)
  · rw [blk_of_words (f := inWord s₀ pass lane slice c) fun i hi => ?_, input_words hp h₁ h₂ h₃ h₄]
    have w := wt i hi
    simp only [sw] at w
    rw [w, inWord]
    by_cases e : i % 2 = 0 ∧ i < 2 * 7
    · rw [ite_eq_left e, ite_eq_left (by omega)]
    · rw [ite_eq_right e, ite_eq_right (by omega), ← sw, sw_frame hp f₂ (by omega) (by omega) (by decide)]
      exact z₁ i hi
  · rw [blk_of_words (f := fun _ => 0) fun i hi => ?_, ofWords_zero]
    rw [← sw, sw_frame hp ft (by omega) (by omega) (by decide)]
    exact z₂ i hi

end
end VG.Proof.Argon2.X86.Derive
