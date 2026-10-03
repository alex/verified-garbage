import VerifiedGarbage.Proof.Rc4.X86.Lookup

/-! # RC4 on x86 (32-bit): replacing a secret-indexed byte of the table -/

namespace VG.Proof.Rc4.X86
open VG VG.X86 VG.Impl.Rc4.X86 VG.Proof.Rc4
open VG.Proof.MlDsa.X86.Pack (Keep WP.keep writesOnly addr_of_fit)

/-! ## Moving the difference to the byte's lane -/

/-- The difference `c`, once lanes `3, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 32 :=
  if jj ≤ L then (c.setWidth 32) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 32) : (0 : BitVec 32) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 32) : x ||| (0 : BitVec 32) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 32) : (0 : BitVec 32) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 32).rotateRight 24 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 4) :
    (spread c L (j + 1)).rotateRight 24 ||| (if L = j then c.setWidth 32 else 0) =
      spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte32 c (by omega), ite_eq_right (show ¬ L = j by omega),
      or_zero', ite_eq_left (show j ≤ L by omega), show L - (j + 1) + 1 = L - j by omega]
  · rw [ite_eq_right h1, rot_zero, zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 4)
    (hbp : s.gpr .ebp = idx.setWidth 32) (hax : s.gpr .eax = c.setWidth 32)
    (hcx : s.gpr .ecx = spread c (idx.toNat % 4) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .ecx = spread c (idx.toNat % 4) j ∧ t.gpr .eax = s.gpr .eax ∧
      t.gpr .ebp = s.gpr .ebp ∧ t.mem = s.mem := by
  unfold spreadStep laneMask
  rrun [hbp, hax, hcx]
  rw [lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (hbp : s₀.gpr .ebp = idx.setWidth 32)
    (hax : s₀.gpr .eax = c.setWidth 32) :
    ∀ n ≤ 4, ∀ s, s.gpr .ecx = spread c (idx.toNat % 4) n → s.gpr .eax = s₀.gpr .eax →
      s.gpr .ebp = s₀.gpr .ebp → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .ecx = spread c (idx.toNat % 4) 0 ∧ t.gpr .eax = s₀.gpr .eax ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s hcx hax' _ hm; exact WP.block_nil ⟨hcx, hax', hm⟩
  | succ n ih =>
    intro s hcx hax' hbp' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega) (hbp'.trans hbp) (hax'.trans hax) hcx)
      fun t ⟨tcx, tax, tbp, tm⟩ => ?_
    exact ih (by omega) t tcx (tax.trans hax') (tbp.trans hbp') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 4).reverse := rfl

/-! ## Storing back every doubleword -/

/-- The memory once doublewords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) : Mem :=
  if n / 4 < k then
    m.writeW (p + BitVec.ofNat 64 (4 * (n / 4)))
      (m.readW (p + BitVec.ofNat 64 (4 * (n / 4))) 32 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 32) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (4 * k))
      ((if n / 4 = k then d else 0) ^^^
        (scatter m p n d k).readW (p + BitVec.ofNat 64 (4 * k)) 32) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 4 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 4 = k by omega), zero_xor', writeW_readW32,
      ite_eq_left (show n / 4 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 4 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 4 < k + 1 by omega), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, zero_xor', writeW_readW32,
        ite_eq_right (show ¬ n / 4 < k + 1 by omega)]

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 64)
    (hbp : s.gpr .ebp = idx.setWidth 32)
    (hw : InRegions s.wr (addr (s.gpr .edi) (4 * k)) 4) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (addr (s.gpr .edi) (4 * k))
        ((if idx.toNat / 4 = k then s.gpr .ecx else 0) ^^^
          s.mem.readW (addr (s.gpr .edi) (4 * k)) 32) ∧
      t.gpr .ecx = s.gpr .ecx ∧ t.gpr .ebp = s.gpr .ebp ∧ t.gpr .edi = s.gpr .edi ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (4 * k)) 4 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask
  rrun [hbp, hr, hw]
  rw [row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 32)
    (hbp : s₀.gpr .ebp = idx.setWidth 32) (hfit : (s₀.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s₀.wr ((s₀.gpr .edi).setWidth 64) 256) :
    ∀ n ≤ 64, ∀ s, s.gpr .ecx = d → s.gpr .ebp = s₀.gpr .ebp → s.gpr .edi = s₀.gpr .edi →
      s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem ((s₀.gpr .edi).setWidth 64) idx.toNat d n ∧ t.gpr .ecx = d ∧
        t.gpr .ebp = s₀.gpr .ebp ∧ t.gpr .edi = s₀.gpr .edi ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s hcx hbp' hdi hwr hm
    refine WP.block_nil ⟨?_, hcx, hbp', hdi, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s hcx hbp' hdi hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s hcx hbp' hdi hwr hm) fun t ⟨tm, tcx, tbp, tdi, twr⟩ => ?_
    have hq : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [twr, tdi, row_addr hfit (by omega)]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hw
    refine WP.mono (scatter_step t idx (by omega) (tbp.trans hbp) hq)
      fun u ⟨um, ucx, ubp, udi, _, uwr⟩ => ?_
    refine ⟨?_, ucx.trans tcx, ubp.trans tbp, udi.trans tdi, uwr.trans twr⟩
    rw [um, tm, tcx, tdi, row_addr hfit (by omega), scatter_succ]

/-! ## The replacement -/

theorem xor_byte32 (a b : Byte) : a.setWidth 32 ^^^ b.setWidth 32 = (a ^^^ b).setWidth 32 := by
  rw [BitVec.setWidth_xor]

/-- The address `loadI` reads: byte `i` of the table at `P`. -/
theorem idx_addr {P : BitVec 32} (hP : P.toNat + 256 ≤ 2 ^ 32) (i : Byte) :
    addr (P + i.setWidth 32) 0 = P.setWidth 64 + BitVec.ofNat 64 i.toNat := by
  unfold addr
  rw [BitVec.add_zero, byte32 i]
  exact VG.Proof.MlKem.X86.ea_off (by have := i.isLt; omega)

theorem loadI_ok (s : State) (ii : Byte) (hsi : s.gpr .esi = ii.setWidth 32)
    (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block loadI) s fun t =>
      t.gpr .edx = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      Keep [.edx] s t ∧ t.mem = s.mem := by
  have hi : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi + ii.setWidth 32) 0) 1 := by
    rw [idx_addr hfit ii]
    exact region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  refine WP.mono (WP.keep (Q := fun t =>
      t.gpr .edx = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)).setWidth 32 ∧
      t.mem = s.mem) [.edx] ?_ (by decide +kernel)) fun t ⟨h, hk⟩ => ⟨h.1, hk, h.2⟩
  unfold loadI
  rw [← hsi] at hi
  rrun [hi]
  rw [hsi, idx_addr hfit ii]

theorem replace_core (s : State) (idx ii : Byte) (hbp : s.gpr .ebp = idx.setWidth 32)
    (hsi : s.gpr .esi = ii.setWidth 32) (hfit : (s.gpr .edi).toNat + 256 ≤ 2 ^ 32)
    (hw : InRegions s.wr ((s.gpr .edi).setWidth 64) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .eax = (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat)).setWidth 32 ∧
      t.mem = s.mem.write ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 idx.toNat) 1
        (s.mem ((s.gpr .edi).setWidth 64 + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) ((s.gpr .edi).setWidth 64) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  let p := (s.gpr .edi).setWidth 64
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.eax, .ecx, .edx] (lookup_core s idx hbp hfit hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have tbp : t.gpr .ebp = s.gpr .ebp := tk.gpr (by decide)
  have tdi : t.gpr .edi = s.gpr .edi := tk.gpr (by decide)
  have tsi : t.gpr .esi = s.gpr .esi := tk.gpr (by decide)
  have htr : InRegions (t.rd ++ t.wr) ((t.gpr .edi).setWidth 64) 256 := by
    rw [tk.2.1, tk.2.2, tdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok t ii (tsi.trans hsi) (by rw [tdi]; exact hfit) htr)
    fun t' ⟨t'dx, t'k, t'm⟩ => ?_
  rw [tdi, tm] at t'dx
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.alu .xor .eax (.reg .edx), .mov .ecx (imm 0)]) t' fun u =>
      u.gpr .eax = (b ^^^ v).setWidth 32 ∧ u.gpr .ecx = 0 ∧ u.gpr .ebp = s.gpr .ebp ∧
        u.gpr .edi = s.gpr .edi ∧ u.gpr .esi = s.gpr .esi ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr := by
    have t'ax : t'.gpr .eax = b.setWidth 32 := (t'k.gpr (by decide)).trans tax
    rrun [t'ax, t'dx, t'm, tm, (t'k.gpr (r := .ebp) (by decide)).trans tbp,
      (t'k.gpr (r := .edi) (by decide)).trans tdi, (t'k.gpr (r := .esi) (by decide)).trans tsi,
      t'k.2.1, t'k.2.2, tk.2.1, tk.2.2]
    rw [xor_byte32]
  refine WP.mono h1 fun u ⟨uax, ucx, ubp, udi, usi, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (ubp.trans hbp) uax 4 (by decide) u
    (by rw [ucx]; unfold spread; rw [ite_eq_right (by omega)]) rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.ecx, .edx] hsp (by decide +kernel)) fun w ⟨⟨wcx, wax, wm⟩, wk⟩ => ?_
  have wbp : w.gpr .ebp = s.gpr .ebp := (wk.gpr (by decide)).trans ubp
  have wdi : w.gpr .edi = s.gpr .edi := (wk.gpr (by decide)).trans udi
  have wsi : w.gpr .esi = s.gpr .esi := (wk.gpr (by decide)).trans usi
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  have hwr' : InRegions (w.rd ++ w.wr) ((w.gpr .edi).setWidth 64) 256 := by
    rw [wrd, wwr, wdi]; exact hr
  rw [WP.block_append_iff]
  refine WP.mono (loadI_ok w ii (wsi.trans hsi) (by rw [wdi]; exact hfit) hwr')
    fun w' ⟨w'dx, w'k, w'm⟩ => ?_
  rw [wdi, wm, um] at w'dx
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.alu .xor .eax (.reg .edx)]) w'
      fun x => x.gpr .eax = b.setWidth 32 ∧ x.gpr .ecx = w.gpr .ecx ∧ x.gpr .ebp = s.gpr .ebp ∧
        x.gpr .edi = s.gpr .edi ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    have w'ax : w'.gpr .eax = (b ^^^ v).setWidth 32 :=
      (w'k.gpr (by decide)).trans (wax.trans uax)
    rrun [w'ax, w'dx, w'm, wm, um, (w'k.gpr (r := .ecx) (by decide)),
      (w'k.gpr (r := .ebp) (by decide)).trans wbp, (w'k.gpr (r := .edi) (by decide)).trans wdi,
      w'k.2.2, wwr]
    rw [xor_byte32, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, xcx, xbp, xdi, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.edx] (scatter_steps s idx _ hbp hfit hw 64 (by decide) x rfl xbp xdi
    xwr xm) (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, xcx, wcx]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte32,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.X86
