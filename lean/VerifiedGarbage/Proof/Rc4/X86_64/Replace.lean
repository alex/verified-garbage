import VerifiedGarbage.Proof.Rc4.X86_64.Lookup

/-! # RC4 on x86-64: replacing a secret-indexed byte of the table -/

namespace VG.Proof.Rc4.X86_64
open VG VG.X86_64 VG.Impl.Rc4.X86_64 VG.Proof.Rc4
open VG.Proof.MlKem.X86_64 (Keep WP.keep writesOnly)

/-! ## Moving the difference to the byte's lane -/

/-- The difference `c`, once lanes `7, …, jj` are visited: shifted to lane `L`
by the lanes visited below it. -/
def spread (c : Byte) (L jj : Nat) : BitVec 64 :=
  if jj ≤ L then (c.setWidth 64) <<< (8 * (L - jj)) else 0

theorem zero_xor' (x : BitVec 64) : (0 : BitVec 64) ^^^ x = x := BitVec.zero_xor
theorem or_zero' (x : BitVec 64) : x ||| (0 : BitVec 64) = x := BitVec.or_zero
theorem zero_or' (x : BitVec 64) : (0 : BitVec 64) ||| x = x := BitVec.zero_or
theorem rot_zero : (0 : BitVec 64).rotateRight 56 = 0 := by decide

theorem spread_succ (c : Byte) {L j : Nat} (hL : L < 8) :
    (spread c L (j + 1)).rotateRight 56 ||| (if L = j then c.setWidth 64 else 0) =
      spread c L j := by
  unfold spread
  by_cases h1 : j + 1 ≤ L
  · rw [ite_eq_left h1, rot_byte c (by omega), ite_eq_right (show ¬ L = j by omega),
      or_zero', ite_eq_left (show j ≤ L by omega), show L - (j + 1) + 1 = L - j by omega]
  · rw [ite_eq_right h1, rot_zero, zero_or']
    by_cases h2 : L = j
    · rw [ite_eq_left h2, ite_eq_left (show j ≤ L by omega), h2, Nat.sub_self, Nat.mul_zero,
        BitVec.shiftLeft_zero]
    · rw [ite_eq_right h2, ite_eq_right (show ¬ j ≤ L by omega)]

theorem spread_step (s : State) (idx c : Byte) {j : Nat} (hj : j < 8)
    (h9 : s.gpr .r9 = idx.setWidth 64) (hax : s.gpr .rax = c.setWidth 64)
    (h11 : s.gpr .r11 = spread c (idx.toNat % 8) (j + 1)) :
    WP isa (.block (spreadStep j)) s fun t =>
      t.gpr .r11 = spread c (idx.toNat % 8) j ∧ t.gpr .rax = s.gpr .rax ∧
      t.gpr .r9 = s.gpr .r9 ∧ t.mem = s.mem := by
  unfold spreadStep laneMask
  rrun [h9, hax, h11, sx j (by omega), sx 56]
  rw [lane_mask idx hj, spread_succ c (Nat.mod_lt _ (by decide))]

theorem spread_steps (s₀ : State) (idx c : Byte) (h9 : s₀.gpr .r9 = idx.setWidth 64)
    (hax : s₀.gpr .rax = c.setWidth 64) :
    ∀ n ≤ 8, ∀ s, s.gpr .r11 = spread c (idx.toNat % 8) n → s.gpr .rax = s₀.gpr .rax →
      s.gpr .r9 = s₀.gpr .r9 → s.mem = s₀.mem →
      WP isa (.block ((List.range n).reverse.flatMap spreadStep)) s fun t =>
        t.gpr .r11 = spread c (idx.toNat % 8) 0 ∧ t.gpr .rax = s₀.gpr .rax ∧ t.mem = s₀.mem := by
  intro n hn
  induction n with
  | zero => intro s h11 hax' _ hm; exact WP.block_nil ⟨h11, hax', hm⟩
  | succ n ih =>
    intro s h11 hax' h9' hm
    rw [List.range_succ, List.reverse_append, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, WP.block_append_iff]
    refine WP.mono (spread_step s idx c (by omega) (h9'.trans h9) (hax'.trans hax) h11)
      fun t ⟨t11, tax, t9, tm⟩ => ?_
    exact ih (by omega) t t11 (tax.trans hax') (t9.trans h9') (tm.trans hm)

theorem lanesDown_eq : lanesDown = (List.range 8).reverse := rfl

/-! ## Storing back every quadword -/

/-- The memory once quadwords `0, …, k - 1` are stored back, XORed with `d`
where they hold byte `n`. -/
def scatter (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) : Mem :=
  if n / 8 < k then
    m.writeW (p + BitVec.ofNat 64 (8 * (n / 8)))
      (m.readW (p + BitVec.ofNat 64 (8 * (n / 8))) 64 ^^^ d)
  else m

theorem scatter_succ (m : Mem) (p : Addr) (n : Nat) (d : BitVec 64) (k : Nat) :
    (scatter m p n d k).writeW (p + BitVec.ofNat 64 (8 * k))
      ((if n / 8 = k then d else 0) ^^^
        (scatter m p n d k).readW (p + BitVec.ofNat 64 (8 * k)) 64) = scatter m p n d (k + 1) := by
  unfold scatter
  by_cases h0 : n / 8 < k
  · rw [ite_eq_left h0, ite_eq_right (show ¬ n / 8 = k by omega), zero_xor', writeW_readW,
      ite_eq_left (show n / 8 < k + 1 by omega)]
  · rw [ite_eq_right h0]
    by_cases h1 : n / 8 = k
    · rw [ite_eq_left h1, ite_eq_left (show n / 8 < k + 1 by omega), BitVec.xor_comm, h1]
    · rw [ite_eq_right h1, zero_xor', writeW_readW,
        ite_eq_right (show ¬ n / 8 < k + 1 by omega)]

theorem scatter_step (s : State) (idx : Byte) {k : Nat} (hk : k < 32)
    (h9 : s.gpr .r9 = idx.setWidth 64)
    (hw : InRegions s.wr (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8) :
    WP isa (.block (scatterStep k)) s fun t =>
      t.mem = s.mem.writeW (s.gpr .rdi + BitVec.ofNat 64 (8 * k))
        ((if idx.toNat / 8 = k then s.gpr .r11 else 0) ^^^
          s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64) ∧
      t.gpr .r11 = s.gpr .r11 ∧ t.gpr .r9 = s.gpr .r9 ∧ t.gpr .rdi = s.gpr .rdi ∧
      t.rd = s.rd ∧ t.wr = s.wr := by
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 8 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  unfold scatterStep rowMask
  rrun [h9, hr, hw, sx (8 * k) (by omega)]
  rw [row_mask idx hk]

theorem scatter_steps (s₀ : State) (idx : Byte) (d : BitVec 64)
    (h9 : s₀.gpr .r9 = idx.setWidth 64) (hw : InRegions s₀.wr (s₀.gpr .rdi) 256) :
    ∀ n ≤ 32, ∀ s, s.gpr .r11 = d → s.gpr .r9 = s₀.gpr .r9 → s.gpr .rdi = s₀.gpr .rdi →
      s.wr = s₀.wr → s.mem = s₀.mem →
      WP isa (.block ((List.range n).flatMap scatterStep)) s fun t =>
        t.mem = scatter s₀.mem (s₀.gpr .rdi) idx.toNat d n ∧ t.gpr .r11 = d ∧
        t.gpr .r9 = s₀.gpr .r9 ∧ t.gpr .rdi = s₀.gpr .rdi ∧ t.wr = s₀.wr := by
  intro n hn
  induction n with
  | zero =>
    intro s h11 h9' hdi hwr hm
    refine WP.block_nil ⟨?_, h11, h9', hdi, hwr⟩
    rw [hm]; unfold scatter; rw [ite_eq_right (Nat.not_lt_zero _)]
  | succ n ih =>
    intro s h11 h9' hdi hwr hm
    rw [flatMap_succ, WP.block_append_iff]
    refine WP.mono (ih (by omega) s h11 h9' hdi hwr hm) fun t ⟨tm, t11, t9, tdi, twr⟩ => ?_
    have hq : InRegions t.wr (t.gpr .rdi + BitVec.ofNat 64 (8 * n)) 8 := by
      rw [twr, tdi]
      exact region_offset _ _ _ _ _ (by omega) (by omega) hw
    refine WP.mono (scatter_step t idx (by omega) (t9.trans h9) hq)
      fun u ⟨um, u11, u9, udi, _, uwr⟩ => ?_
    refine ⟨?_, u11.trans t11, u9.trans t9, udi.trans tdi, uwr.trans twr⟩
    rw [um, tm, t11, tdi, scatter_succ]

/-! ## The replacement -/

theorem xor_byte (a b : Byte) : a.setWidth 64 ^^^ b.setWidth 64 = (a ^^^ b).setWidth 64 := by
  rw [BitVec.setWidth_xor]

theorem replace_core (s : State) (idx ii : Byte) (h9 : s.gpr .r9 = idx.setWidth 64)
    (hcx : s.gpr .rcx = ii.setWidth 64) (hw : InRegions s.wr (s.gpr .rdi) 256) :
    WP isa (.block replace) s fun t =>
      t.gpr .rax = (s.mem (s.gpr .rdi + BitVec.ofNat 64 idx.toNat)).setWidth 64 ∧
      t.mem = s.mem.write (s.gpr .rdi + BitVec.ofNat 64 idx.toNat) 1
        (s.mem (s.gpr .rdi + BitVec.ofNat 64 ii.toNat)) := by
  have hn := idx.isLt
  have hr : InRegions (s.rd ++ s.wr) (s.gpr .rdi) 256 := by
    obtain ⟨r, hr, hc⟩ := hw
    exact ⟨r, List.mem_append_right _ hr, hc⟩
  have hi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofNat 64 ii.toNat) 1 :=
    region_offset _ _ _ _ _ (by have := ii.isLt; omega) (by have := ii.isLt; omega) hr
  let p := s.gpr .rdi
  let b := s.mem (p + BitVec.ofNat 64 idx.toNat)
  let v := s.mem (p + BitVec.ofNat 64 ii.toNat)
  simp only [replace, List.append_assoc]
  rw [WP.block_append_iff]
  refine WP.mono (WP.keep [.rax, .r10, .r11] (lookup_core s idx h9 hr) (by decide +kernel))
    fun t ⟨⟨tax, tm⟩, tk⟩ => ?_
  have t9 : t.gpr .r9 = s.gpr .r9 := tk.gpr (by decide)
  have tdi : t.gpr .rdi = s.gpr .rdi := tk.gpr (by decide)
  have tcx : t.gpr .rcx = s.gpr .rcx := tk.gpr (by decide)
  have hit : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h1 : WP isa (.block [.movzx8 .r11 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r11),
      .mov .r11 (imm 0)]) t fun u =>
      u.gpr .rax = (b ^^^ v).setWidth 64 ∧ u.gpr .r11 = 0 ∧ u.gpr .r9 = s.gpr .r9 ∧
        u.gpr .rdi = s.gpr .rdi ∧ u.gpr .rcx = s.gpr .rcx ∧ u.mem = s.mem ∧ u.rd = s.rd ∧
        u.wr = s.wr := by
    rrun [hit, tax, tm, t9, tdi, tcx, tk.2.1, tk.2.2]
    rw [hcx, byte_addr ii, xor_byte]
  refine WP.mono h1 fun u ⟨uax, u11, u9, udi, ucx, um, urd, uwr⟩ => ?_
  rw [WP.block_append_iff]
  have hsp := spread_steps u idx (b ^^^ v) (u9.trans h9) uax 8 (by decide) u
    (by rw [u11]; unfold spread; rw [ite_eq_right (by omega)]) rfl rfl rfl
  rw [← lanesDown_eq] at hsp
  refine WP.mono (WP.keep [.r10, .r11] hsp (by decide +kernel)) fun w ⟨⟨w11, wax, wm⟩, wk⟩ => ?_
  have w9 : w.gpr .r9 = s.gpr .r9 := (wk.gpr (by decide)).trans u9
  have wdi : w.gpr .rdi = s.gpr .rdi := (wk.gpr (by decide)).trans udi
  have wcx : w.gpr .rcx = s.gpr .rcx := (wk.gpr (by decide)).trans ucx
  have wrd : w.rd = s.rd := wk.2.1.trans urd
  have wwr : w.wr = s.wr := wk.2.2.trans uwr
  have hiw : InRegions (s.rd ++ s.wr) (s.gpr .rdi + s.gpr .rcx) 1 := by
    rw [hcx, byte_addr]; exact hi
  rw [WP.block_append_iff]
  have h2 : WP isa (.block [.movzx8 .r10 (atIdx .rdi .rcx), .alu .xor .rax (.reg .r10)]) w
      fun x => x.gpr .rax = b.setWidth 64 ∧ x.gpr .r11 = w.gpr .r11 ∧ x.gpr .r9 = s.gpr .r9 ∧
        x.gpr .rdi = s.gpr .rdi ∧ x.mem = s.mem ∧ x.wr = s.wr := by
    rrun [hiw, wax, uax, wm, um, w9, wdi, wcx, wwr, wrd]
    rw [hcx, byte_addr ii, xor_byte, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  refine WP.mono h2 fun x ⟨xax, x11, x9, xdi, xm, xwr⟩ => ?_
  refine WP.mono (WP.keep [.r10] (scatter_steps s idx _ h9 hw 32 (by decide) x rfl x9 xdi xwr xm)
    (by decide +kernel)) fun y ⟨⟨ym, _⟩, yk⟩ => ?_
  refine ⟨(yk.gpr (by decide)).trans xax, ?_⟩
  rw [ym, x11, w11]
  unfold scatter spread
  rw [ite_eq_left (by omega), ite_eq_left (Nat.zero_le _), Nat.sub_zero, writeW_byte,
    ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

end VG.Proof.Rc4.X86_64
