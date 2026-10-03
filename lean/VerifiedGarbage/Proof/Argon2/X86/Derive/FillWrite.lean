import VerifiedGarbage.Proof.Argon2.X86.Derive.FillPtr
import VerifiedGarbage.Proof.Framework.Omega

/-!
# Argon2 on x86 (32-bit): the new block

`fillCompress_ok`: G of the previous and reference blocks, to
`scratch + 4096`. `writeWords_ok`: its words to the current block, XORed
into the old ones after the first pass; `fillWrite_ok`: the current block
after the step, as `FillStep.update` has it.
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm wp_andi
  wp_sbb_self wp_and wp_xor wp_xorm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (sliceOff segLenOff indexOff laneOff laneLenOff argOff passOff counterOff
  j1Off j2Off refLaneOff startOff countOff tmpOff curOff writeWord)

/-- Words of the memory matrix. -/
abbrev mw (s₀ : State) (m : Mem) (o : Nat) : BitVec 32 := m.readW (addr (memP s₀) o) 32

section
variable {s₀ : State} (hp : DPre s₀)
include hp

theorem blocks22 : blocksN s₀ < 2 ^ 22 := by
  have hb := hp.blocks_lt
  omega

theorem mem_addr' {o : Nat} (ho : o < blocksN s₀ * 1024) : addr (memP s₀) o = memB s₀ + BitVec.ofNat 64 o :=
  addr_eq (by have := hp.mem_fits; omega)

/-- A word of the matrix after a store to another, or the same. -/
theorem mw_store (m : Mem) {a b : Nat} (ha : a + 4 ≤ blocksN s₀ * 1024) (hb : b + 4 ≤ blocksN s₀ * 1024)
    (h : a = b ∨ a + 4 ≤ b ∨ b + 4 ≤ a) (v : BitVec 32) :
    mw s₀ (m.writeW (addr (memP s₀) a) v) b = if a = b then v else mw s₀ m b := by
  have := blocks22 hp
  by_cases e : a = b
  · subst e; rw [ite_eq_left rfl]; exact Mem.readW_writeW_self32 _ _ _
  · rw [ite_eq_right e, mw, mw, mem_addr' hp (by omega), mem_addr' hp (by omega)]
    exact Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)

/-- The words of the current block, `n` of them written. -/
theorem writeWords_ok {s : State} (h : Inv s₀ s) {cur : Nat} (hc : cur < blocksN s₀) (xo : Bool)
    {P : BitVec 32} (hsi : s.gpr .esi = P) (hPfit : P.toNat + 1024 ≤ 2 ^ 32)
    (hPw : ∃ R ∈ [scrR s₀, memR s₀], ∃ off, P.setWidth 64 = R.base + BitVec.ofNat 64 off ∧ off + 1024 ≤ R.len)
    (hPC : Region.Disjoint ⟨P.setWidth 64, 1024⟩ ⟨matrixCell (memB s₀) cur, 1024⟩)
    (hdi : s.gpr .edi = memP s₀ + BitVec.ofNat 32 (cur * 1024)) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).flatMap (writeWord xo))) s fun t =>
      Inv s₀ t ∧ (∀ r, r ≠ .eax → t.gpr r = s.gpr r) ∧
      Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem t.mem ∧
      ∀ i < 256, mw s₀ t.mem (cur * 1024 + 4 * i) = if i < n then
        (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i) else s.mem.readW (addr P (4 * i)) 32)
        else mw s₀ s.mem (cur * 1024 + 4 * i)
  | 0, _ => WP.block_nil ⟨h, fun _ _ => rfl, Frame.refl _ _, fun i _ => by rw [ite_eq_right (by omega)]⟩
  | n + 1, hn => by
    have hs := hp.scr_fits
    have hm := hp.mem_fits
    have hb := blocks22 hp
    have hc' : cur * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    refine WP.block_append ((writeWords_ok h hc xo hsi hPfit hPw hPC hdi n (by omega)).mono
      fun t ⟨it, gt, ft, wt⟩ => ?_)
    have cell : matrixCell (memB s₀) cur = memB s₀ + BitVec.ofNat 64 (cur * 1024) := rfl
    -- The source word is kept: only the current block has been written.
    have eP : addr P (4 * n) = P.setWidth 64 + BitVec.ofNat 64 (4 * n) := addr_eq (by omega_using [hPfit, hn])
    have sw_t : t.mem.readW (addr P (4 * n)) 32 = s.mem.readW (addr P (4 * n)) 32 := by
      rw [eP]
      refine ft.readW (r := ⟨P.setWidth 64 + BitVec.ofNat 64 (4 * n), 4⟩) (Region.contains_self _ _)
        (fun r hr => ?_) (by decide)
      simp only [List.mem_singleton] at hr; subst hr
      exact hPC.sub_left (Offset.sub_base _ (by omega_using [hn]))
    have ea : addr (t.gpr .esi) (4 * n) = addr P (4 * n) := by
      rw [gt _ (by decide), hsi]
    have eb : addr (t.gpr .edi) (4 * n) = addr (memP s₀) (cur * 1024 + 4 * n) := by
      rw [gt _ (by decide), hdi, addr_shift]
    have b1 : cur * 1024 + 4 * n + 4 ≤ blocksN s₀ * 1024 := by omega_using [hc', hn]
    have b2 : cur * 1024 + 1024 < 2 ^ 64 := by omega_using [hc', hb]
    have inS : InRegions (t.rd ++ t.wr) (addr (t.gpr .esi) (4 * n)) 4 := by
      obtain ⟨R, hR, off, bR, lR⟩ := hPw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
      have RW : R ∈ t.wr ∧ R.len ≤ 2 ^ 32 := by
        rw [it.wr]
        rcases hR with rfl | rfl
        · exact ⟨scr_mem hp, by show 16384 ≤ 2 ^ 32; decide⟩
        · exact ⟨mem_mem hp, by show blocksN s₀ * 1024 ≤ 2 ^ 32; omega_using [hm]⟩
      rw [ea, eP, bR, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      exact ⟨R, List.mem_append_right _ RW.1, Offset.contains_base _ (by omega_using [lR, hn])
        (by have := RW.2; omega_using [lR, hn, this])⟩
    have inMc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1])]
      exact Offset.contains_base _ b1 (by omega_using [b1, hb])
    have inC : (⟨matrixCell (memB s₀) cur, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [eb, mem_addr' hp (by omega_using [b1]), cell]
      exact Offset.contains _ (by omega_using []) (by omega_using [hn]) b2
    have inM : InRegions t.wr (addr (t.gpr .edi) (4 * n)) 4 := ⟨memR s₀, by rw [it.wr]; exact mem_mem hp, inMc⟩
    -- The word.
    have fin : ∀ (v : BitVec 32) (u : State), u.mem = t.mem.writeW (addr (t.gpr .edi) (4 * n)) v →
        u.rd = t.rd → u.wr = t.wr → (∀ r, r ≠ .eax → u.gpr r = s.gpr r) →
        v = (if xo then s.mem.readW (addr P (4 * n)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * n)
          else s.mem.readW (addr P (4 * n)) 32) →
        Inv s₀ u ∧ (∀ r, r ≠ .eax → u.gpr r = s.gpr r) ∧
        Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem ∧
        ∀ i < 256, mw s₀ u.mem (cur * 1024 + 4 * i) = if i < n + 1 then
          (if xo then s.mem.readW (addr P (4 * i)) 32 ^^^ mw s₀ s.mem (cur * 1024 + 4 * i)
            else s.mem.readW (addr P (4 * i)) 32)
          else mw s₀ s.mem (cur * 1024 + 4 * i) := fun v u hm hrd hwr gu ev => by
      have fu : Frame [⟨matrixCell (memB s₀) cur, 1024⟩] s.mem u.mem := by
        rw [hm]; exact ft.writeW (List.mem_singleton_self _) v inC
      have iu : Inv s₀ u := it.step (by rw [gu _ (by decide), gt _ (by decide)])
        (by rw [gu _ (by decide), gt _ (by decide)]) hrd hwr
        (by rw [hm]; exact (Frame.refl _ _).writeW (r := memR s₀) (by simp) v inMc)
      refine ⟨iu, gu, fu, fun i hi => ?_⟩
      rw [hm, eb, mw_store hp _ b1 (by omega_using [hi, hc', hb]) (by omega_using []), wt i hi]
      by_cases e : i = n
      · subst e
        rw [ite_eq_left rfl, ite_eq_left (show i < i + 1 by omega_using []), ev]
      · rw [ite_eq_right (show ¬cur * 1024 + 4 * n = cur * 1024 + 4 * i by omega_using [e])]
        by_cases c : i < n
        · rw [ite_eq_left c, ite_eq_left (show i < n + 1 by omega_using [c])]
        · rw [ite_eq_right c, ite_eq_right (show ¬i < n + 1 by omega_using [c, e])]
    cases xo
    · simp only [writeWord, Bool.false_eq_true, ite_false, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_stm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₁.mem]) (by rw [mu.rd, v₁.rd]) (by rw [mu.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₁.other r hr, gt r hr]) ?_
      simp only [Bool.false_eq_true, ite_false]
      rw [v₁.gpr, ea, sw_t]
    · simp only [writeWord, ite_true, List.cons_append, List.nil_append]
      refine wp_ldm rfl inS fun u₁ v₁ => ?_
      refine wp_xorm (b := .edi) (v₁.other .edi (by decide)) (by rw [v₁.rd, v₁.wr]; exact
        ⟨memR s₀, List.mem_append_right _ (by rw [it.wr]; exact mem_mem hp), inMc⟩) fun u₂ v₂ => ?_
      refine wp_stm (b := .edi) (by rw [v₂.other .edi (by decide), v₁.other .edi (by decide)])
        (by rw [v₂.wr, v₁.wr]; exact inM) fun u mu => WP.block_nil ?_
      refine fin _ u (by rw [mu.mem, v₂.mem, v₁.mem]) (by rw [mu.rd, v₂.rd, v₁.rd]) (by rw [mu.wr, v₂.wr, v₁.wr])
        (fun r hr => by rw [mu.gpr, v₂.other r hr, v₁.other r hr, gt r hr]) ?_
      simp only [ite_true]
      rw [v₂.gpr, v₁.gpr, v₁.mem, ea, sw_t, eb, ← mw, wt n (by omega_using [hn]),
        ite_eq_right (show ¬n < n by omega_using [])]

end

end VG.Proof.Argon2.X86.Derive
