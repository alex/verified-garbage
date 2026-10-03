import VerifiedGarbage.Proof.Argon2.X86.Derive.FillLoops
import VerifiedGarbage.Proof.Argon2.FinalReduction
import VerifiedGarbage.Proof.Argon2.Serialization

/-!
# Argon2 on x86 (32-bit): the final block and the tag

`reduce_ok`: the memory's first block becomes the XOR of every lane's last
block (`Proof.Argon2.reduction`), the other blocks kept; `finalOutput_ok`:
H′ of it to `out`, the tag (`Proof.Argon2.finish_reduction`).
-/

namespace VG.Proof.Argon2.X86.Derive

open VG VG.X86
open VG.X86.Wp (Upd Mupd Fupd wp_movi wp_mov wp_add wp_addi wp_subi wp_sub wp_addm wp_cmpi wp_ldm wp_stm)
open VG.Spec.Argon2 (Block blockAt zeroBlock FillState compress xorBlock)
open VG.Spec.Blake2 (bytesAt)
open VG.Proof.Argon2.X86 (blk ofWords blk_of_words xor_words)
open VG.Impl.Sha512.X86 (at_)
open VG.Impl.Argon2.X86.Derive (laneOff laneLenOff argOff divisorOff segLenOff strideOff)

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `n` stores of `eax = 0` to `[edi + 4k]`, `edi` the memory matrix. -/
theorem memZeros_ok {s : State} (h : Inv s₀ s) (hx : s.gpr .edi = memP s₀) (ha : s.gpr .eax = 0) :
    ∀ n ≤ 256, WP isa (.block ((List.range n).map fun k => Instr.store (at_ .edi (4 * k)) .eax)) s fun t =>
      Inv s₀ t ∧ t.gpr = s.gpr ∧ Frame [⟨matrixCell (memB s₀) 0, 1024⟩] s.mem t.mem ∧
      ∀ i < n, mw s₀ t.mem (4 * i) = 0
  | 0, _ => WP.block_nil ⟨h, rfl, Frame.refl _ _, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, hn => by
    have b1 := blocks_pos hp
    have hb := blocks22 hp
    have hm := hp.mem_fits
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append ((memZeros_ok h hx ha n (by omega)).mono fun t ⟨it, gt, ft, wt⟩ => ?_)
    have ea : addr (t.gpr .edi) (4 * n) = memB s₀ + BitVec.ofNat 64 (4 * n) := by
      rw [gt, hx, mem_addr' hp (by omega)]
    have hc : (memR s₀).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [ea]; exact Offset.contains_base _ (by omega) (by omega)
    have hc' : (⟨matrixCell (memB s₀) 0, 1024⟩ : Region).Contains (addr (t.gpr .edi) (4 * n)) 4 := by
      rw [ea, show matrixCell (memB s₀) 0 = memB s₀ by simp [matrixCell]]
      exact Offset.contains_base _ (by omega) (by omega)
    refine Wp.wp_stm rfl ⟨_, by rw [it.wr]; exact mem_mem hp, hc⟩ fun t₁ u₁ => WP.block_nil
      ⟨it.store (R := memR s₀) (by simp) hc u₁, by rw [u₁.gpr, gt], ?_, fun i hi => ?_⟩
    · rw [u₁.mem]
      exact ft.writeW (List.mem_singleton_self _) _ hc'
    · rw [u₁.mem, gt, hx, show 4 * n = 0 + 4 * n by omega, show 4 * i = 0 + 4 * i by omega,
        mw_store hp _ (by omega) (by omega) (by omega), ha]
      by_cases e : 0 + 4 * n = 0 + 4 * i
      · rw [ite_eq_left e]
      · rw [ite_eq_right e, show 0 + 4 * i = 4 * i by omega]; exact wt i (by omega)

end


theorem reduction_snoc (p : Spec.Argon2.Params) (M : Array Block) (l : Nat) (acc : Block) :
    Proof.Argon2.reduction p M 0 (l + 1) acc =
      xorBlock (Proof.Argon2.reduction p M 0 l acc) (M[Proof.Argon2.lastIndex p l]?.getD zeroBlock) := by
  unfold Proof.Argon2.reduction
  rw [foldl_range'_snoc, Nat.zero_add]

/-- The state of the reduction after `l` lanes. -/
structure RI (s₀ : State) (M : Array Block) (l : Nat) (s : State) : Prop where
  inv : Inv s₀ s
  pr : Prm s₀ s
  lane : lw s₀ s laneOff = BitVec.ofNat 32 l
  first : blockAt s.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 l zeroBlock
  rest : ∀ k < (prm s₀).blocks, k ≠ 0 → blockAt s.mem (matrixCell (memB s₀) k) = M[k]?.getD zeroBlock

theorem cell0 (s₀ : State) : matrixCell (memB s₀) 0 = memB s₀ := by simp [matrixCell]

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- One lane of the reduction. -/
theorem reduceLane_ok {s : State} {M : Array Block} {l : Nat} (h : RI s₀ M l s) (hl : l < lanesN s₀) :
    WP isa (.block (Impl.Argon2.X86.Derive.reduceLane ++
      Impl.Argon2.X86.Derive.advance laneOff (Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg))))
      s fun t => RI s₀ M (l + 1) t ∧ t.cf = some (decide (l + 1 < lanesN s₀)) := by
  have L8 := laneLen_ge hp
  have hlt := hp.lanes_lt
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  obtain ⟨cl, _⟩ := cell_fits hp hl (col := (prm s₀).laneLen - 1) (by omega)
  have last : Proof.Argon2.lastIndex (prm s₀) l = l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) := by
    unfold Proof.Argon2.lastIndex; rw [Nat.succ_mul]; omega
  have ne0 : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) ≠ 0 := by omega
  unfold Impl.Argon2.X86.Derive.reduceLane Impl.Argon2.X86.Derive.writeBlock
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  refine wp_ldloc hp h.inv (d := laneOff) (by decide) fun s₁ u₁ => ?_
  have i₁ := h.inv.upd u₁ (by decide) (by decide)
  refine wp_ldloc hp i₁ (d := laneLenOff) (by decide) fun s₂ u₂ => wp_subi fun s₃ u₃ _ _ => ?_
  have i₃ := (i₁.upd u₂ (by decide) (by decide)).upd u₃ (by decide) (by decide)
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  refine blockAddr_ok hp i₃ (h.pr.of_mem m₃) hl (col := (prm s₀).laneLen - 1) (by omega)
    (by rw [u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr, h.lane])
    (by rw [u₃.gpr, u₂.gpr, lw_mem u₁.mem, h.pr.laneLen, Wp.ofNat_pred (by omega)]) fun s₄ a₄ _ k₄ => ?_
  have i₄ := i₃.keep k₄
  refine wp_mov fun s₅ u₅ => ?_
  have i₅ := i₄.upd u₅ (by decide) (by decide)
  refine wp_ldarg hp i₅ (i := 13) (by decide) fun s₆ u₆ => ?_
  have i₆ := i₅.upd u₆ (by decide) (by decide)
  have m₆ : s₆.mem = s.mem := by rw [u₆.mem, u₅.mem, k₄.mem, m₃]
  have hm := hp.mem_fits
  have b22 := blocks22 hp
  have b1 := blocks_pos hp
  generalize hc : l * (prm s₀).laneLen + ((prm s₀).laneLen - 1) = c at cl a₄ ne0 last
  have hc' : c * 1024 + 1024 ≤ blocksN s₀ * 1024 := by omega_using [cl]
  have sx : s₆.gpr .esi = memP s₀ + BitVec.ofNat 32 (c * 1024) := by
    rw [u₆.other _ (by decide), u₅.gpr, a₄]
  have dx : s₆.gpr .edi = memP s₀ + BitVec.ofNat 32 (0 * 1024) := by
    rw [u₆.gpr]; simp
  refine WP.block_append ((writeWords_ok hp i₆ (cur := 0) b1 true sx
    (by rw [add_nat (by omega_using [hc', hm])]; omega_using [hc', hm])
    ⟨memR s₀, by simp, c * 1024, cell_addr hp cl, hc'⟩
    (by rw [cell_addr hp cl]; exact cell_other hp cl b1 ne0) dx 256 (Nat.le_refl _)).mono
    fun t₇ ⟨i₇, g₇, f₇, w₇⟩ => ?_)
  have lt₇ : ∀ d, d + 4 ≤ 144 → lw s₀ t₇ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₆ d]
    exact f₇.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine (advance_ok hp i₇ (d := laneOff) (n := l) (by decide) (by rw [lt₇ _ (by decide)]; exact h.lane)
    (by omega) (B := lanesN s₀) (by omega) fun v iv _ => ?_).mono fun t ⟨it, mt, ct, _⟩ => ⟨?_, ct⟩
  · rw [show Impl.Argon2.X86.Derive.fr (argOff Impl.Argon2.X86.Derive.lanesArg) = .mem ⟨.ebp, argOff 7⟩ from rfl,
      Wp.readSrc_mem iv.ebp (iv.arg_in hp (by decide)), iv.arg hp (by decide)]
    simp
  obtain ⟨lt, _, ct⟩ := loc_store hp (d := laneOff) (by decide) mt
  have new : blockAt t₇.mem (matrixCell (memB s₀) 0) =
      xorBlock (blockAt s.mem (matrixCell (memB s₀) c)) (blockAt s.mem (matrixCell (memB s₀) 0)) := by
    rw [cell_blk hp _ b1, cell_blk hp _ b1, cell_blk hp _ cl,
      blk_of_words (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i) ^^^ mw s₀ s.mem (0 * 1024 + 4 * i)) fun i hi => by
        rw [← mw, w₇ i hi, ite_eq_left hi, ite_eq_left (rfl : true = true), m₆, addr_shift],
      blk_of_words (m := s.mem) (B := memP s₀) (o := c * 1024) (f := fun i => mw s₀ s.mem (c * 1024 + 4 * i))
        fun _ _ => rfl,
      blk_of_words (m := s.mem) (B := memP s₀) (o := 0 * 1024) (f := fun i => mw s₀ s.mem (0 * 1024 + 4 * i))
        fun _ _ => rfl, xor_words]
  refine ⟨it, Prm.of_lw h.pr fun d hd => ?_, ?_, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [lt d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lt₇ d hd4]
  · show t.mem.readW _ 32 = _
    rw [mt, Mem.readW_writeW_self32]
  · rw [ct _ (by rw [← hb]; exact b1), new, h.first, h.rest _ (by rw [← hb]; exact cl) ne0, reduction_snoc,
      Proof.Argon2.xorBlock_comm, last]
  · rw [ct _ hk, blockAt_keep f₇ (fun r hr => ?_), m₆, h.rest k hk k0]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- The first block of `reduce`: the memory's first block cleared, and the lane `0`. -/
theorem reduceStart_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa (.block (Impl.Argon2.X86.Derive.reduceClear ++ Impl.Argon2.X86.Derive.setLocal laneOff 0)) s
      (RI s₀ M 0) := by
  have b1 := blocks_pos hp
  have hb : blocksN s₀ = (prm s₀).blocks := hp.blocks
  unfold Impl.Argon2.X86.Derive.reduceClear Impl.Argon2.X86.Derive.setLocal
  simp only [List.cons_append, List.nil_append]
  refine wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => wp_movi fun s₂ u₂ => ?_
  have i₂ := (h.upd u₁ (by decide) (by decide)).upd u₂ (by decide) (by decide)
  refine WP.block_append ((memZeros_ok hp i₂ (by rw [u₂.other _ (by decide), u₁.gpr]) u₂.gpr 256
    (Nat.le_refl _)).mono fun s₃ ⟨i₃, _, f₃, z₃⟩ => ?_)
  refine wp_movi fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_stloc hp i₄ (d := laneOff) (by decide) fun s₅ i₅ v₅ _ _ m₅ => WP.block_nil ?_
  obtain ⟨l₅, _, c₅⟩ := loc_store hp (d := laneOff) (by decide) m₅
  have m₂ : s₂.mem = s.mem := by rw [u₂.mem, u₁.mem]
  have lt₃ : ∀ d, d + 4 ≤ 144 → lw s₀ s₃ d = lw s₀ s d := fun d hd => by
    rw [← lw_mem m₂ d]
    exact f₃.readW (r := ⟨addr (E s₀) d, 4⟩) (Region.contains_self _ _) (fun r hr => by
      simp only [List.mem_singleton] at hr; subst hr
      exact (loc_disj hp hd (memR s₀) (by simp)).sub_right (cell_in_mem b1)) (by decide)
  refine ⟨i₅, Prm.of_lw pr fun d hd => ?_, by rw [v₅, u₄.gpr]; rfl, ?_, fun k hk k0 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have hd4 : d + 4 ≤ 144 := by rcases hd with rfl | rfl | rfl | rfl <;> decide
    rw [l₅ d (by omega) (by rcases hd with rfl | rfl | rfl | rfl <;> decide), lw_mem u₄.mem, lt₃ d hd4]
  · rw [c₅ _ (by rw [← hb]; exact b1), u₄.mem, cell_blk hp _ b1,
      blk_of_words (f := fun _ => 0) fun i hi => by rw [← mw, Nat.zero_mul, Nat.zero_add]; exact z₃ i hi,
      ofWords_zero]
    rfl
  · rw [c₅ _ hk, u₄.mem, blockAt_keep f₃ (fun r hr => ?_), m₂, hm.block k hk]
    simp only [List.mem_singleton] at hr; subst hr
    exact cell_other hp (by rw [hb]; exact hk) b1 k0

/-- `reduce`: the XOR of every lane's last block, to the memory's first block. -/
theorem reduce_ok {s : State} {M : Array Block} (h : Inv s₀ s) (pr : Prm s₀ s)
    (hm : Represents s.mem (memB s₀) (prm s₀).blocks M) :
    WP isa Impl.Argon2.X86.Derive.reduce s fun t => Inv s₀ t ∧ Prm s₀ t ∧
      blockAt t.mem (matrixCell (memB s₀) 0) = Proof.Argon2.reduction (prm s₀) M 0 (lanesN s₀) zeroBlock := by
  have hl1 := hp.lanes_pos
  unfold Impl.Argon2.X86.Derive.reduce
  refine WP.seq ((reduceStart_ok hp h pr hm).mono fun s₅ start => ?_)
  refine WP.loop (M := isa) (fun n t => ∃ l, n = lanesN s₀ - l ∧ l < lanesN s₀ ∧ RI s₀ M l t) ?_ (lanesN s₀) s₅
    ⟨0, by omega, hl1, start⟩
  rintro n t ⟨l, rfl, hl, ht⟩
  refine (reduceLane_ok hp ht hl).mono fun u ⟨hu, cu⟩ => ?_
  by_cases e : l + 1 < lanesN s₀
  · exact .inr ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], _, by omega, l + 1, rfl, e, hu⟩
  · refine .inl ⟨by rw [show isa.eval .b u = u.cf from rfl, cu]; simp [e], hu.inv, hu.pr, ?_⟩
    rw [hu.first, show l + 1 = lanesN s₀ by omega]

end

section
variable {s₀ : State} (hp : DPre s₀)
include hp

/-- `finalOutput`: H′ of the memory's first block, to `out`. -/
theorem finalOutput_ok {s : State} (h : Inv s₀ s) :
    WP isa Impl.Argon2.X86.Derive.finalOutput s fun t => Inv s₀ t ∧
      bytesAt t.mem ((outP s₀).setWidth 64) (outL s₀) =
        Spec.Argon2.hPrime (outL s₀) (Spec.Argon2.serialize (blockAt s.mem (matrixCell (memB s₀) 0))) := by
  have b1 := blocks_pos hp
  have hm := hp.mem_fits
  have ho := hp.out_fits
  have tg := hp.tag_ge
  unfold Impl.Argon2.X86.Derive.finalOutput
  refine WP.seq (wp_ldarg hp h (i := 13) (by decide) fun s₁ u₁ => ?_)
  have i₁ := h.upd u₁ (by decide) (by decide)
  refine wp_movi fun s₂ u₂ => ?_
  have i₂ := i₁.upd u₂ (by decide) (by decide)
  refine wp_ldarg hp i₂ (i := 16) (by decide) fun s₃ u₃ => ?_
  have i₃ := i₂.upd u₃ (by decide) (by decide)
  refine wp_ldarg hp i₃ (i := 17) (by decide) fun s₄ u₄ => ?_
  have i₄ := i₃.upd u₄ (by decide) (by decide)
  refine wp_ldarg hp i₄ (i := 15) (by decide) fun s₅ u₅ => WP.block_nil ?_
  have i₅ := i₄.upd u₅ (by decide) (by decide)
  have m₅ : s₅.mem = s.mem := by rw [u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have si : s₅.gpr .esi = memP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr]
  have ax : (s₅.gpr .eax).toNat = 1024 := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.other _ (by decide), u₂.gpr]; rfl
  have di : s₅.gpr .edi = outP s₀ := by
    rw [u₅.other _ (by decide), u₄.other _ (by decide), u₃.gpr]
  have cx : (s₅.gpr .ecx).toNat = outL s₀ := by
    rw [u₅.other _ (by decide), u₄.gpr]
  refine hcall_ok hp i₅ (r := .esi) (by decide) u₅.gpr
    ⟨memR s₀, by simp, 0, by rw [si]; simp, by rw [ax]; show 0 + 1024 ≤ blocksN s₀ * 1024; omega⟩
    (by rw [si, ax]; omega) ⟨outR s₀, by simp, 0, by rw [di]; simp, by rw [cx]; show 0 + outL s₀ ≤ outL s₀; omega⟩
    (by rw [di, cx]; exact ho) (by rw [cx]; omega) fun t it _ _ post => ⟨it, ?_⟩
  rw [← di, ← cx, post, cx, ax, si, m₅, cell0, Proof.Argon2.serialize_blockAt]

end
end VG.Proof.Argon2.X86.Derive
