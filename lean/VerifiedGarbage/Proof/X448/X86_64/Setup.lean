import VerifiedGarbage.Proof.X448.X86_64.Freeze
import VerifiedGarbage.Proof.X448.X86_64.Bits
import VerifiedGarbage.Proof.Framework.X86_64.Spill

/-!
# X448 on x86-64: reading the arguments

`setup` saves the callee-saved registers at the start of the working space,
reads the u-coordinate (seven words: all 448 bits are used), and sets the
ladder's variables to their initial values.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64 VG.Proof.X448

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

/-- A number of bytes is its words. -/
theorem leNum_bytesAt_mv (m : Mem) (p : Addr) :
    ∀ (o n : Nat), X25519.leNum (Spec.X448.bytesAt m (off p o) (8 * n)) = mv m p o n
  | _, 0 => by simp [Spec.X448.bytesAt, X25519.leNum, mv]
  | o, n + 1 => by
    rw [show 8 * (n + 1) = 8 + 8 * n by omega, bytesAt_add, X25519.leNum_append, length_bytesAt,
      leNum_bytesAt_read, mv, show off p o + BitVec.ofNat 64 8 = off p (o + 8) by
        simp only [off, BitVec.add_assoc, BitVec.ofNat_add],
      leNum_bytesAt_mv m p (o + 8) n]
    simp only [Mem.readW, Nat.reduceDiv, BitVec.setWidth_eq]
    rfl

theorem decode_mv (m : Mem) (p : Addr) :
    Spec.X448.decodeUCoordinate (Spec.X448.bytesAt m p 56) = mv m p 0 7 := by
  have h := leNum_bytesAt_mv m p 0 7
  rw [show off p 0 = p from BitVec.add_zero p] at h
  rw [decodeUCoordinate_eq (length_bytesAt _ _ _)]
  exact h

/-- The u-coordinate, as seven words. -/
theorem loadU_ok (s : State) {p : Addr} (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block ((List.range 7).map fun i => .mov (w i) (.mem (at_ .rdx (8 * i))))) s fun s' =>
      rv s' W = mv s.mem p 0 7 ∧ Keeps W s s' := by
  apply WP.of_runBlock
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, w, W, List.getD_cons_succ,
    List.getD_cons_zero, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, State.load64,
    ea_at, hp, hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega),
    hr 32 (by omega), hr 40 (by omega), hr 48 (by omega), Nat.reduceMul,
    RegUpd.gpr_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · simp only [rv, mv, RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Nat.reduceAdd]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2, ite_false]

/-! ## Saving the callee-saved registers -/

/-- The callee-saved registers of `g`, saved at the start of the working space. -/
abbrev Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop := Spill.Saved m base g saved

theorem saved_lt : ∀ rd ∈ saved, rd.2 + 8 ≤ 48 := by decide

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h48 : 48 ≤ o) : Saved base g m' := fun rd hrd => by
  have := saved_lt rd hrd
  exact (ho.word (by omega) (by omega)).trans (h rd hrd)

theorem save_ok {s : State} {base : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  refine WP.mono (Spill.save_ok .rcx saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := saved_lt p hp; rw [hc]; exact ⟨_, hw, contains_sc (by omega)⟩
  · rw [hm, hc]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ saved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega
  · rw [hm, hc]; exact Spill.saveMem_saved _ _ _ _ (by decide)

/-! ## The initial values -/

theorem movs_ok (s : State) :
    WP isa (.block ([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr)) s fun s' =>
      s'.gpr .r15 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .rcx ∧ Keeps [.r15, .rdi] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem consts_ok (s : State) :
    WP isa (.block ([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] : List Instr)) s fun s' =>
      s'.gpr .rax = 0 ∧ s'.gpr .rdx = 1 ∧ Keeps [.rax, .rdx] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc32, State.setReg32,
    RegUpd.gpr_setReg, ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨rfl, rfl, fun r hr => ?_, rfl, rfl, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

theorem storeSwap_ok {s : State} {base : Addr} (hs : Scr s base) :
    WP isa (.block ([.store (sc SWAP) .rax] : List Instr)) s fun s' =>
      s'.mem = s.mem.writeW (off base SWAP) (s.gpr .rax) ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧
        s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, ea_sc, hs.rdi, State.store64,
    show InRegions s.wr (off base SWAP) 8 from ⟨_, hs.wr, contains_sc (by decide)⟩, ite_true,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial⟩

/-- Stores into a slot, as an update of the slots. -/
theorem stores_E {s : State} {base : Addr} (hs : Scr s base) (i : Index) (rs : List Reg)
    (hl : rs.length = 7) :
    WP isa (.block (stores (slot i.val) rs)) s fun s' =>
      E s'.mem base = Function.update (E s.mem base) i (toFe (rv s rs)) ∧
      Outside base (slot i.val) 56 s.mem s'.mem ∧
      (∀ r, s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hi := slot_lt i
  refine WP.mono (stores_ok hs (slot i.val) rs (by rw [hl]; simp only [ACC] at hi; omega))
    fun s' ⟨e, o, g, rd, wr⟩ => ?_
  rw [hl] at e o
  refine ⟨?_, o, g, rd, wr⟩
  rw [E_update (o.left ACC 112)]
  congr 1
  simp only [F, fe, e]

theorem setup_eq : setup = save ++ (([.mov .r15 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr) ++
    ((List.range 7).map (fun i => .mov (w i) (.mem (at_ .rdx (8 * i)))) ++
    (stores X1 W ++ (stores X3 W ++ (([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] : List Instr) ++
    (stores X2 ([.rdx, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    (stores Z2 ([.rax, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    (stores Z3 ([.rdx, .rax, .rax, .rax, .rax, .rax, .rax] : List Reg) ++
    ([.store (sc SWAP) .rax] : List Instr))))))))) := by
  simp only [setup, List.append_assoc]

/-- `setup`: the ladder's initial state, from the u-coordinate at `p`. -/
theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 8192⟩ : Region) ∈ s.wr) (hn : base.toNat + 8192 ≤ 2 ^ 64) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 56 → InRegions (s.rd ++ s.wr) (off p d) 8)
    (hd : ∀ j < 56, 8192 ≤ ofs base (off p j)) :
    WP isa (.block setup) s fun s' =>
      Scr s' base ∧ s'.gpr .r15 = s.gpr .rdi ∧
      (∀ r, r ∉ [Reg.rax, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15] →
        s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 8192 s.mem s'.mem ∧ Saved base s.gpr s'.mem ∧
      E s'.mem base 0 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E s'.mem base 1 = 1 ∧ E s'.mem base 2 = 0 ∧
      E s'.mem base 3 = toFe (Spec.X448.decodeUCoordinate (Spec.X448.bytesAt s.mem p 56)) ∧
      E s'.mem base 4 = 1 ∧ word s'.mem base SWAP = 0 := by
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (save_ok hc hw) fun s₁ ⟨g₁, rd₁, wr₁, o₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movs_ok s₁) fun s₂ ⟨r15₂, rdi₂, k₂⟩ => ?_
  have hs₂ : Scr s₂ base := ⟨by rw [rdi₂, g₁, hc], by rw [k₂.2.2.2, wr₁]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (loadU_ok s₂ (p := p) (by rw [k₂.1 _ (by decide), g₁, hp])
    fun d hd' => by rw [k₂.2.2.1, k₂.2.2.2, rd₁, wr₁]; exact hr d hd') fun s₃ ⟨u₃, k₃⟩ => ?_
  have hs₃ := hs₂.of_keeps k₃ (by decide)
  -- The coordinate's bytes are outside the working space, which is all `save` wrote.
  have hu : Spec.X448.bytesAt s₂.mem p 56 = Spec.X448.bytesAt s.mem p 56 := by
    rw [k₂.2.1]
    simp only [Spec.X448.bytesAt]
    refine List.map_congr_left fun i hi => o₁ _ (Or.inr ?_)
    simp only [List.mem_range] at hi
    have := hd i hi
    exact Nat.le_trans (by decide) this
  rw [← decode_mv, hu] at u₃
  rw [WP.block_append_iff]
  refine WP.mono (stores_E hs₃ 0 W rfl) fun s₄ ⟨e₄, o₄, g₄, rd₄, wr₄⟩ => ?_
  have hs₄ : Scr s₄ base := ⟨(g₄ _).trans hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_E hs₄ 3 W rfl) fun s₅ ⟨e₅, o₅, g₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₅) fun s₆ ⟨rax₆, rdx₆, k₆⟩ => ?_
  have hs₆ : Scr s₆ base := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_E hs₆ 1 _ rfl) fun s₇ ⟨e₇, o₇, g₇, rd₇, wr₇⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨(g₇ _).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_E hs₇ 2 _ rfl) fun s₈ ⟨e₈, o₈, g₈, rd₈, wr₈⟩ => ?_
  have hs₈ : Scr s₈ base := ⟨(g₈ _).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_E hs₈ 4 _ rfl) fun s₉ ⟨e₉, o₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (storeSwap_ok hs₉) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have G : ∀ r, r ∉ [Reg.rax, .rdx] → s'.gpr r = s₃.gpr r := fun r hr => by
    rw [g', g₉, g₈, g₇, k₆.1 r hr, g₅, g₄]
  have e' : E s'.mem base = E s₉.mem base := by
    funext i
    have := slot_ge i; have := slot_lt i
    simp only [E, F]
    rw [m', ((writeW_outside _ _ _ (by decide)).fe (d := slot i.val) (Or.inr (by simp only [SWAP]; omega))
      (by simp only [ACC] at *; omega))]
  have one : toFe (rv s₆ [.rdx, .rax, .rax, .rax, .rax, .rax, .rax]) = 1 := by
    simp only [rv, rax₆, rdx₆]; rfl
  have zero : toFe (rv s₇ [.rax, .rax, .rax, .rax, .rax, .rax, .rax]) = 0 := by
    simp only [rv, g₇, rax₆]; rfl
  have one' : toFe (rv s₈ [.rdx, .rax, .rax, .rax, .rax, .rax, .rax]) = 1 := by
    simp only [rv, g₈, g₇, rax₆, rdx₆]; rfl
  have w₄ : rv s₄ W = rv s₃ W := rv_congr fun r _ => g₄ r
  have o₃ : Outside base 0 8192 s.mem s₃.mem := by
    rw [k₃.2.1, k₂.2.1]; exact o₁.mono (by omega) (by omega)
  have o' : Outside base 48 1424 s₃.mem s'.mem := by
    have q : ∀ (i : Index) {m m' : Mem}, Outside base (slot i.val) 56 m m' →
        Outside base 48 1424 m m' := fun i {_ _} h => Outside.mono h (by have := slot_ge i; omega)
          (by have := i.isLt; simp only [slot]; omega)
    refine ((((q 0 o₄).trans (q 3 o₅)).trans ?_).trans ((q 1 o₇).trans ((q 2 o₈).trans (q 4 o₉)))).trans ?_
    · rw [k₆.2.1]; exact Outside.refl _ _ _ _
    · intro x hx
      rw [m']
      exact (writeW_outside _ _ _ (by decide)).mono (by simp only [SWAP]; omega)
        (by simp only [SWAP]; omega) x hx
  refine ⟨⟨by rw [g']; exact hs₉.rdi, wr' ▸ hs₉.wr, hn⟩, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [G _ (by decide), k₃.1 _ (by decide), r15₂, g₁]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [G r (by simp [hr.1, hr.2.1]), k₃.1 r (by simp [W, hr.2.2.2.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1,
      hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2.1]),
      k₂.1 r (by simp [hr.2.2.1, hr.2.2.2.2.2.2.2.2.2.2]), g₁]
  · rw [rd', rd₉, rd₈, rd₇, k₆.2.2.1, rd₅, rd₄, k₃.2.2.1, k₂.2.2.1, rd₁]
  · rw [wr', wr₉, wr₈, wr₇, k₆.2.2.2, wr₅, wr₄, k₃.2.2.2, k₂.2.2.2, wr₁]
  · exact o₃.trans (o'.mono (by omega) (by omega))
  · have sv : Saved base s.gpr s₃.mem := by rw [k₃.2.1, k₂.2.1]; exact sv₁
    exact sv.outside o' (by omega)
  · rw [e', e₉, e₈, e₇, k₆.2.1, e₅, e₄]
    simp (config := {decide := true}) only [Function.update_apply, ite_true, ite_false]
    rw [one, zero, one', w₄, u₃]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [m', word_writeW_self, g₉, g₈, g₇, rax₆]

end VG.Proof.X448.X86_64
