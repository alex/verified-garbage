import VerifiedGarbage.Proof.X25519.X86_64.Freeze
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X25519 on x86-64: reading the arguments

Untrusted: everything here is checked by Lean. `setup` reads the
u-coordinate, saves the callee-saved registers at the start of the working
space, and sets the ladder's variables to their initial values.
-/

namespace VG.Proof.X25519.X86_64

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Proof.X25519

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = off (s.gpr b) d := rfl

/-- The u-coordinate, decoded. -/
theorem loadU_ok (s : State) {p : Addr} (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block loadU) s fun s' =>
      val4 (s'.gpr .r8) (s'.gpr .r9) (s'.gpr .r10) (s'.gpr .r11) =
        Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32) ∧
      Keeps [.r8, .r9, .r10, .r11, .rax] s s' := by
  apply WP.of_runBlock
  simp only [loadU, runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu, State.load64,
    ea_at, hp, hr 0 (by omega), hr 8 (by omega), hr 16 (by omega), hr 24 (by omega),
    RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  refine ⟨?_, fun r hr => ?_, rfl, rfl, rfl⟩
  · rw [decodeUCoordinate_eq (length_bytesAt _ _ _), leNum_bytesAt_words64,
      show off p 0 = p from BitVec.add_zero p, show p + 8 = off p 8 from rfl,
      show p + 16 = off p 16 from rfl, show p + 24 = off p 24 from rfl]
    have := and_low63 ((s.mem.readW (off p 24) 64))
    simp only [val4]
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp only [RegUpd.gpr_setReg, RegUpd.gpr_arithFlags, hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1,
      hr.2.2.2.2, ite_false]

/-! ## Saving the callee-saved registers -/

theorem word_writeW_sep (m : Mem) (base : Addr) (v : BitVec 64) {d e : Nat}
    (h : d + 8 ≤ e ∨ e + 8 ≤ d) (hd : d + 8 ≤ 2 ^ 64) (he : e + 8 ≤ 2 ^ 64) :
    word (m.writeW (off base e) v) base d = word m base d :=
  Mem.readW_writeW_sep (sep_off base h hd he) (by decide)

theorem word_writeW_self (m : Mem) (base : Addr) (v : BitVec 64) (d : Nat) :
    word (m.writeW (off base d) v) base d = v :=
  Mem.readW_writeW_self64 _ _ _

theorem Outside.writeW {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m')
    {d : Nat} (ho : o ≤ d) (hd : d + 8 ≤ o + n) (hn : d + 8 < 2 ^ 64) (v : BitVec 64) :
    Outside base o n m (m'.writeW (off base d) v) :=
  h.trans ((writeW_outside m' base v hn).mono ho hd)

/-- The callee-saved registers of `g`, saved at the start of the working space. -/
def Saved (base : Addr) (g : Reg → BitVec 64) (m : Mem) : Prop :=
  ∀ rd ∈ saved, word m base rd.2 = g rd.1

theorem saved_lt : ∀ rd ∈ saved, rd.2 + 8 ≤ 48 := by decide

theorem Saved.outside {base : Addr} {g : Reg → BitVec 64} {m m' : Mem} (h : Saved base g m)
    {o n : Nat} (ho : Outside base o n m m') (h48 : 48 ≤ o) : Saved base g m' := fun rd hrd => by
  have := saved_lt rd hrd
  exact (ho.word (by omega) (by omega)).trans (h rd hrd)

theorem save_ok {s : State} {base : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) :
    WP isa (.block save) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Saved base s.gpr s'.mem := by
  have w : ∀ d, d + 8 ≤ 4096 → InRegions s.wr (off base d) 8 :=
    fun d hd => ⟨_, hw, contains_sc hd⟩
  apply WP.of_runBlock
  simp only [save, saved, List.map_cons, List.map_nil, runBlock_cons, runStep_some, runBlock_nil,
    exec, ea_at, hc, State.store64, w 0 (by omega), w 8 (by omega), w 16 (by omega),
    w 24 (by omega), w 32 (by omega), w 40 (by omega), ite_true, Option.some.injEq,
    exists_eq_left']
  refine ⟨trivial, trivial, trivial, ?_, fun rd hrd => ?_⟩
  · exact ((((((Outside.refl base 0 48 s.mem).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _).writeW (by omega) (by omega) (by omega) _).writeW
      (by omega) (by omega) (by omega) _
  · simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
    rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp (disch := decide) only [word_writeW_sep, word_writeW_self]

/-! ## The initial values -/

theorem E_st4 (m : Mem) (base : Addr) {o : Nat} (i : Fin 128) (hi : o = 32 * i.val)
    (w0 w1 w2 w3 : BitVec 64) :
    E (st4 m base o w0 w1 w2 w3) base = Function.update (E m base) i (toFe (val4 w0 w1 w2 w3)) := by
  subst hi
  rw [E_update (st4_outside _ _ (by omega) _ _ _ _), F, fe_st4 _ _ (by omega)]

theorem movs_ok (s : State) :
    WP isa (.block ([.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] : List Instr)) s fun s' =>
      s'.gpr .r12 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .rcx ∧ Keeps [.r12, .rdi] s s' := by
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

theorem setup_eq : setup = loadU ++ (save ++ (([.mov .r12 (.reg .rdi), .mov .rdi (.reg .rcx)] :
    List Instr) ++ (store4 X1 ++ (store4 X3 ++ (([.mov32 .rax (.imm 0), .mov32 .rdx (.imm 1)] :
    List Instr) ++ (stores X2 .rdx .rax .rax .rax ++ (stores Z2 .rax .rax .rax .rax ++
    (stores Z3 .rdx .rax .rax .rax ++ ([.store (sc SWAP) .rax] : List Instr))))))))) := by
  simp only [setup, List.append_assoc]

/-- `setup`: the ladder's initial state, from the u-coordinate at `p`. -/
theorem setup_ok {s : State} {base p : Addr} (hc : s.gpr .rcx = base)
    (hw : (⟨base, 4096⟩ : Region) ∈ s.wr) (hn : base.toNat + 4096 ≤ 2 ^ 64) (hp : s.gpr .rdx = p)
    (hr : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off p d) 8) :
    WP isa (.block setup) s fun s' =>
      Scr s' base ∧ s'.gpr .r12 = s.gpr .rdi ∧
      (∀ r, r ∉ [Reg.rax, .rcx, .rdx, .rdi, .r8, .r9, .r10, .r11, .r12] → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 4096 s.mem s'.mem ∧ Saved base s.gpr s'.mem ∧
      E s'.mem base 2 = toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) ∧
      E s'.mem base 3 = 1 ∧ E s'.mem base 4 = 0 ∧
      E s'.mem base 5 = toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) ∧
      E s'.mem base 6 = 1 ∧ word s'.mem base SWAP = 0 := by
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (loadU_ok s hp hr) fun s₁ ⟨u₁, k₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (save_ok (s := s₁) (base := base) (by rw [k₁.1 _ (by decide)]; exact hc)
    (by rw [k₁.2.2.2]; exact hw)) fun s₂ ⟨g₂, rd₂, wr₂, o₂, sv₂⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (movs_ok s₂) fun s₃ ⟨r12₃, rdi₃, k₃⟩ => ?_
  have hs₃ : Scr s₃ base :=
    ⟨by rw [rdi₃, g₂, k₁.1 _ (by decide), hc], by rw [k₃.2.2.2, wr₂, k₁.2.2.2]; exact hw, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₃ (o := X1) (by decide)) fun s₄ ⟨m₄, g₄, rd₄, wr₄⟩ => ?_
  have hs₄ : Scr s₄ base := ⟨(g₄ _).trans hs₃.rdi, wr₄ ▸ hs₃.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (store4_ok hs₄ (o := X3) (by decide)) fun s₅ ⟨m₅, g₅, rd₅, wr₅⟩ => ?_
  have hs₅ : Scr s₅ base := ⟨(g₅ _).trans hs₄.rdi, wr₅ ▸ hs₄.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (consts_ok s₅) fun s₆ ⟨rax₆, rdx₆, k₆⟩ => ?_
  have hs₆ : Scr s₆ base := hs₅.of_keeps k₆ (by decide)
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs₆ (o := X2) (by decide) .rdx .rax .rax .rax)
    fun s₇ ⟨m₇, g₇, rd₇, wr₇⟩ => ?_
  have hs₇ : Scr s₇ base := ⟨(g₇ _).trans hs₆.rdi, wr₇ ▸ hs₆.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs₇ (o := Z2) (by decide) .rax .rax .rax .rax)
    fun s₈ ⟨m₈, g₈, rd₈, wr₈⟩ => ?_
  have hs₈ : Scr s₈ base := ⟨(g₈ _).trans hs₇.rdi, wr₈ ▸ hs₇.wr, hn⟩
  rw [WP.block_append_iff]
  refine WP.mono (stores_ok hs₈ (o := Z3) (by decide) .rdx .rax .rax .rax)
    fun s₉ ⟨m₉, g₉, rd₉, wr₉⟩ => ?_
  have hs₉ : Scr s₉ base := ⟨(g₉ _).trans hs₈.rdi, wr₉ ▸ hs₈.wr, hn⟩
  refine WP.mono (storeSwap_ok hs₉) fun s' ⟨m', g', rd', wr'⟩ => ?_
  have G : ∀ r, r ∉ [Reg.rax, .rdx] → s'.gpr r = s₃.gpr r := fun r hr => by
    rw [g', g₉, g₈, g₇, k₆.1 r hr, g₅, g₄]
  have G₁ : ∀ r, r ∉ [Reg.r8, .r9, .r10, .r11, .rax] → s₂.gpr r = s.gpr r := fun r hr => by
    rw [g₂, k₁.1 r hr]
  have e' : E s'.mem base = Function.update (E s₉.mem base) 20 (F s'.mem base (32 * 20)) := by
    rw [m']; exact E_update ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  have e₉ := E_st4 (o := Z3) s₈.mem base 6 rfl (s₈.gpr .rdx) (s₈.gpr .rax) (s₈.gpr .rax) (s₈.gpr .rax)
  have e₈ := E_st4 (o := Z2) s₇.mem base 4 rfl (s₇.gpr .rax) (s₇.gpr .rax) (s₇.gpr .rax) (s₇.gpr .rax)
  have e₇ := E_st4 (o := X2) s₆.mem base 3 rfl (s₆.gpr .rdx) (s₆.gpr .rax) (s₆.gpr .rax) (s₆.gpr .rax)
  have e₅ := E_st4 (o := X3) s₄.mem base 5 rfl (s₄.gpr .r8) (s₄.gpr .r9) (s₄.gpr .r10) (s₄.gpr .r11)
  have e₄ := E_st4 (o := X1) s₃.mem base 2 rfl (s₃.gpr .r8) (s₃.gpr .r9) (s₃.gpr .r10) (s₃.gpr .r11)
  rw [← m₉] at e₉; rw [← m₈] at e₈; rw [← m₇] at e₇; rw [← m₅] at e₅; rw [← m₄] at e₄
  have hu : ∀ t : State, (∀ r, r ∉ [Reg.rax, .rdx] → t.gpr r = s₃.gpr r) →
      toFe (val4 (t.gpr .r8) (t.gpr .r9) (t.gpr .r10) (t.gpr .r11)) =
        toFe (Spec.X25519.decodeUCoordinate (Spec.X25519.bytesAt s.mem p 32)) := fun t ht => by
    rw [ht _ (by decide), ht _ (by decide), ht _ (by decide), ht _ (by decide),
      k₃.1 _ (by decide), k₃.1 _ (by decide), k₃.1 _ (by decide), k₃.1 _ (by decide), g₂, u₁]
  have one : toFe (val4 1 0 0 0) = 1 := rfl
  have zero : toFe (val4 0 0 0 0) = 0 := rfl
  have r₈ : s₈.gpr .rdx = 1 ∧ s₈.gpr .rax = 0 := ⟨by rw [g₈, g₇, rdx₆], by rw [g₈, g₇, rax₆]⟩
  have r₇ : s₇.gpr .rax = 0 := by rw [g₇, rax₆]
  have o₃ : Outside base 0 4096 s.mem s₃.mem := by
    rw [k₃.2.1]; exact fun x hx => (o₂.mono (by omega) (by omega) x hx).trans (by rw [k₁.2.1])
  have o' : Outside base 64 4032 s₃.mem s'.mem := by
    rw [m', m₉, m₈, m₇, k₆.2.1, m₅, m₄]
    exact (((((st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)).trans
      ((st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide))).trans
      ((st4_outside _ _ (by decide) _ _ _ _).mono (by decide) (by decide)) |>.trans
      ((writeW_outside _ _ _ (by decide)).mono (by decide) (by decide))
  refine ⟨⟨by rw [g']; exact hs₉.rdi, wr' ▸ hs₉.wr, hn⟩, ?_, fun r hr => ?_, ?_, ?_,
    o₃.trans (o'.mono (by omega) (by omega)), ?_, ?_⟩
  · rw [G _ (by decide), r12₃, G₁ _ (by decide)]
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [G r (by simp [hr.1, hr.2.2.1]), k₃.1 r (by simp [hr.2.2.2.1, hr.2.2.2.2.2.2.2.2]),
      G₁ r (by simp [hr.1, hr.2.2.2.2.1, hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1])]
  · rw [rd', rd₉, rd₈, rd₇, k₆.2.2.1, rd₅, rd₄, k₃.2.2.1, rd₂, k₁.2.2.1]
  · rw [wr', wr₉, wr₈, wr₇, k₆.2.2.2, wr₅, wr₄, k₃.2.2.2, wr₂, k₁.2.2.2]
  · have sv : Saved base s.gpr s₃.mem := by
      rw [k₃.2.1]; intro rd hrd
      rw [sv₂ rd hrd]
      simp only [saved, List.mem_cons, List.not_mem_nil, or_false] at hrd
      rcases hrd with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k₁.1 _ (by decide)
    exact sv.outside o' (by omega)
  · rw [e', e₉, e₈, e₇, k₆.2.1, e₅, e₄]
    simp (config := {decide := true}) only [Function.update_apply, ite_true, ite_false]
    rw [hu s₄ (fun r _ => g₄ r), hu s₃ (fun _ _ => rfl), r₈.1, r₈.2, r₇, rdx₆, rax₆, one, zero]
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    rw [m', word_writeW_self, g₉, r₈.2]

end VG.Proof.X25519.X86_64
