import VerifiedGarbage.Proof.Ecdsa.X86_64.Layout

/-!
# ECDSA on x86-64: the setup

`Cfg.setup` saves the callee-saved registers at the start of the working
space (`setupSaves_ok`), keeps `out` in `r14` and moves the working space's
base to `rdi` (`setupMovs_ok`), reads `k`, `d` and the hash big-endian into
their slots (`setupLoad_ok`, once each), stores the constants
(`setupConsts_ok`, by induction on the list) and sets the flag to all ones:
`setup_ok`, the state `SetupPost` describes.
-/

namespace VG.Proof.Ecdsa.X86_64

open VG VG.X86_64 VG.Impl.Mont.X86_64 VG.Impl.Weierstrass.X86_64 VG.Impl.Ecdsa.X86_64
open VG.Proof.Mont.X86_64 VG.Proof.Weierstrass.X86_64 VG.Proof.Weierstrass Spec.Weierstrass

/-! ## Saving the callee-saved registers -/

theorem setupSaved_lt : ∀ rd ∈ Cfg.saved, rd.2 + 8 ≤ 48 := by decide

theorem setupSaves_ok {s : State} {base : Addr} (hb : s.gpr .r8 = base)
    (hw : (⟨base, size⟩ : Region) ∈ s.wr) :
    WP isa (.block (Spill.saveCode .r8 Cfg.saved)) s fun s' =>
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ Outside base 0 48 s.mem s'.mem ∧
      Spill.Saved s'.mem base s.gpr Cfg.saved := by
  refine WP.mono (Spill.save_ok .r8 Cfg.saved s fun p hp => ?_) fun s' ⟨hg, hrd, hwr, hm⟩ =>
    ⟨hg, hrd, hwr, ?_, ?_⟩
  · have := setupSaved_lt p hp
    have hsz : size = 8192 := rfl
    rw [hb]; exact ⟨_, hw, Offset.contains_base base (by omega) (by omega)⟩
  · rw [hm, hb]
    intro x hx
    refine Spill.saveMem_frame_base _ _ _ _ setupSaved_lt (by decide) x fun r hr hx' => ?_
    rw [List.mem_singleton.mp hr] at hx'
    simp only [Region.Contains, ofs] at hx hx'
    omega
  · rw [hm, hb]; exact Spill.saveMem_saved _ _ _ _ (by decide)

/-! ## `out` to `r14`, the working space to `rdi` -/

theorem setupMovs_ok (s : State) :
    WP isa (.block ([.mov .r14 (.reg .rdi), .mov .rdi (.reg .r8)] : List Instr)) s fun s' =>
      s'.gpr .r14 = s.gpr .rdi ∧ s'.gpr .rdi = s.gpr .r8 ∧ KeepRegs [.r14, .rdi] s s' ∧
      s'.mem = s.mem := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, RegUpd.gpr_setReg,
    ite_true, ite_false, reduceCtorEq, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, ⟨fun r hr => ?_, rfl, rfl⟩, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  simp only [RegUpd.gpr_setReg, hr.1, hr.2, ite_false]

/-! ## Reading `k`, `d` and the hash -/

/-- The `8 n` bytes at `p` (readable, outside the working space, and so
unchanged since `s`) to slot `i`. -/
theorem setupLoad_ok {c : Cfg} (hc : CfgOk c) {s t : State} {base p : Addr} {src : Reg} {i : Nat}
    (hs : Scr t base size) (hsrc : src ≠ .rax) (hi : i < 45) (hp : t.gpr src = p)
    (hin : (⟨p, 8 * c.n⟩ : Region) ∈ t.rd ++ t.wr)
    (hd : Region.Disjoint ⟨p, 8 * c.n⟩ ⟨base, size⟩) (ho : Outside base 0 size s.mem t.mem) :
    WP isa (.block (loadBE c.n (c.sl i) src)) t fun t' =>
      wordsVal t'.mem base (c.sl i) c.n = ofBytes (Spec.Ecdsa.bytesAt s.mem p (8 * c.n)) ∧
      KeepRegs [.rax] t t' ∧ Outside base (c.sl i) (8 * c.n) t.mem t'.mem := by
  have hl := sl_le c hc.n7 hi
  have h7 := hc.n7
  have hsz : size = 8192 := rfl
  refine WP.mono (loadBE_ok hs hsrc hl (by rw [hp]; exact inRegions_words hin (by omega))
    (by rw [hp]; exact hd.sub_right (Offset.sub_base base hl))) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have hb : Spec.Ecdsa.bytesAt t.mem p (8 * c.n) = Spec.Ecdsa.bytesAt s.mem p (8 * c.n) :=
    List.map_congr_left fun j hj =>
      keep_of_disjoint' ho hd (by decide) (List.mem_range.mp hj) (by omega)
  rw [e, hp, hb]

/-! ## The constants -/

/-- The constants of `l`, apart slots below `17`, each in its slot; only their
slots change. -/
theorem setupConsts_ok {c : Cfg} (hc : CfgOk c) {base : Addr} : ∀ (l : List (Nat × Nat)) {t : State},
    Scr t base size → (∀ ix ∈ l, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n)) → (l.map Prod.fst).Nodup →
    WP isa (.block (l.flatMap (fun (i, x) => setConst c.n (c.sl i) x))) t fun t' =>
      (∀ ix ∈ l, wordsVal t'.mem base (c.sl ix.1) c.n = ix.2) ∧ KeepRegs [.rax] t t' ∧
      Unch base (l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem
  | [], _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, ⟨fun _ _ => rfl, rfl, rfl⟩,
      Unch.refl _ _ _⟩
  | (i, x) :: l, t, hs, hb, hnd => by
    rw [List.flatMap_cons, WP.block_append_iff]
    have hi := hb (i, x) List.mem_cons_self
    have hl := sl_le c hc.n7 (i := i) (by omega)
    have hsz : size = 8192 := rfl
    refine WP.mono (setConst_ok hs hl hi.2) fun t₁ ⟨e₁, k₁, O₁⟩ => ?_
    have hs₁ := hs.of_keepRegs k₁ (by decide)
    rw [List.map_cons, List.nodup_cons] at hnd
    refine WP.mono (setupConsts_ok hc l hs₁ (fun ix h => hb ix (List.mem_cons_of_mem _ h)) hnd.2)
      fun t' ⟨e', k', U'⟩ => ⟨fun ix h => ?_, k₁.trans k',
        show Unch base ([(c.sl i, 8 * c.n)] ++ l.map fun ix => (c.sl ix.1, 8 * c.n)) t.mem t'.mem from
          O₁.unch.trans U'⟩
    rcases List.mem_cons.mp h with rfl | h
    · refine (U'.wordsVal (fun w hw => ?_) (by dsimp only; omega)).trans e₁
      obtain ⟨jy, hjy, rfl⟩ := List.mem_map.mp hw
      exact sl_apart c fun heq => hnd.1 (heq ▸ List.mem_map_of_mem hjy)
    · exact e' ix h

theorem consts_fst (c : Cfg) :
    c.consts.map Prod.fst = [0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16] := rfl

theorem consts_nodup (c : Cfg) : (c.consts.map Prod.fst).Nodup := by
  rw [consts_fst]; decide

theorem consts_bounds {c : Cfg} (hc : CfgOk c) :
    ∀ ix ∈ c.consts, ix.1 < 17 ∧ ix.2 < 2 ^ (64 * c.n) := by
  intro ix h
  refine ⟨?_, ?_⟩
  · have := List.mem_map_of_mem (f := Prod.fst) h
    rw [consts_fst] at this
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this
    omega
  · have hp0 : 0 < c.C.p := by have := hc.p_ge; omega
    have hn0 : 0 < c.C.n := by have := hc.n_ge; omega
    have hR : 1 < 2 ^ (64 * c.n) := Nat.one_lt_two_pow (by have := hc.n0; omega)
    have hm : ∀ x, c.mont x < 2 ^ (64 * c.n) := fun x =>
      Nat.lt_trans (Nat.mod_lt (x * c.R) hp0) hc.p_lt
    have hn : ∀ x, x % c.C.n < 2 ^ (64 * c.n) := fun x => Nat.lt_trans (Nat.mod_lt x hn0) hc.n_lt
    have hp2 : c.C.p - 2 < 2 ^ (64 * c.n) := by have := hc.p_lt; omega
    have hn2 : c.C.n - 2 < 2 ^ (64 * c.n) := by have := hc.n_lt; omega
    simp only [Cfg.consts, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact hc.p_lt
    · exact hc.n_lt
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hR
    · exact hm 1
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hm _
    · exact hn _
    · exact hn _
    · exact hp2
    · exact hn2
    · exact Nat.lt_trans Nat.one_pos hR
    · exact hm 1
    · exact Nat.lt_trans Nat.one_pos hR

/-! ## The flag -/

theorem setupFlag_ok {c : Cfg} (hc : CfgOk c) {t : State} {base : Addr} (hs : Scr t base size) :
    WP isa (.block (setConst 1 (c.sl FLAG) (2 ^ 64 - 1))) t fun t' =>
      word t'.mem base (c.sl FLAG) = BitVec.allOnes 64 ∧ KeepRegs [.rax] t t' ∧
      Outside base (c.sl FLAG) (8 * 1) t.mem t'.mem := by
  have hl := sl_le c hc.n7 (i := FLAG) (by decide)
  have := hc.n0
  refine WP.mono (setConst_ok hs (by omega) (by decide)) fun t' ⟨e, k, O⟩ => ⟨?_, k, O⟩
  have e' : (word t'.mem base (c.sl FLAG)).toNat = 2 ^ 64 - 1 := by
    simp only [wordsVal, Nat.mul_zero, Nat.add_zero] at e
    exact e
  exact BitVec.eq_of_toNat_eq (by rw [e', BitVec.toNat_allOnes])

/-! ## The whole setup -/

theorem setup_eq (c : Cfg) : c.setup = Spill.saveCode .r8 Cfg.saved ++
    (([.mov .r14 (.reg .rdi), .mov .rdi (.reg .r8)] : List Instr) ++
    (loadBE c.n (c.sl K) .rcx ++ (loadBE c.n (c.sl D) .rsi ++ (loadBE c.n (c.sl E) .rdx ++
    (c.consts.flatMap (fun (i, x) => setConst c.n (c.sl i) x) ++
    setConst 1 (c.sl FLAG) (2 ^ 64 - 1)))))) := by
  simp only [Cfg.setup, List.append_assoc]; rfl

theorem setup_ok {c : Cfg} (hc : CfgOk c) {s : State} (hp : Pre c s) :
    WP isa (.block c.setup) s (SetupPost c s (s.gpr .r8)) := by
  have h7 := hc.n7
  have h0 := hc.n0
  have hsz : size = 8192 := rfl
  have hw : (⟨s.gpr .r8, size⟩ : Region) ∈ s.wr := by rw [hp.wr]; simp
  rw [setup_eq, WP.block_append_iff]
  refine WP.mono (setupSaves_ok rfl hw) fun s₁ ⟨g₁, rd₁, wr₁, O₁, sv₁⟩ => ?_
  rw [WP.block_append_iff]
  refine WP.mono (setupMovs_ok s₁) fun s₂ ⟨r14₂, rdi₂, k₂, m₂⟩ => ?_
  have hs₂ : Scr s₂ (s.gpr .r8) size :=
    ⟨by rw [rdi₂, g₁], by rw [k₂.wr, wr₁]; exact hw, hp.sc_fit⟩
  have G₂ : ∀ r, r ≠ .r14 → r ≠ .rdi → s₂.gpr r = s.gpr r := fun r h₁ h₂ => by
    rw [k₂.gpr r (by simp [h₁, h₂]), g₁]
  have RD₂ : s₂.rd ++ s₂.wr = s.rd ++ s.wr := by rw [k₂.rd, k₂.wr, rd₁, wr₁]
  have O₂ : Outside (s.gpr .r8) 0 size s.mem s₂.mem := by
    rw [m₂]; exact O₁.mono (Nat.le_refl _) (by omega)
  have hK : c.sl K = 64 + 8 * c.n * 31 := rfl
  have hD : c.sl D = 64 + 8 * c.n * 32 := rfl
  have hE : c.sl E = 64 + 8 * c.n * 33 := rfl
  have hF : c.sl FLAG = 64 + 8 * c.n * 44 := rfl
  have h17 : c.sl 17 = 64 + 8 * c.n * 17 := rfl
  -- `k`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₂ (by decide) (i := K) (by decide)
    (G₂ _ (by decide) (by decide)) (by rw [RD₂, hp.rd]; simp) hp.k_sc O₂)
    fun s₃ ⟨e₃, k₃, O₃⟩ => ?_
  have hs₃ := hs₂.of_keepRegs k₃ (by decide)
  -- `d`
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₃ (by decide) (i := D) (by decide)
    (by rw [k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₃.rd, k₃.wr, RD₂, hp.rd]; simp) hp.d_sc
    (O₂.trans (O₃.mono (Nat.zero_le _) (by omega)))) fun s₄ ⟨e₄, k₄, O₄⟩ => ?_
  have hs₄ := hs₃.of_keepRegs k₄ (by decide)
  -- the hash
  rw [WP.block_append_iff]
  refine WP.mono (setupLoad_ok hc (s := s) hs₄ (by decide) (i := E) (by decide)
    (by rw [k₄.gpr _ (by decide), k₃.gpr _ (by decide)]; exact G₂ _ (by decide) (by decide))
    (by rw [k₄.rd, k₄.wr, k₃.rd, k₃.wr, RD₂, hp.rd]; simp) hp.digest_sc
    ((O₂.trans (O₃.mono (Nat.zero_le _) (by omega))).trans (O₄.mono (Nat.zero_le _) (by omega))))
    fun s₅ ⟨e₅, k₅, O₅⟩ => ?_
  have hs₅ := hs₄.of_keepRegs k₅ (by decide)
  -- the constants
  rw [WP.block_append_iff]
  refine WP.mono (setupConsts_ok hc c.consts hs₅ (consts_bounds hc) (consts_nodup c))
    fun s₆ ⟨e₆, k₆, U₆⟩ => ?_
  have hs₆ := hs₅.of_keepRegs k₆ (by decide)
  have O₆ : Outside (s.gpr .r8) (c.sl 0) (8 * c.n * 17) s₅.mem s₆.mem := U₆.outside fun w hw => by
    obtain ⟨ix, hix, rfl⟩ := List.mem_map.mp hw
    have := sl_lt c (consts_bounds hc ix hix).1
    have h0' : c.sl 0 = 64 := by rw [sl_eq]; omega
    have : c.sl 0 ≤ c.sl ix.1 := by rw [h0', sl_eq]; omega
    exact ⟨this, by omega⟩
  have hsl0 : c.sl 0 = 64 := by rw [sl_eq]; omega
  -- the flag
  refine WP.mono (setupFlag_ok hc hs₆) fun s' ⟨f', k', O'⟩ => ?_
  have K₃ : KeepRegs [.rax] s₂ s' := ((((k₃.trans k₄).trans k₅).trans k₆).trans k')
  -- Everything after the movs writes only in `[64, size)`.
  have Ol : Outside (s.gpr .r8) 64 (size - 64) s₂.mem s'.mem :=
    ((((O₃.mono (by omega) (by omega)).trans (O₄.mono (by omega) (by omega))).trans
      (O₅.mono (by omega) (by omega))).trans (O₆.mono (by omega) (by omega))).trans
      (O'.mono (by omega) (by omega))
  refine ⟨hs₆.of_keepRegs k' (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun ix hix => ?_, f'⟩
  · rw [K₃.gpr _ (by decide), r14₂, g₁]
  · refine ⟨fun r hr => ?_, by rw [K₃.rd, k₂.rd, rd₁], by rw [K₃.wr, k₂.wr, wr₁]⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    rw [K₃.gpr r (by simp [hr.1]), G₂ r hr.2.2 hr.2.1]
  · exact (O₂.trans (Ol.mono (Nat.zero_le _) (by omega))).unch
  · intro rd hrd
    have := setupSaved_lt rd hrd
    exact (Ol.word (d := rd.2) (by omega) (by omega)).trans
      ((congrArg (fun m => Mem.readW m _ 64) m₂).trans (sv₁ rd hrd))
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega),
      O₅.wordsVal (by omega) (by omega), O₄.wordsVal (by omega) (by omega), e₃]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega),
      O₅.wordsVal (by omega) (by omega), e₄]
  · show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), O₆.wordsVal (by omega) (by omega), e₅]
  · have := sl_lt c (consts_bounds hc ix hix).1
    have := sl_le c hc.n7 (i := 17) (by decide)
    show wordsVal s'.mem _ _ _ = _
    rw [O'.wordsVal (by omega) (by omega), e₆ ix hix]

end VG.Proof.Ecdsa.X86_64
