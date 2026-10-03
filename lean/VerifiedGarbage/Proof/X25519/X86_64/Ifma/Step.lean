import VerifiedGarbage.Proof.X25519.X86_64.Ifma.Part2

/-!
# X25519 on x86-64 with AVX512_IFMA: the ladder's loop

The loop invariant (`VInv`): the counter `rbx` counts down to `n`, the lanes
of `ymm0–ymm4` hold the ladder's `(x₂, z₂, x₃, z₃)` after the bits 254 down to
`n`, and `swap` its `swap`; since the loop's start only the registers `rax`,
`rbx`, `rcx`, `rdx`, the vector registers, `swap` and the operand slots
changed.
-/

namespace VG.Proof.X25519.X86_64.Ifma

open VG VG.X86_64 VG.Impl.X25519.X86_64 VG.Impl.X25519.X86_64.Ifma VG.Proof.X25519 VG.Spec.X25519
open VG.Proof.X25519.X86_64 (Scr Outside Outside.mono ofs off word stepPre stepPre_ok mask
  contains_sc ofs_off' cswap_fst cswap_snd writeW_outside)
open VG.Proof.Poly1305.X86_64.Avx2 (xr qw)

/-- The bytes an iteration may change: `swap` and the operand slots. -/
def VFrame (base : Addr) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < 640 ∨ (648 ≤ ofs base x ∧ ofs base x < 1024) ∨ 1504 ≤ ofs base x) → m' x = m x

theorem VFrame.refl (base : Addr) (m : Mem) : VFrame base m m := fun _ _ => rfl

theorem VFrame.trans {base : Addr} {m₁ m₂ m₃ : Mem} (h₁ : VFrame base m₁ m₂) (h₂ : VFrame base m₂ m₃) :
    VFrame base m₁ m₃ := fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem VFrame.of_slots {base : Addr} {m m' : Mem} (h : Outside base 1024 480 m m') : VFrame base m m' :=
  fun x hx => h x (by omega)

theorem VFrame.of_swap {base : Addr} {m m' : Mem} (h : Outside base 640 8 m m') : VFrame base m m' :=
  fun x hx => h x (by omega)

theorem Consts.of_word {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1)
    (w : ∀ d, 1504 ≤ d → d + 8 ≤ 2208 → mq m' base d = mq m base d) : Consts m' base x1 := by
  refine ⟨fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_, fun i hi l hl => ?_,
    fun i hi l hl => ?_, hk.x1, fun l hl => ?_, fun l hl => ?_, fun l hl => ?_⟩
  · rw [w _ (by simp only [KM]; omega) (by simp only [KM]; omega)]; exact hk.km l hl
  · rw [w _ (by simp only [K19]; omega) (by simp only [K19]; omega)]; exact hk.k19 l hl
  · rw [w _ (by simp only [KB0]; omega) (by simp only [KB0]; omega)]; exact hk.kb0 l hl
  · rw [w _ (by simp only [KB1]; omega) (by simp only [KB1]; omega)]; exact hk.kb1 l hl
  · rw [slotv, w _ (by simp only [KA24]; omega) (by simp only [KA24]; omega)]; exact hk.a24 i hi l hl
  · rw [slotv, w _ (by simp only [KX1]; omega) (by simp only [KX1]; omega)]; exact hk.kx1 i hi l hl
  · rw [w _ (by simp only [K13]; omega) (by simp only [K13]; omega)]; exact hk.k13 l hl
  · rw [w _ (by simp only [K26]; omega) (by simp only [K26]; omega)]; exact hk.k26 l hl
  · rw [w _ (by simp only [K39]; omega) (by simp only [K39]; omega)]; exact hk.k39 l hl

theorem Consts.of_frame {m m' : Mem} {base : Addr} {x1 : Nat → Nat} (hk : Consts m base x1)
    (h : VFrame base m m') : Consts m' base x1 :=
  hk.of_word fun d h1 h2 => by
    rw [mq_eq_word, mq_eq_word]
    exact (Mem.readW_congr fun i hi => (h _ (by
      right; right; rw [VG.Proof.X25519.X86_64.ofs_off base (by omega)]; omega)).symm).symm

/-- The loop invariant, with the counter `rbx = n`. -/
structure VInv (base : Addr) (k : Nat) (u : Fe) (x1 : Nat → Nat) (s₀ s : State) (n : Nat) : Prop where
  scr : Scr s base
  gpr : ∀ r, r ∉ [.rax, .rbx, .rcx, .rdx] → s.gpr r = s₀.gpr r
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : VFrame base s₀.mem s.mem
  consts : Consts s.mem base x1
  hx1 : fe5 x1 = u
  swap : word s.mem base SWAP = BitVec.ofNat 64 (ladderAfter k u n).swap
  lim : ∀ l < 4, ∀ i < 5, lanes s 0 l i < 2 ^ 61
  x2 : fe5 (lanes s 0 0) = (ladderAfter k u n).x2
  z2 : fe5 (lanes s 0 1) = (ladderAfter k u n).z2
  x3 : fe5 (lanes s 0 2) = (ladderAfter k u n).x3
  z3 : fe5 (lanes s 0 3) = (ladderAfter k u n).z3

theorem vstep_eq : vstep = stepPre ++ (vsw ++ ((stage1 ++ mul4 OPL) ++ ((stage2 ++ mul4 OPV) ++
    ((stage3 ++ mul4 OPG) ++ ([.alu .test .rbx (.reg .rbx)] : List Instr))))) := by
  simp only [vstep, stepPre, vsw, List.append_assoc, List.cons_append, List.nil_append]

theorem lanes_of_vec {s s' : State} (hx : s'.xmm = s.xmm) (hy : s'.ymmHi = s.ymmHi) (r l i : Nat) :
    lanes s' r l i = lanes s r l i := by
  simp only [lanes, qw, State.lane, hx, hy]

theorem xor2_lt : ∀ l < 4, l ^^^ 2 < 4 := by decide

/-- One iteration: from the state after the bits down to `n + 1` to the state
after the bits down to `n`. -/
theorem vstep_ok {s₀ s : State} {base : Addr} {k : Nat} {u : Fe} {x1 : Nat → Nat} {n : Nat} (hn : n < 255)
    (hbits : ∀ t < 255, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 (bit k t))
    (hi : VInv base k u x1 s₀ s (n + 1)) :
    WP isa (.block vstep) s fun s' => VInv base k u x1 s₀ s' n ∧ s'.zf = some (decide (n = 0)) := by
  have hs := hi.scr
  have hbit : s.mem (off base (BITS + n)) = BitVec.ofNat 8 (bit k n) := by
    rw [hi.mem _ (by rw [ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega)]
    exact hbits n hn
  have hsw := ladderAfter_swap_le k u (n := n + 1) (by omega)
  rw [vstep_eq, WP.block_append_iff]
  refine WP.mono (stepPre_ok hs hn hi.rbx (by have := bit_le k n; omega) (by omega) hbit hi.swap)
    fun s₁ ⟨b₁, m₁, g₁, rd₁, wr₁, mem₁, x₁, y₁⟩ => ?_
  have hs₁ : Scr s₁ base := ⟨(g₁ _ (by decide)).trans hs.rdi, wr₁ ▸ hs.wr, hs.nowrap⟩
  have o₁ : Outside base 640 8 s.mem s₁.mem := by
    rw [mem₁]; exact writeW_outside _ _ _ (by omega)
  have hk₁ := hi.consts.of_frame (VFrame.of_swap o₁)
  rw [WP.block_append_iff]
  refine WP.mono (vsw_wp (scr_ctx hs₁) m₁) fun s₂ ⟨v₂, mm₂, u₂, _⟩ => ?_
  have hs₂ := scr_of hs₁ (vm_gpr v₂) (vm_wr v₂)
  have hk₂ : Consts s₂.mem base x1 := by rw [mm₂]; exact hk₁
  -- the swapped lanes
  have sw₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i =
      lanes s 0 (if decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1) then l ^^^ 2 else l) i :=
    fun l hl i hi' => by
      simp only [lanes, Nat.zero_add] at *
      rw [u₂ l hl i hi']
      exact congrArg _ (by simp only [qw, State.lane, x₁, y₁])
  have lim₂ : ∀ l < 4, ∀ i < 5, lanes s₂ 0 l i < 2 ^ 61 := fun l hl i hi' => by
    rw [sw₂ l hl i hi']; exact hi.lim _ (by split <;> [exact xor2_lt l hl; exact hl]) i hi'
  rw [WP.block_append_iff]
  refine WP.mono (part1_ok hs₂ hk₂ lim₂) fun s₃ ⟨K₃, lim₃, a₃, b₃, c₃, d₃⟩ => ?_
  have hs₃ := scr_of hs₂ K₃.gpr K₃.wr
  have hk₃ := hk₂.of_frame (VFrame.of_slots K₃.mem)
  rw [WP.block_append_iff]
  refine WP.mono (part2_ok hs₃ hk₃ lim₃) fun s₄ ⟨K₄, lim₄, v2₄, v3₄, a₄, b₄, c₄, d₄⟩ => ?_
  have hs₄ := scr_of hs₃ K₄.gpr K₄.wr
  have hk₄ := hk₃.of_frame (VFrame.of_slots K₄.mem)
  rw [WP.block_append_iff]
  refine WP.mono (part3_ok hs₄ hk₄ lim₄) fun s₅ ⟨K₅, lim₅, a₅, b₅, c₅, d₅⟩ => ?_
  have hs₅ := scr_of hs₄ K₅.gpr K₅.wr
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, Option.bind_some,
    Option.some.injEq, exists_eq_left']
  have rbx₅ : s₅.gpr .rbx = BitVec.ofNat 64 n := by rw [K₅.gpr, K₄.gpr, K₃.gpr, vm_gpr v₂, b₁]
  have zf : (BitVec.ofNat 64 n &&& BitVec.ofNat 64 n == 0) = decide (n = 0) := by
    rw [BitVec.and_self]
    rcases Nat.eq_zero_or_pos n with rfl | h
    · rfl
    · rw [decide_eq_false (by omega)]
      apply beq_false_of_ne
      intro h'
      have := congrArg BitVec.toNat h'
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      exact absurd this (by simp; omega)
  -- the field elements
  have fsw : ∀ l < 4, fe5 (lanes s₂ 0 l) =
      fe5 (lanes s 0 (if decide ((ladderAfter k u (n + 1)).swap ^^^ bit k n = 1) then l ^^^ 2 else l)) :=
    fun l hl => fe5_congr fun i hi' => sw₂ l hl i hi'
  have L := ladderAfter_step k u hn
  have F : VFrame base s.mem s₅.mem :=
    (((VFrame.of_swap o₁).trans (by rw [mm₂]; exact VFrame.refl _ _)).trans
      (VFrame.of_slots K₃.mem)).trans ((VFrame.of_slots K₄.mem).trans (VFrame.of_slots K₅.mem))
  have hl5 : ∀ l, lanes (arithFlags s₅ (s₅.gpr .rbx &&& s₅.gpr .rbx) false false) 0 l = lanes s₅ 0 l :=
    fun l => funext fun i => lanes_of_vec rfl rfl 0 l i
  have hsw0 : fe5 (lanes s₂ 0 0) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).x2 (ladderAfter k u (n + 1)).x3).1 := by
    rw [fsw 0 (by decide), cswap_fst]; split <;> simp only [show (0 : Nat) ^^^ 2 = 2 by decide, hi.x2, hi.x3]
  have hsw1 : fe5 (lanes s₂ 0 1) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).z2 (ladderAfter k u (n + 1)).z3).1 := by
    rw [fsw 1 (by decide), cswap_fst]; split <;> simp only [show (1 : Nat) ^^^ 2 = 3 by decide, hi.z2, hi.z3]
  have hsw2 : fe5 (lanes s₂ 0 2) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).x2 (ladderAfter k u (n + 1)).x3).2 := by
    rw [fsw 2 (by decide), cswap_snd]; split <;> simp only [show (2 : Nat) ^^^ 2 = 0 by decide, hi.x2, hi.x3]
  have hsw3 : fe5 (lanes s₂ 0 3) = (cswap ((ladderAfter k u (n + 1)).swap ^^^ bit k n)
      (ladderAfter k u (n + 1)).z2 (ladderAfter k u (n + 1)).z3).2 := by
    rw [fsw 3 (by decide), cswap_snd]; split <;> simp only [show (3 : Nat) ^^^ 2 = 1 by decide, hi.z2, hi.z3]
  refine ⟨⟨⟨by rw [RegUpd.gpr_arithFlags]; exact hs₅.rdi, by rw [RegUpd.wr_arithFlags]; exact hs₅.wr,
    hs₅.nowrap⟩, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, hi.hx1, ?_, lim₅, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [RegUpd.gpr_arithFlags, K₅.gpr, K₄.gpr, K₃.gpr, vm_gpr v₂,
      g₁ r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; grind), hi.gpr r hr]
  · rw [RegUpd.gpr_arithFlags, rbx₅]
  · rw [RegUpd.rd_arithFlags, K₅.rd, K₄.rd, K₃.rd, vm_rd v₂, rd₁, hi.rd]
  · rw [RegUpd.wr_arithFlags, K₅.wr, K₄.wr, K₃.wr, vm_wr v₂, wr₁, hi.wr]
  · rw [RegUpd.mem_arithFlags]; exact hi.mem.trans F
  · rw [RegUpd.mem_arithFlags]; exact hk₄.of_frame (VFrame.of_slots K₅.mem)
  · rw [RegUpd.mem_arithFlags]
    have w₁ : word s₅.mem base SWAP = word s₁.mem base SWAP := by
      have O : Outside base 1024 480 s₂.mem s₅.mem := (K₃.mem.trans K₄.mem).trans K₅.mem
      rw [O.word (by simp only [SWAP]; omega) (by simp only [SWAP]; omega), mm₂]
    rw [w₁, mem₁, L]
    simp only [VG.Proof.X25519.X86_64.word, Mem.readW_writeW_self64]
    rfl
  -- the ladder's formulas
  all_goals try rw [RegUpd.zf_arithFlags, rbx₅, zf]
  all_goals try simp only [hl5]
  all_goals rw [L, ladderStep_eq]
  all_goals simp only []
  · rw [a₅, c₄, a₃, b₃, hsw0, hsw1, Fin.mul_one]
  · rw [b₅, v3₄, v2₄, d₄, a₃, b₃, hsw0, hsw1, Fin.mul_comm _ Spec.X25519.a24]
  · rw [c₅, a₄, c₃, d₃, hsw0, hsw1, hsw2, hsw3, Fin.mul_one]
  · rw [d₅, b₄, c₃, d₃, hsw0, hsw1, hsw2, hsw3, hi.hx1, Fin.mul_comm _ u]

end VG.Proof.X25519.X86_64.Ifma
