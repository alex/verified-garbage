import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Sha1.X86_64.ShaNi.Spec
import VerifiedGarbage.Impl.Sha1.X86_64.ShaNi
import VerifiedGarbage.Proof.Sha1.X86_64.Compress

/-!
# SHA-1 compression function on x86-64 with the SHA extensions

Untrusted: everything here is checked by Lean. `compress_verified` proves
`Impl.Sha1.X86_64.ShaNi.compress` against the same contract as the scalar
`vg_sha1_compress`, reusing its precondition (`Pre`) and block lemmas.
-/

namespace VG.Proof.Sha1.X86_64.ShaNi

open VG VG.X86_64 VG.Impl.Sha1.X86_64.ShaNi
open VG.Spec.Sha1 (HashValue Word Block W stateAt blockAt compressBlocks compress)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The registers of a group of four rounds are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7, .xmm8, .xmm9].Nodup := by
  simp only [msg]
  have := Nat.mod_lt n (show 4 > 0 by omega)
  rw [show (n + 1) % 4 = (n % 4 + 1) % 4 by omega, show (n + 2) % 4 = (n % 4 + 2) % 4 by omega,
    show (n + 3) % 4 = (n % 4 + 3) % 4 by omega]
  generalize n % 4 = c at *
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide

/-! ## Four rounds -/

theorem rounds4_ok (n : Nat) (s : State) (a x q : BitVec 128)
    (h0 : s.xmm .xmm0 = a) (h1 : s.xmm .xmm1 = x) (hq : s.xmm (msg n) = q) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = sha1Rnds4 a (XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x q)
        (BitVec.ofNat 8 (n / 5)) ∧
      s'.xmm .xmm1 = a ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4]
  generalize msg n = y at *
  generalize (if n = 0 then XBinOp.paddd else XBinOp.sha1nexte) = op
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, ite_false, hd, h0, h1, hq, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h0 h1 h2 => by simp [h0, h1, h2], trivial⟩

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 2)) = c)
    (hd' : s.xmm (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = sha1Msg2 (XBinOp.eval .pxor (XBinOp.eval .sha1msg1 a b) c) d ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 4 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, ite_true, ite_false, hd'', ha, hb, hc, hd',
    Option.some.injEq, exists_eq_left']
  exact ⟨rfl, fun r h0 => by simp [h0], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) (s.xmm .xmm7) ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd'' := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd''
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.load128, ea_at, hin, ite_true, ite_false, hd'',
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 => by simp [h0], trivial⟩

/-- `msg k` for the three registers other than `msg n` that hold schedule words. -/
theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

theorem msg_other (n : Nat) (r : XReg) (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7 ∨ r = .xmm8 ∨
    r = .xmm9) : msg n ≠ r := by
  have hd := msg_nodup n
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

/-- What `xmm1` holds before rounds `4n …`: for `n = 0`, `E` and zeros; after
that, `ABCD` of four rounds before, whose `A` rotated left by 30 is `E`. -/
def ECarry (n : Nat) (v : HashValue) (x : BitVec 128) : Prop :=
  if n = 0 then x = eReg v else (dword x 3).rotateLeft 30 = v[4]

/-- The value added to rounds `4n … 4n+3`: `W₄ₙ + E`, then `W₄ₙ₊₁ … W₄ₙ₊₃`. -/
theorem wk_eq (M : Block) (n : Nat) (v : HashValue) (x : BitVec 128) (hx : ECarry n v x) :
    XBinOp.eval (if n = 0 then .paddd else .sha1nexte) x (quad M n) =
      ofDwords (W M (4 * n + 3)) (W M (4 * n + 2)) (W M (4 * n + 1)) (W M (4 * n) + v[4]) := by
  by_cases h : n = 0
  · subst h
    simp only [ECarry, ite_true] at hx
    simp only [ite_true, hx, paddd_e]
  · simp only [ECarry, h, ite_false] at hx
    simp only [h, ite_false, nexte_e, hx]

theorem rounds_four (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) :
    Spec.Sha1.rounds H M (4 * (n + 1)) =
      hw4 (n / 5) (Spec.Sha1.rounds H M (4 * n)) (W M (4 * n)) (W M (4 * n + 1)) (W M (4 * n + 2))
        (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ,
    round_hw _ _ (by omega), round_hw _ _ (by omega), round_hw _ _ (by omega), round_hw _ _ (by omega),
    show (4 * n) / 20 = n / 5 by omega, show (4 * n + 1) / 20 = n / 5 by omega,
    show (4 * n + 2) / 20 = n / 5 by omega, show (4 * n + 3) / 20 = n / 5 by omega]
  rfl

theorem rounds4_step (H : HashValue) (M : Block) {n : Nat} (hn : n < 20) (s : State)
    (h0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n)))
    (h1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)) (hq : s.xmm (msg n) = quad M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * (n + 1))) ∧
      ECarry (n + 1) (Spec.Sha1.rounds H M (4 * (n + 1))) (s'.xmm .xmm1) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ _ h0 rfl hq) fun s' ⟨e0, e1, hx, hg, hm, hrd, hwr⟩ => ?_
  rw [wk_eq M n _ _ h1, rnds4_eq _ (by omega)] at e0
  refine ⟨by rw [e0, rounds_four H M hn], ?_, hx, hg, hm, hrd, hwr⟩
  simp only [ECarry, Nat.add_one_ne_zero, ite_false, e1, abcd, dword_ofDwords_3]
  rw [rounds_four H M hn, hw4_e]

theorem ofInt_natCast' (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Reversing the bytes of a register reverses the order of its doublewords
and the bytes of each. -/
theorem pshufb_rev_bytes (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask = ofBytes fun j => byte a (15 - j) := by
  simp only [XBinOp.eval, ofBytes, bswapMask]
  rfl

theorem pshufb_rev (a : BitVec 128) :
    XBinOp.eval .pshufb a bswapMask =
      ofDwords (bswap32 (dword a 3)) (bswap32 (dword a 2)) (bswap32 (dword a 1)) (bswap32 (dword a 0)) := by
  rw [pshufb_rev_bytes]
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  obtain ⟨k, r, hk, hr, rfl⟩ : ∃ k r, k < 16 ∧ r < 8 ∧ i = 8 * k + r :=
    ⟨i / 8, i % 8, by omega, by omega, by omega⟩
  rw [getLsbD_ofBytes _ hk hr, show 8 * k + r = 32 * (k / 4) + (8 * (k % 4) + r) by omega,
    getLsbD_ofDwords_block _ _ _ _ (by omega) (by omega)]
  simp only [getLsbD_bswap32_block _ (Nat.mod_lt k (by decide : 4 > 0)) hr]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
    k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15) with
    h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
  simp (disch := omega) only [↓reduceIte, Nat.reduceSub, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff,
    Nat.reduceAdd, Nat.reduceMul, ← Nat.add_assoc, byte, dword, BitVec.getLsbD_extractLsb',
    decide_eq_true, Bool.true_and]

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap32 (m.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) bswapMask = quad M n := by
  rw [pshufb_rev]
  have e : ∀ j, j < 4 → bswap32 (dword (m.readW (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) j) =
      W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega)]
    refine congrArg (fun a => bswap32 (m.readW a 32)) ?_
    simp only [ofInt_natCast']
    bv_omega
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rfl

/-- What holds after rounds `0 … 4n-1` of a block `M`, from the state `sB` at its start. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (Spec.Sha1.rounds H M (4 * n))
  x1 : ECarry n (Spec.Sha1.rounds H M (4 * n)) (s.xmm .xmm1)
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad M k
  keep : ∀ r, r = .xmm7 ∨ r = .xmm8 ∨ r = .xmm9 → s.xmm r = sB.xmm r
  gpr : s.gpr = sB.gpr
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_ok (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hmask : sB.xmm .xmm7 = bswapMask)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ t : Nat, t < 16 →
      bswap32 (sB.mem.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t)
    (h0 : sB.xmm .xmm0 = abcd H) (h1 : sB.xmm .xmm1 = eReg H) :
    ∀ n ≤ 20, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h0, by simp only [ECarry, ite_true]; exact h1,
      fun _ h => absurd h (by omega), fun _ _ => rfl, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := by rw [hs.gpr, hrsi]
    -- The schedule: `msg n` gets `quad M n`; nothing else changes.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad M n ∧ (∀ r, r ≠ msg n → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi, hs.mem, hs.keep .xmm7 (.inl rfl), hmask]
        exact load_quad M sB.mem bp hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        refine WP.mono (schedule_hi (i + 4) (by omega) s (quad M i) (quad M (i + 1)) (quad M (i + 2))
          (quad M (i + 3)) ?_ ?_ ?_ ?_) fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [msg_add4]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 4 + 1 = i + 1 + 4 by omega, msg_add4]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 4 + 2 = i + 2 + 4 by omega, msg_add4]; exact hs.msgs (i + 2) (by omega) (by omega)
        · rw [show i + 4 + 3 = i + 3 + 4 by omega, msg_add4]; exact hs.msgs (i + 3) (by omega) (by omega)
        · rw [e]; exact schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o0 := msg_other n .xmm0 (by simp)
    have o1 := msg_other n .xmm1 (by simp)
    refine WP.mono (rounds4_step H M (n := n) (by omega) s₁ (by rw [hx₁ _ (Ne.symm o0)]; exact hs.x0)
      (by rw [hx₁ _ (Ne.symm o1)]; exact hs.x1) hq)
      fun s₂ ⟨e0, e1, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e0, e1, fun k hk hk' => ?_, fun r hr => ?_, by rw [hg₂, hg₁, hs.gpr], by rw [hm₂, hm₁, hs.mem],
      by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · have n0 := msg_other k .xmm0 (by simp)
      have n1 := msg_other k .xmm1 (by simp)
      have n2 := msg_other k .xmm2 (by simp)
      rw [hx₂ _ n0 n1 n2]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega))]
        exact hs.msgs k (by omega) (by omega)
    · have := hr
      rcases hr with rfl | rfl | rfl <;>
      · rw [hx₂ _ (by decide) (by decide) (by decide), hx₁ _ (Ne.symm (msg_other n _ (by simp)))]
        exact hs.keep _ (by simp)

/-! ## The prologue and the epilogue -/

theorem stateAt_lo (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j = (stateAt m p)[j] := by
  rw [dword_readW _ _ hj]; simp [stateAt]

theorem stateAt_e (m : Mem) (p : Addr) :
    dword (m.readW (p + BitVec.ofInt 64 ((4 : Nat) : Int)) 128) 3 = (stateAt m p)[4] := by
  rw [dword_readW _ _ (by decide)]
  simp only [stateAt, Vector.getElem_ofFn]
  refine congrArg (fun a => m.readW a 32) ?_
  simp only [ofInt_natCast']
  bv_omega

theorem getLsbD_zero32 (i : Nat) : (0 : Word).getLsbD i = false := by simp

theorem shift_e (x : BitVec 128) :
    XShiftOp.eval .pslldq (XShiftOp.eval .psrldq x 12) 12 = ofDwords 0 0 0 (dword x 3) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e : min (12 : BitVec 8).toNat 16 * 8 = 96 := rfl
  simp only [XShiftOp.eval, e, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_dword]
  rcases (by omega : i < 96 ∨ 96 ≤ i) with h | h
  · simp only [h, decide_true, Bool.not_true, Bool.and_false, Bool.false_and, getLsbD_zero32]
    rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96)) with h' | h' | h' <;>
    simp (disch := omega) only [ite_eq_left, ite_eq_right]
  · simp (disch := omega) only [hi, show ¬ i < 96 by omega, show ¬ i < 32 by omega,
      show ¬ i - 32 < 32 by omega, show ¬ i - 32 - 32 < 32 by omega, show i - 32 - 32 - 32 = i - 96 by omega,
      show i - 96 < 32 by omega, decide_true, decide_false, Bool.not_false, Bool.true_and, ite_false]

/-- `B, C, D, E` from `A, B, C, D` and `E`. -/
theorem por_e (a b c d e : Word) :
    XBinOp.eval .por (XShiftOp.eval .psrldq (ofDwords a b c d) 4) (ofDwords 0 0 0 e) = ofDwords b c d e := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have e32 : min (4 : BitVec 8).toNat 16 * 8 = 32 := rfl
  simp only [XBinOp.eval, XShiftOp.eval, e32, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight, getLsbD_ofDwords,
    getLsbD_zero32]
  rcases (by omega : i < 32 ∨ (32 ≤ i ∧ i < 64) ∨ (64 ≤ i ∧ i < 96) ∨ 96 ≤ i) with h | h | h | h <;>
  simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.or_false]
  · exact congrArg _ (by omega)
  · exact congrArg _ (by omega)
  · exact congrArg _ (by omega)
  · rw [BitVec.getLsbD_of_ge d _ (by omega), Bool.false_or]

theorem shufDwords_1b (a : BitVec 128) :
    shufDwords a 0x1b = ofDwords (dword a 3) (dword a 2) (dword a 1) (dword a 0) := rfl

/-- The hash value, loaded as `ABCD` and `E`. -/
theorem load_ok (s : State)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((4 : Nat) : Int)) 16) :
    WP isa (.block (load ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s fun s' =>
      s'.xmm .xmm0 = abcd (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm1 = eReg (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm7 = bswapMask ∧
      s'.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [load, const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags,
    isa, State.setXmm, State.setReg, State.load128, ea_at, hlo, hhi, ite_true, ite_false, movq_const,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, fun r hr => by simp [hr], trivial⟩
  · rw [shufDwords_1b, stateAt_lo _ _ (show 0 < 4 by decide), stateAt_lo _ _ (show 1 < 4 by decide),
      stateAt_lo _ _ (show 2 < 4 by decide), stateAt_lo _ _ (show 3 < 4 by decide)]
    rfl
  · rw [shift_e, stateAt_e]; rfl

/-- The hash value after storing `x` at `p + 4` and `y` at `p`. -/
theorem stateAt_store (m : Mem) (p : Addr) (x y : BitVec 128) :
    stateAt ((m.writeW (p + BitVec.ofInt 64 ((4 : Nat) : Int)) x).writeW
      (p + BitVec.ofInt 64 ((0 : Nat) : Int)) y) p =
      #v[dword y 0, dword y 1, dword y 2, dword y 3, dword x 3] := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast']
  by_cases hlo : j < 4
  · rw [show p + BitVec.ofNat 64 (4 * j) = p + BitVec.ofNat 64 0 + BitVec.ofNat 64 (4 * j) by bv_omega,
      readW_writeW128 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · obtain rfl : j = 4 := by omega
    rw [Mem.readW_writeW_sep (fun a h₁ h₂ => by bv_omega) (by decide),
      show p + BitVec.ofNat 64 (4 * 4) = p + BitVec.ofNat 64 4 + BitVec.ofNat 64 (4 * 3) by bv_omega,
      readW_writeW128 _ _ _ (by omega)]
    rfl

/-- `ABCD` and `E`, stored back as the hash value. -/
theorem store_ok (s : State) (v : HashValue) (h0 : s.xmm .xmm0 = abcd v) (h1 : s.xmm .xmm1 = eReg v)
    (hlo : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hhi : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((4 : Nat) : Int)) 16) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW (s.gpr .rdi + BitVec.ofInt 64 ((4 : Nat) : Int)) x).writeW
        (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) y) ∧
      stateAt s'.mem (s.gpr .rdi) = v ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [store]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.store128, ea_at, hlo, hhi, ite_true, ite_false, h0, h1, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, trivial⟩
  rw [stateAt_store]
  simp only [shufDwords_1b, abcd, eReg, dword_ofDwords_0, dword_ofDwords_1, dword_ofDwords_2,
    dword_ofDwords_3, por_e]
  apply Vector.ext
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The loop over the blocks -/

open VG.Proof.Sha1.X86_64 (Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' toNat_ofNat_lt satState)

theorem Pre.in_blk16 {s₀ : State} (hp : Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [ofInt_natCast', show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) by simp only [blkAddr]; bv_omega]
  exact contains_offset (by omega) (by omega)

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x0 : s.xmm .xmm0 = abcd (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  x1 : s.xmm .xmm1 = eReg (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x7 : s.xmm .xmm7 = bswapMask
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have h₁ : WP isa (.block [.xop (.bin .movdqa .xmm8 .xmm0), .xop (.bin .movdqa .xmm9 .xmm1)]) s
      fun s₁ => s₁.xmm .xmm8 = s.xmm .xmm0 ∧ s₁.xmm .xmm9 = s.xmm .xmm1 ∧
        (∀ r, r ≠ .xmm8 → r ≠ .xmm9 → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      isa, State.setXmm, ite_true, ite_false, eval_movdqa, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, fun r h8 h9 => by simp [h8, h9], trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e8, e9, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hmem₁ : s₁.mem = s₀.mem := hm₁.trans hL.mem
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.rsi])
    (by rw [hx₁ _ (by decide) (by decide), hL.x7])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    (fun t ht => by rw [hmem₁]; exact blk_word i t ht)
    (by rw [hx₁ _ (by decide) (by decide), hL.x0]) (by rw [hx₁ _ (by decide) (by decide), hL.x1])
    20 (Nat.le_refl _)) fun s₂ hR => ?_)
  have k8 : s₂.xmm .xmm8 = abcd (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [hR.keep .xmm8 (by simp), e8, hL.x0]
  have k9 : s₂.xmm .xmm9 = eReg (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [hR.keep .xmm9 (by simp), e9, hL.x1]
  have hx0 := hR.x0
  have hx1 : (dword (s₂.xmm .xmm1) 3).rotateLeft 30 = (Spec.Sha1.rounds (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
      (blk s₀ i) (4 * 20))[4] := by
    have := hR.x1; simpa [ECarry] using this
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have h₃ : WP isa (.block [.xop (.bin .paddd .xmm0 .xmm8), .xop (.bin .sha1nexte .xmm1 .xmm9),
      .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]) s₂ fun s₃ =>
      s₃.xmm .xmm0 = abcd (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm1 = eReg (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm7 = s₂.xmm .xmm7 ∧
      s₃.gpr .rsi = s₂.gpr .rsi + 64 ∧ s₃.gpr .rdx = s₂.gpr .rdx - 1 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s₃.gpr r = s₂.gpr r) ∧
      s₃.zf = some (s₂.gpr .rdx - 1 == 0) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.setReg, ite_true,
      ite_false, hx0, k8, k9, paddd_abcd, nexte_eReg _ _ _ hx1, e1, e64, Option.some.injEq,
      Option.bind_some, exists_eq_left']
    exact ⟨by rw [compressBlocks_succ]; rfl, by rw [compressBlocks_succ]; rfl, trivial, trivial, trivial,
      fun r h1 h2 => by simp [h1, h2], trivial⟩
  refine WP.mono h₃ fun s₃ ⟨f0, f1, f7, frsi, frdx, fg, fzf, fm, frd, fwr⟩ => ?_
  have g₂ : s₂.gpr = s.gpr := by rw [hR.gpr, hg₁]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [g₂, hL.rdx]
    have := (s₀.gpr .rdx).isLt
    bv_omega
  have hcommon : Common s₀ (i + 1) s₃ :=
    ⟨f0, f1, fun r ha hs hd => by rw [fg r hs hd, g₂, hL.gpr r ha hs hd],
      by rw [fm, hR.mem, hmem₁], by rw [frd, hR.rd, hrd₁, hL.rd], by rw [fwr, hR.wr, hwr₁, hL.wr]⟩
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, fzf]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with x7 := ?_, rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [f7, hR.keep .xmm7 (by simp), hx₁ _ (by decide) (by decide), hL.x7]
    · rw [frsi, g₂, hL.rsi]
      simp only [blkAddr]
      bv_omega
    · rw [frdx, hrdx]

/-! ## The whole function -/

theorem st16 (s₀ : State) {d : Nat} (hd : d ≤ 4) :
    (stR s₀).Contains (st s₀ + BitVec.ofInt 64 (d : Int)) 16 :=
  contains_offset' (by omega) (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha1.compressX86_64.post s₀ s' := by
  have in0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨stR s₀, by simp [hp.wr], st16 s₀ (by omega)⟩
  have in4 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((4 : Nat) : Int)) 16 :=
    ⟨stR s₀, by simp [hp.wr], st16 s₀ (by omega)⟩
  refine WP.seq (WP.mono (load_ok s₀ in0 in4) fun s₁ ⟨h0, h1, h7, hzf, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · have hc₀ : Common s₀ 0 s₁ := ⟨h0, h1, fun r hr _ _ => hg r hr, hm, hrd, hwr⟩
    refine WP.ite (s₀.gpr .rdx &&& s₀.gpr .rdx == 0) (by simp [eval, hzf]) (fun h => ?_) (fun h => ?_)
    · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
      exact WP.block_nil (M := isa) (h0 ▸ hc₀)
    · have hpos : 0 < nb s₀ := by
        simp only [BitVec.and_self, beq_eq_false_iff_ne, ne_eq] at h
        exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
      let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
      have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
          (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
          (eval .ne s' = some true ∧ ∃ m' < m, Inv m' s')) := by
        rintro m s ⟨i, rfl, hi, hL⟩
        refine WP.mono (body_ok hp hi hL) fun s' h => ?_
        rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
        · exact .inl ⟨he, hc⟩
        · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
      have hL₀ : LInv s₀ 0 s₁ :=
        { hc₀ with
          x7 := h7
          rsi := by rw [hg .rsi (by decide)]; simp [blkAddr]
          rdx := by rw [hg .rdx (by decide)]; simp [nb] }
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩
  · have hrdi : s₂.gpr .rdi = st s₀ := hc.gpr .rdi (by decide) (by decide) (by decide)
    have out : ∀ d, d ≤ 4 → InRegions s₂.wr (s₂.gpr .rdi + BitVec.ofInt 64 ((d : Nat) : Int)) 16 :=
      fun d hd => ⟨stR s₀, by simp [hc.wr, hp.wr], by rw [hrdi]; exact st16 s₀ hd⟩
    refine WP.mono (store_ok s₂ _ hc.x0 hc.x1 (out 0 (by omega)) (out 4 (by omega)))
      fun s' ⟨⟨x, y, hm'⟩, hst, hg', _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hg', hc.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · have hret : (retR s₀).Contains (s₀.gpr .rsp) 8 := Region.contains_self _ _
      rw [hm', hrdi, Mem.readW_writeW_sep (hp.ret_st.sep hret (st16 s₀ (by omega))) (by decide),
        Mem.readW_writeW_sep (hp.ret_st.sep hret (st16 s₀ (by omega))) (by decide), hc.mem]
    · show stateAt s'.mem (st s₀) = _
      rw [← hrdi]; exact hst

theorem compress_verified :
    Verified X86_64.target Impl.Sha1.X86_64.ShaNi.compress Proof.Sha1.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact (Proof.Sha1.X86_64.compress_verified).2.2

end VG.Proof.Sha1.X86_64.ShaNi
