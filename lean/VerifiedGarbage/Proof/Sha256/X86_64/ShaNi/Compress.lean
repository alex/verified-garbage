import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Sha256.X86_64.ShaNi.Spec
import VerifiedGarbage.Impl.Sha256.X86_64.ShaNi
import VerifiedGarbage.Proof.Sha256.X86_64.Compress
import VerifiedGarbage.Proof.Framework.Offset

/-!
# SHA-256 compression function on x86-64 with the SHA extensions

Untrusted: everything here is checked by Lean. `compress_verified` proves
`Impl.Sha256.X86_64.ShaNi.compress` against the same contract as the scalar
`vg_sha256_compress`, reusing its precondition (`Pre`) and block lemmas.
-/

namespace VG.Proof.Sha256.X86_64.ShaNi

open VG VG.X86_64 VG.Impl.Sha256.X86_64.ShaNi
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The registers of a group of four rounds are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7, .xmm8, .xmm9,
      .xmm10, .xmm11].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7, .xmm8,
      .xmm9, .xmm10, .xmm11].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q : BitVec 128)
    (h1 : s.xmm .xmm1 = abef v) (h2 : s.xmm .xmm2 = cdgh v) (hq : s.xmm (msg n) = q) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = sha256Rnds2 (abef v) (sha256Rnds2 (cdgh v) (abef v)
        (XBinOp.eval .paddd (kQuad (4 * n)) q))
        (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) q) 0x0e) ∧
      s'.xmm .xmm2 = sha256Rnds2 (cdgh v) (abef v) (XBinOp.eval .paddd (kQuad (4 * n)) q) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm11 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4, const, List.cons_append, List.nil_append]
  generalize msg n = x at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.gpr_setReg_self,
    RegUpd.xmm_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, not_false_eq_true, reduceCtorEq, hd, h1, h2, hq, movq_const,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 h11 => ?_, fun r hr => ?_, trivial⟩
  · simp only [RegUpd.xmm_setXmm_of_ne, RegUpd.xmm_setReg, h0, h1, h2, h11, not_false_eq_true]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.xmm (msg n) = a) (hb : s.xmm (msg (n + 1)) = b) (hc : s.xmm (msg (n + 2)) = c)
    (hd' : s.xmm (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = sha256Msg2 (XBinOp.eval .paddd (XBinOp.eval .sha256msg1 a b) (alignRight d c 4)) d ∧
      (∀ r, r ≠ msg n → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
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
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, hd, hd'', ha, hb, hc, hd',
    eval_movdqa, eval_sha256msg2,
    Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 h7 => by
    simp only [RegUpd.xmm_setXmm_of_ne, h0, h7, not_false_eq_true], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) (s.xmm .xmm8) ∧
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
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, State.load128, ea_at, hin,
    ite_true, hd'',
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 => by simp only [RegUpd.xmm_setXmm_of_ne, h0, not_false_eq_true], trivial⟩

/-- `msg k` for the three registers other than `msg n` that hold schedule words. -/
theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

theorem msg_other (n : Nat) (r : XReg) (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7 ∨ r = .xmm8 ∨
    r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

/-- What holds after rounds `0 … 4n-1` of a block `M`, from the state `sB` at its start. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * n))
  x2 : s.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad M k
  keep : ∀ r, r = .xmm8 ∨ r = .xmm9 ∨ r = .xmm10 → s.xmm r = sB.xmm r
  gpr : ∀ r, r ≠ .rax → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_four (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha256.rounds H M (4 * (n + 1)) =
      roundKW (roundKW (roundKW (roundKW (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n)))
        (K (4 * n + 1)) (W M (4 * n + 1))) (K (4 * n + 2)) (W M (4 * n + 2)))
        (K (4 * n + 3)) (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ]
  rfl

theorem kq_quad (n : Nat) (M : Block) :
    dword (XBinOp.eval .paddd (kQuad (4 * n)) (quad M n)) 0 = K (4 * n) + W M (4 * n) ∧
    dword (XBinOp.eval .paddd (kQuad (4 * n)) (quad M n)) 1 = K (4 * n + 1) + W M (4 * n + 1) ∧
    dword (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) (quad M n)) 0x0e) 0 =
      K (4 * n + 2) + W M (4 * n + 2) ∧
    dword (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) (quad M n)) 0x0e) 1 =
      K (4 * n + 3) + W M (4 * n + 3) := by
  simp only [shufDwords_0e, XBinOp.eval, kQuad, quad, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h1 : s.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * n)))
    (h2 : s.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * n))) (hq : s.xmm (msg n) = quad M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      s'.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm11 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ h1 h2 hq) fun s' ⟨e1, e2, hx, hg, hm, hrd, hwr⟩ => ?_
  obtain ⟨k0, k1, k2, k3⟩ := kq_quad n M
  rw [rnds2_eq _ _ k0 k1] at e1 e2
  rw [← cdgh_two (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n)) (K (4 * n + 1))
    (W M (4 * n + 1)), rnds2_eq _ _ k2 k3] at e1
  refine ⟨by rw [e1, rounds_four], by rw [e2, rounds_four, cdgh_two], hx, hg, hm, hrd, hwr⟩

theorem ofInt_natCast' (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap32 (m.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) bswapMask = quad M n := by
  rw [show bswapMask = 0x0c0d0e0f08090a0b0405060700010203#128 from rfl, pshufb_bswap]
  have e : ∀ j, j < 4 → bswap32 (dword (m.readW (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 128) j) =
      W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega)]
    refine congrArg (fun a => bswap32 (m.readW a 32)) ?_
    simp only [ofInt_natCast']
    exact Offset.add_add_eq _ (by omega)
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rfl

theorem rounds_ok (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hmask : sB.xmm .xmm8 = bswapMask)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16)
    (hblk : ∀ t : Nat, t < 16 →
      bswap32 (sB.mem.readW (bp + BitVec.ofInt 64 ((4 * t : Nat) : Int)) 32) = W M t)
    (h1 : sB.xmm .xmm1 = abef H) (h2 : sB.xmm .xmm2 = cdgh H) :
    ∀ n ≤ 16, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h1, h2, fun _ h => absurd h (by omega), fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := (hs.gpr .rsi (by decide)).trans hrsi
    -- The schedule: `msg n` gets `quad M n`; nothing else but `xmm7` changes.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad M n ∧ (∀ r, r ≠ msg n → r ≠ .xmm7 → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r h _ => hx r h, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi, hs.mem, hs.keep .xmm8 (.inl rfl), hmask]
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
    have o1 := msg_other n .xmm1 (by simp)
    have o2 := msg_other n .xmm2 (by simp)
    refine WP.mono (rounds4_step H M n s₁ (by rw [hx₁ _ (Ne.symm o1) (by decide)]; exact hs.x1)
      (by rw [hx₁ _ (Ne.symm o2) (by decide)]; exact hs.x2) hq)
      fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e2, fun k hk hk' => ?_, fun r hr => ?_, fun r hr => ?_, by rw [hm₂, hm₁, hs.mem],
      by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · have n0 := msg_other k .xmm0 (by simp)
      have n1 := msg_other k .xmm1 (by simp)
      have n2 := msg_other k .xmm2 (by simp)
      have n11 := msg_other k .xmm11 (by simp)
      rw [hx₂ _ n0 n1 n2 n11]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · have n7 := msg_other k .xmm7 (by simp)
        rw [hx₁ _ (msg_ne n k (by omega) (by omega)) n7]
        exact hs.msgs k (by omega) (by omega)
    · have := hr
      rcases hr with rfl | rfl | rfl <;>
      · rw [hx₂ _ (by decide) (by decide) (by decide) (by decide),
          hx₁ _ (Ne.symm (msg_other n _ (by simp))) (by decide)]
        exact hs.keep _ (by simp)
    · rw [hg₂ r hr, hg₁, hs.gpr r hr]

/-! ## The prologue and the epilogue -/

theorem stateAt_lo (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) 128) j = (stateAt m p)[j] := by
  rw [dword_readW _ _ hj]; simp [stateAt]

theorem stateAt_hi (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    dword (m.readW (p + BitVec.ofInt 64 ((16 : Nat) : Int)) 128) j = (stateAt m p)[4 + j] := by
  rw [dword_readW _ _ hj]
  simp only [stateAt, Vector.getElem_ofFn]
  refine congrArg (fun a => m.readW a 32) ?_
  simp only [ofInt_natCast']
  exact Offset.add_add_eq _ (by omega)

/-- The hash value, loaded as `ABEF` and `CDGH`. -/
theorem load_ok (s : State)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) 16) :
    WP isa (.block (load ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s fun s' =>
      s'.xmm .xmm1 = abef (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm2 = cdgh (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm8 = bswapMask ∧
      s'.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [load, const, List.cons_append, List.nil_append]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    execAlu, readSrc, arithFlags, State.setFlags,
    isa, State.setXmm, State.setReg, State.load128, ea_at, hlo, hhi, ite_true, ite_false, movq_const,
    eval_movdqa, Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, fun r hr => by simp [hr], trivial⟩ <;>
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, abef, cdgh, stateAt_lo _ _ (show 0 < 4 by decide),
    stateAt_lo _ _ (show 1 < 4 by decide), stateAt_lo _ _ (show 2 < 4 by decide),
    stateAt_lo _ _ (show 3 < 4 by decide), stateAt_hi _ _ (show 0 < 4 by decide),
    stateAt_hi _ _ (show 1 < 4 by decide), stateAt_hi _ _ (show 2 < 4 by decide),
    stateAt_hi _ _ (show 3 < 4 by decide)]

/-- The hash value after storing `x` and `y` at `p` and `p + 16`. -/
theorem stateAt_store (m : Mem) (p : Addr) (x y : BitVec 128) :
    stateAt ((m.writeW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) x).writeW
      (p + BitVec.ofInt 64 ((16 : Nat) : Int)) y) p =
      #v[dword x 0, dword x 1, dword x 2, dword x 3, dword y 0, dword y 1, dword y 2, dword y 3] := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast']
  by_cases hlo : j < 4
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      show p + BitVec.ofNat 64 (4 * j) = p + BitVec.ofNat 64 0 + BitVec.ofNat 64 (4 * j) from
        (Offset.add_add_eq _ (by omega)).symm,
      readW_writeW128 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [show p + BitVec.ofNat 64 (4 * j) = p + BitVec.ofNat 64 16 + BitVec.ofNat 64 (4 * (j - 4)) from
        (Offset.add_add_eq _ (by omega)).symm, readW_writeW128 _ _ _ (by omega)]
    rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl <;> rfl

/-- `ABEF` and `CDGH`, stored back as the hash value. -/
theorem store_ok (s : State) (v : HashValue) (h1 : s.xmm .xmm1 = abef v) (h2 : s.xmm .xmm2 = cdgh v)
    (hlo : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16)
    (hhi : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) 16) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) x).writeW
        (s.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) y) ∧
      stateAt s'.mem (s.gpr .rdi) = v ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [store]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, State.setXmm, State.store128, ea_at, hlo, hhi, ite_true, ite_false, h1, h2, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, trivial⟩
  rw [stateAt_store]
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, abef, cdgh]
  apply Vector.ext
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The loop over the blocks -/

open VG.Proof.Sha256.X86_64 (Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset' toNat_ofNat_lt)

theorem Pre.in_blk16 {s₀ : State} (hp : Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((16 * n : Nat) : Int)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [ofInt_natCast', show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  x2 : s.xmm .xmm2 = cdgh (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x8 : s.xmm .xmm8 = bswapMask
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have h₁ : WP isa (.block [.xop (.bin .movdqa .xmm9 .xmm1), .xop (.bin .movdqa .xmm10 .xmm2)]) s
      fun s₁ => s₁.xmm .xmm9 = s.xmm .xmm1 ∧ s₁.xmm .xmm10 = s.xmm .xmm2 ∧
        (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      isa, State.setXmm, ite_true, ite_false, eval_movdqa, Option.some.injEq, exists_eq_left']
    exact ⟨trivial, trivial, fun r h9 h10 => by simp [h9, h10], trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e9, e10, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hmem₁ : s₁.mem = s₀.mem := hm₁.trans hL.mem
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.rsi])
    (by rw [hx₁ _ (by decide) (by decide), hL.x8])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    (fun t ht => by rw [hmem₁]; exact blk_word i t ht)
    (by rw [hx₁ _ (by decide) (by decide), hL.x1]) (by rw [hx₁ _ (by decide) (by decide), hL.x2])
    16 (Nat.le_refl _)) fun s₂ hR => ?_)
  have k9 : s₂.xmm .xmm9 = abef (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [hR.keep .xmm9 (by simp), e9, hL.x1]
  have k10 : s₂.xmm .xmm10 = cdgh (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [hR.keep .xmm10 (by simp), e10, hL.x2]
  have hx1 := hR.x1
  have hx2 := hR.x2
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have e64 : BitVec.signExtend 64 (64 : BitVec 32) = 64 := by decide
  have h₃ : WP isa (.block [.xop (.bin .paddd .xmm1 .xmm9), .xop (.bin .paddd .xmm2 .xmm10),
      .alu .add .rsi (.imm 64), .alu .sub .rdx (.imm 1)]) s₂ fun s₃ =>
      s₃.xmm .xmm1 = abef (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm2 = cdgh (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm8 = s₂.xmm .xmm8 ∧
      s₃.gpr .rsi = s₂.gpr .rsi + 64 ∧ s₃.gpr .rdx = s₂.gpr .rdx - 1 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s₃.gpr r = s₂.gpr r) ∧
      s₃.zf = some (s₂.gpr .rdx - 1 == 0) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
      execAlu, readSrc, arithFlags, State.setFlags, isa, State.setXmm, State.setReg, ite_true,
      ite_false, hx1, hx2, k9, k10, paddd_abef, paddd_cdgh, e1, e64, Option.some.injEq,
      Option.bind_some, exists_eq_left']
    exact ⟨by rw [compressBlocks_succ]; rfl, by rw [compressBlocks_succ]; rfl, trivial, trivial, trivial,
      fun r h1 h2 => by simp [h1, h2], trivial⟩
  refine WP.mono h₃ fun s₃ ⟨f1, f2, f8, frsi, frdx, fg, fzf, fm, frd, fwr⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr => by rw [hR.gpr r hr, hg₁]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [g₂ .rdx (by decide), hL.rdx]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hcommon : Common s₀ (i + 1) s₃ :=
    ⟨f1, f2, fun r ha hs hd => by rw [fg r hs hd, g₂ r ha, hL.gpr r ha hs hd],
      by rw [fm, hR.mem, hmem₁], by rw [frd, hR.rd, hrd₁, hL.rd], by rw [fwr, hR.wr, hwr₁, hL.wr]⟩
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, fzf]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with x8 := ?_, rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [f8, hR.keep .xmm8 (by simp), hx₁ _ (by decide) (by decide), hL.x8]
    · rw [frsi, g₂ .rsi (by decide), hL.rsi]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [frdx, hrdx]

/-! ## The whole function -/

theorem st16 (s₀ : State) {d : Nat} (hd : d ≤ 16) :
    (stR s₀).Contains (st s₀ + BitVec.ofInt 64 (d : Int)) 16 :=
  contains_offset' (by omega) (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha256.compressX86_64.post s₀ s' := by
  have in0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 16 :=
    ⟨stR s₀, by simp [hp.wr], st16 s₀ (by omega)⟩
  have in16 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((16 : Nat) : Int)) 16 :=
    ⟨stR s₀, by simp [hp.wr], st16 s₀ (by omega)⟩
  refine WP.seq (WP.mono (load_ok s₀ in0 in16) fun s₁ ⟨h1, h2, h8, hzf, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · have hc₀ : Common s₀ 0 s₁ := ⟨h1, h2, fun r hr _ _ => hg r hr, hm, hrd, hwr⟩
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
          x8 := h8
          rsi := by rw [hg .rsi (by decide)]; simp [blkAddr]
          rdx := by rw [hg .rdx (by decide)]; simp [nb] }
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩
  · have hrdi : s₂.gpr .rdi = st s₀ := hc.gpr .rdi (by decide) (by decide) (by decide)
    have out : ∀ d, d ≤ 16 → InRegions s₂.wr (s₂.gpr .rdi + BitVec.ofInt 64 ((d : Nat) : Int)) 16 :=
      fun d hd => ⟨stR s₀, by simp [hc.wr, hp.wr], by rw [hrdi]; exact st16 s₀ hd⟩
    refine WP.mono (store_ok s₂ _ hc.x1 hc.x2 (out 0 (by omega)) (out 16 (by omega)))
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
    Verified X86_64.target Impl.Sha256.X86_64.ShaNi.compress Proof.Sha256.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by decide +kernel) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact (Proof.Sha256.X86_64.compress_verified).2.2

end VG.Proof.Sha256.X86_64.ShaNi
