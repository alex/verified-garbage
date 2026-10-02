import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Spec
import VerifiedGarbage.Proof.Sha512.X86_64.ShaNi.Lit
import VerifiedGarbage.Proof.Sha512.X86_64.Avx2.Compress
import VerifiedGarbage.Impl.Sha512.X86_64.ShaNi

/-!
# SHA-512 compression function on x86-64 with the SHA512 extension

`compress_verified` proves `Impl.Sha512.X86_64.ShaNi.compress` against the
same contract as the scalar `vg_sha512_compress`, reusing its precondition
(`Pre`) and block lemmas.
-/

namespace VG.Proof.Sha512.X86_64.ShaNi

open VG VG.X86_64 VG.Impl.Sha512.X86_64.ShaNi
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks compress)
open VG.Proof.Sha512.X86_64.Avx2 (pair qword_append_0 qword_append_1 paddq_eq load_pair)
open VG.Proof.Sha512.X86_64 (ofInt_natCast)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The registers of a group of four rounds are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7, .xmm8, .xmm9,
      .xmm10, .xmm11, .xmm12].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7,
      .xmm8, .xmm9, .xmm10, .xmm11, .xmm12].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem punpcklqdq_app (a b c d : Word) : XBinOp.eval .punpcklqdq (a ++ b) (c ++ d) = d ++ b := by
  simp only [XBinOp.eval, qword_append_0]

/-- Two constants into a register, through `rax` and `xmm11`. -/
theorem const2_ok (x : XReg) (hx : x ≠ .xmm11) (c₀ c₁ : Word) (s : State) :
    WP isa (.block (const2 x c₀ c₁)) s fun s' =>
      s'.xmm x = c₁ ++ c₀ ∧ s'.ymmHi x = 0 ∧
      (∀ r, r ≠ x → r ≠ .xmm11 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [const2, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, State.lane, RegUpd.xmm_setV, RegUpd.ymmHi_setV_128, RegUpd.gpr_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_setReg_self, RegUpd.xmm_setReg,
    RegUpd.ymmHi_setReg, RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, VBinOp.sse,
    punpcklqdq_app, hx, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h11 => ?_, fun r hr => ?_, trivial⟩
  · simp only [h0, h11, ite_false, and_self]
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q₀ q₁ : BitVec 128)
    (h1 : s.xmm .xmm1 = abef0 v) (h1' : s.ymmHi .xmm1 = abef1 v)
    (h2 : s.xmm .xmm2 = cdgh0 v) (h2' : s.ymmHi .xmm2 = cdgh1 v)
    (hq : s.xmm (msg n) = q₀) (hq' : s.ymmHi (msg n) = q₁) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm2 = (sha512Rnds2 (cdgh1 v ++ cdgh0 v) (abef1 v ++ abef0 v)
          (XBinOp.eval .paddq (K (4 * n + 1) ++ K (4 * n)) q₀)).extractLsb' 0 128 ∧
      s'.ymmHi .xmm2 = (sha512Rnds2 (cdgh1 v ++ cdgh0 v) (abef1 v ++ abef0 v)
          (XBinOp.eval .paddq (K (4 * n + 1) ++ K (4 * n)) q₀)).extractLsb' 128 128 ∧
      s'.ymm .xmm1 = sha512Rnds2 (abef1 v ++ abef0 v) (s'.ymm .xmm2)
          (XBinOp.eval .paddq (K (4 * n + 3) ++ K (4 * n + 2)) q₁) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm11 → r ≠ .xmm12 →
        s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4, kQuad, const2, vb, List.cons_append, List.nil_append]
  generalize msg n = x at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, State.lane, State.ymm, RegUpd.xmm_setV, RegUpd.ymmHi_setV_128,
    RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    RegUpd.gpr_setReg_self, RegUpd.xmm_setReg, RegUpd.ymmHi_setReg, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, VBinOp.sse, punpcklqdq_app, hd, h1, h1', h2, h2', hq, hq',
    ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, split256 _, fun r h0 h1 h2 h11 h12 => ?_, fun r hr => ?_, trivial⟩
  · simp only [h0, h1, h2, h11, h12, ite_false, and_self]
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_setReg_of_ne _ _ hr]

theorem rounds_four (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha512.rounds H M (4 * (n + 1)) =
      roundKW (roundKW (roundKW (roundKW (Spec.Sha512.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n)))
        (K (4 * n + 1)) (W M (4 * n + 1))) (K (4 * n + 2)) (W M (4 * n + 2)))
        (K (4 * n + 3)) (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ]
  rfl

/-- `Kₜ + Wₜ` for rounds `4n … 4n+3`, as `rounds4` forms them. -/
theorem kw_quad (M : Block) (n : Nat) :
    (XBinOp.eval .paddq (K (4 * n + 1) ++ K (4 * n)) (quad0 M n)).extractLsb' 0 64 = K (4 * n) + W M (4 * n) ∧
    (XBinOp.eval .paddq (K (4 * n + 1) ++ K (4 * n)) (quad0 M n)).extractLsb' 64 64 =
      K (4 * n + 1) + W M (4 * n + 1) ∧
    (XBinOp.eval .paddq (K (4 * n + 3) ++ K (4 * n + 2)) (quad1 M n)).extractLsb' 0 64 =
      K (4 * n + 2) + W M (4 * n + 2) ∧
    (XBinOp.eval .paddq (K (4 * n + 3) ++ K (4 * n + 2)) (quad1 M n)).extractLsb' 64 64 =
      K (4 * n + 3) + W M (4 * n + 3) := by
  simp only [quad0, quad1, pair, paddq_eq, lo64, hi64, show 2 * (2 * n) = 4 * n by omega,
    show 2 * (2 * n + 1) = 4 * n + 2 by omega, show 4 * n + 2 + 1 = 4 * n + 3 by omega]
  exact ⟨trivial, trivial, trivial, trivial⟩

theorem lanes_of_ymm {s : State} {r : XReg} {x₁ x₀ : BitVec 128} (h : s.ymm r = x₁ ++ x₀) :
    s.xmm r = x₀ ∧ s.ymmHi r = x₁ := by
  have h₀ := congrArg (·.extractLsb' 0 128) h
  have h₁ := congrArg (·.extractLsb' 128 128) h
  simp only [State.ymm, lo128, hi128] at h₀ h₁
  exact ⟨h₀, h₁⟩

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h1 : s.xmm .xmm1 = abef0 (Spec.Sha512.rounds H M (4 * n)))
    (h1' : s.ymmHi .xmm1 = abef1 (Spec.Sha512.rounds H M (4 * n)))
    (h2 : s.xmm .xmm2 = cdgh0 (Spec.Sha512.rounds H M (4 * n)))
    (h2' : s.ymmHi .xmm2 = cdgh1 (Spec.Sha512.rounds H M (4 * n)))
    (hq : s.xmm (msg n) = quad0 M n) (hq' : s.ymmHi (msg n) = quad1 M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = abef0 (Spec.Sha512.rounds H M (4 * (n + 1))) ∧
      s'.ymmHi .xmm1 = abef1 (Spec.Sha512.rounds H M (4 * (n + 1))) ∧
      s'.xmm .xmm2 = cdgh0 (Spec.Sha512.rounds H M (4 * (n + 1))) ∧
      s'.ymmHi .xmm2 = cdgh1 (Spec.Sha512.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm11 → r ≠ .xmm12 →
        s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ _ h1 h1' h2 h2' hq hq') fun s' ⟨e2, e2', e1, hx, hg, hm, hrd, hwr⟩ => ?_
  obtain ⟨k0, k1, k2, k3⟩ := kw_quad M n
  rw [rounds_four]
  generalize Spec.Sha512.rounds H M (4 * n) = v at *
  rw [rnds2_eq _ _ k0 k1, lo128] at e2
  rw [rnds2_eq _ _ k0 k1, hi128] at e2'
  simp only [State.ymm] at e1
  rw [e2, e2', ← cdgh1_two v (K (4 * n)) (W M (4 * n)) (K (4 * n + 1)) (W M (4 * n + 1)),
    ← cdgh0_two v (K (4 * n)) (W M (4 * n)) (K (4 * n + 1)) (W M (4 * n + 1)), rnds2_eq _ _ k2 k3] at e1
  obtain ⟨f1, f1'⟩ := lanes_of_ymm e1
  exact ⟨f1, f1', by rw [e2, cdgh0_two], by rw [e2', cdgh1_two], hx, hg, hm, hrd, hwr⟩

/-! ## The message schedule -/

theorem perm2Lanes_21_0 (a b : Nat → BitVec 128) : perm2Lanes a b 0x21 0 = a 1 := by
  simp [perm2Lanes]
theorem perm2Lanes_21_1 (a b : Nat → BitVec 128) : perm2Lanes a b 0x21 1 = b 0 := by
  simp [perm2Lanes]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a₀ a₁ b₀ c₀ c₁ d₀ d₁ : BitVec 128)
    (ha : s.xmm (msg n) = a₀) (ha' : s.ymmHi (msg n) = a₁) (hb : s.xmm (msg (n + 1)) = b₀)
    (hc : s.xmm (msg (n + 2)) = c₀) (hc' : s.ymmHi (msg (n + 2)) = c₁)
    (hd' : s.xmm (msg (n + 3)) = d₀) (hd'' : s.ymmHi (msg (n + 3)) = d₁) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.ymm (msg n) = sha512Msg2
        (XBinOp.eval .paddq ((sha512Msg1 (a₁ ++ a₀) b₀).extractLsb' 128 128) (alignRight d₀ c₁ 8) ++
          XBinOp.eval .paddq ((sha512Msg1 (a₁ ++ a₀) b₀).extractLsb' 0 128) (alignRight c₁ c₀ 8))
        (d₁ ++ d₀) ∧
      (∀ r, r ≠ msg n → r ≠ .xmm7 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd₂ := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, vb, show ¬ n < 4 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 2) = x₂ at *
  generalize msg (n + 3) = x₃ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd₂
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, perm2Lanes_21_0, perm2Lanes_21_1, State.lane, State.ymm, RegUpd.xmm_setV,
    RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    VBinOp.sse, hd, hd₂, ha, ha', hb, hc, hc', hd', hd'', split256, ite_true,
    ite_false, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 h7 => by simp only [h0, h7, ite_false, and_self], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .rsi + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 32) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 256).extractLsb' 0 128)
        (s.xmm .xmm8) ∧
      s'.ymmHi (msg n) = XBinOp.eval .pshufb
        ((s.mem.readW (s.gpr .rsi + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 256).extractLsb' 128 128)
        (s.ymmHi .xmm8) ∧
      (∀ r, r ≠ msg n → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  have hd₂ := VG.nodup_reverse hd
  apply WP.of_runBlock
  simp only [schedule, vb, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hd hd₂
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, State.lane, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, State.load256, ea_at, hin, VBinOp.sse, hd₂,
    ite_true, ite_false, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, fun r h0 => by simp only [h0, ite_false, and_self], trivial⟩

/-- Four message words, loaded and made big-endian. -/
theorem load_quad (M : Block) (m : Mem) (p : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → bswap64 (m.readW (p + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t) :
    XBinOp.eval .pshufb ((m.readW (p + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 256).extractLsb' 0 128)
      bswapMask = quad0 M n ∧
    XBinOp.eval .pshufb ((m.readW (p + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 256).extractLsb' 128 128)
      bswapMask = quad1 M n := by
  have e : ∀ k, k < 2 → (m.readW (p + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 256).extractLsb' (8 * (16 * k)) (8 * 16) =
      m.readW (p + BitVec.ofInt 64 ((16 * (2 * n + k) : Nat) : Int)) 128 := by
    intro k hk
    refine (readW_extract m _ (k := 16 * k) (n := 16) (by omega)).trans ?_
    simp only [ofInt_natCast]
    exact congrArg (m.readW · 128) (Offset.add_add_eq _ (by omega))
  exact ⟨(congrArg (XBinOp.eval .pshufb · bswapMask) (e 0 (by omega))).trans
      (load_pair M m p (n := 2 * n) (by omega) hblk),
    (congrArg (XBinOp.eval .pshufb · bswapMask) (e 1 (by omega))).trans
      (load_pair M m p (n := 2 * n + 1) (by omega) hblk)⟩

/-! ## Rounds `0 … 4n-1` -/

/-- `msg k` for the three registers other than `msg n` that hold schedule words. -/
theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

theorem msg_other (n : Nat) (r : XReg) (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7 ∨ r = .xmm8 ∨
    r = .xmm9 ∨ r = .xmm10 ∨ r = .xmm11 ∨ r = .xmm12) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7, .xmm8, .xmm9, .xmm10, .xmm11, .xmm12],
      msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [List.mem_cons, true_or, or_true])

/-- What holds after rounds `0 … 4n-1` of a block `M`, from the state `sB` at its start. -/
structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef0 (Spec.Sha512.rounds H M (4 * n))
  x1' : s.ymmHi .xmm1 = abef1 (Spec.Sha512.rounds H M (4 * n))
  x2 : s.xmm .xmm2 = cdgh0 (Spec.Sha512.rounds H M (4 * n))
  x2' : s.ymmHi .xmm2 = cdgh1 (Spec.Sha512.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad0 M k ∧ s.ymmHi (msg k) = quad1 M k
  keep : ∀ r, r = .xmm8 ∨ r = .xmm9 ∨ r = .xmm10 → s.xmm r = sB.xmm r ∧ s.ymmHi r = sB.ymmHi r
  gpr : ∀ r, r ≠ .rax → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_ok (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .rsi = bp) (hmask : sB.xmm .xmm8 = bswapMask) (hmask' : sB.ymmHi .xmm8 = bswapMask)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 32)
    (hblk : ∀ t : Nat, t < 16 →
      bswap64 (sB.mem.readW (bp + BitVec.ofInt 64 ((8 * t : Nat) : Int)) 64) = W M t)
    (h1 : sB.xmm .xmm1 = abef0 H) (h1' : sB.ymmHi .xmm1 = abef1 H)
    (h2 : sB.xmm .xmm2 = cdgh0 H) (h2' : sB.ymmHi .xmm2 = cdgh1 H) :
    ∀ n ≤ 20, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h1, h1', h2, h2', fun _ h => absurd h (by omega),
      fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .rsi = bp := (hs.gpr .rsi (by decide)).trans hrsi
    -- The schedule: `msg n` gets `W₄ₙ … W₄ₙ₊₃`; nothing else but `ymm7` changes.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad0 M n ∧ s₁.ymmHi (msg n) = quad1 M n ∧
        (∀ r, r ≠ msg n → r ≠ .xmm7 → s₁.xmm r = s.xmm r ∧ s₁.ymmHi r = s.ymmHi r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, e', hx, hg, hm, hrd, hwr⟩ => ⟨?_, ?_, fun r h _ => hx r h, hg, hm, hrd, hwr⟩
        · rw [e, hs_rsi, hs.mem, (hs.keep .xmm8 (.inl rfl)).1, hmask]
          exact (load_quad M sB.mem bp hlo hblk).1
        · rw [e', hs_rsi, hs.mem, (hs.keep .xmm8 (.inl rfl)).2, hmask']
          exact (load_quad M sB.mem bp hlo hblk).2
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        have m0 := hs.msgs i (by omega) (by omega)
        have m1 := hs.msgs (i + 1) (by omega) (by omega)
        have m2 := hs.msgs (i + 2) (by omega) (by omega)
        have m3 := hs.msgs (i + 3) (by omega) (by omega)
        rw [← msg_add4 i] at m0
        rw [← msg_add4 (i + 1), show i + 1 + 4 = i + 4 + 1 by omega] at m1
        rw [← msg_add4 (i + 2), show i + 2 + 4 = i + 4 + 2 by omega] at m2
        rw [← msg_add4 (i + 3), show i + 3 + 4 = i + 4 + 3 by omega] at m3
        refine WP.mono (schedule_hi (i + 4) (by omega) s _ _ _ _ _ _ _ m0.1 m0.2 m1.1 m2.1 m2.2 m3.1 m3.2)
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ?_
        obtain ⟨f, f'⟩ := lanes_of_ymm (e.trans (schedule_eq M i))
        exact ⟨f, f', hx, hg, hm, hrd, hwr⟩
    refine WP.mono hsched fun s₁ ⟨hq, hq', hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o1 := msg_other n .xmm1 (by simp)
    have o2 := msg_other n .xmm2 (by simp)
    refine WP.mono (rounds4_step H M n s₁
      (by rw [(hx₁ _ (Ne.symm o1) (by decide)).1]; exact hs.x1)
      (by rw [(hx₁ _ (Ne.symm o1) (by decide)).2]; exact hs.x1')
      (by rw [(hx₁ _ (Ne.symm o2) (by decide)).1]; exact hs.x2)
      (by rw [(hx₁ _ (Ne.symm o2) (by decide)).2]; exact hs.x2') hq hq')
      fun s₂ ⟨e1, e1', e2, e2', hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e1', e2, e2', fun k hk hk' => ?_, fun r hr => ?_, fun r hr => ?_,
      by rw [hm₂, hm₁, hs.mem], by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · have n0 := msg_other k .xmm0 (by simp)
      have n1 := msg_other k .xmm1 (by simp)
      have n2 := msg_other k .xmm2 (by simp)
      have n11 := msg_other k .xmm11 (by simp)
      have n12 := msg_other k .xmm12 (by simp)
      rw [(hx₂ _ n0 n1 n2 n11 n12).1, (hx₂ _ n0 n1 n2 n11 n12).2]
      by_cases hkn : k = n
      · subst hkn; exact ⟨hq, hq'⟩
      · have n7 := msg_other k .xmm7 (by simp)
        have hk₁ := hx₁ _ (msg_ne n k (by omega) (by omega)) n7
        rw [hk₁.1, hk₁.2]
        exact hs.msgs k (by omega) (by omega)
    · have o := Ne.symm (msg_other n r (by rcases hr with rfl | rfl | rfl <;> simp))
      have h₂ := hx₂ r (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl <;> decide)
      have h₁ := hx₁ r o (by rcases hr with rfl | rfl | rfl <;> decide)
      rw [h₂.1, h₂.2, h₁.1, h₁.2]
      exact hs.keep r hr
    · rw [hg₂ r hr, hg₁, hs.gpr r hr]

/-! ## The prologue and the epilogue -/

theorem split128 (x : BitVec 128) : x.extractLsb' 64 64 ++ x.extractLsb' 0 64 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  by_cases h : i < 64
  · simp only [h, ite_true, decide_true, Bool.true_and, Nat.zero_add]
  · simp only [h, ite_false, decide_eq_true (show i - 64 < 64 by omega), Bool.true_and]
    exact congrArg _ (by omega)

/-- A lane of a 256-bit load, as the two quadwords in memory. -/
theorem load_lanes (m : Mem) (p : Addr) {d e a b : Nat} (he : e = 0 ∨ e = 128)
    (ha : a = d + e / 8 + 8) (hb : b = d + e / 8) :
    (m.readW (p + BitVec.ofInt 64 ((d : Nat) : Int)) 256).extractLsb' e 128 =
      m.readW (p + BitVec.ofNat 64 a) 64 ++ m.readW (p + BitVec.ofNat 64 b) 64 := by
  rw [← split128 ((m.readW _ 256).extractLsb' e 128), extract_extract _ _ _ _ _ (by omega),
    extract_extract _ _ _ _ _ (by omega), show e + 64 = 8 * (e / 8 + 8) by omega,
    show e + 0 = 8 * (e / 8) by omega]
  rw [readW_extract m _ (k := e / 8 + 8) (n := 8) (by omega), readW_extract m _ (k := e / 8) (n := 8) (by omega),
    ofInt_natCast, Offset.add_add, Offset.add_add, ha, hb, Nat.add_assoc]

theorem permQwords_b1 (a b c d : Word) :
    (permQwords ((a ++ b : BitVec 128) ++ (c ++ d : BitVec 128)) 0xb1).extractLsb' 0 128 = d ++ c ∧
    (permQwords ((a ++ b : BitVec 128) ++ (c ++ d : BitVec 128)) 0xb1).extractLsb' 128 128 = b ++ a := by
  have e0 : ((0xb1 : BitVec 8).extractLsb' (2 * 0) 2).toNat = 1 := rfl
  have e1 : ((0xb1 : BitVec 8).extractLsb' (2 * 1) 2).toNat = 0 := rfl
  have e2 : ((0xb1 : BitVec 8).extractLsb' (2 * 2) 2).toNat = 3 := rfl
  have e3 : ((0xb1 : BitVec 8).extractLsb' (2 * 3) 2).toNat = 2 := rfl
  simp only [permQwords, e0, e1, e2, e3, qword256_0, qword256_1, qword256_2, qword256_3, lo4, hi4]
  exact ⟨trivial, trivial⟩

theorem perm2Lanes_20_0 (a b : Nat → BitVec 128) : perm2Lanes a b 0x20 0 = a 0 := by
  simp [perm2Lanes]
theorem perm2Lanes_20_1 (a b : Nat → BitVec 128) : perm2Lanes a b 0x20 1 = b 0 := by
  simp [perm2Lanes]
theorem perm2Lanes_31_0 (a b : Nat → BitVec 128) : perm2Lanes a b 0x31 0 = a 1 := by
  simp [perm2Lanes]
theorem perm2Lanes_31_1 (a b : Nat → BitVec 128) : perm2Lanes a b 0x31 1 = b 1 := by
  simp [perm2Lanes]

theorem stateAt_word (m : Mem) (p : Addr) (k : Nat) (hk : k < 8) :
    (stateAt m p)[k] = m.readW (p + BitVec.ofNat 64 (8 * k)) 64 := by
  simp only [stateAt, Vector.getElem_ofFn]

theorem mask_ok (s : State) :
    WP isa (.block mask) s fun s' =>
      s'.xmm .xmm8 = bswapMask ∧ s'.ymmHi .xmm8 = bswapMask ∧
      (∀ r, r ≠ .xmm8 → r ≠ .xmm11 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have i1 : (1 : BitVec 8).getLsbD 0 = true := rfl
  rw [mask, WP.block_append_iff]
  refine WP.mono (const2_ok .xmm8 (by decide) _ _ s) fun s₁ ⟨e, e', hx, hg, hm, hrd, hwr⟩ => ?_
  apply WP.of_runBlock
  simp only [i1, runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec, isa, State.lane,
    RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV,
    RegUpd.wr_setV, e, split128, ite_true, Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h8 h11 => ?_, hg, hm, hrd, hwr⟩
  simp only [h8, ite_false]
  exact hx r h8 h11

/-- The hash value, loaded as `ABEF` and `CDGH`, and the byte-swapping mask. -/
theorem load_ok (s : State)
    (hlo : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hhi : InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((32 : Nat) : Int)) 32) :
    WP isa (.block (load ++ ([.alu .test .rdx (.reg .rdx)] : List Instr))) s fun s' =>
      s'.xmm .xmm1 = abef0 (stateAt s.mem (s.gpr .rdi)) ∧
      s'.ymmHi .xmm1 = abef1 (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm2 = cdgh0 (stateAt s.mem (s.gpr .rdi)) ∧
      s'.ymmHi .xmm2 = cdgh1 (stateAt s.mem (s.gpr .rdi)) ∧
      s'.xmm .xmm8 = bswapMask ∧ s'.ymmHi .xmm8 = bswapMask ∧
      s'.zf = some (s.gpr .rdx &&& s.gpr .rdx == 0) ∧
      (∀ r, r ≠ .rax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have a0 := load_lanes s.mem (s.gpr .rdi) (d := 0) (e := 0) (a := 8) (b := 0) (.inl rfl) rfl rfl
  have a1 := load_lanes s.mem (s.gpr .rdi) (d := 0) (e := 128) (a := 24) (b := 16) (.inr rfl) rfl rfl
  have b0 := load_lanes s.mem (s.gpr .rdi) (d := 32) (e := 0) (a := 40) (b := 32) (.inl rfl) rfl rfl
  have b1 := load_lanes s.mem (s.gpr .rdi) (d := 32) (e := 128) (a := 56) (b := 48) (.inr rfl) rfl rfl
  have w : ∀ k (hk : k < 8), (stateAt s.mem (s.gpr .rdi))[k] =
      s.mem.readW (s.gpr .rdi + BitVec.ofNat 64 (8 * k)) 64 := stateAt_word _ _
  rw [load, List.append_assoc, WP.block_append_iff]
  refine WP.mono (mask_ok s) fun s₁ ⟨e8, e8', _, hg, hm, hrd, hwr⟩ => ?_
  have hrdi : s₁.gpr .rdi = s.gpr .rdi := hg .rdi (by decide)
  have hrdx : s₁.gpr .rdx = s.gpr .rdx := hg .rdx (by decide)
  rw [← hrd, ← hwr, ← hrdi] at hlo hhi
  rw [← hm, ← hrdi] at a0 a1 b0 b1
  apply WP.of_runBlock
  simp only [List.cons_append, List.nil_append, runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, perm2Lanes_20_0, perm2Lanes_20_1, perm2Lanes_31_0, perm2Lanes_31_1, State.lane,
    State.ymm, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.load256, ea_at, hlo, hhi, a0, a1, b0, b1, permQwords_b1,
    execAlu, readSrc, RegUpd.gpr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.ymmHi_arithFlags, RegUpd.mem_arithFlags,
    RegUpd.rd_arithFlags, RegUpd.wr_arithFlags, RegUpd.zf_arithFlags, hrdx, reduceCtorEq, e8, e8',
    ite_true, ite_false, Option.map_some, Option.bind_some, Option.some.injEq,
    exists_eq_left']
  rw [hm, hrdi]
  refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, fun r hr => by rw [hg r hr], rfl, hrd, hwr⟩
  · rw [abef0, w 4 (by decide), w 5 (by decide)]
  · rw [abef1, w 0 (by decide), w 1 (by decide)]
  · rw [cdgh0, w 6 (by decide), w 7 (by decide)]
  · rw [cdgh1, w 2 (by decide), w 3 (by decide)]

/-- A quadword of a 256-bit write. -/
theorem readW_writeW256 (m : Mem) (a : Addr) (x : BitVec 256) {j : Nat} (hj : j < 4) :
    (m.writeW a x).readW (a + BitVec.ofNat 64 (8 * j)) 64 = qword256 x j := by
  refine (readW_writeW_inside m a x (k := 8 * j) (n := 8) (by omega) (by decide)).trans ?_
  rw [qword256, show 8 * (8 * j) = 64 * j by omega]

/-- The hash value after storing `x` and `y` at `p` and `p + 32`. -/
theorem stateAt_store (m : Mem) (p : Addr) (x y : BitVec 256) :
    stateAt ((m.writeW (p + BitVec.ofInt 64 ((0 : Nat) : Int)) x).writeW
      (p + BitVec.ofInt 64 ((32 : Nat) : Int)) y) p =
      #v[qword256 x 0, qword256 x 1, qword256 x 2, qword256 x 3,
        qword256 y 0, qword256 y 1, qword256 y 2, qword256 y 3] := by
  apply Vector.ext
  intro j hj
  simp only [stateAt, Vector.getElem_ofFn, ofInt_natCast]
  by_cases hlo : j < 4
  · rw [Mem.readW_writeW_sep (Offset.sep p (by omega) (by omega) (by omega)) (by decide),
      show p + BitVec.ofNat 64 (8 * j) = p + BitVec.ofNat 64 0 + BitVec.ofNat 64 (8 * j) from
        (Offset.add_add_eq _ (by omega)).symm,
      readW_writeW256 _ _ _ hlo]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;> rfl
  · rw [show p + BitVec.ofNat 64 (8 * j) = p + BitVec.ofNat 64 32 + BitVec.ofNat 64 (8 * (j - 4)) from
        (Offset.add_add_eq _ (by omega)).symm, readW_writeW256 _ _ _ (by omega)]
    rcases (by omega : j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with rfl | rfl | rfl | rfl <;> rfl

theorem permQwords_b1' (v : HashValue) :
    (permQwords (abef1 v ++ abef0 v) 0xb1).extractLsb' 0 128 = v[5] ++ v[4] ∧
    (permQwords (abef1 v ++ abef0 v) 0xb1).extractLsb' 128 128 = v[1] ++ v[0] ∧
    (permQwords (cdgh1 v ++ cdgh0 v) 0xb1).extractLsb' 0 128 = v[7] ++ v[6] ∧
    (permQwords (cdgh1 v ++ cdgh0 v) 0xb1).extractLsb' 128 128 = v[3] ++ v[2] :=
  ⟨(permQwords_b1 _ _ _ _).1, (permQwords_b1 _ _ _ _).2, (permQwords_b1 _ _ _ _).1,
    (permQwords_b1 _ _ _ _).2⟩

/-- `ABEF` and `CDGH`, stored back as the hash value. -/
theorem store_ok (s : State) (v : HashValue)
    (h1 : s.xmm .xmm1 = abef0 v) (h1' : s.ymmHi .xmm1 = abef1 v)
    (h2 : s.xmm .xmm2 = cdgh0 v) (h2' : s.ymmHi .xmm2 = cdgh1 v)
    (hlo : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 32)
    (hhi : InRegions s.wr (s.gpr .rdi + BitVec.ofInt 64 ((32 : Nat) : Int)) 32) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 256, s'.mem = (s.mem.writeW (s.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) x).writeW
        (s.gpr .rdi + BitVec.ofInt 64 ((32 : Nat) : Int)) y) ∧
      stateAt s'.mem (s.gpr .rdi) = v ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hp := permQwords_b1' v
  apply WP.of_runBlock
  simp only [store]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
    VOp.exec, isa, perm2Lanes_20_0, perm2Lanes_20_1, perm2Lanes_31_0, perm2Lanes_31_1, State.lane,
    State.ymm, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, State.store256_eq, State.setMem_gpr, State.setMem_mem,
    State.setMem_wr, State.setMem_rd, State.setMem_xmm, State.setMem_ymmHi, ea_at, hlo, hhi, h1,
    h1', h2, h2', hp, ite_true, ite_false, Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, trivial⟩
  rw [stateAt_store]
  simp only [qword256_0, qword256_1, qword256_2, qword256_3]
  apply Vector.ext
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## The loop over the blocks -/

open VG.Proof.Sha512.X86_64 (Pre pre_of st bp nb scr stR blR scrR retR H₀ blkAddr blk blk_word
  compressBlocks_succ contains_offset contains_offset')

theorem Pre.in_blk32 {s₀ : State} (hp : Pre s₀) {i n : Nat} (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofInt 64 ((32 * n : Nat) : Int)) 32 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [ofInt_natCast, show blkAddr s₀ i + BitVec.ofNat 64 (32 * n) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 32 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

/-- What holds between blocks, after `i` of them. -/
structure Common (s₀ : State) (i : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  x1' : s.ymmHi .xmm1 = abef1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  x2 : s.xmm .xmm2 = cdgh0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  x2' : s.ymmHi .xmm2 = cdgh1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i)
  gpr : ∀ r, r ≠ .rax → r ≠ .rsi → r ≠ .rdx → s.gpr r = s₀.gpr r
  mem : s.mem = s₀.mem
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr

/-- The loop invariant, at the start of block `i`. -/
structure LInv (s₀ : State) (i : Nat) (s : State) : Prop extends Common s₀ i s where
  x8 : s.xmm .xmm8 = bswapMask
  x8' : s.ymmHi .xmm8 = bswapMask
  rsi : s.gpr .rsi = blkAddr s₀ i
  rdx : s.gpr .rdx = BitVec.ofNat 64 (nb s₀ - i)

theorem body_ok {s₀ : State} (hp : Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval .ne s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval .ne s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have h₁ : WP isa (.block [.vop (.vmovdqa .l256 .xmm9 .xmm1), .vop (.vmovdqa .l256 .xmm10 .xmm2)]) s
      fun s₁ => s₁.xmm .xmm9 = s.xmm .xmm1 ∧ s₁.ymmHi .xmm9 = s.ymmHi .xmm1 ∧
        s₁.xmm .xmm10 = s.xmm .xmm2 ∧ s₁.ymmHi .xmm10 = s.ymmHi .xmm2 ∧
        (∀ r, r ≠ .xmm9 → r ≠ .xmm10 → s₁.xmm r = s.xmm r ∧ s₁.ymmHi r = s.ymmHi r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec,
      VOp.exec, isa, State.lane, RegUpd.xmm_setV, RegUpd.ymmHi_setV_256, RegUpd.gpr_setV,
      RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, ite_true, ite_false, Option.some.injEq,
      exists_eq_left']
    exact ⟨trivial, trivial, trivial, trivial, fun r h9 h10 => by simp only [h9, h10, ite_false, and_self],
      trivial⟩
  refine WP.seq (WP.mono h₁ fun s₁ ⟨e9, e9', e10, e10', hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hmem₁ : s₁.mem = s₀.mem := hm₁.trans hL.mem
  have k₁ := hx₁ .xmm1 (by decide) (by decide)
  have k₂ := hx₁ .xmm2 (by decide) (by decide)
  have k₈ := hx₁ .xmm8 (by decide) (by decide)
  refine WP.seq (WP.mono (rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.rsi])
    (by rw [k₈.1, hL.x8]) (by rw [k₈.2, hL.x8'])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk32 hp hi hn)
    (fun t ht => by rw [hmem₁]; exact blk_word i t ht)
    (by rw [k₁.1, hL.x1]) (by rw [k₁.2, hL.x1']) (by rw [k₂.1, hL.x2]) (by rw [k₂.2, hL.x2'])
    20 (Nat.le_refl _)) fun s₂ hR => ?_)
  have k9 : s₂.xmm .xmm9 = abef0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [(hR.keep .xmm9 (by simp)).1, e9, hL.x1]
  have k9' : s₂.ymmHi .xmm9 = abef1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [(hR.keep .xmm9 (by simp)).2, e9', hL.x1']
  have k10 : s₂.xmm .xmm10 = cdgh0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [(hR.keep .xmm10 (by simp)).1, e10, hL.x2]
  have k10' : s₂.ymmHi .xmm10 = cdgh1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) i) := by
    rw [(hR.keep .xmm10 (by simp)).2, e10', hL.x2']
  have hx1 := hR.x1
  have hx1' := hR.x1'
  have hx2 := hR.x2
  have hx2' := hR.x2'
  have e1 : BitVec.signExtend 64 (1 : BitVec 32) = 1 := by decide
  have e128 : BitVec.signExtend 64 (128 : BitVec 32) = 128 := by decide
  have h₃ : WP isa (.block [vb .vpaddq .xmm1 .xmm1 .xmm9, vb .vpaddq .xmm2 .xmm2 .xmm10,
      .alu .add .rsi (.imm 128), .alu .sub .rdx (.imm 1)]) s₂ fun s₃ =>
      s₃.xmm .xmm1 = abef0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.ymmHi .xmm1 = abef1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm2 = cdgh0 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.ymmHi .xmm2 = cdgh1 (compressBlocks (H₀ s₀) s₀.mem (bp s₀) (i + 1)) ∧
      s₃.xmm .xmm8 = s₂.xmm .xmm8 ∧ s₃.ymmHi .xmm8 = s₂.ymmHi .xmm8 ∧
      s₃.gpr .rsi = s₂.gpr .rsi + 128 ∧ s₃.gpr .rdx = s₂.gpr .rdx - 1 ∧
      (∀ r, r ≠ .rsi → r ≠ .rdx → s₃.gpr r = s₂.gpr r) ∧
      s₃.zf = some (s₂.gpr .rdx - 1 == 0) ∧
      s₃.mem = s₂.mem ∧ s₃.rd = s₂.rd ∧ s₃.wr = s₂.wr := by
    apply WP.of_runBlock
    simp (config := {decide := true}) only [vb, runBlock_cons, runStep_some, runBlock_nil, exec,
      VOp.exec, execAlu, readSrc, arithFlags, State.setFlags, isa, State.lane, State.setV,
      State.setReg, VBinOp.sse, ite_true, ite_false, hx1, hx1', hx2, hx2', k9, k9', k10, k10',
      paddq_abef0, paddq_abef1, paddq_cdgh0, paddq_cdgh1, e1, e128, Option.some.injEq,
      Option.bind_some, exists_eq_left']
    refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, fun r h1 h2 => by simp [h1, h2], trivial⟩ <;>
      rw [compressBlocks_succ] <;> rfl
  refine WP.mono h₃ fun s₃ ⟨f1, f1', f2, f2', f8, f8', frsi, frdx, fg, fzf, fm, frd, fwr⟩ => ?_
  have g₂ : ∀ r, r ≠ .rax → s₂.gpr r = s.gpr r := fun r hr => by rw [hR.gpr r hr, hg₁]
  have hrdx : s₂.gpr .rdx - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [g₂ .rdx (by decide), hL.rdx]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hcommon : Common s₀ (i + 1) s₃ :=
    ⟨f1, f1', f2, f2', fun r ha hs hd => by rw [fg r hs hd, g₂ r ha, hL.gpr r ha hs hd],
      by rw [fm, hR.mem, hmem₁], by rw [frd, hR.rd, hrd₁, hL.rd], by rw [fwr, hR.wr, hwr₁, hL.wr]⟩
  have hev : eval .ne s₃ = some (!(s₂.gpr .rdx - 1 == 0)) := by
    simp [eval, fzf]
  rw [hrdx] at hev
  by_cases hlast : i + 1 = nb s₀
  · left
    refine ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · right
    have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    refine ⟨?_, by omega, { hcommon with x8 := ?_, x8' := ?_, rsi := ?_, rdx := ?_ }⟩
    · rw [hev]
      have := hp.nb_lt
      have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
        intro h
        have h' := congrArg BitVec.toNat h
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
        exact hne h'
      simpa using h0
    · rw [f8, (hR.keep .xmm8 (by simp)).1, k₈.1, hL.x8]
    · rw [f8', (hR.keep .xmm8 (by simp)).2, k₈.2, hL.x8']
    · rw [frsi, g₂ .rsi (by decide), hL.rsi]
      exact (Offset.add_add _ _ 128).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [frdx, hrdx]

/-! ## The whole function -/

theorem st32 (s₀ : State) {d : Nat} (hd : d ≤ 32) :
    (stR s₀).Contains (st s₀ + BitVec.ofInt 64 (d : Int)) 32 :=
  contains_offset' (by omega) (by omega)

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa compress s₀ fun s' => gprPreserved s₀ s' ∧ Proof.Sha512.compressX86_64.post s₀ s' := by
  have in0 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((0 : Nat) : Int)) 32 :=
    ⟨stR s₀, by simp [hp.wr], st32 s₀ (by omega)⟩
  have in32 : InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .rdi + BitVec.ofInt 64 ((32 : Nat) : Int)) 32 :=
    ⟨stR s₀, by simp [hp.wr], st32 s₀ (by omega)⟩
  refine WP.seq (WP.mono (load_ok s₀ in0 in32)
    fun s₁ ⟨h1, h1', h2, h2', h8, h8', hzf, hg, hm, hrd, hwr⟩ => ?_)
  refine WP.seq (WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s₂ hc => ?_)
  · have hc₀ : Common s₀ 0 s₁ := ⟨h1, h1', h2, h2', fun r hr _ _ => hg r hr, hm, hrd, hwr⟩
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
          x8' := h8'
          rsi := by rw [hg .rsi (by decide)]; simp [blkAddr]
          rdx := by rw [hg .rdx (by decide)]; simp [nb] }
      exact WP.loop (M := isa) Inv hstep (nb s₀) s₁ ⟨0, rfl, hpos, hL₀⟩
  · have hrdi : s₂.gpr .rdi = st s₀ := hc.gpr .rdi (by decide) (by decide) (by decide)
    have out : ∀ d, d ≤ 32 → InRegions s₂.wr (s₂.gpr .rdi + BitVec.ofInt 64 ((d : Nat) : Int)) 32 :=
      fun d hd => ⟨stR s₀, by simp [hc.wr, hp.wr], by rw [hrdi]; exact st32 s₀ hd⟩
    refine WP.mono (store_ok s₂ _ hc.x1 hc.x1' hc.x2 hc.x2' (out 0 (by omega)) (out 32 (by omega)))
      fun s' ⟨⟨x, y, hm'⟩, hst, hg', _, _⟩ => ⟨⟨fun r hr => ?_, ?_⟩, ?_⟩
    · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
      rw [hg', hc.gpr r (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
        (by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · have hret : (retR s₀).Contains (s₀.gpr .rsp) 8 := Region.contains_self _ _
      rw [hm', hrdi, Mem.readW_writeW_sep (hp.ret_st.sep hret (st32 s₀ (by omega))) (by decide),
        Mem.readW_writeW_sep (hp.ret_st.sep hret (st32 s₀ (by omega))) (by decide), hc.mem]
    · show stateAt s'.mem (st s₀) = _
      rw [← hrdi]; exact hst

theorem compress_verified :
    Verified X86_64.target Impl.Sha512.X86_64.ShaNi.compress Proof.Sha512.compressX86_64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, abiPreserved_of_exec (by lit_decide) he h.1, h.2⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.rdi, .rsi, .rdx, .rcx]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4⟩
    refine Taint.agree_ofRegs fun r hr => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact (Proof.Sha512.X86_64.compress_verified).2.2

/-- `compress_verified`, with the scratch space of the shared contract (which it does not use). -/
theorem compressWide_verified :
    Verified X86_64.target Impl.Sha512.X86_64.ShaNi.compress Proof.Sha512.compressWideX86_64 :=
  Verified.widen compress_verified
    (fun s => [⟨s.gpr .rdi, 64⟩, ⟨s.gpr .rcx, 176⟩])
    (fun _ ⟨h₁, _, h₃, h₄, h₅, h₆, h₇⟩ =>
      ⟨h₁, rfl, h₃.sub_right (sub176 _), h₄, h₅.sub_right (sub176 _), h₆, h₇.sub_right (sub176 _)⟩)
    (fun _ ⟨_, h₂, _⟩ => h₂ ▸ .cons (pfx rfl) (.cons (pfx rfl) .nil))
    (fun _ _ _ h => h) (fun _ _ _ _ h => h)
    ⟨wideSat, rfl, rfl, Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide),
      Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide), Region.disjoint_of_sep (by decide)⟩

end VG.Proof.Sha512.X86_64.ShaNi
