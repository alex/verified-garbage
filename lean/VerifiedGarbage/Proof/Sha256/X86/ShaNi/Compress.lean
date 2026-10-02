import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.SseRegUpd
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Spec
import VerifiedGarbage.Impl.Sha256.X86.ShaNi
import VerifiedGarbage.Proof.Sha256.X86.Compress
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Memory
import VerifiedGarbage.Proof.Sha256.X86.ShaNi.Const

namespace VG.Proof.Sha256.X86.ShaNi
open VG VG.X86 VG.Impl.Sha256.X86.ShaNi
open VG.Spec.Sha256 (HashValue Word Block K W stateAt blockAt compressBlocks compress)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem const_ok (c : BitVec 128) (s : State) :
    WP isa (.block (const c)) s fun s' =>
      s'.xmm .xmm0 = c ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.zf = s.zf := by
  have ldq : ∀ a b, XBinOp.eval .punpckldq a b =
      ofDwords (dword a 0) (dword b 0) (dword a 1) (dword b 1) := fun _ _ => rfl
  apply WP.of_runBlock
  simp (config := {decide := true}) only [const, runBlock_cons, runStep_some, runBlock_nil,
    exec, readSrc, XOp.exec, isa, movd_value, ldq,
    dword_ofDwords_0, dword_ofDwords_1, punpcklqdq_eq,
    shift_last_value,
    RegUpd.gpr_setReg_self,
    RegUpd.mem_setReg, RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, fun r h0 h7 => ?_, fun r hr => ?_, trivial⟩
  · exact (or_last_value _ _ _ _).trans (ofDwords_dword c)
  · simp only [RegUpd.xmm_setReg, RegUpd.xmm_setXmm_of_ne, h0, h7, not_false_eq_true]
  · simp only [RegUpd.gpr_setXmm, RegUpd.gpr_setReg_of_ne, hr, not_false_eq_true]

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
  have key : ∀ c < 4, [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .xmm0, .xmm1, .xmm2, .xmm7].Nodup := by
    decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem roundOps_ok (n : Nat) (s : State) (v : HashValue) (q k : BitVec 128)
    (h0 : s.xmm .xmm0 = k) (h1 : s.xmm .xmm1 = abef v)
    (h2 : s.xmm .xmm2 = cdgh v) (hq : s.xmm (msg n) = q) :
    WP isa (.block (roundOps n)) s fun s' =>
      s'.xmm .xmm1 = sha256Rnds2 (abef v) (sha256Rnds2 (cdgh v) (abef v)
        (XBinOp.eval .paddd k q)) (shufDwords (XBinOp.eval .paddd k q) 0x0e) ∧
      s'.xmm .xmm2 = sha256Rnds2 (cdgh v) (abef v) (XBinOp.eval .paddd k q) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [roundOps]
  generalize msg n = x at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, reduceCtorEq, hd, h0, h1, h2, hq,
    Option.some.injEq, exists_eq_left']
  refine ⟨trivial, trivial, fun r h0 h1 h2 => ?_, trivial⟩
  simp only [RegUpd.xmm_setXmm_of_ne, h0, h1, h2, not_false_eq_true]

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
    (hin : InRegions (s.rd ++ s.wr) (addr (s.gpr .edi) (16 * n)) 16)
    (hmask : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 16) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.xmm (msg n) = XBinOp.eval .pshufb
        (s.mem.readW (addr (s.gpr .edi) (16 * n)) 128)
        (s.mem.readW (addr (s.gpr .esi) 16) 128) ∧
      (∀ r, r ≠ msg n → r ≠ .xmm0 → s'.xmm r = s.xmm r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  generalize msg n = x₀ at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, XOp.exec,
    isa, RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm, RegUpd.mem_setXmm,
    RegUpd.rd_setXmm, RegUpd.wr_setXmm, not_false_eq_true, State.load128, ea_at, hin,
    hmask, ite_true, hd, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r h0 hx => by simp only [RegUpd.xmm_setXmm_of_ne, h0, hx, not_false_eq_true], trivial⟩

theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1


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


theorem msg_other (n : Nat) (r : XReg)
    (h : r = .xmm0 ∨ r = .xmm1 ∨ r = .xmm2 ∨ r = .xmm7) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [XReg.xmm0, .xmm1, .xmm2, .xmm7], msg c ≠ r := by
    decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q : BitVec 128)
    (h1 : s.xmm .xmm1 = abef v) (h2 : s.xmm .xmm2 = cdgh v)
    (hq : s.xmm (msg n) = q)
:
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = sha256Rnds2 (abef v) (sha256Rnds2 (cdgh v) (abef v)
        (XBinOp.eval .paddd (kQuad (4 * n)) q))
        (shufDwords (XBinOp.eval .paddd (kQuad (4 * n)) q) 0x0e) ∧
      s'.xmm .xmm2 = sha256Rnds2 (cdgh v) (abef v) (XBinOp.eval .paddd (kQuad (4 * n)) q) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  rw [rounds4, WP.block_append_iff]
  refine WP.mono (const_ok (kQuad (4 * n)) s)
    fun s₁ ⟨h0, hx, hg, hm, hrd, hwr, _⟩ => ?_
  have hq₁ : s₁.xmm (msg n) = q := (hx _ (msg_other n _ (.inl rfl)) (msg_other n _ (.inr (.inr (.inr rfl))))).trans hq
  refine WP.mono (roundOps_ok n s₁ v q (kQuad (4 * n)) h0
    ((hx _ (by decide) (by decide)).trans h1) ((hx _ (by decide) (by decide)).trans h2) hq₁)
    fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
  exact ⟨e1, e2, fun r h0 h1 h2 h7 => (hx₂ r h0 h1 h2).trans (hx r h0 h7),
    fun r hr => (congrFun hg₂ r).trans (hg r hr), hm₂.trans hm,
    hrd₂.trans hrd, hwr₂.trans hwr⟩

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h1 : s.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * n)))
    (h2 : s.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * n)))
    (hq : s.xmm (msg n) = quad M n)
:
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      s'.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → r ≠ .xmm7 → s'.xmm r = s.xmm r) ∧
      (∀ r, r ≠ .eax → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ h1 h2 hq)
    fun s' ⟨e1, e2, hx, hg, hm, hrd, hwr⟩ => ?_
  obtain ⟨k0, k1, k2, k3⟩ := kq_quad n M
  rw [rnds2_eq _ _ k0 k1] at e1 e2
  rw [← cdgh_two (Spec.Sha256.rounds H M (4 * n)) (K (4 * n)) (W M (4 * n))
    (K (4 * n + 1)) (W M (4 * n + 1)), rnds2_eq _ _ k2 k3] at e1
  exact ⟨by rw [e1, rounds_four], by rw [e2, rounds_four, cdgh_two], hx, hg, hm, hrd, hwr⟩

structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  x1 : s.xmm .xmm1 = abef (Spec.Sha256.rounds H M (4 * n))
  x2 : s.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.xmm (msg k) = quad M k
  gpr : ∀ r, r ≠ .eax → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 →
      bswap (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    XBinOp.eval .pshufb (m.readW (bp + BitVec.ofNat 64 (16 * n)) 128) bswapMask = quad M n := by
  rw [show bswapMask = 0x0c0d0e0f08090a0b0405060700010203#128 from rfl, pshufb_bswap]
  have e : ∀ j, j < 4 → bswap (dword (m.readW (bp + BitVec.ofNat 64 (16 * n)) 128) j) =
      W M (4 * n + j) := by
    intro j hj
    rw [dword_readW _ _ hj, ← hblk (4 * n + j) (by omega)]
    refine congrArg (fun a => bswap (m.readW a 32)) ?_
    exact Offset.add_add_eq _ (by omega)
  rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega)]
  rfl

theorem rounds_ok (H : HashValue) (M : Block) (bp scr : BitVec 32) (sB : State)
    (hrdi : sB.gpr .edi = bp) (hrsi : sB.gpr .esi = scr)
    (hbpFit : bp.toNat + 64 ≤ 2 ^ 32) (hscFit : scr.toNat + 32 ≤ 2 ^ 32)
    (hin : ∀ n < 4, InRegions (sB.rd ++ sB.wr)
      (bp.setWidth 64 + BitVec.ofNat 64 (16 * n)) 16)
    (hinMask : InRegions (sB.rd ++ sB.wr) (scr.setWidth 64 + BitVec.ofNat 64 16) 16)
    (hmask : sB.mem.readW (scr.setWidth 64 + BitVec.ofNat 64 16) 128 = bswapMask)
    (hblk : ∀ t < 16, bswap (sB.mem.readW
      (bp.setWidth 64 + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h1 : sB.xmm .xmm1 = abef H) (h2 : sB.xmm .xmm2 = cdgh H) :
    ∀ n ≤ 16, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h1, h2, fun _ h => absurd h (by omega),
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hdi : s.gpr .edi = bp := (hs.gpr .edi (by decide)).trans hrdi
    have hsi : s.gpr .esi = scr := (hs.gpr .esi (by decide)).trans hrsi
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.xmm (msg n) = quad M n ∧
        (∀ r, r ≠ msg n → r ≠ .xmm0 → r ≠ .xmm7 → s₁.xmm r = s.xmm r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · have eaB : addr (s.gpr .edi) (16 * n) = bp.setWidth 64 + BitVec.ofNat 64 (16 * n) := by
          rw [hdi]; exact addr_eq (by omega)
        have eaS : addr (s.gpr .esi) 16 = scr.setWidth 64 + BitVec.ofNat 64 16 := by
          rw [hsi]; exact addr_eq (by omega)
        refine WP.mono (schedule_lo n hlo s (by rw [eaB, hs.rd, hs.wr]; exact hin n hlo)
          (by rw [eaS, hs.rd, hs.wr]; exact hinMask))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr h0 _ => hx r hr h0, hg, hm, hrd, hwr⟩
        rw [e, eaB, eaS, hs.mem, hmask]
        exact load_quad M sB.mem (bp.setWidth 64) hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 4 := ⟨n - 4, by omega⟩
        refine WP.mono (schedule_hi (i + 4) (by omega) s (quad M i) (quad M (i + 1))
          (quad M (i + 2)) (quad M (i + 3)) ?_ ?_ ?_ ?_)
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr _ h7 => hx r hr h7, hg, hm, hrd, hwr⟩
        · rw [msg_add4]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 4 + 1 = i + 1 + 4 by omega, msg_add4]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 4 + 2 = i + 2 + 4 by omega, msg_add4]; exact hs.msgs (i + 2) (by omega) (by omega)
        · rw [show i + 4 + 3 = i + 3 + 4 by omega, msg_add4]; exact hs.msgs (i + 3) (by omega) (by omega)
        · rw [e]; exact schedule_eq M i
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have o1 := msg_other n .xmm1 (.inr (.inl rfl))
    have o2 := msg_other n .xmm2 (.inr (.inr (.inl rfl)))
    refine WP.mono (rounds4_step H M n s₁
      (by rw [hx₁ _ (Ne.symm o1) (by decide) (by decide)]; exact hs.x1)
      (by rw [hx₁ _ (Ne.symm o2) (by decide) (by decide)]; exact hs.x2) hq)
      fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e2, fun k hk hk' => ?_, fun r hr => ?_, ?_,
      hrd₂.trans (hrd₁.trans hs.rd), hwr₂.trans (hwr₁.trans hs.wr)⟩
    · rw [hx₂ _ (msg_other k _ (.inl rfl)) (msg_other k _ (.inr (.inl rfl)))
        (msg_other k _ (.inr (.inr (.inl rfl)))) (msg_other k _ (.inr (.inr (.inr rfl))))]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega)) (msg_other k _ (.inl rfl))
          (msg_other k _ (.inr (.inr (.inr rfl))))]
        exact hs.msgs k (by omega) (by omega)
    · exact (hg₂ r hr).trans ((congrFun hg₁ r).trans (hs.gpr r hr))
    · exact hm₂.trans (hm₁.trans hs.mem)

theorem loadState_ok (s : State)
    (hfit : (s.gpr .ebx).toNat + 32 ≤ 2 ^ 32)
    (hlo : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64) 16)
    (hhi : InRegions (s.rd ++ s.wr) ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) 16) :
    WP isa (.block loadState) s fun s' =>
      s'.xmm .xmm1 = abef (stateAt s.mem ((s.gpr .ebx).setWidth 64)) ∧
      s'.xmm .xmm2 = cdgh (stateAt s.mem ((s.gpr .ebx).setWidth 64)) ∧
      s'.zf = s.zf ∧ s'.gpr = s.gpr ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea0 : addr (s.gpr .ebx) 0 = (s.gpr .ebx).setWidth 64 := by
    rw [addr_eq (by omega)]; exact BitVec.add_zero _
  have ea16 : addr (s.gpr .ebx) 16 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16 :=
    addr_eq (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [loadState, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, isa, State.load128, ea_at, ea0, ea16, hlo, hhi, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm, RegUpd.zf_setXmm,
    reduceCtorEq, not_false_eq_true, eval_movdqa,
    Option.map_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial⟩ <;>
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, abef, cdgh, stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 0 < 4 by decide),
    stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 1 < 4 by decide), stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 2 < 4 by decide),
    stateAt_lo s.mem ((s.gpr .ebx).setWidth 64) (show 3 < 4 by decide), stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 0 < 4 by decide),
    stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 1 < 4 by decide), stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 2 < 4 by decide),
    stateAt_hi s.mem ((s.gpr .ebx).setWidth 64) (show 3 < 4 by decide)]

theorem store_ok (s : State) (v : HashValue)
    (h1 : s.xmm .xmm1 = abef v) (h2 : s.xmm .xmm2 = cdgh v)
    (hfit : (s.gpr .ebx).toNat + 32 ≤ 2 ^ 32)
    (hlo : InRegions s.wr ((s.gpr .ebx).setWidth 64) 16)
    (hhi : InRegions s.wr ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) 16) :
    WP isa (.block store) s fun s' =>
      (∃ x y : BitVec 128, s'.mem = (s.mem.writeW ((s.gpr .ebx).setWidth 64) x).writeW
        ((s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16) y) ∧
      stateAt s'.mem ((s.gpr .ebx).setWidth 64) = v ∧
      s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have ea0 : addr (s.gpr .ebx) 0 = (s.gpr .ebx).setWidth 64 := by
    rw [addr_eq (by omega)]; exact BitVec.add_zero _
  have ea16 : addr (s.gpr .ebx) 16 = (s.gpr .ebx).setWidth 64 + BitVec.ofNat 64 16 :=
    addr_eq (by omega)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [store, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, isa, State.store128, ea_at, ea0, ea16, hlo, hhi, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    reduceCtorEq, not_false_eq_true, h1, h2, eval_movdqa,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨_, _, rfl⟩, ?_, trivial⟩
  rw [stateAt_store]
  simp only [punpcklqdq_eq, punpckhqdq_eq, shufDwords_b1, dword_ofDwords_0, dword_ofDwords_1,
    dword_ofDwords_2, dword_ofDwords_3, abef, cdgh]
  apply Vector.ext
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem saveHash_ok (s : State)
    (h32 : InRegions s.wr (addr (s.gpr .esi) 32) 16)
    (h48 : InRegions s.wr (addr (s.gpr .esi) 48) 16) :
    WP isa (.block saveHash) s fun s' =>
      s'.mem = (s.mem.writeW (addr (s.gpr .esi) 32) (s.xmm .xmm1)).writeW
        (addr (s.gpr .esi) 48) (s.xmm .xmm2) ∧
      s'.xmm = s.xmm ∧ s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [saveHash, runBlock_cons, runStep_some, runBlock_nil, exec, isa, State.store128,
    ea_at, h32, h48, ite_true, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

theorem finishBlock_ok (s : State) (H : HashValue) (M : Block)
    (h1 : s.xmm .xmm1 = abef (Spec.Sha256.rounds H M 64))
    (h2 : s.xmm .xmm2 = cdgh (Spec.Sha256.rounds H M 64))
    (h32 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 32) 16)
    (h48 : InRegions (s.rd ++ s.wr) (addr (s.gpr .esi) 48) 16)
    (v32 : s.mem.readW (addr (s.gpr .esi) 32) 128 = abef H)
    (v48 : s.mem.readW (addr (s.gpr .esi) 48) 128 = cdgh H) :
    WP isa (.block finishBlock) s fun s' =>
      s'.xmm .xmm1 = abef (compress H M) ∧ s'.xmm .xmm2 = cdgh (compress H M) ∧
      s'.gpr .edi = s.gpr .edi + 64 ∧ s'.gpr .ebp = s.gpr .ebp - 1 ∧
      (∀ r, r ≠ .edi → r ≠ .ebp → s'.gpr r = s.gpr r) ∧
      s'.zf = some (s.gpr .ebp - 1 == 0) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [finishBlock, runBlock_cons, runStep_some, runBlock_nil,
    exec, XOp.exec, execAlu, readSrc, isa, State.load128, ea_at, h32, h48, ite_true,
    RegUpd.xmm_setXmm_self, RegUpd.xmm_setXmm_of_ne, RegUpd.gpr_setXmm,
    RegUpd.mem_setXmm, RegUpd.rd_setXmm, RegUpd.wr_setXmm,
    RegUpd.gpr_setReg_self, RegUpd.gpr_setReg_of_ne, RegUpd.mem_setReg,
    RegUpd.rd_setReg, RegUpd.wr_setReg, RegUpd.xmm_setReg,
    RegUpd.gpr_arithFlags, RegUpd.mem_arithFlags, RegUpd.rd_arithFlags,
    RegUpd.wr_arithFlags, RegUpd.xmm_arithFlags, RegUpd.zf_arithFlags, RegUpd.zf_setReg,
    reduceCtorEq, not_false_eq_true, h1, h2, v32, v48, paddd_abef, paddd_cdgh,
    Option.map_some, Option.bind_some, Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, trivial, trivial, fun r hdi hbp => ?_, trivial⟩
  · rfl
  · rfl
  · simp only [RegUpd.gpr_arithFlags, RegUpd.gpr_setReg_of_ne, hdi, hbp, not_false_eq_true,
      RegUpd.gpr_setXmm]

end VG.Proof.Sha256.X86.ShaNi
