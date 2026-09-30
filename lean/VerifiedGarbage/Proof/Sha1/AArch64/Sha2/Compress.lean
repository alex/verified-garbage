import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Spec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha1.AArch64.Sha2.Lit
import VerifiedGarbage.Proof.Sha1.AArch64.Compress

/-! Correctness of SHA-1 compression with the AArch64 SHA-2 instructions. -/

namespace VG.Proof.Sha1.AArch64.Sha2

open VG VG.AArch64 VG.Impl.Sha1.AArch64.Sha2
open VG.Spec.Sha1 (HashValue Word Block K W stateAt blockAt compressBlocks)

def kQuad (n : Nat) : BitVec 128 := ofVWords (K (4 * n)) (K (4 * n)) (K (4 * n)) (K (4 * n))

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), .v0, .v1, .v2, .v3, .v16, .v17].Nodup := by
  have key : ∀ c < 4,
      [msg c, msg (c + 1), msg (c + 2), msg (c + 3), .v0, .v1, .v2, .v3, .v16, .v17].Nodup := by decide
  have e : ∀ k, msg (n + k) = msg (n % 4 + k) := fun k => by
    simp only [msg]; rw [show (n % 4 + k) % 4 = (n + k) % 4 by omega]
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod], e 1, e 2, e 3]
  exact key _ (Nat.mod_lt _ (by decide))

theorem exec_vop (s : State) (op : VOp) :
    exec (.vop op) s = (VOp.eval s op).map (fun p => s.setV p.1 p.2) := rfl

theorem exec_ldrq {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions (s.rd ++ s.wr) (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.ldrq t n off) s = some (s.setV t (s.mem.read (s.gpr n + BitVec.ofNat 64 off) 16)) := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.load,
    h, Option.bind_some, Option.map_some]

theorem exec_strq {s : State} {t : VReg} {n : Reg} {off : Nat}
    (ho : off % 16 = 0 ∧ off < 65536)
    (h : InRegions s.wr (s.gpr n + BitVec.ofNat 64 off) 16) :
    exec (.strq t n off) s =
      some { s with mem := s.mem.write (s.gpr n + BitVec.ofNat 64 off) 16 (s.v t) } := by
  simp only [exec, addr, show 4096 * 16 = 65536 from rfl, ho, and_self, ite_true, State.store,
    h, Option.bind_some]

theorem rounds4_ok (n : Nat) (s : State) (v : HashValue) (q : BitVec 128)
    (h0 : s.v .v0 = abcd v) (h1 : s.v .v1 = eReg v) (hq : s.v (msg n) = q) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.v .v0 = sha1Hash (op n).f (abcd v) v[4] (VArr.s4.map2 (fun _ x y => x + y) (kQuad n) q) ∧
      s'.v .v1 = (v[0].rotateLeft 30).setWidth 128 ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hd := msg_nodup n
  apply WP.of_runBlock
  simp only [rounds4]
  generalize msg n = x at *
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hd
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_movz_w, exec_movk_w, exec_vop, VOp.eval,
    isa, RegUpd.v_setV, ite_true, ite_false, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_write_self, RegUpd.v_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits,
    Nat.reduceLeDiff, ite_true,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.map_some,
    hd, h0, h1, hq, eReg_low, vword_ofVWords_0, abcd,
    Option.some.injEq, exists_eq_left']
  have hc (x : BitVec 32) :
      (x.extractLsb' 0 16).setWidth 32 &&& (65535 : BitVec 32) |||
        (x.extractLsb' 16 16).setWidth 32 <<< 16 = x := by
    simpa only [BitVec.natCast_eq_ofNat, BitVec.ofNat_eq_ofNat] using VG.AArch64.movz_movk x
  simp only [hc, kQuad]
  refine ⟨trivial, trivial, fun r h0 h1 h2 h3 => ?_, fun r hr => ?_, trivial⟩
  · simp only [h0, h1, h2, h3, ite_false]
  · simp only [RegUpd.gpr_write_of_ne, hr, not_false_eq_true]

theorem schedule_hi (n : Nat) (hn : 4 ≤ n) (s : State) (a b c d : BitVec 128)
    (ha : s.v (msg n) = a) (hb : s.v (msg (n + 1)) = b) (hc : s.v (msg (n + 2)) = c)
    (hd' : s.v (msg (n + 3)) = d) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = sha1Su1 (sha1Su0 a b c) d ∧
      (∀ r, r ≠ msg n → s'.v r = s.v r) ∧
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
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, RegUpd.v_setV, ite_true, ite_false, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, hd'', ha, hb, hc, hd',
    Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 4) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = VRevOp.rev32b.eval (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) ∧
      (∀ r, r ≠ msg n → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [schedule, hn, ite_true]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, exec_ldrq, show 16 * n % 16 = 0 by omega, show 16 * n < 65536 by omega,
    and_self, ite_true, hin, Option.map_some,
    RegUpd.v_setV, ite_true, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr => by simp only [hr, ite_false], trivial⟩

theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 3) : msg k ≠ msg n := by
  have hd := msg_nodup k
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  rcases (by omega : n = k + 1 ∨ n = k + 2 ∨ n = k + 3) with rfl | rfl | rfl
  · exact hd.1.1
  · exact hd.1.2.1
  · exact hd.1.2.2.1

theorem msg_other (n : Nat) (r : VReg)
    (h : r = .v0 ∨ r = .v1 ∨ r = .v2 ∨ r = .v3 ∨ r = .v16 ∨ r = .v17) : msg n ≠ r := by
  have key : ∀ c < 4, ∀ r ∈ [VReg.v0, .v1, .v2, .v3, .v16, .v17], msg c ≠ r := by decide
  rw [show msg n = msg (n % 4) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r (by
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [List.mem_cons, true_or, or_true])

structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  v0 : s.v .v0 = abcd (Spec.Sha1.rounds H M (4 * n))
  v1 : s.v .v1 = eReg (Spec.Sha1.rounds H M (4 * n))
  msgs : ∀ k < n, n ≤ k + 4 → s.v (msg k) = quad M k
  keep : ∀ r, r = .v16 ∨ r = .v17 → s.v r = sB.v r
  gpr : ∀ r, r ≠ .x4 → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_four (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha1.rounds H M (4 * (n + 1)) =
      hw4 (op n) (Spec.Sha1.rounds H M (4 * n)) (K (4 * n))
        (W M (4 * n)) (W M (4 * n + 1)) (W M (4 * n + 2)) (W M (4 * n + 3)) := by
  rw [show 4 * (n + 1) = 4 * n + 3 + 1 by omega, rounds_succ, rounds_succ, rounds_succ, rounds_succ]
  rw [round_hw M _ n 3 (by decide), round_hw M _ n 2 (by decide), round_hw M _ n 1 (by decide)]
  have h := round_hw M (Spec.Sha1.rounds H M (4 * n)) n 0 (by decide)
  simp only [Nat.add_zero] at h
  rw [h]
  rfl

theorem rounds4_step (H : HashValue) (M : Block) (n : Nat) (s : State)
    (h0 : s.v .v0 = abcd (Spec.Sha1.rounds H M (4 * n)))
    (h1 : s.v .v1 = eReg (Spec.Sha1.rounds H M (4 * n))) (hq : s.v (msg n) = quad M n) :
    WP isa (.block (rounds4 n)) s fun s' =>
      s'.v .v0 = abcd (Spec.Sha1.rounds H M (4 * (n + 1))) ∧
      s'.v .v1 = eReg (Spec.Sha1.rounds H M (4 * (n + 1))) ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  refine WP.mono (rounds4_ok n s _ _ h0 h1 hq) fun s' ⟨e0, e1, hv, hg, hm, hrd, hwr⟩ => ?_
  have h := hash_eq (op n) (Spec.Sha1.rounds H M (4 * n)) (K (4 * n))
    (W M (4 * n)) (W M (4 * n + 1)) (W M (4 * n + 2)) (W M (4 * n + 3))
  simp only [VArr.map2, kQuad, quad, vword_ofVWords_0, vword_ofVWords_1,
    vword_ofVWords_2, vword_ofVWords_3] at e0
  rw [h] at e0
  exact ⟨by rw [rounds_four]; exact e0,
    by rw [rounds_four]; exact e1, hv, hg, hm, hrd, hwr⟩

theorem load_quad (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 4)
    (hblk : ∀ t : Nat, t < 16 → rev32 (m.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t) :
    VRevOp.rev32b.eval (m.read (bp + BitVec.ofNat 64 (16 * n)) 16) = quad M n := by
  apply vec_ext
  intro j hj
  rw [vword_rev32b _ hj, vword_read16 _ _ hj,
    Offset.add_add_eq _ (show 16 * n + 4 * j = 4 * (4 * n + j) by omega), hblk _ (by omega)]
  simp only [quad, vword_ofVWords _ _ _ _ hj]
  rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl

theorem rounds_ok (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .x1 = bp)
    (hin : ∀ n : Nat, n < 4 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (16 * n)) 16)
    (hblk : ∀ t : Nat, t < 16 →
      rev32 (sB.mem.readW (bp + BitVec.ofNat 64 (4 * t)) 32) = W M t)
    (h1 : sB.v .v0 = abcd H) (h2 : sB.v .v1 = eReg H) :
    ∀ n ≤ 20, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨h1, h2, fun _ h => absurd h (by omega), fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .x1 = bp := (hs.gpr .x1 (by decide)).trans hrsi
    -- The schedule replaces `msg n` with `quad M n`, preserving the other registers.
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.v (msg n) = quad M n ∧ (∀ r, r ≠ msg n → s₁.v r = s.v r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 4
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi, hs.mem]
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
    have o1 := msg_other n .v0 (by simp)
    have o2 := msg_other n .v1 (by simp)
    refine WP.mono (rounds4_step H M n s₁ (by rw [hx₁ _ (Ne.symm o1)]; exact hs.v0)
      (by rw [hx₁ _ (Ne.symm o2)]; exact hs.v1) hq)
      fun s₂ ⟨e1, e2, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨e1, e2, fun k hk hk' => ?_, fun r hr => ?_, fun r hr => ?_, by rw [hm₂, hm₁, hs.mem],
      by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · have n0 := msg_other k .v2 (by simp)
      have n1 := msg_other k .v0 (by simp)
      have n2 := msg_other k .v1 (by simp)
      have n11 := msg_other k .v3 (by simp)
      rw [hx₂ _ n1 n2 n0 n11]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega))]
        exact hs.msgs k (by omega) (by omega)
    · have := hr
      rcases hr with rfl | rfl <;>
      · rw [hx₂ _ (by decide) (by decide) (by decide) (by decide),
          hx₁ _ (Ne.symm (msg_other n _ (by simp)))]
        exact hs.keep _ (by simp)
    · rw [hg₂ r hr, hg₁, hs.gpr r hr]


theorem read_abcd (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 0) 16 = abcd (stateAt m p) := by
  rw [read16]
  simp only [abcd, stateAt_get _ _ (by decide : 0 < 5), stateAt_get _ _ (by decide : 1 < 5),
    stateAt_get _ _ (by decide : 2 < 5), stateAt_get _ _ (by decide : 3 < 5), BitVec.add_zero]

theorem read_e (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 16) 4 = (stateAt m p)[4] := by
  rw [stateAt_get _ _ (by decide : 4 < 5)]
  rfl

theorem write_pair (m : Mem) (p : Addr) (v : HashValue) :
    (m.write (p + BitVec.ofNat 64 0) 16 (abcd v)).write (p + BitVec.ofNat 64 16) 4 v[4] =
      writeState m p v := by
  simp only [abcd, write16, writeState, Nat.reduceMul, BitVec.add_zero, Mem.writeW, BitVec.setWidth_eq]

theorem load_ok (s : State)
    (h0 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 16) 4) :
    WP isa (.block load) s fun s' =>
      s'.v .v0 = abcd (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v1 = eReg (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v16 = abcd (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v17 = eReg (stateAt s.mem (s.gpr .x0)) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [load, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, VOp.eval, Option.bind_some, and_self, ite_true, ite_false, isa,
    Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.gpr_write_self,
    RegUpd.v_write, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, Size.bytes, Size.bits,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, vword_ofVWords_0,
    h0, h16, read_abcd, read_e, eReg, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial,
    fun r hr => by simp only [RegUpd.gpr_write_of_ne, RegUpd.gpr_setV, hr, not_false_eq_true], trivial⟩

theorem store_ok (s : State) (v H : HashValue)
    (hv0 : s.v .v0 = abcd v) (hv1 : s.v .v1 = eReg v)
    (hv16 : s.v .v16 = abcd H) (hv17 : s.v .v17 = eReg H)
    (h0 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 0) 16)
    (h16 : InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 16) 4) :
    WP isa (.block store) s fun s' =>
      s'.mem = writeState s.mem (s.gpr .x0) (Vector.zipWith (· + ·) v H) ∧
      s'.gpr .x1 = s.gpr .x1 + 64 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have he (v : HashValue) : (eReg v).extractLsb' (32 * 0) 32 = v[4] := eReg_low v
  apply WP.of_runBlock
  simp (config := {decide := true}) only [store, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, VOp.eval, Option.bind_some, and_self, ite_true, ite_false, isa,
    State.read, Size.bits, Size.bytes, Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV,
    RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_write_self, RegUpd.v_write,
    RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    h0, h16, hv0, hv1, hv16, hv17, add_abcd, add_eReg, he, write_pair,
    BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, fun r h1 h2 h4 => by
    simp only [RegUpd.gpr_write_of_ne, h1, h2, h4, not_false_eq_true], trivial⟩

theorem Pre.in_blk16 {s₀ : State} (hp : AArch64.Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 4) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * n)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (64 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem body_ok {s₀ : State} (hp : AArch64.Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hin : ∀ d k, d + k ≤ 20 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) k := by
    intro d k hd
    refine ⟨stR s₀, by simp [hL.wr, hp.wr], ?_⟩
    rw [hL.x0]; exact contains_offset (by omega) (by omega)
  refine WP.seq ((load_ok s (hin 0 16 (by decide)) (hin 16 4 (by decide))).mono
    fun s₁ ⟨hv0, hv1, hv16, hv17, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hblk : ∀ t : Nat, t < 16 →
      rev32 (s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (4 * t)) 32) = W (blk s₀ i) t := by
    intro t ht
    rw [hm₁, hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  refine WP.seq ((rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁ .x1 (by decide), hL.x1])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    hblk hv0 hv1 20 (Nat.le_refl _)).mono fun s₂ hR => ?_)
  have hg₂ : ∀ r, r ≠ .x4 → s₂.gpr r = s.gpr r := fun r hr => by rw [hR.gpr r hr, hg₁ r hr]
  have hout : ∀ d k, d + k ≤ 20 → InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 d) k := by
    intro d k hd
    refine ⟨stR s₀, by simp [hR.wr, hwr₁, hL.wr, hp.wr], ?_⟩
    rw [hg₂ .x0 (by decide), hL.x0]; exact contains_offset (by omega) (by omega)
  refine (store_ok s₂ _ (stateAt s.mem (s.gpr .x0)) hR.v0 hR.v1
    (by rw [hR.keep .v16 (.inl rfl), hv16]) (by rw [hR.keep .v17 (.inr rfl), hv17])
    (hout 0 16 (by decide)) (hout 16 4 (by decide))).mono fun s₃ ⟨hm₃, hx1₃, hx2₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg₂ .x2 (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [hm₃, hR.mem, hm₁, hg₂ .x0 (by decide), hL.x0]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hg₃ .x0 (by decide) (by decide) (by decide), hg₂ .x0 (by decide), hL.x0],
      by rw [hg₃ .x3 (by decide) (by decide) (by decide), hg₂ .x3 (by decide), hL.x3],
      ?_, by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    · intro r hr
      have key : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 := by decide
      have hn := key r hr
      rw [hg₃ r hn.1 hn.2.1 hn.2.2, hg₂ r hn.2.2, hL.kept r hr]
    · rw [hm₃, hg₂ .x0 (by decide), hL.x0, stateAt_writeState,
        compressBlocks_succ, ← hL.state]
      rfl
  have hev : eval (.nonzero .x .x2) s₃ = some (BitVec.ofNat 64 (nb s₀ - (i + 1)) != 0) := by
    simp only [eval, State.read, Size.bits, BitVec.setWidth_eq, hx2₃, hx2]
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · exact .inl ⟨by rw [hev, hlast]; simp, hlast ▸ hcommon⟩
  · have hne : nb s₀ - (i + 1) ≠ 0 := by omega
    have h0 : BitVec.ofNat 64 (nb s₀ - (i + 1)) ≠ 0 := by
      intro h
      have h' := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
      exact hne h'
    refine .inr ⟨by rw [hev]; simpa using h0, by omega, { hcommon with x1 := ?_, x2 := ?_ }⟩
    · rw [hx1₃, hg₂ .x1 (by decide), hL.x1]
      exact (Offset.add_add _ _ 64).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [hx2₃, hx2]

theorem correct {s₀ : State} (hp : AArch64.Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha1.compressAArch64.post s₀ s' := by
  have hc₀ : Common s₀ 0 s₀ :=
    ⟨rfl, rfl, fun _ _ => rfl, rfl, rfl, Frame.refl _ _, rfl⟩
  refine WP.mono (Q := Common s₀ (nb s₀)) ?_ fun s' hc => ⟨hc.kept, hc.state⟩
  refine WP.ite (s₀.gpr .x2 == 0) (by simp [eval, State.read]) (fun h => ?_) (fun h => ?_)
  · have h0 : nb s₀ = 0 := by simp at h; simp [nb, h]
    exact WP.block_nil (M := isa) (h0 ▸ hc₀)
  · have hpos : 0 < nb s₀ := by
      simp only [beq_eq_false_iff_ne, ne_eq] at h
      exact Nat.pos_of_ne_zero fun h' => h (BitVec.eq_of_toNat_eq (by simpa using h'))
    let Inv : Nat → State → Prop := fun m s => ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL⟩
      refine WP.mono (body_ok hp hi hL) fun s' h => ?_
      rcases h with ⟨he, hc⟩ | ⟨he, hi', hL'⟩
      · exact .inl ⟨he, hc⟩
      · exact .inr ⟨he, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL'⟩
    have hL₀ : LInv s₀ 0 s₀ :=
      { hc₀ with
        x1 := by simp [blkAddr]
        x2 := by simp [nb] }
    exact WP.loop (M := isa) Inv hstep (nb s₀) s₀ ⟨0, rfl, hpos, hL₀⟩


theorem compress_verified :
    Verified AArch64.target Impl.Sha1.AArch64.Sha2.compress Proof.Sha1.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact AArch64.compress_verified.2.2

end VG.Proof.Sha1.AArch64.Sha2
