import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Spec
import VerifiedGarbage.Proof.Framework.AArch64.SimdMem64
import VerifiedGarbage.Proof.Framework.AArch64.RegUpd
import VerifiedGarbage.Proof.Sha512.AArch64.Sha3.Lit
import VerifiedGarbage.Proof.Sha512.AArch64.Compress

/-! Correctness of SHA-512 compression with the AArch64 SHA512 instructions. -/

namespace VG.Proof.Sha512.AArch64.Sha3

open VG VG.AArch64 VG.Impl.Sha512.AArch64.Sha3
open VG.Spec.Sha512 (HashValue Word Block K W stateAt blockAt compressBlocks)

def kPair (n : Nat) : BitVec 128 := ofVDwords (K (2 * n)) (K (2 * n + 1))

theorem msg_add8 (n : Nat) : msg (n + 8) = msg n := by
  simp only [msg, Nat.add_mod_right]

theorem msg_other (n : Nat) :
    msg n ≠ .v0 ∧ msg n ≠ .v1 ∧ msg n ≠ .v2 ∧ msg n ≠ .v3 ∧
    msg n ≠ .v4 ∧ msg n ≠ .v5 ∧ msg n ≠ .v6 ∧
    msg n ≠ .v24 ∧ msg n ≠ .v25 ∧ msg n ≠ .v26 ∧ msg n ≠ .v27 := by
  have key : ∀ c < 8,
    msg c ≠ .v0 ∧ msg c ≠ .v1 ∧ msg c ≠ .v2 ∧ msg c ≠ .v3 ∧
    msg c ≠ .v4 ∧ msg c ≠ .v5 ∧ msg c ≠ .v6 ∧
    msg c ≠ .v24 ∧ msg c ≠ .v25 ∧ msg c ≠ .v26 ∧ msg c ≠ .v27 := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide))

theorem msg_ne (n k : Nat) (h₁ : k < n) (h₂ : n ≤ k + 7) : msg k ≠ msg n := by
  have key : ∀ i < 8, ∀ j < 8, msg i = msg j → i = j := by decide
  intro h
  have e : k % 8 = n % 8 := key (k % 8) (by omega) (n % 8) (by omega) (by
    simpa only [msg, Nat.mod_mod] using h)
  omega

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


structure Vars (s : State) (v : HashValue) : Prop where
  v0 : s.v .v0 = ab v
  v1 : s.v .v1 = cd v
  v2 : s.v .v2 = ef v
  v3 : s.v .v3 = gh v

theorem constants_ok (n : Nat) (s : State) :
    WP isa (.block (constant n 0 ++ constant n 1)) s fun s' =>
      s'.v .v4 = kPair n ∧ (∀ r, r ≠ .v4 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp only [constant, List.cons_append, List.nil_append, ite_true, show ¬ (1 : Nat) = 0 by decide,
    ite_false]
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.eval,
    isa, State.read, RegUpd.v_setV, ite_true, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, RegUpd.gpr_write_self, RegUpd.v_write,
    RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write, Size.bits,
    BitVec.setWidth_eq, Option.map_some, setLane_pair_hi, movz_movk64', Nat.add_zero,
    Option.some.injEq, exists_eq_left']
  refine ⟨rfl, fun r hr => ?_, fun r hr => ?_, trivial⟩
  · simp only [hr, ite_false]
  · simp only [RegUpd.gpr_setV, RegUpd.gpr_write_of_ne, hr, not_false_eq_true]

theorem rounds2_ok (n : Nat) (s : State) (v : HashValue) (M : Block)
    (hv : Vars s v) (hq : s.v (msg n) = pair M n) :
    WP isa (.block (rounds2 n)) s fun s' =>
      Vars s' (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → r ≠ .v4 → r ≠ .v5 → r ≠ .v6 → s'.v r = s.v r) ∧
      (∀ r, r ≠ .x4 → s'.gpr r = s.gpr r) ∧
      s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  simp only [rounds2, List.append_assoc]
  rw [← List.append_assoc, WP.block_append_iff]
  refine (constants_ok n s).mono fun s₁ ⟨hk, hvk, hgk, hmk, hrdk, hwrk⟩ => ?_
  have hd := msg_other n
  have h0 := (hvk .v0 (by decide)).trans hv.v0
  have h1 := (hvk .v1 (by decide)).trans hv.v1
  have h2 := (hvk .v2 (by decide)).trans hv.v2
  have h3 := (hvk .v3 (by decide)).trans hv.v3
  have hq' := (hvk (msg n) hd.2.2.2.2.1).trans hq
  apply WP.of_runBlock
  generalize msg n = x at *
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, RegUpd.v_setV, ite_true, ite_false, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, Option.map_some, h0, h1, h2, h3, hq', hk,
    Option.some.injEq, exists_eq_left']
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, hgk, hmk, hrdk, hwrk⟩
  rotate_right
  · intro r h0 h1 h2 h3 h4 h5 h6
    simp only [h0, h1, h2, h3, h4, h5, h6, ite_false]
    exact hvk r h4
  · have hab := h2_eq v (K (2 * n)) (W M (2 * n)) (K (2 * n + 1)) (W M (2 * n + 1))
    simp only [kPair, pair, ab, cd, ef, gh, VArr.map2, vdword_ofVDwords_0, vdword_ofVDwords_1, ext8_pair, h_eq]
    exact hab
  · exact (cd_eq _ _ _ _ _).symm
  · have hef := ef_eq v (K (2 * n)) (W M (2 * n)) (K (2 * n + 1)) (W M (2 * n + 1))
    simp only [kPair, pair, ab, cd, ef, gh, VArr.map2, vdword_ofVDwords_0, vdword_ofVDwords_1, ext8_pair, h_eq] at hef ⊢
    exact hef
  · exact (gh_eq _ _ _ _ _).symm

theorem msg_not (n : Nat) {r : VReg}
    (hr : r ∈ [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v24, .v25, .v26, .v27]) : msg n ≠ r := by
  have key : ∀ c < 8, ∀ r ∈ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v24, .v25, .v26, .v27],
    msg c ≠ r := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r hr

theorem schedule_hi (n : Nat) (hn : 8 ≤ n) (s : State) (a b c d e : BitVec 128)
    (ha : s.v (msg n) = a) (hb : s.v (msg (n + 1)) = b) (hc : s.v (msg (n + 4)) = c)
    (hd' : s.v (msg (n + 5)) = d) (he : s.v (msg (n + 7)) = e) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = sha512Su1 (sha512Su0 a b) e (((d ++ c) >>> (8 * 8)).extractLsb' 0 128) ∧
      (∀ r, r ≠ msg n → r ≠ .v6 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := msg_not n (r := .v6) (by decide)
  have h1 := msg_not (n + 1) (r := .v6) (by decide)
  have h7 := msg_not (n + 7) (r := .v6) (by decide)
  have hn7 := Ne.symm (msg_ne (n + 7) n (by omega) (by omega))
  apply WP.of_runBlock
  simp only [schedule, show ¬ n < 8 by omega, ite_false]
  generalize msg n = x₀ at *
  generalize msg (n + 1) = x₁ at *
  generalize msg (n + 4) = x₄ at *
  generalize msg (n + 5) = x₅ at *
  generalize msg (n + 7) = x₇ at *
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, RegUpd.v_setV, ite_true, ite_false, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, h0, h1, h7, hn7, ha, hb, hc, hd', he,
    Ne.symm h0, Option.map_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, fun r hr h6 => by simp only [hr, h6, ite_false], trivial⟩

theorem schedule_lo (n : Nat) (hn : n < 8) (s : State)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) :
    WP isa (.block (schedule n)) s fun s' =>
      s'.v (msg n) = VRevOp.rev64b.eval (s.mem.read (s.gpr .x1 + BitVec.ofNat 64 (16 * n)) 16) ∧
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

structure RInv (H : HashValue) (M : Block) (sB : State) (n : Nat) (s : State) : Prop where
  vars : Vars s (Spec.Sha512.rounds H M (2 * n))
  msgs : ∀ k < n, n ≤ k + 8 → s.v (msg k) = pair M k
  keep : ∀ r ∈ [VReg.v24, .v25, .v26, .v27], s.v r = sB.v r
  gpr : ∀ r, r ≠ .x4 → s.gpr r = sB.gpr r
  mem : s.mem = sB.mem
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr

theorem rounds_two (H : HashValue) (M : Block) (n : Nat) :
    Spec.Sha512.rounds H M (2 * (n + 1)) =
      roundKW (roundKW (Spec.Sha512.rounds H M (2 * n)) (K (2 * n)) (W M (2 * n)))
        (K (2 * n + 1)) (W M (2 * n + 1)) := by
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega, rounds_succ, rounds_succ]
  rfl

theorem load_pair (M : Block) (m : Mem) (bp : Addr) {n : Nat} (hn : n < 8)
    (hblk : ∀ t : Nat, t < 16 → rev64 (m.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t) :
    VRevOp.rev64b.eval (m.read (bp + BitVec.ofNat 64 (16 * n)) 16) = pair M n := by
  have hj (j : Nat) (hj : j < 2) :
      vdword (VRevOp.rev64b.eval (m.read (bp + BitVec.ofNat 64 (16 * n)) 16)) j = W M (2 * n + j) := by
    rw [vdword_rev64b _ hj, vdword_read16 _ _ hj,
      Offset.add_add_eq _ (show 16 * n + 8 * j = 8 * (2 * n + j) by omega), hblk _ (by omega)]
  apply vec64_ext
  · simpa only [pair, vdword_ofVDwords_0, Nat.add_zero] using hj 0 (by decide)
  · simpa only [pair, vdword_ofVDwords_1] using hj 1 (by decide)

theorem rounds_ok (H : HashValue) (M : Block) (bp : Addr) (sB : State)
    (hrsi : sB.gpr .x1 = bp)
    (hin : ∀ n : Nat, n < 8 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (16 * n)) 16)
    (hblk : ∀ t : Nat, t < 16 →
      rev64 (sB.mem.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
    (hv : Vars sB H) :
    ∀ n ≤ 40, WP isa (rounds n) sB (RInv H M sB n) := by
  intro n hn
  induction n with
  | zero =>
    exact WP.block_nil (M := isa) ⟨hv, fun _ h => absurd h (by omega), fun _ _ => rfl,
      fun _ _ => rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [WP.block_append_iff]
    have hs_rsi : s.gpr .x1 = bp := (hs.gpr .x1 (by decide)).trans hrsi
    have hsched : WP isa (.block (schedule n)) s fun s₁ =>
        s₁.v (msg n) = pair M n ∧ (∀ r, r ≠ msg n → r ≠ .v6 → s₁.v r = s.v r) ∧
        s₁.gpr = s.gpr ∧ s₁.mem = s.mem ∧ s₁.rd = s.rd ∧ s₁.wr = s.wr := by
      by_cases hlo : n < 8
      · refine WP.mono (schedule_lo n hlo s (by rw [hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr _ => hx r hr, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi, hs.mem]
        exact load_pair M sB.mem bp hlo hblk
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 8 := ⟨n - 8, by omega⟩
        refine WP.mono (schedule_hi (i + 8) (by omega) s (pair M i) (pair M (i + 1)) (pair M (i + 4))
          (pair M (i + 5)) (pair M (i + 7)) ?_ ?_ ?_ ?_ ?_)
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [msg_add8]; exact hs.msgs i (by omega) (by omega)
        · rw [show i + 8 + 1 = i + 1 + 8 by omega, msg_add8]; exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [show i + 8 + 4 = i + 4 + 8 by omega, msg_add8]; exact hs.msgs (i + 4) (by omega) (by omega)
        · rw [show i + 8 + 5 = i + 5 + 8 by omega, msg_add8]; exact hs.msgs (i + 5) (by omega) (by omega)
        · rw [show i + 8 + 7 = i + 7 + 8 by omega, msg_add8]; exact hs.msgs (i + 7) (by omega) (by omega)
        · rw [e]
          have h := schedule_eq M i
          simpa only [pair, ext8_pair] using h
    refine WP.mono hsched fun s₁ ⟨hq, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have hv₁ : Vars s₁ (Spec.Sha512.rounds H M (2 * n)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hx₁ _ (Ne.symm (msg_not n (by decide))) (by decide)]; exact hs.vars.v0
      · rw [hx₁ _ (Ne.symm (msg_not n (by decide))) (by decide)]; exact hs.vars.v1
      · rw [hx₁ _ (Ne.symm (msg_not n (by decide))) (by decide)]; exact hs.vars.v2
      · rw [hx₁ _ (Ne.symm (msg_not n (by decide))) (by decide)]; exact hs.vars.v3
    refine WP.mono (rounds2_ok n s₁ _ M hv₁ hq)
      fun s₂ ⟨hv₂, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨by rw [rounds_two]; exact hv₂, fun k hk hk' => ?_, fun r hr => ?_, fun r hr => ?_,
      by rw [hm₂, hm₁, hs.mem], by rw [hrd₂, hrd₁, hs.rd], by rw [hwr₂, hwr₁, hs.wr]⟩
    · rw [hx₂ _ (msg_not k (by decide)) (msg_not k (by decide)) (msg_not k (by decide))
        (msg_not k (by decide)) (msg_not k (by decide)) (msg_not k (by decide)) (msg_not k (by decide))]
      by_cases hkn : k = n
      · subst hkn; exact hq
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega)) (msg_not k (by decide))]
        exact hs.msgs k (by omega) (by omega)
    · have hne : r ≠ .v0 ∧ r ≠ .v1 ∧ r ≠ .v2 ∧ r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v6 := by
        have key : ∀ r ∈ [VReg.v24, .v25, .v26, .v27],
          r ≠ .v0 ∧ r ≠ .v1 ∧ r ≠ .v2 ∧ r ≠ .v3 ∧ r ≠ .v4 ∧ r ≠ .v5 ∧ r ≠ .v6 := by decide
        exact key r hr
      obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hne
      rw [hx₂ r h0 h1 h2 h3 h4 h5 h6, hx₁ _ (Ne.symm (msg_not n (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hr))))))))) h6]
      exact hs.keep r hr
    · rw [hg₂ r hr, hg₁, hs.gpr r hr]

theorem read_ab (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 0) 16 = ab (stateAt m p) := by
  rw [read16_dwords]
  simp only [ab, stateAt_get _ _ (by decide : 0 < 8), stateAt_get _ _ (by decide : 1 < 8),
    Nat.reduceMul, BitVec.add_zero]

theorem read_cd (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 16) 16 = cd (stateAt m p) := by
  rw [read16_dwords]
  simp only [cd, stateAt_get _ _ (by decide : 2 < 8), stateAt_get _ _ (by decide : 3 < 8),
    Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem read_ef (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 32) 16 = ef (stateAt m p) := by
  rw [read16_dwords]
  simp only [ef, stateAt_get _ _ (by decide : 4 < 8), stateAt_get _ _ (by decide : 5 < 8),
    Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem read_gh (m : Mem) (p : Addr) : m.read (p + BitVec.ofNat 64 48) 16 = gh (stateAt m p) := by
  rw [read16_dwords]
  simp only [gh, stateAt_get _ _ (by decide : 6 < 8), stateAt_get _ _ (by decide : 7 < 8),
    Offset.add_add, Nat.reduceMul, Nat.reduceAdd]

theorem write_pairs (m : Mem) (p : Addr) (v : HashValue) :
    (((m.write (p + BitVec.ofNat 64 0) 16 (ab v)).write (p + BitVec.ofNat 64 16) 16 (cd v)).write
      (p + BitVec.ofNat 64 32) 16 (ef v)).write (p + BitVec.ofNat 64 48) 16 (gh v) = writeState m p v := by
  simp only [ab, cd, ef, gh, write16_dwords, writeState, Offset.add_add, Nat.reduceMul, Nat.reduceAdd,
    BitVec.add_zero]

theorem load_ok (s : State)
    (hin : ∀ d, d ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 16) :
    WP isa (.block load) s fun s' =>
      Vars s' (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v24 = ab (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v25 = cd (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v26 = ef (stateAt s.mem (s.gpr .x0)) ∧
      s'.v .v27 = gh (stateAt s.mem (s.gpr .x0)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := hin 0 (by decide)
  have h16 := hin 16 (by decide)
  have h32 := hin 32 (by decide)
  have h48 := hin 48 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [load, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, VOp.eval, Option.bind_some, and_self, ite_true, ite_false, isa,
    Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    h0, h16, h32, h48, read_ab, read_cd, read_ef, read_gh, Option.some.injEq, exists_eq_left']
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, trivial⟩

theorem store_ok (s : State) (v H : HashValue)
    (hv : Vars s v) (hv24 : s.v .v24 = ab H) (hv25 : s.v .v25 = cd H)
    (hv26 : s.v .v26 = ef H) (hv27 : s.v .v27 = gh H)
    (hout : ∀ d, d ≤ 48 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 16) :
    WP isa (.block store) s fun s' =>
      s'.mem = writeState s.mem (s.gpr .x0) (Vector.zipWith (· + ·) v H) ∧
      s'.gpr .x1 = s.gpr .x1 + 128 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := hout 0 (by decide)
  have h16 := hout 16 (by decide)
  have h32 := hout 32 (by decide)
  have h48 := hout 48 (by decide)
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  apply WP.of_runBlock
  simp (config := {decide := true}) only [store, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, VOp.eval, Option.bind_some, and_self, ite_true, ite_false, isa, State.read, Size.bits,
    Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    h0, h16, h32, h48, hv0, hv1, hv2, hv3, hv24, hv25, hv26, hv27,
    add_ab, add_cd, add_ef, add_gh, write_pairs, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, fun r h1 h2 => by
    simp only [RegUpd.gpr_write_of_ne, h1, h2, not_false_eq_true], trivial⟩

theorem Pre.in_blk16 {s₀ : State} (hp : AArch64.Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * n)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem body_ok {s₀ : State} (hp : AArch64.Pre s₀) {i : Nat} (hi : i < nb s₀) {s : State}
    (hL : LInv s₀ i s) :
    WP isa body s fun s' =>
      (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
      (eval (.nonzero .x .x2) s' = some true ∧ i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s') := by
  have hin : ∀ d, d ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 16 := by
    intro d hd
    refine ⟨stR s₀, by simp [hL.wr, hp.wr], ?_⟩
    rw [hL.x0]; exact contains_offset (by omega) (by omega)
  refine WP.seq ((load_ok s hin).mono
    fun s₁ ⟨hv, hv24, hv25, hv26, hv27, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hblk : ∀ t : Nat, t < 16 →
      rev64 (s₁.mem.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
    intro t ht
    rw [hm₁, hL.frame.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  refine WP.seq ((rounds_ok _ (blk s₀ i) (blkAddr s₀ i) s₁ (by rw [hg₁, hL.x1])
    (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    hblk hv 40 (Nat.le_refl _)).mono fun s₂ hR => ?_)
  have hg₂ : ∀ r, r ≠ .x4 → s₂.gpr r = s.gpr r := fun r hr => by rw [hR.gpr r hr, hg₁]
  have hout : ∀ d, d ≤ 48 → InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 d) 16 := by
    intro d hd
    refine ⟨stR s₀, by simp [hR.wr, hwr₁, hL.wr, hp.wr], ?_⟩
    rw [hg₂ .x0 (by decide), hL.x0]; exact contains_offset (by omega) (by omega)
  refine (store_ok s₂ _ (stateAt s.mem (s.gpr .x0)) hR.vars
    (by rw [hR.keep .v24 (by decide), hv24]) (by rw [hR.keep .v25 (by decide), hv25])
    (by rw [hR.keep .v26 (by decide), hv26]) (by rw [hR.keep .v27 (by decide), hv27])
    hout).mono fun s₃ ⟨hm₃, hx1₃, hx2₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg₂ .x2 (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [hm₃, hR.mem, hm₁, hg₂ .x0 (by decide), hL.x0]
    exact (frame_writeState (Frame.refl _ _) _).sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hg₃ .x0 (by decide) (by decide), hg₂ .x0 (by decide), hL.x0],
      by rw [hg₃ .x3 (by decide) (by decide), hg₂ .x3 (by decide), hL.x3],
      ?_, by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    · intro r hr
      have key : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 := by decide
      have hn := key r hr
      rw [hg₃ r hn.1 hn.2.1, hg₂ r hn.2.2, hL.kept r hr]
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
      exact (Offset.add_add _ _ 128).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [hx2₃, hx2]

theorem correct {s₀ : State} (hp : AArch64.Pre s₀) :
    WP isa compress s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Sha512.compressAArch64.post s₀ s' := by
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
    Verified AArch64.target Impl.Sha512.AArch64.Sha3.compress Proof.Sha512.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact AArch64.compress_verified.2.2

end VG.Proof.Sha512.AArch64.Sha3
