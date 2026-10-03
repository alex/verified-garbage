import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
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


theorem msg_not (n : Nat) {r : VReg}
    (hr : r ∈ [.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v24, .v25, .v26, .v27, .v28, .v31]) :
    msg n ≠ r := by
  have key : ∀ c < 8,
    ∀ r ∈ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v24, .v25, .v26, .v27, .v28, .v31],
    msg c ≠ r := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) r hr

/-- The state pairs `v` are in the registers of pair of rounds `n`. -/
structure Vars (n : Nat) (s : State) (v : HashValue) : Prop where
  v0 : s.v (reg n 0) = ab v
  v1 : s.v (reg n 1) = cd v
  v2 : s.v (reg n 2) = ef v
  v3 : s.v (reg n 3) = gh v

theorem reg_succ (n : Nat) :
    reg (n + 1) 0 = reg n 4 ∧ reg (n + 1) 1 = reg n 0 ∧ reg (n + 1) 2 = reg n 5 ∧
      reg (n + 1) 3 = reg n 2 := by
  simp only [reg]
  rw [show (n + 1) % 3 = (n % 3 + 1) % 3 by omega]
  have := Nat.mod_lt n (show 3 > 0 by omega)
  generalize n % 3 = c at *
  revert this; revert c; decide

/-- The registers of a pair of rounds, its temporaries and the registers kept
across it are all different. -/
theorem reg_nodup (n : Nat) :
    [reg n 0, reg n 1, reg n 2, reg n 3, reg n 4, reg n 5, .v6, .v7, .v28, .v31,
      .v24, .v25, .v26, .v27].Nodup := by
  simp only [reg]
  have := Nat.mod_lt n (show 3 > 0 by omega)
  generalize n % 3 = c at *
  revert this; revert c; decide

theorem msg_ne_reg (n i k : Nat) (hk : k < 6) : msg n ≠ reg i k := by
  have key : ∀ c < 8, ∀ d < 3, ∀ k < 6, msg c ≠ reg d k := by decide
  rw [show msg n = msg (n % 8) by simp only [msg, Nat.mod_mod],
    show reg i k = reg (i % 3) k by simp only [reg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) _ (Nat.mod_lt _ (by decide)) _ hk

/-- The state registers are none of the temporaries or kept registers. -/
theorem reg_ne (n k : Nat) (hk : k < 6) {r : VReg}
    (hr : r ∈ [VReg.v6, .v7, .v28, .v31, .v24, .v25, .v26, .v27]) : reg n k ≠ r := by
  have key : ∀ d < 3, ∀ k < 6, ∀ r ∈ [VReg.v6, .v7, .v28, .v31, .v24, .v25, .v26, .v27],
    reg d k ≠ r := by decide
  rw [show reg n k = reg (n % 3) k by simp only [reg, Nat.mod_mod]]
  exact key _ (Nat.mod_lt _ (by decide)) _ hk r hr

/-- A pair of rounds, symbolically executed once for any registers (which
`reg_nodup` and `msg_ne_reg` say are different). -/
theorem rounds2With_ok (n : Nat) (a b c d t f : VReg) (s : State) (v : HashValue) (M : Block)
    (hs : [a, b, c, d, t, f, .v6, .v7, .v28, .v31].Nodup)
    (hx : msg n ∉ [a, b, c, d, t, f, .v6, .v7, .v28, .v31])
    (ha : s.v a = ab v) (hb : s.v b = cd v) (hc : s.v c = ef v) (hd : s.v d = gh v)
    (hq : s.v (msg n) = pair M n) (hz : s.v .v31 = ofVDwords 0 0) (hn : n < 40)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16)
    (hk : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16 = kPair n) :
    WP isa (.block (rounds2With n a b c d t f)) s fun s' =>
      s'.v t = ab (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      s'.v a = cd (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      s'.v f = ef (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      s'.v c = gh (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      (∀ r, r ≠ t → r ≠ f → r ≠ .v6 → r ≠ .v7 → r ≠ .v28 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hl := exec_ldrq (s := s) (t := t) (n := .x3) (off := 16 * n) ⟨by omega, by omega⟩ hin
  have ha' : a ≠ t := fun h => by subst h; simp at hs
  have hb' : b ≠ t := fun h => by subst h; simp at hs
  have hc' : c ≠ t := fun h => by subst h; simp at hs
  have hd' : d ≠ t := fun h => by subst h; simp at hs
  have hz' : (VReg.v31) ≠ t := fun h => by subst h; simp at hs
  have hs' := VG.nodup_reverse hs
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, or_false, not_or, List.nodup_nil, and_true] at hs hs' hx
  simp only [rounds2With]
  have hq' := hq
  have h0 := ha
  have h1 := hb
  have h2 := hc
  have h3 := hd
  have h31 := hz
  apply WP.of_runBlock
  generalize msg n = x at *
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec_vop, VOp.eval,
    isa, hl, RegUpd.v_setV, ite_true, ite_false, RegUpd.gpr_setV, RegUpd.mem_setV,
    RegUpd.rd_setV, RegUpd.wr_setV, Option.map_some, h0, h1, h2, h3, h31, hq', hk, hs, hs', hx,
    Option.some.injEq, exists_eq_left']
  refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
  rotate_right
  · intro r h0 h1 h6 h7 h28
    simp only [h0, h1, h6, h7, h28, ite_false]
  · have hab := h2_eq v (K (2 * n)) (W M (2 * n)) (K (2 * n + 1)) (W M (2 * n + 1))
    simp only [kPair, pair, ab, cd, ef, gh, VArr.map2, vdword_ofVDwords_0, vdword_ofVDwords_1, ext8_pair, h_eq]
    exact hab
  · exact (cd_eq _ _ _ _ _).symm
  · have hef := hF_eq v (K (2 * n)) (W M (2 * n)) (K (2 * n + 1)) (W M (2 * n + 1))
    simp only [kPair, pair, cd, ef, gh, VArr.map2, vdword_ofVDwords_0, vdword_ofVDwords_1, ext8_pair]
    exact hef
  · exact (gh_eq _ _ _ _ _).symm

theorem rounds2_ok (n : Nat) (s : State) (v : HashValue) (M : Block)
    (hv : Vars n s v) (hq : s.v (msg n) = pair M n) (hz : s.v .v31 = ofVDwords 0 0) (hn : n < 40)
    (hin : InRegions (s.rd ++ s.wr) (s.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16)
    (hk : s.mem.read (s.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16 = kPair n) :
    WP isa (.block (rounds2 n)) s fun s' =>
      Vars (n + 1) s' (roundKW (roundKW v (K (2 * n)) (W M (2 * n))) (K (2 * n + 1)) (W M (2 * n + 1))) ∧
      (∀ r, r ≠ reg n 4 → r ≠ reg n 5 → r ≠ .v6 → r ≠ .v7 → r ≠ .v28 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hs := reg_nodup n
  have hs₁ : [reg n 0, reg n 1, reg n 2, reg n 3, reg n 4, reg n 5, .v6, .v7, .v28, .v31].Nodup :=
    hs.sublist (by simp)
  have hx : msg n ∉ [reg n 0, reg n 1, reg n 2, reg n 3, reg n 4, reg n 5, .v6, .v7, .v28, .v31] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨msg_ne_reg n n 0 (by decide), msg_ne_reg n n 1 (by decide), msg_ne_reg n n 2 (by decide),
      msg_ne_reg n n 3 (by decide), msg_ne_reg n n 4 (by decide), msg_ne_reg n n 5 (by decide),
      msg_not n (by decide), msg_not n (by decide), msg_not n (by decide), msg_not n (by decide)⟩
  obtain ⟨e0, e1, e2, e3⟩ := reg_succ n
  refine (rounds2With_ok n _ _ _ _ _ _ s v M hs₁ hx hv.v0 hv.v1 hv.v2 hv.v3 hq hz hn hin hk).mono
    fun s' ⟨ht, ha, hf, hc, hr, hg, hm, hrd, hwr⟩ => ⟨⟨?_, ?_, ?_, ?_⟩, hr, hg, hm, hrd, hwr⟩
  · rw [e0]; exact ht
  · rw [e1]; exact ha
  · rw [e2]; exact hf
  · rw [e3]; exact hc

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

/-! ## The table of round constants -/

/-- `Kₜ` is at `scr + 8t` for every `t < k`. -/
def Tab (m : Mem) (scr : Addr) (k : Nat) : Prop :=
  ∀ t < k, m.readW (scr + BitVec.ofNat 64 (8 * t)) 64 = K t

/-- How much of the table is built after `n` pairs of rounds of the first
block (two pairs of rounds ahead), or of a later one. -/
def tabLen (first : Bool) (n : Nat) : Nat := if first then min 80 (2 * n + 4) else 80

theorem Tab.mono {m : Mem} {scr : Addr} {k k' : Nat} (h : Tab m scr k) (hk : k' ≤ k) :
    Tab m scr k' := fun t ht => h t (by omega)

/-- A pair of constants, as `ldr q` loads it. -/
theorem Tab.pair {m : Mem} {scr : Addr} {k n : Nat} (h : Tab m scr k) (hn : 2 * n + 1 < k) :
    m.read (scr + BitVec.ofNat 64 (16 * n)) 16 = kPair n := by
  rw [read16_dwords, Offset.add_add, show 16 * n = 8 * (2 * n) by omega, h _ (by omega),
    show 8 * (2 * n) + 8 = 8 * (2 * n + 1) by omega, h _ (by omega)]
  rfl

/-- Building pair `j` extends a table of `2j` constants. -/
theorem Tab.build {m : Mem} {scr : Addr} {j : Nat} (h : Tab m scr (2 * j)) (hj : j < 40) :
    Tab ((m.writeW (scr + BitVec.ofNat 64 (16 * j)) (K (2 * j))).writeW
      (scr + BitVec.ofNat 64 (16 * j + 8)) (K (2 * j + 1))) scr (2 * j + 2) := by
  intro t ht
  by_cases h1 : t = 2 * j + 1
  · subst h1
    rw [show 8 * (2 * j + 1) = 16 * j + 8 by omega, Mem.readW_writeW_self64]
  · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
    by_cases h0 : t = 2 * j
    · subst h0
      rw [show 8 * (2 * j) = 16 * j by omega, Mem.readW_writeW_self64]
    · rw [Mem.readW_writeW_sep (Offset.sep _ (by omega) (by omega) (by omega)) (by decide)]
      exact h t (by omega)

/-- Writing outside the table keeps it. -/
theorem Tab.of_frame {m m' : Mem} {scr : Addr} {k : Nat} (h : Tab m scr k) (hk : k ≤ 80)
    {rs : List Region} (hf : Frame rs m m') (hd : ∀ r ∈ rs, (⟨scr, 640⟩ : Region).Disjoint r) :
    Tab m' scr k :=
  fun t ht => by
    rw [← h t ht]
    exact hf.readW (r := ⟨scr, 640⟩) (Offset.contains_base _ (by omega) (by omega)) hd (by decide)

theorem writeW64 (m : Mem) (a : Addr) (v : BitVec 64) : m.writeW a v = m.write a 8 v := by
  simp only [Mem.writeW]
  rfl

theorem build_ok (j : Nat) (hj : j < 40) (s : State)
    (h1 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) 8)
    (h2 : InRegions s.wr (s.gpr .x3 + BitVec.ofNat 64 (16 * j + 8)) 8) :
    WP isa (.block (build j)) s fun s' =>
      s'.mem = (s.mem.writeW (s.gpr .x3 + BitVec.ofNat 64 (16 * j)) (K (2 * j))).writeW
        (s.gpr .x3 + BitVec.ofNat 64 (16 * j + 8)) (K (2 * j + 1)) ∧
      s'.v = s.v ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.sp = s.sp ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [build, runBlock_cons, runStep_some, runBlock_nil, exec,
    addr, State.store, Option.bind_some, and_self, ite_true, isa, State.read, Size.bits,
    Size.bytes, RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write,
    RegUpd.wr_write, RegUpd.v_write, RegUpd.sp_write, BitVec.setWidth_eq, movz_movk64',
    show (16 * j) % 8 = 0 by omega, show 16 * j < 4096 * 8 by omega,
    show (16 * j + 8) % 8 = 0 by omega, show 16 * j + 8 < 4096 * 8 by omega,
    h1, h2, Option.some.injEq, exists_eq_left']
  refine ⟨by rw [writeW64, writeW64], trivial, fun r h4 h5 => ?_, trivial⟩
  simp only [RegUpd.gpr_write_of_ne, h4, h5, not_false_eq_true]

/-- The scratch space the table occupies. -/
abbrev tabR (scr : Addr) : Region := ⟨scr, 640⟩

/-- Rounds invariant, relative to the state `sB` at the start of the rounds. -/
structure RInv (first : Bool) (H : HashValue) (M : Block) (scr : Addr) (sB : State) (n : Nat)
    (s : State) : Prop where
  vars : Vars n s (Spec.Sha512.rounds H M (2 * n))
  msgs : ∀ k < n, n ≤ k + 8 → s.v (msg k) = pair M k
  keep : ∀ r ∈ [VReg.v24, .v25, .v26, .v27, .v31], s.v r = sB.v r
  gpr : ∀ r, r ≠ .x4 → r ≠ .x5 → s.gpr r = sB.gpr r
  rd : s.rd = sB.rd
  wr : s.wr = sB.wr
  frame : Frame [tabR scr] sB.mem s.mem
  tab : Tab s.mem scr (tabLen first n)

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

/-- What building the table does: the two words of pair `j` within `tabR`. -/
theorem build_frame {s : State} {scr : Addr} {j : Nat} (hj : j < 40) :
    Frame [tabR scr] s.mem ((s.mem.writeW (scr + BitVec.ofNat 64 (16 * j)) (K (2 * j))).writeW
      (scr + BitVec.ofNat 64 (16 * j + 8)) (K (2 * j + 1))) :=
  ((Frame.refl _ _).writeW (List.mem_singleton_self _) _
      (Offset.contains_base _ (by omega) (by omega))).writeW (List.mem_singleton_self _) _
    (Offset.contains_base _ (by omega) (by omega))

/-- One pair `j` of the table, with its preconditions from the scratch space. -/
theorem build_step {s : State} {scr : Addr} {j : Nat} (hj : j < 40) (hx3 : s.gpr .x3 = scr)
    (hw : ∀ d, d + 8 ≤ 640 → InRegions s.wr (scr + BitVec.ofNat 64 d) 8) (ht : Tab s.mem scr (2 * j)) :
    WP isa (.block (build j)) s fun s' =>
      s'.v = s.v ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [tabR scr] s.mem s'.mem ∧ Tab s'.mem scr (2 * j + 2) := by
  refine (build_ok j hj s (by rw [hx3]; exact hw _ (by omega)) (by rw [hx3]; exact hw _ (by omega))).mono
    fun s' ⟨hm, hv, hg, _, hrd, hwr⟩ => ⟨hv, hg, hrd, hwr, ?_, ?_⟩
  · rw [hm, hx3]; exact build_frame hj
  · rw [hm, hx3]; exact ht.build hj

theorem tabLen_succ (first : Bool) (n : Nat) (hn : n < 40) :
    (first && decide (n + 2 < 40)) = false → tabLen first (n + 1) ≤ tabLen first n := by
  cases first <;> simp [tabLen] <;> omega

/-- The table-building part of pair of rounds `n` (two pairs ahead, in the first block). -/
theorem buildPart_ok (first : Bool) {n : Nat} (hn : n < 40) {s : State} {scr : Addr}
    (hx3 : s.gpr .x3 = scr) (hw : ∀ d, d + 8 ≤ 640 → InRegions s.wr (scr + BitVec.ofNat 64 d) 8)
    (ht : Tab s.mem scr (tabLen first n)) :
    WP isa (.block (if first && n + 2 < 40 then build (n + 2) else [])) s fun s' =>
      s'.v = s.v ∧ (∀ r, r ≠ .x4 → r ≠ .x5 → s'.gpr r = s.gpr r) ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧
      Frame [tabR scr] s.mem s'.mem ∧ Tab s'.mem scr (tabLen first (n + 1)) := by
  by_cases hb : (first && decide (n + 2 < 40)) = true
  · simp only [hb, ite_true]
    have hf : first = true := by simpa using (Bool.and_eq_true _ _).mp hb |>.1
    have hn2 : n + 2 < 40 := by simpa using (Bool.and_eq_true _ _).mp hb |>.2
    subst hf
    refine (build_step hn2 hx3 hw (ht.mono (by simp [tabLen]; omega))).mono
      fun s' ⟨hv, hg, hrd, hwr, hf, ht'⟩ => ⟨hv, hg, hrd, hwr, hf, ht'.mono (by simp [tabLen]; omega)⟩
  · simp only [Bool.not_eq_true] at hb
    simp only [hb]
    exact WP.block_nil (M := isa) ⟨rfl, fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _,
      ht.mono (tabLen_succ first n hn hb)⟩

theorem rounds_ok (first : Bool) (H : HashValue) (M : Block) (bp scr : Addr) (sB : State)
    (hrsi : sB.gpr .x1 = bp) (hx3 : sB.gpr .x3 = scr)
    (hin : ∀ n : Nat, n < 8 → InRegions (sB.rd ++ sB.wr) (bp + BitVec.ofNat 64 (16 * n)) 16)
    (hblk : ∀ m, Frame [tabR scr] sB.mem m → ∀ t : Nat, t < 16 →
      rev64 (m.readW (bp + BitVec.ofNat 64 (8 * t)) 64) = W M t)
    (hw : ∀ d, d + 8 ≤ 640 → InRegions sB.wr (scr + BitVec.ofNat 64 d) 8)
    (hq : ∀ d, d + 16 ≤ 640 → InRegions (sB.rd ++ sB.wr) (scr + BitVec.ofNat 64 d) 16)
    (hv : Vars 0 sB H) (hz : sB.v .v31 = ofVDwords 0 0) (htab : first = false → Tab sB.mem scr 80) :
    ∀ n ≤ 40, WP isa (roundsWith first n) sB (RInv first H M scr sB n) := by
  intro n hn
  induction n with
  | zero =>
    cases first with
    | false =>
      exact WP.block_nil (M := isa) ⟨hv, fun _ h => absurd h (by omega), fun _ _ => rfl,
        fun _ _ _ => rfl, rfl, rfl, Frame.refl _ _, htab rfl⟩
    | true =>
      show WP isa (.block (build 0 ++ build 1)) sB _
      rw [WP.block_append_iff]
      refine (build_step (j := 0) (by decide) hx3 hw (fun t ht => absurd ht (by omega))).mono
        fun s₁ ⟨hv₁, hg₁, hrd₁, hwr₁, hf₁, ht₁⟩ => ?_
      refine (build_step (j := 1) (by decide) (by rw [hg₁ _ (by decide) (by decide), hx3])
        (by rw [hwr₁]; exact hw) ht₁).mono fun s₂ ⟨hv₂, hg₂, hrd₂, hwr₂, hf₂, ht₂⟩ => ?_
      refine ⟨?_, fun _ h => absurd h (by omega), fun r _ => by rw [hv₂, hv₁],
        fun r h4 h5 => by rw [hg₂ r h4 h5, hg₁ r h4 h5], by rw [hrd₂, hrd₁], by rw [hwr₂, hwr₁],
        hf₁.trans hf₂, ht₂⟩
      exact ⟨by rw [hv₂, hv₁]; exact hv.v0, by rw [hv₂, hv₁]; exact hv.v1,
        by rw [hv₂, hv₁]; exact hv.v2, by rw [hv₂, hv₁]; exact hv.v3⟩
  | succ n ih =>
    refine WP.seq (WP.mono (ih (by omega)) fun s hs => ?_)
    rw [List.append_assoc, WP.block_append_iff]
    have hs3 : s.gpr .x3 = scr := (hs.gpr .x3 (by decide) (by decide)).trans hx3
    refine (buildPart_ok first (n := n) (by omega) hs3 (by rw [hs.wr]; exact hw) hs.tab).mono
      fun s' ⟨hv', hg', hrd', hwr', hf', ht'⟩ => ?_
    rw [WP.block_append_iff]
    have hfr : Frame [tabR scr] sB.mem s'.mem := hs.frame.trans hf'
    have hs_rsi : s'.gpr .x1 = bp := by
      rw [hg' _ (by decide) (by decide), hs.gpr .x1 (by decide) (by decide), hrsi]
    have hsched : WP isa (.block (schedule n)) s' fun s₁ =>
        s₁.v (msg n) = pair M n ∧ (∀ r, r ≠ msg n → r ≠ .v6 → s₁.v r = s'.v r) ∧
        s₁.gpr = s'.gpr ∧ s₁.mem = s'.mem ∧ s₁.rd = s'.rd ∧ s₁.wr = s'.wr := by
      by_cases hlo : n < 8
      · refine WP.mono (schedule_lo n hlo s' (by rw [hrd', hwr', hs.rd, hs.wr, hs_rsi]; exact hin n hlo))
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, fun r hr _ => hx r hr, hg, hm, hrd, hwr⟩
        rw [e, hs_rsi]
        exact load_pair M s'.mem bp hlo (hblk _ hfr)
      · obtain ⟨i, rfl⟩ : ∃ i, n = i + 8 := ⟨n - 8, by omega⟩
        refine WP.mono (schedule_hi (i + 8) (by omega) s' (pair M i) (pair M (i + 1)) (pair M (i + 4))
          (pair M (i + 5)) (pair M (i + 7)) ?_ ?_ ?_ ?_ ?_)
          fun s₁ ⟨e, hx, hg, hm, hrd, hwr⟩ => ⟨?_, hx, hg, hm, hrd, hwr⟩
        · rw [hv', msg_add8]; exact hs.msgs i (by omega) (by omega)
        · rw [hv', show i + 8 + 1 = i + 1 + 8 by omega, msg_add8]
          exact hs.msgs (i + 1) (by omega) (by omega)
        · rw [hv', show i + 8 + 4 = i + 4 + 8 by omega, msg_add8]
          exact hs.msgs (i + 4) (by omega) (by omega)
        · rw [hv', show i + 8 + 5 = i + 5 + 8 by omega, msg_add8]
          exact hs.msgs (i + 5) (by omega) (by omega)
        · rw [hv', show i + 8 + 7 = i + 7 + 8 by omega, msg_add8]
          exact hs.msgs (i + 7) (by omega) (by omega)
        · rw [e]
          have h := schedule_eq M i
          simpa only [pair, ext8_pair] using h
    refine WP.mono hsched fun s₁ ⟨hq₁, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_
    have hv₁ : Vars n s₁ (Spec.Sha512.rounds H M (2 * n)) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hx₁ _ (Ne.symm (msg_ne_reg n n 0 (by decide))) (reg_ne n 0 (by decide) (by decide)), hv']
        exact hs.vars.v0
      · rw [hx₁ _ (Ne.symm (msg_ne_reg n n 1 (by decide))) (reg_ne n 1 (by decide) (by decide)), hv']
        exact hs.vars.v1
      · rw [hx₁ _ (Ne.symm (msg_ne_reg n n 2 (by decide))) (reg_ne n 2 (by decide) (by decide)), hv']
        exact hs.vars.v2
      · rw [hx₁ _ (Ne.symm (msg_ne_reg n n 3 (by decide))) (reg_ne n 3 (by decide) (by decide)), hv']
        exact hs.vars.v3
    have hz₁ : s₁.v .v31 = ofVDwords 0 0 := by
      rw [hx₁ _ (Ne.symm (msg_not n (by decide))) (by decide), hv', hs.keep .v31 (by decide), hz]
    have h3₁ : s₁.gpr .x3 = scr := by rw [hg₁, hg' _ (by decide) (by decide), hs3]
    have hin₁ : InRegions (s₁.rd ++ s₁.wr) (s₁.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16 := by
      rw [hrd₁, hwr₁, hrd', hwr', hs.rd, hs.wr, h3₁]; exact hq _ (by omega)
    have hk₁ : s₁.mem.read (s₁.gpr .x3 + BitVec.ofNat 64 (16 * n)) 16 = kPair n := by
      rw [hm₁, h3₁]
      exact ht'.pair (by cases first <;> simp [tabLen] <;> omega)
    refine WP.mono (rounds2_ok n s₁ _ M hv₁ hq₁ hz₁ (by omega) hin₁ hk₁)
      fun s₂ ⟨hv₂, hx₂, hg₂, hm₂, hrd₂, hwr₂⟩ => ?_
    refine ⟨by rw [rounds_two]; exact hv₂, fun k hk hk' => ?_, fun r hr => ?_,
      fun r h4 h5 => by rw [hg₂, hg₁, hg' r h4 h5, hs.gpr r h4 h5],
      by rw [hrd₂, hrd₁, hrd', hs.rd], by rw [hwr₂, hwr₁, hwr', hs.wr],
      by rw [hm₂, hm₁]; exact hfr, by rw [hm₂, hm₁]; exact ht'⟩
    · rw [hx₂ _ (msg_ne_reg k n 4 (by decide)) (msg_ne_reg k n 5 (by decide))
        (msg_not k (by decide)) (msg_not k (by decide)) (msg_not k (by decide))]
      by_cases hkn : k = n
      · subst hkn; exact hq₁
      · rw [hx₁ _ (msg_ne n k (by omega) (by omega)) (msg_not k (by decide)), hv']
        exact hs.msgs k (by omega) (by omega)
    · have hm : r ∈ [VReg.v0, .v1, .v2, .v3, .v4, .v5, .v6, .v7, .v24, .v25, .v26, .v27, .v28, .v31] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
      have hr' : r ∈ [VReg.v6, .v7, .v28, .v31, .v24, .v25, .v26, .v27] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
      have h678 : r ≠ .v6 ∧ r ≠ .v7 ∧ r ≠ .v28 := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hx₂ r (Ne.symm (reg_ne n 4 (by decide) hr')) (Ne.symm (reg_ne n 5 (by decide) hr'))
        h678.1 h678.2.1 h678.2.2, hx₁ _ (Ne.symm (msg_not n hm)) h678.1, hv']
      exact hs.keep r hr

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

/-- The hash value `v` is held in v24–v27, and v31 is zero. -/
structure Held (s : State) (v : HashValue) : Prop where
  v24 : s.v .v24 = ab v
  v25 : s.v .v25 = cd v
  v26 : s.v .v26 = ef v
  v27 : s.v .v27 = gh v
  v31 : s.v .v31 = ofVDwords 0 0

theorem zero_pair : (0 : BitVec 128) = ofVDwords 0 0 := rfl

theorem init_ok (s : State)
    (hin : ∀ d, d ≤ 48 → InRegions (s.rd ++ s.wr) (s.gpr .x0 + BitVec.ofNat 64 d) 16) :
    WP isa (.block init) s fun s' =>
      Held s' (stateAt s.mem (s.gpr .x0)) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := hin 0 (by decide)
  have h16 := hin 16 (by decide)
  have h32 := hin 32 (by decide)
  have h48 := hin 48 (by decide)
  apply WP.of_runBlock
  simp (config := {decide := true}) only [init, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.load, VOp.eval, Option.bind_some, and_self, ite_true, isa,
    Option.map_some, RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    h0, h16, h32, h48, read_ab, read_cd, read_ef, read_gh, Option.some.injEq, exists_eq_left']
  exact ⟨⟨rfl, rfl, rfl, rfl, zero_pair⟩, trivial⟩

theorem load_ok (s : State) (v : HashValue) (hH : Held s v) :
    WP isa (.block load) s fun s' =>
      Vars 0 s' v ∧ (∀ r, r ≠ .v0 → r ≠ .v1 → r ≠ .v2 → r ≠ .v3 → s'.v r = s.v r) ∧
      s'.gpr = s.gpr ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr := by
  apply WP.of_runBlock
  simp (config := {decide := true}) only [load, runBlock_cons, runStep_some, runBlock_nil,
    exec_vop, VOp.eval, isa, Option.map_some, RegUpd.v_setV, ite_false,
    RegUpd.gpr_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    hH.v24, hH.v25, hH.v26, hH.v27, Option.some.injEq, exists_eq_left']
  exact ⟨⟨rfl, rfl, rfl, rfl⟩, fun r h0 h1 h2 h3 => by simp only [h0, h1, h2, h3, ite_false],
    trivial⟩

theorem reg_40 : reg 40 0 = .v4 ∧ reg 40 1 = .v0 ∧ reg 40 2 = .v5 ∧ reg 40 3 = .v2 := by decide

theorem store_ok (s : State) (v H : HashValue) (hv : Vars 40 s v) (hH : Held s H)
    (hout : ∀ d, d ≤ 48 → InRegions s.wr (s.gpr .x0 + BitVec.ofNat 64 d) 16) :
    WP isa (.block store) s fun s' =>
      s'.mem = writeState s.mem (s.gpr .x0) (Vector.zipWith (· + ·) v H) ∧
      s'.v .v24 = ab (Vector.zipWith (· + ·) v H) ∧ s'.v .v25 = cd (Vector.zipWith (· + ·) v H) ∧
      s'.v .v26 = ef (Vector.zipWith (· + ·) v H) ∧ s'.v .v27 = gh (Vector.zipWith (· + ·) v H) ∧
      s'.v .v31 = s.v .v31 ∧
      s'.gpr .x1 = s.gpr .x1 + 128 ∧ s'.gpr .x2 = s.gpr .x2 - 1 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → s'.gpr r = s.gpr r) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have h0 := hout 0 (by decide)
  have h16 := hout 16 (by decide)
  have h32 := hout 32 (by decide)
  have h48 := hout 48 (by decide)
  obtain ⟨hv0, hv1, hv2, hv3⟩ := hv
  obtain ⟨e0, e1, e2, e3⟩ := reg_40
  rw [e0] at hv0; rw [e1] at hv1; rw [e2] at hv2; rw [e3] at hv3
  apply WP.of_runBlock
  simp (config := {decide := true}) only [store, e0, e1, e2, e3, runBlock_cons, runStep_some, runBlock_nil,
    exec, addr, State.store, VOp.eval, Option.bind_some, and_self, ite_true, ite_false, isa, State.read, Size.bits,
    Option.map_some, RegUpd.gpr_setV, RegUpd.v_setV, RegUpd.mem_setV, RegUpd.rd_setV, RegUpd.wr_setV,
    RegUpd.gpr_write_self, RegUpd.gpr_write_of_ne, RegUpd.mem_write, RegUpd.rd_write, RegUpd.wr_write,
    RegUpd.v_write, h0, h16, h32, h48, hv0, hv1, hv2, hv3, hH.v24, hH.v25, hH.v26, hH.v27,
    add_ab, add_cd, add_ef, add_gh, write_pairs, BitVec.setWidth_eq, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, trivial, trivial, trivial, trivial, trivial, rfl, rfl, fun r h1 h2 => by
    simp only [RegUpd.gpr_write_of_ne, h1, h2, not_false_eq_true], trivial⟩

theorem Pre.in_blk16 {s₀ : State} (hp : AArch64.Pre s₀) {i n : Nat}
    (hi : i < nb s₀) (hn : n < 8) :
    InRegions (s₀.rd ++ s₀.wr) (blkAddr s₀ i + BitVec.ofNat 64 (16 * n)) 16 := by
  have := hp.nb_lt
  refine ⟨blR s₀, by simp [hp.rd], ?_⟩
  rw [show blkAddr s₀ i + BitVec.ofNat 64 (16 * n) =
    bp s₀ + BitVec.ofNat 64 (128 * i + 16 * n) from Offset.add_add _ _ _]
  exact contains_offset (by omega) (by omega)

theorem tab_in (s₀ : State) : ∀ r ∈ [tabR (scr s₀)], ∃ R ∈ [stR s₀, scrR s₀], Region.Sub r R :=
  fun r hr => ⟨scrR s₀, by simp, by simp at hr; subst hr; exact Region.sub_prefix (Nat.le_refl _)⟩

/-- One block, building the table (`first`) or with it built. -/
theorem block_ok (first : Bool) {s₀ : State} (hp : AArch64.Pre s₀) {i : Nat} (hi : i < nb s₀)
    {s : State} (hL : LInv s₀ i s) (hH : Held s (stateAt s.mem (st s₀)))
    (htab : first = false → Tab s.mem (scr s₀) 80) :
    WP isa (blockWith first) s fun s' =>
      (i + 1 = nb s₀ ∧ Common s₀ (nb s₀) s' ∧ s'.gpr .x2 = 0) ∨
      (i + 1 < nb s₀ ∧ LInv s₀ (i + 1) s' ∧ Held s' (stateAt s'.mem (st s₀)) ∧
        Tab s'.mem (scr s₀) 80) := by
  refine WP.seq ((load_ok s _ hH).mono fun s₁ ⟨hv, hx₁, hg₁, hm₁, hrd₁, hwr₁⟩ => ?_)
  have hscr : ∀ d, d + 8 ≤ 640 → InRegions s₁.wr (scr s₀ + BitVec.ofNat 64 d) 8 :=
    fun d hd => ⟨scrR s₀, by simp [hwr₁, hL.wr, hp.wr], contains_offset (by omega) (by omega)⟩
  have hscr16 : ∀ d, d + 16 ≤ 640 → InRegions (s₁.rd ++ s₁.wr) (scr s₀ + BitVec.ofNat 64 d) 16 :=
    fun d hd => ⟨scrR s₀, by simp [hwr₁, hL.wr, hp.wr], contains_offset (by omega) (by omega)⟩
  have hblk : ∀ m, Frame [tabR (scr s₀)] s₁.mem m → ∀ t : Nat, t < 16 →
      rev64 (m.readW (blkAddr s₀ i + BitVec.ofNat 64 (8 * t)) 64) = W (blk s₀ i) t := by
    intro m hf t ht
    have hf' : Frame [stR s₀, scrR s₀] s₀.mem m := by
      rw [hm₁] at hf
      exact hL.frame.trans (hf.sub (tab_in s₀))
    rw [hf'.readW (hp.blk_contains hi ht) (by simpa using ⟨hp.blk_st, hp.blk_scr⟩) (by decide)]
    exact blk_word i t ht
  have hz₁ : s₁.v .v31 = ofVDwords 0 0 := by
    rw [hx₁ _ (by decide) (by decide) (by decide) (by decide)]; exact hH.v31
  have htab₁ : first = false → Tab s₁.mem (scr s₀) 80 := fun h => by rw [hm₁]; exact htab h
  refine WP.seq ((rounds_ok first _ (blk s₀ i) (blkAddr s₀ i) (scr s₀) s₁ (by rw [hg₁, hL.x1])
    (by rw [hg₁, hL.x3]) (fun n hn => by rw [hrd₁, hwr₁, hL.rd, hL.wr]; exact Pre.in_blk16 hp hi hn)
    hblk hscr hscr16 hv hz₁ htab₁ 40 (Nat.le_refl _)).mono fun s₂ hR => ?_)
  have hg₂ : ∀ r, r ≠ .x4 → r ≠ .x5 → s₂.gpr r = s.gpr r := fun r h4 h5 => by
    rw [hR.gpr r h4 h5, hg₁]
  have hout : ∀ d, d ≤ 48 → InRegions s₂.wr (s₂.gpr .x0 + BitVec.ofNat 64 d) 16 := by
    intro d hd
    refine ⟨stR s₀, by simp [hR.wr, hwr₁, hL.wr, hp.wr], ?_⟩
    rw [hg₂ .x0 (by decide) (by decide), hL.x0]; exact contains_offset (by omega) (by omega)
  have hH₂ : Held s₂ (stateAt s.mem (st s₀)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
      rw [hR.keep _ (by decide), hx₁ _ (by decide) (by decide) (by decide) (by decide)]
    exacts [hH.v24, hH.v25, hH.v26, hH.v27, hH.v31]
  refine (store_ok s₂ _ _ hR.vars hH₂ hout).mono
    fun s₃ ⟨hm₃, h24₃, h25₃, h26₃, h27₃, h31₃, hx1₃, hx2₃, hg₃, hrd₃, hwr₃⟩ => ?_
  have hx2 : s₂.gpr .x2 - 1 = BitVec.ofNat 64 (nb s₀ - (i + 1)) := by
    rw [hg₂ .x2 (by decide) (by decide), hL.x2]
    rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, Offset.ofNat_sub_ofNat (by omega), Nat.sub_sub]
  have hst₃ : Frame [stR s₀] s₂.mem s₃.mem := by
    rw [hm₃, hg₂ .x0 (by decide) (by decide), hL.x0]
    exact frame_writeState (Frame.refl _ _) _
  have hframe : Frame [stR s₀, scrR s₀] s₀.mem s₃.mem := by
    refine hL.frame.trans ?_
    rw [← hm₁]
    refine Frame.trans (hR.frame.sub (tab_in s₀)) ?_
    exact hst₃.sub fun r hr => ⟨r, by simp at hr; simp [hr], fun _ h => h⟩
  have hst : stateAt s₃.mem (st s₀) =
      Vector.zipWith (· + ·) (Spec.Sha512.rounds (stateAt s.mem (st s₀)) (blk s₀ i) (2 * 40))
        (stateAt s.mem (st s₀)) := by
    rw [hm₃, hg₂ .x0 (by decide) (by decide), hL.x0, stateAt_writeState]
  have hcommon : Common s₀ (i + 1) s₃ := by
    refine ⟨by rw [hg₃ .x0 (by decide) (by decide), hg₂ .x0 (by decide) (by decide), hL.x0],
      by rw [hg₃ .x3 (by decide) (by decide), hg₂ .x3 (by decide) (by decide), hL.x3],
      ?_, by rw [hrd₃, hR.rd, hrd₁, hL.rd], by rw [hwr₃, hR.wr, hwr₁, hL.wr], hframe, ?_⟩
    · intro r hr
      have key : ∀ r ∈ preserved, r ≠ .x1 ∧ r ≠ .x2 ∧ r ≠ .x4 ∧ r ≠ .x5 := by decide
      have hn := key r hr
      rw [hg₃ r hn.1 hn.2.1, hg₂ r hn.2.2.1 hn.2.2.2, hL.kept r hr]
    · rw [hst, compressBlocks_succ, ← hL.state]
      rfl
  have htab₃ : Tab s₃.mem (scr s₀) 80 :=
    (hR.tab.mono (by cases first <;> simp [tabLen])).of_frame (by decide) hst₃
      (by simpa using hp.st_scr.symm)
  have := hp.nb_lt
  by_cases hlast : i + 1 = nb s₀
  · refine .inl ⟨hlast, hlast ▸ hcommon, ?_⟩
    rw [hx2₃, hx2, hlast, Nat.sub_self]; rfl
  · refine .inr ⟨by omega, { hcommon with x1 := ?_, x2 := ?_ },
      by rw [hst]; exact ⟨h24₃, h25₃, h26₃, h27₃, h31₃.trans hH₂.v31⟩, htab₃⟩
    · rw [hx1₃, hg₂ .x1 (by decide) (by decide), hL.x1]
      exact (Offset.add_add _ _ 128).trans
        (congrArg (bp s₀ + ·) (congrArg (BitVec.ofNat 64) (by omega)))
    · rw [hx2₃, hx2]

theorem x2_ne_zero {s₀ s : State} {i : Nat} (hp : AArch64.Pre s₀) (hi : i < nb s₀) (hL : LInv s₀ i s) :
    (s.gpr .x2 == 0) = false := by
  have := hp.nb_lt
  rw [hL.x2]
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro h
  have h' := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h'
  simp at h'; omega

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
    have hin : ∀ d, d ≤ 48 → InRegions (s₀.rd ++ s₀.wr) (s₀.gpr .x0 + BitVec.ofNat 64 d) 16 :=
      fun d hd => ⟨stR s₀, by simp [hp.wr], contains_offset (by omega) (by omega)⟩
    refine WP.seq ((init_ok s₀ hin).mono fun s₁ ⟨hH, hg, hm, hrd, hwr⟩ => ?_)
    have hL₀ : LInv s₀ 0 s₁ :=
      { x0 := by rw [hg]
        x3 := by rw [hg]
        kept := fun r _ => by rw [hg]
        rd := hrd
        wr := hwr
        frame := by rw [hm]; exact Frame.refl _ _
        state := by rw [hm]; rfl
        x1 := by rw [hg]; simp [blkAddr]
        x2 := by rw [hg]; simp [nb] }
    refine WP.seq ((block_ok true hp hpos hL₀ (by rw [hm]; exact hH) (fun h => absurd h (by decide))).mono
      fun s₂ h₂ => ?_)
    let Inv : Nat → State → Prop := fun m s =>
      ∃ i, m = nb s₀ - i ∧ i < nb s₀ ∧ LInv s₀ i s ∧ Held s (stateAt s.mem (st s₀)) ∧
        Tab s.mem (scr s₀) 80
    have hstep : ∀ m s, Inv m s → WP isa body s (fun s' =>
        (eval (.nonzero .x .x2) s' = some false ∧ Common s₀ (nb s₀) s') ∨
        (eval (.nonzero .x .x2) s' = some true ∧ ∃ m' < m, Inv m' s')) := by
      rintro m s ⟨i, rfl, hi, hL, hH, ht⟩
      refine WP.mono (block_ok false hp hi hL hH fun _ => ht) fun s' h => ?_
      rcases h with ⟨-, hc, h0⟩ | ⟨hi', hL', hH', ht'⟩
      · exact .inl ⟨by simp [eval, State.read, h0], hc⟩
      · refine .inr ⟨?_, nb s₀ - (i + 1), by omega, i + 1, rfl, hi', hL', hH', ht'⟩
        have := x2_ne_zero hp hi' hL'
        simp only [eval, State.read, Size.bits, BitVec.setWidth_eq]
        simpa using this
    rcases h₂ with ⟨-, hc, h0⟩ | ⟨hi', hL', hH', ht'⟩
    · refine WP.ite true (by simp [eval, State.read, h0]) (fun _ => WP.block_nil (M := isa) hc)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp only [eval, State.read, Size.bits, BitVec.setWidth_eq,
          x2_ne_zero hp hi' hL']) (fun h => absurd h (by decide)) (fun _ => ?_)
      exact WP.loop (M := isa) Inv hstep (nb s₀ - 1) s₂ ⟨1, rfl, hi', hL', hH', ht'⟩


theorem compress_verified :
    Verified AArch64.target Impl.Sha512.AArch64.Sha3.compress Proof.Sha512.compressAArch64 := by
  refine ⟨fun s hs => ?_, ?_, ?_⟩
  · obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
    exact ⟨t, s', he, ⟨h₁, Exec.sp he, Exec.preservedV he⟩, h₂⟩
  · refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.x0, .x1, .x2, .x3]) ?_ (by taint_decide)
    intro s₁ s₂ _ _ ⟨h1, h2, h3, h4, hsp⟩
    refine ⟨hsp, fun r hr => ?_⟩
    simp only [VG.AArch64.Taint.mem_ofRegs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> assumption
  · exact AArch64.compress_verified.2.2

end VG.Proof.Sha512.AArch64.Sha3
