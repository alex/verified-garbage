import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Rounds
import VerifiedGarbage.Impl.Aes.X86_64.Vaes
import VerifiedGarbage.Proof.Framework.X86_64.Avx
import VerifiedGarbage.Proof.Framework.X86_64.YFrame

/-!
# VAES: encrypting both lanes of the block registers

`aesG_ok`: `Impl.Aes.X86_64.Vaes.aesK k regs g` encrypts both 128-bit lanes
of each register of `regs` with the key schedule at `rdi` (10, 12 or 14
rounds, as `rsi` says), with the round keys in `k`, whatever the list of
registers; the blocks `g j` between the rounds, which leave those registers
and `k` alone, do what they do (`Q`). `aes_ok` is the case of `ymm8` and no
blocks between the rounds. The VEX.256 `vpxor`, `vaesenc`
and `vaesenclast` act on each lane as `pxor`, `aesenc` and `aesenclast` do on
an SSE register (`VBinOp.sse`), so each lane goes through the rounds that
`AesNi.aes_ok` proves of an SSE register (`AesNi.pxor_st`, `aesenc_st`,
`aesenclast_st`); `vbroadcasti128` puts the round key in both lanes.
-/

namespace VG.Proof.Aes.X86_64.Vaes

open VG.X86_64
open VG.Impl.Aes.X86_64.Vaes (keyOpK roundK aesK aes)
open VG.Impl.Aes.X86_64.AesNi (at_)
open VG.Proof.Aes.X86_64.AesNi (st rnds rnds_zero rnds_succ cipher_eq Keys ea_at ofInt_natCast
  byte_roundKey pxor_st aesenc_st aesenclast_st cmpRsi_ok)
open VG.Spec.Aes (roundKey cipher)

theorem YFrame.of_keys {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : Keys nr w s)
    (hf : YFrame rs s s') : Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

/-- `op b, b, k` for each `b` of `regs`. -/
theorem map_ok (op : VBinOp) (kr : XReg) : ∀ (regs : List XReg) (s : State), regs.Nodup → kr ∉ regs →
    WP isa (.block (regs.map fun b => .vop (.vbin op .l256 b b kr))) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, s'.lane b l = op.sse.eval (s.lane b l) (s.lane kr l)) ∧ YFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, YFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ kr := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : kr ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨(VOp.vbin op .l256 b b kr).exec s, rfl, ?_⟩
    refine WP.mono (map_ok op kr bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc l hl
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.lane _ hbs l hl, lane_vbin256]; simp
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc l hl, lane_vbin256, lane_vbin256]; simp [hcb, Ne.symm hb8]
    · refine ⟨by rw [hf.gpr]; simp, by rw [hf.mem]; simp, by rw [hf.rd]; simp, by rw [hf.wr]; simp,
        fun r hr l hl => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.lane r hr.2 l hl, lane_vbin256]; simp [hr.1]

/-- A round key into both lanes of `k`, then `op b, b, k` for each `b` of
`regs`. -/
theorem keyOp_ok (kr : XReg) (regs : List XReg) (op : VBinOp) (a : MemOp) (s : State) (hnd : regs.Nodup)
    (h8 : kr ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOpK kr regs op a)) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, s'.lane b l = op.sse.eval (s.lane b l) (s.mem.readW (s.ea a) 128)) ∧
      YFrame (kr :: regs) s s' := by
  rw [keyOpK, WP.block_cons_iff]
  let v := s.mem.readW (s.ea a) 128
  refine ⟨s.setV .l256 kr v v, by simp [isa, exec, State.load128, hin, v], ?_⟩
  refine WP.mono (map_ok op kr regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, ?_⟩
  · have hb8 : b ≠ kr := fun h => h8 (h ▸ hb)
    rw [hv b hb l hl, State.lane_setV256, State.lane_setV256]
    simp only [hb8, ite_false, ite_true]
    split <;> rfl
  · refine ⟨by rw [hf.gpr]; rfl, by rw [hf.mem]; rfl, by rw [hf.rd]; rfl, by rw [hf.wr]; rfl,
      fun r hr l hl => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.lane r hr.2 l hl, State.lane_setV256]; simp [hr.1]

/-! ## The rounds -/

/-- Both lanes of each register `b` of `regs` hold the state after `k` rounds
of the cipher, from the states `x b l`. -/
def RInv (regs : List XReg) (w : List Byte) (x : XReg → Nat → Spec.Aes.State) (k : Nat) (s : State) :
    Prop :=
  ∀ b ∈ regs, ∀ l < 2, st (s.lane b l) = rnds w (x b l) k

theorem round_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (roundK kr regs (k + 1))) s fun s' =>
      RInv regs w x (k + 1) s' ∧ YFrame (kr :: regs) s s' := by
  refine WP.mono (keyOp_ok kr regs .vaesenc _ s hnd h8 (by rw [ea_at]; exact hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb l hl => ?_, hf⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenc _ _) = _
  rw [aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.sched, ea_at]; exact byte_roundKey _ _ (by omega)), hI b hb l hl, rnds_succ]

theorem mem_kr_l {kr r : XReg} {regs G : List XReg} (h : r ∈ kr :: regs) : r ∈ kr :: (regs ++ G) := by
  rcases List.mem_cons.mp h with h | h
  · exact h ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)

theorem mem_kr_r {kr r : XReg} {regs G : List XReg} (h : r ∈ G) : r ∈ kr :: (regs ++ G) :=
  List.mem_cons_of_mem _ (List.mem_append_right _ h)

/-- Rounds 1 to `k` (at most 9), with `g j` after round `j`. -/
theorem roundsG_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Nat → Spec.Aes.State} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (kr :: regs) s s' → Q j s')
    (k : Nat) (s : State) (hk : k ≤ 9) (hnr : 9 ≤ nr) (hK : Keys nr w s) (hI : RInv regs w x 0 s)
    (hQ : Q 1 s) :
    WP isa (.block ((List.range k).flatMap fun j => roundK kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv regs w x k s' ∧ Q (k + 1) s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
  induction k with
  | zero =>
    rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, hQ, YFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [WP.block_append_iff]
    refine WP.mono (round_ok kr regs hnd h8 (k := k) (by omega) (YFrame.of_keys hK hf₁) hI₁)
      fun s₂ ⟨hI₂, hf₂⟩ => ?_
    refine WP.mono (hg (k + 1) (by omega) (by omega) s₂ (YFrame.of_keys (YFrame.of_keys hK hf₁) hf₂)
      (hq _ _ _ hQ₁ hf₂)) fun s' ⟨hQ', hf'⟩ => ⟨fun b hb l hl => ?_, hQ', ?_⟩
    · rw [hf'.lane b (fun h => (hG b h).2 hb) l hl]; exact hI₂ b hb l hl
    · exact hf₁.trans ((hf₂.mono fun _ => mem_kr_l).trans
        (hf'.mono fun _ => mem_kr_r))

/-- `cmp rsi, c` with `rsi = nr`. -/
theorem cmpRsi_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ YFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

theorem aesG_ok (kr : XReg) (regs : List XReg) (hnd : regs.Nodup) (h8 : kr ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (g : Nat → List Instr) (G : List XReg)
    (hG : ∀ r ∈ G, r ≠ kr ∧ r ∉ regs) (Q : Nat → State → Prop)
    (hg : ∀ j, 1 ≤ j → j ≤ 9 → ∀ s, Keys nr w s → Q j s →
      WP isa (.block (g j)) s fun s' => Q (j + 1) s' ∧ YFrame G s s')
    (hq : ∀ j s s', Q j s → YFrame (kr :: regs) s s' → Q j s')
    (s : State) (hK : Keys nr w s) (hQ : Q 1 s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aesK kr regs g) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧ Q 10 s' ∧
      YFrame (kr :: (regs ++ G)) s s' := by
  let x : XReg → Nat → Spec.Aes.State := fun b l => st (s.lane b l)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOpK kr regs .vpxor (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => roundK kr regs (j + 1) ++ g (j + 1))) s fun s' =>
      RInv regs w x 9 s' ∧ Q 10 s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (keyOp_ok kr regs .vpxor _ s hnd h8 (by rw [ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : RInv regs w x 0 s₁ := fun b hb l hl => by
      rw [hv₁ b hb l hl]
      show st (XBinOp.eval .pxor _ _) = _
      rw [pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
    exact WP.mono (roundsG_ok kr regs hnd h8 g G hG Q hg hq 9 s₁ (by omega) (by omega)
        (YFrame.of_keys hK hf₁) hI₁ (hq _ _ _ hQ hf₁))
      fun s' ⟨hI', hQ', hf'⟩ => ⟨hI', hQ', (hf₁.mono fun _ => mem_kr_l).trans hf'⟩
  have keep : ∀ {s₁ s₂ : State} {k : Nat}, RInv regs w x k s₁ → YFrame [] s₁ s₂ →
      RInv regs w x k s₂ :=
    fun hI hf b hb l hl => by rw [hf.lane b (by simp) l hl]; exact hI b hb l hl
  -- Rounds 10 to `nr - 1`.
  have keepQ : ∀ {s₁ s₂ : State}, Q 10 s₁ → YFrame (kr :: regs) s₁ s₂ → Q 10 s₂ :=
    fun h hf => hq _ _ _ h hf
  have h₂ : ∀ s₁, RInv regs w x 9 s₁ → Q 10 s₁ → YFrame (kr :: (regs ++ G)) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (roundK kr regs 10 ++ roundK kr regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (roundK kr regs 12 ++ roundK kr regs 13))))) s₁ fun s' =>
        RInv regs w x (nr - 1) s' ∧ Q 10 s' ∧ YFrame (kr :: (regs ++ G)) s s' := by
    intro s₁ hI₁ hQ₁ hf₁ hz₁
    have hK₁ := YFrame.of_keys hK hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hQ₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (round_ok kr regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (round_ok kr regs hnd h8 (k := 10) (by omega) (YFrame.of_keys hK₁ hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (cmpRsi_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hQ₄ : Q 10 s₄ := keepQ (keepQ (keepQ hQ₁ hf₂) hf₃) (hf₄.mono (by simp))
      have hf₂₄ : YFrame (kr :: regs) s₁ s₄ := hf₂.trans (hf₃.trans (hf₄.mono (by simp)))
      have hf₁₄ := hf₁.trans (hf₂₄.mono fun _ => mem_kr_l)
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil ⟨keep hI₃ hf₄, hQ₄, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := YFrame.of_keys hK₁ (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      refine WP.mono (round_ok kr regs hnd h8 (k := 11) (by omega) hK₄ (keep hI₃ hf₄))
        fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (round_ok kr regs hnd h8 (k := 12) (by omega) (YFrame.of_keys hK₄ hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', keepQ (keepQ hQ₄ hf₅) hf', hf₁₄.trans ((hf₅.trans hf').mono fun _ => mem_kr_l)⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hQ₁, hf₁⟩ => ?_
  refine WP.mono (cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (keep hI₁ hf₁') (keepQ hQ₁ (hf₁'.mono (by simp))) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hQ₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hf₂.gpr, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := YFrame.of_keys hK hf₂
  refine WP.mono (keyOp_ok kr regs .vaesenclast _ s₂ hnd h8 (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb l hl => ?_, keepQ hQ₂ hf', hf₂.trans (hf'.mono fun _ => mem_kr_l)⟩
  rw [hv b hb l hl]
  show st (XBinOp.eval .aesenclast _ _) = _
  rw [aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb l hl, cipher_eq]

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, ∀ l < 2, st (s'.lane b l) = cipher nr w (st (s.lane b l))) ∧
      YFrame (.xmm8 :: regs) s s' :=
  WP.mono (aesG_ok .xmm8 regs hnd h8 hnr (fun _ => []) [] (fun _ h => absurd h List.not_mem_nil)
      (fun _ _ => True) (fun _ _ _ _ _ _ => WP.block_nil ⟨trivial, YFrame.refl _ _⟩)
      (fun _ _ _ _ _ => trivial) s hK trivial hrsi hr10)
    fun _ ⟨hc, _, hf⟩ => ⟨hc, hf.mono fun r hr => by simpa using hr⟩

end VG.Proof.Aes.X86_64.Vaes
