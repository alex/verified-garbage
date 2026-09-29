import VerifiedGarbage.Proof.Aes.X86_64.AesNi.Cipher
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Impl.Aes.X86_64.AesNi

/-!
# AES-NI: encrypting the block registers

Untrusted: everything here is checked by Lean. `aes_ok`: `Impl.Aes.X86_64.AesNi.aes regs`
encrypts each register of `regs` with the key schedule at `rdi` (10, 12 or
14 rounds, as `rsi` says), whatever the list of registers; the rounds are
composed by induction, one symbolic execution per instruction.
-/

namespace VG.Proof.Aes.X86_64.AesNi

open VG.X86_64
open VG.Impl.Aes.X86_64.AesNi (at_ keyOp round aes)
open VG.Spec.Aes (subBytes shiftRows mixColumns addRoundKey roundKey cipher bytesAt)

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

theorem contains_offset {base : Addr} {len off n : Nat} (h : off + n ≤ len) (ho : off < 2 ^ 64) :
    (⟨base, len⟩ : Region).Contains (base + BitVec.ofNat 64 off) n := by
  simp only [Region.Contains]
  rw [show base + BitVec.ofNat 64 off - base = BitVec.ofNat 64 off by bv_omega, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ho]
  exact h

/-- An address relative to `p + o`, as a distance from `p`. -/
theorem off_toNat (a p : Addr) {o : Nat} (ho : o < 2 ^ 64) :
    (a - (p + BitVec.ofNat 64 o)).toNat = ((a - p).toNat + (2 ^ 64 - o)) % 2 ^ 64 := by
  rw [show a - (p + BitVec.ofNat 64 o) = (a - p) - BitVec.ofNat 64 o by
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc],
    BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho, Nat.add_comm]

/-- `s'` is `s` but for the SSE registers `rs` (and the flags). -/
structure XFrame (rs : List XReg) (s s' : State) : Prop where
  gpr : s'.gpr = s.gpr
  mem : s'.mem = s.mem
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  xmm : ∀ r, r ∉ rs → s'.xmm r = s.xmm r

theorem XFrame.refl (rs : List XReg) (s : State) : XFrame rs s s :=
  ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem XFrame.trans {rs : List XReg} {s s' s'' : State} (h : XFrame rs s s') (h' : XFrame rs s' s'') :
    XFrame rs s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr,
    fun r hr => (h'.xmm r hr).trans (h.xmm r hr)⟩

theorem XFrame.comp {rs rs' : List XReg} {s s' s'' : State} (h : XFrame rs s s')
    (h' : XFrame rs' s' s'') : XFrame (rs ++ rs') s s'' :=
  ⟨h'.gpr.trans h.gpr, h'.mem.trans h.mem, h'.rd.trans h.rd, h'.wr.trans h.wr, fun r hr => by
    simp only [List.mem_append, not_or] at hr
    exact (h'.xmm r hr.2).trans (h.xmm r hr.1)⟩

theorem XFrame.mono {rs rs' : List XReg} {s s' : State} (h : XFrame rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    XFrame rs' s s' :=
  ⟨h.gpr, h.mem, h.rd, h.wr, fun r hr => h.xmm r fun h' => hr (hs r h')⟩

/-- `op b, xmm8` for each `b` of `regs`. -/
theorem map_ok (op : XBinOp) : ∀ (regs : List XReg) (s : State), regs.Nodup → .xmm8 ∉ regs →
    WP isa (.block (regs.map fun b => .xop (.bin op b .xmm8))) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.xmm .xmm8)) ∧ XFrame regs s s'
  | [], s, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, XFrame.refl _ _⟩
  | b :: bs, s, hnd, h8 => by
    have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ List.mem_cons_self ..)
    have h8' : .xmm8 ∉ bs := fun h => h8 (List.mem_cons_of_mem _ h)
    have hbs : b ∉ bs := (List.nodup_cons.mp hnd).1
    rw [List.map_cons, WP.block_cons_iff]
    refine ⟨s.setXmm b (op.eval (s.xmm b) (s.xmm .xmm8)), rfl, ?_⟩
    refine WP.mono (map_ok op bs _ (List.nodup_cons.mp hnd).2 h8') fun s' ⟨hv, hf⟩ => ⟨?_, ?_⟩
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · rw [hf.xmm _ hbs]; simp [State.setXmm]
      · have hcb : c ≠ b := fun h => hbs (h ▸ hc)
        rw [hv c hc]; simp [State.setXmm, hcb, Ne.symm hb8]
    · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
      simp only [List.mem_cons, not_or] at hr
      rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-- A round key into `xmm8`, then `op b, xmm8` for each `b` of `regs`. -/
theorem keyOp_ok (regs : List XReg) (op : XBinOp) (a : MemOp) (s : State) (hnd : regs.Nodup)
    (h8 : .xmm8 ∉ regs) (hin : InRegions (s.rd ++ s.wr) (s.ea a) 16) :
    WP isa (.block (keyOp regs op a)) s fun s' =>
      (∀ b ∈ regs, s'.xmm b = op.eval (s.xmm b) (s.mem.readW (s.ea a) 128)) ∧
      XFrame (.xmm8 :: regs) s s' := by
  rw [keyOp, WP.block_cons_iff]
  refine ⟨s.setXmm .xmm8 (s.mem.readW (s.ea a) 128), by
    simp [isa, exec, State.load128, hin], ?_⟩
  refine WP.mono (map_ok op regs _ hnd h8) fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, ?_⟩
  · have hb8 : b ≠ .xmm8 := fun h => h8 (h ▸ hb)
    rw [hv b hb]; simp [State.setXmm, hb8]
  · refine ⟨hf.gpr, hf.mem, hf.rd, hf.wr, fun r hr => ?_⟩
    simp only [List.mem_cons, not_or] at hr
    rw [hf.xmm r hr.2]; simp [State.setXmm, hr.1]

/-! ## The rounds -/

/-- Each register `b` of `regs` holds the state after `k` rounds of the
cipher, from the state `x b`. -/
def RInv (regs : List XReg) (w : List Byte) (x : XReg → Spec.Aes.State) (k : Nat) (s : State) : Prop :=
  ∀ b ∈ regs, st (s.xmm b) = rnds w (x b) k

/-- What the rounds need of the state: the key schedule at `rdi`, readable. -/
structure Keys (nr : Nat) (w : List Byte) (s : State) : Prop where
  sched : w = bytesAt s.mem (s.gpr .rdi) (16 * (nr + 1))
  le : nr ≤ 14
  keys : ∀ j ≤ nr, InRegions (s.rd ++ s.wr) (s.gpr .rdi + BitVec.ofInt 64 ((16 * j : Nat) : Int)) 16

theorem Keys.of_frame {nr : Nat} {w : List Byte} {rs : List XReg} {s s' : State} (h : Keys nr w s)
    (hf : XFrame rs s s') : Keys nr w s' :=
  ⟨by rw [hf.mem, hf.gpr]; exact h.sched, h.le, by rw [hf.rd, hf.wr, hf.gpr]; exact h.keys⟩

theorem round_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} {k : Nat} (hk : k + 1 ≤ nr) {s : State}
    (hK : Keys nr w s) (hI : RInv regs w x k s) :
    WP isa (.block (round regs (k + 1))) s fun s' =>
      RInv regs w x (k + 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
  refine WP.mono (keyOp_ok regs .aesenc _ s hnd h8 (by rw [ea_at]; exact hK.keys _ hk))
    fun s' ⟨hv, hf⟩ => ⟨fun b hb => ?_, hf⟩
  rw [hv b hb, aesenc_st _ _ (roundKey w (k + 1)) (by
    rw [hK.sched, ea_at]; exact byte_roundKey _ _ (by omega)), hI b hb, rnds_succ]

theorem rounds_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    {w : List Byte} {x : XReg → Spec.Aes.State} (k : Nat) (s : State) (hk : k ≤ nr)
    (hK : Keys nr w s) (hI : RInv regs w x 0 s) :
    WP isa (.block ((List.range k).flatMap fun j => round regs (j + 1))) s fun s' =>
      RInv regs w x k s' ∧ XFrame (.xmm8 :: regs) s s' := by
  induction k with
  | zero => rw [List.range_zero, List.flatMap_nil]; exact WP.block_nil ⟨hI, XFrame.refl _ _⟩
  | succ k ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ ⟨hI₁, hf₁⟩ => ?_
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact WP.mono (round_ok regs hnd h8 (k := k) (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩

/-- `cmp rsi, c` with `rsi = nr`. -/
theorem cmpRsi_ok (s : State) (c : BitVec 32) (nr : Nat) (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr) :
    WP isa (.block [.alu .cmp .rsi (.imm c)]) s fun s' =>
      s'.zf = some (BitVec.ofNat 64 nr - c.signExtend 64 == 0) ∧ XFrame [] s s' := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, execAlu, readSrc, arithFlags,
    State.setFlags, isa, hrsi, Option.bind_some, Option.some.injEq, exists_eq_left']
  exact ⟨trivial, rfl, rfl, rfl, rfl, fun _ _ => rfl⟩

theorem aes_ok (regs : List XReg) (hnd : regs.Nodup) (h8 : .xmm8 ∉ regs) {nr : Nat}
    (hnr : nr = 10 ∨ nr = 12 ∨ nr = 14) {w : List Byte} (s : State) (hK : Keys nr w s)
    (hrsi : s.gpr .rsi = BitVec.ofNat 64 nr)
    (hr10 : s.gpr .r10 = s.gpr .rdi + BitVec.ofNat 64 (16 * nr)) :
    WP isa (aes regs) s fun s' =>
      (∀ b ∈ regs, st (s'.xmm b) = cipher nr w (st (s.xmm b))) ∧ XFrame (.xmm8 :: regs) s s' := by
  let x : XReg → Spec.Aes.State := fun b => st (s.xmm b)
  have k0 := byte_roundKey s.mem (s.gpr .rdi) (L := 16 * (nr + 1)) (j := 0) (by omega)
  simp only [Nat.mul_zero] at k0
  -- `AddRoundKey` and rounds 1–9.
  have h₁ : WP isa (.block (keyOp regs .pxor (at_ .rdi 0) ++
      (List.range 9).flatMap fun j => round regs (j + 1))) s fun s' =>
      RInv regs w x 9 s' ∧ XFrame (.xmm8 :: regs) s s' := by
    rw [WP.block_append_iff]
    refine WP.mono (keyOp_ok regs .pxor _ s hnd h8 (by rw [ea_at]; exact hK.keys 0 (by omega)))
      fun s₁ ⟨hv₁, hf₁⟩ => ?_
    have hI₁ : RInv regs w x 0 s₁ := fun b hb => by
      rw [hv₁ b hb, pxor_st _ _ (roundKey w 0) (by rw [hK.sched, ea_at]; exact k0), rnds_zero]
    exact WP.mono (rounds_ok regs hnd h8 9 s₁ (by omega) (hK.of_frame hf₁) hI₁)
      fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁.trans hf'⟩
  -- Rounds 10 to `nr - 1`.
  have h₂ : ∀ s₁, RInv regs w x 9 s₁ → XFrame (.xmm8 :: regs) s s₁ →
      s₁.zf = some (BitVec.ofNat 64 nr - (10 : BitVec 32).signExtend 64 == 0) →
      WP isa (.ite .e (.block [])
        (.seq (.block (round regs 10 ++ round regs 11 ++ [.alu .cmp .rsi (.imm 12)]))
          (.ite .e (.block []) (.block (round regs 12 ++ round regs 13))))) s₁ fun s' =>
        RInv regs w x (nr - 1) s' ∧ XFrame (.xmm8 :: regs) s s' := by
    intro s₁ hI₁ hf₁ hz₁
    have hK₁ := hK.of_frame hf₁
    have hrsi₁ : s₁.gpr .rsi = BitVec.ofNat 64 nr := by rw [hf₁.gpr, hrsi]
    rcases hnr with rfl | rfl | rfl
    · exact WP.ite true (by simp [eval, hz₁]) (fun _ => WP.block_nil ⟨hI₁, hf₁⟩)
        (fun h => absurd h (by decide))
    all_goals
      refine WP.ite false (by simp [eval, hz₁]) (fun h => absurd h (by decide)) fun _ => ?_
      refine WP.seq ?_
      rw [WP.block_append_iff, WP.block_append_iff]
      refine WP.mono (round_ok regs hnd h8 (k := 9) (by omega) hK₁ hI₁) fun s₂ ⟨hI₂, hf₂⟩ => ?_
      refine WP.mono (round_ok regs hnd h8 (k := 10) (by omega) (hK₁.of_frame hf₂) hI₂)
        fun s₃ ⟨hI₃, hf₃⟩ => ?_
      have hrsi₃ : s₃.gpr .rsi = s₁.gpr .rsi := by rw [hf₃.gpr, hf₂.gpr]
      refine WP.mono (cmpRsi_ok s₃ 12 _ (hrsi₃.trans hrsi₁)) fun s₄ ⟨hz₄, hf₄⟩ => ?_
      have hf₁₄ := hf₁.trans (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
    · exact WP.ite true (by simp [eval, hz₄]) (fun _ => WP.block_nil
        ⟨fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb, hf₁₄⟩)
        (fun h => absurd h (by decide))
    · refine WP.ite false (by simp [eval, hz₄]) (fun h => absurd h (by decide)) fun _ => ?_
      rw [WP.block_append_iff]
      have hK₄ := hK₁.of_frame (hf₂.trans (hf₃.trans (hf₄.mono (by simp))))
      have hI₄ : RInv regs w x 11 s₄ := fun b hb => by rw [hf₄.xmm b (by simp)]; exact hI₃ b hb
      refine WP.mono (round_ok regs hnd h8 (k := 11) (by omega) hK₄ hI₄) fun s₅ ⟨hI₅, hf₅⟩ => ?_
      exact WP.mono (round_ok regs hnd h8 (k := 12) (by omega) (hK₄.of_frame hf₅) hI₅)
        fun s' ⟨hI', hf'⟩ => ⟨hI', hf₁₄.trans (hf₅.trans hf')⟩
  refine WP.seq ?_
  rw [WP.block_append_iff]
  refine WP.mono h₁ fun s₁ ⟨hI₁, hf₁⟩ => ?_
  refine WP.mono (cmpRsi_ok s₁ 10 nr (by rw [hf₁.gpr, hrsi])) fun s₁' ⟨hz₁, hf₁'⟩ => ?_
  have hf₁₁ := hf₁.trans (hf₁'.mono (by simp))
  refine WP.seq (WP.mono (h₂ s₁' (fun b hb => by rw [hf₁'.xmm b (by simp)]; exact hI₁ b hb) hf₁₁ hz₁)
    fun s₂ ⟨hI₂, hf₂⟩ => ?_)
  have hea : s₂.ea (at_ .r10 0) = s₂.gpr .rdi + BitVec.ofInt 64 ((16 * nr : Nat) : Int) := by
    rw [ea_at, hf₂.gpr, hr10, ofInt_natCast, ofInt_natCast]; exact BitVec.add_zero _
  have hK₂ := hK.of_frame hf₂
  refine WP.mono (keyOp_ok regs .aesenclast _ s₂ hnd h8 (by rw [hea]; exact hK₂.keys nr (Nat.le_refl _)))
    fun s' ⟨hv, hf'⟩ => ⟨fun b hb => ?_, hf₂.trans hf'⟩
  rw [hv b hb, aesenclast_st _ _ (roundKey w nr) (by
    rw [hea, hK₂.sched]; exact byte_roundKey _ _ (by omega)), hI₂ b hb, cipher_eq]
