import VerifiedGarbage.Proof.Sha512.Arm.Rounds

/-!
# SHA-512 on ARMv7: the inlined compression function

Untrusted: everything here is checked by Lean. `compress_ok`: with `state`
in `r0` and `scratch` in `r3`, `Impl.Sha512.Arm.compress` compresses the
block in the streaming state's buffer into its hash value.
-/

namespace VG.Proof.Sha512.Arm

open VG VG.Arm VG.Impl.Sha512.Arm
open VG.Spec.Sha512 (HashValue Word Block W stateAt blockAt compress parseBlock)
open VG.Proof.Sha256.Arm (contains_offset)

/-! ## Memory -/

theorem stateAt_get {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) (m : Mem) {k : Nat} (hk : k < 8) :
    (stateAt m (State.addr st))[k] = rd64 m st (8 * k) := by
  simp only [stateAt, Vector.getElem_ofFn, rd64]
  rw [readW64, A_eq (by omega), A_eq (by omega),
    show State.addr st + BitVec.ofNat 64 (8 * k) + 4 = State.addr st + BitVec.ofNat 64 (8 * k + 4) by
      bv_omega]

theorem stateAt_ext {st : BitVec 32} (hfit : st.toNat + 64 ≤ 2 ^ 32) {m : Mem} {H : HashValue}
    (h : ∀ k (hk : k < 8), rd64 m st (8 * k) = H[k]) : stateAt m (State.addr st) = H := by
  ext k hk
  rw [stateAt_get hfit m hk, h k hk]

theorem cat44 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((b0 ++ b1 ++ b2 ++ b3 : BitVec 32) ++ (b4 ++ b5 ++ b6 ++ b7 : BitVec 32) : BitVec 64) =
      (b0 ++ b1 ++ b2 ++ b3 ++ b4 ++ b5 ++ b6 ++ b7 : BitVec 64) := by
  simp only [BitVec.append_assoc, BitVec.cast_eq]

theorem add_one' (p : Addr) (a : Nat) : p + BitVec.ofNat 64 a + 1 = p + BitVec.ofNat 64 (a + 1) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

theorem add_64' (p : Addr) (a : Nat) : p + 64 + BitVec.ofNat 64 a = p + BitVec.ofNat 64 (64 + a) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]; rfl

/-- `loadW` makes the block's words from its bytes. -/
theorem raw_block {st : BitVec 32} (hfit : st.toNat + 192 ≤ 2 ^ 32) (m : Mem) :
    Raw st (blockAt m (State.addr st + 64)) m := by
  intro j hj
  rw [W_lt _ hj]
  simp only [blockAt, parseBlock, rd64, lo_append, hi_append, wOff, Nat.mod_eq_of_lt hj]
  rw [A_eq (by omega), A_eq (by omega), rev_readW, rev_readW]
  simp only [add_one', add_64', Nat.add_assoc]
  exact cat44 _ _ _ _ _ _ _ _

theorem rd64_frame {rs : List Region} {m m' : Mem} (h : Frame rs m m') {b : BitVec 32} {N o : Nat}
    (hd : ∀ r ∈ rs, Region.Disjoint ⟨State.addr b, N⟩ r) (hfit : b.toNat + N ≤ 2 ^ 32) (ho : o + 8 ≤ N) :
    rd64 m' b o = rd64 m b o := by
  simp only [rd64]
  rw [h.readW (contains_A hfit (by omega)) hd (by decide),
    h.readW (contains_A hfit (by omega)) hd (by decide)]

/-! ## Loading the working variables -/

structure LInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  vars : ∀ k < n, rd64 s'.mem scr (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [varR scr] s.mem s'.mem

theorem load_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap loadH)) s (LInv st scr s n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [loadH, ← List.append_nil (Impl.Sha512.Arm.st X0 X1 .r3 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r0 (c₁.wS _ (by omega)).1
      (c₁.wS _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_st (by omega) (by rw [o₂.gpr _ (by decide), c₁.r3]) p₂
      (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wV _ (by omega)).2)
      fun s₃ u₃ => WP.block_nil ⟨fun r hr => ?_, by rw [u₃.rd, o₂.rd, h₁.rd],
        by rw [u₃.wr, o₂.wr, h₁.wr], by rw [u₃.sp, o₂.sp, h₁.sp], fun k hk => ?_, ?_⟩
    · rw [u₃.gpr, o₂.gpr r hr, h₁.gpr r hr]
    · have fitV := c.fitV
      rw [u₃.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disj) c.fitS (by omega)]
      · rw [rd64_write64_ne (b := scr) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega), o₂.mem]
        exact h₁.vars k (by omega)
    · rw [u₃.mem, o₂.mem]
      exact frame_write64 (N := 64) (o := 8 * n) h₁.frame (by simp) c.fitV (by omega) _

/-! ## Adding them into the hash value -/

structure UInv (st scr : BitVec 32) (s : State) (n : Nat) (s' : State) : Prop where
  gpr : ∀ r, r ∉ [Z0, Z1, X0, X1] → s'.gpr r = s.gpr r
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr
  sp : s'.sp = s.sp
  done : ∀ k < n, rd64 s'.mem st (8 * k) = rd64 s.mem scr (8 * k) + rd64 s.mem st (8 * k)
  todo : ∀ k, n ≤ k → k < 8 → rd64 s'.mem st (8 * k) = rd64 s.mem st (8 * k)
  frame : Frame [stR st] s.mem s'.mem

theorem update_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap addH)) s (UInv st scr s n) := by
  intro n hn
  have fitS := c.fitS
  induction n with
  | zero => exact WP.block_nil ⟨fun _ _ => rfl, rfl, rfl, rfl, fun _ h => absurd h (by omega),
      fun _ _ _ => rfl, Frame.refl _ _⟩
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, WP.block_append_iff]
    refine WP.mono (ih (by omega)) fun s₁ h₁ => ?_
    have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [addH, List.append_assoc, List.append_assoc, ← List.append_nil (Impl.Sha512.Arm.st Z0 Z1 .r0 (8 * n))]
    refine wp_ld (by decide) (by decide) (by omega) c₁.r3 (c₁.wV _ (by omega)).1
      (c₁.wV _ (by omega)).2 fun s₂ o₂ p₂ => ?_
    refine wp_ld (by decide) (by decide) (by omega) (by rw [o₂.gpr _ (by decide), c₁.r0])
      (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).1) (by rw [o₂.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₃ o₃ p₃ => ?_
    refine wp_add64 (by decide) (by decide) (p₂.of_only o₃ (by decide) (by decide)) p₃
      fun s₄ o₄ p₄ => ?_
    have O := (o₂.trans o₃).trans o₄
    refine wp_st (by omega) (by rw [O.gpr _ (by decide), c₁.r0]) p₄
      (by rw [O.wr]; exact (c₁.wS _ (by omega)).1) (by rw [O.wr]; exact (c₁.wS _ (by omega)).2)
      fun s₅ u₅ => WP.block_nil ⟨fun r hr => ?_, by rw [u₅.rd, O.rd, h₁.rd],
        by rw [u₅.wr, O.wr, h₁.wr], by rw [u₅.sp, O.sp, h₁.sp], fun k hk => ?_, fun k hk hk' => ?_, ?_⟩
    · rw [u₅.gpr, (O.mono (by decide)).gpr r hr, h₁.gpr r hr]
    · rw [u₅.mem, O.mem, o₂.mem]
      by_cases hkn : k = n
      · subst hkn
        rw [rd64_write64_self _ _ (by omega), h₁.todo k (by omega) (by omega),
          rd64_frame h₁.frame (fun r hr => by simp at hr; subst hr; exact c.disj.symm) c.fitV
            (by omega)]
      · rw [rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega) (by omega)
          (by omega)]
        exact h₁.done k (by omega)
    · rw [u₅.mem, O.mem, rd64_write64_ne (b := st) (o := 8 * n) (o' := 8 * k) _ _ (by omega)
        (by omega) (by omega)]
      exact h₁.todo k (by omega) hk'
    · rw [u₅.mem, O.mem]
      exact frame_write64 (N := 192) (o := 8 * n) h₁.frame (by simp) c.fitS (by omega) _

/-! ## The whole compression -/

theorem compress_ok {st scr : BitVec 32} {s : State} (c : Ctx st scr s) {Q : State → Prop}
    (hQ : ∀ s', (∀ r, r ∉ temps → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      Frame [stR st, varR scr] s.mem s'.mem →
      stateAt s'.mem (State.addr st) =
        compress (stateAt s.mem (State.addr st)) (blockAt s.mem (State.addr st + 64)) → Q s') :
    WP isa Impl.Sha512.Arm.compress s Q := by
  have fitS := c.fitS
  have fitV := c.fitV
  set H := stateAt s.mem (State.addr st)
  set M := blockAt s.mem (State.addr st + 64)
  refine WP.seq (WP.mono (load_ok c 8 le_rfl) fun s₁ h₁ => ?_)
  have c₁ := c.of_eq (h₁.gpr _ (by decide)) (h₁.gpr _ (by decide)) h₁.wr
  have hd₁ : ∀ r ∈ [varR scr], Region.Disjoint (stR st) r := fun r hr => by
    simp at hr; subst hr; exact c.disj
  have hM : Raw st M s₁.mem := fun j hj => by
    rw [rd64_frame h₁.frame hd₁ fitS (wOff_lt j)]
    exact raw_block fitS s.mem j hj
  have h0 : ∀ k (hk : k < 8), rd64 s₁.mem scr (8 * k) = H[k] := fun k hk => by
    rw [h₁.vars k hk, stateAt_get (by omega) _ hk]
  refine WP.seq (WP.mono (rounds_ok c₁ hM h0 80 le_rfl) fun s₂ h₂ => ?_)
  have c₂ := c₁.of_rinv h₂
  refine WP.mono (update_ok c₂ 8 le_rfl) fun s₃ h₃ => hQ s₃ (fun r hr => ?_)
    (by rw [h₃.rd, h₂.rd, h₁.rd]) (by rw [h₃.wr, h₂.wr, h₁.wr]) (by rw [h₃.sp, h₂.sp, h₁.sp]) ?_ ?_
  · have e₃ : ∀ r ∈ [Z0, Z1, X0, X1], r ∈ temps := by decide
    have e₁ : ∀ r ∈ [X0, X1], r ∈ temps := by decide
    rw [h₃.gpr r fun h => hr (e₃ r h), h₂.gpr r hr, h₁.gpr r fun h => hr (e₁ r h)]
  · exact ((h₁.frame.mono (by simp)).trans h₂.frame).trans (h₃.frame.mono (by simp))
  · refine stateAt_ext (by omega) fun k hk => ?_
    rw [h₃.done k hk, show 8 * k = vOff 80 k by simp only [vOff]; omega, h₂.vars k hk,
      show vOff 80 k = 8 * k by simp only [vOff]; omega, h₂.hash k hk,
      rd64_frame h₁.frame hd₁ fitS (by omega), ← stateAt_get (by omega) _ hk]
    simp only [Spec.Sha512.compress, Vector.getElem_zipWith]
    rfl

end VG.Proof.Sha512.Arm
