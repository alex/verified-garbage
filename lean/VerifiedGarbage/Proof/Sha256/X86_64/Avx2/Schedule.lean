import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Sha256.X86_64.Avx2.Lanes

/-!
# SHA-256 with AVX2 on x86-64: running the message schedule

Untrusted: everything here is checked by Lean. `schedule i` computes, in
each lane of `msg i`, what `xupd` says, and stores the register.
-/

namespace VG.Proof.Sha256.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Sha256.X86_64.Avx2

theorem msg_add4 (n : Nat) : msg (n + 4) = msg n := by
  simp only [msg, Nat.add_mod_right]

/-- The vector registers of `schedule i` are all different. -/
theorem msg_nodup (n : Nat) :
    [msg n, msg (n + 1), msg (n + 2), msg (n + 3), t0, t1, t2, t3, mBA, mDC, mBswap, tmp].Nodup := by
  simp only [msg]
  have := Nat.mod_lt n (show 4 > 0 by omega)
  rw [show (n + 1) % 4 = (n % 4 + 1) % 4 by omega, show (n + 2) % 4 = (n % 4 + 2) % 4 by omega,
    show (n + 3) % 4 = (n % 4 + 3) % 4 by omega]
  generalize n % 4 = c at *
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3) with rfl | rfl | rfl | rfl <;> decide

theorem ea_at (s : State) (b : Reg) (d : Nat) :
    s.ea (at_ b d) = s.gpr b + BitVec.ofInt 64 (d : Int) := rfl

/-- The schedule of words `4i … 4i+3`, from lanes `a, b, c, d` (lane 0) and
`a', b', c', d'` (lane 1) of `msg i … msg (i+3)`. -/
theorem schedule_ok (i : Nat) (s : State) (a b c d a' b' c' d' : BitVec 128)
    (ha : s.xmm (msg i) = a) (hb : s.xmm (msg (i + 1)) = b) (hc : s.xmm (msg (i + 2)) = c)
    (hd : s.xmm (msg (i + 3)) = d) (ha' : s.ymmHi (msg i) = a') (hb' : s.ymmHi (msg (i + 1)) = b')
    (hc' : s.ymmHi (msg (i + 2)) = c') (hd' : s.ymmHi (msg (i + 3)) = d')
    (hBA : s.xmm mBA = maskBA) (hBA' : s.ymmHi mBA = maskBA)
    (hDC : s.xmm mDC = maskDC) (hDC' : s.ymmHi mDC = maskDC)
    (hout : InRegions s.wr (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int)) 32) :
    WP isa (.block (schedule i)) s fun s' =>
      s'.xmm (msg i) = xupd a b c d ∧ s'.ymmHi (msg i) = xupd a' b' c' d' ∧
      (∀ r, r ≠ msg i → r ≠ t0 → r ≠ t1 → r ≠ t2 → r ≠ t3 → s'.xmm r = s.xmm r ∧ s'.ymmHi r = s.ymmHi r) ∧
      s'.gpr = s.gpr ∧
      s'.mem = s.mem.writeW (s.gpr .rcx + BitVec.ofInt 64 ((32 * i : Nat) : Int))
        (xupd a' b' c' d' ++ xupd a b c d) ∧
      s'.rd = s.rd ∧ s'.wr = s.wr := by
  have hn := msg_nodup i
  have hn' := VG.nodup_reverse hn
  apply WP.of_runBlock
  simp only [schedule, vb, vs]
  generalize msg i = x₀ at *
  generalize msg (i + 1) = x₁ at *
  generalize msg (i + 2) = x₂ at *
  generalize msg (i + 3) = x₃ at *
  simp only [t0, t1, t2, t3, mBA, mDC, mBswap, tmp, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, not_or, List.nodup_nil, and_true, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hn hn' hBA hBA' hDC hDC' ⊢
  simp (config := {decide := true}) only [runBlock_cons, runStep_some, runBlock_nil, exec, VOp.exec,
    isa, State.setV, State.lane, State.ymm, State.store256, ea_at, hout, ite_true, ite_false, hn, hn',
    ha, hb, hc, hd, ha', hb', hc', hd', hBA, hBA', hDC, hDC', Option.some.injEq, exists_eq_left']
  refine ⟨rfl, rfl, fun r h0 h1 h2 h3 h4 => by simp [h0, h1, h2, h3, h4], trivial, rfl, trivial⟩

end VG.Proof.Sha256.X86_64.Avx2
