import VerifiedGarbage.Proof.Rc2.X86.Stream.UpdateLong

/-!
# Streaming RC2-CBC on x86 (32-bit): everything before the call

Untrusted: everything here is checked by Lean. The state before the call of
the CBC function (`Mid`): the copies done, and its arguments in `eax`,
`ecx`, `edx`, `esi` and `ebx` (`head_ok`).
-/

namespace VG.Proof.Rc2.X86.Stream.Update

open VG VG.X86 VG.X86.Wp VG.Impl.Rc2.X86.Stream

/-- `shr d, n`, and ZF. -/
theorem wp_shrZ {s : State} {is : List Instr} {Q : State → Prop} {d : Reg} {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31)
    (k : ∀ s', Upd s s' d (s.gpr d >>> n) → s'.zf = some (s.gpr d >>> n == 0) → WP isa (.block is) s' Q) :
    WP isa (.block (.shift .shr d n :: is)) s Q :=
  cons (by simp only [exec, execShift, hn, and_self, ite_true]; rfl) (k _ (Upd.setFlags _ _ _ _ _ _ _) rfl)

theorem shr3 (x : BitVec 32) : x >>> 3 = BitVec.ofNat 32 (x.toNat / 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  omega

/-- The state before the call, from the entry state `s₀`. -/
structure Mid (s₀ s : State) : Prop where
  common : Common s₀ s
  ebx : s.gpr .ebx = scr s₀
  eax : s.gpr .eax = ctx s₀
  ecx : s.gpr .ecx = ctx s₀ + 128
  edx : s.gpr .edx = op s₀
  esi : s.gpr .esi = BitVec.ofNat 32 (O s₀ / 8)
  zf : s.zf = some (decide (O s₀ = 0))
  short : O s₀ = 0 →
    Spec.Rc2.bytesAt s.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
      Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀)
  out : O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (oA s₀) (O s₀) =
      Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
        Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀)
  pend : O s₀ ≠ 0 →
    Spec.Rc2.bytesAt s.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
      Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8)

theorem cbcArgs_ok {s₀ s : State} (hp : Pre s₀) (hc : Common s₀ s) {Q : State → Prop}
    (hQ : ∀ t, Common s₀ t → t.mem = s.mem → t.gpr .ebx = scr s₀ → t.gpr .eax = ctx s₀ →
      t.gpr .ecx = ctx s₀ + 128 → t.gpr .edx = op s₀ → t.gpr .esi = BitVec.ofNat 32 (O s₀ / 8) →
      t.zf = some (decide (O s₀ = 0)) → Q t) :
    WP isa (.block cbcArgs) s Q := by
  have hOe := hp.O_eq
  refine wp_arg hp hc (i := 6) (by decide) fun s₁ u₁ => ?_
  have c₁ := hc.upd u₁ (by decide) (by decide) (by decide)
  refine wp_arg hp c₁ (i := 0) (by decide) fun s₂ u₂ => ?_
  have c₂ := c₁.upd u₂ (by decide) (by decide) (by decide)
  refine wp_mov fun s₃ u₃ => ?_
  have c₃ := c₂.upd u₃ (by decide) (by decide) (by decide)
  refine wp_addi fun s₄ u₄ => ?_
  have c₄ := c₃.upd u₄ (by decide) (by decide) (by decide)
  refine wp_arg hp c₄ (i := 4) (by decide) fun s₅ u₅ => ?_
  have c₅ := c₄.upd u₅ (by decide) (by decide) (by decide)
  refine wp_arg hp c₅ (i := 5) (by decide) fun s₆ u₆ => ?_
  have c₆ := c₅.upd u₆ (by decide) (by decide) (by decide)
  refine wp_shrZ ⟨by decide, by decide⟩ fun s₇ u₇ hz₇ => WP.block_nil ?_
  have esi₇ : s₇.gpr .esi = BitVec.ofNat 32 (O s₀ / 8) := by rw [u₇.gpr, u₆.gpr, shr3]
  refine hQ s₇ (c₆.upd u₇ (by decide) (by decide) (by decide))
    (by rw [u₇.mem, u₆.mem, u₅.mem, u₄.mem, u₃.mem, u₂.mem, u₁.mem])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.other _ (by decide), u₁.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.other _ (by decide),
      u₃.other _ (by decide), u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.other _ (by decide), u₄.gpr, u₃.gpr, u₂.gpr])
    (by rw [u₇.other _ (by decide), u₆.other _ (by decide), u₅.gpr]) esi₇ ?_
  have hOlt : O s₀ < 2 ^ 32 := (arg s₀ 5).isLt
  rw [hz₇, ← u₇.gpr, esi₇, ofNat_beq_zero (by omega)]
  exact congrArg some (decide_eq_decide.mpr (by omega))

theorem head_ok {s₀ : State} (hp : Pre s₀) : WP isa head s₀ (Mid s₀) := by
  refine WP.seq (entry_ok hp fun s c f hz => ?_)
  refine WP.seq (WP.mono (Q := fun (t : State) => Common s₀ t ∧
      (O s₀ = 0 → Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀ + len s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (len s₀)) ∧
      (O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (oA s₀) (O s₀) =
        Spec.Rc2.bytesAt s₀.mem (cA s₀ + BitVec.ofNat 64 136) (p s₀) ++
          Spec.Rc2.bytesAt s₀.mem (dA s₀) (O s₀ - p s₀)) ∧
      (O s₀ ≠ 0 → Spec.Rc2.bytesAt t.mem (cA s₀ + BitVec.ofNat 64 136) ((p s₀ + len s₀) % 8) =
        Spec.Rc2.bytesAt s₀.mem (dA s₀ + BitVec.ofNat 64 (O s₀ - p s₀)) ((p s₀ + len s₀) % 8)))
    (WP.ite _ hz (fun h => ?_) (fun h => ?_)) fun t ⟨ct, h₁, h₂, h₃⟩ => cbcArgs_ok hp ct
      fun u cu mu ebx eax ecx edx esi zf =>
        ⟨cu, ebx, eax, ecx, edx, esi, zf, fun h => mu ▸ h₁ h, fun h => mu ▸ h₂ h, fun h => mu ▸ h₃ h⟩)
  · have h0 : O s₀ = 0 := by simpa using h
    exact short_ok hp h0 c f fun s' c' b => ⟨c', fun _ => b, fun h => absurd h0 h, fun h => absurd h0 h⟩
  · have h0 : O s₀ ≠ 0 := by simpa using h
    exact long_ok hp h0 c f fun s' c' b₁ b₂ => ⟨c', fun h => absurd h h0, fun _ => b₁, fun _ => b₂⟩

end VG.Proof.Rc2.X86.Stream.Update
