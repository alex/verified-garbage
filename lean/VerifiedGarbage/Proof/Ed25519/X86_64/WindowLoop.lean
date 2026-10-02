import VerifiedGarbage.Proof.Ed25519.X86_64.WindowByte

/-!
# Verification's loops over the bytes of the scalars

Untrusted. Bytes 63 down to 32 hold digits of `k` alone, bytes 31 down to 0
of both scalars; after the loops the accumulator represents `[k]A - [S]B`.
-/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64 VG.Proof.Ed25519 Edwards
open VG.Proof.X25519.X86_64 (off ofs Keeps clob Outside)

variable {fld : Arith} [EdArith fld]

/-- The loops' invariant, with `c` bytes left. -/
structure WinLoop (s₀ : State) (base kp sp : Addr) (A : EPoint dZ) (K S c : Nat) (s : State) : Prop where
  ctx : WinCtx base kp sp A s
  d : env s.mem base 16 = Spec.Ed25519.d
  counter : s.mem.readW (off base 56) 64 = BitVec.ofNat 64 c
  kVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem kp 64) = K
  sVal : Spec.Ed25519.decodeLE (Spec.Ed25519.bytesAt s.mem (off sp 32) 32) = S
  value : Rep (point (env s.mem base) 0 1 2 3) ((K / 256 ^ c) • A + (S / 256 ^ c) • (-baseAff))
  keep : ByteKeep base s₀ s

/-- A byte of `k` alone, from `32 + j + 1` bytes left to `32 + j`. -/
theorem stepA_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (32 + (j + 1)) t) :
    WP isa (byteStepA fld) t fun u => u.zf = some (decide (j = 0)) ∧ WinLoop s₀ base kp sp A K S (32 + j) u := by
  have hS : S < 256 ^ 32 := ht.sVal ▸ decodeLE_lt32 _ _
  refine WP.mono (byteStepA_ok (i := 32 + j) ht.ctx ht.d (by omega) (by omega)
    (by rw [ht.counter]; rfl) hS (by rw [ht.kVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  refine ⟨by rw [uz]; simp, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal] at uv; exact uv, ht.keep.trans uk⟩

/-- A byte of both scalars, from `j + 1` bytes left to `j`. -/
theorem stepB_ok {s₀ t : State} {base kp sp : Addr} {A : EPoint dZ} {K S j : Nat} (hj : j < 32)
    (ht : WinLoop s₀ base kp sp A K S (j + 1) t) :
    WP isa (byteStepAB fld) t fun u => u.zf = some (decide (j = 0)) ∧ WinLoop s₀ base kp sp A K S j u := by
  refine WP.mono (byteStepAB_ok (i := j) ht.ctx ht.d hj ht.counter
    (by rw [ht.kVal, ht.sVal]; exact ht.value)) fun u ⟨uz, uc, ud, uv, uk⟩ => ?_
  exact ⟨uz, ht.ctx.of_byte uk, ud, uc, by rw [uk.bytesK ht.ctx, ht.kVal],
    by rw [uk.bytesS ht.ctx, ht.sVal], by rw [ht.kVal, ht.sVal] at uv; exact uv, ht.keep.trans uk⟩

theorem loopA_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 64 s) :
    WP isa (.loop (byteStepA fld) .ne) s (WinLoop s₀ base kp sp A K S 32) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S (32 + n) t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepA_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

theorem loopB_ok {s₀ s : State} {base kp sp : Addr} {A : EPoint dZ} {K S : Nat}
    (h : WinLoop s₀ base kp sp A K S 32 s) :
    WP isa (.loop (byteStepAB fld) .ne) s (WinLoop s₀ base kp sp A K S 0) := by
  apply WP.loop (fun (n : Nat) (t : State) => WinLoop s₀ base kp sp A K S n t ∧ 0 < n ∧ n ≤ 32)
    (n := 32)
  · intro n t ⟨ht, hn0, hn⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    refine WP.mono (stepB_ok (by omega) ht) fun u ⟨uz, hu⟩ => ?_
    by_cases hj : j = 0
    · subst hj
      exact Or.inl ⟨by simp only [eval, uz, decide_true, Option.map_some, Bool.not_true], hu⟩
    · exact Or.inr ⟨by simp only [eval, uz, decide_eq_false hj, Option.map_some, Bool.not_false],
        j, by omega, hu, by omega, by omega⟩
  · exact ⟨h, by decide, by decide⟩

end VG.Proof.Ed25519.X86_64
