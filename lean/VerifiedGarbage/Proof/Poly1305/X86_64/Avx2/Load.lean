import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Mul

/-!
# Poly1305 on x86-64 with AVX2: loading blocks, `r` and the accumulator

`addGroup` splits the four blocks at `rsi` into limbs (block `k` in lane `k`)
and adds them, with the pad bit, to `H`; `loadR` and `loadH` split `r` and the
accumulator the same way.
-/

namespace VG.Proof.Poly1305.X86_64.Avx2

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx2

def addS : Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 5, addS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

section
variable (E : Env)

theorem addS_0 : ∀ k < 4, (addS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 4, (addS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 4, (addS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_3 : ∀ k < 4, (addS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl
theorem addS_4 : ∀ k < 4, (addS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * k + 1) / 2 ^ 40 ||| E.g .r9)) % 2 ^ 64 := by
  intro k hk; rcases cases4 hk with rfl | rfl | rfl | rfl <;> rfl

end

/-- The words of block `k` of the group at `rsi`. -/
def blo (s : State) (k : Nat) : Nat := (envOf s).m (2 * k)
def bhi (s : State) (k : Nat) : Nat := (envOf s).m (2 * k + 1)

theorem envOf_m_lt (s : State) (j : Nat) : (envOf s).m j < 2 ^ 64 := BitVec.isLt _

theorem or_pad {x : Nat} (hx : x < 2 ^ 24) : (x ||| 0x1000000) = x + 2 ^ 24 := by
  rw [Nat.or_comm, show (0x1000000 : Nat) = 2 ^ 24 * 1 by decide, ← Nat.two_pow_add_eq_or_of_lt hx]
  omega

structure AddPre (s : State) : Prop where
  r9 : s.gpr .r9 = 0x1000000
  ctx : Ctx s
  h : ∀ k < 4, ∀ i < 5, hv s k i < 2 ^ 27

/-- What `addGroup` leaves: block `k`, with its pad bit, added to lane `k`
of `H`, and `Y` as it was. -/
structure AddPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 4, qw s' (yreg i) k = qw s (yreg i) k
  h : ∀ k < 4, Limbs26.val (hv s' k) = Limbs26.val (hv s k) + (blo s k + 2 ^ 64 * bhi s k + 2 ^ 128)
  hb : ∀ k < 4, ∀ i < 5, hv s' k i < 2 ^ 28

theorem addGroup_ok {s : State} (hp : AddPre s) : WP isa (.block addGroup) s (AddPost s) := by
  refine WP.mono (run_ok (fun _ => hp.ctx) addS_eq) fun s' h => ?_
  have H : ∀ k < 4, hv s' k 0 = hv s k 0 + blo s k * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = hv s k 1 + blo s k * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = hv s k 2 + (2 ^ 12 * (bhi s k % 2 ^ 14) + blo s k / 2 ^ 52) ∧
      hv s' k 3 = hv s k 3 + bhi s k * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = hv s k 4 + (bhi s k / 2 ^ 40 + 2 ^ 24) := by
    intro k hk
    have hl := envOf_m_lt s (2 * k)
    have hh := envOf_m_lt s (2 * k + 1)
    have b0 := hp.h k hk 0 (by decide)
    have b1 := hp.h k hk 1 (by decide)
    have b2 := hp.h k hk 2 (by decide)
    have b3 := hp.h k hk 3 (by decide)
    have b4 := hp.h k hk 4 (by decide)
    simp only [hv] at b0 b1 b2 b3 b4 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, addS_0 _ k hk, addS_1 _ k hk,
      addS_2 _ k hk, addS_3 _ k hk, addS_4 _ k hk, envOf_v, envOf_v, envOf_v, envOf_v, envOf_v,
      Limbs26.split_or hl]
    have r9 : (s.gpr .r9).toNat = 0x1000000 := by rw [hp.r9]; rfl
    simp only [envOf, r9, blo, bhi] at hl hh ⊢
    rw [or_pad (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, addS_y i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have := Limbs26.split_val (envOf_m_lt s (2 * k)) (bhi s k)
    rw [Limbs26.split_or (envOf_m_lt s (2 * k))] at this
    simp only [Limbs26.val, e0, e1, e2, e3, e4]
    simp only [blo] at this ⊢
    omega
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have hl := envOf_m_lt s (2 * k)
    have hh := envOf_m_lt s (2 * k + 1)
    have b := hp.h k hk
    simp only [blo, bhi] at e0 e1 e2 e3 e4
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega
    · rw [e1]; have := b 1 (by decide); omega
    · rw [e2]; have := b 2 (by decide); omega
    · rw [e3]; have := b 3 (by decide); omega
    · rw [e4]; have := b 4 (by decide); omega

end VG.Proof.Poly1305.X86_64.Avx2
