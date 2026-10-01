import VerifiedGarbage.Proof.Poly1305.X86_64.Avx512.Mul
import VerifiedGarbage.Proof.Poly1305.X86_64.Avx2.Load

/-!
# Poly1305 on x86-64 with AVX-512: loading blocks

Untrusted: everything here is checked by Lean. `addGroup` splits the eight
blocks at `rsi` into limbs (block `π k` in quadword `k`) and adds them, with
the pad bit, to `H`; `addGroupM` likewise, with the pad bit from the state.
-/

namespace VG.Proof.Poly1305.X86_64.Avx512

open VG VG.X86_64 VG.Impl.Poly1305.X86_64.Avx512
open VG.Impl.Poly1305.X86_64.Avx2 (hreg dreg yreg tP)
open VG.Proof.Poly1305.X86_64.Avx2 (xr xi xr_xi vec or_pad)

def addS : Sym := (Sym.init.run true addGroup).get (by decide +kernel)

theorem addS_eq : Sym.init.run true addGroup = some addS := (Option.some_get _).symm

theorem addS_y : ∀ i < 5, addS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

def addMS : Sym := (Sym.init.run true addGroupM).get (by decide +kernel)

theorem addMS_eq : Sym.init.run true addGroupM = some addMS := (Option.some_get _).symm

theorem addMS_y : ∀ i < 5, addMS.reg (xi (yreg i)) = .reg (xi (yreg i)) := by decide +kernel

/-- The block of a group in quadword `k`: blocks `0, 4, 1, 5, 2, 6, 3, 7`. -/
def pi (k : Nat) : Nat := 4 * (k % 2) + k / 2

section
variable (E : Env)

theorem addS_0 : ∀ k < 8, (addS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_1 : ∀ k < 8, (addS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_2 : ∀ k < 8, (addS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_3 : ∀ k < 8, (addS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addS_4 : ∀ k < 8, (addS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * pi k + 1) / 2 ^ 40 ||| E.g .r9)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem addMS_0 : ∀ k < 8, (addMS.reg (xi (hreg 0))).natw E k =
    (E.v (xi (hreg 0)) k + E.m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_1 : ∀ k < 8, (addMS.reg (xi (hreg 1))).natw E k =
    (E.v (xi (hreg 1)) k + E.m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_2 : ∀ k < 8, (addMS.reg (xi (hreg 2))).natw E k =
    (E.v (xi (hreg 2)) k + (E.m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 ||| E.m (2 * pi k) / 2 ^ 52)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_3 : ∀ k < 8, (addMS.reg (xi (hreg 3))).natw E k =
    (E.v (xi (hreg 3)) k + E.m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
theorem addMS_4 : ∀ k < 8, (addMS.reg (xi (hreg 4))).natw E k =
    (E.v (xi (hreg 4)) k + (E.m (2 * pi k + 1) / 2 ^ 40 ||| E.mb 112)) % 2 ^ 64 := by
  intro k hk; rcases cases8 hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end

/-- The words of the block of the group at `rsi` in quadword `k`. -/
def blo (s : State) (k : Nat) : Nat := (envOf s).m (2 * pi k)
def bhi (s : State) (k : Nat) : Nat := (envOf s).m (2 * pi k + 1)

theorem envOf_m_lt (s : State) (j : Nat) : (envOf s).m j < 2 ^ 64 := BitVec.isLt _

structure AddPre (s : State) : Prop where
  r9 : s.gpr .r9 = 0x1000000
  ctx : Ctx s
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27

structure AddMPre (s : State) : Prop where
  pad : (envOf s).mb 112 = 0x1000000
  ctx : Ctx s
  h : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27

/-- What `addGroup` leaves: block `π k`, with its pad bit, added to
quadword `k` of `H`, and `Y` as it was. -/
structure AddPost (s s' : State) : Prop where
  vec : vec s s' = s'
  y : ∀ i < 5, ∀ k < 8, qz s' (yreg i) k = qz s (yreg i) k
  h : ∀ k < 8, Limbs26.val (hv s' k) = Limbs26.val (hv s k) + (blo s k + 2 ^ 64 * bhi s k + 2 ^ 128)
  hb : ∀ k < 8, ∀ i < 5, hv s' k i < 2 ^ 28

/-- `AddPost` from the terms that `addGroup` (with the pad bit `pd`) computes. -/
theorem addPost_of {s s' : State} {σ : Sym} (h : SRel σ s s') (hb : ∀ k < 8, ∀ i < 5, hv s k i < 2 ^ 27)
    {pd : Nat} (hpd : pd = 0x1000000) (hy : ∀ i < 5, σ.reg (xi (yreg i)) = .reg (xi (yreg i)))
    (S0 : ∀ k < 8, (σ.reg (xi (hreg 0))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 0)) k + (envOf s).m (2 * pi k) * 2 ^ 38 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S1 : ∀ k < 8, (σ.reg (xi (hreg 1))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 1)) k + (envOf s).m (2 * pi k) * 2 ^ 12 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S2 : ∀ k < 8, (σ.reg (xi (hreg 2))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 2)) k + ((envOf s).m (2 * pi k + 1) * 2 ^ 50 % 2 ^ 64 / 2 ^ 38 |||
        (envOf s).m (2 * pi k) / 2 ^ 52)) % 2 ^ 64)
    (S3 : ∀ k < 8, (σ.reg (xi (hreg 3))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 3)) k + (envOf s).m (2 * pi k + 1) * 2 ^ 24 % 2 ^ 64 / 2 ^ 38) % 2 ^ 64)
    (S4 : ∀ k < 8, (σ.reg (xi (hreg 4))).natw (envOf s) k =
      ((envOf s).v (xi (hreg 4)) k + ((envOf s).m (2 * pi k + 1) / 2 ^ 40 ||| pd)) % 2 ^ 64) :
    AddPost s s' := by
  have H : ∀ k < 8, hv s' k 0 = hv s k 0 + blo s k * 2 ^ 38 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 1 = hv s k 1 + blo s k * 2 ^ 12 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 2 = hv s k 2 + (2 ^ 12 * (bhi s k % 2 ^ 14) + blo s k / 2 ^ 52) ∧
      hv s' k 3 = hv s k 3 + bhi s k * 2 ^ 24 % 2 ^ 64 / 2 ^ 38 ∧
      hv s' k 4 = hv s k 4 + (bhi s k / 2 ^ 40 + 2 ^ 24) := by
    intro k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b0 := hb k hk 0 (by decide)
    have b1 := hb k hk 1 (by decide)
    have b2 := hb k hk 2 (by decide)
    have b3 := hb k hk 3 (by decide)
    have b4 := hb k hk 4 (by decide)
    simp only [hv] at b0 b1 b2 b3 b4 ⊢
    rw [h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, h.natw _ hk, S0 k hk, S1 k hk,
      S2 k hk, S3 k hk, S4 k hk, envOf_v, envOf_v, envOf_v, envOf_v, envOf_v,
      Limbs26.split_or hl, hpd]
    simp only [envOf, blo, bhi] at hl hh ⊢
    rw [or_pad (by omega)]
    omega
  refine ⟨h.eq, fun i hi k hk => ?_, fun k hk => ?_, fun k hk i hi => ?_⟩
  · rw [h.reg _ k hk, hy i hi]; simp only [Q.eval, xr_xi]
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have := Limbs26.split_val (envOf_m_lt s (2 * pi k)) (bhi s k)
    rw [Limbs26.split_or (envOf_m_lt s (2 * pi k))] at this
    simp only [Limbs26.val, e0, e1, e2, e3, e4]
    simp only [blo] at this ⊢
    omega
  · obtain ⟨e0, e1, e2, e3, e4⟩ := H k hk
    have hl := envOf_m_lt s (2 * pi k)
    have hh := envOf_m_lt s (2 * pi k + 1)
    have b := hb k hk
    simp only [blo, bhi] at e0 e1 e2 e3 e4
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl
    · rw [e0]; have := b 0 (by decide); omega
    · rw [e1]; have := b 1 (by decide); omega
    · rw [e2]; have := b 2 (by decide); omega
    · rw [e3]; have := b 3 (by decide); omega
    · rw [e4]; have := b 4 (by decide); omega

theorem addGroup_ok {s : State} (hp : AddPre s) : WP isa (.block addGroup) s (AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) addS_eq) fun _ h =>
    addPost_of h hp.h (show (envOf s).g .r9 = 0x1000000 by simp only [envOf, hp.r9]; rfl) addS_y
      (addS_0 _) (addS_1 _) (addS_2 _) (addS_3 _) (addS_4 _)

theorem addGroupM_ok {s : State} (hp : AddMPre s) : WP isa (.block addGroupM) s (AddPost s) :=
  WP.mono (run_ok (fun _ => hp.ctx) addMS_eq) fun _ h =>
    addPost_of h hp.h hp.pad addMS_y (addMS_0 _) (addMS_1 _) (addMS_2 _) (addMS_3 _) (addMS_4 _)

end VG.Proof.Poly1305.X86_64.Avx512
