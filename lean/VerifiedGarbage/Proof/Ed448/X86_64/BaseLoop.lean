import VerifiedGarbage.Proof.Ed448.X86_64.BaseStep
import VerifiedGarbage.Proof.Ed448.Group.Projective

/-!
# Ed448 base-point multiplication on x86-64: the loop over the bits

After the bits above `n` (counting down from 456), `R` (slots 0–2)
represents `[k >> n]B`, for `k` the scalar: each iteration doubles it and
adds `B` when the next bit is set (`shift_step`). `Q` (slots 8–10) stays the
base point and slot 11 `d`.
-/

namespace VG.Proof.Ed448.X86_64

open VG VG.X86_64 VG.Impl.Ed448.X86_64 VG.Proof.Ed448 VG.Proof.Ed448.Edwards
open VG.Proof.X448.X86_64 (Scr Index Env E Keep FieldOk off contains_sc mask opSwap clob Outside)
open VG.Impl.X448.X86_64 (BITS slot)

theorem stepEnv_pt (sw : Bool) (e : Env) :
    pt (stepEnv sw e) 0 1 2 =
      if sw then addWith (e 11) (double (pt e 0 1 2)) (pt e 8 9 10) else double (pt e 0 1 2) := by
  cases sw <;> rfl

theorem stepEnv_q (sw : Bool) (e : Env) : pt (stepEnv sw e) 8 9 10 = pt e 8 9 10 := by
  cases sw <;> rfl

theorem stepEnv_d (sw : Bool) (e : Env) : stepEnv sw e 11 = e 11 := by
  cases sw <;> rfl

theorem shift_step (k t : Nat) : k >>> t = 2 * (k >>> (t + 1)) + ((k >>> t) &&& 1) := by
  rw [Nat.shiftRight_succ, Nat.and_one_is_mod]
  omega

/-- One bit: `R` for `[k >> (t + 1)]B` becomes `R` for `[k >> t]B`. -/
theorem rep_step {e : Env} {k t : Nat}
    (hr : Rep (pt e 0 1 2) ((k >>> (t + 1)) • baseAff)) (hq : pt e 8 9 10 = Spec.Ed448.basePoint)
    (hd : e 11 = Spec.Ed448.d) :
    Rep (pt (stepEnv (decide ((k >>> t) &&& 1 = 1)) e) 0 1 2) ((k >>> t) • baseAff) := by
  rw [stepEnv_pt, hd, hq, addWith_d]
  have h2 := double_rep hr
  have hb : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have e1 : (k >>> t) • baseAff = (k >>> (t + 1)) • baseAff + (k >>> (t + 1)) • baseAff +
      ((k >>> t) &&& 1) • baseAff := by
    conv => lhs; rw [shift_step k t]
    rw [add_nsmul, two_mul, add_nsmul]
  rw [e1]
  rcases (by omega : (k >>> t) &&& 1 = 0 ∨ (k >>> t) &&& 1 = 1) with h | h
  · rw [h, zero_nsmul, add_zero, show decide ((0 : Nat) = 1) = false from rfl]
    exact h2
  · rw [h, one_nsmul, show decide ((1 : Nat) = 1) = true from rfl]
    exact pointAdd_rep h2 basePoint_rep

/-- The loop's invariant, after the bits above `n` of `k`. -/
structure MInv (base : Addr) (k : Nat) (s₀ : State) (n : Nat) (s : State) : Prop where
  scr : Scr s base
  rbx : s.gpr .rbx = BitVec.ofNat 64 n
  gpr : ∀ r, r ∉ .rbx :: clob → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  mem : Outside base 64 1584 s₀.mem s.mem
  q : pt (E s.mem base) 8 9 10 = Spec.Ed448.basePoint
  d : E s.mem base 11 = Spec.Ed448.d
  rep : Rep (pt (E s.mem base) 0 1 2) ((k >>> n) • baseAff)

variable {fld : Impl.X448.X86_64.Field} (hf : FieldOk fld)

include hf in
theorem loop_ok {s₀ : State} {base : Addr} {k : Nat}
    (hbits : ∀ t < 456, s₀.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1)) :
    ∀ n, ∀ s, 1 ≤ n → n ≤ 456 → MInv base k s₀ n s →
      WP isa (.loop (.block (step fld)) .ne) s fun s' => MInv base k s₀ 0 s' := by
  intro n s hn1 hn2 hi
  refine WP.loop (M := isa) (Q := fun s' => MInv base k s₀ 0 s')
    (fun m (s : State) => 1 ≤ m ∧ m ≤ 456 ∧ MInv base k s₀ m s) ?_ n s ⟨hn1, hn2, hi⟩
  rintro m s ⟨hm1, hm2, hi⟩
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  have hb2 : (k >>> t) &&& 1 < 2 := Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have hbit : s.mem (off base (BITS + t)) = BitVec.ofNat 8 ((k >>> t) &&& 1) := by
    rw [hi.mem _ (Or.inr (by
      rw [Proof.X448.X86_64.ofs_off' base (by simp only [BITS]; omega)]; simp only [BITS]; omega))]
    exact hbits t (by omega)
  refine WP.mono (step_ok hf hi.scr (by omega) hi.rbx hb2 hbit)
    fun s' ⟨b', z', g', rd', wr', o', e'⟩ => ?_
  have inv : MInv base k s₀ t s' := by
    refine ⟨⟨(g' _ (by decide)).trans hi.scr.rdi, wr' ▸ hi.scr.wr, hi.scr.nowrap⟩, b',
      fun r hr => (g' r hr).trans (hi.gpr r hr), rd'.trans hi.rd, wr'.trans hi.wr,
      hi.mem.trans o', ?_, ?_, ?_⟩
    · rw [e', stepEnv_q]; exact hi.q
    · rw [e', stepEnv_d]; exact hi.d
    · rw [e']; exact rep_step hi.rep hi.q hi.d
  simp only [eval, z', Option.map_some]
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h
    exact .inl ⟨rfl, inv⟩
  · exact .inr ⟨by simp only [decide_eq_false (by omega : ¬t = 0), Bool.not_false], t, by omega,
      h, by omega, inv⟩

end VG.Proof.Ed448.X86_64
