import VerifiedGarbage.Proof.Framework.AArch64.VecPreserved
import VerifiedGarbage.Proof.MlKem.AArch64.Reduce
import VerifiedGarbage.Proof.MlKem.Mem
import VerifiedGarbage.Proof.Framework.AArch64.Taint
import VerifiedGarbage.Proof.Framework.Contract
import VerifiedGarbage.Spec.MlKem.Poly

/-!
# ML-KEM on AArch64: what the proofs share

Untrusted: everything here is checked by Lean. Memory of zeros (for the
states that show a precondition satisfiable), the tactic that moves a
proof from a per-target contract to the shared one, and facts about the
registers a function never writes.
-/

namespace VG.Proof.MlKem.AArch64

open VG VG.AArch64
open VG.Spec.MlKem

theorem coeffAt_zero (p : Addr) (i : Nat) : coeffAt (fun _ => 0) p i = 0 := by
  simp only [coeffAt, Mem.readW, Mem.read]
  rfl

/-- A polynomial of zeros is reduced. -/
theorem reduced_zero (p : Addr) : Reduced (fun _ => 0) p := fun i _ => by
  rw [coeffAt_zero]; decide

/-- `k.Implies k'` for `k'` built with `Sig.contract`, as `sig_implies`
proves it, where the satisfying state `w` may have preconditions on
polynomials of zeros (`reduced_zero`). -/
syntax "mlkem_implies " "[" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]"
  " using " term : tactic
macro_rules
  | `(tactic| mlkem_implies [$ls,*] [$ws,*] using $w) => `(tactic| exact
      { pre := by sig_implies_pre [$ls,*]
        post := by sig_implies_post [$ls,*]
        pub := by sig_implies_pub [$ls,*]
        sat := by
          refine ⟨$w, ?_⟩
          sig_pre [$ls,*]
          and_intros
          all_goals first
            | rfl
            | decide
            | exact Region.disjoint_of_sep (by decide)
            | exact reduced_zero _ _ ‹_›
            | exact reduced_zero _
            | (intro a h₁ h₂
               set_option linter.unusedSimpArgs false in
               simp only [Region.Contains, $ws,*] at h₁ h₂
               bv_omega) })

/-- No instruction of `c` (without calls) writes a callee-saved register. -/
theorem preserved_of {c : Prog isa} (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) :
    ∀ r ∈ preserved, ∀ i ∈ instrs c, dstOf i ≠ some r := by
  intro r hr i hi
  have := List.all_eq_true.mp (List.all_eq_true.mp (instrs_keeps h) i hi) r hr
  simpa using this

/-- Code without calls that writes no callee-saved register, and keeps the
stack pointer, meets the calling convention. -/
theorem abi_of {c : Prog isa} (hc : c.noCalls = true)
    (h : c.allInstrs (keeps (RegSet.ofList preserved)) = true) {s s' : State} {t : List Leak}
    (he : Exec isa c s t s') (hv : c.allInstrs keepsV = true := by decide +kernel) : abiPreserved s s' :=
  ⟨fun r hr => Exec.gpr (preserved_of h r hr) he (.inl hc), Exec.sp he, Exec.preservedV he hv⟩

/-- Agreement on the registers `rs` and the stack pointer. -/
theorem agree_of {rs : List Reg} {s₁ s₂ : State} (hsp : s₁.sp = s₂.sp)
    (h : ∀ r ∈ rs, s₁.gpr r = s₂.gpr r) :
    VG.AArch64.Taint.Agree (VG.AArch64.Taint.ofRegs rs) s₁ s₂ :=
  ⟨hsp, fun r hr => h r (VG.AArch64.Taint.mem_ofRegs.mp hr)⟩

/-! ## Outputs written in order -/

theorem addr_ne (p : Addr) {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    p + BitVec.ofNat 64 a ≠ p + BitVec.ofNat 64 b := by
  intro e
  apply h
  bv_omega

/-- Byte `j` after writing byte `c` of the bytes at `p`. -/
theorem write8_at (m : Mem) (p : Addr) {j c : Nat} (hj : j < 2 ^ 64) (hc : c < 2 ^ 64) (b : Byte) :
    m.writeW (p + BitVec.ofNat 64 c) b (p + BitVec.ofNat 64 j) =
      if j = c then b else m (p + BitVec.ofNat 64 j) := by
  rw [writeW8_apply]
  by_cases h : j = c
  · subst h; simp
  · rw [ite_eq_right (addr_ne p hj hc h), ite_eq_right h]

/-- The bytes at `p`: the first `t` of them are `L`'s, the others `old`'s. -/
def BytesUpTo (m : Mem) (p : Addr) (N t : Nat) (L old : Nat → Byte) : Prop :=
  ∀ j < N, m (p + BitVec.ofNat 64 j) = if j < t then L j else old j

theorem BytesUpTo.zero {m : Mem} {p : Addr} {N : Nat} (L : Nat → Byte) :
    BytesUpTo m p N 0 L fun j => m (p + BitVec.ofNat 64 j) := fun j _ => by
  rw [ite_eq_right (Nat.not_lt_zero j)]

/-- Writing byte `t`. -/
theorem BytesUpTo.write {m : Mem} {p : Addr} {N t : Nat} {L old : Nat → Byte}
    (h : BytesUpTo m p N t L old) (hN : N < 2 ^ 64) (ht : t < N) {b : Byte} (hb : b = L t) :
    BytesUpTo (m.writeW (p + BitVec.ofNat 64 t) b) p N (t + 1) L old := fun j hj => by
  rw [write8_at m p (by omega) (by omega)]
  by_cases e : j = t
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hb]
  · rw [ite_eq_right e, h j hj]
    by_cases hjt : j < t
    · rw [ite_eq_left hjt, ite_eq_left (by omega)]
    · rw [ite_eq_right hjt, ite_eq_right (by omega)]

/-- All `N` bytes written. -/
theorem BytesUpTo.eq {m : Mem} {p : Addr} {N : Nat} {L : Nat → Byte} {old : Nat → Byte}
    (h : BytesUpTo m p N N L old) {xs : List Byte} (hl : xs.length = N)
    (hx : ∀ j < N, xs[j]! = L j) : Spec.Sha3.bytesAt m p N = xs :=
  bytesAt_eq! hl fun j hj => by rw [h j hj, ite_eq_left hj, hx j hj]

/-- The coefficients at `p`: the first `t` of them are `G`'s, the others `old`'s. -/
def CoeffsUpTo (m : Mem) (p : Addr) (t : Nat) (G old : Nat → BitVec 32) : Prop :=
  ∀ i < 256, coeffAt m p i = if i < t then G i else old i

theorem CoeffsUpTo.zero {m : Mem} {p : Addr} (G : Nat → BitVec 32) :
    CoeffsUpTo m p 0 G fun i => coeffAt m p i := fun i _ => by
  rw [ite_eq_right (Nat.not_lt_zero i)]

/-- Writing coefficient `t`. -/
theorem CoeffsUpTo.write {m : Mem} {p : Addr} {t : Nat} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p t G old) (ht : t < 256) {v : BitVec 32} (hv : v = G t) :
    CoeffsUpTo (m.writeW (coeffAddr p t) v) p (t + 1) G old := fun i hi => by
  rw [coeffAt_writeW m p (show i < n from hi) (show t < n from ht)]
  by_cases e : t = i
  · subst e; rw [ite_eq_left rfl, ite_eq_left (by omega), hv]
  · rw [ite_eq_right e, h i hi]
    by_cases hit : i < t
    · rw [ite_eq_left hit, ite_eq_left (by omega)]
    · rw [ite_eq_right hit, ite_eq_right (by omega)]

/-- All 256 coefficients written. -/
theorem CoeffsUpTo.polyIs {m : Mem} {p : Addr} {G old : Nat → BitVec 32}
    (h : CoeffsUpTo m p 256 G old) {f : Poly} (hf : ∀ i < 256, G i = BitVec.ofNat 32 (f[i]!).val) :
    PolyIs m p f :=
  polyIs_of_coeffAt fun i hi => by rw [h i hi, ite_eq_left hi, hf i hi]

/-- A coefficient of a polynomial in a region the frame does not write. -/
theorem coeffAt_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr}
    (hd : ∀ r ∈ rs, (polyRegion p).Disjoint r) {i : Nat} (hi : i < 256) :
    coeffAt m' p i = coeffAt m p i :=
  coeffAt_congr (bytes_frame hf hd (by decide)) (show i < n from hi)

/-- A byte of a region the frame does not write. -/
theorem byte_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {p : Addr} {len : Nat}
    (hd : ∀ r ∈ rs, (⟨p, len⟩ : Region).Disjoint r) (hlen : len ≤ 2 ^ 64) {j : Nat} (hj : j < len) :
    m' (p + BitVec.ofNat 64 j) = m (p + BitVec.ofNat 64 j) :=
  bytes_frame hf hd hlen j hj

end VG.Proof.MlKem.AArch64
