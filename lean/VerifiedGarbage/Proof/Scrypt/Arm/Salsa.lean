import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Impl.Scrypt.Arm.Salsa
import VerifiedGarbage.Proof.Framework.Arm.Contract

/-!
# The Salsa20/8 Core on 32-bit ARM

Untrusted: everything here is checked by Lean. The sixteen words live in
`scratch`, word `k` at `4k`, and `b` keeps the input until the final
addition. Each line of the rounds is proved once, for any indices
(`line_ok`), and the lines are composed by induction.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32; 16])`:
replaces the 64 bytes at `b` by their Salsa20/8 Core.

The code may read and write `b` (in `r0`) and `scratch` (in `r1`; 64 bytes
each, the contents of `scratch` on exit unspecified), which may not overlap
or wrap around the end of the address space. The pointers are public; the
data is secret. -/
def salsaArm : Contract Arm.isa where
  pre s :=
    let b : Region := ⟨State.addr (s.gpr .r0), 64⟩
    let scratch : Region := ⟨State.addr (s.gpr .r1), 64⟩
    s.rd = [] ∧ s.wr = [b, scratch] ∧ b.Disjoint scratch ∧
    (s.gpr .r0).toNat + 64 ≤ 2 ^ 32 ∧ (s.gpr .r1).toNat + 64 ≤ 2 ^ 32
  post s s' := bytesAt s'.mem (State.addr (s.gpr .r0)) 64 =
    salsa (bytesAt s.mem (State.addr (s.gpr .r0)) 64)
  pub s₁ s₂ := s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧ s₁.sp = s₂.sp

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for
`vg_scrypt_blockmix(b = r0, r = r1, y = r2, ry = r3, scratch = [sp])`:
if `ry = r > 0`, writes scryptBlockMix of the `128 r` bytes at `b` to `y`.
The code may read `b` and the stack argument, and read and write `y` and
`scratch` (128 bytes). -/
def blockMixArm : Contract Arm.isa where
  pre s :=
    let r := (s.gpr .r1).toNat
    let b : Region := ⟨State.addr (s.gpr .r0), r * 128⟩
    let y : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), 128⟩
    let args : Region := ⟨stackArgAddr s 0, 4⟩
    s.rd = [b, args] ∧ s.wr = [y, scratch] ∧
    y.Disjoint scratch ∧ b.Disjoint y ∧ b.Disjoint scratch ∧ args.Disjoint y ∧
    args.Disjoint scratch ∧
    (s.gpr .r0).toNat + r * 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 4 ≤ 2 ^ 32 ∧
    s.gpr .r3 = s.gpr .r1 ∧ 0 < r
  post s s' := let r := (s.gpr .r1).toNat
    bytesAt s'.mem (State.addr (s.gpr .r2)) (128 * r) =
      blockMix r (bytesAt s.mem (State.addr (s.gpr .r0)) (128 * r))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0

open VG.Arm in
/-- The contract the proof is written against (and verified callers use); the
artifact's is the shared contract of `Spec/`, which implies it.
32-bit ARM contract for
`vg_scrypt_romix(b = r0, r = r1, v = r2, vlen = r3, scratch = [sp], slen = [sp + 4])`:
if `r > 0`, `vlen = N r` for a power of two `N`, and `slen = r + 2`, replaces
the `128 r` bytes at `b` by their scryptROMix. The code may read the stack
arguments, and read and write `b`, `v` and `scratch`. The indices `j` of
step 3 are public. -/
def roMixArm : Contract Arm.isa where
  pre s :=
    let r := (s.gpr .r1).toNat
    let b : Region := ⟨State.addr (s.gpr .r0), r * 128⟩
    let v : Region := ⟨State.addr (s.gpr .r2), (s.gpr .r3).toNat * 128⟩
    let scratch : Region := ⟨State.addr (stackArg s 0), (stackArg s 1).toNat * 128⟩
    let args : Region := ⟨stackArgAddr s 0, 8⟩
    s.rd = [args] ∧ s.wr = [b, v, scratch] ∧
    b.Disjoint v ∧ b.Disjoint scratch ∧ v.Disjoint scratch ∧
    args.Disjoint b ∧ args.Disjoint v ∧ args.Disjoint scratch ∧
    (s.gpr .r0).toNat + r * 128 ≤ 2 ^ 32 ∧ (s.gpr .r2).toNat + (s.gpr .r3).toNat * 128 ≤ 2 ^ 32 ∧
    (stackArg s 0).toNat + (stackArg s 1).toNat * 128 ≤ 2 ^ 32 ∧ s.sp.toNat + 8 ≤ 2 ^ 32 ∧
    0 < r ∧ (s.gpr .r3).toNat % r = 0 ∧ ((s.gpr .r3).toNat / r).isPowerOfTwo ∧
    (stackArg s 1).toNat = r + 2
  post s s' := let r := (s.gpr .r1).toNat
    bytesAt s'.mem (State.addr (s.gpr .r0)) (128 * r) =
      roMix r ((s.gpr .r3).toNat / r) (bytesAt s.mem (State.addr (s.gpr .r0)) (128 * r))
  pub s₁ s₂ :=
    s₁.sp = s₂.sp ∧ s₁.gpr .r0 = s₂.gpr .r0 ∧ s₁.gpr .r1 = s₂.gpr .r1 ∧
    s₁.gpr .r2 = s₂.gpr .r2 ∧ s₁.gpr .r3 = s₂.gpr .r3 ∧ stackArg s₁ 0 = stackArg s₂ 0 ∧
    stackArg s₁ 1 = stackArg s₂ 1 ∧
    roMixIndices (s₁.gpr .r1).toNat ((s₁.gpr .r3).toNat / (s₁.gpr .r1).toNat)
        (bytesAt s₁.mem (State.addr (s₁.gpr .r0)) (128 * (s₁.gpr .r1).toNat)) =
      roMixIndices (s₂.gpr .r1).toNat ((s₂.gpr .r3).toNat / (s₂.gpr .r1).toNat)
        (bytesAt s₂.mem (State.addr (s₂.gpr .r0)) (128 * (s₂.gpr .r1).toNat))

end VG.Proof.Scrypt

namespace VG.Proof.Scrypt.Arm

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (Word)
open VG.Proof.Scrypt
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str wp_add op2_reg)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Scrypt.Memory (contains_off)

/-! ## The precondition -/

section
variable (s₀ : State)
/-- `b`. -/
abbrev bA : Addr := State.addr (s₀.gpr .r0)
/-- `scratch`. -/
abbrev sA : Addr := State.addr (s₀.gpr .r1)
abbrev bR : Region := ⟨bA s₀, 64⟩
abbrev sR : Region := ⟨sA s₀, 64⟩
/-- The input words. -/
def V : Vector Word 16 := Vector.ofFn fun j => s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j.1)) 32
/-- The result of the rounds. -/
abbrev Rs : Vector Word 16 := Nat.repeat Spec.Scrypt.doubleRound 4 (V s₀)
end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = []
  wr : s₀.wr = [bR s₀, sR s₀]
  disj : (bR s₀).Disjoint (sR s₀)
  b_fit : (s₀.gpr .r0).toNat + 64 ≤ 2 ^ 32
  s_fit : (s₀.gpr .r1).toNat + 64 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : Proof.Scrypt.salsaArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

theorem V_get (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k] = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  simp only [V, Vector.getElem_ofFn]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {a b : α} (h : ¬c) :
    (if c then a else b) = b := by simp [h]

/-- Word `k` of `b` or `scratch`, as an address. -/
theorem addr_word {p : BitVec 32} (hp : p.toNat + 64 ≤ 2 ^ 32) {k : Nat} (hk : k < 16) :
    State.addr (p + BitVec.ofNat 32 (4 * k)) = State.addr p + BitVec.ofNat 64 (4 * k) :=
  addr_add (by omega)

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem in_b {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem in_s {k : Nat} (hk : k < 16) (rs : List Region) :
    InRegions (rs ++ s₀.wr) (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_b {k : Nat} (hk : k < 16) : InRegions s₀.wr (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨bR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

theorem out_s {k : Nat} (hk : k < 16) : InRegions s₀.wr (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 :=
  ⟨sR s₀, by simp [hp.wr], contains_off (by omega) (by omega)⟩

/-- A word of `b` is unchanged by a write to `scratch`. -/
theorem b_scr (m : Mem) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16) :
    (m.writeW (sA s₀ + BitVec.ofNat 64 (4 * k)) v).readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (hp.disj.sep (contains_off (by omega) (by omega))
    (contains_off (by omega) (by omega))) (by decide)

/-- A word of `scratch` is unchanged by a write to `b`. -/
theorem s_b (m : Mem) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16) :
    (m.writeW (bA s₀ + BitVec.ofNat 64 (4 * k)) v).readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (hp.disj.symm.sep (contains_off (by omega) (by omega))
    (contains_off (by omega) (by omega))) (by decide)

end Pre

theorem readW_writeW_word (m : Mem) (p : Addr) (v : Word) {j k : Nat} (hj : j < 16) (hk : k < 16)
    (h : j ≠ k) :
    (m.writeW (p + BitVec.ofNat 64 (4 * k)) v).readW (p + BitVec.ofNat 64 (4 * j)) 32 =
      m.readW (p + BitVec.ofNat 64 (4 * j)) 32 :=
  Mem.readW_writeW_sep (fun _ _ _ => by bv_omega) (by decide)

/-- The registers other than `r2` and `r3`, and the permissions, are those on entry. -/
structure Keep (s₀ s : State) : Prop where
  gpr : ∀ r, r ≠ .r2 → r ≠ .r3 → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp

theorem Keep.upd {s₀ s s' : State} (h : Keep s₀ s) {d : Reg} {v : Word} (u : Upd s s' d v)
    (hd : d = .r2 ∨ d = .r3) : Keep s₀ s' :=
  ⟨fun r h2 h3 => by
    rw [u.other r (by rcases hd with rfl | rfl <;> assumption), h.gpr r h2 h3],
    u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp⟩

theorem Keep.mupd {s₀ s s' : State} (h : Keep s₀ s) {m : Mem} (u : Mupd s s' m) : Keep s₀ s' :=
  ⟨fun r h2 h3 => by rw [u.gpr, h.gpr r h2 h3], u.rd.trans h.rd, u.wr.trans h.wr, u.sp.trans h.sp⟩

section
variable {s₀ : State} (hp : Pre s₀) {s : State} (h : Keep s₀ s)
include hp h

theorem ea_b {k : Nat} (hk : k < 16) :
    State.addr (s.gpr .r0 + BitVec.ofNat 32 (4 * k)) = bA s₀ + BitVec.ofNat 64 (4 * k) := by
  rw [h.gpr _ (by decide) (by decide)]; exact addr_word hp.b_fit hk

theorem ea_s {k : Nat} (hk : k < 16) :
    State.addr (s.gpr .r1 + BitVec.ofNat 32 (4 * k)) = sA s₀ + BitVec.ofNat 64 (4 * k) := by
  rw [h.gpr _ (by decide) (by decide)]; exact addr_word hp.s_fit hk

theorem ld_b {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.rd, h.wr]; exact hp.in_b hk _

theorem ld_s {k : Nat} (hk : k < 16) :
    InRegions (s.rd ++ s.wr) (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.rd, h.wr]; exact hp.in_s hk _

theorem st_b {k : Nat} (hk : k < 16) : InRegions s.wr (bA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.wr]; exact hp.out_b hk

theorem st_s {k : Nat} (hk : k < 16) : InRegions s.wr (sA s₀ + BitVec.ofNat 64 (4 * k)) 4 := by
  rw [h.wr]; exact hp.out_s hk

end

/-! ## Copying the input -/

/-- After copying `n` words: `b` is as on entry, and its first `n` words are
in `scratch`. -/
structure CI (s₀ : State) (n : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  b : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!
  copied : ∀ j < 16, j < n → s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!

theorem V_get! (s₀ : State) {k : Nat} (hk : k < 16) :
    (V s₀)[k]! = s₀.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * k)) 32 := by
  rw [getElem!_pos (V s₀) k hk, V_get _ hk]

theorem copy_step {s₀ : State} (hp : Pre s₀) {n : Nat} (hn : n < 16) {s : State} (h : CI s₀ n s) :
    WP isa (.block (copyWord n)) s (CI s₀ (n + 1)) := by
  refine wp_ldr (by omega) (ea_b hp h.keep hn) (ld_b hp h.keep hn) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁ (.inl rfl)
  refine wp_str (by omega) (ea_s hp k₁ hn) (st_s hp k₁ hn) fun s₂ u₂ => WP.block_nil ?_
  have hv : s₁.gpr .r2 = (V s₀)[n]! := by rw [u₁.gpr, h.b n hn]
  refine ⟨k₁.mupd u₂, fun j hj => ?_, fun j hj hjn => ?_⟩
  · rw [u₂.mem, hp.b_scr _ _ hj hn, u₁.mem, h.b j hj]
  · rw [u₂.mem, hv, u₁.mem]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hjn with hjn | rfl
    · rw [readW_writeW_word _ _ _ hj hn (by omega), h.copied j hj hjn]
    · exact Mem.readW_writeW_self32 _ _ _

/-! ## The rounds -/

/-- The words `v` are in `scratch`, and `b` is as on entry. -/
structure RI (s₀ : State) (v : Vector Word 16) (s : State) : Prop where
  keep : Keep s₀ s
  b : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (V s₀)[j]!
  holds : ∀ j < 16, s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = v[j]!

theorem op2_ror {s : State} {r : Reg} {n : Nat} (h : 1 ≤ n ∧ n ≤ 31) :
    (Op2.shifted r .ror n).eval s = some ((s.gpr r).rotateRight n) := by
  simp [Op2.eval, h]

/-- The side conditions of `line_ok`, decidable for concrete arguments. -/
def LSide (i j k n : Nat) : Bool :=
  decide (i < 16 ∧ j < 16 ∧ k < 16 ∧ 1 ≤ n ∧ n ≤ 31 ∧ 4 * i < 4096)

theorem stepN_get! (x : Vector Word 16) {i j k : Nat} (n : Nat) (hi : i < 16) (hj : j < 16)
    (hk : k < 16) (m : Nat) (hm : m < 16) :
    (stepN x i j k n)[m]! = if i = m then x[i]! ^^^ (x[j]! + x[k]!).rotateLeft n else x[m]! := by
  rw [getElem!_pos _ m hm, getElem!_pos _ i hi, getElem!_pos _ j hj, getElem!_pos _ k hk,
    getElem!_pos _ m hm, stepN_get x n hi hj hk m hm]

theorem line_ok {i j k n : Nat} (hs : LSide i j k n = true) {s₀ : State} (hp : Pre s₀)
    {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    WP isa (.block (line i j k n)) s (RI s₀ (stepN v i j k n)) := by
  simp only [LSide, decide_eq_true_eq] at hs
  obtain ⟨hi, hj, hk, h1, h2, -⟩ := hs
  unfold line
  refine wp_ldr (by omega) (ea_s hp h.keep hj) (ld_s hp h.keep hj) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁ (.inl rfl)
  refine wp_ldr (by omega) (ea_s hp k₁ hk) (ld_s hp k₁ hk) fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂ (.inr rfl)
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ := k₂.upd u₃ (.inl rfl)
  refine wp_ldr (by omega) (ea_s hp k₃ hi) (ld_s hp k₃ hi) fun s₄ u₄ => ?_
  have k₄ := k₃.upd u₄ (.inr rfl)
  refine wp_eor (op2_ror (by omega)) fun s₅ u₅ => ?_
  have k₅ := k₄.upd u₅ (.inr rfl)
  refine wp_str (by omega) (ea_s hp k₅ hi) (st_s hp k₅ hi) fun s₆ u₆ => WP.block_nil ?_
  have m₄ : s₄.mem = s.mem := by rw [u₄.mem, u₃.mem, u₂.mem, u₁.mem]
  have e2 : s₄.gpr .r2 = v[j]! + v[k]! := by
    rw [u₄.other _ (by decide), u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem,
      h.holds j hj, h.holds k hk]
  have e3 : s₅.gpr .r3 = v[i]! ^^^ (v[j]! + v[k]!).rotateLeft n := by
    rw [u₅.gpr, u₄.gpr, e2, u₃.mem, u₂.mem, u₁.mem, h.holds i hi, rotateLeft_eq _ (by omega) (by omega)]
  refine ⟨k₅.mupd u₆, fun m hm => ?_, fun m hm => ?_⟩
  · rw [u₆.mem, hp.b_scr _ _ hm hi, u₅.mem, m₄, h.b m hm]
  · rw [u₆.mem, u₅.mem, m₄, e3, stepN_get! v n hi hj hk m hm]
    by_cases e : i = m
    · subst e
      rw [ite_pos' rfl]
      exact Mem.readW_writeW_self32 _ _ _
    · rw [ite_neg' e, readW_writeW_word _ _ _ hm hi (Ne.symm e), h.holds m hm]

theorem lines_ok {s₀ : State} (hp : Pre s₀) :
    ∀ (l : List (Nat × Nat × Nat × Nat)), (l.all fun (i, j, k, n) => LSide i j k n) = true →
      ∀ (v : Vector Word 16) (s : State), RI s₀ v s →
      WP isa (.block (l.flatMap fun (i, j, k, n) => line i j k n)) s
        (RI s₀ (l.foldl (fun x (i, j, k, n) => stepN x i j k n) v))
  | [], _, _, _, h => WP.block_nil h
  | (i, j, k, n) :: l, hl, v, s, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hl
    rw [List.flatMap_cons, WP.block_append_iff, List.foldl_cons]
    exact WP.mono (line_ok hl.1 hp h) fun s' h' => lines_ok hp l hl.2 _ s' h'

theorem doubleRound_eq (v : Vector Word 16) : Spec.Scrypt.doubleRound v =
    lines.foldl (fun x (i, j, k, n) => stepN x i j k n) v := rfl

theorem doubleRound_ok {s₀ : State} (hp : Pre s₀) {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    WP isa doubleRound s (RI s₀ (Spec.Scrypt.doubleRound v)) := by
  rw [doubleRound_eq]
  exact lines_ok hp lines (by decide) v s h

theorem rounds_ok {s₀ : State} (hp : Pre s₀) {v : Vector Word 16} {s : State} (h : RI s₀ v s) :
    ∀ n, WP isa (rounds n) s (RI s₀ (Nat.repeat Spec.Scrypt.doubleRound n v))
  | 0 => WP.block_nil h
  | n + 1 => WP.seq (WP.mono (rounds_ok hp h n) fun _ h' => doubleRound_ok hp h')

/-! ## Adding the input -/

/-- After finishing words `0 … i - 1`: those words of `b` hold the sums,
the others still hold the input, and `scratch` holds the rounds' result. -/
structure FI (s₀ : State) (R : Vector Word 16) (i : Nat) (s : State) : Prop where
  keep : Keep s₀ s
  out : ∀ j < 16, s.mem.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 =
    if j < i then R[j]! + (V s₀)[j]! else (V s₀)[j]!
  scr : ∀ j < 16, s.mem.readW (sA s₀ + BitVec.ofNat 64 (4 * j)) 32 = R[j]!

theorem finish_step {s₀ : State} (hp : Pre s₀) {R : Vector Word 16} {i : Nat} (hi : i < 16)
    {s : State} (h : FI s₀ R i s) : WP isa (.block (finishWord i)) s (FI s₀ R (i + 1)) := by
  unfold finishWord
  refine wp_ldr (by omega) (ea_s hp h.keep hi) (ld_s hp h.keep hi) fun s₁ u₁ => ?_
  have k₁ := h.keep.upd u₁ (.inl rfl)
  refine wp_ldr (by omega) (ea_b hp k₁ hi) (ld_b hp k₁ hi) fun s₂ u₂ => ?_
  have k₂ := k₁.upd u₂ (.inr rfl)
  refine wp_add (op2_reg _ _) fun s₃ u₃ => ?_
  have k₃ := k₂.upd u₃ (.inl rfl)
  refine wp_str (by omega) (ea_b hp k₃ hi) (st_b hp k₃ hi) fun s₄ u₄ => WP.block_nil ?_
  have m₃ : s₃.mem = s.mem := by rw [u₃.mem, u₂.mem, u₁.mem]
  have e2 : s₃.gpr .r2 = R[i]! + (V s₀)[i]! := by
    rw [u₃.gpr, u₂.other _ (by decide), u₁.gpr, u₂.gpr, u₁.mem, h.scr i hi, h.out i hi,
      ite_neg' (Nat.lt_irrefl i)]
  refine ⟨k₃.mupd u₄, fun j hj => ?_, fun j hj => ?_⟩
  · rw [u₄.mem, m₃, e2]
    by_cases e : j = i
    · subst e
      rw [Mem.readW_writeW_self32, ite_pos' (Nat.lt_succ_self j)]
    · rw [readW_writeW_word _ _ _ hj hi e, h.out j hj]
      by_cases hji : j < i
      · rw [ite_pos' hji, ite_pos' (by omega)]
      · rw [ite_neg' hji, ite_neg' (by omega)]
  · rw [u₄.mem, m₃, hp.s_b _ _ hj hi, h.scr j hj]

/-! ## The whole function -/

/-- The input words are those the specification reads from the bytes. -/
theorem input_eq (s₀ : State) :
    (Vector.ofFn fun j : Fin 16 => Spec.Scrypt.wordLE (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) j.1) =
      V s₀ := by
  apply Vector.ext
  intro j hj
  rw [Vector.getElem_ofFn, V_get _ hj, wordLE_bytesAt _ _ (by omega)]

/-- The result words are where the specification writes its bytes. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ j < 16, m.readW (bA s₀ + BitVec.ofNat 64 (4 * j)) 32 = (Rs s₀)[j]! + (V s₀)[j]!) :
    Spec.Scrypt.bytesAt m (bA s₀) 64 = Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64) := by
  rw [Spec.Scrypt.salsa, input_eq]
  refine bytesAt_eq_serialize _ _ _ fun j hj => ?_
  rw [Spec.Scrypt.core, Vector.getElem_zipWith, h j hj, getElem!_pos _ j hj, getElem!_pos _ j hj]

theorem correct {s₀ : State} (hp : Pre s₀) :
    WP isa salsa s₀ fun s' =>
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) ∧ Proof.Scrypt.salsaArm.post s₀ s' := by
  have k₀ : Keep s₀ s₀ := ⟨fun _ _ _ => rfl, rfl, rfl, rfl⟩
  have hc₀ : CI s₀ 0 s₀ := ⟨k₀, fun j hj => (V_get! _ hj).symm, fun _ _ h => absurd h (by omega)⟩
  have hcopy : WP isa (.block copy) s₀ (CI s₀ 16) := by
    unfold copy
    exact wp_range_flatMap (M := isa) (CI s₀) (fun k s hk h => copy_step hp hk h) 16 (Nat.le_refl _) s₀ hc₀
  refine WP.seq (WP.mono hcopy fun s₁ h₁ => ?_)
  have hr₁ : RI s₀ (V s₀) s₁ := ⟨h₁.keep, h₁.b, fun j hj => h₁.copied j hj hj⟩
  refine WP.seq (WP.mono (rounds_ok hp hr₁ 4) fun s₂ h₂ => ?_)
  have hF₀ : FI s₀ (Rs s₀) 0 s₂ :=
    ⟨h₂.keep, fun j hj => by rw [ite_neg' (Nat.not_lt_zero j), h₂.b j hj], h₂.holds⟩
  unfold finish
  refine WP.mono (wp_range_flatMap (M := isa) (FI s₀ (Rs s₀)) (fun i s hi h => finish_step hp hi h)
    16 (Nat.le_refl _) s₂ hF₀) fun s' hF => ⟨fun r hr => ?_, ?_⟩
  · refine hF.keep.gpr r ?_ ?_ <;> rintro rfl <;> simp [preserved] at hr
  · show Spec.Scrypt.bytesAt s'.mem (bA s₀) 64 =
      Spec.Scrypt.salsa (Spec.Scrypt.bytesAt s₀.mem (bA s₀) 64)
    exact post_of fun j hj => by rw [hF.out j hj, ite_pos' hj]

/-- A state satisfying the precondition. -/
def satState : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 0x2000 | _ => 0
  sp := 0x4000
  n := false
  z := false
  c := false
  v := false
  mem _ := 0
  rd := []
  wr := [⟨0x1000, 64⟩, ⟨0x2000, 64⟩]

theorem salsa_correct (s : State) (hs : Proof.Scrypt.salsaArm.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.Arm.salsa s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.salsaArm.post s s' := by
  obtain ⟨t, s', he, h₁, h₂⟩ := correct (pre_of s hs)
  exact ⟨t, s', he, ⟨h₁, Exec.sp he⟩, h₂⟩

theorem salsa_ct : ConstantTime isa Proof.Scrypt.salsaArm.pre Proof.Scrypt.salsaArm.pub
    Impl.Scrypt.Arm.salsa := by
  refine VG.Taint.constantTime (A := taint) (Taint.ofRegs [.r0, .r1]) ?_ (by taint_decide)
  intro s₁ s₂ _ _ ⟨h1, h2, _⟩
  refine Taint.agree_ofRegs fun r hr => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> assumption

theorem salsa_verified :
    Verified Arm.target Impl.Scrypt.Arm.salsa (Spec.Scrypt.salsaContract Arm.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, Proof.Scrypt.salsaArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.Scrypt.Arm.satState]
      using Proof.Scrypt.Arm.satState)

end VG.Proof.Scrypt.Arm
