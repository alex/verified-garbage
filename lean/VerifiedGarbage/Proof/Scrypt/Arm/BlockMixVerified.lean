import VerifiedGarbage.Proof.Scrypt.BlockMix
import VerifiedGarbage.Proof.Scrypt.Spec
import VerifiedGarbage.Spec.Scrypt.Contract
import VerifiedGarbage.TCB.Arm.Target
import VerifiedGarbage.Proof.Scrypt.Memory
import VerifiedGarbage.Proof.Framework.Range
import VerifiedGarbage.Proof.Hmac.Arm.Init
import VerifiedGarbage.Impl.Scrypt.Arm.Salsa
import VerifiedGarbage.Proof.Framework.Arm.Contract
import VerifiedGarbage.Proof.Framework.Arm.RelCT
import VerifiedGarbage.Impl.Scrypt.Arm.BlockMix

/-!
# The Salsa20/8 Core on 32-bit ARM

The sixteen words live in `scratch`, word `k` at `4k`, and `b` keeps the input
until the final addition. Each line of the rounds is proved once, for any
indices (`line_ok`), and the lines are composed by induction.
-/

namespace VG.Proof.Scrypt

open Spec.Scrypt

open VG.Arm in
/-- 32-bit ARM contract for `vg_salsa20_8(b: *mut [u8; 64], scratch: *mut [u32;
16])`: replaces the 64 bytes at `b` by their Salsa20/8 Core.

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
/-- 32-bit ARM contract for `vg_scrypt_blockmix(b = r0, r = r1, y = r2, ry =
r3, scratch = [sp])`: if `ry = r > 0`, writes scryptBlockMix of the `128 r`
bytes at `b` to `y`. The code may read `b` and the stack argument, and read
and write `y` and `scratch` (128 bytes). -/
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
/-- 32-bit ARM contract for `vg_scrypt_romix(b = r0, r = r1, v = r2, vlen = r3,
scratch = [sp], slen = [sp + 4])`: if `r > 0`, `vlen = N r` for a power of two
`N`, and `slen = r + 2`, replaces the `128 r` bytes at `b` by their scryptROMix.
The code may read the stack arguments, and read and write `b`, `v` and
`scratch`. The indices `j` of step 3 are public. -/
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
    rw [u.other r (by rcases hd with rfl | rfl <;> with_reducible assumption), h.gpr r h2 h3],
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
  rcases hr with rfl | rfl <;> with_reducible assumption

theorem salsa_verified :
    Verified Arm.target Impl.Scrypt.Arm.salsa (Spec.Scrypt.salsaContract Arm.abi) :=
  Verified.of_correct salsa_correct salsa_ct (by
    sig_implies [Spec.Scrypt.salsaContract, Spec.Scrypt.salsaSig, Proof.Scrypt.salsaArm, Arm.abi,
      Arm.argRegs, Arm.reduceClassify, Arm.Loc.val, Arm.State.addr] [Proof.Scrypt.Arm.satState]
      using Proof.Scrypt.Arm.satState)

end VG.Proof.Scrypt.Arm

/-!
# scrypt on 32-bit ARM: common lemmas

The target-independent lemmas about addresses and bytes are in
`Proof/Scrypt/Memory.lean`; here are 32-bit pointers as addresses, and the
64-byte exclusive-or.
-/

namespace VG.Proof.Scrypt.Arm

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_append writeBytes_nil writeBytes_frame)
open VG.Proof.MdStream.Arm (Upd Mupd wp_ldr wp_str op2_reg saveMem)
open VG.Proof.Hmac.Arm.Init (wp_eor)
open VG.Proof.Scrypt.Memory (sub_off xorBytes_length bytesAt_length bytesAt_add
  bytesAt_writeBytes_sep)

/-! ## 32-bit pointers -/

theorem addr_toNat (a : BitVec 32) : (State.addr a).toNat = a.toNat := by
  simp only [State.addr, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (by have := a.isLt; omega)

theorem toNat_add32 {p : BitVec 32} {o : Nat} (h : p.toNat + o < 2 ^ 32) :
    (p + BitVec.ofNat 32 o).toNat = p.toNat + o := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega),
    Nat.mod_eq_of_lt h]

theorem add32 (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + BitVec.ofNat 32 j = p + BitVec.ofNat 32 (o + j) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

/-- A pointer plus two offsets, as an address. -/
theorem addr_add2 {p : BitVec 32} {o j : Nat} (h : p.toNat + o + j < 2 ^ 32) :
    State.addr (p + BitVec.ofNat 32 o + BitVec.ofNat 32 j) =
      State.addr p + BitVec.ofNat 64 o + BitVec.ofNat 64 j := by
  rw [add32, addr_add (by omega), BitVec.add_assoc, ← BitVec.ofNat_add]

theorem sub32 (p : BitVec 32) {o : Nat} (h : 64 ≤ o) :
    p + BitVec.ofNat 32 o - 64 = p + BitVec.ofNat 32 (o - 64) := by
  rw [show o = (o - 64) + 64 by omega, BitVec.ofNat_add, ← BitVec.add_assoc, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem shl32 {x : BitVec 32} {n : Nat} (h : x.toNat * 2 ^ n < 2 ^ 32) :
    x <<< n = BitVec.ofNat 32 (x.toNat * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mod_eq_of_lt h]

/-- A register plus a small constant, as the code writes it. -/
theorem add32_lit (p : BitVec 32) (o j : Nat) :
    p + BitVec.ofNat 32 o + (OfNat.ofNat j : BitVec 32) =
      p + BitVec.ofNat 32 (o + (OfNat.ofNat j : Nat)) :=
  add32 p o j

theorem ofNat_pred32 {k : Nat} (h : 1 ≤ k) :
    BitVec.ofNat 32 k - 1 = BitVec.ofNat 32 (k - 1) := by
  rw [show k = (k - 1) + 1 by omega, BitVec.ofNat_add, Nat.add_sub_cancel]
  exact BitVec.add_sub_cancel _ _

theorem ofNat_toNat32 (x : BitVec 32) : x = BitVec.ofNat 32 x.toNat := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Words of bytes -/

theorem writeW_xor32 (m m' : Mem) (d a b : Addr) :
    m.writeW d (m'.readW a 32 ^^^ m'.readW b 32) =
      writeBytes m d (xorBytes (bytesAt m' a 4) (bytesAt m' b 4)) := by
  simp only [Mem.writeW, Mem.readW]
  rw [show (32 : Nat) / 8 = 4 from rfl, BitVec.setWidth_eq, BitVec.setWidth_eq, BitVec.setWidth_eq,
    Proof.Sha256.Stream.write_eq_writeBytes]
  congr 1
  apply List.ext_getElem (by simp [xorBytes, bytesAt])
  intro j h₁ h₂
  simp only [List.length_map, List.length_range] at h₁
  simp only [xorBytes, bytesAt, List.getElem_map, List.getElem_range, List.getElem_zipWith]
  rw [BitVec.extractLsb'_xor, Proof.Hmac.Common.extractLsb'_read _ _ h₁,
    Proof.Hmac.Common.extractLsb'_read _ _ h₁]

/-! ## The 64-byte exclusive-or -/

/-- The first `n` words of `[dst] ← [x] xor [src]`, for 64-byte blocks at
`d`, `x`, `y`, where `d` overlaps neither of the others. The code uses `r2`
and `r3`. -/
theorem xor64_ok {dR xR sR : Reg} (hd : dR ≠ .r2 ∧ dR ≠ .r3) (hx : xR ≠ .r2 ∧ xR ≠ .r3)
    (hs : sR ≠ .r2 ∧ sR ≠ .r3) {d x y : BitVec 32} (fd : d.toNat + 64 ≤ 2 ^ 32)
    (fx : x.toNat + 64 ≤ 2 ^ 32) (fy : y.toNat + 64 ≤ 2 ^ 32)
    (hdx : Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr x, 64⟩)
    (hdy : Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr y, 64⟩) :
    ∀ n ≤ 16, ∀ (rest : List Instr) (s : State) (Q : State → Prop),
    s.gpr dR = d → s.gpr xR = x → s.gpr sR = y →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions (s.rd ++ s.wr) (State.addr y + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ k < 16, InRegions s.wr (State.addr d + BitVec.ofNat 64 (4 * k)) 4) →
    (∀ s', (∀ r, r ≠ .r2 → r ≠ .r3 → s'.gpr r = s.gpr r) → s'.rd = s.rd → s'.wr = s.wr →
      s'.sp = s.sp →
      s'.mem = writeBytes s.mem (State.addr d)
        (xorBytes (bytesAt s.mem (State.addr x) (4 * n)) (bytesAt s.mem (State.addr y) (4 * n))) →
      WP isa (.block rest) s' Q) →
    WP isa (.block ((List.range n).flatMap (xorW dR xR sR) ++ rest)) s Q := by
  intro n
  induction n with
  | zero =>
    intro _ rest s Q _ _ _ _ _ _ k
    exact k s (fun _ _ _ => rfl) rfl rfl rfl (by simp [bytesAt, xorBytes, writeBytes_nil])
  | succ n ih =>
    intro hn rest s Q gd gx gy hinx hiny hout k
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.append_assoc]
    refine ih (by omega) _ s Q gd gx gy hinx hiny hout fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => ?_
    simp only [xorW, List.cons_append, List.nil_append]
    refine wp_ldr (a := State.addr x + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [g₁ _ hx.1 hx.2, gx, addr_add (by omega)]) (by rw [rd₁, wr₁]; exact hinx n (by omega))
      fun s₂ u₂ => ?_
    refine wp_ldr (a := State.addr y + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₂.other _ hs.1, g₁ _ hs.1 hs.2, gy, addr_add (by omega)])
      (by rw [u₂.rd, u₂.wr, rd₁, wr₁]; exact hiny n (by omega)) fun s₃ u₃ => ?_
    refine wp_eor (op2_reg _ _) fun s₄ u₄ => ?_
    refine wp_str (a := State.addr d + BitVec.ofNat 64 (4 * n)) (by omega)
      (by rw [u₄.other _ hd.1, u₃.other _ hd.2, u₂.other _ hd.1, g₁ _ hd.1 hd.2, gd,
        addr_add (by omega)])
      (by rw [u₄.wr, u₃.wr, u₂.wr, wr₁]; exact hout n (by omega))
      fun s₅ u₅ => k s₅ (fun r h2 h3 => by
          rw [u₅.gpr, u₄.other r h2, u₃.other r h3, u₂.other r h2, g₁ r h2 h3])
        (by rw [u₅.rd, u₄.rd, u₃.rd, u₂.rd, rd₁]) (by rw [u₅.wr, u₄.wr, u₃.wr, u₂.wr, wr₁])
        (by rw [u₅.sp, u₄.sp, u₃.sp, u₂.sp, sp₁]) ?_
    have hl : (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
        (bytesAt s.mem (State.addr y) (4 * n))).length = 4 * n := by
      rw [xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]
    have sx : Region.Disjoint ⟨State.addr x + BitVec.ofNat 64 (4 * n), 4⟩
        ⟨State.addr d, (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
          (bytesAt s.mem (State.addr y) (4 * n))).length⟩ := by
      rw [hl]; exact (hdx.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    have sy : Region.Disjoint ⟨State.addr y + BitVec.ofNat 64 (4 * n), 4⟩
        ⟨State.addr d, (xorBytes (bytesAt s.mem (State.addr x) (4 * n))
          (bytesAt s.mem (State.addr y) (4 * n))).length⟩ := by
      rw [hl]; exact (hdy.symm.sub_left (sub_off (by omega) (by omega))).sub_right
        (Region.sub_prefix (by omega))
    rw [u₅.mem, u₄.gpr, u₄.mem, u₃.gpr, u₃.other _ (by decide), u₂.gpr, u₃.mem, u₂.mem, writeW_xor32,
      m₁, bytesAt_writeBytes_sep _ _ sx (by omega), bytesAt_writeBytes_sep _ _ sy (by omega)]
    have e := writeBytes_append s.mem (State.addr d) _
      (xorBytes (bytesAt s.mem (State.addr x + BitVec.ofNat 64 (4 * n)) 4)
        (bytesAt s.mem (State.addr y + BitVec.ofNat 64 (4 * n)) 4))
      (by rw [hl, xorBytes_length _ _ (by simp [bytesAt]), bytesAt_length]; omega)
    rw [hl] at e
    rw [e, Nat.mul_succ, bytesAt_add, bytesAt_add, xorBytes, xorBytes, xorBytes,
      List.zipWith_append (by simp [bytesAt])]

/-! ## Saving and restoring our caller's registers -/

/-- The stores of `saveMem` stay in `R`. -/
theorem saveMem_frame' {R : Region} {B : Addr} (g : Reg → BitVec 32) :
    ∀ (l : List (Reg × Nat)) (m : Mem), (∀ p ∈ l, R.Contains (B + BitVec.ofNat 64 p.2) 4) →
      Frame [R] m (saveMem m B g l) := by
  intro l
  induction l with
  | nil => intro m _; exact Frame.refl _ _
  | cons p l ih =>
    intro m hl
    exact ((Frame.refl _ _).writeW (List.mem_singleton_self _) _ (hl p (by simp))).trans
      (ih _ fun q hq => hl q (List.mem_cons_of_mem _ hq))

/-- Loading the registers `l` through the pointer in `b`, which none of them is. -/
theorem restoreList_ok {b : Reg} {rest : List Instr} (l : List (Reg × Nat)) :
    ∀ (s : State) (Q : State → Prop), (l.map Prod.fst).Nodup →
    (∀ p ∈ l, p.1 ≠ b ∧ p.2 < 4096 ∧ (s.gpr b).toNat + p.2 < 2 ^ 32 ∧
      InRegions (s.rd ++ s.wr) (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 4) →
    (∀ s', (∀ p ∈ l, s'.gpr p.1 = s.mem.readW (State.addr (s.gpr b) + BitVec.ofNat 64 p.2) 32) →
      (∀ r, r ∉ l.map Prod.fst → s'.gpr r = s.gpr r) → s'.mem = s.mem → s'.rd = s.rd →
      s'.wr = s.wr → s'.sp = s.sp → WP isa (.block rest) s' Q) →
    WP isa (.block (l.map (fun p => Instr.ldr p.1 b p.2) ++ rest)) s Q := by
  induction l with
  | nil => intro s Q _ _ k; exact k s (fun _ h => by cases h) (fun _ _ => rfl) rfl rfl rfl rfl
  | cons p l ih =>
    intro s Q hnd hl k
    obtain ⟨h0, h1, h2, h3⟩ := hl p (by simp)
    simp only [List.map_cons, List.nodup_cons] at hnd
    refine wp_ldr h1 (addr_add h2) h3 fun s₁ u₁ => ?_
    have eb : s₁.gpr b = s.gpr b := u₁.other _ (Ne.symm h0)
    refine ih s₁ Q hnd.2 (fun q hq => ?_) fun s' hl' ho hm hrd hwr hsp => k s' (fun q hq => ?_)
      (fun r hr => ?_) (hm.trans u₁.mem) (hrd.trans u₁.rd) (hwr.trans u₁.wr) (hsp.trans u₁.sp)
    · rw [eb, u₁.rd, u₁.wr]; exact hl q (List.mem_cons_of_mem _ hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [ho _ hnd.1, u₁.gpr]
      · rw [hl' q hq, u₁.mem, eb]
    · simp only [List.map_cons, List.mem_cons, not_or] at hr
      rw [ho r hr.2, u₁.other r hr.1]

end VG.Proof.Scrypt.Arm

/-!
# scryptBlockMix on 32-bit ARM: the loop

As on AArch64 (`Proof/Scrypt/AArch64/BlockMixVerified.lean`), the calls of
`vg_salsa20_8` are used through `SalsaSpec`, what its proof says about a call;
the proof of this file holds for any code meeting it. Registers hold 32-bit
pointers, and memory is addressed by their zero extensions (`State.addr`), which
do not wrap.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blk salsa)
open VG.Spec.Pbkdf2 (xorBytes)
open VG.Proof.Scrypt (yAt xBefore yAt_eq xBefore_succ)
open VG.Proof.Sha256.Stream (writeBytes writeBytes_frame)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add op2_reg op2_imm)
open VG.Proof.Scrypt.Memory (toNat_ofNat_lt add_ofNat contains_off sub_off disj_off InRegions.of_mem
  frame_bytesAt bytesAt_writeBytes_self xorBytes_length bytesAt_length blk_bytesAt)

/-! ## What a call of `vg_salsa20_8` does -/

/-- A call of `c` replaces the 64 bytes at `r0` by their Salsa20/8 Core,
with the 64 bytes at `r1` as working space. -/
def SalsaSpec (c : Prog isa) : Prop :=
  ∀ (s : State) (d sc : BitVec 32), s.gpr .r0 = d → s.gpr .r1 = sc →
    d.toNat + 64 ≤ 2 ^ 32 → sc.toNat + 64 ≤ 2 ^ 32 →
    Region.Disjoint ⟨State.addr d, 64⟩ ⟨State.addr sc, 64⟩ → InRegions s.wr (State.addr d) 64 →
    InRegions s.wr (State.addr sc) 64 →
    ∀ Q : State → Prop, (∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
        (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
        Frame [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩] s.mem s'.mem →
        bytesAt s'.mem (State.addr d) 64 = salsa (bytesAt s.mem (State.addr d) 64) → Q s') →
    WP isa (.call "vg_salsa20_8" c) s Q

/-! ## The precondition -/

section
variable (s₀ : State)

abbrev bP : BitVec 32 := s₀.gpr .r0
abbrev rr : Nat := (s₀.gpr .r1).toNat
abbrev yP : BitVec 32 := s₀.gpr .r2
abbrev sc : BitVec 32 := stackArg s₀ 0
abbrev bA : Addr := State.addr (bP s₀)
abbrev yA : Addr := State.addr (yP s₀)
abbrev scA : Addr := State.addr (sc s₀)
abbrev bR : Region := ⟨bA s₀, rr s₀ * 128⟩
abbrev yR : Region := ⟨yA s₀, rr s₀ * 128⟩
abbrev scR : Region := ⟨scA s₀, 128⟩
abbrev argR : Region := ⟨stackArgAddr s₀ 0, 4⟩
/-- The input. -/
abbrev B : List Byte := bytesAt s₀.mem (bA s₀) (128 * rr s₀)

/-- `Y[2i]` goes to `y + 64 i`. -/
abbrev yE (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * i)
/-- `Y[2i + 1]` goes to `y + 64 (r + i)`. -/
abbrev yO (i : Nat) : Addr := yA s₀ + BitVec.ofNat 64 (64 * (rr s₀ + i))
/-- Where `X` is before the pair `(2k, 2k + 1)`. -/
def xP : Nat → Addr
  | 0 => bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)
  | k + 1 => yO s₀ k
/-- `xP`, as the 32-bit pointer in `r9`. -/
def xP32 : Nat → BitVec 32
  | 0 => bP s₀ + BitVec.ofNat 32 (128 * rr s₀ - 64)
  | k + 1 => yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))

/-- The caller's `r4`–`r9` and our return address are saved in the scratch space. -/
def Saved (m : Mem) : Prop :=
  ∀ p ∈ bmSaved, m.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1

end

/-- The callee-saved registers the code never writes. -/
def others : List Reg := [.r10, .r11]

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [bR s₀, argR s₀]
  wr : s₀.wr = [yR s₀, scR s₀]
  y_s : (yR s₀).Disjoint (scR s₀)
  b_y : (bR s₀).Disjoint (yR s₀)
  b_s : (bR s₀).Disjoint (scR s₀)
  a_y : (argR s₀).Disjoint (yR s₀)
  a_s : (argR s₀).Disjoint (scR s₀)
  b_nw : (bP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  y_nw : (yP s₀).toNat + rr s₀ * 128 ≤ 2 ^ 32
  s_nw : (sc s₀).toNat + 128 ≤ 2 ^ 32
  sp_nw : s₀.sp.toNat + 4 ≤ 2 ^ 32
  r3 : s₀.gpr .r3 = s₀.gpr .r1
  pos : 0 < rr s₀

section
variable {s₀ : State} (hp : Pre s₀)
include hp

/-- `y` is not the whole address space, since `scratch` is not in it. -/
theorem r_lt : 128 * rr s₀ < 2 ^ 32 := by
  by_contra hc
  have hy : yA s₀ = 0 := by
    apply BitVec.eq_of_toNat_eq
    rw [addr_toNat]; show _ = 0; have := hp.y_nw; omega
  have hs : (scA s₀).toNat < 2 ^ 32 := by rw [addr_toNat]; exact (sc s₀).isLt
  refine hp.y_s (scA s₀) ?_ ?_
  · show (scA s₀ - yA s₀).toNat + 1 ≤ rr s₀ * 128
    rw [hy, show (0 : Addr) = 0#64 from rfl, BitVec.sub_zero]; omega
  · show (scA s₀ - scA s₀).toNat + 1 ≤ 128
    rw [BitVec.sub_self, BitVec.toNat_zero]; omega

theorem in_y {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (yR s₀).Contains (yA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

theorem in_b {o n : Nat} (h : o + n ≤ 128 * rr s₀) :
    (bR s₀).Contains (bA s₀ + BitVec.ofNat 64 o) n :=
  contains_off (by omega) (by have := r_lt hp; omega)

/-- Two parts of `y`. -/
theorem y_disj {o₁ n₁ o₂ n₂ : Nat} (h : o₁ + n₁ ≤ o₂ ∨ o₂ + n₂ ≤ o₁) (h₁ : o₁ + n₁ ≤ 128 * rr s₀)
    (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨yA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  have := r_lt hp
  disj_off _ h (by omega) (by omega) (by omega) (by omega)

theorem y_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨yA s₀ + BitVec.ofNat 64 o, n⟩ (yR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

theorem b_sub {o n : Nat} (h : o + n ≤ 128 * rr s₀) : Region.Sub ⟨bA s₀ + BitVec.ofNat 64 o, n⟩ (bR s₀) :=
  sub_off (by omega) (by have := r_lt hp; omega)

/-- A part of `y` and a part of `b`. -/
theorem yb_disj {o₁ n₁ o₂ n₂ : Nat} (h₁ : o₁ + n₁ ≤ 128 * rr s₀) (h₂ : o₂ + n₂ ≤ 128 * rr s₀) :
    Region.Disjoint ⟨yA s₀ + BitVec.ofNat 64 o₁, n₁⟩ ⟨bA s₀ + BitVec.ofNat 64 o₂, n₂⟩ :=
  (hp.b_y.symm.sub_left (y_sub hp h₁)).sub_right (b_sub hp h₂)

/-- A pointer into `y`, as an address. -/
theorem y_addr {o : Nat} (h : o < 128 * rr s₀) :
    State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.y_nw; omega)

theorem b_addr {o : Nat} (h : o < 128 * rr s₀) :
    State.addr (bP s₀ + BitVec.ofNat 32 o) = bA s₀ + BitVec.ofNat 64 o :=
  addr_add (by have := hp.b_nw; omega)

theorem y_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (yP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.y_nw
  rw [toNat_add32 (by omega)]; omega

theorem b_fit {o : Nat} (h : o + 64 ≤ 128 * rr s₀) : (bP s₀ + BitVec.ofNat 32 o).toNat + 64 ≤ 2 ^ 32 := by
  have := hp.b_nw
  rw [toNat_add32 (by omega)]; omega

end

theorem in_s (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    (scR s₀).Contains (scA s₀ + BitVec.ofNat 64 o) n :=
  contains_off h (by omega)

theorem s_sub (s₀ : State) {o n : Nat} (h : o + n ≤ 128) :
    Region.Sub ⟨scA s₀ + BitVec.ofNat 64 o, n⟩ (scR s₀) :=
  sub_off h (by omega)

/-! ## The loop invariant -/

/-- After `k` pairs. -/
structure Inv (s₀ : State) (k : Nat) (s : State) : Prop where
  k_le : k ≤ rr s₀
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀ + BitVec.ofNat 32 (128 * k)
  r5 : s.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k)
  r6 : s.gpr .r6 = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  r7 : s.gpr .r7 = sc s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (rr s₀ - k)
  r9 : s.gpr .r9 = xP32 s₀ k
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)
  x : bytesAt s.mem (xP s₀ k) 64 = xBefore (B s₀) (rr s₀) (2 * k)

/-- The input is unchanged in any memory that differs from the initial one
only in `y` and `scratch`. -/
theorem b_frame {s₀ : State} (hp : Pre s₀) {m : Mem} (hf : Frame [yR s₀, scR s₀] s₀.mem m)
    {o n : Nat} (ho : o + n ≤ 128 * rr s₀) :
    bytesAt m (bA s₀ + BitVec.ofNat 64 o) n = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 o) n := by
  refine frame_bytesAt hf (fun r hr => ?_) (by have := r_lt hp; omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp.b_y.sub_left (b_sub hp ho)
  · exact hp.b_s.sub_left (b_sub hp ho)

/-- Block `i` of the input. -/
theorem blk_B (s₀ : State) {i : Nat} (hi : i < 2 * rr s₀) :
    blk (B s₀) i = bytesAt s₀.mem (bA s₀ + BitVec.ofNat 64 (64 * i)) 64 :=
  blk_bytesAt _ _ (by omega)

/-! ## A call of `vg_salsa20_8` on a block of `y` -/

theorem pres_ne : ∀ r ∈ preserved, r ≠ .r0 ∧ r ≠ .r1 ∧ r ≠ .r2 ∧ r ≠ .r3 := by decide

/-- A 64-byte slot of `y` at offset `o`. -/
abbrev slot (s₀ : State) (o : Nat) : Region := ⟨yA s₀ + BitVec.ofNat 64 o, 64⟩

theorem salsaAt_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR : Reg}
    {s : State} {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) (hd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o)
    (h7 : s.gpr .r7 = sc s₀) (hwr : s.wr = s₀.wr) {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (bytesAt s.mem (yA s₀ + BitVec.ofNat 64 o) 64) → Q s') :
    WP isa (salsaAt c dR) s Q := by
  unfold salsaAt
  refine WP.seq (wp_mov (op2_reg _ _) fun s₁ u₁ => wp_mov (op2_reg _ _) fun s₂ u₂ => WP.block_nil ?_)
  have e₁ : s₂.gpr .r0 = yP s₀ + BitVec.ofNat 32 o := by rw [u₂.other _ (by decide), u₁.gpr, hd]
  have e₂ : s₂.gpr .r1 = sc s₀ := by rw [u₂.gpr, u₁.other _ (by decide), h7]
  have e₃ : ∀ r ∈ preserved, s₂.gpr r = s.gpr r := fun r hr => by
    rw [u₂.other _ (pres_ne r hr).2.1, u₁.other _ (pres_ne r hr).1]
  have ea : State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have hsub : Region.Sub (slot s₀ o) (yR s₀) := y_sub hp ho
  have hsub' : Region.Sub ⟨scA s₀, 64⟩ (scR s₀) := Region.sub_prefix (by omega)
  have hsc : (scR s₀).Contains (scA s₀) 64 := by
    simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
  refine hS s₂ _ _ e₁ e₂ (y_fit hp ho) (by have := hp.s_nw; omega)
    (by rw [ea]; exact hp.y_s.sub_left hsub |>.sub_right hsub')
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr, ea]; exact InRegions.of_mem (by simp) (in_y hp ho))
    (by rw [u₂.wr, u₁.wr, hwr, hp.wr]; exact InRegions.of_mem (R := scR s₀) (by simp) hsc)
    _ fun s' hrd hwr' hsp hcs hf hb => hQ s' (by rw [hrd, u₂.rd, u₁.rd]) (by rw [hwr', u₂.wr, u₁.wr])
      (by rw [hsp, u₂.sp, u₁.sp]) (fun r hr hlr => by rw [hcs r hr hlr, e₃ r hr])
      (by rw [u₂.mem, u₁.mem, ea] at hf; exact hf) (by rw [ea] at hb; rw [hb, u₂.mem, u₁.mem])

/-! ## One pair -/

theorem slot_s {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) :
    (slot s₀ o).Disjoint ⟨scA s₀, 64⟩ :=
  (hp.y_s.sub_left (y_sub hp ho)).sub_right (Region.sub_prefix (by omega))

/-- Where `X` is, as an address. -/
theorem xP_addr {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    State.addr (xP32 s₀ k) = xP s₀ k := by
  cases k with
  | zero => exact b_addr hp (by have := hp.pos; omega)
  | succ j => exact y_addr hp (by omega)

theorem xP_fit {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    (xP32 s₀ k).toNat + 64 ≤ 2 ^ 32 := by
  cases k with
  | zero => exact b_fit hp (by have := hp.pos; omega)
  | succ j => exact y_fit hp (by omega)

theorem xP_in {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (hrd : s.rd = [bR s₀, argR s₀]) (hwr : s.wr = [yR s₀, scR s₀]) :
    ∀ i < 16, InRegions (s.rd ++ s.wr) (xP s₀ k + BitVec.ofNat 64 (4 * i)) 4 := by
  intro i hi
  rw [hrd, hwr]
  cases k with
  | zero =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_b hp (by have := hp.pos; omega))
  | succ j =>
    simp only [xP]
    rw [add_ofNat]
    exact InRegions.of_mem (by simp) (in_y hp (by omega))

theorem xP_disj {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) :
    Region.Disjoint (slot s₀ (64 * k)) ⟨xP s₀ k, 64⟩ := by
  cases k with
  | zero => exact yb_disj hp (by omega) (by have := hp.pos; omega)
  | succ j => exact y_disj hp (by omega) (by omega) (by omega)

/-- What a call's frame keeps: our caller's saved registers. -/
theorem saved_keep {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') (h : Saved s₀ m) : Saved s₀ m' := by
  intro p hp'
  rw [← h p hp']
  have hp4 : p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 := by
    simp only [bmSaved, List.mem_cons, List.not_mem_nil, or_false] at hp'
    rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hsub : Region.Sub ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩ (scR s₀) := s_sub s₀ (by omega)
  refine hf.readW (r := ⟨scA s₀ + BitVec.ofNat 64 p.2, 4⟩) (Region.contains_self _ _) (fun r hr => ?_)
    (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact (hp.y_s.sub_left (y_sub hp ho)).sub_right hsub |>.symm
  · have := disj_off (scA s₀) (o₁ := p.2) (n₁ := 4) (o₂ := 0) (n₂ := 64) (by omega) (by omega)
      (by omega) (by omega) (by omega)
    simpa using this

/-- What a call's frame keeps: the other blocks of `y`. -/
theorem slot_keep {s₀ : State} (hp : Pre s₀) {o o' : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    (ho' : o' + 64 ≤ 128 * rr s₀) (hd : o' + 64 ≤ o ∨ o + 64 ≤ o') {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') :
    bytesAt m' (yA s₀ + BitVec.ofNat 64 o') 64 = bytesAt m (yA s₀ + BitVec.ofNat 64 o') 64 := by
  refine frame_bytesAt hf (fun r hr => ?_) (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact y_disj hp hd ho' ho
  · exact slot_s hp ho'

theorem frame_big {s₀ : State} (hp : Pre s₀) {o : Nat} (ho : o + 64 ≤ 128 * rr s₀) {m m' : Mem}
    (hf : Frame [slot s₀ o, ⟨scA s₀, 64⟩] m m') : Frame [yR s₀, scR s₀] m m' :=
  hf.sub fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨yR s₀, List.mem_cons_self, y_sub hp ho⟩
    · exact ⟨scR s₀, List.mem_cons_of_mem _ List.mem_cons_self, Region.sub_prefix (by omega)⟩

/-- Half a pair: `T = X xor B[i]` into block `o` of `y`, then Salsa20/8 of it. -/
theorem half_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {dR xR sR : Reg}
    (hd : dR ≠ .r2 ∧ dR ≠ .r3) (hx : xR ≠ .r2 ∧ xR ≠ .r3) (hs : sR ≠ .r2 ∧ sR ≠ .r3)
    {o : Nat} (ho : o + 64 ≤ 128 * rr s₀)
    {x : BitVec 32} (fx : x.toNat + 64 ≤ 2 ^ 32) {ob : Nat} (hob : ob + 64 ≤ 128 * rr s₀) {s : State}
    (hrd : s.rd = [bR s₀, argR s₀]) (hwr : s.wr = [yR s₀, scR s₀])
    (gd : s.gpr dR = yP s₀ + BitVec.ofNat 32 o) (gx : s.gpr xR = x)
    (gs : s.gpr sR = bP s₀ + BitVec.ofNat 32 ob) (h7 : s.gpr .r7 = sc s₀)
    (hdx : Region.Disjoint (slot s₀ o) ⟨State.addr x, 64⟩)
    (hinx : ∀ i < 16, InRegions (s.rd ++ s.wr) (State.addr x + BitVec.ofNat 64 (4 * i)) 4)
    {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', s'.rd = s.rd → s'.wr = s.wr → s'.sp = s.sp →
      (∀ r ∈ preserved, r ≠ .lr → s'.gpr r = s.gpr r) →
      Frame [slot s₀ o, ⟨scA s₀, 64⟩] s.mem s'.mem →
      bytesAt s'.mem (yA s₀ + BitVec.ofNat 64 o) 64 =
        salsa (xorBytes (bytesAt s.mem (State.addr x) 64)
          (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)) →
      WP isa P s' Q) :
    WP isa (.block (xor64 dR xR sR)) s fun s' => WP isa (.seq (salsaAt c dR) P) s' Q := by
  have lt := r_lt hp
  have ed : State.addr (yP s₀ + BitVec.ofNat 32 o) = yA s₀ + BitVec.ofNat 64 o := y_addr hp (by omega)
  have eb : State.addr (bP s₀ + BitVec.ofNat 32 ob) = bA s₀ + BitVec.ofNat 64 ob := b_addr hp (by omega)
  rw [← List.append_nil (xor64 dR xR sR)]
  refine xor64_ok hd hx hs (y_fit hp ho) fx (b_fit hp hob) (by rw [ed]; exact hdx)
    (by rw [ed, eb]; exact yb_disj hp ho hob) 16 (Nat.le_refl _) [] s _ gd gx gs hinx
    (fun i hi => by
      rw [hrd, hwr, eb, add_ofNat]; exact InRegions.of_mem (by simp) (in_b hp (by omega)))
    (fun i hi => by
      rw [hwr, ed, add_ofNat]; exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₁ g₁ rd₁ wr₁ sp₁ m₁ => WP.block_nil ?_
  rw [ed, eb] at m₁
  have l1 : (xorBytes (bytesAt s.mem (State.addr x) 64)
      (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 ob) 64)).length = 64 := by
    rw [xorBytes_length _ _ (by simp [bytesAt_length]), bytesAt_length]
  have f₁ : Frame [slot s₀ o] s.mem s₁.mem := by
    rw [m₁]; exact writeBytes_frame _ _ _ (by rw [l1]; exact Region.contains_self _ _)
  have hw := bytesAt_writeBytes_self s.mem (yA s₀ + BitVec.ofNat 64 o) _ (by rw [l1]; omega)
  rw [l1] at hw
  refine WP.seq (salsaAt_ok hS hp ho (by rw [g₁ _ hd.1 hd.2, gd]) (by rw [g₁ _ (by decide) (by decide), h7])
    (by rw [wr₁, hwr, hp.wr]) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  refine hQ s₂ (by rw [rd₂, rd₁]) (by rw [wr₂, wr₁]) (by rw [sp₂, sp₁])
    (fun r hr hlr => by rw [cs₂ r hr hlr, g₁ r (pres_ne r hr).2.2.1 (pres_ne r hr).2.2.2])
    ((f₁.mono (by simp)).trans f₂) ?_
  rw [b₂, m₁, hw]

/-- The state after both halves of pair `k`. -/
structure Mid (s₀ : State) (k : Nat) (s : State) : Prop where
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  sp : s.sp = s₀.sp
  r4 : s.gpr .r4 = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1))
  r5 : s.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k)
  r6 : s.gpr .r6 = yP s₀ + BitVec.ofNat 32 (64 * (rr s₀ + k))
  r7 : s.gpr .r7 = sc s₀
  r8 : s.gpr .r8 = BitVec.ofNat 32 (rr s₀ - k)
  keep : ∀ r ∈ others, s.gpr r = s₀.gpr r
  frame : Frame [yR s₀, scR s₀] s₀.mem s.mem
  saved : Saved s₀ s.mem
  done : ∀ i < k + 1, bytesAt s.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
    bytesAt s.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)

/-- The memory after pair `k`. -/
theorem mem_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s s₂ s₅ : State}
    (h : Inv s₀ k s)
    (f₂ : Frame [slot s₀ (64 * k), ⟨scA s₀, 64⟩] s.mem s₂.mem)
    (b₂ : bytesAt s₂.mem (yE s₀ k) 64 =
      salsa (xorBytes (bytesAt s.mem (xP s₀ k) 64) (bytesAt s.mem (bA s₀ + BitVec.ofNat 64 (128 * k)) 64)))
    (f₅ : Frame [slot s₀ (64 * (rr s₀ + k)), ⟨scA s₀, 64⟩] s₂.mem s₅.mem)
    (b₅ : bytesAt s₅.mem (yO s₀ k) 64 = salsa (xorBytes (bytesAt s₂.mem (yE s₀ k) 64)
      (bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64))) :
    Frame [yR s₀, scR s₀] s₀.mem s₅.mem ∧ Saved s₀ s₅.mem ∧
    ∀ i < k + 1, bytesAt s₅.mem (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt s₅.mem (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1) := by
  have lt := r_lt hp
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have F₂ := h.frame.trans (frame_big hp oE f₂)
  have yE_eq : bytesAt s₂.mem (yE s₀ k) 64 = yAt (B s₀) (rr s₀) (2 * k) := by
    rw [b₂, h.x, b_frame hp h.frame (by omega : 128 * k + 64 ≤ 128 * rr s₀),
      show 128 * k = 64 * (2 * k) by omega, ← blk_B s₀ (by omega), yAt_eq]
  have hb : bytesAt s₂.mem (bA s₀ + BitVec.ofNat 64 (64 * (2 * k + 1))) 64 =
      blk (B s₀) (2 * k + 1) := by
    rw [blk_B s₀ (by omega)]
    exact b_frame hp F₂ (by omega)
  refine ⟨F₂.trans (frame_big hp oO f₅), saved_keep hp oO f₅ (saved_keep hp oE f₂ h.saved),
    fun i hi => ?_⟩
  by_cases hik : i = k
  · subst i
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO oE (by omega) f₅, yE_eq]
    · rw [b₅, yE_eq, hb, yAt_eq (B s₀) (rr s₀) (2 * k + 1), xBefore_succ]
  · have hi' : i < k := by omega
    obtain ⟨d₁, d₂⟩ := h.done i hi'
    refine ⟨?_, ?_⟩
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₁]
    · rw [slot_keep hp oO (by omega) (by omega) f₅, slot_keep hp oE (by omega) (by omega) f₂, d₂]

theorem others_pres : ∀ r ∈ others, r ∈ preserved ∧ r ≠ .lr ∧ r ≠ .r4 := by decide

/-- Both halves of pair `k`. -/
theorem halves_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) {P : Prog isa} {Q : State → Prop}
    (hQ : ∀ s', Mid s₀ k s' → WP isa P s' Q) :
    WP isa (.seq (.block (xor64 .r5 .r9 .r4)) <| .seq (salsaAt c .r5) <|
      .seq (.block (.dp .add .r4 .r4 (.imm 64) :: xor64 .r6 .r5 .r4)) <| .seq (salsaAt c .r6) P)
      s Q := by
  have lt := r_lt hp
  have hrd : s.rd = [bR s₀, argR s₀] := by rw [h.rd, hp.rd]
  have hwr : s.wr = [yR s₀, scR s₀] := by rw [h.wr, hp.wr]
  have oE : 64 * k + 64 ≤ 128 * rr s₀ := by omega
  have oO : 64 * (rr s₀ + k) + 64 ≤ 128 * rr s₀ := by omega
  have ex := xP_addr hp hk
  refine WP.seq (half_ok hS hp (by decide) (by decide) (by decide) oE (xP_fit hp hk) (ob := 128 * k)
    (by omega) hrd hwr h.r5 h.r9 h.r4 h.r7 (by rw [ex]; exact xP_disj hp hk)
    (by rw [ex]; exact xP_in hp hk hrd hwr) fun s₂ rd₂ wr₂ sp₂ cs₂ f₂ b₂ => ?_)
  rw [ex] at b₂
  refine WP.seq (wp_add (op2_imm (by decide)) fun s₃ u₃ => ?_)
  have k3 : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → s₃.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [u₃.other _ h1, cs₂ r h2 h3]
  have e3 : s₃.gpr .r4 = bP s₀ + BitVec.ofNat 32 (64 * (2 * k + 1)) := by
    rw [u₃.gpr, cs₂ _ (by decide) (by decide), h.r4, add32_lit]; congr 2; omega
  have hrd₃ : s₃.rd = [bR s₀, argR s₀] := by rw [u₃.rd, rd₂, hrd]
  have hwr₃ : s₃.wr = [yR s₀, scR s₀] := by rw [u₃.wr, wr₂, hwr]
  have e5 : s₃.gpr .r5 = yP s₀ + BitVec.ofNat 32 (64 * k) := by
    rw [k3 _ (by decide) (by decide) (by decide), h.r5]
  refine half_ok hS hp (by decide) (by decide) (by decide) oO (y_fit hp oE) (ob := 64 * (2 * k + 1))
    (by omega) hrd₃ hwr₃ (by rw [k3 _ (by decide) (by decide) (by decide), h.r6]) e5 e3
    (by rw [k3 _ (by decide) (by decide) (by decide), h.r7])
    (by rw [y_addr hp (by omega)]; exact y_disj hp (by omega) oO oE)
    (fun i hi => by
      rw [hrd₃, hwr₃, y_addr hp (by omega), add_ofNat]
      exact InRegions.of_mem (by simp) (in_y hp (by omega)))
    fun s₅ rd₅ wr₅ sp₅ cs₅ f₅ b₅ => ?_
  rw [u₃.mem, y_addr hp (by omega)] at b₅
  rw [u₃.mem] at f₅
  obtain ⟨F, S, D⟩ := mem_ok hp hk h f₂ b₂ f₅ b₅
  have k5 : ∀ r, r ≠ .r4 → r ∈ preserved → r ≠ .lr → s₅.gpr r = s.gpr r := fun r h1 h2 h3 => by
    rw [cs₅ r h2 h3, k3 r h1 h2 h3]
  exact hQ s₅ ⟨by rw [rd₅, hrd₃, hp.rd], by rw [wr₅, hwr₃, hp.wr],
    by rw [sp₅, u₃.sp, sp₂, h.sp],
    by rw [cs₅ _ (by decide) (by decide), e3],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r5],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r6],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r7],
    by rw [k5 _ (by decide) (by decide) (by decide), h.r8],
    fun r hr => by
      rw [k5 r (others_pres r hr).2.2 (others_pres r hr).1 (others_pres r hr).2.1, h.keep r hr],
    F, S, D⟩

/-- The pointers move on. -/
theorem regs_ok {s₀ : State} (hp : Pre s₀) {k : Nat} (hk : k < rr s₀) {s : State}
    (h : Mid s₀ k s) :
    WP isa (.block [.mov .r9 (.reg .r6), .dp .add .r4 .r4 (.imm 64), .dp .add .r5 .r5 (.imm 64),
      .dp .add .r6 .r6 (.imm 64), .subs .r8 .r8 (.imm 1)]) s
      fun s' => Inv s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = rr s₀) := by
  have lt := r_lt hp
  refine wp_mov (op2_reg _ _) fun s₆ u₆ => wp_add (op2_imm (by decide)) fun s₇ u₇ =>
    wp_add (op2_imm (by decide)) fun s₈ u₈ => wp_add (op2_imm (by decide)) fun s₉ u₉ =>
    Proof.MdStream.Arm.wp_subs (op2_imm (by decide)) fun s₁₀ u₁₀ z₁₀ => WP.block_nil ?_
  have m₁₀ : s₁₀.mem = s.mem := by rw [u₁₀.mem, u₉.mem, u₈.mem, u₇.mem, u₆.mem]
  have g : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r8 → r ≠ .r9 → s₁₀.gpr r = s.gpr r :=
    fun r h4 h5 h6 h8 h9 => by
      rw [u₁₀.other _ h8, u₉.other _ h6, u₈.other _ h5, u₇.other _ h4, u₆.other _ h9]
  have e8 : s₁₀.gpr .r8 = BitVec.ofNat 32 (rr s₀ - (k + 1)) := by
    rw [u₁₀.gpr, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r8, ofNat_pred32 (by omega), Nat.sub_sub]
  refine ⟨⟨(by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, e8, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [u₁₀.rd, u₉.rd, u₈.rd, u₇.rd, u₆.rd, h.rd]
  · rw [u₁₀.wr, u₉.wr, u₈.wr, u₇.wr, u₆.wr, h.wr]
  · rw [u₁₀.sp, u₉.sp, u₈.sp, u₇.sp, u₆.sp, h.sp]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide), u₇.gpr,
      u₆.other _ (by decide), h.r4, add32_lit]
    congr 2; omega
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.gpr, u₇.other _ (by decide),
      u₆.other _ (by decide), h.r5, add32_lit]
    congr 2
  · rw [u₁₀.other _ (by decide), u₉.gpr, u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r6, add32_lit]
    congr 2
  · rw [g _ (by decide) (by decide) (by decide) (by decide) (by decide), h.r7]
  · rw [u₁₀.other _ (by decide), u₉.other _ (by decide), u₈.other _ (by decide),
      u₇.other _ (by decide), u₆.gpr, h.r6]
    rfl
  · intro r hr
    have : r ≠ .r4 ∧ r ≠ .r5 ∧ r ≠ .r6 ∧ r ≠ .r8 ∧ r ≠ .r9 := by
      simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> decide
    rw [g r this.1 this.2.1 this.2.2.1 this.2.2.2.1 this.2.2.2.2, h.keep r hr]
  · rw [m₁₀]; exact h.frame
  · rw [m₁₀]; exact h.saved
  · rw [m₁₀]; exact h.done
  · rw [m₁₀]
    show bytesAt s.mem (yO s₀ k) 64 = _
    rw [(h.done k (by omega)).2]
    rfl
  · rw [z₁₀, u₉.other _ (by decide), u₈.other _ (by decide), u₇.other _ (by decide),
      u₆.other _ (by decide), h.r8,
      ofNat_pred32 (by omega), Proof.MdStream.Arm.ofNat_beq_zero (by omega)]
    simp only [decide_eq_decide]
    omega

theorem body_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {k : Nat}
    (hk : k < rr s₀) {s : State} (h : Inv s₀ k s) :
    WP isa (bmBody c) s fun s' => Inv s₀ (k + 1) s' ∧ s'.z = decide (k + 1 = rr s₀) :=
  halves_ok hS hp hk h fun _ hm => regs_ok hp hk hm

end VG.Proof.Scrypt.Arm.BlockMix

/-!
# scryptBlockMix on 32-bit ARM: the whole function

The prologue loads the scratch pointer from the stack, saves our caller's
`r4`–`r9` and our return address in `scratch` and sets up the loop's
registers; the loop runs the `r` pairs; the epilogue restores the registers.
There is no stack frame.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm VG.Impl.Scrypt.Arm
open VG.Spec.Scrypt (bytesAt blk blockMix)
open VG.Proof.Scrypt (yAt xBefore blockMix_eq flatMap_congr)
open VG.Proof.MdStream.Arm (Upd wp_mov wp_add wp_sub wp_ldr wp_ldrSp op2_reg op2_imm op2_lsl
  eval_ne ofNat_beq_zero saveMem saveList_ok readW_writeW_save)
open VG.Proof.Scrypt.Memory (add_ofNat InRegions.of_mem frame_bytesAt bytesAt_add bytesAt_blocks)

/-! ## The prologue -/

/-- The prologue's register moves. -/
def bmSetup : List Instr :=
  [.mov .r8 (.reg .r1), .mov .r4 (.reg .r0), .mov .r5 (.reg .r2), .mov .r7 (.reg .r12),
   .dp .add .r6 .r2 (.shifted .r1 .lsl 6), .dp .add .r9 .r0 (.shifted .r1 .lsl 7),
   .dp .sub .r9 .r9 (.imm 64)]

theorem prologue_eq : bmPrologue =
    .ldrSp .r12 0 :: (bmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ bmSetup) := rfl

theorem saveMem_saved (m : Mem) (B : Addr) (g : Reg → BitVec 32) :
    ∀ p ∈ bmSaved, (saveMem m B g bmSaved).readW (B + BitVec.ofNat 64 p.2) 32 = g p.1 :=
  Spill.saveMem_saved (lo := 64) (hi := 92) B g m bmSaved (by decide)

theorem bmSaved_bound : ∀ p ∈ bmSaved, p.2 + 4 ≤ 128 ∧ 64 ≤ p.2 ∧ p.1 ≠ .r12 := by decide

theorem bmSaved_r7 : ∀ p ∈ bmSaved.take 6, p.1 ≠ .r7 := by decide

theorem save_ok {s₀ : State} (hp : Pre s₀) {rest : List Instr} {Q : State → Prop}
    (k : ∀ s₁, (∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r) → s₁.gpr .r12 = sc s₀ → s₁.rd = s₀.rd →
      s₁.wr = s₀.wr → s₁.sp = s₀.sp → Frame [scR s₀] s₀.mem s₁.mem → Saved s₀ s₁.mem →
      WP isa (.block rest) s₁ Q) :
    WP isa (.block (.ldrSp .r12 0 :: (bmSaved.map (fun p => Instr.str p.1 .r12 p.2) ++ rest)))
      s₀ Q := by
  have hs := hp.s_nw
  refine wp_ldrSp (a := stackArgAddr s₀ 0) (by decide) rfl ?_ fun s₁ u₁ => ?_
  · rw [hp.rd]
    refine InRegions.of_mem (R := argR s₀) (by simp) ?_
    show (stackArgAddr s₀ 0 - stackArgAddr s₀ 0).toNat + 4 ≤ 4
    rw [BitVec.sub_self, BitVec.toNat_zero]
  have e12 : s₁.gpr .r12 = sc s₀ := u₁.gpr
  refine saveList_ok bmSaved s₁ Q (fun p hp' => ?_) fun s₂ g rd wr sp m => ?_
  · obtain ⟨h1, h2, -⟩ := bmSaved_bound p hp'
    rw [e12, u₁.wr, hp.wr]
    exact ⟨by omega, by omega, InRegions.of_mem (by simp) (in_s s₀ h1)⟩
  refine k s₂ (fun r hr => by rw [g, u₁.other r hr]) (by rw [g, e12]) (by rw [rd, u₁.rd])
    (by rw [wr, u₁.wr]) (by rw [sp, u₁.sp]) ?_ ?_
  · rw [m, e12, u₁.mem]
    exact saveMem_frame' _ _ _ fun p hp' => in_s s₀ (bmSaved_bound p hp').1
  · intro p hp'
    rw [m, e12, saveMem_saved, u₁.other _ (bmSaved_bound p hp').2.2]
    exact hp'

/-- The registers the loop starts with. -/
theorem setup_ok {s₀ : State} (hp : Pre s₀) {s₁ : State} (g : ∀ r, r ≠ .r12 → s₁.gpr r = s₀.gpr r)
    (g12 : s₁.gpr .r12 = sc s₀) (hrd : s₁.rd = s₀.rd) (hwr : s₁.wr = s₀.wr) (hsp : s₁.sp = s₀.sp)
    (hf : Frame [scR s₀] s₀.mem s₁.mem) (hsv : Saved s₀ s₁.mem) :
    WP isa (.block bmSetup) s₁ (Inv s₀ 0) := by
  have lt := r_lt hp
  have pos := hp.pos
  refine wp_mov (op2_reg _ _) fun a ua => wp_mov (op2_reg _ _) fun b ub =>
    wp_mov (op2_reg _ _) fun c uc => wp_mov (op2_reg _ _) fun d ud =>
    wp_add (op2_lsl (by decide)) fun e ue => wp_add (op2_lsl (by decide)) fun f uf =>
    wp_sub (op2_imm (by decide)) fun i ui => WP.block_nil ?_
  have hm : i.mem = s₁.mem := by
    rw [ui.mem, uf.mem, ue.mem, ud.mem, uc.mem, ub.mem, ua.mem]
  have k : ∀ r, r ≠ .r4 → r ≠ .r5 → r ≠ .r6 → r ≠ .r7 → r ≠ .r8 → r ≠ .r9 → r ≠ .r12 →
      i.gpr r = s₀.gpr r := fun r h4 h5 h6 h7 h8 h9 h12 => by
    rw [ui.other _ h9, uf.other _ h9, ue.other _ h6, ud.other _ h7, uc.other _ h5, ub.other _ h4,
      ua.other _ h8, g _ h12]
  have hr : rr s₀ = (s₀.gpr .r1).toNat := rfl
  have x1 : d.gpr .r1 = s₀.gpr .r1 := by
    rw [ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide),
      ua.other _ (by decide), g _ (by decide)]
  have e0 : e.gpr .r0 = bP s₀ := by
    rw [ue.other _ (by decide), ud.other _ (by decide), uc.other _ (by decide),
      ub.other _ (by decide), ua.other _ (by decide), g _ (by decide)]
  have e1 : e.gpr .r1 = s₀.gpr .r1 := by rw [ue.other _ (by decide), x1]
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun i hi => absurd hi (by omega), ?_⟩
  · rw [ui.rd, uf.rd, ue.rd, ud.rd, uc.rd, ub.rd, ua.rd, hrd]
  · rw [ui.wr, uf.wr, ue.wr, ud.wr, uc.wr, ub.wr, ua.wr, hwr]
  · rw [ui.sp, uf.sp, ue.sp, ud.sp, uc.sp, ub.sp, ua.sp, hsp]
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.gpr, ua.other _ (by decide),
      g _ (by decide)]
    simp
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.gpr, ub.other _ (by decide), ua.other _ (by decide),
      g _ (by decide)]
    simp
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.gpr, x1, ud.other _ (by decide),
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g _ (by decide),
      shl32 (by omega)]
    congr 2; omega
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide), ud.gpr,
      uc.other _ (by decide), ub.other _ (by decide), ua.other _ (by decide), g12]
  · rw [ui.other _ (by decide), uf.other _ (by decide), ue.other _ (by decide),
      ud.other _ (by decide), uc.other _ (by decide), ub.other _ (by decide), ua.gpr,
      g _ (by decide), Nat.sub_zero]
    exact ofNat_toNat32 _
  · rw [ui.gpr, uf.gpr, e0, e1, shl32 (by omega),
      show (s₀.gpr .r1).toNat * 2 ^ 7 = 128 * rr s₀ by omega, sub32 _ (by omega)]
    rfl
  · intro r hr
    simp only [others, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> exact k _ (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · rw [hm]; exact hf.mono (by simp)
  · rw [hm]; exact hsv
  · rw [hm]
    show bytesAt s₁.mem (bA s₀ + BitVec.ofNat 64 (128 * rr s₀ - 64)) 64 =
      blk (B s₀) (2 * rr s₀ - 1)
    rw [blk_B s₀ (by omega), show 64 * (2 * rr s₀ - 1) = 128 * rr s₀ - 64 by omega]
    exact b_frame hp (hf.mono (by simp)) (by omega)

/-! ## The loop -/

theorem loop_ok {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) {s : State}
    (h : Inv s₀ 0 s) : WP isa (.loop (bmBody c) .ne) s (Inv s₀ (rr s₀)) := by
  refine WP.loop (M := isa) (fun n s => ∃ k, n = rr s₀ - k ∧ k < rr s₀ ∧ Inv s₀ k s) ?_ (rr s₀) s
    ⟨0, rfl, hp.pos, h⟩
  rintro n s ⟨k, rfl, hk, hi⟩
  refine WP.mono (body_ok hS hp hk hi) fun s' ⟨hi', hz⟩ => ?_
  have he : isa.eval .ne s' = some (!decide (k + 1 = rr s₀)) := by
    rw [← hz]; exact eval_ne s'
  by_cases hl : k + 1 = rr s₀
  · refine .inl ⟨by rw [he]; simp [hl], ?_⟩
    rwa [hl] at hi'
  · exact .inr ⟨by rw [he]; simp [hl], rr s₀ - (k + 1), by omega, k + 1, rfl, by omega, hi'⟩

/-! ## The epilogue -/

theorem epilogue_eq : bmEpilogue =
    (bmSaved.take 6).map (fun p => Instr.ldr p.1 .r7 p.2) ++ ([.ldr .r7 .r7 88] : List Instr) := rfl

theorem restore_ok {s₀ : State} (hp : Pre s₀) {s : State} (h : Inv s₀ (rr s₀) s) :
    WP isa (.block bmEpilogue) s fun s' => s'.mem = s.mem ∧ s'.sp = s.sp ∧
      (∀ r ∈ preserved, s'.gpr r = s₀.gpr r) := by
  have hs := hp.s_nw
  have hin : ∀ d, d + 4 ≤ 128 → ∀ t : State, t.rd = s.rd → t.wr = s.wr →
      InRegions (t.rd ++ t.wr) (scA s₀ + BitVec.ofNat 64 d) 4 := fun d hd t hr hw => by
    rw [hr, hw, h.rd, h.wr, hp.rd, hp.wr]; exact InRegions.of_mem (by simp) (in_s s₀ hd)
  rw [epilogue_eq]
  refine restoreList_ok _ s _ (by decide) (fun p hp' => ?_) fun s₁ hl ho hm hrd hwr hsp => ?_
  · have hb := bmSaved_bound p (List.mem_of_mem_take hp')
    rw [h.r7]
    exact ⟨bmSaved_r7 p hp', by omega, by omega, hin _ hb.1 _ rfl rfl⟩
  have e7 : s₁.gpr .r7 = sc s₀ := by rw [ho _ (by decide), h.r7]
  refine wp_ldr (a := scA s₀ + BitVec.ofNat 64 88) (by decide) (by rw [e7, addr_add (by omega)])
    (hin _ (by omega) _ hrd hwr) fun s₂ u₂ => WP.block_nil ?_
  refine ⟨by rw [u₂.mem, hm], by rw [u₂.sp, hsp], fun r hr => ?_⟩
  have sv : ∀ p ∈ bmSaved, s.mem.readW (scA s₀ + BitVec.ofNat 64 p.2) 32 = s₀.gpr p.1 := h.saved
  have lo : ∀ p ∈ bmSaved.take 6, s₂.gpr p.1 = s₀.gpr p.1 := fun p hp' => by
    rw [u₂.other _ (bmSaved_r7 p hp'), hl p hp', h.r7]
    exact sv p (List.mem_of_mem_take hp')
  simp only [preserved, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lo (.r4, 64) (by decide)
  · exact lo (.r5, 68) (by decide)
  · exact lo (.r6, 72) (by decide)
  · rw [u₂.gpr, hm, sv (.r7, 88) (by decide)]
  · exact lo (.r8, 76) (by decide)
  · exact lo (.r9, 80) (by decide)
  · rw [u₂.other _ (by decide), ho _ (by decide)]; exact h.keep _ (by decide)
  · rw [u₂.other _ (by decide), ho _ (by decide)]; exact h.keep _ (by decide)
  · exact lo (.lr, 84) (by decide)

/-! ## The whole function -/

/-- The output, from the blocks the loop wrote. -/
theorem post_of {s₀ : State} {m : Mem}
    (h : ∀ i < rr s₀, bytesAt m (yE s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i) ∧
      bytesAt m (yO s₀ i) 64 = yAt (B s₀) (rr s₀) (2 * i + 1)) :
    bytesAt m (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀) := by
  rw [blockMix_eq, show 128 * rr s₀ = 64 * rr s₀ + 64 * rr s₀ by omega, bytesAt_add,
    bytesAt_blocks, bytesAt_blocks]
  congr 1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    exact (h i hi).1
  · refine flatMap_congr fun i hi => ?_
    rw [List.mem_range] at hi
    rw [add_ofNat, ← Nat.mul_add]
    exact (h i hi).2

theorem pre_of {s₀ : State} (h : Proof.Scrypt.blockMixArm.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩ := h
  rw [h12] at h2 h3 h4 h6 h9
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

theorem correct {c : Prog isa} (hS : SalsaSpec c) {s₀ : State} (hp : Pre s₀) :
    WP isa (blockMixWith c) s₀ fun s' =>
      abiPreserved s₀ s' ∧ Proof.Scrypt.blockMixArm.post s₀ s' := by
  unfold blockMixWith
  refine WP.seq ?_
  rw [prologue_eq]
  refine save_ok hp fun s₁ g g12 hrd hwr hsp hf hsv => ?_
  refine WP.mono (setup_ok hp g g12 hrd hwr hsp hf hsv) fun s₂ h₂ => ?_
  refine WP.seq (WP.mono (loop_ok hS hp h₂) fun s₃ h₃ => ?_)
  refine WP.mono (restore_ok hp h₃) fun s' ⟨hm', hsp', hg'⟩ => ⟨⟨hg', hsp'.trans h₃.sp⟩, ?_⟩
  show bytesAt s'.mem (yA s₀) (128 * rr s₀) = blockMix (rr s₀) (B s₀)
  rw [hm']
  exact post_of fun i hi => h₃.done i hi

end VG.Proof.Scrypt.Arm.BlockMix

/-!
# scryptBlockMix on 32-bit ARM: verified

`SalsaSpec` of the verified Salsa20/8 Core, from its `Verified` proof by
`WP.call`; then the `Verified` proof of `vg_scrypt_blockmix`. Only the
pointers, `r` and the stack argument (the scratch pointer) are public, and the
taint analysis checks that nothing else reaches an address or a branch.
-/

namespace VG.Proof.Scrypt.Arm.BlockMix

open VG VG.Arm

/-- A region inside one of `rs` is covered by `rs`. -/
theorem covers_of_in {rs : List Region} {a : Addr} {n : Nat} (h : InRegions rs a n) :
    Covers [⟨a, n⟩] rs := by
  obtain ⟨R, hR, hc⟩ := h
  refine Covers.of_sub fun r hr => ?_
  simp only [List.mem_singleton] at hr; subst hr
  exact ⟨R, hR, (a - R.base).toNat, by rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega, hc⟩

theorem covers_pair {rs : List Region} {a b : Region} (ha : Covers [a] rs) (hb : Covers [b] rs) :
    Covers [a, b] rs := by
  intro x n ⟨r, hr, hc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ha x n ⟨_, List.mem_singleton_self _, hc⟩
  · exact hb x n ⟨_, List.mem_singleton_self _, hc⟩

theorem salsaSpec : SalsaSpec Impl.Scrypt.Arm.salsa := by
  intro s d sc hd hsc fd fsc hds hind hins Q hQ
  have c0 : s.callEntry.gpr .r0 = d := (State.callEntry_gpr _ (by decide)).trans hd
  have c1 : s.callEntry.gpr .r1 = sc := (State.callEntry_gpr _ (by decide)).trans hsc
  have hw : Covers [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩] s.wr :=
    covers_pair (covers_of_in hind) (covers_of_in hins)
  refine WP.call (k := Proof.Scrypt.salsaArm) Proof.Scrypt.Arm.salsa_correct
    (rd := []) (wr := [⟨State.addr d, 64⟩, ⟨State.addr sc, 64⟩]) ?_ ?_ hw ?_
  · simp only [Proof.Scrypt.salsaArm, State.withRegions_gpr, State.withRegions_rd,
      State.withRegions_wr, c0, c1]
    exact ⟨by trivial, by trivial, hds, fd, fsc⟩
  · intro a n h
    obtain ⟨R, hR, hc⟩ := hw a n (by simpa using h)
    exact ⟨R, List.mem_append_right _ hR, hc⟩
  · intro s' hrd hwr hsp hf hcs _ hpost
    simp only [Proof.Scrypt.salsaArm, State.withRegions_gpr, State.withRegions_mem,
      State.callEntry_mem, c0] at hpost
    exact hQ s' hrd hwr hsp hcs hf hpost

/-- The initial taint: `r0`–`r3` are public, and so is the stack argument
(the scratch pointer). -/
def τ₀ : VG.Arm.Taint.T := { regs := .ofList [.r0, .r1, .r2, .r3], flags := false, argLen := 4 }

theorem wf₀ {s : State} (h : Proof.Scrypt.blockMixArm.pre s) : VG.Arm.Taint.Wf τ₀ s := by
  have hp := pre_of h
  refine ⟨fun h => absurd rfl h, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hp.sp_nw, ?_⟩, fun _ h => (List.not_mem_nil h).elim⟩
  have e : (⟨State.addr s.sp, 4⟩ : Region) = argR s := by simp [stackArgAddr]
  simp only [τ₀, e, hp.wr, List.mem_cons, List.not_mem_nil, or_false]
  rintro r (rfl | rfl)
  · exact hp.a_y
  · exact hp.a_s

theorem argByte_eq (s : State) (k : Nat) :
    VG.Arm.Taint.argByte s k = stackArgAddr s 0 + BitVec.ofNat 64 k := by
  simp [VG.Arm.Taint.argByte, stackArgAddr]

theorem agree₀ {s₁ s₂ : State} (h₁ : Proof.Scrypt.blockMixArm.pre s₁)
    (h₂ : Proof.Scrypt.blockMixArm.pre s₂) (hpub : Proof.Scrypt.blockMixArm.pub s₁ s₂) :
    VG.Arm.Taint.Agree τ₀ s₁ s₂ := by
  obtain ⟨psp, p0, p1, p2, p3, a0⟩ := hpub
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun h => absurd rfl h, wf₀ h₁, wf₀ h₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => psp,
    fun k hk => ?_⟩
  · simp only [τ₀, RegSet.mem_ofList, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> with_reducible assumption
  · simp only [τ₀] at hk
    rw [argByte_eq, argByte_eq, Mem.readW_byte s₁.mem _ hk, Mem.readW_byte s₂.mem _ hk]
    exact congrArg _ a0

/-- A state satisfying the precondition: `b` at `0x1000`, `y` at `0x2000`
and the scratch space at `0x3000`, passed on the stack at `0x5000`. -/
def bmSat : State where
  gpr r := match r with
    | .r0 => 0x1000 | .r1 => 1 | .r2 => 0x2000 | .r3 => 1 | _ => 0
  sp := 0x5000
  n := false
  z := false
  c := false
  v := false
  mem a := if a = 0x5001 then 0x30 else 0
  rd := [⟨0x1000, 128⟩, ⟨0x5000, 4⟩]
  wr := [⟨0x2000, 128⟩, ⟨0x3000, 128⟩]

theorem blockMix_correct (s : State) (hs : Proof.Scrypt.blockMixArm.pre s) :
    ∃ t s', Exec isa Impl.Scrypt.Arm.blockMix s t s' ∧ abiPreserved s s' ∧
      Proof.Scrypt.blockMixArm.post s s' := by
  obtain ⟨t, s', he, h⟩ := BlockMix.correct salsaSpec (pre_of hs)
  exact ⟨t, s', he, h⟩

theorem blockMix_ct : ConstantTime isa Proof.Scrypt.blockMixArm.pre Proof.Scrypt.blockMixArm.pub
    Impl.Scrypt.Arm.blockMix := by
  exact VG.Taint.constantTime (A := taint) τ₀ (fun _ _ h₁ h₂ hp => agree₀ h₁ h₂ hp)
    (by taint_decide)

theorem blockMix_verified :
    Verified Arm.target Impl.Scrypt.Arm.blockMix (Spec.Scrypt.blockMixContract Arm.abi) :=
  Verified.of_correct blockMix_correct blockMix_ct
    { pre := by
        sig_implies_pre [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      post := by
        sig_implies_post [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      pub := by
        sig_implies_pub [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
      sat := by
        implies_sat [Spec.Scrypt.blockMixContract, Spec.Scrypt.blockMixSig,
          Proof.Scrypt.blockMixArm, Arm.abi, Arm.argRegs, Arm.reduceClassify, Arm.Loc.val,
          Arm.State.addr]
          [Proof.Scrypt.Arm.BlockMix.bmSat, Arm.stackArg, Arm.stackArgAddr, Mem.readW, Mem.read]
          using Proof.Scrypt.Arm.BlockMix.bmSat }

end VG.Proof.Scrypt.Arm.BlockMix
