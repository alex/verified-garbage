import VerifiedGarbage.Impl.X448.X86_64
import VerifiedGarbage.Proof.Framework.X86_64.Exec
import VerifiedGarbage.Proof.Framework.X86_64.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Proof.X448.Field
import VerifiedGarbage.Proof.X25519.Bytes

/-!
# X448 on x86-64: the working space and words

The working space is 8 KiB at `base`, which `rdi` holds (`Scr`). Numbers of
several words are read from registers (`rv`, lowest first) or from memory
(`mv`, at consecutive offsets of the working space); a field element is the
seven words at an offset (`fe`). `Keeps rs` says that a block changed only
the registers `rs` (and the flags), and `Stable X s src v` that the source
operand `src` reads `v` in every state that agrees with `s` but on the
registers `X`. `Outside base o n` says that memory changed only in the bytes
`[o, o + n)` of the working space.
-/

namespace VG.Proof.X448.X86_64

open VG VG.X86_64 VG.Impl.X448.X86_64

/-- `p + d`. -/
abbrev off (p : Addr) (d : Nat) : Addr := p + BitVec.ofNat 64 d

/-- The registers of `s'` are those of `s` but for `rs`, and memory and the
regions are unchanged. -/
def Keeps (rs : List Reg) (s s' : State) : Prop :=
  (∀ r, r ∉ rs → s'.gpr r = s.gpr r) ∧ s'.mem = s.mem ∧ s'.rd = s.rd ∧ s'.wr = s.wr

theorem Keeps.refl (rs : List Reg) (s : State) : Keeps rs s s := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem Keeps.trans {rs : List Reg} {s₁ s₂ s₃ : State} (h₁ : Keeps rs s₁ s₂) (h₂ : Keeps rs s₂ s₃) :
    Keeps rs s₁ s₃ :=
  ⟨fun r hr => (h₂.1 r hr).trans (h₁.1 r hr), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem Keeps.mono {rs rs' : List Reg} {s s' : State} (h : Keeps rs s s') (hs : ∀ r ∈ rs, r ∈ rs') :
    Keeps rs' s s' :=
  ⟨fun r hr => h.1 r fun h' => hr (hs r h'), h.2⟩

/-- The working space: `rdi` holds its base `base`, it is writable and it
does not wrap around. -/
structure Scr (s : State) (base : Addr) : Prop where
  rdi : s.gpr .rdi = base
  wr : (⟨base, 8192⟩ : Region) ∈ s.wr
  nowrap : base.toNat + 8192 ≤ 2 ^ 64

/-- The word at `base + d`. -/
abbrev word (m : Mem) (base : Addr) (d : Nat) : BitVec 64 := m.readW (off base d) 64

/-- The value of the registers `rs`, lowest first. -/
def rv (s : State) : List Reg → Nat
  | [] => 0
  | r :: rs => (s.gpr r).toNat + 2 ^ 64 * rv s rs

/-- The value of the `n` words at `base + o`, lowest first. -/
def mv (m : Mem) (base : Addr) : Nat → Nat → Nat
  | _, 0 => 0
  | o, n + 1 => (word m base o).toNat + 2 ^ 64 * mv m base (o + 8) n

/-- The value of words, lowest first. -/
def wv : List (BitVec 64) → Nat
  | [] => 0
  | v :: vs => v.toNat + 2 ^ 64 * wv vs

/-- The field element at `base + o`: seven words. -/
abbrev fe (m : Mem) (base : Addr) (o : Nat) : Nat := mv m base o 7

theorem pow64_succ (n : Nat) : 2 ^ (64 * (n + 1)) = 2 ^ 64 * 2 ^ (64 * n) := by
  rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]

theorem rv_lt (s : State) : ∀ rs : List Reg, rv s rs < 2 ^ (64 * rs.length)
  | [] => by simp [rv]
  | r :: rs => by
    have h1 := (s.gpr r).isLt
    have h2 := rv_lt s rs
    rw [rv, List.length_cons, pow64_succ]
    generalize 2 ^ (64 * rs.length) = P at *
    generalize rv s rs = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem mv_lt (m : Mem) (base : Addr) : ∀ o n, mv m base o n < 2 ^ (64 * n)
  | _, 0 => by simp [mv]
  | o, n + 1 => by
    have h1 := (word m base o).isLt
    have h2 := mv_lt m base (o + 8) n
    rw [mv, pow64_succ]
    generalize 2 ^ (64 * n) = P at *
    generalize mv m base (o + 8) n = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem wv_lt : ∀ vs : List (BitVec 64), wv vs < 2 ^ (64 * vs.length)
  | [] => by simp [wv]
  | v :: vs => by
    have h1 := v.isLt
    have h2 := wv_lt vs
    rw [wv, List.length_cons, pow64_succ]
    generalize 2 ^ (64 * vs.length) = P at *
    generalize wv vs = y at *
    have : 2 ^ 64 * (y + 1) ≤ 2 ^ 64 * P := Nat.mul_le_mul_left _ h2
    omega

theorem fe_lt (m : Mem) (base : Addr) (o : Nat) : fe m base o < 2 ^ 448 := by
  have := mv_lt m base o 7
  rwa [show 64 * 7 = 448 from rfl] at this

theorem rv_congr {s s' : State} : ∀ {rs : List Reg}, (∀ r ∈ rs, s'.gpr r = s.gpr r) →
    rv s' rs = rv s rs
  | [], _ => rfl
  | r :: rs, h => by
    simp only [rv, h r List.mem_cons_self, rv_congr (rs := rs) fun r' hr => h r' (List.mem_cons_of_mem _ hr)]

theorem ea_sc (s : State) (d : Nat) : s.ea (sc d) = off (s.gpr .rdi) d := by
  simp only [State.ea, sc, at_, BitVec.ofInt_natCast]

theorem contains_sc {base : Addr} {d n : Nat} (h : d + n ≤ 8192) :
    (⟨base, 8192⟩ : Region).Contains (off base d) n :=
  Offset.contains_base base h (by omega)

theorem Scr.read {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions (s.rd ++ s.wr) (off base d) n :=
  ⟨_, List.mem_append_right _ hs.wr, contains_sc hd⟩

theorem Scr.write {s : State} {base : Addr} (hs : Scr s base) {d n : Nat} (hd : d + n ≤ 8192) :
    InRegions s.wr (off base d) n := ⟨_, hs.wr, contains_sc hd⟩

theorem load_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    s.load64 (s.ea (sc d)) = some (word s.mem base d) := by
  rw [ea_sc, hs.rdi, State.load64, ite_eq_left (hs.read hd)]

theorem readSrc_sc {s : State} {base : Addr} (hs : Scr s base) {d : Nat} (hd : d + 8 ≤ 8192) :
    readSrc s (.mem (sc d)) = some (word s.mem base d) := load_sc hs hd

theorem Scr.of_keeps {rs : List Reg} {s s' : State} {base : Addr} (hs : Scr s base)
    (h : Keeps rs s s') (hr : .rdi ∉ rs) : Scr s' base :=
  ⟨(h.1 _ hr).trans hs.rdi, h.2.2.2 ▸ hs.wr, hs.nowrap⟩

/-! ## Modulo `p`

`2⁴⁴⁸ ≡ 2²²⁴ + 1`. Lemmas about `P` are applied to explicit arguments:
unifying a pattern with `2 ^ 448` in it against another term makes Lean
try to evaluate the power. -/

open VG.Spec.X448 (P) in
theorem P_eq : 2 ^ 448 = P + (2 ^ 224 + 1) := by decide +kernel

open VG.Spec.X448 (P) in
theorem fold448 (a b : Nat) : (a + 2 ^ 448 * b) % P = (a + (2 ^ 224 + 1) * b) % P := by
  rewrite [P_eq, Nat.add_mul, Nat.add_comm (P * b), ← Nat.add_assoc]
  exact Nat.add_mul_mod_self_left _ _ _

/-- A 32-bit load reads the low half of the word. -/
theorem readW32 (m : Mem) (p : Addr) : (m.readW p 32).toNat = (m.readW p 64).toNat % 2 ^ 32 := by
  rw [← X25519.leNum_bytesAt_32bit, ← X25519.leNum_bytesAt_64, show 8 = 4 + 4 from rfl,
    X25519.bytesAt_add, X25519.leNum_append, X25519.length_bytesAt]
  have := X25519.leNum_lt (Spec.X25519.bytesAt m p 4)
  rw [X25519.length_bytesAt] at this
  omega

/-! ## Stable sources -/

/-- `src` reads `v` in every state that agrees with `s` but on the registers
`X` and the flags. -/
def Stable (X : List Reg) (s : State) (src : Src) (v : BitVec 64) : Prop :=
  ∀ t, (∀ r, r ∉ X → t.gpr r = s.gpr r) → t.mem = s.mem → t.rd = s.rd → t.wr = s.wr →
    readSrc t src = some v

theorem Stable.read {X : List Reg} {s : State} {src : Src} {v : BitVec 64} (h : Stable X s src v) :
    readSrc s src = some v := h s (fun _ _ => rfl) rfl rfl rfl

theorem Stable.mono {X Y : List Reg} {s : State} {src : Src} {v : BitVec 64} (h : Stable Y s src v)
    (hXY : ∀ r ∈ X, r ∈ Y) : Stable X s src v :=
  fun t hg hm hrd hwr => h t (fun r hr => hg r fun h' => hr (hXY r h')) hm hrd hwr

/-- A stable source of `s` is one of any state that agrees with `s` but on
`X`. -/
theorem Stable.of_keeps {X : List Reg} {s s' : State} {src : Src} {v : BitVec 64}
    (h : Stable X s src v) (hk : Keeps X s s') : Stable X s' src v :=
  fun t hg hm hrd hwr => h t (fun r hr => (hg r hr).trans (hk.1 r hr)) (hm.trans hk.2.1)
    (hrd.trans hk.2.2.1) (hwr.trans hk.2.2.2)

theorem stable_reg {X : List Reg} (s : State) {r : Reg} (hr : r ∉ X) :
    Stable X s (.reg r) (s.gpr r) :=
  fun _ hg _ _ _ => by rw [readSrc, hg r hr]

theorem stable_imm (X : List Reg) (s : State) (v : BitVec 32) :
    Stable X s (.imm v) (v.signExtend 64) := fun _ _ _ _ _ => rfl

theorem stable_imm0 (X : List Reg) (s : State) : Stable X s (.imm 0) 0 := fun _ _ _ _ _ => rfl

theorem stable_sc {X : List Reg} {s : State} {base : Addr} (hs : Scr s base) (hX : .rdi ∉ X)
    {d : Nat} (hd : d + 8 ≤ 8192) : Stable X s (.mem (sc d)) (word s.mem base d) :=
  fun t hg hm _ hwr => by
    rw [← hm]
    exact readSrc_sc ⟨(hg _ hX).trans hs.rdi, hwr ▸ hs.wr, hs.nowrap⟩ hd

/-! ## Memory outside a range -/

/-- The offset of `x` from `base`. -/
abbrev ofs (base x : Addr) : Nat := (x - base).toNat

theorem ofs_off (base : Addr) {d i : Nat} (h : d + i < 2 ^ 64) :
    ofs base (off base d + BitVec.ofNat 64 i) = d + i := by
  simp only [ofs, off]
  rw [Offset.add_add, Mem.sub_ofNat_toNat base h]

theorem ofs_off' (base : Addr) {d : Nat} (h : d < 2 ^ 64) : ofs base (off base d) = d :=
  Mem.sub_ofNat_toNat base h

/-- `m'` agrees with `m` but on the bytes at offsets `[o, o + n)` of `base`. -/
def Outside (base : Addr) (o n : Nat) (m m' : Mem) : Prop :=
  ∀ x, (ofs base x < o ∨ o + n ≤ ofs base x) → m' x = m x

theorem Outside.refl (base : Addr) (o n : Nat) (m : Mem) : Outside base o n m m := fun _ _ => rfl

theorem Outside.trans {base : Addr} {o n : Nat} {m₁ m₂ m₃ : Mem} (h₁ : Outside base o n m₁ m₂)
    (h₂ : Outside base o n m₂ m₃) : Outside base o n m₁ m₃ :=
  fun x hx => (h₂ x hx).trans (h₁ x hx)

theorem Outside.mono {base : Addr} {o n o' n' : Nat} {m m' : Mem} (h : Outside base o n m m')
    (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n') : Outside base o' n' m m' :=
  fun x hx => h x (by omega)

/-- A word at an offset outside the bytes that changed. -/
theorem Outside.word {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 8 ≤ o ∨ o + n ≤ d) (hd' : d + 8 < 2 ^ 64) : word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside.mv {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') :
    ∀ {d k : Nat}, (d + 8 * k ≤ o ∨ o + n ≤ d) → d + 8 * k < 2 ^ 64 →
      mv m' base d k = mv m base d k
  | _, 0, _, _ => rfl
  | d, k + 1, hd, hd' => by
    simp only [X86_64.mv]
    rw [h.word (by omega) (by omega), h.mv (d := d + 8) (k := k) (by omega) (by omega)]

theorem Outside.fe {base : Addr} {o n : Nat} {m m' : Mem} (h : Outside base o n m m') {d : Nat}
    (hd : d + 56 ≤ o ∨ o + n ≤ d) (hd' : d + 56 < 2 ^ 64) : fe m' base d = fe m base d :=
  h.mv (by omega) (by omega)

theorem writeW_outside (m : Mem) (base : Addr) {d : Nat} (v : BitVec 64) (h : d + 8 < 2 ^ 64) :
    Outside base d 8 m (m.writeW (off base d) v) := by
  intro x hx
  simp only [Mem.writeW]
  apply Mem.write_apply
  rw [Offset.lt_iff x base (by omega)]
  simp only [ofs] at hx
  omega

theorem word_writeW_self (m : Mem) (base : Addr) (d : Nat) (v : BitVec 64) :
    word (m.writeW (off base d) v) base d = v := Mem.readW_writeW_self64 _ _ _

/-- Memory outside two ranges. -/
def Outside2 (base : Addr) (x nx y ny : Nat) (m m' : Mem) : Prop :=
  ∀ p, (ofs base p < x ∨ x + nx ≤ ofs base p) →
    (ofs base p < y ∨ y + ny ≤ ofs base p) → m' p = m p

theorem Outside2.refl (base : Addr) (x nx y ny : Nat) (m : Mem) : Outside2 base x nx y ny m m :=
  fun _ _ _ => rfl

theorem Outside2.trans {base : Addr} {x nx y ny : Nat} {m₁ m₂ m₃ : Mem}
    (h₁ : Outside2 base x nx y ny m₁ m₂) (h₂ : Outside2 base x nx y ny m₂ m₃) :
    Outside2 base x nx y ny m₁ m₃ := fun p hx hy => (h₂ p hx hy).trans (h₁ p hx hy)

theorem Outside.left {base : Addr} {x nx : Nat} {m m' : Mem} (h : Outside base x nx m m')
    (y ny : Nat) : Outside2 base x nx y ny m m' := fun p hp _ => h p hp

theorem Outside.right {base : Addr} {y ny : Nat} {m m' : Mem} (h : Outside base y ny m m')
    (x nx : Nat) : Outside2 base x nx y ny m m' := fun p _ hp => h p hp

theorem Outside2.word {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m')
    {d : Nat} (hx : d + 8 ≤ x ∨ x + nx ≤ d) (hy : d + 8 ≤ y ∨ y + ny ≤ d) (hd : d + 8 < 2 ^ 64) :
    word m' base d = word m base d :=
  (Mem.readW_congr fun i hi => (h _ (by rw [ofs_off base (by omega)]; omega)
    (by rw [ofs_off base (by omega)]; omega)).symm).symm

theorem Outside2.mv {base : Addr} {x nx y ny : Nat} {m m' : Mem} (h : Outside2 base x nx y ny m m') :
    ∀ {d k : Nat}, (d + 8 * k ≤ x ∨ x + nx ≤ d) → (d + 8 * k ≤ y ∨ y + ny ≤ d) →
      d + 8 * k < 2 ^ 64 → mv m' base d k = mv m base d k
  | _, 0, _, _, _ => rfl
  | d, k + 1, hx, hy, hd' => by
    simp only [X86_64.mv]
    rw [h.word (by omega) (by omega) (by omega),
      h.mv (d := d + 8) (k := k) (by omega) (by omega) (by omega)]

theorem Outside2.outside {base : Addr} {x nx y ny : Nat} {m m' : Mem}
    (h : Outside2 base x nx y ny m m') {o n : Nat} (hx : o ≤ x) (hx' : x + nx ≤ o + n) (hy : o ≤ y)
    (hy' : y + ny ≤ o + n) : Outside base o n m m' :=
  fun p hp => h p (by omega) (by omega)

end VG.Proof.X448.X86_64
