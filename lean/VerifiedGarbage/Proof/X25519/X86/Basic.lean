import VerifiedGarbage.Proof.Framework.X86.Exec
import VerifiedGarbage.Proof.Framework.X86.RegUpd
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.Offset
import VerifiedGarbage.Proof.Framework.Omega
import VerifiedGarbage.Impl.X25519.X86

/-!
# X25519 on x86 (32-bit): words of the working space

Untrusted: everything here is checked by Lean. The working space, 4096 bytes
at `x` (`edi` in the code), holds words at constant offsets; a field element
is eight of them (`fe`). A store to a word leaves the others unchanged, and
code that stores only to some regions of it leaves the rest of memory
unchanged (`Frame`).
-/

namespace VG.Proof.X25519.X86

open VG VG.X86 VG.Impl.X25519.X86

/-- The value of a register, as a number. -/
abbrev v (s : State) (r : Reg) : Nat := (s.gpr r).toNat

/-- The 32-bit word at `[x + d]`. -/
abbrev wd (m : Mem) (x : BitVec 32) (d : Nat) : BitVec 32 := m.readW (addr x d) 32

/-- The same, as a number. -/
abbrev wv (m : Mem) (x : BitVec 32) (d : Nat) : Nat := (wd m x d).toNat

/-- The number of the words `f 0, …, f (n - 1)`, in radix `2³²`. -/
def num (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => num f n + (2 ^ 32) ^ n * f n

/-- The eight words of a field element at `[x + o]`, as a number. -/
def fe (m : Mem) (x : BitVec 32) (o : Nat) : Nat := num (fun k => wv m x (o + 4 * k)) 8

/-- The region of `n` bytes at `[x + d]`. -/
abbrev sub (x : BitVec 32) (d n : Nat) : Region := ⟨addr x d, n⟩

/-- The working space. -/
abbrev scR (x : BitVec 32) : Region := ⟨x.setWidth 64, 4096⟩

theorem ea_at (s : State) (b : Reg) (d : Nat) : s.ea (at_ b d) = addr (s.gpr b) d := rfl

theorem addr_zero (x : BitVec 32) : addr x 0 = x.setWidth 64 := by simp [addr]

theorem sub_contains {x : BitVec 32} {a k d n : Nat} (hx : x.toNat + a + k ≤ 2 ^ 32) (h₁ : a ≤ d)
    (h₂ : d + n ≤ a + k) (hn : 0 < n) : (sub x a k).Contains (addr x d) n := by
  rw [sub, addr_eq (by omega_using [hx, h₁, h₂, hn]), addr_eq (by omega_using [hx, h₂, hn])]
  exact Offset.contains _ h₁ h₂ (by omega_using [hx])

theorem sub_disj {x : BitVec 32} {d n e k : Nat} (hd : x.toNat + d + n ≤ 2 ^ 32)
    (he : x.toNat + e + k ≤ 2 ^ 32) (h : d + n ≤ e ∨ e + k ≤ d) : (sub x d n).Disjoint (sub x e k) := by
  intro a h₁ h₂
  simp only [Region.Contains] at h₁ h₂
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) h₁
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) h₂
  rw [addr_eq (by omega_using [hd, hn])] at h₁
  rw [addr_eq (by omega_using [he, hk])] at h₂
  exact Offset.disjoint _ h (by omega_using [hd]) (by omega_using [he]) a h₁ h₂

theorem scR_eq (x : BitVec 32) : scR x = sub x 0 4096 := by rw [sub, addr_zero]

theorem scR_contains {x : BitVec 32} (hx : x.toNat + 4096 ≤ 2 ^ 32) {d n : Nat} (h : d + n ≤ 4096)
    (hn : 0 < n) : (scR x).Contains (addr x d) n := by
  rw [scR_eq]; exact sub_contains (by omega_using [hx]) (Nat.zero_le d) (by omega_using [h]) hn

/-- The 32-bit word at `[x + d]`, after a store at `[x + e]` that does not overlap it. -/
theorem wd_write_ne (m : Mem) {x : BitVec 32} (w : BitVec 32) {d e : Nat}
    (hd : x.toNat + d + 4 ≤ 2 ^ 32) (he : x.toNat + e + 4 ≤ 2 ^ 32) (h : d + 4 ≤ e ∨ e + 4 ≤ d) :
    wd (m.writeW (addr x e) w) x d = wd m x d :=
  Mem.readW_writeW_sep ((sub_disj hd he h).sep (Region.contains_self _ _) (Region.contains_self _ _))
    (by decide)

theorem wd_write_self (m : Mem) (x : BitVec 32) (w : BitVec 32) (d : Nat) :
    wd (m.writeW (addr x d) w) x d = w :=
  Mem.readW_writeW_self32 _ _ _

/-- A word outside the regions a frame allows to change. -/
theorem wd_frame {rs : List Region} {m m' : Mem} (hf : Frame rs m m') {x : BitVec 32} {d : Nat}
    (hd : ∀ r ∈ rs, (sub x d 4).Disjoint r) : wd m' x d = wd m x d :=
  hf.readW (Region.contains_self _ _) hd (by decide)

/-- A word of the working space outside a frame's region `[x + o, x + o + n)`. -/
theorem wd_frame1 {m m' : Mem} {x : BitVec 32} {o n d : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) (hd : d + 4 ≤ 4096) (h : d + 4 ≤ o ∨ o + n ≤ d) :
    wd m' x d = wd m x d :=
  wd_frame hf fun r hr => by
    rw [List.mem_singleton.mp hr]
    exact sub_disj (by omega_using [hx, hd]) (by omega_using [hx, ho]) h

/-- Stores into a frame's region. -/
theorem frame_write1 {m m' : Mem} {x : BitVec 32} {o n : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) {d : Nat} (h₁ : o ≤ d) (h₂ : d + 4 ≤ o + n)
    (w : BitVec 32) : Frame [sub x o n] m (m'.writeW (addr x d) w) :=
  hf.writeW (List.mem_singleton_self _) _
    (sub_contains (by omega_using [hx, ho]) h₁ h₂ (by decide))

/-- A region of the working space within another. -/
theorem sub_sub {x : BitVec 32} {o n o' n' : Nat} (hx : x.toNat + 4096 ≤ 2 ^ 32) (h₁ : o' ≤ o)
    (h₂ : o + n ≤ o' + n') (hn : o < 4096) : Region.Sub (sub x o n) (sub x o' n') := by
  rw [sub, sub, addr_eq (by omega_using [hx, hn]), addr_eq (by omega_using [hx, h₁, hn])]
  exact Offset.sub _ h₁ h₂

/-- A frame of a region is one of any region containing it. -/
theorem frameWiden {m m' : Mem} {x : BitVec 32} {o n o' n' : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (h₁ : o' ≤ o) (h₂ : o + n ≤ o' + n')
    (hn : o < 4096) : Frame [sub x o' n'] m m' :=
  hf.sub fun _ hr => ⟨_, List.mem_singleton_self _, List.mem_singleton.mp hr ▸ sub_sub hx h₁ h₂ hn⟩

/-- The code's view of the working space: `edi` points at it, it is
writable, and it does not wrap around the 32-bit address space. -/
structure Ctx (x : BitVec 32) (s : State) : Prop where
  edi : s.gpr .edi = x
  fit : x.toNat + 4096 ≤ 2 ^ 32
  wr : scR x ∈ s.wr

namespace Ctx
variable {x : BitVec 32} {s : State} (h : Ctx x s)
include h

theorem inW {d n : Nat} (hd : d + n ≤ 4096) (hn : 0 < n) : InRegions s.wr (addr x d) n :=
  ⟨_, h.wr, scR_contains h.fit hd hn⟩

theorem inRW {d n : Nat} (hd : d + n ≤ 4096) (hn : 0 < n) :
    InRegions (s.rd ++ s.wr) (addr x d) n :=
  ⟨_, List.mem_append_right _ h.wr, scR_contains h.fit hd hn⟩

/-- The context survives a change of other registers and of memory. -/
theorem keep {s' : State} (he : s'.gpr .edi = s.gpr .edi) (hw : s'.wr = s.wr) : Ctx x s' :=
  ⟨he.trans h.edi, h.fit, hw ▸ h.wr⟩

end Ctx

/-- What the arithmetic keeps: the counter `esi`, the base `edi`, `esp` and
the regions. -/
structure Keep (s s' : State) : Prop where
  esi : s'.gpr .esi = s.gpr .esi
  edi : s'.gpr .edi = s.gpr .edi
  esp : s'.gpr .esp = s.gpr .esp
  rd : s'.rd = s.rd
  wr : s'.wr = s.wr

theorem Keep.refl (s : State) : Keep s s := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {s₁ s₂ s₃ : State} (h₁ : Keep s₁ s₂) (h₂ : Keep s₂ s₃) : Keep s₁ s₃ :=
  ⟨h₂.esi.trans h₁.esi, h₂.edi.trans h₁.edi, h₂.esp.trans h₁.esp, h₂.rd.trans h₁.rd,
    h₂.wr.trans h₁.wr⟩

theorem Keep.ctx {x : BitVec 32} {s s' : State} (h : Keep s s') (hc : Ctx x s) : Ctx x s' :=
  hc.keep h.edi h.wr

/-! ## Numbers of words -/

theorem num_succ (f : Nat → Nat) (n : Nat) : num f (n + 1) = num f n + (2 ^ 32) ^ n * f n := rfl

theorem num_congr {f g : Nat → Nat} {n : Nat} (h : ∀ k < n, f k = g k) : num f n = num g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [num_succ, num_succ, ih fun k hk => h k (by omega_using [hk]), h n (by omega_using [])]

theorem num_lt {f : Nat → Nat} {n : Nat} (h : ∀ k < n, f k < 2 ^ 32) : num f n < (2 ^ 32) ^ n := by
  induction n with
  | zero => simp [num]
  | succ n ih =>
    rw [num_succ]
    have h1 := ih fun k hk => h k (by omega_using [hk])
    have h2 : f n + 1 ≤ 2 ^ 32 := h n (by omega_using [])
    have h3 : (2 ^ 32) ^ n * (f n + 1) ≤ (2 ^ 32) ^ n * 2 ^ 32 := Nat.mul_le_mul_left _ h2
    rw [← Nat.pow_succ] at h3
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega_using [h1, h3]

theorem num_add (f g : Nat → Nat) (n : Nat) : num (fun k => f k + g k) n = num f n + num g n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [num_succ, num_succ, num_succ, ih, Nat.mul_add]; omega_using []

theorem num_mul (c : Nat) (f : Nat → Nat) (n : Nat) : num (fun k => c * f k) n = c * num f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [num_succ, num_succ, ih, Nat.mul_add, Nat.mul_left_comm]

theorem fe_lt (m : Mem) (x : BitVec 32) (o : Nat) : fe m x o < 2 ^ 256 :=
  num_lt (f := fun k => wv m x (o + 4 * k)) fun _ _ => BitVec.isLt _

/-- A field element's words are unchanged if their region is. -/
theorem fe_frame {m m' : Mem} {x : BitVec 32} {o : Nat} (h : ∀ k < 8, wd m' x (o + 4 * k) = wd m x (o + 4 * k)) :
    fe m' x o = fe m x o :=
  num_congr fun k hk => by show (wd m' x (o + 4 * k)).toNat = (wd m x (o + 4 * k)).toNat; rw [h k hk]

/-- A field element outside a frame's region. -/
theorem fe_frame1 {m m' : Mem} {x : BitVec 32} {o n q : Nat} (hf : Frame [sub x o n] m m')
    (hx : x.toNat + 4096 ≤ 2 ^ 32) (ho : o + n ≤ 4096) (hq : q + 32 ≤ 4096) (h : q + 32 ≤ o ∨ o + n ≤ q) :
    fe m' x q = fe m x q :=
  fe_frame fun k hk => wd_frame1 hf hx ho (by omega_using [hq, hk]) (by omega_using [h, hk])

end VG.Proof.X25519.X86
