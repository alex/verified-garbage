import VerifiedGarbage.Proof.Poly1305.Arm.Common

/-!
# Poly1305 on 32-bit ARM: runs of stores and loads

Untrusted: everything here is checked by Lean. A run of stores of registers
(words, or bytes) at distinct offsets from a base register (`stores_ok`),
and a run of loads (`loads_ok`).
-/

namespace VG.Proof.Poly1305.Arm

open VG VG.Arm VG.Impl.Poly1305.Arm

/-- The store of register `r` at `[b, #o]`: a word, or a byte if `byte`. -/
def storeI (b : Reg) : Reg × Nat × Bool → Instr
  | (r, o, false) => .str r b o
  | (r, o, true) => .strb r b o

/-- The size of a store. -/
def ssize : Bool → Nat
  | false => 4
  | true => 1

/-- The bytes a store writes. -/
def sregion (B : Addr) (x : Reg × Nat × Bool) : Region := ⟨B + BitVec.ofNat 64 x.2.1, ssize x.2.2⟩

/-- What a store leaves in memory: register `r`'s value, or its low byte, at `B + o`. -/
def Stored (B : Addr) (g : Reg → BitVec 32) (m : Mem) : Reg × Nat × Bool → Prop
  | (r, o, false) => m.readW (B + BitVec.ofNat 64 o) 32 = g r
  | (r, o, true) => m (B + BitVec.ofNat 64 o) = (g r).setWidth 8

/-- Two stores' bytes do not overlap. -/
def Apart (x y : Reg × Nat × Bool) : Prop := x.2.1 + ssize x.2.2 ≤ y.2.1 ∨ y.2.1 + ssize y.2.2 ≤ x.2.1

instance (x y : Reg × Nat × Bool) : Decidable (Apart x y) := by unfold Apart; infer_instance

theorem sregion_disjoint (B : Addr) {x y : Reg × Nat × Bool} (h : Apart x y) (hx : x.2.1 < 2 ^ 32)
    (hy : y.2.1 < 2 ^ 32) : (sregion B x).Disjoint (sregion B y) := by
  obtain ⟨_, o, b⟩ := x
  obtain ⟨_, o', b'⟩ := y
  simp only [Apart] at h hx hy
  intro a h₁ h₂
  simp only [sregion, Region.Contains] at h₁ h₂
  cases b <;> cases b' <;> simp only [ssize] at h h₁ h₂ <;> bv_omega

theorem Stored.frame {B : Addr} {g : Reg → BitVec 32} {m m' : Mem} {x : Reg × Nat × Bool}
    (h : Stored B g m x) {F : List Region} (hf : Frame F m m')
    (hd : ∀ r ∈ F, (sregion B x).Disjoint r) : Stored B g m' x := by
  obtain ⟨r, o, b⟩ := x
  cases b
  · simp only [Stored] at h ⊢
    rw [hf.readW (Region.contains_self _ _) hd (by decide)]; exact h
  · simp only [Stored] at h ⊢
    rw [hf _ fun r' hr' hc => hd r' hr' _ (by simp [sregion, Region.Contains, ssize]) hc]; exact h

theorem stores_ok (b : Reg) {B : Addr} {bv : BitVec 32} {len : Nat} (hfit : bv.toNat + len ≤ 2 ^ 32)
    (hB : B = State.addr bv) : ∀ (l : List (Reg × Nat × Bool)) (s : State),
    s.gpr b = bv → (⟨B, len⟩ : Region) ∈ s.wr → (∀ x ∈ l, x.2.1 + ssize x.2.2 ≤ len ∧ x.2.1 < 4096) →
    l.Pairwise Apart →
    WP isa (.block (l.map (storeI b))) s fun s' =>
      (∀ x ∈ l, Stored B s.gpr s'.mem x) ∧ Frame (l.map (sregion B)) s.mem s'.mem ∧
        s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp
  | [], s, _, _, _, _ => WP.block_nil ⟨fun _ h => absurd h List.not_mem_nil, Frame.refl _ _, rfl, rfl, rfl, rfl⟩
  | x :: xs, s, hb, hw, hl, hp => by
    obtain ⟨r, o, byte⟩ := x
    have ⟨hlo, ho⟩ := hl _ List.mem_cons_self
    simp only at hlo ho
    have h1s : 1 ≤ ssize byte := by cases byte <;> simp [ssize]
    have ha : State.addr (s.gpr b + BitVec.ofNat 32 o) = B + BitVec.ofNat 64 o := by
      rw [hb, hB]; exact addr_add (by omega)
    have hc : (⟨B, len⟩ : Region).Contains (B + BitVec.ofNat 64 o) (ssize byte) :=
      contains_off hlo (by omega)
    have hp' := List.pairwise_cons.mp hp
    have rest : ∀ s1 : State, Mupd s s1 (s1.mem) → Stored B s.gpr s1.mem (r, o, byte) →
        Frame [sregion B (r, o, byte)] s.mem s1.mem →
        WP isa (.block (xs.map (storeI b))) s1 fun s' =>
          (∀ x ∈ (r, o, byte) :: xs, Stored B s.gpr s'.mem x) ∧
          Frame (((r, o, byte) :: xs).map (sregion B)) s.mem s'.mem ∧
          s'.gpr = s.gpr ∧ s'.rd = s.rd ∧ s'.wr = s.wr ∧ s'.sp = s.sp := by
      intro s1 u1 hst hf1
      refine WP.mono (stores_ok b hfit hB xs s1 (by rw [u1.gpr, hb]) (by rw [u1.wr]; exact hw)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy)) hp'.2) fun s' ⟨hs', hf', hg', hrd', hwr', hsp'⟩ =>
        ⟨fun y hy => ?_, ?_, hg'.trans u1.gpr, hrd'.trans u1.rd, hwr'.trans u1.wr, hsp'.trans u1.sp⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · refine hst.frame hf' fun q hq => ?_
          obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
          exact sregion_disjoint B (hp'.1 z hz) (by simp only; omega)
            (by have := hl z (List.mem_cons_of_mem _ hz); omega)
        · rw [← u1.gpr]; exact hs' y hy
      · simp only [List.map_cons]
        refine (hf1.mono fun q hq => by simp at hq; simp [hq]).trans (hf'.mono fun q hq => by simp [hq])
    cases byte
    · refine wp_str (a := B + BitVec.ofNat 64 o) (by omega) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp⟩ ?_ ?_
      · simp only [Stored]; rw [u1.mem, Mem.readW_writeW_self32]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)
    · refine wp_strb (a := B + BitVec.ofNat 64 o) (by omega) ha ⟨_, hw, hc⟩ fun s1 u1 => rest s1
        ⟨u1.gpr, rfl, u1.rd, u1.wr, u1.sp⟩ ?_ ?_
      · simp only [Stored]; rw [u1.mem]
        simp [Mem.writeW, Mem.write]
      · rw [u1.mem]; exact (Frame.refl _ _).writeW (List.mem_singleton_self _) _ (Region.contains_self _ _)

end VG.Proof.Poly1305.Arm
