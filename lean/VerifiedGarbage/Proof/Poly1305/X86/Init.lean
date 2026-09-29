import VerifiedGarbage.Proof.Poly1305.X86.Blocks

/-!
# Poly1305 on x86 (32-bit): `init`

Untrusted: everything here is checked by Lean.
-/

namespace VG.Proof.Poly1305.X86

open VG VG.X86 VG.Impl.Poly1305.X86
open VG.Spec.Poly1305 (P clamp leNum bytesAt accumulate Repr)

section
variable (s₀ : State)
/-- The key, on entry. -/
abbrev kp : BitVec 32 := arg s₀ 1
end

structure IPre (s₀ : State) : Prop where
  rd : s₀.rd = [⟨(kp s₀).setWidth 64, 32⟩, ⟨argAddr s₀ 0, 8⟩]
  wr : s₀.wr = [sR (stp s₀)]
  st_key : (sR (stp s₀)).Disjoint ⟨(kp s₀).setWidth 64, 32⟩
  arg_st : Region.Disjoint ⟨argAddr s₀ 0, 8⟩ (sR (stp s₀))
  ret_st : (retR s₀).Disjoint (sR (stp s₀))
  st_fit : (stp s₀).toNat + 128 ≤ 2 ^ 32
  key_fit : (kp s₀).toNat + 32 ≤ 2 ^ 32
  sp_fit : (s₀.gpr .esp).toNat + 12 ≤ 2 ^ 32

theorem IPre.of (s₀ : State) (h : Proof.Poly1305.initX86.pre s₀) : IPre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- The key's word `j`. -/
theorem key_contains {kp : BitVec 32} (hfit : kp.toNat + 32 ≤ 2 ^ 32) {j : Nat} (hj : j < 8) :
    (⟨kp.setWidth 64, 32⟩ : Region).Contains (addr kp (4 * j)) 4 := by
  have := sub_contains (x := kp) (a := 0) (k := 32) (d := 4 * j) (n := 4) (by omega) (by omega) (by omega)
    (by omega)
  simpa [sub, addr] using this

/-- After copying the words below `j` of the key. -/
structure KInv (s₀ : State) (j : Nat) (s : State) : Prop where
  eax : s.gpr .eax = stp s₀
  ecx : s.gpr .ecx = kp s₀
  esp : s.gpr .esp = s₀.gpr .esp
  others : ∀ r, r ≠ .eax → r ≠ .ecx → r ≠ .edx → s.gpr r = s₀.gpr r
  rd : s.rd = s₀.rd
  wr : s.wr = s₀.wr
  frame : Frame [sR (stp s₀)] s₀.mem s.mem
  words : ∀ k < j, wd s.mem (stp s₀) (24 + 4 * k) = wd s₀.mem (kp s₀) (4 * k)

theorem copyWord_ok {s₀ : State} (hp : IPre s₀) {j : Nat} (hj : j < 8) {s : State} (h : KInv s₀ j s) :
    WP isa (.block [.mov .edx (.mem (at_ .ecx (4 * j))), .store (at_ .eax (24 + 4 * j)) .edx]) s
      (KInv s₀ (j + 1)) := by
  have hfit := hp.st_fit
  have hin : InRegions (s.rd ++ s.wr) (addr (kp s₀) (4 * j)) 4 :=
    ⟨_, by rw [h.rd, hp.rd]; simp, key_contains hp.key_fit hj⟩
  refine wp_movm (a := addr (kp s₀) (4 * j)) (by rw [ea_at, h.ecx]) hin fun s₁ u₁ _ => ?_
  refine wp_store (a := addr (stp s₀) (24 + 4 * j)) (by rw [ea_at, u₁.other _ (by decide), h.eax])
    (by rw [u₁.wr, h.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, sR_contains hfit (by omega) (by omega)⟩)
    fun s₂ u₂ => WP.block_nil ⟨?_, ?_, ?_, fun r h₁ h₂ h₃ => ?_, ?_, ?_, ?_, fun k hk => ?_⟩
  · rw [u₂.gpr, u₁.other _ (by decide), h.eax]
  · rw [u₂.gpr, u₁.other _ (by decide), h.ecx]
  · rw [u₂.gpr, u₁.other _ (by decide), h.esp]
  · rw [u₂.gpr, u₁.other r h₃, h.others r h₁ h₂ h₃]
  · rw [u₂.rd, u₁.rd, h.rd]
  · rw [u₂.wr, u₁.wr, h.wr]
  · rw [u₂.mem, u₁.mem]; exact h.frame.trans (frame_write (Frame.refl _ _) hfit (by omega) _)
  · have hkey : wd s.mem (kp s₀) (4 * j) = wd s₀.mem (kp s₀) (4 * j) :=
      wd_frame h.frame (by simpa using (hp.st_key.sub_right (fun a ha => by
        have := key_contains hp.key_fit hj
        simp only [Region.Contains] at ha this ⊢
        have : (a - (kp s₀).setWidth 64).toNat ≤ (a - addr (kp s₀) (4 * j)).toNat +
            (addr (kp s₀) (4 * j) - (kp s₀).setWidth 64).toNat := by
          rw [show a - (kp s₀).setWidth 64 = (a - addr (kp s₀) (4 * j)) +
            (addr (kp s₀) (4 * j) - (kp s₀).setWidth 64) by bv_omega, BitVec.toNat_add]
          exact Nat.mod_le _ _
        omega)).symm)
    rw [u₂.mem, u₁.mem, u₁.gpr]
    by_cases e : k = j
    · subst e; rw [wd_write_self]; exact hkey
    · rw [wd_write_ne _ _ (by omega) (by omega) (by omega)]; exact h.words k (by omega)


theorem copies_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : KInv s₀ 0 s) :
    ∀ n ≤ 8, WP isa (.block ((List.range n).flatMap fun j =>
      [.mov .edx (.mem (at_ .ecx (4 * j))), .store (at_ .eax (24 + 4 * j)) .edx])) s (KInv s₀ n) := by
  intro n hn
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    exact WP.block_append (WP.mono (ih (by omega)) fun s₁ h₁ => copyWord_ok hp (by omega) h₁)

/-- After zeroing the words below `j` of the accumulator. -/
structure ZInv (s₀ : State) (j : Nat) (s : State) : Prop extends KInv s₀ 8 s where
  edx : s.gpr .edx = 0
  zeros : ∀ k < j, wd s.mem (stp s₀) (4 * k) = 0

theorem zeros_ok {s₀ : State} (hp : IPre s₀) {s : State} (h : ZInv s₀ 0 s) :
    ∀ n ≤ 6, WP isa (.block ((List.range n).map fun j => .store (at_ .eax (4 * j)) .edx)) s
      (ZInv s₀ n) := by
  have hfit := hp.st_fit
  intro n hn
  induction n with
  | zero => exact WP.block_nil h
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_singleton]
    refine WP.block_append (WP.mono (ih (by omega)) fun s₁ h₁ => ?_)
    refine wp_store (a := addr (stp s₀) (4 * n)) (by rw [ea_at, h₁.eax])
      (by rw [h₁.wr, hp.wr]; exact ⟨_, List.mem_singleton_self _, sR_contains hfit (by omega) (by omega)⟩)
      fun s₂ u₂ => WP.block_nil ⟨⟨?_, ?_, ?_, fun r a b c => ?_, ?_, ?_, ?_, fun k hk => ?_⟩, ?_,
        fun k hk => ?_⟩
    · rw [u₂.gpr]; exact h₁.eax
    · rw [u₂.gpr]; exact h₁.ecx
    · rw [u₂.gpr]; exact h₁.esp
    · rw [u₂.gpr]; exact h₁.others r a b c
    · rw [u₂.rd]; exact h₁.rd
    · rw [u₂.wr]; exact h₁.wr
    · rw [u₂.mem]; exact h₁.frame.trans (frame_write (Frame.refl _ _) hfit (by omega) _)
    · rw [u₂.mem, wd_write_ne _ _ (by omega) (by omega) (by omega)]; exact h₁.words k hk
    · rw [u₂.gpr]; exact h₁.edx
    · rw [u₂.mem]
      by_cases e : k = n
      · subst e; rw [wd_write_self, h₁.edx]
      · rw [wd_write_ne _ _ (by omega) (by omega) (by omega)]; exact h₁.zeros k (by omega)

theorem init_eq : init = .block (.mov .eax (.mem (at_ .esp 4)) :: .mov .ecx (.mem (at_ .esp 8)) ::
    ((List.range 8).flatMap (fun j => [.mov .edx (.mem (at_ .ecx (4 * j))),
      .store (at_ .eax (24 + 4 * j)) .edx]) ++
    (.mov .edx (.imm 0) :: (List.range 6).map fun j => .store (at_ .eax (4 * j)) .edx))) := by
  simp only [init, List.append_assoc, List.cons_append, List.nil_append]

theorem init_correct {s₀ : State} (hp : IPre s₀) :
    WP isa init s₀ fun s' => abiPreserved s₀ s' ∧ Proof.Poly1305.initX86.post s₀ s' := by
  have hfit := hp.st_fit
  have harg : ∀ i, i < 2 → InRegions (s₀.rd ++ s₀.wr) (addr (s₀.gpr .esp) (4 + 4 * i)) 4 := fun i hi =>
    ⟨⟨argAddr s₀ 0, 8⟩, by rw [hp.rd]; simp, arg_contains (n := 8) (by have := hp.sp_fit; omega)
      (by omega)⟩
  rw [init_eq]
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 0)) (ea_at _ _ _) (harg 0 (by omega)) fun s₁ u₁ _ => ?_
  refine wp_movm (a := addr (s₀.gpr .esp) (4 + 4 * 1)) (by rw [ea_at, u₁.other _ (by decide)])
    (by rw [u₁.rd, u₁.wr]; exact harg 1 (by omega)) fun s₂ u₂ _ => ?_
  have k₀ : KInv s₀ 0 s₂ := ⟨by rw [u₂.other _ (by decide), u₁.gpr]; rfl, by rw [u₂.gpr, u₁.mem]; rfl,
    by rw [u₂.other _ (by decide), u₁.other _ (by decide)], fun r a b _ => by rw [u₂.other r b, u₁.other r a],
    by rw [u₂.rd, u₁.rd], by rw [u₂.wr, u₁.wr], by rw [u₂.mem, u₁.mem]; exact Frame.refl _ _,
    fun k hk => absurd hk (by omega)⟩
  refine WP.block_append (WP.mono (copies_ok hp k₀ 8 (Nat.le_refl _)) fun s₃ k₃ => ?_)
  refine wp_movi fun s₄ u₄ _ => ?_
  have z₀ : ZInv s₀ 0 s₄ := ⟨⟨by rw [u₄.other _ (by decide)]; exact k₃.eax,
    by rw [u₄.other _ (by decide)]; exact k₃.ecx, by rw [u₄.other _ (by decide)]; exact k₃.esp,
    fun r a b c => by rw [u₄.other r c]; exact k₃.others r a b c, by rw [u₄.rd]; exact k₃.rd,
    by rw [u₄.wr]; exact k₃.wr, by rw [u₄.mem]; exact k₃.frame, fun k hk => by rw [u₄.mem]; exact k₃.words k hk⟩,
    u₄.gpr, fun k hk => absurd hk (by omega)⟩
  refine WP.mono (zeros_ok hp z₀ 6 (Nat.le_refl _)) fun s₅ z₅ => ⟨⟨fun r hr => ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp only [calleeSaved, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    all_goals exact z₅.others _ (by decide) (by decide) (by decide)
  · exact z₅.frame.readW (Region.contains_self _ _) (by simpa using hp.ret_st) (by decide)
  · simp
  · show bytesAt s₅.mem ((stp s₀).setWidth 64 + 24) (4 * 8) = bytesAt s₀.mem ((kp s₀).setWidth 64) (4 * 8)
    refine bytesAt_congr_words2 fun k hk => ?_
    have := z₅.words k hk
    simp only [wd] at this
    rw [show (24 : Addr) = BitVec.ofNat 64 24 from rfl, add_ofNat_add, ← addr_eq (by omega),
      ← addr_eq (by have := hp.key_fit; omega)]
    exact this
  · rw [leNum_bytesAt_24]
    have e : ∀ k < 6, w32 s₅.mem ((stp s₀).setWidth 64) k = 0 := fun k hk => by
      rw [w32_eq hfit (by omega), wv, z₅.zeros k hk]; rfl
    rw [e 0 (by omega), e 1 (by omega), e 2 (by omega), e 3 (by omega), e 4 (by omega), e 5 (by omega)]
    rfl

/-! ## Constant time and satisfiability -/

def initτ₀ : VG.X86.Taint.T :=
  { regs := .ofList [.esp], flags := false, lens := [128], argLen := 12, argBases := [(4, 0)] }

theorem init_wf₀ {s : State} (hp : IPre s) : VG.X86.Taint.Wf initτ₀ s := by
  have hst := hp.st_fit; have hs := hp.sp_fit
  refine VG.X86.Taint.Wf.entry rfl rfl ⟨fun _ => ⟨by simp [hp.wr, initτ₀], by simp [hp.wr], ?_⟩,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim,
    fun _ => ⟨hs, ?_⟩, ?_⟩
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl; simp only [BitVec.toNat_setWidth]; omega
  · simp only [hp.wr, List.mem_singleton]
    rintro r rfl
    exact VG.X86.Taint.frame_disjoint (n := 8) (by omega) hp.ret_st hp.arg_st
  · intro p hp'
    simp only [initτ₀, List.mem_singleton] at hp'
    subst hp'
    refine ⟨by decide, ?_⟩
    simp [VG.X86.Taint.region, hp.wr, addr, arg, argAddr]

theorem init_agree₀ {s₁ s₂ : State} (h₁ : Proof.Poly1305.initX86.pre s₁)
    (h₂ : Proof.Poly1305.initX86.pre s₂) (hpub : Proof.Poly1305.initX86.pub s₁ s₂) :
    VG.X86.Taint.Agree initτ₀ s₁ s₂ := by
  obtain ⟨hesp, a0, a1⟩ := hpub
  have hp₁ := IPre.of _ h₁; have hp₂ := IPre.of _ h₂
  refine ⟨⟨fun r hr => ?_, fun h => nomatch h⟩, fun _ => ?_, init_wf₀ hp₁, init_wf₀ hp₂,
    fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim, fun _ => hesp,
    fun k h4 hk => (Nat.zero_add k).symm ▸ argMem_eq hp₁.sp_fit hp₂.sp_fit (fun i hi => ?_) h4 hk⟩
  · simp only [initτ₀, RegSet.mem_ofList, List.mem_singleton] at hr
    subst hr; exact hesp
  · rw [hp₁.wr, hp₂.wr]; simp only [stp, a0]
  · have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl
    exacts [a0, a1]

/-- Memory holding the arguments `0x1000, 0x2000` at `0x4004`. -/
def initSatMem : Mem := fun a => if a = 0x4005 then 0x10 else if a = 0x4009 then 0x20 else 0

/-- A state satisfying the precondition. -/
def initSat : State where
  gpr r := match r with
    | .esp => 0x4000 | _ => 0
  cf := none
  zf := none
  sf := none
  of := none
  mem := initSatMem
  rd := [⟨0x2000, 32⟩, ⟨0x4004, 8⟩]
  wr := [⟨0x1000, 128⟩]

theorem initSat_pre : Proof.Poly1305.initX86.pre initSat := by
  have a0 : arg initSat 0 = 0x1000 := by decide
  have a1 : arg initSat 1 = 0x2000 := by decide
  have e : argAddr initSat 0 = 0x4004 := by decide
  simp only [Proof.Poly1305.initX86, a0, a1, e]
  refine ⟨rfl, rfl, ?_, ?_, ?_, by decide, by decide, by decide⟩ <;>
  · intro a h₁ h₂
    simp only [Region.Contains, initSat] at h₁ h₂
    bv_omega

theorem init_verified : Verified X86.target init Proof.Poly1305.initX86 :=
  ⟨fun s hs => init_correct (IPre.of s hs),
    VG.Taint.constantTime (A := taint) initτ₀ (fun _ _ h₁ h₂ hp => init_agree₀ h₁ h₂ hp)
      (by taint_decide),
    ⟨initSat, initSat_pre⟩⟩

end VG.Proof.Poly1305.X86
