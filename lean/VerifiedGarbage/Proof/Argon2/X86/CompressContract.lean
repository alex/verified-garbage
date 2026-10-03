import VerifiedGarbage.Proof.Argon2.X86.Words
import VerifiedGarbage.TCB.X86.Target

/-!
# Argon2 compression on x86 (32-bit): the contract of the proof

`compressX86`: the contract the proof is written against, with the arguments
on the stack only read; `Spec.Argon2.compressContract`, which lets the code
write them, is reached by narrowing (`Proof/Argon2/X86/CompressVerified.lean`).
`Pre` names the facts of its precondition.
-/

namespace VG.Proof.Argon2.X86

open VG VG.X86 VG.Spec.Argon2
open VG.Proof.Sha512.X86 (Acc mem_rd)
open VG.Proof.Sha256.X86.Stream (contains_addr)

/-- `vg_argon2_compress(x, y, out, scratch)`: reads the arguments (16 bytes
above the return address) and the two input blocks, writes the output block
and 4096 bytes of scratch. -/
def compressX86 : Contract X86.isa where
  pre s :=
    let x : Region := ⟨(arg s 0).setWidth 64, 1024⟩
    let y : Region := ⟨(arg s 1).setWidth 64, 1024⟩
    let out : Region := ⟨(arg s 2).setWidth 64, 1024⟩
    let scratch : Region := ⟨(arg s 3).setWidth 64, 4096⟩
    let args : Region := ⟨argAddr s 0, 16⟩
    let ret : Region := ⟨(s.gpr .esp).setWidth 64, 4⟩
    s.rd = [x, y, args] ∧ s.wr = [out, scratch] ∧
    out.Disjoint scratch ∧ x.Disjoint out ∧ x.Disjoint scratch ∧ y.Disjoint out ∧
    y.Disjoint scratch ∧ args.Disjoint out ∧ args.Disjoint scratch ∧ ret.Disjoint out ∧
    ret.Disjoint scratch ∧
    (arg s 0).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 1).toNat + 1024 ≤ 2 ^ 32 ∧
    (arg s 2).toNat + 1024 ≤ 2 ^ 32 ∧ (arg s 3).toNat + 4096 ≤ 2 ^ 32 ∧
    (s.gpr .esp).toNat + 20 ≤ 2 ^ 32
  post s s' := blockAt s'.mem ((arg s 2).setWidth 64) =
    compress (blockAt s.mem ((arg s 0).setWidth 64)) (blockAt s.mem ((arg s 1).setWidth 64))
  pub s₁ s₂ := s₁.gpr .esp = s₂.gpr .esp ∧ ∀ i < 4, arg s₁ i = arg s₂ i

section
variable (s₀ : State)

abbrev xp : BitVec 32 := arg s₀ 0
abbrev yp : BitVec 32 := arg s₀ 1
abbrev op : BitVec 32 := arg s₀ 2
abbrev scr : BitVec 32 := arg s₀ 3
abbrev esp₀ : BitVec 32 := s₀.gpr .esp
abbrev xR : Region := ⟨(xp s₀).setWidth 64, 1024⟩
abbrev yR : Region := ⟨(yp s₀).setWidth 64, 1024⟩
abbrev outR : Region := ⟨(op s₀).setWidth 64, 1024⟩
abbrev scrR : Region := ⟨(scr s₀).setWidth 64, 4096⟩
abbrev argR : Region := ⟨argAddr s₀ 0, 16⟩
abbrev retR : Region := ⟨(esp₀ s₀).setWidth 64, 4⟩

end

structure Pre (s₀ : State) : Prop where
  rd : s₀.rd = [xR s₀, yR s₀, argR s₀]
  wr : s₀.wr = [outR s₀, scrR s₀]
  out_scr : (outR s₀).Disjoint (scrR s₀)
  x_out : (xR s₀).Disjoint (outR s₀)
  x_scr : (xR s₀).Disjoint (scrR s₀)
  y_out : (yR s₀).Disjoint (outR s₀)
  y_scr : (yR s₀).Disjoint (scrR s₀)
  arg_out : (argR s₀).Disjoint (outR s₀)
  arg_scr : (argR s₀).Disjoint (scrR s₀)
  ret_out : (retR s₀).Disjoint (outR s₀)
  ret_scr : (retR s₀).Disjoint (scrR s₀)
  x_fits : (xp s₀).toNat + 1024 ≤ 2 ^ 32
  y_fits : (yp s₀).toNat + 1024 ≤ 2 ^ 32
  out_fits : (op s₀).toNat + 1024 ≤ 2 ^ 32
  scr_fits : (scr s₀).toNat + 4096 ≤ 2 ^ 32
  esp_fits : (esp₀ s₀).toNat + 20 ≤ 2 ^ 32

theorem pre_of (s₀ : State) (h : compressX86.pre s₀) : Pre s₀ := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

namespace Pre
variable {s₀ : State} (hp : Pre s₀)
include hp

theorem acc {s : State} (hw : s.wr = s₀.wr) : Acc s.wr (scr s₀) 4096 :=
  VG.Proof.Sha512.X86.Acc.of_mem (by rw [hw, hp.wr]; simp) hp.scr_fits

theorem in_scr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 4096) :
    InRegions (s.rd ++ s.wr) (addr (scr s₀) d) 4 :=
  mem_rd (hp.acc hw d hd)

theorem out_wr {s : State} (hw : s.wr = s₀.wr) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions s.wr (addr (op s₀) d) 4 :=
  ⟨outR s₀, by simp [hw, hp.wr], contains_addr hd (by omega) hp.out_fits⟩

theorem in_x {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (xp s₀) d) 4 :=
  ⟨xR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.x_fits⟩

theorem in_y {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : d + 4 ≤ 1024) :
    InRegions (s.rd ++ s.wr) (addr (yp s₀) d) 4 :=
  ⟨yR s₀, by simp [hrd, hp.rd], contains_addr hd (by omega) hp.y_fits⟩

theorem argAddr_eq {d : Nat} (hd : d < 20) :
    addr (esp₀ s₀) d = (esp₀ s₀).setWidth 64 + BitVec.ofNat 64 d :=
  addr_eq (by have := hp.esp_fits; omega)

theorem arg_contains {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    (argR s₀).Contains (addr (esp₀ s₀) d) 4 := by
  show (⟨addr (esp₀ s₀) 4, 16⟩ : Region).Contains _ _
  rw [hp.argAddr_eq (by omega), hp.argAddr_eq (by omega)]
  exact Offset.contains _ hd (by omega) (by omega)

theorem in_arg {s : State} (hrd : s.rd = s₀.rd) {d : Nat} (hd : 4 ≤ d) (hd' : d + 4 ≤ 20) :
    InRegions (s.rd ++ s.wr) (addr (esp₀ s₀) d) 4 :=
  ⟨argR s₀, by simp [hrd, hp.rd], hp.arg_contains hd hd'⟩

/-- An argument is unchanged while only `out` and `scratch` are written. -/
theorem arg_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : 4 ≤ d)
    (hd' : d + 4 ≤ 20) : m.readW (addr (esp₀ s₀) d) 32 = s₀.mem.readW (addr (esp₀ s₀) d) 32 := by
  refine hf.readW (r := argR s₀) (hp.arg_contains hd hd') ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.arg_out, hp.arg_scr⟩

/-- A word of `x` is unchanged while only `out` and `scratch` are written. -/
theorem x_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (xp s₀) d) 32 = s₀.mem.readW (addr (xp s₀) d) 32 := by
  refine hf.readW (r := xR s₀) (contains_addr hd (by omega) hp.x_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.x_out, hp.x_scr⟩

theorem y_frame {m : Mem} (hf : Frame [outR s₀, scrR s₀] s₀.mem m) {d : Nat} (hd : d + 4 ≤ 1024) :
    m.readW (addr (yp s₀) d) 32 = s₀.mem.readW (addr (yp s₀) d) 32 := by
  refine hf.readW (r := yR s₀) (contains_addr hd (by omega) hp.y_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨hp.y_out, hp.y_scr⟩

/-- A word of `scratch` is unchanged while only `out` is written. -/
theorem scr_frame {m m' : Mem} (hf : Frame [outR s₀] m m') {d : Nat} (hd : d + 4 ≤ 4096) :
    m'.readW (addr (scr s₀) d) 32 = m.readW (addr (scr s₀) d) 32 := by
  refine hf.readW (r := scrR s₀) (contains_addr hd (by omega) hp.scr_fits) ?_ (by decide)
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]
  exact hp.out_scr.symm

end Pre

end VG.Proof.Argon2.X86
