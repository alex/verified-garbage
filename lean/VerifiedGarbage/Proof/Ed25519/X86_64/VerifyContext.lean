import VerifiedGarbage.Proof.Ed25519.X86_64.PointDecode
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyPoints
import VerifiedGarbage.Proof.Ed25519.X86_64.VerifyTables

/-! Untrusted: the verification inputs remain readable and outside the workspace. -/

namespace VG.Proof.Ed25519.X86_64

open VG VG.X86_64 VG.Impl.Ed25519.X86_64
open VG.Proof.X25519.X86_64 (off ofs Keeps)

abbrev VerifyKeep (base : Addr) (s t : State) := PowersKeep base 56 7752 s t

theorem PowersKeep.of_decode {base : Addr} {o n : Nat} {s t : State} (h : DecodeKeep base s t) :
    PowersKeep base o n s t :=
  ⟨fun r hb hi hr => h.gpr r hr hb hi, h.rd, h.wr, fun p hp _ => h.mem p hp⟩

structure VerifyContext (s : State) (base pk sig challenge : Addr) : Prop where
  scratch : Scratch s base
  pkHeader : s.mem.readW (off base 7936) 64 = pk
  sigHeader : s.mem.readW (off base 7944) 64 = sig
  challengeHeader : s.mem.readW (off base 7952) 64 = challenge
  pkRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off pk d) 8
  rRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off sig d) 8
  scalarRead : ∀ d, d + 8 ≤ 32 → InRegions (s.rd ++ s.wr) (off (off sig 32) d) 8
  scalarBytes : ∀ i < 32, InRegions (s.rd ++ s.wr) (off (off sig 32) i) 1
  challengeRead : ∀ i < 64, InRegions (s.rd ++ s.wr) (off challenge i) 1
  pkFar : ∀ i < 32, 8192 ≤ ofs base (off pk i)
  rFar : ∀ i < 32, 8192 ≤ ofs base (off sig i)
  scalarFar : ∀ i < 32, 8192 ≤ ofs base (off (off sig 32) i)
  challengeFar : ∀ i < 64, 8192 ≤ ofs base (off challenge i)

theorem VerifyContext.of_keep {s t : State} {base pk sig challenge : Addr}
    (h : VerifyContext s base pk sig challenge) (k : VerifyKeep base s t) :
    VerifyContext t base pk sig challenge := by
  refine ⟨k.scratch h.scratch,
    (k.header (by decide) (by decide) (by decide)).trans h.pkHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.sigHeader,
    (k.header (by decide) (by decide) (by decide)).trans h.challengeHeader,
    ?_, ?_, ?_, ?_, ?_, h.pkFar, h.rFar, h.scalarFar, h.challengeFar⟩
  all_goals intros; rw [k.rd, k.wr]
  · exact h.pkRead _ ‹_›
  · exact h.rRead _ ‹_›
  · exact h.scalarRead _ ‹_›
  · exact h.scalarBytes _ ‹_›
  · exact h.challengeRead _ ‹_›

theorem verifyKeep_bytes {base p : Addr} {len : Nat} {s t : State}
    (h : VerifyKeep base s t) (hf : ∀ i < len, 8192 ≤ ofs base (off p i)) :
    Spec.Ed25519.bytesAt t.mem p len = Spec.Ed25519.bytesAt s.mem p len :=
  outside_bytes (tableFrame_work h.mem (by decide) (by decide)) (by decide) hf

theorem testResult_ok {s : State} (b : Bool) (hs : s.gpr .rax = signWord b) :
    WP isa (.block [.alu .test .rax (.reg .rax)]) s fun t => t.zf = some (!b) ∧ Keeps [] s t := by
  apply WP.of_runBlock
  simp only [runBlock_cons, runStep_some, runBlock_nil, exec, readSrc, execAlu,
    RegUpd.zf_arithFlags, Option.bind_some, Option.some.injEq, exists_eq_left', BitVec.and_self, hs]
  refine ⟨?_, fun _ _ => rfl, rfl, rfl, rfl⟩
  cases b <;> rfl

theorem decodedThen_ok {s : State} {base : Addr} {p : Option Spec.Ed25519.Point}
    {next : Prog isa} {P : State → Prop} (hr : DecodeResult base p s)
    (hn : ∀ t, Keeps [] s t → p = none → WP isa recoverInvalid t P)
    (hy : ∀ t a, Keeps [] s t → p = some a → point (env t.mem base) 0 1 2 3 = a → WP isa next t P) :
    WP isa (decodedThen next) s P := by
  rw [decodedThen]
  cases hp : p with
  | none =>
    rw [hp] at hr
    refine WP.seq (WP.mono (testResult_ok false hr) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite false (by simp only [eval, tz, Option.map_some, Bool.not_false, Bool.not_true])
    · intro h; contradiction
    · intro _; exact hn t kt hp
  | some a =>
    rw [hp] at hr
    refine WP.seq (WP.mono (testResult_ok true hr.1) fun t ⟨tz, kt⟩ => ?_)
    apply WP.ite true (by simp only [eval, tz, Option.map_some, Bool.not_true, Bool.not_false])
    · intro _; exact hy t a kt hp (by rw [kt.2.1]; exact hr.2)
    · intro h; contradiction

end VG.Proof.Ed25519.X86_64
